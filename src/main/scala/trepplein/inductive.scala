package trepplein

import trepplein.Level.Param

/**
 * Compiled inductive type declaration.
 *
 * @param indMod
 *   The original inductive type declaration.
 * @param env
 *   The pre-environment in which the inductive type declaration is compiled.
 */
final case class CompiledIndMod(indMod: IndMod, env: PreEnvironment)
  extends CompiledModification { comp =>
  import indMod._, CompiledIndMod._
  val tc = new TypeChecker(env.addNow(decl))
  import tc.NormalizedPis

  def name: Name = indMod.name
  def univParams: Vector[Param] = indMod.univParams

  /**
   * The constant to be introduced for the type.
   */
  val indTy: Const = Const(name, univParams)

  // Obtain parameters, indices and level of the inductive type
  val ((params: List[LocalConst], indices: List[LocalConst]), level: Level) =
    ty match {
      case NormalizedPis(doms: List[LocalConst], Sort(lvl: Level)) =>
        (doms.splitAt(numParams), lvl)
      case _ =>
        throw new IllegalArgumentException(
          s"Type $ty did not match as a NormalizedPis even with empty doms")
    }

  /**
   * Inductive type with parameters (but not indices) applied.
   */
  val indTyWParams: Expr = Apps(indTy, params)

  def introHeadsFromType(instantiated: Expr): List[(Const, List[Expr])] = {
    val NormalizedPis(arguments, _) =
      instantiated
    arguments.flatMap {
      case LocalConst(
        Binding(
          _,
          NormalizedPis(
            eps,
            head @ Apps(const @ Const(modName, levels), recArgs)
            ),
          _
          ),
        _
        ) =>
        env.indMods.get(modName).flatMap { indMod: IndMod =>
          if (indMod.numParams > recArgs.size) None
          else if (recArgs
            .take(indMod.numParams)
            .exists(arg => arg.constants.contains(name))) {
            // println(s"Found recursive argument in $name, arguments: $arguments, recArgs: $recArgs, headLevels: ${head.univParams}, levels: $levels")
            // println(s"Derived from $instantiated with levels ${instantiated.univParams}")
            Some(const -> recArgs.take(indMod.numParams))
          } else None
        }
      case _ => None
    }
  }

  def introHeads(
    introType: Expr,
    introParams: List[Expr]): List[(Const, List[Expr])] = {
    val instantiated = NormalizedPis.instantiate(introType, introParams)
    introHeadsFromType(instantiated)
  }

  def introHeadsRec(
    accum: Vector[(Const, List[Expr])],
    indTypes: Vector[(Const, List[Expr])]): Vector[(Const, List[Expr])] = {
    val heads = indTypes.flatMap {
      case (indType, indParams) =>
        val indMod = env.indMods(indType.name)
        val intros = indMod.intros.map {
          case (name, ty) =>
            Const(name, indType.levels)
        }
        intros.flatMap { intro =>
          val folded = Apps(intro, indParams)
          val typ = tc.infer(folded)
          introHeadsFromType(typ)
        }
    }
    val newHeads = heads.filterNot(accum.contains(_)).distinct
    val newAccum = accum ++ newHeads
    if (newHeads.isEmpty) accum else introHeadsRec(newAccum, newHeads)
  }

  val initIntroHeads = intros.flatMap {
    case (name, ty) =>
      introHeads(ty, params)
  }
  // if (initIntroHeads.nonEmpty)
  //   println(s"Saw intro heads $initIntroHeads in $name")
  val allIntroHeads = introHeadsRec(initIntroHeads, initIntroHeads)
  val mutRec = initIntroHeads.nonEmpty
  // if (mutRec)
  //   println(s"Found intro heads $allIntroHeads in $name")

  def getArgInfo: LocalConst => ArgInfo = {
    case LocalConst(
      Binding(
        _,
        NormalizedPis(
          eps,
          Apps(recArgIndTy @ Const(indMod.name, _), recArgs)
          ),
        _
        ),
      _
      ) =>
      require(recArgs.size >= numParams, "too few recursive arguments")
      tc.requireDefEq(Apps(recArgIndTy, recArgs.take(numParams)), indTyWParams)
      RecArg(eps, recArgs.drop(numParams))
    case arg @ LocalConst(
      Binding(
        _,
        NormalizedPis(
          eps,
          Apps(Const(name, _), recArgs)
          ),
        _
        ),
      _
      ) =>
      allIntroHeads
        .find { case (n, ps) => name == n.name && recArgs.take(ps.size) == ps }
        .map {
          case (n, ps) =>
            // println(
            //   s"Found mutual recursive argument of type $name, parameters: $ps, recArgs: $recArgs")
            MutRecArg(eps, n.name, ps, recArgs.drop(ps.size))
        }
        .getOrElse {
          NonRecArg(arg)
        }

    case nonRecArg => NonRecArg(nonRecArg)
  }

  def getIhs(arguments: List[LocalConst], argInfos: List[ArgInfo]) = arguments
    .lazyZip(argInfos)
    .collect {
      case (recArg, RecArg(eps, recIndices)) =>
        LocalConst(
          Binding(
            "ih",
            Pis(eps)(mkMotiveApp(recIndices, Apps(recArg, eps))),
            BinderInfo.Default))
      case (mutRecArg, MutRecArg(eps, name, params, recIndices)) =>
        LocalConst(
          Binding(
            "ih",
            Pis(eps)(
              filledMod((name, params))
                .mkMotiveApp(recIndices, Apps(mutRecArg, eps))),
            BinderInfo.Default))
    }
    .toList

  def getRedRule(
    arguments: List[LocalConst],
    argInfos: List[ArgInfo],
    minorPremise: LocalConst,
    name: Name): ReductionRule = {
    val recCalls = arguments.zip(argInfos).collect {
      case (recArg, RecArg(eps, recArgIndices)) =>
        Lams(eps)(
          Apps(
            Const(elimDecl.name, elimLevelParams),
            params ++ Seq(motive) ++ minorPremises ++ recArgIndices :+ Apps(
              recArg,
              eps)))
      case (mutRecArg, MutRecArg(eps, name, params, recArgIndices)) =>
        val mod = filledMod((name, params))
        Lams(eps)(
          Apps(
            Const(mod.elimName, elimLevelParams),
            params ++ Seq(mod.motive) ++ minorPremises ++ recArgIndices :+ Apps(
              mutRecArg,
              eps)))
    }
    ReductionRule(
      Vector() ++ params ++ Seq(motive) ++ filledIndMods.map(
        _.motive) ++ minorPremises ++ indices ++ arguments,
      Apps(
        Const(elimDecl.name, elimLevelParams),
        params ++ Seq(motive) ++ minorPremises ++ indices
          :+ Apps(Const(name, univParams), params ++ arguments)),
      Apps(minorPremise, arguments ++ recCalls),
      List())
  }

  import CompiledIndMod.ArgInfo

  case class CompiledIntro(name: Name, ty: Expr) {
    val NormalizedPis(arguments, Apps(introType, introTyArgs)) =
      NormalizedPis.instantiate(ty, params)
    val introTyIndices: List[Expr] = introTyArgs.drop(numParams)

    /**
     * Arguments separated into those that are recursive and those that are
     * not.
     */
    val argInfos: List[ArgInfo] = arguments.map(getArgInfo)

    /**
     * Whether all arguments are non-recursive.
     */
    val nonRec: Boolean = argInfos.forall(_.isNonRec)

    /**
     * Variables corresponding to recursive arguments.
     *
     * @return
     *   A list of variables corresponding to recursive arguments, in the same
     *   order as the recursive arguments.
     */
    lazy val ihs: List[LocalConst] = getIhs(arguments, argInfos)

    /**
     * Minor premise for the introduction rule, i.e., the data that defines the
     * value of the function for the image.
     *
     * @return
     *   The minor premise for the introduction rule.
     */
    lazy val minorPremise = LocalConst(
      Binding(
        "h",
        Pis(arguments ++ ihs)(
          mkMotiveApp(
            introTyIndices,
            Apps(Const(name, univParams), params ++ arguments))),
        BinderInfo.Default))

    /**
     * Reduction rule for the introduction rule. The value of the function is
     * defined by the minor premise.
     *
     * @return
     *   Reduction rule for the introduction rule.
     */
    lazy val redRule: ReductionRule =
      getRedRule(arguments, argInfos, minorPremise, name)

    def check(): Unit = {
      require(introTyArgs.size >= numParams)
      tc.requireDefEq(
        Apps(introType, introTyArgs.take(numParams)),
        Apps(indTy, params))

      val tc0 = new TypeChecker(env)
      arguments.zip(argInfos).foreach {
        case (_, NonRecArg(nonRecArg)) =>
          try { tc0.inferUniverseOfType(tc0.infer(nonRecArg)) }
          catch {
            case t: Throwable =>
              println(
                s"Error in $name while checking non-recursive argument $nonRecArg of type ${tc0.infer(nonRecArg)}")
              throw t
          }
        case (_, RecArg(eps, _)) =>
          for (e <- eps) tc0.inferUniverseOfType(tc0.infer(e))
        case (_, MutRecArg(eps, _, _, _)) =>
          for (e <- eps) tc0.inferUniverseOfType(tc0.infer(e))
      }

      if (level.maybeNonZero) for (arg <- arguments) {
        val argLevel = tc.inferUniverseOfType(tc.infer(arg))
        require(argLevel <== level)
      }
    }
  }

  /**
   * Introduction rules compiled to generate declarations, reduction rules etc.
   */
  val compiledIntros: Vector[CompiledIntro] = intros.map(CompiledIntro.tupled)

  /**
   * Whether the inductive type is a structure.
   */
  val isStructure: Boolean =
    intros.size == 1 && compiledIntros.forall(_.nonRec) && indices.isEmpty

  /**
   * Whether the elimination type is a proposition.
   */
  val elimIntoProp: Boolean = level.maybeZero &&
    (intros.size > 1 || compiledIntros.exists { intro =>
      intro.arguments.exists { arg =>
        !tc.isProof(arg) && !intro.introTyArgs.contains(arg)
      }
    })

  /**
   * Level for the elimination type. If the inductive type is a proposition,
   * this is zero. Otherwise, it is a fresh parameter.
   */
  val elimLevel: Level =
    if (elimIntoProp) Level.Zero
    else Level.Param(Name.fresh("l", univParams.map(_.param).toSet))
  val extraElimLevelParams: Vector[Param] =
    Vector(elimLevel).collect { case p: Level.Param => p }

  /**
   * The motive type for the elimination type.
   */
  val motiveType: Expr =
    Pis(
      indices :+ LocalConst(
        Binding("c", Apps(indTy, params ++ indices), BinderInfo.Default)))(Sort(elimLevel))

  /**
   * Variable for the motive.
   */
  val motive: LocalConst = LocalConst(
    Binding("motive", motiveType, BinderInfo.Implicit))

  /**
   * The motive expression for the elimination type.
   *
   * @param indices
   *   indices for the inductive type
   * @param e
   *   the major premise
   * @return
   *   the motive expression
   */
  def mkMotiveApp(indices: Seq[Expr], e: Expr): Expr =
    App(Apps(motive, indices), e)

  case class FilledIndMod(const: Const, params: List[Expr], num: Int) {
    filled =>
    val mod = env.indMods(const.name)
    val indTy = Apps(const, params)
    // println("Universe parameters: " + indTy.univParams + "for " + indTy + " versus " + comp.indTy.univParams)

    val intros = mod.intros.map {
      case (name, _) =>
        Apps(Const(name, const.levels), params)
    }

    val indices =
      ty match {
        case NormalizedPis(indices: List[LocalConst], Sort(lvl: Level)) =>
          indices
        case _ =>
          throw new IllegalArgumentException(
            s"Type $ty did not match as a NormalizedPis even with empty doms")
      }

    // println(intros.mkString("\n"))
    val introTyps = intros.map(tc.infer(_))
    // println(introTyps.mkString("\n"))

    /**
     * The motive type for the elimination type.
     */
    val motiveType: Expr =
      Pis(
        indices :+ LocalConst(
          Binding("c", Apps(indTy, indices), BinderInfo.Default)))(Sort(elimLevel))

    /**
     * Variable for the motive.
     */
    val motive: LocalConst = LocalConst(
      Binding("motive_" + num, motiveType, BinderInfo.Implicit))

    def mkMotiveApp(indices: Seq[Expr], e: Expr): Expr =
      App(Apps(motive, indices), e)

    val elimName = Name.Str(name, "rec_" + num)

    case class MutCompiledIntro(name: Name) {
      val intro = Apps(Const(name, const.levels), params)
      val ty = tc.infer(intro)
      val NormalizedPis(arguments, Apps(introType, introTyArgs)) = ty
      val introTyIndices: List[Expr] = introTyArgs.drop(params.size)

      val argInfos: List[ArgInfo] = arguments.map(getArgInfo)

      lazy val ihs: List[LocalConst] = getIhs(arguments, argInfos)

      lazy val minorPremise = LocalConst(
        Binding(
          "h",
          Pis(arguments ++ ihs)(
            mkMotiveApp(
              introTyIndices,
              Apps(Const(name, const.levels), params ++ arguments))),
          BinderInfo.Default))

      lazy val redRule: ReductionRule =
        getRedRule(arguments, argInfos, minorPremise, name)
    }

    val mutCompiledIntros: Vector[MutCompiledIntro] = mod.intros.map {
      case (name, _) => MutCompiledIntro(name)
    }
  }

  val filledIndMods: Vector[FilledIndMod] = allIntroHeads.zipWithIndex.map {
    case ((indName, indParams), n) =>
      FilledIndMod(indName, indParams, n + 1)
  }

  val filledMod: Map[(Name, List[Expr]), FilledIndMod] = filledIndMods.map {
    filled =>
      (filled.mod.name -> filled.params, filled)
  }.toMap

  val allMutCompiledIntros = filledIndMods.flatMap { filled =>
    filled.mutCompiledIntros
  }

  // filledIndMods.foreach { filled =>
  //   println(s"Filled inductive type ${filled.mod.name}, type ${filled.mod.ty} with params ${filled.params} and indices ${filled.indices}")
  //   println(s"Obtained instantiated type ${filled.indTy}")
  //   println(s"Obtained motive type ${filled.motiveType} (compare with $motiveType)")
  // }
  /**
   * The minor premises for the introduction rules.
   */
  val minorPremises: Vector[LocalConst] = compiledIntros.map {
    _.minorPremise
  } ++ allMutCompiledIntros.map { _.minorPremise }

  /**
   * The major premise, i.e., a variable for an element of the inductive type.
   */
  val majorPremise = LocalConst(
    Binding("x", Apps(indTy, params ++ indices), BinderInfo.Default))

  /**
   * The elimination rule type.
   */
  val elimType: Expr = Pis(
    params ++ Seq(motive) ++ filledIndMods.map(
      _.motive) ++ minorPremises ++ indices :+ majorPremise)(mkMotiveApp(indices, majorPremise))
  val elimLevelParams: Vector[Param] = extraElimLevelParams ++ univParams

  /**
   * The elimination rule (i.e., recursive definitions) declaration.
   */
  val elimDecl = Declaration(
    Name.Str(name, "rec"),
    elimLevelParams,
    elimType,
    builtin = true)

  /**
   * The reduction rule for recursion for a single introduction rule with no
   * arguments such as in the case of equality.
   */
  val kIntroRule: Option[ReductionRule] =
    compiledIntros match {
      case Vector(intro) if intro.arguments.isEmpty =>
        Some(
          ReductionRule(
            Vector() ++ params ++ Seq(
              motive) ++ minorPremises ++ indices ++ Seq(majorPremise),
            Apps(
              Const(elimDecl.name, elimLevelParams),
              params ++ Seq(motive) ++ minorPremises ++ indices
                ++ Seq(majorPremise)),
            minorPremises(0),
            (intro.introTyArgs zip (params ++ indices)).filter {
              case (a, b) =>
                a != b
            }))
      case _ => None
    }

  /**
   * Declarations for the introduction rules.
   */
  val introDecls: Vector[Declaration] =
    for (i <- compiledIntros)
      yield Declaration(i.name, univParams, i.ty, builtin = true)

  val structIntros: Map[Name, StructInfo] =
    if (isStructure) Map(name -> StructInfo(name, introDecls(0), params.size))
    else Map()

  val indMods: Map[Name, IndMod] = Map(indMod.name -> indMod)

  val structRules: Vector[ReductionRule] =
    if (isStructure) {
      val intro = compiledIntros(0)
      if (intro.arguments.size == 0) Vector()
      else {
        val projArgs = Vector.range(0, intro.arguments.size).map { i =>
          Proj(name, i, majorPremise)
        }
        val elem = Apps(Const(name, univParams), params ++ intro.arguments)
        val lhs = Apps(Const(intro.name, univParams), params ++ projArgs)
        Vector(
          ReductionRule(
            (params :+ majorPremise).toVector,
            lhs,
            majorPremise,
            List()))
      }
    } else Vector()

  val decls: Vector[Declaration] =
    Declaration(name, univParams, ty, builtin = true) +: introDecls :+ elimDecl
  val rules: Vector[ReductionRule] =
    if (kIntroRule.isDefined)
      kIntroRule.toVector
    else
      compiledIntros.map(_.redRule) ++ structRules
  // if (mutRec)
  //   println(s"Recursion type: $elimType")

  def check(): Unit = {
    val withType: PreEnvironment = env.addNow(decl)
    val withIntros: PreEnvironment = introDecls.foldLeft(withType) { (env, i) =>
      i.check(withType); env.addNow(i)
    }
    withIntros.addNow(elimDecl)

    for (i <- compiledIntros) i.check()
  }
}

object CompiledIndMod {
  sealed trait ArgInfo {
    val isNonRec: Boolean
  }
  case class NonRecArg(expr: Expr) extends ArgInfo {
    val isNonRec = true
  }
  case class RecArg(es: List[LocalConst], indices: List[Expr]) extends ArgInfo {
    val isNonRec = false
  }

  case class MutRecArg(
      es: List[LocalConst],
      modName: Name,
      params: List[Expr],
      indices: List[Expr]) extends ArgInfo {
    val isNonRec = false
  }

}

/**
 * Inductive type declaration.
 *
 * @param name
 *   Name of the inductive type.
 * @param univParams
 *   Universe parameters.
 * @param ty
 *   Type of the inductive type.
 * @param numParams
 *   Number of parameters (as distinct from indices).
 * @param intros
 *   Names and types of the introduction rules.
 */
final case class IndMod(
    name: Name,
    univParams: Vector[Level.Param],
    ty: Expr,
    numParams: Int,
    intros: Vector[(Name, Expr)]) extends Modification {
  val decl: Declaration = Declaration(name, univParams, ty, builtin = true)

  def compile(env: PreEnvironment): CompiledIndMod = CompiledIndMod(this, env)
}
