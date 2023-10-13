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
  extends CompiledModification {
  import indMod._
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

  case class CompiledIntro(name: Name, ty: Expr) {
    val NormalizedPis(arguments, Apps(introType, introTyArgs)) =
      NormalizedPis.instantiate(ty, params)
    val introTyIndices: List[Expr] = introTyArgs.drop(numParams)

    type ArgInfo = Either[Expr, (List[LocalConst], List[Expr])]

    /**
     * Arguments separated into those that are recursive and those that are
     * not.
     */
    val argInfos: List[ArgInfo] = arguments.map {
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
        require(recArgs.size >= numParams)
        tc.requireDefEq(
          Apps(recArgIndTy, recArgs.take(numParams)),
          indTyWParams)
        Right((eps, recArgs.drop(numParams)))
      case nonRecArg => Left(nonRecArg)
    }

    /**
     * Whether all arguments are non-recursive.
     */
    val nonRec: Boolean = argInfos.forall(_.isLeft)

    /**
     * Variables corresponding to recursive arguments.
     *
     * @return
     *   A list of variables corresponding to recursive arguments, in the same
     *   order as the recursive arguments.
     */
    lazy val ihs: List[LocalConst] = arguments
      .lazyZip(argInfos)
      .collect {
        case (recArg, Right((eps, recIndices))) =>
          LocalConst(
            Binding(
              "ih",
              Pis(eps)(mkMotiveApp(recIndices, Apps(recArg, eps))),
              BinderInfo.Default))
      }
      .toList

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
    lazy val redRule: ReductionRule = {
      val recCalls = arguments.zip(argInfos).collect {
        case (recArg, Right((eps, recArgIndices))) =>
          Lams(eps)(
            Apps(
              Const(elimDecl.name, elimLevelParams),
              params ++ Seq(motive) ++ minorPremises ++ recArgIndices :+ Apps(
                recArg,
                eps)))
      }
      ReductionRule(
        Vector() ++ params ++ Seq(
          motive) ++ minorPremises ++ indices ++ arguments,
        Apps(
          Const(elimDecl.name, elimLevelParams),
          params ++ Seq(motive) ++ minorPremises ++ indices
            :+ Apps(Const(name, univParams), params ++ arguments)),
        Apps(minorPremise, arguments ++ recCalls),
        List())
    }

    def check(): Unit = {
      require(introTyArgs.size >= numParams)
      tc.requireDefEq(
        Apps(introType, introTyArgs.take(numParams)),
        Apps(indTy, params))

      val tc0 = new TypeChecker(env)
      arguments.zip(argInfos).foreach {
        case (_, Left(nonRecArg)) =>
          tc0.inferUniverseOfType(tc0.infer(nonRecArg))
        case (_, Right((eps, _))) =>
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
    Binding("C", motiveType, BinderInfo.Implicit))

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

  /**
   * The minor premises for the introduction rules.
   */
  val minorPremises: Vector[LocalConst] = compiledIntros.map { _.minorPremise }

  /**
   * The major premise, i.e., a variable for an element of the inductive type.
   */
  val majorPremise = LocalConst(
    Binding("x", Apps(indTy, params ++ indices), BinderInfo.Default))

  /**
   * The elimination rule type.
   */
  val elimType: Expr = Pis(
    params ++ Seq(motive) ++ minorPremises ++ indices :+ majorPremise)(mkMotiveApp(indices, majorPremise))
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

  val decls: Vector[Declaration] =
    Declaration(name, univParams, ty, builtin = true) +: introDecls :+ elimDecl
  val rules: Vector[ReductionRule] =
    if (kIntroRule.isDefined)
      kIntroRule.toVector
    else
      compiledIntros.map(_.redRule)

  val structIntros: Map[Name, Declaration] =
    if (isStructure) Map(name -> introDecls(0))
    else Map()

  def check(): Unit = {
    val withType: PreEnvironment = env.addNow(decl)
    val withIntros: PreEnvironment = introDecls.foldLeft(withType) { (env, i) =>
      i.check(withType); env.addNow(i)
    }
    withIntros.addNow(elimDecl)

    for (i <- compiledIntros) i.check()
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
