package trepplein

import scala.annotation.tailrec
import scala.collection.mutable

sealed trait DefEqRes {
  @inline final def &(that: => DefEqRes): DefEqRes =
    if (this != IsDefEq) this else that
}
case object IsDefEq extends DefEqRes {
  def forall(rs: Iterable[DefEqRes]): DefEqRes =
    rs.collectFirst { case r: NotDefEq => r }.getOrElse(IsDefEq)

  var lhs: Option[Expr] = None
  var rhs: Option[Expr] = None
}
final case class NotDefEq(a: Expr, b: Expr) extends DefEqRes

class TypeChecker(
    val env: PreEnvironment,
    val unsafeUnchecked: Boolean = false) {
  def shouldCheck: Boolean = !unsafeUnchecked

  object NormalizedPis {

    /**
     * Maximal match with pi-types allowing normalization by `whnf`.
     *
     * @param e
     *   the expression to match.
     * @return
     *   list of variables and the body of the pi-type.
     */
    def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
      whnf(e) match {
        case Pis(lcs1, f) if lcs1.nonEmpty =>
          val NormalizedPis(lcs2, g) = f
          Some((lcs1 ::: lcs2, g))
        case f => Some((Nil, f))
      }

    /**
     * Instantiates an iterated pi-type (allowing normalization by `whnf`) with
     * a list of expressions for the pi-type variables and a context with the
     * remaining variables.
     *
     * @param e
     *   The expressio to instantiate.
     * @param ts
     *   The list of expressions to instantiate with for variables of the
     *   pi-type.
     * @param ctx
     *   The context to instantiate with for the remaining variables.
     * @return
     */
    @tailrec def instantiate(
      e: Expr,
      ts: List[Expr],
      ctx: List[Expr] = Nil): Expr =
      (e, ts) match {
        case (Pi(_, body), t :: ts_) =>
          instantiate(body, ts_, t :: ctx)
        case (_, _ :: _) =>
          instantiate(whnf(e).ensuring(_.isInstanceOf[Pi]), ts, ctx)
        case (_, Nil) => e.instantiate(0, ctx.toVector)
      }
  }

  private val levelDefEqCache = mutable.AnyRefMap[(Level, Level), Boolean]()
  def isDefEq(a: Level, b: Level): Boolean =
    levelDefEqCache.getOrElseUpdate((a, b), a === b)

  def isProp(s: Expr): Boolean = whnf(s) match {
    case Sort(l) => l.isZero
    case _ => false
  }
  def isProposition(ty: Expr): Boolean = isProp(infer(ty))
  def isProof(p: Expr): Boolean = isProposition(infer(p))

  private def isProofIrrelevantEq(e1: Expr, e2: Expr): Boolean =
    isProof(e1) && isProof(e2)

  private def reqDefEq(cond: Boolean, e1: Expr, e2: Expr, message: String) =
    if (cond) IsDefEq
    else {
      NotDefEq(e1, e2)
    }

  def isDefEq(e1: Expr, e2: Expr): Boolean = checkDefEq(e1, e2) == IsDefEq

  def defHeight(fn: Expr, as: List[Expr]): Int =
    fn match {
      case Const(n, _) => env.get(n).map(_.height + 1).getOrElse(0)
      case _ => 0
    }

  private def reduceOneStep(e1: Expr, e2: Expr)(implicit transparency: Transparency): Option[(Expr, Expr)] = {
    val Apps(fn1, as1) = e1
    val Apps(fn2, as2) = e2

    @inline def red1 = reduceOneStep(fn1, as1).map(_ -> e2)
    @inline def red2 = reduceOneStep(fn2, as2).map(e1 -> _)

    if (defHeight(fn1, as1) > defHeight(fn2, as2))
      red1 orElse red2
    else
      red2 orElse red1
  }

  private val lcCache =
    mutable.AnyRefMap[Expr, List[LocalConst]]().withDefaultValue(Nil)
  private def popCachedLC(binding: Binding): LocalConst =
    lcCache(binding.ty) match {
      case cached :: rest =>
        lcCache(binding.ty) = rest
        cached
      case Nil => LocalConst(binding)
    }
  @inline private def withLC[T](binding: Binding)(f: LocalConst => T): T = {
    val lc = popCachedLC(binding)
    val result = f(lc)
    lcCache(binding.ty) ::= lc
    result
  }

  private def checkDefEqCore(e1_0: Expr, e2_0: Expr): DefEqRes = {
    val transparency = Transparency(rho = false)
    val e1 @ Apps(fn1, as1) = whnfCore(e1_0)(transparency)
    val e2 @ Apps(fn2, as2) = whnfCore(e2_0)(transparency)
    def checkArgs: DefEqRes =
      reqDefEq(as1.size == as2.size, e1, e2, "argument sizes must match") &
        IsDefEq.forall(as1.lazyZip(as2).view.map {
          case (a, b) =>
            checkDefEq(a, b)
        })
    ((fn1, fn2) match {
      case (Sort(l1), Sort(l2)) =>
        return reqDefEq(
          isDefEq(l1, l2) && as1.isEmpty && as2.isEmpty,
          e1,
          e2,
          "universes must have the same levels")
      case (Const(c1, ls1), Const(c2, ls2)) if c1 == c2 && ls1.lazyZip(ls2).forall(isDefEq) =>
        checkArgs
      case (LocalConst(_, i1), LocalConst(_, i2)) if i1 == i2 =>
        checkArgs
      case (Lam(dom, b1), Lam(_, b2)) =>
        require(as1.isEmpty && as2.isEmpty, "unexpected arguments to lambda")
        return withLC(dom)(lc =>
          checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc)))
      case (Lam(dom1, _), _) =>
        require(as1.isEmpty, "unexpected arguments to lambda")
        return checkDefEqCore(e1, Lam(dom1, App(e2, Var(0))))
      case (_, Lam(dom2, _)) =>
        require(as2.isEmpty, "unexpected arguments to lambda")
        return checkDefEqCore(Lam(dom2, App(e1, Var(0))), e2)
      case (Pi(dom1, b1), Pi(dom2, b2)) =>
        require(as1.isEmpty && as2.isEmpty, "unexpected arguments to pi-type")
        return checkDefEq(dom1.ty, dom2.ty) & withLC(dom1)(lc =>
          checkDefEqCore(b1.instantiate(lc), b2.instantiate(lc)))
      case (Proj(typeName1, idx1, struct1), Proj(typeName2, idx2, struct2)) if idx1 == idx2 && typeName1 == typeName2 =>
        // require(as1.isEmpty && as2.isEmpty, "unexpected arguments to projection")
        return checkArgs & checkDefEq(struct1, struct2)
      case (Nat(n1), Nat(n2)) =>
        return reqDefEq(n1 == n2, e1, e2, "nat literals must be equal")
      case (StringLit(s1), StringLit(s2)) =>
        return reqDefEq(s1 == s2, e1, e2, "string literals must be equal")
      case (_, _) =>
        NotDefEq(e1, e2)
    }) match {
      case IsDefEq => IsDefEq
      case d @ NotDefEq(_, _) =>
        reduceOneStep(e1, e2)(Transparency.all) match {
          case Some((e1_, e2_)) =>
            checkDefEqCore(e1_, e2_)
          case None => d
        }
    }
  }

  private val defEqCache = mutable.AnyRefMap[(Expr, Expr), DefEqRes]()
  // requires that e1 and e2 have the same type, or are types
  def checkDefEq(e1: Expr, e2: Expr): DefEqRes =
    if (e1.eq(e2) || e1 == e2) IsDefEq
    else
      defEqCache.getOrElseUpdate(
        (e1, e2), {
          if (isProofIrrelevantEq(e1, e2)) IsDefEq else checkDefEqCore(e1, e2)
        })

  case class Transparency(rho: Boolean) {
    def canReduceConstants: Boolean = rho
  }
  object Transparency {
    val all = Transparency(rho = true)
  }

  def reduceOneStep(e: Expr)(implicit transparency: Transparency): Option[Expr] =
    e match { case Apps(fn, as) => reduceOneStep(fn, as) }
  private implicit object reductionRuleCache extends ReductionRuleCache {
    private val instantiationCache =
      mutable.AnyRefMap[(ReductionRule, Map[Level.Param, Level]), Expr]()
    override def instantiation(
      rr: ReductionRule,
      subst: Map[Level.Param, Level],
      v: => Expr): Expr =
      instantiationCache.getOrElseUpdate((rr, subst), v)
  }
  import Expr.C
  def decLeImpl(n: Long, m: Long): Expr = {
    val prop = Apps(C("Nat.le"), NatLit(n), NatLit(m))
    if (n <= m)
      Apps(
        C("Decidable.isTrue"),
        prop,
        Apps(
          C("Nat.le_of_ble_eq_true"),
          NatLit(n),
          NatLit(m),
          Apps(C("Eq.refl", Level.One), C("Nat"), NatLit(n))))
    else
      Apps(
        C("Decidable.isFalse"),
        prop,
        Apps(
          C("Nat.not_le_of_not_ble_eq_true"),
          NatLit(n),
          NatLit(m),
          C("Bool.not_false'")))
  }

  def decEqImpl(n: Long, m: Long): Expr = {
    val prop = Apps(C("Eq", Level.One), C("Nat"), NatLit(n), NatLit(m))
    if (n == m)
      Apps(
        C("Decidable.isTrue"),
        prop,
        Apps(
          C("Nat.eq_of_beq_eq_true"),
          NatLit(n),
          NatLit(m),
          Apps(C("Eq.refl", Level.One), C("Nat"), NatLit(n))))
    else
      Apps(
        C("Decidable.isFalse"),
        prop,
        Apps(
          C("Nat.ne_of_beq_eq_false"),
          NatLit(n),
          NatLit(m),
          C("Bool.ff_ne_tt")))
  }

  def reduceOneStep(fn: Expr, as0: List[Expr])(implicit transparency: Transparency): Option[Expr] =
    fn match {
      case Const(n @ Name.Str(Name.Str(Name.Anon, "Nat"), op), _) if Set(
        "add",
        "mul",
        "pow",
        "sub",
        "ble",
        "beq",
        "decLe",
        "decLt",
        "decEq").contains(op) =>
        as0.map(whnf) match {
          case Nat(n) :: Nat(m) :: Nil =>
            op match {
              case "ble" =>
                if (n <= m) Some(Const(Name.ofString("Bool.true"), Vector()))
                else Some(Const(Name.ofString("Bool.false"), Vector()))
              case "beq" =>
                if (n == m) Some(Const(Name.ofString("Bool.true"), Vector()))
                else Some(Const(Name.ofString("Bool.false"), Vector()))
              case "decLe" => Some(decLeImpl(n, m))
              case "decLt" =>
                Some(decLeImpl(n + 1, m))
              case "decEq" => Some(decEqImpl(n, m))
              case "add" => Some(NatLit(n + m))
              case "mul" => Some(NatLit(n * m))
              case "pow" =>
                Some(NatLit(math.pow(n.toDouble, m.toDouble).toLong))
              case "sub" => if (m > n) Some(NatLit(0)) else Some(NatLit(n - m))
            }
          case _ if transparency.rho =>
            val major = env.reductions.major(n)
            val as =
              for ((a, i) <- as0.zipWithIndex)
                yield if (major(i)) whnf(a) else a
            env.reductions(Apps(fn, as)) match {
              case Some((result, constraints)) if constraints.forall {
                case (a, b) => isDefEq(a, b)
              } =>
                Some(result)
              case _ => None
            }
          case _ => None
        }
      case Const(n, _) if transparency.rho =>
        val major = env.reductions.major(n)
        val as =
          for ((a, i) <- as0.zipWithIndex)
            yield if (major(i)) whnf(a) else a
        if (n == Name.ofString("Nat.rec") && Nat.unapply(as.last).isDefined) {
          val List(typ, zero, step, Nat(n)) = as
          Some(natRecImpl(zero, step, n))
        } else env.reductions(Apps(fn, as)) match {
          case Some((result, constraints)) if constraints.forall {
            case (a, b) => isDefEq(a, b)
          } =>
            Some(result)
          case _ => None
        }
      case _ => None
    }

  @tailrec
  final def natRecImplAux(init: Expr, step: Expr, cur: Long, n: Long): Expr =
    if (cur == n) {
      // println("Obtained recursion result")
      init
    } else {
      val next = Apps(step, NatLit(cur), init)
      // if (n > 1000) println(s"Recursing step $cur of $n")
      // infer(whnf(next))
      // if (n > 1000 && cur == 10) println(s"Simplified: ${whnf(next) != next}; \n\n$next\n\n${whnf(next)}\n\n\n")
      natRecImplAux(whnf(next), step, cur + 1, n)
    }

  def natRecImpl(zero: Expr, step: Expr, n: Long): Expr = natRecImplAux(zero, step, 0, n)

  object NormNat {
    def unapply(e: Expr): Option[Long] = e match {
      case Nat(n) => Some(n)
      case _ => whnf(e) match {
        case Nat(n) => Some(n)
        case _ => None
      }
    }
  }

  private val whnfCache = mutable.AnyRefMap[Expr, Expr]()
  def whnf(e: Expr): Expr =
    whnfCache.getOrElseUpdate(e, whnfCore(e)(Transparency.all))
  @tailrec final def whnfCore(
    e: Expr)(implicit transparency: Transparency = Transparency.all): Expr = e match {
    case Nat(n) =>
      if (n < 2) NatLit.expand(n) else NatLit(n)
    // case Apps(Const(name, _), List(typ, zero, step, NormNat(n))) if name == Name.ofString("Nat.rec") && n > 2 =>
    //   natRecImpl(zero, step, n)
    case _ => {
      val Apps(fn, as) = e
      fn match {
        case Sort(l) => Sort(l.simplify)
        case Lam(_, _) if as.nonEmpty =>
          @tailrec def go(fn: Expr, ctx: List[Expr], as: List[Expr]): Expr =
            (fn, as) match {
              case (Lam(_, fn_), a :: as_) => go(fn_, a :: ctx, as_)
              case _ => Apps(fn.instantiate(0, ctx.toVector), as)
            }
          whnfCore(go(fn, Nil, as))
        case Let(_, value, body) =>
          whnfCore(Apps(body.instantiate(value), as))
        case Proj(typeName, idx, struct) =>
          struct match {
            case Apps(Const(name, _), structParams) if name == env.structIntros(typeName).intro.name =>
              val x =
                structParams.drop(env.structIntros(typeName).numParams)(idx)
              whnfCore(Apps(x, as))
            case _ =>
              whnf(struct) match {
                case Apps(Const(name, _), structParams) if name == env.structIntros(typeName).intro.name =>
                  val x =
                    structParams.drop(env.structIntros(typeName).numParams)(idx)
                  whnfCore(Apps(x, as))
                case struct_ =>
                  if (struct_ == struct) e
                  else whnfCore(Apps(Proj(typeName, idx, struct_), as))
              }
          }
        case Nat(n) =>
          if (n < 2) NatLit.expand(n) else NatLit(n)
        case _ =>
          reduceOneStep(fn, as) match {
            case Some(e_) => whnfCore(e_)
            case None => e
          }
      }
    }
  }

  def stuck(e: Expr): Option[Expr] = whnf(e) match {
    case Apps(Const(n, _), as) if env.reductions.get(n).nonEmpty =>
      val numAs = as.size
      env.reductions
        .major(n)
        .filter(_ < numAs)
        .map(as(_))
        .flatMap(stuck)
        .headOption
    case e_ => Some(e_)
  }

  def ppError(e: Expr): Doc =
    new PrettyPrinter(
      Some(this),
      options = PrettyOptions(showImplicits = false)).pp(e).doc

  def checkType(e: Expr, ty: Expr): Unit = {
    val inferredTy = infer(e)
    checkDefEq(ty, inferredTy) match {
      case IsDefEq =>
      case neq @ NotDefEq(t_, i_) =>
        IsDefEq.lhs = Some(t_)
        IsDefEq.rhs = Some(i_)
        throw new IllegalArgumentException(
          Doc
            .stack(
              Doc.spread("wrong type: ", ppError(e), " : ", ppError(ty)),
              Doc.spread("inferred type: ", ppError(inferredTy)),
              Doc.spread(ppError(t_), " !=def ", ppError(i_)),
              Doc.spread(
                Seq[Doc]("stuck on: ") ++ Seq(t_, i_)
                  .flatMap(stuck)
                  .map(ppError)))
            .render(80))
    }
  }
  def requireDefEq(a: Expr, b: Expr): Unit =
    checkDefEq(a, b) match {
      case IsDefEq =>
      case NotDefEq(a_, b_) =>
        throw new IllegalArgumentException(
          Doc.stack("", ppError(a_), "!=def", ppError(b_)).render(80))
    }

  def inferUniverseOfType(ty: Expr): Level =
    whnf(infer(ty)) match {
      case Sort(l) => l
      case s =>
        throw new IllegalArgumentException(
          Doc.spread("not a sort: ", ppError(s)).render(80))
    }

  private val inferCache = mutable.AnyRefMap[Expr, Expr]()
  def infer(e: Expr): Expr = inferCache.getOrElseUpdate(
    e,
    e match {
      case Var(_) =>
        throw new IllegalArgumentException
      case Sort(level) =>
        Sort(Level.Succ(level))
      case Const(name, levels) =>
        val decl = env
          .get(name)
          .getOrElse(
            throw new IllegalArgumentException(s"unknown constant: $name"))
        require(
          decl.univParams.size == levels.size,
          s"incorrect number of universe parameters: $levels, expected ${decl.univParams}")
        decl.ty.instantiate(decl.univParams.zip(levels).toMap)
      case LocalConst(of, _) =>
        of.ty
      case Apps(fn, as0) if as0.nonEmpty =>
        @tailrec def go(fnt: Expr, as: List[Expr], ctx: List[Expr]): Expr =
          (fnt, as) match {
            case (_, Nil) => fnt.instantiate(0, ctx.toVector)
            case (Pi(dom, body), a :: as_) =>
              if (shouldCheck)
                checkType(a, dom.ty.instantiate(0, ctx.toVector))
              go(body, as_, a :: ctx) // should we be instantiating here?
            case (_, _ :: _) =>
              whnf(fnt.instantiate(0, ctx.toVector)) match {
                case fnt_ @ Pi(_, _) => go(fnt_, as, Nil)
                case _ =>
                  throw new IllegalArgumentException(
                    s"not a function type: $fnt")
              }
          }
        go(infer(fn), as0, Nil)
      case Lam(_, _) =>
        def go(e: Expr, ctx: List[LocalConst]): Expr = e match {
          case Lam(dom, body) =>
            val dom_ = dom.copy(ty = dom.ty.instantiate(0, ctx.toVector))
            if (shouldCheck) inferUniverseOfType(dom_.ty)
            Pi(dom, withLC(dom_)(lc => go(body, lc :: ctx)))
          case _ =>
            val ctxVec = ctx.toVector
            infer(e.instantiate(0, ctxVec)).abstr(0, ctxVec)
        }
        go(e, Nil)
      case Pi(_, _) =>
        def go(e: Expr, ctx: List[LocalConst]): Level = e match {
          case Pi(dom, body) =>
            val dom_ = dom.copy(ty = dom.ty.instantiate(0, ctx.toVector))
            val domUniv = inferUniverseOfType(dom_.ty)
            Level.IMax(domUniv, withLC(dom_)(lc => go(body, lc :: ctx)))
          case _ =>
            val ctxVec = ctx.toVector
            inferUniverseOfType(e.instantiate(0, ctxVec))
        }
        Sort(go(e, Nil).simplify)
      case Let(domain, value, body) =>
        if (shouldCheck) inferUniverseOfType(domain.ty)
        if (shouldCheck) checkType(value, domain.ty)
        infer(body.instantiate(value))
      case NatLit(n) =>
        Const(Name("Nat"), Vector())
      case StringLit(n) =>
        Const(Name("String"), Vector())
      case Proj(typeName, idx, struct) =>
        val structType = infer(struct)
        val structType_ = whnf(structType)
        val Apps(structHead, structParams) = structType_
        val decl = env.structIntros(typeName)
        val levels = structHead.asInstanceOf[Const].levels
        val constructorHead = Const(decl.intro.name, levels)
        val constructorType = infer(Apps(constructorHead, structParams))
        val foldedType: Expr =
          (0 until (idx)).foldLeft(constructorType) {
            case (ty, i) =>
              whnf(ty) match {
                case Pi(domain, body) =>
                  body.instantiate(0, Vector(Proj(typeName, i, struct)))
                case e =>
                  throw new IllegalArgumentException(
                    s"Expected Pi-type in projection, got $e")
              }
          }
        val typ = whnf(foldedType) match {
          case Pi(domain, body) => domain.ty
          case e =>
            throw new IllegalArgumentException(
              s"Expected Pi-type in projection, got $e")
        }
        typ
      case App(a, b) =>
        throw new IllegalArgumentException(
          "Unexpectedly matched App when Apps was a case")
    })
}
