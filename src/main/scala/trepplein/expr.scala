package trepplein

import java.util.function.Predicate

import trepplein.Level._

import scala.annotation.tailrec
import scala.collection.mutable

/**
 * The type of binder for lambda-definitions and pi-types (for example whether
 * implicit)
 */
sealed trait BinderInfo extends Product {
  def dump = s"BinderInfo.$productPrefix"
}
object BinderInfo {

  /**
   * The default binder info, i.e., explicit variable.
   */
  case object Default extends BinderInfo

  /**
   * The implicit binder info.
   */
  case object Implicit extends BinderInfo

  /**
   * The strict implicit binder info.
   */
  case object StrictImplicit extends BinderInfo

  /**
   * The instance implicit binder info.
   */
  case object InstImplicit extends BinderInfo
}

/**
 * A binding for a lambda-definition or pi-type.
 *
 * @param prettyName
 *   the display name
 * @param ty
 *   the type (as an expression)
 * @param info
 *   the binder info
 */
case class Binding(prettyName: Name, ty: Expr, info: BinderInfo) {
  def dump(implicit lcs: mutable.Map[LocalConst.Name, String]) =
    s"Binding(${prettyName.dump}, ${ty.dump}, ${info.dump})"

  override val hashCode: Int =
    prettyName.hashCode + 37 * (ty.hashCode + 37 * info.hashCode)

  def equalsCore(that: Binding)(implicit cache: ExprEqCache): Boolean =
    this.info == that.info &&
      this.ty.equalsCore(that.ty) &&
      this.prettyName == that.prettyName
}

private class ExprCache extends java.util.IdentityHashMap[Expr, Expr] {
  @inline final def getOrElseUpdate(k: Expr)(v: Expr => Expr): Expr = {
    val cached: Expr = get(k)
    if (cached != null) {
      cached
    } else {
      val computed: Expr = v(k)
      put(k, computed)
      computed
    }
  }
}
private class ExprOffCache extends mutable.ArrayBuffer[ExprCache] {
  @inline final def getOrElseUpdate(k: Expr, off: Int)(
    v: Expr => Expr): Expr = {
    while (off >= size) this += new ExprCache
    this(off).getOrElseUpdate(k)(v)
  }
}

private class ExprEqCache extends java.util.IdentityHashMap[Expr, UFNode] {
  def find(e: Expr): UFNode = {
    var n = get(e)
    if (n == null) {
      n = new UFNode
      put(e, n)
    } else {
      n = n.find()
    }
    n
  }

  @inline final def checkAndThenUnion(a: Expr, b: Expr)(
    v: (Expr, Expr) => Boolean): Boolean = {
    val a_ = find(a)
    val b_ = find(b)
    if (a_ eq b_) return true
    if (v(a, b)) {
      a_.union(b_)
      true
    } else {
      false
    }
  }
}

private object Breadcrumb

/**
 * A kernel expression which represents a term in Lean. Terms include types, propositions, proofs and universes.
 * The expression may contain local constants, which are bound by lambda-definitions and pi-types, and also global
 * constants, which depend on the environment. Besides substituting constants, expressions can be definitionally
 * equal if they are related by a sequence of reduction rules.
 *
 * @param varBound bound on the de Bruijn indices of variables.
 * @param hasLocals whether the expression has local constants.
 * @param hashCode the hash code of the expression.
 */
sealed abstract class Expr(
    val varBound: Int,
    val hasLocals: Boolean,
    override val hashCode: Int) extends Product {
  final def hasVar(i: Int): Boolean = {
    this match {
      case _ if varBound <= i => false
      case Var(idx) => idx == i
      case App(a, b) => a.hasVar(i) || b.hasVar(i)
      case Lam(dom, body) => dom.ty.hasVar(i) || body.hasVar(i + 1)
      case Pi(dom, body) => dom.ty.hasVar(i) || body.hasVar(i + 1)
      case Let(dom, value, body) =>
        dom.ty.hasVar(i) || value.hasVar(i) || body.hasVar(i + 1)
      case Proj(typeName, idx, struct) => struct.hasVar(i)
      case expr =>
        throw new IllegalArgumentException(
          s"hasVar($i) called on $expr which has varBound $varBound greater than $i")
    }
  }

  def hasVars: Boolean = varBound > 0

  override def equals(that: Any): Boolean =
    that match {
      case that: Expr => equals(that)
      case _ => false
    }
  def equals(that: Expr): Boolean = equalsCore(that)(new ExprEqCache)
  def equalsCore(that: Expr)(implicit cache: ExprEqCache): Boolean =
    (this eq that) || this.hashCode == that.hashCode &&
      cache.checkAndThenUnion(this, that) {
        case (Var(i1), Var(i2)) => i1 == i2
        case (Sort(l1), Sort(l2)) => l1 == l2
        case (Const(n1, l1), Const(n2, l2)) => n1 == n2 && l1 == l2
        case (LocalConst(_, n1), LocalConst(_, n2)) => n1 == n2
        case (App(a1, b1), App(a2, b2)) =>
          a1.equalsCore(a2) && b1.equalsCore(b2)
        case (Lam(d1, b1), Lam(d2, b2)) =>
          d1.equalsCore(d2) && b1.equalsCore(b2)
        case (Pi(d1, b1), Pi(d2, b2)) => d1.equalsCore(d2) && b1.equalsCore(b2)
        case (Let(d1, v1, b1), Let(d2, v2, b2)) =>
          d1.equalsCore(d2) && v1.equalsCore(v2) && b1.equalsCore(b2)
        case _ => false
      }

  /**
   * Abstracts the local constant, i.e., replaces it with a de Bruijn indexed
   * variable.
   *
   * @param lc
   *   the local constant
   * @return
   *   the abstracted expression
   */
  def abstr(lc: LocalConst): Expr = abstr(0, Vector(lc))

  /**
   * Abstracts the local constants, i.e., replaces them with de Bruijn indexed
   * variables with offset. The offset is shifted by 1 in recursive calls in
   * the body of lambda-definitions and Pi-types.
   *
   * @param off
   *   the offset
   * @param lcs
   *   the local constants
   * @return
   *   the abstracted expression
   */
  def abstr(off: Int, lcs: Vector[LocalConst]): Expr =
    abstrCore(off, lcs)(new ExprOffCache)
  private def abstrCore(off: Int, lcs: Vector[LocalConst])(implicit cache: ExprOffCache): Expr =
    cache.getOrElseUpdate(this, off) {
      case _ if !hasLocals => this
      case LocalConst(_, name) =>
        lcs.indexWhere(_.name == name) match {
          case -1 => this
          case i => Var(i + off)
        }
      case App(a, b) =>
        App(a.abstrCore(off, lcs), b.abstrCore(off, lcs))
      case Lam(domain, body) =>
        Lam(
          domain.copy(ty = domain.ty.abstrCore(off, lcs)),
          body.abstrCore(off + 1, lcs))
      case Pi(domain, body) =>
        Pi(
          domain.copy(ty = domain.ty.abstrCore(off, lcs)),
          body.abstrCore(off + 1, lcs))
      case Let(domain, value, body) =>
        Let(
          domain.copy(ty = domain.ty.abstrCore(off, lcs)),
          value.abstrCore(off, lcs),
          body.abstrCore(off + 1, lcs))
      case Proj(typeName, idx, struct) =>
        Proj(typeName, idx, struct.abstrCore(off, lcs))
      case _ =>
        throw new IllegalArgumentException(
          s"abstrCore($off, $lcs) called on $this which should have no locals but hasLocals = $hasLocals")
    }

  /**
   * Instantiates the variable with de Bruijn index 0 with the given
   * expression.
   *
   * @param e
   *   the expression
   * @return
   *   the instantiated expression
   */
  def instantiate(e: Expr): Expr = instantiate(0, Vector(e))
  /**
   * Instantiates the variables with de Bruijn indices in the range `[off, off + es.size -1]` with
   * the given expressions. The offset is shifted by 1 in recursive calls in
   * the body of lambda-definitions and Pi-types.
   *
   * @param off the offset
   * @param es the expressions
   * @return the instantiated expression
   */
  def instantiate(off: Int, es: Vector[Expr]): Expr =
    if (varBound <= off) this
    else
      instantiateCore(off, es)(new ExprOffCache)
  private def instantiateCore(off: Int, es: Vector[Expr])(implicit cache: ExprOffCache): Expr =
    cache.getOrElseUpdate(this, off) {
      case _ if varBound <= off => this
      case Var(idx) =>
        if (off <= idx && idx < off + es.size) es(idx - off) else this
      case App(a, b) =>
        App(a.instantiateCore(off, es), b.instantiateCore(off, es))
      case Lam(domain, body) =>
        Lam(
          domain.copy(ty = domain.ty.instantiateCore(off, es)),
          body.instantiateCore(off + 1, es))
      case Pi(domain, body) =>
        Pi(
          domain.copy(ty = domain.ty.instantiateCore(off, es)),
          body.instantiateCore(off + 1, es))
      case Let(domain, value, body) =>
        Let(
          domain.copy(ty = domain.ty.instantiateCore(off, es)),
          value.instantiateCore(off, es),
          body.instantiateCore(off + 1, es))
      case Proj(typeName, idx, struct) =>
        Proj(typeName, idx, struct.instantiateCore(off, es))
      case _ =>
        throw new IllegalArgumentException(
          s"instantiateCore($off, $es) called on $this which has varBound $varBound which is greater than offset $off")
    }

  /**
   * Instantiates universe parameters with the given levels.
   *
   * @param subst map of parameters to levels
   * @return the instantiated expression
   */
  def instantiate(subst: Map[Param, Level]): Expr =
    if (subst.forall(x => x._1 == x._2)) this
    else instantiateCore(subst)(new ExprCache)
  private def instantiateCore(
    subst: Map[Param, Level])(implicit cache: ExprCache): Expr =
    cache.getOrElseUpdate(this) {
      case v: Var => v
      case Sort(level) => Sort(level.instantiate(subst))
      case Const(name, levels) => Const(name, levels.map(_.instantiate(subst)))
      case LocalConst(of, name) =>
        LocalConst(of.copy(ty = of.ty.instantiateCore(subst)), name)
      case App(a, b) => App(a.instantiateCore(subst), b.instantiateCore(subst))
      case Lam(domain, body) =>
        Lam(
          domain.copy(ty = domain.ty.instantiateCore(subst)),
          body.instantiateCore(subst))
      case Pi(domain, body) =>
        Pi(
          domain.copy(ty = domain.ty.instantiateCore(subst)),
          body.instantiateCore(subst))
      case Let(domain, value, body) =>
        Let(
          domain.copy(ty = domain.ty.instantiateCore(subst)),
          value.instantiateCore(subst),
          body.instantiateCore(subst))
      case Proj(typeName, idx, struct) =>
        Proj(typeName, idx, struct.instantiateCore(subst))
      case NatLit(n) => NatLit(n)
      case StringLit(s) => StringLit(s)
    }

  final def foreach_(f: Predicate[Expr]): Unit =
    if (f.test(this)) this match {
      case App(a, b) =>
        a.foreach_(f)
        b.foreach_(f)
      case Lam(domain, body) =>
        domain.ty.foreach_(f)
        body.foreach_(f)
      case Pi(domain, body) =>
        domain.ty.foreach_(f)
        body.foreach_(f)
      case Let(domain, value, body) =>
        domain.ty.foreach_(f)
        value.foreach_(f)
        body.foreach_(f)
      case Proj(typeName, idx, struct) =>
        struct.foreach_(f)
      case _: Var | _: Const | _: Sort | _: LocalConst | _: NatLit | _: StringLit =>

    }

  @inline final def foreachNoDups(f: Expr => Unit): Unit = {
    val seen = new java.util.IdentityHashMap[Expr, Breadcrumb.type]()
    foreach_ { x =>
      if (seen.put(x, Breadcrumb) == null) {
        f(x)
        true
      } else {
        false
      }
    }
  }

  @inline private def buildSet[T](f: mutable.Set[T] => Unit): Set[T] = {
    val set = mutable.Set[T]()
    f(set)
    set.toSet
  }

  /**
   * Returns the universe parameters of the expression.
   *
   * @return the universe parameters
   */
  def univParams: Set[Param] =
    buildSet { ps =>
      foreachNoDups {
        case Sort(level) => ps ++= level.univParams
        case Const(_, levels) => ps ++= levels.view.flatMap(_.univParams)
        case _ =>
      }
    }

  /**
   * Returns the constants of the expression.
   * @return the constants
   */
  def constants: Set[Name] =
    buildSet { cs =>
      foreachNoDups {
        case Const(name, _) => cs += name
        case _ =>
      }
    }

  /**
   * Constructs the Pi-type `that -> this`.
   *
   * @param that
   * @return
   */
  def -->:(that: Expr): Expr =
    Pi(Binding(Name.Anon, that, BinderInfo.Default), this)

  override def toString: String = pretty(this)

  def dump(implicit lcs: mutable.Map[LocalConst.Name, String] = null): String =
    this match {
      case _ if lcs eq null =>
        val lcs_ = mutable.Map[LocalConst.Name, String]()
        val d = dump(lcs_)
        if (lcs_.isEmpty) d
        else {
          val decls = lcs.values.map { n =>
            s"val $n = new LocalConst.Name()\n"
          }.mkString
          s"{$decls$d}"
        }
      case Var(i) => s"Var($i)"
      case Sort(level) => s"Sort(${level.dump})"
      case Const(name, levels) =>
        s"Const(${name.dump}, Vector(${levels.map(_.dump).mkString(", ")}))"
      case App(a, b) => s"App(${a.dump}, ${b.dump})"
      case Lam(dom, body) => s"Lam(${dom.dump}, ${body.dump})"
      case Pi(dom, body) => s"Pi(${dom.dump}, ${body.dump})"
      case LocalConst(of, name) =>
        val of1 =
          of.prettyName.toString.replace('.', '_').filter { _.isLetterOrDigit }
        val of2 = if (of1.isEmpty || !of1.head.isLetter) s"n$of1" else of1
        val n = lcs.getOrElseUpdate(
          name,
          LazyList.from(0).map(i => s"$of2$i").diff(lcs.values.toSeq).head)
        s"LocalConst(${of.dump}, $n)"
      case Let(dom, value, body) =>
        s"Let(${dom.dump}, ${value.dump}, ${body.dump})"
      case Proj(typeName, idx, struct) =>
        s"Proj(${typeName.dump}, $idx, ${struct.dump})"
      case NatLit(n) => s"NatLit($n)"
      case StringLit(s) => s"StringLit($s)"
    }
}

object Expr {
  def locals(exp: Expr): List[LocalConst] = exp match {
    case Var(idx) => List()
    case Sort(level) => List()
    case Const(name, levels) => List()
    case lc @ LocalConst(of, name) => List(lc)
    case App(a, b) => locals(a) ++ locals(b)
    case Lam(domain, body) => locals(domain.ty) ++ locals(body)
    case Pi(domain, body) => locals(domain.ty) ++ locals(body)
    case Let(domain, value, body) => locals(domain.ty) ++ locals(value) ++ locals(body)
    case Proj(typeName, idx, struct) => locals(struct)
    case NatLit(n) => List()
    case StringLit(s) => List()
  }
}

/**
 * A variable with de Bruijn indexing.
 *
 * @param idx
 *   the index
 */
case class Var(idx: Int)
  extends Expr(varBound = idx + 1, hasLocals = false, hashCode = idx)

/**
 * A sort.
 *
 * @param level
 *   the level
 */
case class Sort(level: Level)
  extends Expr(varBound = 0, hasLocals = false, hashCode = level.hashCode)

/**
 * A (globally defined) constant.
 *
 * @param name
 *   the name
 * @param levels
 *   the universe levels
 */
case class Const(name: Name, levels: Vector[Level])
  extends Expr(varBound = 0, hasLocals = false, hashCode = 37 * name.hashCode)

/**
 * A local constant.
 *
 * @param of
 *   the binding
 * @param name
 *   the name
 */
case class LocalConst(of: Binding, name: LocalConst.Name = new LocalConst.Name)
  extends Expr(varBound = 0, hasLocals = true, hashCode = 4 + name.hashCode)

/**
 * An application expression.
 *
 * @param a
 *   the function
 * @param b
 *   the argument
 */
case class App(a: Expr, b: Expr)
  extends Expr(
    varBound = math.max(a.varBound, b.varBound),
    hasLocals = a.hasLocals || b.hasLocals,
    hashCode = a.hashCode + 37 * b.hashCode)

/**
 * A lambda expression.
 *
 * @param domain
 *   the domain
 * @param body
 *   the body
 */
case class Lam(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals,
    hashCode = 1 + 37 * domain.hashCode + body.hashCode)

/**
 * A pi-type.
 *
 * @param domain
 *   the domain
 * @param body
 *   the body
 */
case class Pi(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals,
    hashCode = 2 + 37 * domain.hashCode + body.hashCode)

/**
 * A let-expression.
 *
 * @param domain
 *   the domain
 * @param value
 *   the value
 * @param body
 *   the body in which the variable is substituted
 */
case class Let(domain: Binding, value: Expr, body: Expr)
  extends Expr(
    varBound = math
      .max(math.max(domain.ty.varBound, value.varBound), body.varBound - 1),
    hasLocals = domain.ty.hasLocals || value.hasLocals || body.hasLocals,
    hashCode =
      3 + 37 * (domain.hashCode + 37 * value.hashCode) + body.hashCode)

case class Proj(typeName: Name, idx: Int, struct: Expr) extends Expr(
  varBound = struct.varBound,
  hasLocals = struct.hasLocals,
  hashCode = 5 + 37 * (typeName.hashCode + 37 * idx) + struct.hashCode)

case class NatLit(n: Long) extends Expr(
  varBound = 0,
  hasLocals = false,
  hashCode = 6 + 37 * n.toInt)

object NatLit {
  def expand(n: Long): Expr = {
    if (n == 0) {
      Const(Name("Nat", "zero"), Vector())
    } else {
      App(Const(Name("Nat", "succ"), Vector()), expand(n - 1))
    }
  }
}
case class StringLit(s: String) extends Expr(
  varBound = 0,
  hasLocals = false,
  hashCode = 7 + 37 * s.hashCode)

object Sort {

  /**
   * The sort of propositions.
   */
  val Prop = Sort(Level.Zero)
}

object LocalConst {

  /**
   * A generated name for a local constant.
   *
   */
  final class Name {
    override def toString: String = Integer.toHexString(hashCode()).take(4)
  }
}

/**
 * For constructing and pattern matching lambda-definitions and Pi-types,
 * with the variable as a local constant instead of a binding.
 */
trait Binder[T] {
  def apply(domain: Binding, body: Expr): T
  def apply(domain: LocalConst, body: Expr): T =
    apply(domain.of, body.abstr(domain))

  trait GenericUnapply {
    def unapply(e: Expr): Option[(Binding, Expr)]
  }
  val generic: GenericUnapply
}

/**
 * For constructing and pattern matching (iterated) lambda-definitions and Pi-types,
 * with variables as a local constants.
 */
trait Binders[T <: Expr] {
  protected val Single: Binder[T]

  def apply(domains: Iterable[LocalConst])(body: Expr): Expr =
    domains.foldRight(body)(Single.apply)

  def apply(domains: LocalConst*)(body: Expr): Expr =
    apply(domains)(body)

  def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
    e match {
      case Single.generic(dom, expr) =>
        val lc = LocalConst(dom)
        unapply(expr.instantiate(lc)) match {
          case Some((lcs, head)) =>
            Some((lc :: lcs, head))
        }
      case _ => Some((Nil, e))
    }
}

/**
 * For constructing `let` expressions,
 * with the variable as a local constant instead of a binding.
 */
object Let {
  def apply(x: LocalConst, v: Expr, b: Expr): Let =
    Let(x.of, v, b.abstr(x))
}

/**
 * For constructing and pattern matching lambda-definitions,
 * with the variable as a local constant instead of a binding.
 */
object Lam extends Binder[Lam] {
  val generic: GenericUnapply = {
    case e: Lam => Lam.unapply(e)
    case _ => None
  }
}

/**
 * For constructing and pattern matching (iterated) lambda-definitions,
 * with variables as a local constants.
 */
object Lams extends Binders[Lam] {
  protected val Single = Lam
}

/**
 * For constructing and pattern matching Pi-types,
 * with the variable as a local constant instead of a binding.
 */
object Pi extends Binder[Pi] {
  val generic: GenericUnapply = {
    case e: Pi => Pi.unapply(e)
    case _ => None
  }
}

/**
 * For constructing and pattern matching (iterated) Pi-types,
 * with variables as a local constants.
 */
object Pis extends Binders[Pi] {
  protected val Single = Pi
}

object Apps {
  @tailrec
  private def decompose(e: Expr, as: List[Expr] = Nil): (Expr, List[Expr]) =
    e match {
      case App(f, a) => decompose(f, a :: as)
      case _ => (e, as)
    }

  def unapply(e: Expr): Some[(Expr, List[Expr])] =
    Some(decompose(e))

  def apply(fn: Expr, as: Iterable[Expr]): Expr =
    as.foldLeft(fn)(App)

  def apply(fn: Expr, as: Expr*): Expr =
    apply(fn, as)
}

object Nat {
  val Zero = Const(Name("Nat", "zero"), Vector())
  val Succ = Const(Name("Nat", "succ"), Vector())

  def unapply(e: Expr): Option[Long] = e match {
    case NatLit(n) => Some(n)
    case Zero => Some(0)
    case App(Succ, n) => unapply(n).map(_ + 1)
    case _ => None
  }
}
