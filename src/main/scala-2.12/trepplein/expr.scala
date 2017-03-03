package trepplein

import trepplein.Level._

import scala.annotation.tailrec
import scala.runtime.ScalaRunTime

sealed abstract class BinderInfo
object BinderInfo {
  case object Default extends BinderInfo
  case object Implicit extends BinderInfo
  case object StrictImplicit extends BinderInfo
  case object InstImplicit extends BinderInfo
}

case class Binding(prettyName: Name, ty: Expr, info: BinderInfo) {
  def abstr(off: Int, lcs: Vector[LocalConst]): Binding =
    copy(ty = ty.abstr(off, lcs))

  def instantiate(off: Int, es: Vector[Expr]): Binding =
    copy(ty = ty.instantiate(off, es))

  def instantiate(subst: Map[Param, Level]): Binding =
    copy(ty = ty.instantiate(subst))
}

sealed abstract class Expr(val varBound: Int, val hasLocals: Boolean) extends Product {
  def abstr(lc: LocalConst): Expr = abstr(0, Vector(lc))
  def abstr(off: Int, lcs: Vector[LocalConst]): Expr =
    this match {
      case _ if !hasLocals => this
      case LocalConst(_, name) =>
        lcs.indexWhere(_.name == name) match {
          case -1 => this
          case i => Var(i + off)
        }
      case App(a, b) =>
        App(a.abstr(off, lcs), b.abstr(off, lcs))
      case Lam(domain, body) =>
        Lam(domain.abstr(off, lcs), body.abstr(off + 1, lcs))
      case Pi(domain, body) =>
        Pi(domain.abstr(off, lcs), body.abstr(off + 1, lcs))
      case Let(domain, value, body) =>
        Let(domain.abstr(off, lcs), value.abstr(off, lcs), body.abstr(off + 1, lcs))
    }

  def instantiate(e: Expr): Expr = instantiate(0, Vector(e))
  def instantiate(off: Int, es: Vector[Expr]): Expr =
    this match {
      case _ if varBound <= off => this
      case Var(idx) => if (off <= idx && idx < off + es.size) es(idx - off) else this
      case App(a, b) => App(a.instantiate(off, es), b.instantiate(off, es))
      case Lam(domain, body) => Lam(domain.instantiate(off, es), body.instantiate(off + 1, es))
      case Pi(domain, body) => Pi(domain.instantiate(off, es), body.instantiate(off + 1, es))
      case Let(domain, value, body) => Let(domain.instantiate(off, es), value.instantiate(off, es), body.instantiate(off + 1, es))
    }

  def instantiate(subst: Map[Param, Level]): Expr =
    this match {
      case _ if subst.isEmpty => this
      case v: Var => v
      case Sort(level) => Sort(level.instantiate(subst))
      case Const(name, levels) => Const(name, levels.map(_.instantiate(subst)))
      case LocalConst(of, name) => LocalConst(of.instantiate(subst), name)
      case App(a, b) => App(a.instantiate(subst), b.instantiate(subst))
      case Lam(domain, body) => Lam(domain.instantiate(subst), body.instantiate(subst))
      case Pi(domain, body) => Pi(domain.instantiate(subst), body.instantiate(subst))
      case Let(domain, value, body) => Let(domain.instantiate(subst), value.instantiate(subst), body.instantiate(subst))
    }

  def univParams: Set[Param] =
    this match {
      case Var(_) => Set()
      case Sort(level) => level.univParams
      case Const(_, levels) => levels.view.flatMap(_.univParams).toSet
      case LocalConst(of, _) => of.ty.univParams
      case App(a, b) => a.univParams union b.univParams
      case Lam(domain, body) => domain.ty.univParams union body.univParams
      case Pi(domain, body) => domain.ty.univParams union body.univParams
      case Let(domain, value, body) => domain.ty.univParams union value.univParams union body.univParams
    }

  def -->:(that: Expr): Expr =
    Pi(Binding(Name.Anon, that, BinderInfo.Default), this)

  override def toString: String = pretty(this)

  override val hashCode: Int = ScalaRunTime._hashCode(this)
}
case class Var(idx: Int) extends Expr(varBound = idx + 1, hasLocals = false)
case class Sort(level: Level) extends Expr(varBound = 0, hasLocals = false) {
}

case class Const(name: Name, levels: Vector[Level]) extends Expr(varBound = 0, hasLocals = false)
case class LocalConst(of: Binding, name: LocalConst.Name = new LocalConst.Name) extends Expr(varBound = 0, hasLocals = true)
case class App(a: Expr, b: Expr)
  extends Expr(
    varBound = math.max(a.varBound, b.varBound),
    hasLocals = a.hasLocals || b.hasLocals
  )
case class Lam(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals
  )
case class Pi(domain: Binding, body: Expr)
  extends Expr(
    varBound = math.max(domain.ty.varBound, body.varBound - 1),
    hasLocals = domain.ty.hasLocals || body.hasLocals
  )
case class Let(domain: Binding, value: Expr, body: Expr)
  extends Expr(
    varBound = math.max(math.max(domain.ty.varBound, value.varBound), body.varBound - 1),
    hasLocals = domain.ty.hasLocals || value.hasLocals || body.hasLocals
  )

object Sort {
  val Prop = Sort(Level.Zero)
}

object LocalConst {
  final class Name {
    override def toString: String = Integer.toHexString(hashCode()).take(4)
  }
}

object Lam {
  def apply(domain: LocalConst, body: Expr): Expr =
    Lam(domain.of, body.abstr(domain))
}
object Lams {
  def apply(domains: Iterable[LocalConst])(body: Expr): Expr =
    domains.foldRight(body)(Lam(_, _))

  def apply(domains: LocalConst*)(body: Expr): Expr =
    apply(domains)(body)
}

object Pi {
  def apply(domain: LocalConst, body: Expr): Expr =
    Pi(domain.of, body.abstr(domain))
}
object Pis {
  def apply(domains: Iterable[LocalConst])(body: Expr): Expr =
    domains.foldRight(body)(Pi(_, _))

  def apply(domains: LocalConst*)(body: Expr): Expr =
    apply(domains)(body)

  def unapply(e: Expr): Some[(List[LocalConst], Expr)] =
    e match {
      case Pi(dom, expr) =>
        val lc = LocalConst(dom)
        expr.instantiate(lc) match {
          case Pis(lcs, head) =>
            Some((lc :: lcs, head))
        }
      case _ => Some((Nil, e))
    }

  def drop(n: Int, e: Expr): Expr =
    e match {
      case _ if n == 0 => e
      case Pi(dom, b) => drop(n - 1, b)
    }
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
