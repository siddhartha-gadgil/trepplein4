package trepplein

import trepplein.Level.Param

import scala.collection.mutable
import scala.runtime.ScalaRunTime

trait ReductionRuleCache {
  def instantiation(rr: ReductionRule, subst: Map[Param, Level], v: => Expr): Expr
}

private object NoReductionRuleCache extends ReductionRuleCache {
  override def instantiation(rr: ReductionRule, subst: Map[Param, Level], v: => Expr): Expr = v
}

/**
 * A reduction rule. The `apply` method applies the rule to an expression and returns an `Option` of the result
 * together with a list of definitional equalities that need to be checked for the reduction to be valid.
 *
 * @param ctx The context of the rule, i.e., the local declarations that are bound in the rule.
 * @param lhs The general left-hand side of the rule. This can have variables, which are substituted in a reduction.
 * @param rhs The general right-hand side of the rule.
 * @param defEqConstraints The general definitional equalities that need to be checked for the reduction to be valid.
 */
final case class ReductionRule(ctx: Vector[Binding], lhs: Expr, rhs: Expr, defEqConstraints: List[(Expr, Expr)]) {
  require(!lhs.hasLocals)
  require(!rhs.hasLocals)

  val varBound: Int = lhs.varBound
  require(rhs.varBound <= varBound)

  val Apps(Const(lhsConst, _), lhsArgs) = lhs
  val lhsArgsSize: Int = lhsArgs.size

  val major: List[Int] = for ((a, i) <- lhsArgs.zipWithIndex if !a.isInstanceOf[Var]) yield i

  private def applyCore(e: Expr)(implicit cache: ReductionRuleCache = NoReductionRuleCache): Option[(Expr, List[(Expr, Expr)])] = {
    val subst = if (varBound == 0) null else new Array[Expr](varBound)
    val univSubst = mutable.Map[Level.Param, Level]()

    def go(a: Expr, b: Expr): Boolean =
      (a, b) match {
        case (App(a1, a2), App(b1, b2)) => go(a1, b1) && go(a2, b2)
        case (Const(an, als), Const(bn, bls)) if an == bn =>
          als.lazyZip(bls).foreach { (al, bl) => univSubst(al.asInstanceOf[Level.Param]) = bl }
          true
        case (Var(i), _) =>
          subst(i) = b; true
        case (_, _) => false
      }

    if (!go(lhs, e)) return None

    val univSubstMap = univSubst.toMap
    if (varBound == 0) {
      Some(cache.instantiation(this, univSubstMap, rhs.instantiate(univSubstMap)) -> defEqConstraints)
    } else {
      val substVect = subst.toVector
      Some(cache.instantiation(this, univSubstMap, rhs.instantiate(univSubstMap)).instantiate(0, substVect) ->
        defEqConstraints.map { case (i, j) => i.instantiate(0, substVect) -> j.instantiate(0, substVect) })
    }
  }

  def apply(hd: Const, as: List[Expr])(implicit cache: ReductionRuleCache = NoReductionRuleCache): Option[(Expr, List[(Expr, Expr)])] =
    if (as.length < lhsArgsSize) None else {
      val (as1, as2) = as.splitAt(lhsArgsSize)
      applyCore(Apps(hd, as1)) match {
        case Some((red, cs)) => Some(Apps(red, as2) -> cs)
        case None => None
      }
    }

  def apply(e: Expr): Option[(Expr, List[(Expr, Expr)])] = e match {
    case Apps(hd: Const, as) => apply(hd, as)
    case _ => None
  }

  override val hashCode: Int = ScalaRunTime._hashCode(this)
}
object ReductionRule {
  /**
   * Build reduction rules using local constants in place of bindings in the context.
   *
   * @param lcs The local constants to use.
   * @param lhs The general left-hand side of the rule. This can have variables, which are substituted in a reduction.
   * @param rhs The general right-hand side of the rule.
   * @param defEqConstraints The general definitional equalities that need to be checked for the reduction to be valid.
   * @param dummy Dummy implicit to avoid ambiguity with the other `apply` method.
   * @return The reduction rule.
   */
  def apply(lcs: Vector[LocalConst], lhs: Expr, rhs: Expr, defEqConstraints: List[(Expr, Expr)])(implicit dummy: DummyImplicit): ReductionRule =
    ReductionRule(lcs.map(_.of), lhs.abstr(0, lcs), rhs.abstr(0, lcs),
      defEqConstraints.map { case (a, b) => a.abstr(0, lcs) -> b.abstr(0, lcs) })
}

/**
 * A map from constant names to reduction rules and sets of major arguments.
 *
 * @param keyMap The map from constant names to pairs of reduction rules and sets of major arguments.
 */
final class ReductionMap private (keyMap: Map[Name, (Vector[ReductionRule], Set[Int])]) {
  def +(reductionRule: ReductionRule): ReductionMap = {
    val (rs, ms) = keyMap(reductionRule.lhsConst)
    new ReductionMap(keyMap.updated(reductionRule.lhsConst, (rs :+ reductionRule) -> (ms ++ reductionRule.major)))
  }

  def ++(rs: Iterable[ReductionRule]): ReductionMap = rs.foldLeft(this)((t, r) => t + r)

  def major(k: Name): Set[Int] = keyMap(k)._2

  def rules: Vector[ReductionRule] = Vector() ++ keyMap.values.flatMap(_._1)
  def get(k: Name): Vector[ReductionRule] = keyMap(k)._1

  def apply(e: Expr)(implicit cache: ReductionRuleCache = NoReductionRuleCache): Option[(Expr, List[(Expr, Expr)])] =
    e match {
      case Apps(hd @ Const(c, _), as) =>
        val it = keyMap(c)._1.iterator
        while (it.hasNext) {
          val res = it.next().apply(hd, as)
          if (res.isDefined) return res
        }
        None
      case _ => None
    }
}
object ReductionMap {
  def apply() = new ReductionMap(keyMap = Map().withDefaultValue(Vector() -> Set()))
}