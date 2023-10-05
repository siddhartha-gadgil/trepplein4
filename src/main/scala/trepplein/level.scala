package trepplein

import trepplein.Level.{ IMax, Max, _ }

import scala.annotation.tailrec
import scala.language.implicitConversions

/**
 * A level is a non-negative integer, a parameter, or a max or imax of two
 * levels. This represents the universe level of a universe.
 *
 * The level `0` is special as types having this level are ''propositions''. As
 * universally quantified propositions are also propositions, we need to use
 * the impredecative maximum `imax` in place of `max` for defining types of
 * (dependent) functions.
 */
sealed trait Level {
  def dump: String

  /**
   * Instantiate level parameters using the given substitution.
   *
   * @param subst
   *   the substitution
   * @return
   *   the instantiated level
   */
  def instantiate(subst: Map[Param, Level]): Level
  /**
   * Returns the set of level parameters occurring in this level.
   *
   * @return
   *   the set of level parameters
   */

  def univParams: Set[Param]

  /**
   * Simplifies this level. Successors and maxes are simplified recursively.
   * IMax is simplified to Zero if the second argument simplifies to zero, and
   * to a max if the second argument is a successor (so known to be not zero).
   *
   * @return the simplified level
   */
  def simplify: Level

  /**
   * Checks whether this level is known to be less than or equal to the given
   * one.
   *
   * @param that
   *   the other level
   * @return
   *   true if this level is known to be less than or equal to the given one.
   */
  def <==(that: Level): Boolean = isLeqCore(this.simplify, that.simplify, 0)

  /**
   * Checks whether this level is known to be equal to the given one after
   * simplification.
   *
   * @param that
   *   the other level
   * @return
   *   true if this level is known to be equal to the given one
   */
  def ===(that: Level): Boolean = {
    val a = this.simplify
    val b = that.simplify
    isLeqCore(a, b, 0) && isLeqCore(b, a, 0)
  }

  /**
   * Checks whether this level is known to be `Zero` after simplification.
   *
   * @return
   *   true if this level is `Zero`
   */
  def isZero: Boolean = this <== Zero

  /**
   * Checks whether this level is known to be not `Zero` after simplification.
   *
   * @return
   *   true if this level is known to be not `Zero`.
   */
  def isNonZero: Boolean = Succ(Zero) <== this

  /**
   * Checks whether we cannot rule out this level being `Zero`.
   *
   * @return
   *   true if we cannot rule out this level being `Zero`.
   */
  def maybeZero: Boolean = !isNonZero

  /**
   * Checks whether we cannot rule out this level being not `Zero`.
   *
   * @return
   *   true if we cannot rule out this level being not `Zero`.
   */
  def maybeNonZero: Boolean = !isZero
}

/**
 * A level is a non-negative integer, a parameter, or a max or imax of two
 * levels. This represents the universe level of a universe.
 *
 * The level `0` is special as types having this level are ''propositions''. As
 * universally quantified propositions are also propositions, we need to use
 * the impredecative maximum `imax` in place of `max` for defining types of
 * (dependent) functions.
 */
object Level {
  case object Zero extends Level {
    def dump: String = "Level.Zero"

    def instantiate(subst: Map[Param, Level]): Level = Zero

    def univParams: Set[Param] = Set()

    def simplify: Level = Zero

  }
  case class Succ(level: Level) extends Level {
    def dump: String = s"Level.Succ(${level.dump})"

    def instantiate(subst: Map[Param, Level]): Level = Succ(level.instantiate(subst))

    def univParams: Set[Param] = level.univParams

    def simplify: Level = Succ(level.simplify)

  }
  case class Max(a: Level, b: Level) extends Level {
    def dump: String = s"Level.Max(${a.dump}, ${b.dump})"

    def instantiate(subst: Map[Param, Level]): Level = Max(a.instantiate(subst), b.instantiate(subst))

    def univParams: Set[Param] = a.univParams union b.univParams

    def simplify: Level = Max.combining(a.simplify, b.simplify)

  }
  case class IMax(a: Level, b: Level) extends Level {
    def dump: String = s"Level.IMax(${a.dump}, ${b.dump})"

    def instantiate(subst: Map[Param, Level]): Level = IMax(a.instantiate(subst), b.instantiate(subst))

    def univParams: Set[Param] = a.univParams union b.univParams

    def simplify: Level =
      b.simplify match {
        case b_ @ Succ(_) => Max.combining(a.simplify, b_)
        case Zero => Zero
        case b_ => IMax(a.simplify, b_)
      }

  }
  case class Param(param: Name) extends Level { p =>
    def dump: String = s"Level.Param(${param.dump})"

    def instantiate(subst: Map[Param, Level]): Level = subst.getOrElse(p, p)

    def univParams: Set[Param] = Set(p)

    def simplify: Level = p

  }

  object Max {

    /**
     * Combines two levels using the max constructor. We have simplifications
     * when both levels are successors or one of them is zero.
     *
     * @param l1
     *   the first level
     * @param l2
     *   the second level
     * @return
     */
    def combining(l1: Level, l2: Level): Level =
      (l1, l2) match {
        case (Succ(l1_), Succ(l2_)) => Succ(combining(l1_, l2_))
        case (Zero, _) => l2
        case (_, Zero) => l1
        case (_, _) => Max(l1, l2)
      }
  }

  /**
   * Level corresponding to the natural number `n`.
   *
   * @param n
   *   the natural number
   * @return
   *   the level
   */
  implicit def ofNat(n: Int): Level = Offset(n, Zero)

  /**
   * Level offset (using `Succ`) from a given one by a given natural number.
   */
  object Offset {

    /**
     * Maximally offset description of a level. The base must be a parameter,
     * max or imax.
     *
     * @param level
     * @return
     *   the offset and the base
     */
    def unapply(level: Level): Some[(Int, Level)] = {
      @tailrec
      def decompose(i: Int, level: Level): (Int, Level) =
        level match {
          case Succ(l) => decompose(i + 1, l)
          case _ => (i, level)
        }
      Some(decompose(0, level))
    }

    /**
     * Level offset (using `Succ`) from a given one by a given natural number.
     *
     * @param i
     *   the offset
     * @param level
     *   the level
     * @return
     *   the offset level
     */
    @tailrec
    def apply(i: Int, level: Level): Level =
      if (i == 0) level else apply(i - 1, Succ(level))
  }

  /** l1 <= l2 + diff */
  private def isLeqCore(l1: Level, l2: Level, diff: Int): Boolean = {
    def split(p: Param): Boolean =
      Seq(Map(p -> Succ(p)), Map(p -> Zero)).forall(subst =>
        isLeqCore(
          l1.instantiate(subst).simplify,
          l2.instantiate(subst).simplify,
          diff))

    (l1, l2) match {
      // simplification
      case (Zero, _) if diff >= 0 => true
      case (_, Zero) if diff < 0 => false
      case (Zero, Zero) =>
        diff >= 0 // not needed, just to convince the compiler
      case (Param(i), Param(j)) => i == j && diff >= 0
      case (Param(_), Zero) => false
      case (Zero, Param(_)) => diff >= 0
      case (Succ(l1_), _) => isLeqCore(l1_, l2, diff - 1)
      case (_, Succ(l2_)) => isLeqCore(l1, l2_, diff + 1)

      // descend left
      case (Max(a, b), _) => isLeqCore(a, l2, diff) && isLeqCore(b, l2, diff)

      // descend right
      case (Param(_) | Zero, Max(a, b)) =>
        isLeqCore(l1, a, diff) || isLeqCore(l1, b, diff)

      // imax
      case (IMax(a1, b1), IMax(a2, b2)) if a1 == a2 && b1 == b2 => true
      case (IMax(_, p @ Param(_)), _) => split(p)
      case (_, IMax(_, p @ Param(_))) => split(p)
      case (IMax(a, IMax(b, c)), _) =>
        isLeqCore(Max(IMax(a, c), IMax(b, c)), l2, diff)
      case (IMax(a, Max(b, c)), _) =>
        isLeqCore(Max(IMax(a, b), IMax(a, c)).simplify, l2, diff)
      case (_, IMax(a, IMax(b, c))) =>
        isLeqCore(l1, Max(IMax(a, c), IMax(b, c)), diff)
      case (_, IMax(a, Max(b, c))) =>
        isLeqCore(l1, Max(IMax(a, b), IMax(a, c)).simplify, diff)
      case _ => throw new IllegalArgumentException(s"cannot compare $l1 and $l2") // Porting note: This case was left unmatched in the original code.
    }
  }
}
