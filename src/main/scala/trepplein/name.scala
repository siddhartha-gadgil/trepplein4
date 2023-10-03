package trepplein

import Name._

import scala.annotation.tailrec
import scala.collection.immutable.ArraySeq
import scala.language.implicitConversions
import scala.runtime.ScalaRunTime

/**
 * A name is a sequence of strings or numerals separated by dots,
 * or an anonymous name.
 *
 */
sealed trait Name extends Product {
  override val hashCode: Int = ScalaRunTime._hashCode(this)

  /**
   * Returns true if the two names are equal.
   *
   * @param n1 the first name
   * @param n2 the second name
   * @return true if the two names are equal
   */
  @tailrec
  private def equals(n1: Name, n2: Name): Boolean =
    (n1 eq n2) || ((n1, n2) match {
      case (Name.Str(p1, l1), Name.Str(p2, l2)) =>
        if (l1 != l2) return false
        equals(p1, p2)
      case (Name.Num(p1, l1), Name.Num(p2, l2)) =>
        if (l1 != l2) return false
        equals(p1, p2)
      case _ => false
    })
  override def equals(that: Any): Boolean =
    that match {
      case that: Name => equals(this, that)
      case _ => false
    }

  // TODO: a more direct implementation may be better
  override def toString: String = {
    val buf: StringBuilder = new StringBuilder
    def write(n: Name): Boolean =
      n match {
        case Anon => false
        case Str(prefix, limb) =>
          if (write(prefix)) buf += '.'
          buf ++= limb
          true
        case Num(prefix, limb) =>
          if (write(prefix)) buf += '.'
          buf.append(limb)
          true
      }
    write(this)
    buf.result()
  }

  def isAnon: Boolean

  def dump: String
}

/**
 * A name can be constructed from a sequence of strings or numerals separated by dots,
 * or an anonymous name.
 *
 */
object Name {
  /**
   * Constructs a name from a sequence of strings.
   *
   * @param limbs the sequence of strings
   * @return the name
   */
  def apply(limbs: String*): Name =
    limbs.foldLeft[Name](Anon)(Str)

  /**
   * A fresh name, i.e., a name that is not in a given set of names.
   *
   * @param suggestion the suggestion for the name
   * @param blacklist the set of names that the fresh name should not be in
   * @return the fresh name
   */
  def fresh(suggestion: Name, blacklist: Set[Name]): Name =
    (suggestion #:: LazyList.from(0).map(i => Name.Num(suggestion, i): Name)).
      filterNot(blacklist).head

  /**
   * An anonymous name.
   */
  case object Anon extends Name {
    def dump = "Name.Anon"

    def isAnon: Boolean = true
  }

  /**
   * A name obtained by appending a string to a prefix.
   *
   * @param prefix the prefix
   * @param limb the string to append
   */
  final case class Str(prefix: Name, limb: String) extends Name {
    def dump = s"""Name.Str(${prefix.dump}, "$limb")"""

    def isAnon: Boolean = false
  }

  /**
   * A name obtained by appending a numeral to a prefix.
   *
   * @param prefix the prefix
   * @param limb the numeral to append
   */
  final case class Num(prefix: Name, limb: Long) extends Name {
    def dump = s"Name.Num(${prefix.dump}, $limb)"

    def isAnon: Boolean = false
  }

  /**
   * Constructs a name from a strings by splitting it at dots.
   *
   * @param s the string
   * @return the name
   */
  implicit def ofString(s: String): Name =
    Name(ArraySeq.unsafeWrapArray(s.split("\\.")): _*)
}
