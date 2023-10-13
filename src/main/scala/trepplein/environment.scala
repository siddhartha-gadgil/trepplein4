package trepplein

import scala.concurrent.{ ExecutionContext, Future }
import scala.language.implicitConversions
import scala.util.Try

/**
 * A declaration such as a definition, theorem, or axiom. Inductive type
 * definitions introduce multiple declarations.
 *
 * @param name
 *   The name of the declaration
 * @param univParams
 *   The universe parameters of the declaration
 * @param ty
 *   The type of the declaration
 * @param height
 *   The height of the declaration. A constant used should have lower height.
 * @param builtin
 *   Whether the declaration is built-in
 */
final case class Declaration(
    name: Name,
    univParams: Vector[Level.Param],
    ty: Expr,
    height: Int = 0,
    builtin: Boolean = false) {

  /**
   * Partial check of the validity of the declaration, namely that the name is
   * not already in the environment and that the type is well-formed. It is
   * also checked that there are no local variables in the type.
   *
   * @param env The pre-environment
   */
  def check(env: PreEnvironment): Unit = check(env, new TypeChecker(env))
  /**
   * Partial check of the validity of the declaration, namely that the name is
   * not already in the environment and that the type is well-formed. It is
   * also checked that there are no local variables in the type.
   *
   * @param env The pre-environment
   * @param tc The type-checker
   */
  def check(env: PreEnvironment, tc: TypeChecker): Unit = {
    require(!env.declarations.contains(name))
    require(ty.univParams.subsetOf(univParams.toSet))
    require(!ty.hasVars)
    require(!ty.hasLocals)
    tc.inferUniverseOfType(ty)
  }
}

/**
 * An environment modification compiled in a pre-environment. In particular
 * this has a `check` method that checks the modification is valid, for example
 * type-checking is done and it is checked that any name introduced is not
 * already in the environment.
 */
trait CompiledModification {

  /**
   * Check the modification is valid, including type-checking and avoiding name
   * collisions.
   */
  def check(): Unit

  /**
   * The declarations introduced by the modification.
   *
   * @return
   *   The declarations
   */
  def decls: Seq[Declaration]

  /**
   * The reduction rules introduced by the modification.
   *
   * @return
   *   The reduction rules
   */
  def rules: Seq[ReductionRule]

  def structIntros: Map[Name, Declaration] 
}

/**
 * An environment modification, such as a definition, axiom, or theorem.
 */
trait Modification {

  /**
   * The name of the modification.
   *
   * @return
   *   The name
   */
  def name: Name

  /**
   * The compilation of the modification in a pre-environment, including
   * introduction of a `check` function.
   *
   * @param env
   *   The pre-environment
   * @return
   *   The compiled modification
   */
  def compile(env: PreEnvironment): CompiledModification
}
object Modification {

  /**
   * Implicitly convert an axiom to a modification.
   *
   * @param axiom
   *   The axiom
   * @return
   *   The modification
   */
  implicit def ofAxiom(axiom: Declaration): Modification =
    AxiomMod(axiom.name, axiom.univParams, axiom.ty)
}

/**
 * The environment modification associated with an axiom.
 *
 * @param name
 *   The name of the axiom
 * @param univParams
 *   The universe parameters of the axiom
 * @param ty
 *   The type of the axiom
 */
final case class AxiomMod(name: Name, univParams: Vector[Level.Param], ty: Expr)
  extends Modification {
  def compile(env: PreEnvironment): CompiledModification =
    new CompiledModification {
      val decl = Declaration(name, univParams, ty)
      def check(): Unit = decl.check(env)
      def decls: Seq[Declaration] = Seq(decl)
      def rules: Seq[ReductionRule] = Seq()
      def structIntros: Map[Name,Declaration] = Map()
    }
}
final case class DefMod(
    name: Name,
    univParams: Vector[Level.Param],
    ty: Expr,
    value: Expr) extends Modification {
  def compile(env: PreEnvironment): CompiledModification =
    new CompiledModification {
      val height: Int =
        value.constants.view
          .flatMap(env.get)
          .map(_.height)
          .fold(0)(math.max) + 1

      // declaration of the constant
      val decl: Declaration = Declaration(name, univParams, ty, height = height)

      // reduction rule: the constant is reduced to its value.
      val rule: ReductionRule =
        ReductionRule(Vector[Binding](), Const(name, univParams), value, List())

      // check: uniqueness of name and type-checking
      def check(): Unit = {
        val tc = new TypeChecker(env)
        decl.check(env, tc)
        require(!value.hasVars)
        require(!value.hasLocals)
        tc.checkType(value, ty, s"definition $name")
      }
      def decls: Seq[Declaration] = Seq(decl)
      def rules: Seq[ReductionRule] = Seq(rule)
      def structIntros: Map[Name,Declaration] = Map()
    }
}

final case class StructMod(name: Name, decl: Declaration)
  extends Modification {
  def compile(env: PreEnvironment): CompiledModification =
    new CompiledModification {
      def check(): Unit = require(env.declarations.values.toSet.contains(decl))
      def decls: Seq[Declaration] = Seq(decl)
      def rules: Seq[ReductionRule] = Seq()
      def structIntros: Map[Name,Declaration] = Map(name -> decl)
    }
}

case class EnvironmentUpdateError(mod: Modification, msg: String) {
  override def toString = s"${mod.name}: $msg"
}

/**
 * A pre-environment, which is an environment that is being built. It contains
 * a map from names to declarations, a map from names to reduction rules, and a
 * list of proof obligations that need to be checked before the environment can
 * be finalized.
 *
 * @param declarations The declarations in the environment
 * @param reductions The reduction rules in the environment
 * @param proofObligations The proof obligations that need to be checked before
 */
sealed class PreEnvironment protected (
    val declarations: Map[Name, Declaration],
    val reductions: ReductionMap,
    val structIntros : Map[Name, Declaration],
    val proofObligations: List[Future[Option[EnvironmentUpdateError]]]) {

  /**
   * Get the declaration with the given name, if it exists.
   *
   * @param name The name
   * @return The declaration, if it exists
   */
  def get(name: Name): Option[Declaration] =
    declarations.get(name)

  /**
   * Get the declaration with the given name, throwing an exception if it does
   * not exist.
   *
   * @param name The name
   * @return The declaration
   */
  def apply(name: Name): Declaration =
    declarations(name)

  /**
   * Get the value of the declaration, provided that it is a definition.
   *
   * @param name The name
   * @return The value of the definition, if it exists.
   */
  def value(name: Name): Option[Expr] =
    reductions.get(name).find(_.lhs.isInstanceOf[Const]).map(_.rhs)

  /**
   * Check whether the declaration is an axiom.
   *
   * @param name The name
   * @return Whether the declaration is an axiom
   */
  def isAxiom(name: Name): Boolean =
    !this(name).builtin && value(name).isEmpty

  /**
   * Add declarations for the declarations in the compiled modification (without checking).
   *
   * @param mod The compiled modification
   * @return The new pre-environment
   */
  private def addDeclsFor(mod: CompiledModification): Map[Name, Declaration] =
    declarations ++ mod.decls.view.map(d => d.name -> d)

  /**
   * Add declarations for the declarations in the compiled modification returning a future.
   * Checking is spawned as a task which is returned and added to the proof obligations.
   *
   * @param mod The compiled modification
   * @param executionContext The execution context (for running futures)
   * @return A future of a possible error while compiling the modification and the new pre-environment.
   */
  def addWithFuture(mod: Modification)(implicit executionContext: ExecutionContext): (Future[Option[EnvironmentUpdateError]], PreEnvironment) = {
    val compiled: CompiledModification = mod.compile(this)
    val checkingTask: Future[Option[EnvironmentUpdateError]] = Future {
      Try(compiled.check()).failed.toOption.map(t =>
        EnvironmentUpdateError(mod, t.getMessage))
    }
    checkingTask -> new PreEnvironment(
      addDeclsFor(compiled),
      reductions ++ compiled.rules,
      structIntros ++ compiled.structIntros,
      checkingTask :: proofObligations)
  }

  /**
   * Add declarations for the declarations in the compiled modification with checks (blocking).
   *
   * @param mod The compiled modification
   * @return The new pre-environment
   */
  def addNow(mod: Modification): PreEnvironment = {
    val compiled = mod.compile(this)
    compiled.check()
    new PreEnvironment(
      addDeclsFor(compiled),
      reductions ++ compiled.rules,
      structIntros ++ compiled.structIntros,
      proofObligations)
  }

  /**
   * Add declarations for the declarations in the compiled modification without checks,
   * but with the check added as a proof obligation.
   *
   * @param mod The compiled modification
   * @param executionContext The execution context (for running futures)
   * @return The new pre-environment
   */
  def add(mod: Modification)(implicit executionContext: ExecutionContext): PreEnvironment =
    addWithFuture(mod)._2

  /**
   * Obtain an environment or an error in the future, depending on whether all the
   * proof obligations are satisfied or at least one fails.
   *
   * @param executionContext The execution context (for running futures)
   * @return A future of either an error or an environment
   */
  def force(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Environment.force(this)
}

/**
 * An environment, where everything is type-checked and consistent, and where
 * all proof obligations have been checked.
 *
 * @param declarations The declarations in the environment
 * @param reductionMap The reduction rules in the environment
 */
final class Environment private (
    declarations: Map[Name, Declaration],
    reductionMap: ReductionMap,
    structIntros : Map[Name, Declaration]) extends PreEnvironment(declarations, reductionMap, structIntros, Nil)
object Environment {
  /**
   * From a pre-environment, obtain an environment or an error in the future, depending on whether all the
   * proof obligations are satisfied or at least one fails.
   *
   * @param preEnvironment The pre-environment
   * @param executionContext The execution context (for running futures)
   * @return
   */
  def force(preEnvironment: PreEnvironment)(implicit executionContext: ExecutionContext): Future[Either[Seq[EnvironmentUpdateError], Environment]] =
    Future.sequence(preEnvironment.proofObligations).map(_.flatten).map {
      case Nil =>
        Right(
          new Environment(
            preEnvironment.declarations,
            preEnvironment.reductions,
            preEnvironment.structIntros))
      case exs => Left(exs)
    }

  /**
   * The empty environment.
   *
   * @return The empty environment
   */
  def default: Environment = new Environment(Map(), ReductionMap(), Map())
}
