import trepplein._, Name._

// Checking whether anonymous names are equal
Name.Anon == Name.Anon

Name.Anon eq Name.Anon

val exportedCommands = TextExportParser.parseFile("/home/gadgil/Downloads/Init.export")
val modifications = exportedCommands.collect { case ExportedModification(mod) => mod }
val env0 = Environment.default

val preEnv = modifications.take(372).foldLeft[PreEnvironment](env0)(_.addNow(_))
val breaker = modifications(372).asInstanceOf[DefMod]
breaker.name
val breakerConsts = modifications(372).asInstanceOf[DefMod].value.constants
val defNames = modifications.take(372).collect { case d : DefMod => d.name }
defNames.contains(Name.ofString("Lean.TSyntaxArray.raw"))
import scala.util._
val errCase = Try(preEnv.addNow(modifications(372).asInstanceOf[DefMod]))
val axiomNames = modifications.take(372).collect { case d : AxiomMod => d.name }
axiomNames.contains(Name.ofString("Lean.TSyntaxArray.raw"))