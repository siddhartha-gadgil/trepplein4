import trepplein._, Name._, scala.util._

val exportedCommands = TextExportParser.parseFile("/home/gadgil/Downloads/Init.export")
val modifications = exportedCommands.collect { case ExportedModification(mod) => mod }
val env0 = Environment.default

@annotation.tailrec
final def tillError(env: PreEnvironment, mods: LazyList[Modification]): (PreEnvironment, LazyList[Modification]) = mods match {
  case head #:: tail => Try(env.addNow(head)) match {
    case Success(env1) => tillError(env1, tail)
    case Failure(_) => (env, mods)
  }
  case LazyList() => (env, LazyList())
  }

val (preEnv, tailMods) = tillError(env0, modifications) 
val errorCase = tailMods.head.asInstanceOf[DefMod]
errorCase.name.toString
errorCase.value.toString()
Expr.natLits(errorCase.value)