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
errorCase.ty.toString
val tc = new TypeChecker(preEnv)
tc.whnf(errorCase.ty).toString
tc.whnf(errorCase.value)
preEnv.get(Name.ofString("UInt32.size")).get
errorCase.ty
val unint32sizeDecl = preEnv.get(Name.ofString("UInt32.size")).get
val uint32size = Const(Name.ofString("UInt32.size"), Vector())
tc.reduceOneStep(uint32size)(tc.Transparency(true)).toString
print(tc.whnf(errorCase.value).toString)
tc.reduceOneStep(Const(Name.ofString("Nat.decLe"), Vector()))(tc.Transparency(true)).toString
tc.whnf(Const(Name.ofString("Nat.decLe"), Vector())).toString
tc.whnf(Const(Name.ofString("Nat.decLt"), Vector())).toString
Try(tc.infer(errorCase.value))


IsDefEq.lhs.toString()
tc.whnf(IsDefEq.lhs.get) == IsDefEq.lhs.get
val Apps(f, as0) = IsDefEq.lhs.get 
val Const(n,_) = f
val major = tc.env.reductions.major(n)
import tc._
val as =
              for ((a, i) <- as0.zipWithIndex)
                yield if (major(i)) whnf(a) else a
as.size == as0.size
as.size 
as.dropRight(1) == as0.dropRight(1)
as.last.toString()
as0.last.toString()
val Apps(f1, as1) = as.last
f == f1
val bl = as1.last
bl.toString()
whnf (bl).toString()

Nat.unapply(Const(Name("Nat", "zero"), Vector()))
Nat.unapply(App(Nat.Succ, Nat.Zero))
App(Nat.Succ, Nat.Zero).toString
Nat.Succ.name
Name.ofString("Nat.mul")
Str(Str(Anon, "Nat"), "mul") == Name.ofString("Nat.mul")
