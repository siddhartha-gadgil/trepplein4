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

preEnv.declarations.size
import Expr._, tc._
IsDefEq.lhs.toString()
whnf(IsDefEq.lhs.get) == IsDefEq.lhs.get
val Apps(f, as0) = IsDefEq.lhs.get 
val rhs = IsDefEq.rhs.get
rhs.toString()
tc.whnf(rhs).toString()
val Proj(typeName, idx, struct) = rhs
// val Apps(Const(name, _), structParams) = struct
whnf(struct).toString()
struct == whnf(struct)
val Apps(fn, as) = struct
as.size
val Proj(typeName1, idx1, struct1) = fn
struct1 == whnf(struct1)
struct1.toString()
println(struct1.toString())
// env.structIntros(typeName).intro.name
// errorCase.name.toString()
// val Apps(f1, as1) = whnf(struct)
// f1.toString()




Nat.unapply(Const(Name("Nat", "zero"), Vector()))
Nat.unapply(App(Nat.Succ, Nat.Zero))
App(Nat.Succ, Nat.Zero).toString
Nat.Succ.name
Name.ofString("Nat.mul")
Str(Str(Anon, "Nat"), "mul") == Name.ofString("Nat.mul")

preEnv.get(Name.ofString("rfl")).get
preEnv.get(Name.ofString("Nat.decLe")).get.toString
preEnv.get(Name.ofString("Eq.refl")).get.toString


tc.infer(Apps(C("Eq.refl", Level.One), C("Nat"), NatLit(3))).toString
tc.whnf(Apps(C("Eq.refl", Level.One), C("Nat"), NatLit(3))).toString
tc.infer(Apps(C("Eq.refl", Level.One), C("Nat"), NatLit(3))).toString
Apps(C("Eq", Level.One), C("Nat"), NatLit(3), NatLit(3)).toString