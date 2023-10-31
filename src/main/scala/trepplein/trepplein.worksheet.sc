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
// @Decidable.rec.{0}
//   (@LT.lt.{0} @Nat @instLTNat (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//     @UInt32.size)
//   (fun (x :
//       @Decidable
//         (@LT.lt.{0} @Nat @instLTNat
//           (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//           @UInt32.size)) ↦ (fun (inst_InitPrelude_hyg1444 :
//         @Decidable
//           (@LT.lt.{0} @Nat @instLTNat
//             (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//             @UInt32.size)) ↦ @LT.lt.{0} @Nat @instLTNat
//       (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size) x)
//   (fun (h :
//       @Not
//         (@LT.lt.{0} @Nat @instLTNat
//           (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//           @UInt32.size)) ↦ (fun (h_InitPrelude_hyg1465 :
//         @Not
//           (@LT.lt.{0} @Nat @instLTNat
//             (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//             @UInt32.size)) ↦ (fun (h_0 :
//           @Not
//             (@LT.lt.{0} @Nat @instLTNat
//               (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//               @UInt32.size)) ↦ @absurd.{0}
//         (@Eq.{1} @Bool
//           (@Decidable.decide
//             (@LT.lt.{0} @Nat @instLTNat
//               (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
//             (@Nat.decLt (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//               @UInt32.size)) @Bool.true)
//         (@LT.lt.{0} @Nat @instLTNat
//           (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
//         (@Eq.refl.{1} @Bool @Bool.true)
//         (@ne_true_of_eq_false
//           (@Decidable.decide
//             (@LT.lt.{0} @Nat @instLTNat
//               (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
//             (@Nat.decLt (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//               @UInt32.size))
//           (@decide_eq_false
//             (@LT.lt.{0} @Nat @instLTNat
//               (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
//             (@Nat.decLt (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//               @UInt32.size) h_0))) h_InitPrelude_hyg1465) h)
//   (fun (h :
//       @LT.lt.{0} @Nat @instLTNat (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//         @UInt32.size) ↦ (fun (h_InitPrelude_hyg1466 :
//         @LT.lt.{0} @Nat @instLTNat
//           (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127))
//           @UInt32.size) ↦ (fun (h_0 :
//           @LT.lt.{0} @Nat @instLTNat
//             (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size) ↦ h_0)
//       h_InitPrelude_hyg1466) h)
//   (@Nat.decLt (@OfNat.ofNat.{0} @Nat 127 (@instOfNatNat 127)) @UInt32.size)
tc.reduceOneStep(Const(Name.ofString("Nat.decLe"), Vector()))(tc.Transparency(true)).toString
tc.whnf(Const(Name.ofString("Nat.decLe"), Vector())).toString
Try(tc.infer(errorCase.value))
Nat.unapply(Const(Name("Nat", "zero"), Vector()))
Nat.unapply(App(Nat.Succ, Nat.Zero))
App(Nat.Succ, Nat.Zero).toString
Nat.Succ.name
Name.ofString("Nat.mul")
Str(Str(Anon, "Nat"), "mul") == Name.ofString("Nat.mul")
