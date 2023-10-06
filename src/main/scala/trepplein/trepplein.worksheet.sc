import trepplein._, Name._

// Checking whether anonymous names are equal
Name.Anon == Name.Anon

Name.Anon eq Name.Anon

val n1 = Name.Anon
val n2 = Name.Anon

n1 == n2

Lam.apply _

object nat { // From the test
  val nat = Const("nat", Vector())
  val natZero = Const(Name("nat", "zero"), Vector())
  val natSucc = Const(Name("nat", "succ"), Vector())

  val natAdd = Const(Name("nat", "add"), Vector())
  def addDef = {
    val x = LocalConst(Binding("x", nat, BinderInfo.Default))
    val y = LocalConst(Binding("y", nat, BinderInfo.Default))
    Lam(
      x,
      Apps(
        Const(Name("nat", "rec"), Vector(1)),
        Lam(y, nat),
        x,
        Lam(y, natSucc)
      )
    )
  }

  val eqDef = {
    val u = Level.Param("u")
    val alpha = LocalConst(Binding("A", Sort(u), BinderInfo.Default))
    val x = LocalConst(Binding("x", alpha, BinderInfo.Default))
    val y = LocalConst(Binding("y", alpha, BinderInfo.Default))
    IndMod(
      "eq",
      Vector(u),
      Pi(alpha, alpha -->: alpha -->: Sort.Prop),
      2,
      Vector(
        Name("eq", "refl") -> Pis(alpha, x)(
          Apps(Const("eq", Vector(u)), alpha, x, x)
        )
      )
    )
  }

  def env_ =
    Environment.default
      .addNow(eqDef)
      .addNow(IndMod(nat.name, Vector(), Sort(1),
        0, Vector(natZero.name -> nat, natSucc.name -> (nat -->: nat))))
      .addNow(DefMod(natAdd.name, Vector(), nat -->: nat -->: nat, addDef))

}

import nat._
nat.eqDef
val natInd = IndMod(nat.nat.name, Vector(), Sort(1),
        0, Vector(natZero.name -> nat.nat, natSucc.name -> (nat.nat -->: nat.nat)))
val natIndComp = natInd.compile (Environment.default)
print (natIndComp.motiveType)

natIndComp.rules.size
natIndComp.compiledIntros.size

print (natIndComp.rules(0).lhs)
print (natIndComp.rules(0).rhs)
print (natIndComp.rules(1).lhs)
natIndComp.rules(1).lhs
print (natIndComp.rules(1).rhs)
natIndComp.rules(1).rhs
natIndComp.rules.map(_.defEqConstraints.size)
nat.env_.declarations.keys
natIndComp.params
natIndComp.indices

natIndComp.introDecls.size
natIndComp.introDecls.map(_.name)

val eqIndComp = eqDef.compile (Environment.default)

eqIndComp.rules.size
eqIndComp.compiledIntros.size
println(eqIndComp.rules(0).lhs)
println(eqIndComp.rules(0).rhs)
eqIndComp.rules(0).ctx.size
for (i <- eqIndComp.rules(0).ctx) println(i)
eqIndComp.rules(0).defEqConstraints.size
for (i <- eqIndComp.rules(0).defEqConstraints) println(i)
eqIndComp.compiledIntros.map(_.arguments)

eqIndComp.kIntroRule

natIndComp.compiledIntros.map(_.arguments)
println(natIndComp.compiledIntros(0).ty)
println(natIndComp.compiledIntros(0).arguments)
println(natIndComp.compiledIntros(1).ty)

println(natIndComp.compiledIntros(1).arguments.size)
println(natIndComp.compiledIntros(0).introType)
println(natIndComp.compiledIntros(1).introType)
println(natIndComp.compiledIntros(0).introTyArgs)
println(natIndComp.compiledIntros(1).introTyArgs)
println(natIndComp.compiledIntros(0).ihs)
println(natIndComp.compiledIntros(1).ihs)
print(natIndComp.compiledIntros(1).ihs(0).of.ty)
natIndComp.compiledIntros(1).argInfos
natIndComp.compiledIntros(0).argInfos
natIndComp.compiledIntros(1).argInfos(0).toOption.get._1.size
natIndComp.compiledIntros(1).ihs

println(natIndComp.compiledIntros(1).minorPremise.of.ty)
println(natIndComp.compiledIntros(0).minorPremise.of.ty)
println(natIndComp.compiledIntros(0).minorPremise)

println(natIndComp.majorPremise.of.ty)
println(natIndComp.majorPremise)


println(natIndComp.compiledIntros(1).ihs)

import natIndComp._
tc.NormalizedPis.instantiate(compiledIntros(1).ty, params)
compiledIntros(1).arguments



natIndComp.compiledIntros.map(_.arguments)