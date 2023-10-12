Nat.gcd_self: (@Nat.rec.{max 1 1}
  (fun (t : @Nat) ↦ @PProd.{1 max 1 1} (#3 t) (@Nat.below.{1} #3 t))
  (@PProd.mk.{1 max 1 1} (#2 @Nat.zero) @PUnit.{max 1 1}
    (#0 @Nat.zero @PUnit.unit.{max 1 1}) @PUnit.unit.{max 1 1})
  (fun (n : @Nat)
    (n_ih : @PProd.{1 max 1 1} (#3 n) (@Nat.below.{1} #3 n)) ↦ @PProd.mk.{1
    max 1
    1} (#4 (@Nat.succ n))
    (@PProd.{max 1 1 max 1 1} (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n))
      @PUnit.{max 1 1})
    (#2 (@Nat.succ n)
      (@PProd.mk.{max 1 1 max 1 1}
        (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
        @PUnit.unit.{max 1 1}))
    (@PProd.mk.{max 1 1 max 1 1}
      (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
      @PUnit.unit.{max 1 1})) #1).0 (of class trepplein.Proj)
Nat.zero_mod: (#0).0 (of class trepplein.Proj)
Nat.zero_sub: (#0).0 (of class trepplein.Proj)
False.elim: wrong type:  fun (x_InitPrelude_hyg150 : False) ↦ C  :  Sort u
inferred type:  ∀ (x_InitPrelude_hyg150 : False) , Sort u
Sort u  !=def  ∀ (x_InitPrelude_hyg150 : False) , Sort u
stuck on:  Sort u ∀ (x_InitPrelude_hyg150 : False) , Sort u
Nat.le_zero_eq: (@Nat.rec.{max 1 1}
  (fun (t : @Nat) ↦ @PProd.{1 max 1 1} (#3 t) (@Nat.below.{1} #3 t))
  (@PProd.mk.{1 max 1 1} (#2 @Nat.zero) @PUnit.{max 1 1}
    (#0 @Nat.zero @PUnit.unit.{max 1 1}) @PUnit.unit.{max 1 1})
  (fun (n : @Nat)
    (n_ih : @PProd.{1 max 1 1} (#3 n) (@Nat.below.{1} #3 n)) ↦ @PProd.mk.{1
    max 1
    1} (#4 (@Nat.succ n))
    (@PProd.{max 1 1 max 1 1} (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n))
      @PUnit.{max 1 1})
    (#2 (@Nat.succ n)
      (@PProd.mk.{max 1 1 max 1 1}
        (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
        @PUnit.unit.{max 1 1}))
    (@PProd.mk.{max 1 1 max 1 1}
      (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
      @PUnit.unit.{max 1 1})) #1).0 (of class trepplein.Proj)
Nat.sub_self: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
congrFun: wrong type:  fun (x_InitPrelude_hyg388 : (∀ (x : α) , β x))
  (h_InitPrelude_hyg389 : Eq f x_InitPrelude_hyg388) ↦ Eq
  (f a._@.Init.WF._hyg.504)
  (x_InitPrelude_hyg388 a._@.Init.WF._hyg.504)  :  ∀ (a_InitPrelude_hyg170 :
    (∀ (x : α) , β x)) , Prop
inferred type:  ∀ (x_InitPrelude_hyg388 : (∀ (x : α) , β x))
  (h_InitPrelude_hyg389 : Eq f x_InitPrelude_hyg388) , Prop
Prop  !=def  ∀ (h_InitPrelude_hyg389 : Eq f x._@.Init.Prelude._hyg.388) , Prop
stuck on:  Prop ∀ (h_InitPrelude_hyg389 :
    Eq f x._@.Init.Prelude._hyg.388) , Prop
Nat.ne_of_beq_eq_false: (@Nat.rec.{max 1 1}
  (fun (t : @Nat) ↦ @PProd.{1 max 1 1} (#3 t) (@Nat.below.{1} #3 t))
  (@PProd.mk.{1 max 1 1} (#2 @Nat.zero) @PUnit.{max 1 1}
    (#0 @Nat.zero @PUnit.unit.{max 1 1}) @PUnit.unit.{max 1 1})
  (fun (n : @Nat)
    (n_ih : @PProd.{1 max 1 1} (#3 n) (@Nat.below.{1} #3 n)) ↦ @PProd.mk.{1
    max 1
    1} (#4 (@Nat.succ n))
    (@PProd.{max 1 1 max 1 1} (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n))
      @PUnit.{max 1 1})
    (#2 (@Nat.succ n)
      (@PProd.mk.{max 1 1 max 1 1}
        (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
        @PUnit.unit.{max 1 1}))
    (@PProd.mk.{max 1 1 max 1 1}
      (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
      @PUnit.unit.{max 1 1})) #1).0 (of class trepplein.Proj)
Nat.eq_of_beq_eq_true: (@Nat.rec.{max 1 1}
  (fun (t : @Nat) ↦ @PProd.{1 max 1 1} (#3 t) (@Nat.below.{1} #3 t))
  (@PProd.mk.{1 max 1 1} (#2 @Nat.zero) @PUnit.{max 1 1}
    (#0 @Nat.zero @PUnit.unit.{max 1 1}) @PUnit.unit.{max 1 1})
  (fun (n : @Nat)
    (n_ih : @PProd.{1 max 1 1} (#3 n) (@Nat.below.{1} #3 n)) ↦ @PProd.mk.{1
    max 1
    1} (#4 (@Nat.succ n))
    (@PProd.{max 1 1 max 1 1} (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n))
      @PUnit.{max 1 1})
    (#2 (@Nat.succ n)
      (@PProd.mk.{max 1 1 max 1 1}
        (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
        @PUnit.unit.{max 1 1}))
    (@PProd.mk.{max 1 1 max 1 1}
      (@PProd.{1 max 1 1} (#4 n) (@Nat.below.{1} #4 n)) @PUnit.{max 1 1} n_ih
      @PUnit.unit.{max 1 1})) #1).0 (of class trepplein.Proj)
of_eq_true: wrong type:  fun (x_InitSimpLemmas_hyg17 : Prop)
  (h_InitSimpLemmas_hyg18 :
    Eq True
      x_InitSimpLemmas_hyg17) ↦ x_InitSimpLemmas_hyg17  :  ∀ (a_InitPrelude_hyg170 :
    Prop) , Prop
inferred type:  ∀ (x_InitSimpLemmas_hyg17 : Prop)
  (h_InitSimpLemmas_hyg18 : Eq True x_InitSimpLemmas_hyg17) , Prop
Prop  !=def  ∀ (h_InitSimpLemmas_hyg18 :
    Eq True x._@.Init.SimpLemmas._hyg.17) , Prop
stuck on:  Prop ∀ (h_InitSimpLemmas_hyg18 :
    Eq True x._@.Init.SimpLemmas._hyg.17) , Prop
Nat.gcd: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Gcd.0.Nat.gcdF: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.mod_lt: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Iff.mp: (#0).0 (of class trepplein.Proj)
Nat.mod_eq_of_lt: wrong type:  fun (x_InitDataNatDiv_hyg1343 : Nat)
  (h_InitDataNatDiv_hyg1344 :
    Eq
      (ite (And (LT.lt (OfNat.ofNat n) b) (LE.le b a))
        (HMod.hMod (HSub.hSub a b) b) a) x_InitDataNatDiv_hyg1343) ↦ Eq
  x_InitDataNatDiv_hyg1343 a  :  ∀ (a_InitPrelude_hyg170 : Nat) , Prop
inferred type:  ∀ (x_InitDataNatDiv_hyg1343 : Nat)
  (h_InitDataNatDiv_hyg1344 :
    Eq
      (ite (And (LT.lt (OfNat.ofNat n) b) (LE.le b a))
        (HMod.hMod (HSub.hSub a b) b) a) x_InitDataNatDiv_hyg1343) , Prop
Prop  !=def  ∀ (h_InitDataNatDiv_hyg1344 :
    Eq
      (ite (And (LT.lt (OfNat.ofNat n) b) (LE.le b a))
        (HMod.hMod (HSub.hSub a b) b) a)
      x._@.Init.Data.Nat.Div._hyg.1343) , Prop
stuck on:  Prop ∀ (h_InitDataNatDiv_hyg1344 :
    Eq
      (ite (And (LT.lt (OfNat.ofNat n) b) (LE.le b a))
        (HMod.hMod (HSub.hSub a b) b) a)
      x._@.Init.Data.Nat.Div._hyg.1343) , Prop
Nat.le_antisymm: (#0).0 (of class trepplein.Proj)
Nat.lt_of_le_of_lt: (#0).0 (of class trepplein.Proj)
Nat.le_antisymm.match_1: (#0).0 (of class trepplein.Proj)
Nat.lt_trans: (#0).0 (of class trepplein.Proj)
Nat.le_step: (#0).0 (of class trepplein.Proj)
Nat.lt_or_ge: (#0).0 (of class trepplein.Proj)
Eq.mp: wrong type:  fun (x_InitPrelude_hyg297 : Sort u)
  (x_InitPrelude_hyg296 :
    Eq α
      x_InitPrelude_hyg297) ↦ x_InitPrelude_hyg297  :  ∀ (a_InitPrelude_hyg170 :
    Sort u) , Sort u
inferred type:  ∀ (x_InitPrelude_hyg297 : Sort u)
  (x_InitPrelude_hyg296 : Eq α x_InitPrelude_hyg297) , Sort u
Sort u  !=def  ∀ (x_InitPrelude_hyg296 :
    Eq α x._@.Init.Prelude._hyg.297) , Sort u
stuck on:  Sort u ∀ (x_InitPrelude_hyg296 :
    Eq α x._@.Init.Prelude._hyg.297) , Sort u
Nat.mod_eq_sub_mod: wrong type:  fun (x_InitDataNatDiv_hyg1390 : Nat)
  (h_InitDataNatDiv_hyg1391 : Eq (OfNat.ofNat n) x_InitDataNatDiv_hyg1390) ↦ Eq
  (HMod.hMod a x_InitDataNatDiv_hyg1390)
  (HMod.hMod (HSub.hSub a x_InitDataNatDiv_hyg1390)
    x_InitDataNatDiv_hyg1390)  :  ∀ (a_InitPrelude_hyg170 : Nat) , Prop
inferred type:  ∀ (x_InitDataNatDiv_hyg1390 : Nat)
  (h_InitDataNatDiv_hyg1391 :
    Eq (OfNat.ofNat n) x_InitDataNatDiv_hyg1390) , Prop
Prop  !=def  ∀ (h_InitDataNatDiv_hyg1391 :
    Eq (OfNat.ofNat n) x._@.Init.Data.Nat.Div._hyg.1390) , Prop
stuck on:  Prop ∀ (h_InitDataNatDiv_hyg1391 :
    Eq (OfNat.ofNat n) x._@.Init.Data.Nat.Div._hyg.1390) , Prop
Nat.modCore_eq_mod: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Div.0.Nat.modCore._eq_1: (@invImage.{1 1} (@PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) @Nat
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      @PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) ↦ @PSigma.casesOn.{1 1 1} @Nat
    (fun (x : @Nat) ↦ @Nat)
    (fun (x : @PSigma.{1 1} @Nat (fun (x_0 : @Nat) ↦ @Nat)) ↦ @Nat)
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        @Nat) ↦ @SizeOf.sizeOf.{1} @Nat @instSizeOfNat x_InitDataNatDiv_hyg779))
  (@instWellFoundedRelation.{1} @Nat @instSizeOfNat)).0 (of class trepplein.Proj)
WellFounded.fixFEq.proof_1: wrong type:  fun (x : α) (acx : Acc r x) ↦ Eq (WellFounded.fixF F x acx)
  (F x
    (fun (y : α) (p : r y x) ↦ WellFounded.fixF F y
      (Acc.inv acx p)))  :  ∀ (a_InitPrelude_hyg170 : α) , Prop
inferred type:  ∀ (x : α) (acx : Acc r x) , Prop
Prop  !=def  ∀ (acx : Acc r a._@.Init.Prelude._hyg.170) , Prop
stuck on:  Prop ∀ (acx : Acc r a._@.Init.Prelude._hyg.170) , Prop
Eq.trans: wrong type:  fun (x_InitPrelude_hyg284 : α)
  (h_InitPrelude_hyg285 : Eq b x_InitPrelude_hyg284) ↦ Eq a
  x_InitPrelude_hyg284  :  ∀ (a_InitPrelude_hyg170 : α) , Prop
inferred type:  ∀ (x_InitPrelude_hyg284 : α)
  (h_InitPrelude_hyg285 : Eq b x_InitPrelude_hyg284) , Prop
Prop  !=def  ∀ (h_InitPrelude_hyg285 : Eq b x._@.Init.Prelude._hyg.284) , Prop
stuck on:  Prop ∀ (h_InitPrelude_hyg285 :
    Eq b x._@.Init.Prelude._hyg.284) , Prop
Nat.sub_zero: (#0).0 (of class trepplein.Proj)
Nat.eq_zero_or_pos: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.zero_lt_succ: (#0).0 (of class trepplein.Proj)
Nat.zero_add.match_1: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Eq.mpr: wrong type:  fun (x_InitCore_hyg5079 : Sort u)
  (h_InitCore_hyg5080 :
    Eq β x_InitCore_hyg5079) ↦ x_InitCore_hyg5079  :  ∀ (a_InitPrelude_hyg170 :
    Sort u) , Sort u
inferred type:  ∀ (x_InitCore_hyg5079 : Sort u)
  (h_InitCore_hyg5080 : Eq β x_InitCore_hyg5079) , Sort u
Sort u  !=def  ∀ (h_InitCore_hyg5080 : Eq β x._@.Init.Core._hyg.5079) , Sort u
stuck on:  Sort u ∀ (h_InitCore_hyg5080 :
    Eq β x._@.Init.Core._hyg.5079) , Sort u
Nat.div.inductionOn: (#0).0 (of class trepplein.Proj)
Nat.div.inductionOn._unary: (#0).0 (of class trepplein.Proj)
Nat.mod: (#0).0 (of class trepplein.Proj)
Nat.modCore._unary: (@invImage.{1 1} (@PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) @Nat
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      @PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) ↦ @PSigma.casesOn.{1 1 1} @Nat
    (fun (x : @Nat) ↦ @Nat)
    (fun (x : @PSigma.{1 1} @Nat (fun (x_0 : @Nat) ↦ @Nat)) ↦ @Nat)
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        @Nat) ↦ @SizeOf.sizeOf.{1} @Nat @instSizeOfNat x_InitDataNatDiv_hyg779))
  (@instWellFoundedRelation.{1} @Nat @instSizeOfNat)).0 (of class trepplein.Proj)
Nat.lt_of_lt_of_le: (#0).0 (of class trepplein.Proj)
Nat.sub_lt: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.succ_sub_succ_eq_sub: (#0).0 (of class trepplein.Proj)
congrArg: wrong type:  fun (x_InitPrelude_hyg322 : α)
  (h_InitPrelude_hyg323 : Eq a₁ x_InitPrelude_hyg322) ↦ Eq (f a₁)
  (f x_InitPrelude_hyg322)  :  ∀ (a_InitPrelude_hyg170 : α) , Prop
inferred type:  ∀ (x_InitPrelude_hyg322 : α)
  (h_InitPrelude_hyg323 : Eq a₁ x_InitPrelude_hyg322) , Prop
Prop  !=def  ∀ (h_InitPrelude_hyg323 : Eq a₁ a._@.Init.WF._hyg.798) , Prop
stuck on:  Prop ∀ (h_InitPrelude_hyg323 : Eq a₁ a._@.Init.WF._hyg.798) , Prop
Nat.sub_le: (#0).0 (of class trepplein.Proj)
Nat.pred_le: (#0).0 (of class trepplein.Proj)
Nat.le_refl: (#0).0 (of class trepplein.Proj)
Nat.lt_succ_of_le: (#0).0 (of class trepplein.Proj)
Nat.lt_irrefl: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_self: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.sub_lt.match_1: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
And.casesOn: wrong type:  motive  :  Sort u
inferred type:  ∀ (t : And a b) , Sort u
Sort u  !=def  ∀ (t : And a b) , Sort u
stuck on:  Sort u ∀ (t : And a b) , Sort u
Nat.sub: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.mul.match_1: wrong type:  h_1 x._@.Init.Prelude._hyg.2940.2959  :  (fun (x : Nat) ↦ motive
    x._@.Init.Prelude._hyg.2940.2959 x) Nat.zero
inferred type:  motive x._@.Init.Prelude._hyg.2940.2959 n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Sub.sub: (#0).0 (of class trepplein.Proj)
HSub.hSub: (#0).0 (of class trepplein.Proj)
Nat.decLt: (#0).0 (of class trepplein.Proj)
Nat.ble_eq_true_of_le: (#0).0 (of class trepplein.Proj)
Nat.ble_succ_eq_true: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.ble_succ_eq_true.match_1: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.ble_self_eq_true: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.not_succ_le_self.match_1: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.ble_eq_true_of_le.match_1: (#0).0 (of class trepplein.Proj)
Nat.le_of_ble_eq_true: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.le_of_ble_eq_true.match_1: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Eq.casesOn: wrong type:  motive  :  ∀ (a_InitPrelude_hyg170 : α) , Sort u
inferred type:  ∀ (a_InitPrelude_hyg170 : α)
  (t : Eq a._@.Init.Prelude._hyg.168 a_InitPrelude_hyg170) , Sort u
Sort u  !=def  ∀ (t :
    Eq a._@.Init.Prelude._hyg.168 a._@.Init.Prelude._hyg.170) , Sort u
stuck on:  Sort u ∀ (t :
    Eq a._@.Init.Prelude._hyg.168 a._@.Init.Prelude._hyg.170) , Sort u
And.left: (#0).0 (of class trepplein.Proj)
And.right: (#0).1 (of class trepplein.Proj)
Nat.modCore._unary.proof_1: (@invImage.{1 1} (@PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) @Nat
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      @PSigma.{1 1} @Nat (fun (x : @Nat) ↦ @Nat)) ↦ @PSigma.casesOn.{1 1 1} @Nat
    (fun (x : @Nat) ↦ @Nat)
    (fun (x : @PSigma.{1 1} @Nat (fun (x_0 : @Nat) ↦ @Nat)) ↦ @Nat)
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        @Nat) ↦ @SizeOf.sizeOf.{1} @Nat @instSizeOfNat x_InitDataNatDiv_hyg779))
  (@instWellFoundedRelation.{1} @Nat @instSizeOfNat)).0 (of class trepplein.Proj)
SizeOf.sizeOf: (#0).0 (of class trepplein.Proj)
Nat.mod.match_1: (#0).0 (of class trepplein.Proj)
Mod.mod: (#0).0 (of class trepplein.Proj)
HMod.hMod: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Gcd.0.Nat.gcdF.match_1: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.lt_wfRel.proof_1: (#0).0 (of class trepplein.Proj)
Nat.eq_or_lt_of_le: (#0).0 (of class trepplein.Proj)
Nat.pred_le_pred: (#0).0 (of class trepplein.Proj)
Nat.le_succ: (#0).0 (of class trepplein.Proj)
Nat.le_trans: (#0).0 (of class trepplein.Proj)
Nat.le_trans.match_1: (#0).0 (of class trepplein.Proj)
Nat.pred_le_pred.match_1: (#0).0 (of class trepplein.Proj)
Nat.pow.match_1: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.zero_le: (#0).0 (of class trepplein.Proj)
Nat.succ_le_succ: (#0).0 (of class trepplein.Proj)
PProd.fst: (#0).0 (of class trepplein.Proj)
Add.add: (#0).0 (of class trepplein.Proj)
HAdd.hAdd: (#0).0 (of class trepplein.Proj)
Nat.succ_le_succ.match_1: (#0).0 (of class trepplein.Proj)
eq_of_heq: wrong type:  fun (x_InitPrelude_hyg488 : Sort u)
  (x_InitPrelude_hyg487 : x_InitPrelude_hyg488)
  (x_InitPrelude_hyg486 : HEq a x_InitPrelude_hyg487) ↦ ∀ (h :
    Eq α x_InitPrelude_hyg488) , Eq (cast h a) x_InitPrelude_hyg487  :  ∀ {β :
    Sort u} (a_InitPrelude_hyg417 : β) , Prop
inferred type:  ∀ (x_InitPrelude_hyg488 : Sort u)
  (x_InitPrelude_hyg487 : x_InitPrelude_hyg488)
  (x_InitPrelude_hyg486 : HEq a x_InitPrelude_hyg487) , Prop
Prop  !=def  ∀ (x_InitPrelude_hyg486 : HEq a x._@.Init.Prelude._hyg.487) , Prop
stuck on:  Prop ∀ (x_InitPrelude_hyg486 :
    HEq a x._@.Init.Prelude._hyg.487) , Prop
cast: wrong type:  fun (x_InitPrelude_hyg297 : Sort u)
  (x_InitPrelude_hyg296 :
    Eq α
      x_InitPrelude_hyg297) ↦ x_InitPrelude_hyg297  :  ∀ (a_InitPrelude_hyg170 :
    Sort u) , Sort u
inferred type:  ∀ (x_InitPrelude_hyg297 : Sort u)
  (x_InitPrelude_hyg296 : Eq α x_InitPrelude_hyg297) , Sort u
Sort u  !=def  ∀ (x_InitPrelude_hyg296 :
    Eq α x._@.Init.Prelude._hyg.297) , Sort u
stuck on:  Sort u ∀ (x_InitPrelude_hyg296 :
    Eq α x._@.Init.Prelude._hyg.297) , Sort u
Eq.symm: wrong type:  fun (x_InitPrelude_hyg261 : α)
  (h_InitPrelude_hyg262 : Eq a x_InitPrelude_hyg261) ↦ Eq x_InitPrelude_hyg261
  a  :  ∀ (a_InitPrelude_hyg170 : α) , Prop
inferred type:  ∀ (x_InitPrelude_hyg261 : α)
  (h_InitPrelude_hyg262 : Eq a x_InitPrelude_hyg261) , Prop
Prop  !=def  ∀ (h_InitPrelude_hyg262 : Eq a x._@.Init.Prelude._hyg.261) , Prop
stuck on:  Prop ∀ (h_InitPrelude_hyg262 :
    Eq a x._@.Init.Prelude._hyg.261) , Prop
Nat.brecOn: (@Nat.rec.{max 1 u}
  (fun (t : @Nat) ↦ @PProd.{u max 1 u} (#3 t) (@Nat.below.{u} #3 t))
  (@PProd.mk.{u max 1 u} (#2 @Nat.zero) @PUnit.{max 1 u}
    (#0 @Nat.zero @PUnit.unit.{max 1 u}) @PUnit.unit.{max 1 u})
  (fun (n : @Nat)
    (n_ih : @PProd.{u max 1 u} (#3 n) (@Nat.below.{u} #3 n)) ↦ @PProd.mk.{u
    max 1
    u} (#4 (@Nat.succ n))
    (@PProd.{max 1 u max 1 u} (@PProd.{u max 1 u} (#4 n) (@Nat.below.{u} #4 n))
      @PUnit.{max 1 u})
    (#2 (@Nat.succ n)
      (@PProd.mk.{max 1 u max 1 u}
        (@PProd.{u max 1 u} (#4 n) (@Nat.below.{u} #4 n)) @PUnit.{max 1 u} n_ih
        @PUnit.unit.{max 1 u}))
    (@PProd.mk.{max 1 u max 1 u}
      (@PProd.{u max 1 u} (#4 n) (@Nat.below.{u} #4 n)) @PUnit.{max 1 u} n_ih
      @PUnit.unit.{max 1 u})) #1).0 (of class trepplein.Proj)
Acc.recOn: wrong type:  motive  :  ∀ (a_InitPrelude_hyg170 : α) , Sort u_1
inferred type:  ∀ (a_InitWF_hyg10 : α) (t : Acc r a_InitWF_hyg10) , Sort u_1
Sort u_1  !=def  ∀ (t : Acc r a._@.Init.Prelude._hyg.170) , Sort u_1
stuck on:  Sort u_1 ∀ (t : Acc r a._@.Init.Prelude._hyg.170) , Sort u_1
Or.casesOn: wrong type:  motive  :  Prop
inferred type:  ∀ (t : Or a b) , Prop
Prop  !=def  ∀ (t : Or a b) , Prop
stuck on:  Prop ∀ (t : Or a b) , Prop
Nat.not_lt_zero: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_zero: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.not_succ_le_zero.match_2: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.not_succ_le_zero.match_1: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
Nat.le.casesOn: wrong type:  motive  :  ∀ (a_InitPrelude_hyg3756 : Nat) , Prop
inferred type:  ∀ (a_InitPrelude_hyg3756 : Nat)
  (t : Nat.le n a_InitPrelude_hyg3756) , Prop
Prop  !=def  ∀ (t : Nat.le n m) , Prop
stuck on:  Prop ∀ (t : Nat.le n m) , Prop
Nat.not_succ_le_zero.match_3: requirement failed: incorrect number of universe parameters: @Nat.{1}, expected Vector()
LE.le: (#0).0 (of class trepplein.Proj)
LT.lt: (#0).0 (of class trepplein.Proj)
absurd: wrong type:  fun (x_InitPrelude_hyg164 : False) ↦ b  :  Sort v
inferred type:  ∀ (x_InitPrelude_hyg164 : False) , Sort v
Sort v  !=def  ∀ (x_InitPrelude_hyg164 : False) , Sort v
stuck on:  Sort v ∀ (x_InitPrelude_hyg164 : False) , Sort v
OfNat.ofNat: (#0).0 (of class trepplein.Proj)
WellFoundedRelation.wf: (#0).1 (of class trepplein.Proj)
_private.Init.WF.0.InvImage.accAux.proof_1: wrong type:  fun {b : β} (ac : Acc r b) ↦ ∀ (x : α)
  (a_InitWF_hyg749 : Eq (f x) b) , Acc (InvImage r f)
  x  :  ∀ (a_InitPrelude_hyg170 : β) , Prop
inferred type:  ∀ {b : β} (ac : Acc r b) , Prop
Prop  !=def  ∀ (ac : Acc r a._@.Init.Prelude._hyg.170) , Prop
stuck on:  Prop ∀ (ac : Acc r a._@.Init.Prelude._hyg.170) , Prop
Eq.ndrec: wrong type:  fun (x_InitPrelude_hyg197 : α)
  (x_InitPrelude_hyg196 : Eq a x_InitPrelude_hyg197) ↦ motive
  x_InitPrelude_hyg197  :  ∀ (a_InitPrelude_hyg170 : α) , Sort u1
inferred type:  ∀ (x_InitPrelude_hyg197 : α)
  (x_InitPrelude_hyg196 : Eq a x_InitPrelude_hyg197) , Sort u1
Sort u1  !=def  ∀ (x_InitPrelude_hyg196 :
    Eq a x._@.Init.Prelude._hyg.197) , Sort u1
stuck on:  Sort u1 ∀ (x_InitPrelude_hyg196 :
    Eq a x._@.Init.Prelude._hyg.197) , Sort u1
WellFoundedRelation.rel: (#0).0 (of class trepplein.Proj)
WellFounded.apply.proof_1: wrong type:  fun (x_InitWF_hyg225 : WellFounded r) ↦ ∀ (x_InitWF_hyg224 :
    α) , Acc r x_InitWF_hyg224  :  Prop
inferred type:  ∀ (x_InitWF_hyg225 : WellFounded r) , Prop
Prop  !=def  ∀ (x_InitWF_hyg225 : WellFounded r) , Prop
stuck on:  Prop ∀ (x_InitWF_hyg225 : WellFounded r) , Prop
WellFounded.fixF: wrong type:  fun (x : α) (a : Acc r x) ↦ C x  :  ∀ (a_InitPrelude_hyg170 :
    α) , Sort v
inferred type:  ∀ (x : α) (a : Acc r x) , Sort v
Sort v  !=def  ∀ (a : Acc r a._@.Init.Prelude._hyg.170) , Sort v
stuck on:  Sort v ∀ (a : Acc r a._@.Init.Prelude._hyg.170) , Sort v
