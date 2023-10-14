Nat.gcd_self: java.lang.IllegalArgumentException: wrong type:  eq_self (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237)  :  Eq
  (Eq (Nat.gcd (OfNat.ofNat n) (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237))
    (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237)) True
inferred type:  Eq
  (Eq (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237)
    (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237)) True
Acc.rec (fun (y x : Nat) ↦ WellFoundedRelation.rel y x)
  (fun (x : Nat)
    (h_InitWF_hyg413 :
      (∀ (y : Nat)
        (a_InitWF_hyg16 :
          (fun (y_0 x_0 : Nat) ↦ WellFoundedRelation.rel y_0 x_0) y x) , Acc
        (fun (y_0 x_0 : Nat) ↦ WellFoundedRelation.rel y_0 x_0) y))
    (ih :
      (∀ (y : Nat)
        (a_InitWF_hyg16 :
          (fun (y_0 x_0 : Nat) ↦ WellFoundedRelation.rel y_0 x_0) y
            x) , (fun (y_0 : Nat) ↦ (fun (y_1 : Nat) ↦ ∀ (n : Nat) , Nat) y_0)
        y)) ↦ _private.Init.Data.Nat.Gcd.0.Nat.gcdF x ih) (OfNat.ofNat n)
  (WellFounded.apply Nat.gcd.proof_1 (OfNat.ofNat n))
  (Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237)  !=def  Nat.succ
  t._@.Init.Data.Nat.Gcd._hyg.237
stuck on:  n Nat.succ t._@.Init.Data.Nat.Gcd._hyg.237
Nat.zero_mod: java.lang.IllegalArgumentException: wrong type:  eq_self (OfNat.ofNat n)  :  Eq
  (Eq (ite False (HMod.hMod (OfNat.ofNat n) b) (OfNat.ofNat n)) (OfNat.ofNat n))
  True
inferred type:  Eq (Eq (OfNat.ofNat n) (OfNat.ofNat n)) True
n  !=def  n
stuck on:  n n
Nat.zero_sub: java.lang.IllegalArgumentException: wrong type:  Eq.refl (HSub.hSub (OfNat.ofNat n) Nat.zero)  :  (fun (n :
      Nat) ↦ Eq (HSub.hSub (OfNat.ofNat n) n) (OfNat.ofNat n)) Nat.zero
inferred type:  Eq (HSub.hSub (OfNat.ofNat n) Nat.zero)
  (HSub.hSub (OfNat.ofNat n) Nat.zero)
n  !=def  n
stuck on:  n n
Nat.le_zero_eq: java.lang.IllegalArgumentException: wrong type:  Eq.refl Bool.true  :  Eq
  (Decidable.decide (LE.le (OfNat.ofNat n) (OfNat.ofNat n))) Bool.true
inferred type:  Eq Bool.true Bool.true
Decidable.rec (LE.le (OfNat.ofNat n) (OfNat.ofNat n))
  (fun (h :
      Not
        (LE.le (OfNat.ofNat n) (OfNat.ofNat n))) ↦ (fun (x_InitPrelude_hyg1211 :
        Not (LE.le (OfNat.ofNat n) (OfNat.ofNat n))) ↦ Bool.false) h)
  (fun (h :
      LE.le (OfNat.ofNat n) (OfNat.ofNat n)) ↦ (fun (x_InitPrelude_hyg1218 :
        LE.le (OfNat.ofNat n) (OfNat.ofNat n)) ↦ Bool.true) h)
  (Nat.decLe (OfNat.ofNat n) (OfNat.ofNat n))  !=def  Bool.true
stuck on:  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg3669 : Nat) (f : Nat.below x_InitPrelude_hyg3669)
          (x_InitPrelude_hyg3670 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3669
          x_InitPrelude_hyg3670
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3242 : Nat)
            (x_InitPrelude_hyg3741 :
              Nat.below (Nat.succ n_InitPrelude_hyg3242)) ↦ Bool.false)
          (fun (n m : Nat)
            (x_InitPrelude_hyg3741 : Nat.below (Nat.succ n)) ↦ PProd.fst
            (PProd.fst x_InitPrelude_hyg3741) m) f) Nat.zero PUnit.unit)
      PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg3669 : Nat) ↦ ∀ (a_InitPrelude_hyg3665 :
                Nat) , Bool) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg3669 : Nat) (f : Nat.below x_InitPrelude_hyg3669)
          (x_InitPrelude_hyg3670 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3669
          x_InitPrelude_hyg3670
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3242 : Nat)
            (x_InitPrelude_hyg3741 :
              Nat.below (Nat.succ n_InitPrelude_hyg3242)) ↦ Bool.false)
          (fun (n_0 m : Nat)
            (x_InitPrelude_hyg3741 : Nat.below (Nat.succ n_0)) ↦ PProd.fst
            (PProd.fst x_InitPrelude_hyg3741) m) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 (OfNat.ofNat n) Bool.true
Nat.sub_self: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit) (x_InitDataNatBasic_hyg2798 : Nat.below n) ↦ Eq.mpr
  (id
    (Eq.ndrec
      (Eq.refl (Eq (HSub.hSub (OfNat.ofNat n) (OfNat.ofNat n)) (OfNat.ofNat n)))
      (Nat.sub_zero (OfNat.ofNat n)))) (Eq.refl (OfNat.ofNat n))  :  Unit →
(fun (x_InitDataNatBasic_hyg27242735 : Nat) ↦ ∀ (x_InitDataNatBasic_hyg2798 :
      Nat.below x_InitDataNatBasic_hyg27242735) , Eq
    (HSub.hSub x_InitDataNatBasic_hyg27242735 x_InitDataNatBasic_hyg27242735)
    (OfNat.ofNat n)) n
inferred type:  Unit → (∀ (x_InitDataNatBasic_hyg2798 : Nat.below n) , Eq
  (HSub.hSub (OfNat.ofNat n) (OfNat.ofNat n)) (OfNat.ofNat n))
n  !=def  n
stuck on:  n n
_private.Init.Data.Nat.Gcd.0.Nat.gcdF: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit)
  (x_InitDataNatGcd_hyg31 :
    (∀ (x : Nat) (a_InitDataNatGcd_hyg11 : LT.lt x (OfNat.ofNat n))
      (n : Nat) , Nat)) (a_0 : Nat) ↦ a_0  :  Unit →
(fun (x_InitDataNatGcd_hyg26 : Nat) ↦ ∀ (a_InitDataNatGcd_hyg5 :
      (∀ (x : Nat) (a_InitDataNatGcd_hyg11 : LT.lt x x_InitDataNatGcd_hyg26)
        (n_0 : Nat) , Nat)) (n : Nat) , Nat) n
inferred type:  ∀ (a : Unit)
  (x_InitDataNatGcd_hyg31 :
    (∀ (x : Nat) (a_InitDataNatGcd_hyg11 : LT.lt x (OfNat.ofNat n))
      (n : Nat) , Nat)) (a_0 : Nat) , Nat
n  !=def  n
stuck on:  n n
Nat.mod_lt: java.lang.IllegalArgumentException: wrong type:  fun (x y : Nat) (h : And (LT.lt (OfNat.ofNat n) y) (LE.le y x))
  (h_0 :
    (∀ (a_InitDataNatDiv_hyg1418 : GT.gt y (OfNat.ofNat n)) , LT.lt
      (HMod.hMod (HSub.hSub x y) y) y))
  (h_1 : GT.gt y (OfNat.ofNat n)) ↦ Nat.div_rec_lemma.match_1
  (fun (h_InitDataNatDiv_hyg1617 :
      And (LT.lt (OfNat.ofNat n) y) (LE.le y x)) ↦ LT.lt (HMod.hMod x y) y) h
  (fun (left_InitDataNatDiv_hyg1626 : LT.lt (OfNat.ofNat n) y)
    (h_2 : LE.le y x) ↦ Eq.mpr
    (id (Eq.ndrec (Eq.refl (LT.lt (HMod.hMod x y) y)) (Nat.mod_eq_sub_mod h_2)))
    (h_0 h_1))  :  ∀ (x y : Nat)
  (a_InitDataNatDiv_hyg233 : And (LT.lt (OfNat.ofNat n) y) (LE.le y x))
  (a_InitDataNatDiv_hyg247 :
    (fun (x_0 : Nat) {y_0 : Nat} ↦ ∀ (a_InitDataNatDiv_hyg1418 :
          GT.gt y_0 (OfNat.ofNat n)) , LT.lt (HMod.hMod x_0 y_0) y_0)
      (HSub.hSub x y)) , (fun (x_0 : Nat)
    {y_0 : Nat} ↦ ∀ (a_InitDataNatDiv_hyg1418 :
      GT.gt y_0 (OfNat.ofNat n)) , LT.lt (HMod.hMod x_0 y_0) y_0) x
inferred type:  ∀ (x y : Nat) (h : And (LT.lt (OfNat.ofNat n) y) (LE.le y x))
  (h_0 :
    (∀ (a_InitDataNatDiv_hyg1418 : GT.gt y (OfNat.ofNat n)) , LT.lt
      (HMod.hMod (HSub.hSub x y) y) y))
  (h_1 : GT.gt y (OfNat.ofNat n)) , (fun (h_InitDataNatDiv_hyg1617 :
      And (LT.lt (OfNat.ofNat n) y) (LE.le y x)) ↦ LT.lt (HMod.hMod x y) y) h
n  !=def  n
stuck on:  n n
Nat.lt_or_ge: java.lang.IllegalArgumentException: wrong type:  Nat.zero_le n  :  GE.ge n Nat.zero
inferred type:  LE.le (OfNat.ofNat n) n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.modCore_eq_mod: java.lang.IllegalArgumentException: wrong type:  hle  :  LE.le y (OfNat.ofNat n)
inferred type:  LE.le y Nat.zero
n  !=def  Nat.zero
stuck on:  n Nat.zero
Nat.sub_zero: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ rfl  :  ∀ (n : Nat) , Eq
  (HSub.hSub n (OfNat.ofNat n)) n
inferred type:  ∀ (n : Nat) , Eq (HSub.hSub n (OfNat.ofNat n))
  (HSub.hSub n (OfNat.ofNat n))
n  !=def  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n
stuck on:  n (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n
Nat.eq_zero_or_pos: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Or.inl rfl  :  Unit →
(fun (x_InitDataNatBasic_hyg33113322 : Nat) ↦ Or
    (Eq x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))
    (GT.gt x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))) n
inferred type:  ∀ (a : Unit) , Or (Eq (OfNat.ofNat n) (OfNat.ofNat n))
  (GT.gt (OfNat.ofNat n) (OfNat.ofNat n))
n  !=def  n
stuck on:  n n
Nat.zero_add.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.mod: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.839.858
  (Nat.succ x._@.Init.Prelude._hyg.4249.4260)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.839.858
  (HAdd.hAdd x._@.Init.Prelude._hyg.4249.4260 (OfNat.ofNat n))
Nat.succ x._@.Init.Prelude._hyg.4249.4260  !=def  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 x._@.Init.Prelude._hyg.4249.4260
stuck on:  Nat.succ x._@.Init.Prelude._hyg.4249.4260 (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 x._@.Init.Prelude._hyg.4249.4260
Nat.sub_lt: java.lang.IllegalArgumentException: wrong type:  h1  :  LT.lt (OfNat.ofNat n) n
inferred type:  LT.lt (OfNat.ofNat n) (OfNat.ofNat n)
n  !=def  n
stuck on:  n n
Nat.succ_sub_succ_eq_sub: java.lang.IllegalArgumentException: wrong type:  fun (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 :
    Nat.below n) ↦ x_InitPrelude_hyg3059  :  ∀ (x_InitPrelude_hyg3059 :
    Nat) , (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
      Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
      Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg3059 n
inferred type:  ∀ (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 : Nat.below n) , Nat
n  !=def  n
stuck on:  n n
Nat.sub_le: java.lang.IllegalArgumentException: wrong type:  Nat.le_refl (HSub.hSub n (OfNat.ofNat n))  :  (fun (m :
      Nat) ↦ LE.le (HSub.hSub n m) n) Nat.zero
inferred type:  LE.le (HSub.hSub n (OfNat.ofNat n))
  (HSub.hSub n (OfNat.ofNat n))
n  !=def  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n
stuck on:  n (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg5385 : Nat) (f : Nat.below x_InitPrelude_hyg5385)
          (x_InitPrelude_hyg5384 : Nat) ↦ Nat.mul.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg5384
          x_InitPrelude_hyg5385
          (fun (x_InitPrelude_hyg3059 : Nat)
            (x_InitPrelude_hyg5431 : Nat.below n) ↦ x_InitPrelude_hyg3059)
          (fun (a b : Nat)
            (x_InitPrelude_hyg5431 : Nat.below (Nat.succ b)) ↦ Nat.pred
            (PProd.fst (PProd.fst x_InitPrelude_hyg5431) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n
Nat.pred_le: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Nat.le.refl  :  Unit →
(fun (x_InitDataNatBasic_hyg23662377 : Nat) ↦ LE.le
    (Nat.pred x_InitDataNatBasic_hyg23662377) x_InitDataNatBasic_hyg23662377)
  Nat.zero
inferred type:  ∀ (a : Unit) , Nat.le (Nat.pred Nat.zero) (Nat.pred Nat.zero)
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.not_succ_le_self: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg4791 : Nat.below n) ↦ Nat.not_succ_le_zero
  (OfNat.ofNat n)  :  Unit → (fun (x_InitPrelude_hyg47564767 :
      Nat) ↦ ∀ (x_InitPrelude_hyg4791 :
      Nat.below x_InitPrelude_hyg47564767) , Not
    (LE.le (Nat.succ x_InitPrelude_hyg47564767) x_InitPrelude_hyg47564767)) n
inferred type:  Unit → (∀ (x_InitPrelude_hyg4791 : Nat.below n)
  (a_InitPrelude_hyg3820 :
    LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)) , False)
n  !=def  n
stuck on:  n n
Nat.sub_lt.match_1: java.lang.IllegalArgumentException: wrong type:  h1  :  LT.lt (OfNat.ofNat n) n
inferred type:  LT.lt (OfNat.ofNat n) (OfNat.ofNat n)
n  !=def  n
stuck on:  n n
Nat.sub: java.lang.IllegalArgumentException: wrong type:  fun (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 :
    Nat.below n) ↦ x_InitPrelude_hyg3059  :  ∀ (x_InitPrelude_hyg3059 :
    Nat) , (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
      Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
      Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg3059 n
inferred type:  ∀ (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 : Nat.below n) , Nat
n  !=def  n
stuck on:  n n
Nat.mul.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 x._@.Init.Prelude._hyg.2940.2959  :  (fun (x : Nat) ↦ motive
    x._@.Init.Prelude._hyg.2940.2959 x) Nat.zero
inferred type:  motive x._@.Init.Prelude._hyg.2940.2959 n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.ble_succ_eq_true: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5094.5121) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5094.5121)
  Bool.true
n  !=def  n
stuck on:  n n
Nat.ble_succ_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5137) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5137)
  Bool.true
n  !=def  n
stuck on:  n n
Nat.ble_self_eq_true: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg5066 : Nat.below n) ↦ rfl  :  Unit →
(fun (x_InitPrelude_hyg50425053 : Nat) ↦ ∀ (x_InitPrelude_hyg5066 :
      Nat.below x_InitPrelude_hyg50425053) , Eq
    (Nat.ble x_InitPrelude_hyg50425053 x_InitPrelude_hyg50425053) Bool.true) n
inferred type:  Unit → (∀ (x_InitPrelude_hyg5066 : Nat.below n) , Eq
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n))
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n)))
n  !=def  n
stuck on:  n n
Nat.not_succ_le_self.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.le_of_ble_eq_true: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n n._@.Init.Prelude._hyg.4984) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) n._@.Init.Prelude._hyg.4984)
  Bool.true
n  !=def  n
stuck on:  n n
Nat.le_of_ble_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n x._@.Init.Prelude._hyg.5000) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5000)
  Bool.true
n  !=def  n
stuck on:  n n
Nat.mod.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.869 (Nat.succ n._@.Init.Data.Nat.Div._hyg.886)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.869
  (HAdd.hAdd n._@.Init.Data.Nat.Div._hyg.886 (OfNat.ofNat n))
Nat.succ n._@.Init.Data.Nat.Div._hyg.886  !=def  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n._@.Init.Data.Nat.Div._hyg.886
stuck on:  Nat.succ n._@.Init.Data.Nat.Div._hyg.886 (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 n._@.Init.Data.Nat.Div._hyg.886
_private.Init.Data.Nat.Gcd.0.Nat.gcdF.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.lt_wfRel.proof_1: java.lang.IllegalArgumentException: wrong type:  Acc.intro (OfNat.ofNat n)
  (fun (y_InitWF_hyg992 : Nat)
    (h : Nat.lt y_InitWF_hyg992 (OfNat.ofNat n)) ↦ absurd h
    (Nat.not_lt_zero y_InitWF_hyg992))  :  (fun (n : Nat) ↦ Acc Nat.lt n)
  Nat.zero
inferred type:  Acc Nat.lt (OfNat.ofNat n)
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.eq_or_lt_of_le: java.lang.IllegalArgumentException: wrong type:  Nat.zero_le x._@.Init.Prelude._hyg.4483.4510  :  LE.le Nat.zero
  x._@.Init.Prelude._hyg.4483.4510
inferred type:  LE.le (OfNat.ofNat n) x._@.Init.Prelude._hyg.4483.4510
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.pred_le_pred: java.lang.IllegalArgumentException: wrong type:  Nat.le.step h  :  LE.le n
  (Nat.succ x._@.Init.Prelude._hyg.4294.4321)
inferred type:  Nat.le (OfNat.ofNat n)
  (Nat.succ x._@.Init.Prelude._hyg.4294.4321)
n  !=def  n
stuck on:  n n
Nat.pred_le_pred.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.step h  :  LE.le n (Nat.succ n._@.Init.Prelude._hyg.4337)
inferred type:  Nat.le (OfNat.ofNat n) (Nat.succ n._@.Init.Prelude._hyg.4337)
n  !=def  n
stuck on:  n n
Nat.pow.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.zero_le: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg3938 : Nat.below Nat.zero) ↦ Nat.le.refl  :  Unit →
(fun (x_InitPrelude_hyg39103921 : Nat) ↦ ∀ (x_InitPrelude_hyg3938 :
      Nat.below x_InitPrelude_hyg39103921) , LE.le (OfNat.ofNat n)
    x_InitPrelude_hyg39103921) Nat.zero
inferred type:  Unit → (∀ (x_InitPrelude_hyg3938 : Nat.below Nat.zero) , Nat.le
  (OfNat.ofNat n) (OfNat.ofNat n))
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.succ_le_succ: java.lang.IllegalArgumentException: wrong type:  PProd.fst (PProd.fst x._@.Init.Prelude._hyg.4017) h  :  Nat.le
  (Nat.succ n) (HAdd.hAdd m._@.Init.Prelude._hyg.3982 (OfNat.ofNat n))
inferred type:  LE.le (Nat.succ n) (Nat.succ m._@.Init.Prelude._hyg.3982)
(Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 m._@.Init.Prelude._hyg.3982  !=def  Nat.succ
  m._@.Init.Prelude._hyg.3982
stuck on:  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) Nat.zero
        PUnit.unit) PUnit.unit)
    (fun (n : Nat)
      (n_ih :
        PProd
          ((fun (x_InitPrelude_hyg2941 : Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                Nat) , Nat) n) (Nat.below n)) ↦ PProd.mk
      ((fun (x_InitPrelude_hyg2941 : Nat) (f : Nat.below x_InitPrelude_hyg2941)
          (x_InitPrelude_hyg2940 : Nat) ↦ Nat.add.match_1
          (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
              Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg2940
          x_InitPrelude_hyg2941
          (fun (a : Nat) (x_InitPrelude_hyg2988 : Nat.below Nat.zero) ↦ a)
          (fun (a b : Nat)
            (x_InitPrelude_hyg2988 : Nat.below (Nat.succ b)) ↦ Nat.succ
            (PProd.fst (PProd.fst x_InitPrelude_hyg2988) a)) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (OfNat.ofNat n)).0 m._@.Init.Prelude._hyg.3982 Nat.succ
  m._@.Init.Prelude._hyg.3982
Nat.not_succ_le_zero: java.lang.IllegalArgumentException: wrong type:  h  :  LE.le (Nat.succ n) (OfNat.ofNat n)
inferred type:  LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)
n  !=def  n
stuck on:  n n
Nat.not_succ_le_zero.match_2: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3881  :  Eq n
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
inferred type:  Eq (OfNat.ofNat n)
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
n  !=def  n
stuck on:  n n
Nat.not_succ_le_zero.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3862  :  Eq n n
inferred type:  Eq (OfNat.ofNat n) (Nat.succ (OfNat.ofNat n))
n  !=def  n
stuck on:  n n
Nat.not_succ_le_zero.match_3: java.lang.IllegalArgumentException: wrong type:  h  :  LE.le (Nat.succ n) (OfNat.ofNat n)
inferred type:  LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)
n  !=def  n
stuck on:  n n
