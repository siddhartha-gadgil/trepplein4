Nat.gcd_self: java.lang.IllegalArgumentException: wrong type:  Eq.refl Bool.true  :  Eq
  (Decidable.decide (Eq (Nat.gcd Nat.zero Nat.zero) Nat.zero)) Bool.true
inferred type:  Eq Bool.true Bool.true
Decidable.rec (Eq (Nat.gcd Nat.zero Nat.zero) Nat.zero)
  (fun (h :
      Not
        (Eq (Nat.gcd Nat.zero Nat.zero)
          Nat.zero)) ↦ (fun (x_InitPrelude_hyg1211 :
        Not (Eq (Nat.gcd Nat.zero Nat.zero) Nat.zero)) ↦ Bool.false) h)
  (fun (h :
      Eq (Nat.gcd Nat.zero Nat.zero) Nat.zero) ↦ (fun (x_InitPrelude_hyg1218 :
        Eq (Nat.gcd Nat.zero Nat.zero) Nat.zero) ↦ Bool.true) h)
  (instDecidableEqNat (Nat.gcd Nat.zero Nat.zero) Nat.zero)  !=def  Bool.true
stuck on:  (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
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
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
          (fun (n_InitPrelude_hyg3242 : Nat)
            (x_InitPrelude_hyg3741 :
              Nat.below (Nat.succ n_InitPrelude_hyg3242)) ↦ Bool.false)
          (fun (n_0 m : Nat)
            (x_InitPrelude_hyg3741 : Nat.below (Nat.succ n_0)) ↦ PProd.fst
            (PProd.fst x_InitPrelude_hyg3741) m) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit))
    (Nat.gcd Nat.zero Nat.zero)).0 Nat.zero Bool.true
Nat.zero_sub: java.lang.IllegalArgumentException: wrong type:  Eq.refl (HSub.hSub (OfNat.ofNat n) Nat.zero)  :  (fun (n :
      Nat) ↦ Eq (HSub.hSub (OfNat.ofNat n) n) (OfNat.ofNat n)) Nat.zero
inferred type:  Eq (HSub.hSub (OfNat.ofNat n) Nat.zero)
  (HSub.hSub (OfNat.ofNat n) Nat.zero)
(instOfNatNat n).0  !=def  (instHSub).0 (OfNat.ofNat n) Nat.zero
stuck on:  (instOfNatNat n).0 (instHSub).0 (OfNat.ofNat n) Nat.zero
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
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.ne_of_beq_eq_false: java.lang.IllegalArgumentException: wrong type:  fun (h : Eq (Nat.beq Nat.zero Nat.zero) Bool.false)
  (x_InitPrelude_hyg3507 : Eq Nat.zero Nat.zero)
  (x_InitPrelude_hyg3601 : Nat.below Nat.zero) ↦ Bool.noConfusion h  :  ∀ (h :
    Eq (Nat.beq Nat.zero Nat.zero) Bool.false)
  (x_InitPrelude_hyg3507 :
    Eq Nat.zero Nat.zero) , (fun (x_InitPrelude_hyg34513486
      x_InitPrelude_hyg34523489 :
      Nat)
    (x_InitPrelude_hyg34533492 :
      Eq (Nat.beq x_InitPrelude_hyg34513486 x_InitPrelude_hyg34523489)
        Bool.false)
    (x_InitPrelude_hyg34543495 :
      Eq x_InitPrelude_hyg34513486
        x_InitPrelude_hyg34523489) ↦ ∀ (x_InitPrelude_hyg3601 :
      Nat.below x_InitPrelude_hyg34513486) , False) Nat.zero Nat.zero h
  x_InitPrelude_hyg3507
inferred type:  ∀ (h : Eq (Nat.beq Nat.zero Nat.zero) Bool.false)
  (x_InitPrelude_hyg3507 : Eq Nat.zero Nat.zero)
  (x_InitPrelude_hyg3601 : Nat.below Nat.zero) , Bool.noConfusionType False
  (Nat.beq Nat.zero Nat.zero) Bool.false
False  !=def  Bool.rec (Bool.casesOn Bool.false (∀ (a : False) , False) False)
  (Bool.casesOn Bool.false False (∀ (a : False) , False))
  (Nat.beq Nat.zero Nat.zero)
stuck on:  False (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
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
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
          (fun (n_InitPrelude_hyg3242 : Nat)
            (x_InitPrelude_hyg3741 :
              Nat.below (Nat.succ n_InitPrelude_hyg3242)) ↦ Bool.false)
          (fun (n_0 m : Nat)
            (x_InitPrelude_hyg3741 : Nat.below (Nat.succ n_0)) ↦ PProd.fst
            (PProd.fst x_InitPrelude_hyg3741) m) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit)) Nat.zero).0
  Nat.zero
Nat.eq_of_beq_eq_true: java.lang.IllegalArgumentException: wrong type:  fun (n_InitPrelude_hyg3361 : Nat)
  (h : Eq (Nat.beq Nat.zero (Nat.succ n_InitPrelude_hyg3361)) Bool.true)
  (x_InitPrelude_hyg3427 : Nat.below Nat.zero) ↦ Bool.noConfusion
  h  :  ∀ (n_InitPrelude_hyg3361 : Nat)
  (h :
    Eq (Nat.beq Nat.zero (Nat.succ n_InitPrelude_hyg3361))
      Bool.true) , (fun (x_InitPrelude_hyg33033330 x_InitPrelude_hyg33043333 :
      Nat)
    (x_InitPrelude_hyg33053336 :
      Eq (Nat.beq x_InitPrelude_hyg33033330 x_InitPrelude_hyg33043333)
        Bool.true) ↦ ∀ (x_InitPrelude_hyg3427 :
      Nat.below x_InitPrelude_hyg33033330) , Eq x_InitPrelude_hyg33033330
    x_InitPrelude_hyg33043333) Nat.zero (Nat.succ n_InitPrelude_hyg3361) h
inferred type:  ∀ (n_InitPrelude_hyg3361 : Nat)
  (h : Eq (Nat.beq Nat.zero (Nat.succ n_InitPrelude_hyg3361)) Bool.true)
  (x_InitPrelude_hyg3427 : Nat.below Nat.zero) , Bool.noConfusionType
  (Eq Nat.zero (Nat.succ n_InitPrelude_hyg3361))
  (Nat.beq Nat.zero (Nat.succ n_InitPrelude_hyg3361)) Bool.true
Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330)  !=def  Bool.rec
  (Bool.casesOn Bool.true
    (∀ (a : Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330)) , Eq
      Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330))
    (Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330)))
  (Bool.casesOn Bool.true
    (Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330))
    (∀ (a : Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330)) , Eq
      Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330)))
  (Nat.beq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330))
stuck on:  Eq Nat.zero (Nat.succ x._@.Init.Prelude._hyg.3303.3330) (Nat.rec
    (PProd.mk
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
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
      ((fun (x_InitPrelude_hyg3190 : Nat) (f : Nat.below x_InitPrelude_hyg3190)
          (x_InitPrelude_hyg3191 : Nat) ↦ Nat.beq.match_1
          (fun (x_InitPrelude_hyg36693688 x_InitPrelude_hyg36703691 :
              Nat) ↦ ∀ (x_InitPrelude_hyg3741 :
              Nat.below x_InitPrelude_hyg36693688) , Bool) x_InitPrelude_hyg3190
          x_InitPrelude_hyg3191
          (fun (_ : Unit)
            (x_InitPrelude_hyg3741 : Nat.below Nat.zero) ↦ Bool.true)
          (fun (n_InitPrelude_hyg3230 : Nat)
            (x_InitPrelude_hyg3262 : Nat.below Nat.zero) ↦ Bool.false)
          (fun (n_InitPrelude_hyg3242 : Nat)
            (x_InitPrelude_hyg3741 :
              Nat.below (Nat.succ n_InitPrelude_hyg3242)) ↦ Bool.false)
          (fun (n_0 m : Nat)
            (x_InitPrelude_hyg3741 : Nat.below (Nat.succ n_0)) ↦ PProd.fst
            (PProd.fst x_InitPrelude_hyg3741) m) f) (Nat.succ n)
        (PProd.mk n_ih PUnit.unit)) (PProd.mk n_ih PUnit.unit)) Nat.zero).0
  (Nat.succ x._@.Init.Prelude._hyg.3303.3330)
Nat.gcd: java.lang.IllegalArgumentException: wrong type:  _private.Init.Data.Nat.Gcd.0.Nat.gcdF  :  ∀ (x : Nat)
  (a_InitWF_hyg517 :
    (∀ (y : Nat) (a_InitWF_hyg523 : WellFoundedRelation.rel y x) , (fun (y_0 :
          Nat) ↦ ∀ (n : Nat) , Nat) y)) , (fun (y : Nat) ↦ ∀ (n : Nat) , Nat) x
inferred type:  ∀ (x : Nat)
  (a_InitDataNatGcd_hyg5 :
    (∀ (x_0 : Nat) (a_InitDataNatGcd_hyg11 : LT.lt x_0 x) (n_0 : Nat) , Nat))
  (n : Nat) , Nat
(measure id).0 n y  !=def  (instLTNat).0 n y
stuck on:  (measure id).0 n y (instLTNat).0 n y
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
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
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
Nat.le_antisymm: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.lt_of_le_of_lt: java.lang.IllegalArgumentException: wrong type:  a._@.Init.Prelude._hyg.4161  :  LE.le (Nat.succ m) k
inferred type:  LT.lt m k
(instLENat).0 (Nat.succ m) k  !=def  (instLTNat).0 m k
stuck on:  (instLENat).0 (Nat.succ m) k (instLTNat).0 m k
Nat.le_antisymm.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.lt_trans: java.lang.IllegalArgumentException: wrong type:  h₁  :  LE.le (Nat.succ n) m
inferred type:  LT.lt n m
(instLENat).0 (Nat.succ n) m  !=def  (instLTNat).0 n m
stuck on:  (instLENat).0 (Nat.succ n) m (instLTNat).0 n m
Nat.le_step: java.lang.IllegalArgumentException: wrong type:  h  :  Nat.le n m
inferred type:  LE.le n m
Nat.le n m  !=def  (instLENat).0 n m
stuck on:  Nat.le n m (instLENat).0 n m
Nat.lt_or_ge: java.lang.IllegalArgumentException: wrong type:  Nat.zero_le n  :  GE.ge n Nat.zero
inferred type:  LE.le (OfNat.ofNat n) n
Nat.zero  !=def  (instOfNatNat n).0
stuck on:  Nat.zero (instOfNatNat n).0
Nat.modCore_eq_mod: java.lang.IllegalArgumentException: wrong type:  hle  :  LE.le y (OfNat.ofNat n)
inferred type:  LE.le y Nat.zero
(instOfNatNat n).0  !=def  Nat.zero
stuck on:  (instOfNatNat n).0 Nat.zero
_private.Init.Data.Nat.Div.0.Nat.modCore._eq_1: java.lang.IllegalArgumentException: wrong type:  Nat.div_rec_lemma h._@.Init.Data.Nat.Div._hyg.814  :  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817)
inferred type:  LT.lt (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
(invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817)  !=def  (instLTNat).0
  (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
stuck on:  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817) (instLTNat).0
  (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
Nat.sub_zero: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ rfl  :  ∀ (n : Nat) , Eq
  (HSub.hSub n (OfNat.ofNat n)) n
inferred type:  ∀ (n : Nat) , Eq (HSub.hSub n (OfNat.ofNat n))
  (HSub.hSub n (OfNat.ofNat n))
n  !=def  (instHSub).0 n (OfNat.ofNat n)
stuck on:  n (instHSub).0 n (OfNat.ofNat n)
Nat.eq_zero_or_pos: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Or.inl rfl  :  Unit →
(fun (x_InitDataNatBasic_hyg33113322 : Nat) ↦ Or
    (Eq x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))
    (GT.gt x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))) n
inferred type:  ∀ (a : Unit) , Or (Eq (OfNat.ofNat n) (OfNat.ofNat n))
  (GT.gt (OfNat.ofNat n) (OfNat.ofNat n))
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.zero_lt_succ: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.succ_le_succ (Nat.zero_le n)  :  ∀ (n :
    Nat) , LT.lt (OfNat.ofNat n) (Nat.succ n)
inferred type:  ∀ (n : Nat) , LE.le (Nat.succ (OfNat.ofNat n)) (Nat.succ n)
(instLTNat).0 (OfNat.ofNat n) (Nat.succ n)  !=def  (instLENat).0
  (Nat.succ (OfNat.ofNat n)) (Nat.succ n)
stuck on:  (instLTNat).0 (OfNat.ofNat n) (Nat.succ n) (instLENat).0
  (Nat.succ (OfNat.ofNat n)) (Nat.succ n)
Nat.zero_add.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.div.inductionOn: java.lang.IllegalArgumentException: wrong type:  fun {motive : (∀ (v1 t : Nat) , Sort u)} (x y : Nat)
  (ind :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg233 :
        And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))
      (a_InitDataNatDiv_hyg247 : motive (HSub.hSub x_0 y_0) y_0) , motive x_0
      y_0))
  (base :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg264 :
        Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive x_0
      y_0)) ↦ Nat.div.inductionOn._unary
  (PSigma.mk x (PSigma.mk y (PSigma.mk ind base)))  :  ∀ {motive :
    (∀ (v1 t : Nat) , Sort u)} (x y : Nat)
  (ind :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg233 :
        And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))
      (a_InitDataNatDiv_hyg247 : motive (HSub.hSub x_0 y_0) y_0) , motive x_0
      y_0))
  (base :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg264 :
        Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive x_0
      y_0)) , motive x y
inferred type:  ∀ {motive : (∀ (v1 t : Nat) , Sort u)} (x y : Nat)
  (ind :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg233 :
        And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))
      (a_InitDataNatDiv_hyg247 : motive (HSub.hSub x_0 y_0) y_0) , motive x_0
      y_0))
  (base :
    (∀ (x_0 y_0 : Nat)
      (a_InitDataNatDiv_hyg264 :
        Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive x_0
      y_0)) , motive ((PSigma.mk x (PSigma.mk y (PSigma.mk ind base))).0)
  (((PSigma.mk x (PSigma.mk y (PSigma.mk ind base))).1).0)
v1  !=def  (PSigma.mk v1 (PSigma.mk t (PSigma.mk ind base))).0
stuck on:  v1 (PSigma.mk v1 (PSigma.mk t (PSigma.mk ind base))).0
Nat.div.inductionOn._unary: java.lang.IllegalArgumentException: wrong type:  Nat.div_rec_lemma h  :  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg340 :
        PSigma
          (fun (x : Nat) ↦ PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_1 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_1))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_1 y_1) y_1) , motive x_1
                    y_1)) ↦ ∀ (x_0 y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not
                    (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive
                x_0 y_0)))) ↦ PSigma.casesOn a_InitWF860InitDataNatDiv_hyg340
      (fun (x_InitDataNatDiv_hyg221 : Nat)
        (snd_InitDataNatDiv_hyg341 :
          PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0))) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg341
        (fun (y : Nat)
          (snd_InitDataNatDiv_hyg342 :
            PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg342
          (fun (ind :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg233 :
                  And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))
                (a_InitDataNatDiv_hyg247 :
                  motive (HSub.hSub x y_0) y_0) , motive x y_0))
            (snd_InitDataNatDiv_hyg343 :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg221))))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub v1 t)
    (PSigma.mk t (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343)))
  (PSigma.mk v1 (PSigma.mk t (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343)))
inferred type:  LT.lt (HSub.hSub v1 t) v1
(invImage
    (fun (a_InitWF860InitDataNatDiv_hyg340 :
        PSigma
          (fun (x : Nat) ↦ PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_1 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_1))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_1 y_1) y_1) , motive x_1
                    y_1)) ↦ ∀ (x_0 y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not
                    (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive
                x_0 y_0)))) ↦ PSigma.casesOn a_InitWF860InitDataNatDiv_hyg340
      (fun (x_InitDataNatDiv_hyg221 : Nat)
        (snd_InitDataNatDiv_hyg341 :
          PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0))) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg341
        (fun (y : Nat)
          (snd_InitDataNatDiv_hyg342 :
            PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg342
          (fun (ind :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg233 :
                  And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))
                (a_InitDataNatDiv_hyg247 :
                  motive (HSub.hSub x y_0) y_0) , motive x y_0))
            (snd_InitDataNatDiv_hyg343 :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg221))))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub v1 t)
    (PSigma.mk t (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343)))
  (PSigma.mk v1
    (PSigma.mk t
      (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343)))  !=def  (instLTNat).0
  (HSub.hSub v1 t) v1
stuck on:  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg340 :
        PSigma
          (fun (x : Nat) ↦ PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_1 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_1))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_1 y_1) y_1) , motive x_1
                    y_1)) ↦ ∀ (x_0 y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not
                    (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive
                x_0 y_0)))) ↦ PSigma.casesOn a_InitWF860InitDataNatDiv_hyg340
      (fun (x_InitDataNatDiv_hyg221 : Nat)
        (snd_InitDataNatDiv_hyg341 :
          PSigma
            (fun (y : Nat) ↦ PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0))) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg341
        (fun (y : Nat)
          (snd_InitDataNatDiv_hyg342 :
            PSigma
              (fun (ind :
                  (∀ (x_0 y_1 : Nat)
                    (a_InitDataNatDiv_hyg233 :
                      And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_0))
                    (a_InitDataNatDiv_hyg247 :
                      motive (HSub.hSub x_0 y_1) y_1) , motive x_0 y_1)) ↦ ∀ (x
                  y_0 :
                  Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ PSigma.casesOn snd_InitDataNatDiv_hyg342
          (fun (ind :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg233 :
                  And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))
                (a_InitDataNatDiv_hyg247 :
                  motive (HSub.hSub x y_0) y_0) , motive x y_0))
            (snd_InitDataNatDiv_hyg343 :
              (∀ (x y_0 : Nat)
                (a_InitDataNatDiv_hyg264 :
                  Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x))) , motive
                x y_0)) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg221))))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub v1 t)
    (PSigma.mk t (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343)))
  (PSigma.mk v1
    (PSigma.mk t
      (PSigma.mk ind snd._@.Init.Data.Nat.Div._hyg.343))) (instLTNat).0
  (HSub.hSub v1 t) v1
Nat.mod: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.839.858
  (Nat.succ x._@.Init.Prelude._hyg.4249.4260)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.839.858
  (HAdd.hAdd x._@.Init.Prelude._hyg.4249.4260 (OfNat.ofNat n))
Nat.succ x._@.Init.Prelude._hyg.4249.4260  !=def  (instHAdd).0
  x._@.Init.Prelude._hyg.4249.4260 (OfNat.ofNat n)
stuck on:  Nat.succ x._@.Init.Prelude._hyg.4249.4260 (instHAdd).0
  x._@.Init.Prelude._hyg.4249.4260 (OfNat.ofNat n)
Nat.modCore._unary: java.lang.IllegalArgumentException: wrong type:  Nat.div_rec_lemma h._@.Init.Data.Nat.Div._hyg.814  :  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817)
inferred type:  LT.lt (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
(invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817)  !=def  (instLTNat).0
  (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
stuck on:  (invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0
  (PSigma.mk (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817)
    snd._@.Init.Data.Nat.Div._hyg.817)
  (PSigma.mk x snd._@.Init.Data.Nat.Div._hyg.817) (instLTNat).0
  (HSub.hSub x snd._@.Init.Data.Nat.Div._hyg.817) x
Nat.lt_of_lt_of_le: java.lang.IllegalArgumentException: wrong type:  fun {n m k : Nat} ↦ Nat.le_trans  :  ∀ {n m k : Nat}
  (a_InitDataNatBasic_hyg2832 : LT.lt n m)
  (a_InitDataNatBasic_hyg2838 : LE.le m k) , LT.lt n k
inferred type:  ∀ {n m k : Nat} (a_InitPrelude_hyg4065 : LE.le (Nat.succ n) m)
  (a_InitPrelude_hyg4069 : LE.le m k) , LE.le (Nat.succ n) k
(instLTNat).0 n m  !=def  (instLENat).0 (Nat.succ n) m
stuck on:  (instLTNat).0 n m (instLENat).0 (Nat.succ n) m
Nat.sub_lt: java.lang.IllegalArgumentException: wrong type:  h1  :  LT.lt (OfNat.ofNat n) n
inferred type:  LT.lt (OfNat.ofNat n) (OfNat.ofNat n)
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.succ_sub_succ_eq_sub: java.lang.IllegalArgumentException: wrong type:  rfl  :  (fun (m : Nat) ↦ Eq (HSub.hSub (Nat.succ n) (Nat.succ m))
    (HSub.hSub n m)) Nat.zero
inferred type:  Eq (HSub.hSub (Nat.succ n) (Nat.succ Nat.zero))
  (HSub.hSub (Nat.succ n) (Nat.succ Nat.zero))
n  !=def  Nat.succ n
stuck on:  n Nat.succ n
Nat.sub_le: java.lang.IllegalArgumentException: wrong type:  Nat.le_refl (HSub.hSub n (OfNat.ofNat n))  :  (fun (m :
      Nat) ↦ LE.le (HSub.hSub n m) n) Nat.zero
inferred type:  LE.le (HSub.hSub n (OfNat.ofNat n))
  (HSub.hSub n (OfNat.ofNat n))
Nat.zero  !=def  (instOfNatNat n).0
stuck on:  Nat.zero (instOfNatNat n).0
Nat.pred_le: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Nat.le.refl  :  Unit →
(fun (x_InitDataNatBasic_hyg23662377 : Nat) ↦ LE.le
    (Nat.pred x_InitDataNatBasic_hyg23662377) x_InitDataNatBasic_hyg23662377)
  Nat.zero
inferred type:  ∀ (a : Unit) , Nat.le (Nat.pred Nat.zero) (Nat.pred Nat.zero)
(instLENat).0 (Nat.pred Nat.zero) Nat.zero  !=def  Nat.le (Nat.pred Nat.zero)
  (Nat.pred Nat.zero)
stuck on:  (instLENat).0 (Nat.pred Nat.zero) Nat.zero Nat.le (Nat.pred Nat.zero)
  (Nat.pred Nat.zero)
Nat.le_refl: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.le.refl  :  ∀ (n : Nat) , LE.le n n
inferred type:  ∀ (n : Nat) , Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.lt_succ_of_le: java.lang.IllegalArgumentException: wrong type:  fun {n m : Nat} ↦ Nat.succ_le_succ  :  ∀ {n m : Nat}
  (a_InitDataNatBasic_hyg2304 : LE.le n m) , LT.lt n (Nat.succ m)
inferred type:  ∀ {n m : Nat} (a_InitPrelude_hyg3952 : LE.le n m) , LE.le
  (Nat.succ n) (Nat.succ m)
(instLTNat).0 n (Nat.succ m)  !=def  (instLENat).0 (Nat.succ n) (Nat.succ m)
stuck on:  (instLTNat).0 n (Nat.succ m) (instLENat).0 (Nat.succ n) (Nat.succ m)
Nat.lt_irrefl: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.not_succ_le_self n  :  ∀ (n : Nat) , Not
  (LT.lt n n)
inferred type:  ∀ (n : Nat) , Not (LE.le (Nat.succ n) n)
(instLTNat).0 n n  !=def  (instLENat).0 (Nat.succ n) n
stuck on:  (instLTNat).0 n n (instLENat).0 (Nat.succ n) n
Nat.not_succ_le_self: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg4791 : Nat.below n) ↦ Nat.not_succ_le_zero
  (OfNat.ofNat n)  :  Unit → (fun (x_InitPrelude_hyg47564767 :
      Nat) ↦ ∀ (x_InitPrelude_hyg4791 :
      Nat.below x_InitPrelude_hyg47564767) , Not
    (LE.le (Nat.succ x_InitPrelude_hyg47564767) x_InitPrelude_hyg47564767)) n
inferred type:  Unit → (∀ (x_InitPrelude_hyg4791 : Nat.below n)
  (a_InitPrelude_hyg3820 :
    LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)) , False)
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.sub_lt.match_1: java.lang.IllegalArgumentException: wrong type:  h1  :  LT.lt (OfNat.ofNat n) n
inferred type:  LT.lt (OfNat.ofNat n) (OfNat.ofNat n)
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
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
Nat.decLt: java.lang.IllegalArgumentException: wrong type:  fun (n m : Nat) ↦ Nat.decLe (Nat.succ n) m  :  ∀ (n m :
    Nat) , Decidable (LT.lt n m)
inferred type:  ∀ (n m : Nat) , Decidable (LE.le (Nat.succ n) m)
(instLTNat).0 n m  !=def  (instLENat).0 (Nat.succ n) m
stuck on:  (instLTNat).0 n m (instLENat).0 (Nat.succ n) m
Nat.ble_eq_true_of_le: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.ble_succ_eq_true: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5094.5121) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5094.5121)
  Bool.true
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.ble_succ_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5137) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5137)
  Bool.true
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.ble_self_eq_true: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg5066 : Nat.below n) ↦ rfl  :  Unit →
(fun (x_InitPrelude_hyg50425053 : Nat) ↦ ∀ (x_InitPrelude_hyg5066 :
      Nat.below x_InitPrelude_hyg50425053) , Eq
    (Nat.ble x_InitPrelude_hyg50425053 x_InitPrelude_hyg50425053) Bool.true) n
inferred type:  Unit → (∀ (x_InitPrelude_hyg5066 : Nat.below n) , Eq
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n))
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n)))
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.not_succ_le_self.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.ble_eq_true_of_le.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.le_of_ble_eq_true: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n n._@.Init.Prelude._hyg.4984) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) n._@.Init.Prelude._hyg.4984)
  Bool.true
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.le_of_ble_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n x._@.Init.Prelude._hyg.5000) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5000)
  Bool.true
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.mod.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.869 (Nat.succ n._@.Init.Data.Nat.Div._hyg.886)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.869
  (HAdd.hAdd n._@.Init.Data.Nat.Div._hyg.886 (OfNat.ofNat n))
Nat.succ n._@.Init.Data.Nat.Div._hyg.886  !=def  (instHAdd).0
  n._@.Init.Data.Nat.Div._hyg.886 (OfNat.ofNat n)
stuck on:  Nat.succ n._@.Init.Data.Nat.Div._hyg.886 (instHAdd).0
  n._@.Init.Data.Nat.Div._hyg.886 (OfNat.ofNat n)
_private.Init.Data.Nat.Gcd.0.Nat.gcdF.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.lt_wfRel.proof_1: java.lang.IllegalArgumentException: wrong type:  Nat.not_lt_zero a._@.Init.Prelude._hyg.170  :  Not
  (Nat.lt a._@.Init.Prelude._hyg.170 (OfNat.ofNat n))
inferred type:  Not (LT.lt a._@.Init.Prelude._hyg.170 (OfNat.ofNat n))
Nat.le (Nat.succ a._@.Init.Prelude._hyg.170)
  (OfNat.ofNat n)  !=def  (instLTNat).0 a._@.Init.Prelude._hyg.170
  (OfNat.ofNat n)
stuck on:  Nat.le (Nat.succ a._@.Init.Prelude._hyg.170)
  (OfNat.ofNat n) (instLTNat).0 a._@.Init.Prelude._hyg.170 (OfNat.ofNat n)
Nat.eq_or_lt_of_le: java.lang.IllegalArgumentException: wrong type:  Nat.zero_le x._@.Init.Prelude._hyg.4483.4510  :  LE.le Nat.zero
  x._@.Init.Prelude._hyg.4483.4510
inferred type:  LE.le (OfNat.ofNat n) x._@.Init.Prelude._hyg.4483.4510
Nat.zero  !=def  (instOfNatNat n).0
stuck on:  Nat.zero (instOfNatNat n).0
Nat.pred_le_pred: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
inferred type:  Nat.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
(instLENat).0 x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321  !=def  Nat.le
  x._@.Init.Prelude._hyg.4294.4321 x._@.Init.Prelude._hyg.4294.4321
stuck on:  (instLENat).0 x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321 Nat.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
Nat.le_succ: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.le.step Nat.le.refl  :  ∀ (n : Nat) , LE.le n
  (Nat.succ n)
inferred type:  ∀ (n : Nat) , Nat.le n (Nat.succ n)
(instLENat).0 n (Nat.succ n)  !=def  Nat.le n (Nat.succ n)
stuck on:  (instLENat).0 n (Nat.succ n) Nat.le n (Nat.succ n)
Nat.le_trans: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le m m
inferred type:  Nat.le m m
(instLENat).0 m m  !=def  Nat.le m m
stuck on:  (instLENat).0 m m Nat.le m m
Nat.le_trans.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le m m
inferred type:  Nat.le m m
(instLENat).0 m m  !=def  Nat.le m m
stuck on:  (instLENat).0 m m Nat.le m m
Nat.pred_le_pred.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337
inferred type:  Nat.le n._@.Init.Prelude._hyg.4337 n._@.Init.Prelude._hyg.4337
(instLENat).0 n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337  !=def  Nat.le n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337
stuck on:  (instLENat).0 n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337 Nat.le n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337
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
(instLENat).0 (OfNat.ofNat n) Nat.zero  !=def  Nat.le (OfNat.ofNat n)
  (OfNat.ofNat n)
stuck on:  (instLENat).0 (OfNat.ofNat n) Nat.zero Nat.le (OfNat.ofNat n)
  (OfNat.ofNat n)
Nat.succ_le_succ: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.succ_le_succ.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
(instLENat).0 n n  !=def  Nat.le n n
stuck on:  (instLENat).0 n n Nat.le n n
Nat.not_lt_zero: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.not_succ_le_zero n  :  ∀ (n : Nat) , Not
  (LT.lt n (OfNat.ofNat n))
inferred type:  ∀ (n : Nat)
  (a_InitPrelude_hyg3820 : LE.le (Nat.succ n) (OfNat.ofNat n)) , False
(instLTNat).0 n (OfNat.ofNat n)  !=def  (instLENat).0 (Nat.succ n)
  (OfNat.ofNat n)
stuck on:  (instLTNat).0 n (OfNat.ofNat n) (instLENat).0 (Nat.succ n)
  (OfNat.ofNat n)
Nat.not_succ_le_zero: java.lang.IllegalArgumentException: wrong type:  h  :  LE.le (Nat.succ n) (OfNat.ofNat n)
inferred type:  LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.not_succ_le_zero.match_2: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3881  :  Eq n
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
inferred type:  Eq (OfNat.ofNat n)
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.not_succ_le_zero.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3862  :  Eq n n
inferred type:  Eq (OfNat.ofNat n) (Nat.succ (OfNat.ofNat n))
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
Nat.not_succ_le_zero.match_3: java.lang.IllegalArgumentException: wrong type:  h  :  LE.le (Nat.succ n) (OfNat.ofNat n)
inferred type:  LE.le (Nat.succ (OfNat.ofNat n)) (OfNat.ofNat n)
n  !=def  (instOfNatNat n).0
stuck on:  n (instOfNatNat n).0
