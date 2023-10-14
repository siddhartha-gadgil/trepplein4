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
stuck on:  Bool.true
Nat.zero_sub: java.lang.IllegalArgumentException: wrong type:  Eq.refl Bool.true  :  Eq
  (Decidable.decide (Eq (Nat.pred (OfNat.ofNat n)) (OfNat.ofNat n))) Bool.true
inferred type:  Eq Bool.true Bool.true
Decidable.rec (Eq (Nat.pred (OfNat.ofNat n)) (OfNat.ofNat n))
  (fun (h :
      Not
        (Eq (Nat.pred (OfNat.ofNat n))
          (OfNat.ofNat n))) ↦ (fun (x_InitPrelude_hyg1211 :
        Not (Eq (Nat.pred (OfNat.ofNat n)) (OfNat.ofNat n))) ↦ Bool.false) h)
  (fun (h :
      Eq (Nat.pred (OfNat.ofNat n))
        (OfNat.ofNat n)) ↦ (fun (x_InitPrelude_hyg1218 :
        Eq (Nat.pred (OfNat.ofNat n)) (OfNat.ofNat n)) ↦ Bool.true) h)
  (instDecidableEqNat (Nat.pred (OfNat.ofNat n))
    (OfNat.ofNat n))  !=def  Bool.true
stuck on:  Nat Bool.true
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
stuck on:  Nat Bool.true
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
stuck on:  False (fun (x_InitPrelude_hyg3669 : Nat) ↦ ∀ (a_InitPrelude_hyg3665 :
      Nat) , Bool) Nat.zero
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
stuck on:  Eq Nat.zero
  (Nat.succ x._@.Init.Prelude._hyg.3303.3330) (fun (x_InitPrelude_hyg3669 :
      Nat) ↦ ∀ (a_InitPrelude_hyg3665 : Nat) , Bool) Nat.zero
Nat.le_antisymm: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.le_antisymm.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.le_step: java.lang.IllegalArgumentException: wrong type:  h  :  Nat.le n m
inferred type:  LE.le n m
Nat.le n m  !=def  Nat
stuck on:  Nat.le n m Nat
Nat.modCore_eq_mod: java.lang.IllegalArgumentException: wrong type:  if_neg
  (fun (x_InitDataNatDiv_hyg957 :
      And (LT.lt (OfNat.ofNat n) y)
        (LE.le y Nat.zero)) ↦ Nat.modCore_eq_mod.match_1 y
    (fun (x_InitDataNatDiv_hyg957966 :
        And (LT.lt (OfNat.ofNat n) y) (LE.le y Nat.zero)) ↦ False)
    x_InitDataNatDiv_hyg957
    (fun (hlt : LT.lt (OfNat.ofNat n) y)
      (hle : LE.le y Nat.zero) ↦ Nat.lt_irrefl (OfNat.ofNat n)
      (Nat.lt_of_lt_of_le hlt hle)))  :  Eq
  (ite (And (LT.lt (OfNat.ofNat n) y) (LE.le y Nat.zero))
    (Nat.modCore (HSub.hSub Nat.zero y) y) Nat.zero) (HMod.hMod Nat.zero y)
inferred type:  Eq
  (ite (And (LT.lt (OfNat.ofNat n) y) (LE.le y Nat.zero))
    (Nat.modCore (HSub.hSub Nat.zero y) y) Nat.zero) Nat.zero
Nat  !=def  Nat.zero
stuck on:  Nat Nat.zero
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
PSigma (fun (x : Nat) ↦ Nat)  !=def  Nat
stuck on:  PSigma (fun (x : Nat) ↦ Nat) Nat
Nat.sub_zero: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ rfl  :  ∀ (n : Nat) , Eq
  (HSub.hSub n (OfNat.ofNat n)) n
inferred type:  ∀ (n : Nat) , Eq (HSub.hSub n (OfNat.ofNat n))
  (HSub.hSub n (OfNat.ofNat n))
n  !=def  Nat
stuck on:  n Nat
Nat.eq_zero_or_pos: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Or.inl rfl  :  Unit →
(fun (x_InitDataNatBasic_hyg33113322 : Nat) ↦ Or
    (Eq x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))
    (GT.gt x_InitDataNatBasic_hyg33113322 (OfNat.ofNat n))) n
inferred type:  ∀ (a : Unit) , Or (Eq (OfNat.ofNat n) (OfNat.ofNat n))
  (GT.gt (OfNat.ofNat n) (OfNat.ofNat n))
n  !=def  Nat
stuck on:  n Nat
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
v1  !=def  Nat
stuck on:  v1 Nat
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
PSigma
  (fun (x : Nat) ↦ PSigma
    (fun (y : Nat) ↦ PSigma
      (fun (ind :
          (∀ (x_1 y_1 : Nat)
            (a_InitDataNatDiv_hyg233 :
              And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_1))
            (a_InitDataNatDiv_hyg247 : motive (HSub.hSub x_1 y_1) y_1) , motive
            x_1 y_1)) ↦ ∀ (x_0 y_0 : Nat)
        (a_InitDataNatDiv_hyg264 :
          Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive x_0
        y_0)))  !=def  Nat
stuck on:  PSigma
  (fun (x : Nat) ↦ PSigma
    (fun (y : Nat) ↦ PSigma
      (fun (ind :
          (∀ (x_1 y_1 : Nat)
            (a_InitDataNatDiv_hyg233 :
              And (LT.lt (OfNat.ofNat n) y_1) (LE.le y_1 x_1))
            (a_InitDataNatDiv_hyg247 : motive (HSub.hSub x_1 y_1) y_1) , motive
            x_1 y_1)) ↦ ∀ (x_0 y_0 : Nat)
        (a_InitDataNatDiv_hyg264 :
          Not (And (LT.lt (OfNat.ofNat n) y_0) (LE.le y_0 x_0))) , motive x_0
        y_0))) Nat
Nat.mod: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.839.858
  (Nat.succ x._@.Init.Prelude._hyg.4249.4260)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.839.858
  (HAdd.hAdd x._@.Init.Prelude._hyg.4249.4260 (OfNat.ofNat n))
Nat.succ x._@.Init.Prelude._hyg.4249.4260  !=def  Nat
stuck on:  Nat.succ x._@.Init.Prelude._hyg.4249.4260 Nat
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
PSigma (fun (x : Nat) ↦ Nat)  !=def  Nat
stuck on:  PSigma (fun (x : Nat) ↦ Nat) Nat
Nat.succ_sub_succ_eq_sub: java.lang.IllegalArgumentException: wrong type:  fun (m : Nat)
  (ih : Eq (HSub.hSub (Nat.succ n) (Nat.succ m)) (HSub.hSub n m)) ↦ congrArg
  Nat.pred ih  :  ∀ (n : Nat)
  (ih :
    (fun (m : Nat) ↦ Eq (HSub.hSub (Nat.succ n) (Nat.succ m)) (HSub.hSub n m))
      n) , (fun (m : Nat) ↦ Eq (HSub.hSub (Nat.succ n) (Nat.succ m))
    (HSub.hSub n m)) (Nat.succ n)
inferred type:  ∀ (m : Nat)
  (ih : Eq (HSub.hSub (Nat.succ n) (Nat.succ m)) (HSub.hSub n m)) , Eq
  (Nat.pred (HSub.hSub (Nat.succ n) (Nat.succ m))) (Nat.pred (HSub.hSub n m))
Nat  !=def  Nat.rec ((fun (a : Unit) ↦ OfNat.ofNat n) Unit.unit)
  (fun (n : Nat)
    (n_ih :
      (fun (x : Nat) ↦ (fun (x_InitPrelude_hyg42494260 : Nat) ↦ Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : Nat) ↦ (fun (a : Nat) ↦ a)
      n_InitPrelude_hyg3937) n) (HSub.hSub (Nat.succ n) (Nat.succ m))
stuck on:  Nat Nat
Nat.pred_le: java.lang.IllegalArgumentException: wrong type:  fun (a : Unit) ↦ Nat.le.refl  :  Unit →
(fun (x_InitDataNatBasic_hyg23662377 : Nat) ↦ LE.le
    (Nat.pred x_InitDataNatBasic_hyg23662377) x_InitDataNatBasic_hyg23662377)
  Nat.zero
inferred type:  ∀ (a : Unit) , Nat.le (Nat.pred Nat.zero) (Nat.pred Nat.zero)
Nat  !=def  Nat.le (Nat.pred Nat.zero) (Nat.pred Nat.zero)
stuck on:  Nat Nat.le (Nat.pred Nat.zero) (Nat.pred Nat.zero)
Nat.le_refl: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.le.refl  :  ∀ (n : Nat) , LE.le n n
inferred type:  ∀ (n : Nat) , Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.sub_lt.match_1: java.lang.IllegalArgumentException: wrong type:  fun (x_InitDataNatBasic_hyg25272566 :
    LT.lt (OfNat.ofNat n) Nat.zero) ↦ h_1
  x._@.Init.Data.Nat.Basic._hyg.2526.2563 x_InitDataNatBasic_hyg25272566
  x._@.Init.Data.Nat.Basic._hyg.2528.2569  :  (fun (x :
      Nat) ↦ ∀ (x_InitDataNatBasic_hyg25272566 :
      LT.lt (OfNat.ofNat n) x) , motive x
    x._@.Init.Data.Nat.Basic._hyg.2526.2563 x_InitDataNatBasic_hyg25272566
    x._@.Init.Data.Nat.Basic._hyg.2528.2569) Nat.zero
inferred type:  ∀ (x_InitDataNatBasic_hyg25272566 :
    LT.lt (OfNat.ofNat n) Nat.zero) , motive n
  x._@.Init.Data.Nat.Basic._hyg.2526.2563 x_InitDataNatBasic_hyg25272566
  x._@.Init.Data.Nat.Basic._hyg.2528.2569
Nat.zero  !=def  n
stuck on:  Nat.zero n
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
Nat.ble_eq_true_of_le: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.ble_succ_eq_true: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5094.5121) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5094.5121)
  Bool.true
n  !=def  Nat
stuck on:  n Nat
Nat.ble_succ_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  x._@.Init.Prelude._hyg.5136  :  Eq
  (Nat.ble n x._@.Init.Prelude._hyg.5137) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5137)
  Bool.true
n  !=def  Nat
stuck on:  n Nat
Nat.ble_self_eq_true: java.lang.IllegalArgumentException: wrong type:  fun (_ : Unit)
  (x_InitPrelude_hyg5066 : Nat.below n) ↦ rfl  :  Unit →
(fun (x_InitPrelude_hyg50425053 : Nat) ↦ ∀ (x_InitPrelude_hyg5066 :
      Nat.below x_InitPrelude_hyg50425053) , Eq
    (Nat.ble x_InitPrelude_hyg50425053 x_InitPrelude_hyg50425053) Bool.true) n
inferred type:  Unit → (∀ (x_InitPrelude_hyg5066 : Nat.below n) , Eq
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n))
  (Nat.ble (OfNat.ofNat n) (OfNat.ofNat n)))
n  !=def  Nat
stuck on:  n Nat
Nat.not_succ_le_self.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.ble_eq_true_of_le.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.le_of_ble_eq_true: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n n._@.Init.Prelude._hyg.4984) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) n._@.Init.Prelude._hyg.4984)
  Bool.true
n  !=def  Nat
stuck on:  n Nat
Nat.le_of_ble_eq_true.match_1: java.lang.IllegalArgumentException: wrong type:  h  :  Eq (Nat.ble n x._@.Init.Prelude._hyg.5000) Bool.true
inferred type:  Eq (Nat.ble (OfNat.ofNat n) x._@.Init.Prelude._hyg.5000)
  Bool.true
n  !=def  Nat
stuck on:  n Nat
Nat.mod.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Data.Nat.Div._hyg.873  :  Eq
  x._@.Init.Data.Nat.Div._hyg.869 (Nat.succ n._@.Init.Data.Nat.Div._hyg.886)
inferred type:  Eq x._@.Init.Data.Nat.Div._hyg.869
  (HAdd.hAdd n._@.Init.Data.Nat.Div._hyg.886 (OfNat.ofNat n))
Nat.succ n._@.Init.Data.Nat.Div._hyg.886  !=def  Nat
stuck on:  Nat.succ n._@.Init.Data.Nat.Div._hyg.886 Nat
_private.Init.Data.Nat.Gcd.0.Nat.gcdF.match_1: java.lang.IllegalArgumentException: wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.lt_wfRel.proof_1: java.lang.IllegalArgumentException: wrong type:  Nat.not_lt_zero a._@.Init.Prelude._hyg.170  :  Not
  (Nat.lt a._@.Init.Prelude._hyg.170 (OfNat.ofNat n))
inferred type:  Not (LT.lt a._@.Init.Prelude._hyg.170 (OfNat.ofNat n))
Nat.le (Nat.succ a._@.Init.Prelude._hyg.170) (OfNat.ofNat n)  !=def  Nat
stuck on:  Nat.le (Nat.succ a._@.Init.Prelude._hyg.170) (OfNat.ofNat n) Nat
Nat.pred_le_pred: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
inferred type:  Nat.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
Nat  !=def  Nat.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
stuck on:  Nat Nat.le x._@.Init.Prelude._hyg.4294.4321
  x._@.Init.Prelude._hyg.4294.4321
Nat.le_succ: java.lang.IllegalArgumentException: wrong type:  fun (n : Nat) ↦ Nat.le.step Nat.le.refl  :  ∀ (n : Nat) , LE.le n
  (Nat.succ n)
inferred type:  ∀ (n : Nat) , Nat.le n (Nat.succ n)
Nat  !=def  Nat.le n (Nat.succ n)
stuck on:  Nat Nat.le n (Nat.succ n)
Nat.le_trans: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le m m
inferred type:  Nat.le m m
Nat  !=def  Nat.le m m
stuck on:  Nat Nat.le m m
Nat.le_trans.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le m m
inferred type:  Nat.le m m
Nat  !=def  Nat.le m m
stuck on:  Nat Nat.le m m
Nat.pred_le_pred.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n._@.Init.Prelude._hyg.4337
  n._@.Init.Prelude._hyg.4337
inferred type:  Nat.le n._@.Init.Prelude._hyg.4337 n._@.Init.Prelude._hyg.4337
Nat  !=def  Nat.le n._@.Init.Prelude._hyg.4337 n._@.Init.Prelude._hyg.4337
stuck on:  Nat Nat.le n._@.Init.Prelude._hyg.4337 n._@.Init.Prelude._hyg.4337
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
Nat  !=def  Nat.le (OfNat.ofNat n) (OfNat.ofNat n)
stuck on:  Nat Nat.le (OfNat.ofNat n) (OfNat.ofNat n)
Nat.succ_le_succ: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.succ_le_succ.match_1: java.lang.IllegalArgumentException: wrong type:  Nat.le.refl  :  LE.le n n
inferred type:  Nat.le n n
Nat  !=def  Nat.le n n
stuck on:  Nat Nat.le n n
Nat.not_succ_le_zero.match_2: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3881  :  Eq n
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
inferred type:  Eq (OfNat.ofNat n)
  (Nat.succ (Nat.succ n._@.Init.Prelude._hyg.3873))
n  !=def  Nat
stuck on:  n Nat
Nat.not_succ_le_zero.match_1: java.lang.IllegalArgumentException: wrong type:  h._@.Init.Prelude._hyg.3862  :  Eq n n
inferred type:  Eq (OfNat.ofNat n) (Nat.succ (OfNat.ofNat n))
n  !=def  Nat
stuck on:  n Nat
Nat.not_succ_le_zero.match_3: java.lang.IllegalArgumentException: wrong type:  fun (x_InitPrelude_hyg38293850 :
    LE.le (Nat.succ Nat.zero) (OfNat.ofNat n)) ↦ h_1
  x_InitPrelude_hyg38293850  :  (fun (x : Nat) ↦ ∀ (x_InitPrelude_hyg38293850 :
      LE.le (Nat.succ x) (OfNat.ofNat n)) , motive x x_InitPrelude_hyg38293850)
  Nat.zero
inferred type:  ∀ (x_InitPrelude_hyg38293850 :
    LE.le (Nat.succ Nat.zero) (OfNat.ofNat n)) , motive n
  x_InitPrelude_hyg38293850
Nat.zero  !=def  n
stuck on:  Nat.zero n
