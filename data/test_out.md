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
Nat.sub_self: (#0).0 (of class trepplein.Proj)
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
Nat.gcd: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Gcd.0.Nat.gcdF: (#0).0 (of class trepplein.Proj)
Nat.mod_lt: (#0).0 (of class trepplein.Proj)
Iff.mp: (#0).0 (of class trepplein.Proj)
Nat.le_antisymm: (#0).0 (of class trepplein.Proj)
Nat.lt_of_le_of_lt: (#0).0 (of class trepplein.Proj)
Nat.le_antisymm.match_1: (#0).0 (of class trepplein.Proj)
Nat.lt_trans: (#0).0 (of class trepplein.Proj)
Nat.le_step: (#0).0 (of class trepplein.Proj)
Nat.lt_or_ge: (#0).0 (of class trepplein.Proj)
Nat.modCore_eq_mod: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Div.0.Nat.modCore._eq_1: (#0).0 (of class trepplein.Proj)
Nat.sub_zero: (#0).0 (of class trepplein.Proj)
Nat.eq_zero_or_pos: (#0).0 (of class trepplein.Proj)
Nat.zero_lt_succ: (#0).0 (of class trepplein.Proj)
Nat.zero_add.match_1: type error: within (type of `@Nat.casesOn.{0}`)  Pi-type `Binding(zero,#1 @Nat.zero,Default), ∀ (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2` in `∀ (zero : #1 @Nat.zero) (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2`; context: List(a._@.Init.Prelude._hyg.3756, fun (x : @Nat) ↦ motive x); args: List(h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); List(fun (x : @Nat) ↦ motive x, a._@.Init.Prelude._hyg.3756, h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); checking @Nat.casesOn.{0} (fun (x : @Nat) ↦ motive x) a._@.Init.Prelude._hyg.3756
  (h_1 @Unit.unit)
  (fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937)
wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.div.inductionOn: (#0).0 (of class trepplein.Proj)
Nat.div.inductionOn._unary: (#0).0 (of class trepplein.Proj)
Nat.mod: (#0).0 (of class trepplein.Proj)
Nat.modCore._unary: (#0).0 (of class trepplein.Proj)
Nat.lt_of_lt_of_le: (#0).0 (of class trepplein.Proj)
Nat.sub_lt: (#0).0 (of class trepplein.Proj)
Nat.succ_sub_succ_eq_sub: (#0).0 (of class trepplein.Proj)
Nat.sub_le: (#0).0 (of class trepplein.Proj)
Nat.pred_le: (#0).0 (of class trepplein.Proj)
Nat.le_refl: (#0).0 (of class trepplein.Proj)
Nat.lt_succ_of_le: (#0).0 (of class trepplein.Proj)
Nat.lt_irrefl: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_self: (#0).0 (of class trepplein.Proj)
Nat.sub_lt.match_1: (#0).0 (of class trepplein.Proj)
Nat.sub: type error: within (type of `@Nat.mul.match_1.{1}`)  Pi-type `Binding(h_1,∀ (x_InitPrelude_hyg3059 : @Nat) , #3 x_InitPrelude_hyg3059 n,Default), ∀ (h_2 : (∀ (a b : @Nat) , #5 a (@Nat.succ b))) , #4 #3 #2` in `∀ (h_1 : (∀ (x_InitPrelude_hyg3059 : @Nat) , #3 x_InitPrelude_hyg3059 n))   (h_2 : (∀ (a b : @Nat) , #5 a (@Nat.succ b))) , #4 #3 #2`; context: List(x._@.Init.Prelude._hyg.2941, a._@.Init.Prelude._hyg.2934, fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
    @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat); args: List(fun (x_InitPrelude_hyg3059 : @Nat)
  (x_InitPrelude_hyg5431 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059, fun (a b : @Nat)
  (x_InitPrelude_hyg5431 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
  (@PProd.fst.{1 1}
    ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) b)
    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
        (@PProd.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) n) n_ih) @PUnit.{1}) b)
    (@PProd.fst.{1 1}
      (@PProd.{1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) b)
        (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
          (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
      x_InitPrelude_hyg5431) a), f); List(fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
    @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat, a._@.Init.Prelude._hyg.2934, x._@.Init.Prelude._hyg.2941, fun (x_InitPrelude_hyg3059 : @Nat)
  (x_InitPrelude_hyg5431 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059, fun (a b : @Nat)
  (x_InitPrelude_hyg5431 :
    @Nat.below.{1}
      (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
  (@PProd.fst.{1 1}
    ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) b)
    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
        (@PProd.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) n) n_ih) @PUnit.{1}) b)
    (@PProd.fst.{1 1}
      (@PProd.{1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) b)
        (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
          (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
      x_InitPrelude_hyg5431) a), f); checking @Nat.mul.match_1.{1}
  (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
      @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
      @Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat)
  a._@.Init.Prelude._hyg.2934 x._@.Init.Prelude._hyg.2941
  (fun (x_InitPrelude_hyg3059 : @Nat)
    (x_InitPrelude_hyg5431 :
      @Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059)
  (fun (a b : @Nat)
    (x_InitPrelude_hyg5431 :
      @Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
    (@PProd.fst.{1 1}
      ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) b)
      (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
        (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
          (@PProd.{1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n) n_ih) @PUnit.{1}) b)
      (@PProd.fst.{1 1}
        (@PProd.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n) n_ih)
              @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431) a)) f
wrong type:  fun (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 :
    Nat.below n) ↦ x_InitPrelude_hyg3059  :  ∀ (x_InitPrelude_hyg3059 :
    Nat) , (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
      Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
      Nat.below x_InitPrelude_hyg29412962) , Nat) x_InitPrelude_hyg3059 n
inferred type:  ∀ (x_InitPrelude_hyg3059 : Nat)
  (x_InitPrelude_hyg5431 : Nat.below n) , Nat
n  !=def  n
stuck on:  n n
Nat.mul.match_1: type error: within (type of `@Nat.casesOn.{u_1}`)  Pi-type `Binding(zero,#1 @Nat.zero,Default), ∀ (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2` in `∀ (zero : #1 @Nat.zero) (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2`; context: List(x._@.Init.Prelude._hyg.2941.2962, fun (x : @Nat) ↦ motive x._@.Init.Prelude._hyg.2940.2959 x); args: List(h_1 x._@.Init.Prelude._hyg.2940.2959, fun (n_InitPrelude_hyg2985 : @Nat) ↦ h_2 x._@.Init.Prelude._hyg.2940.2959
  n_InitPrelude_hyg2985); List(fun (x : @Nat) ↦ motive x._@.Init.Prelude._hyg.2940.2959 x, x._@.Init.Prelude._hyg.2941.2962, h_1 x._@.Init.Prelude._hyg.2940.2959, fun (n_InitPrelude_hyg2985 : @Nat) ↦ h_2 x._@.Init.Prelude._hyg.2940.2959
  n_InitPrelude_hyg2985); checking @Nat.casesOn.{u_1} (fun (x : @Nat) ↦ motive x._@.Init.Prelude._hyg.2940.2959 x)
  x._@.Init.Prelude._hyg.2941.2962 (h_1 x._@.Init.Prelude._hyg.2940.2959)
  (fun (n_InitPrelude_hyg2985 : @Nat) ↦ h_2 x._@.Init.Prelude._hyg.2940.2959
    n_InitPrelude_hyg2985)
wrong type:  h_1 x._@.Init.Prelude._hyg.2940.2959  :  (fun (x : Nat) ↦ motive
    x._@.Init.Prelude._hyg.2940.2959 x) Nat.zero
inferred type:  motive x._@.Init.Prelude._hyg.2940.2959 n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Sub.sub: (#0).0 (of class trepplein.Proj)
HSub.hSub: (#0).0 (of class trepplein.Proj)
Nat.decLt: (#0).0 (of class trepplein.Proj)
Nat.ble_eq_true_of_le: (#0).0 (of class trepplein.Proj)
Nat.ble_succ_eq_true: (#0).0 (of class trepplein.Proj)
Nat.ble_succ_eq_true.match_1: (#0).0 (of class trepplein.Proj)
Nat.ble_self_eq_true: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_self.match_1: type error: within (type of `@Nat.casesOn.{0}`)  Pi-type `Binding(zero,#1 @Nat.zero,Default), ∀ (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2` in `∀ (zero : #1 @Nat.zero) (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2`; context: List(a._@.Init.Prelude._hyg.3756, fun (x : @Nat) ↦ motive x); args: List(h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); List(fun (x : @Nat) ↦ motive x, a._@.Init.Prelude._hyg.3756, h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); checking @Nat.casesOn.{0} (fun (x : @Nat) ↦ motive x) a._@.Init.Prelude._hyg.3756
  (h_1 @Unit.unit)
  (fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937)
wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.ble_eq_true_of_le.match_1: (#0).0 (of class trepplein.Proj)
Nat.le_of_ble_eq_true: (#0).0 (of class trepplein.Proj)
Nat.le_of_ble_eq_true.match_1: (#0).0 (of class trepplein.Proj)
And.left: (#0).0 (of class trepplein.Proj)
And.right: (#0).1 (of class trepplein.Proj)
Nat.modCore._unary.proof_1: type error: definition Nat.modCore._unary.proof_1
wrong type:  (invImage
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
  instWellFoundedRelation).1  :  WellFounded
  ((invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0)
inferred type:  WellFounded
  ((invImage
    (fun (a_InitWF860InitDataNatDiv_hyg816 :
        PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
      a_InitWF860InitDataNatDiv_hyg816
      (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
          Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
    instWellFoundedRelation).0)
(invImage
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
  instWellFoundedRelation).0  !=def  (invImage
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
  instWellFoundedRelation).0
stuck on:  (invImage
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
  instWellFoundedRelation).0 (invImage
  (fun (a_InitWF860InitDataNatDiv_hyg816 :
      PSigma (fun (x : Nat) ↦ Nat)) ↦ PSigma.casesOn
    a_InitWF860InitDataNatDiv_hyg816
    (fun (x_InitDataNatDiv_hyg779 snd_InitDataNatDiv_hyg817 :
        Nat) ↦ SizeOf.sizeOf x_InitDataNatDiv_hyg779))
  instWellFoundedRelation).0
SizeOf.sizeOf: (#0).0 (of class trepplein.Proj)
Nat.mod.match_1: (#0).0 (of class trepplein.Proj)
Mod.mod: (#0).0 (of class trepplein.Proj)
HMod.hMod: (#0).0 (of class trepplein.Proj)
_private.Init.Data.Nat.Gcd.0.Nat.gcdF.match_1: type error: within (type of `@Nat.casesOn.{u_1}`)  Pi-type `Binding(zero,#1 @Nat.zero,Default), ∀ (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2` in `∀ (zero : #1 @Nat.zero) (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2`; context: List(x._@.Init.Data.Nat.Gcd._hyg.26, fun (x : @Nat) ↦ motive x); args: List(h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); List(fun (x : @Nat) ↦ motive x, x._@.Init.Data.Nat.Gcd._hyg.26, h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); checking @Nat.casesOn.{u_1} (fun (x : @Nat) ↦ motive x) x._@.Init.Data.Nat.Gcd._hyg.26
  (h_1 @Unit.unit)
  (fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937)
wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
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
Nat.pow.match_1: type error: within (type of `@Nat.casesOn.{u_1}`)  Pi-type `Binding(zero,#1 @Nat.zero,Default), ∀ (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2` in `∀ (zero : #1 @Nat.zero) (succ : (∀ (n : @Nat) , #3 (@Nat.succ n))) , #3 #2`; context: List(x._@.Init.Prelude._hyg.2941.2962, fun (x : @Nat) ↦ motive x); args: List(h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); List(fun (x : @Nat) ↦ motive x, x._@.Init.Prelude._hyg.2941.2962, h_1 @Unit.unit, fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937); checking @Nat.casesOn.{u_1} (fun (x : @Nat) ↦ motive x) x._@.Init.Prelude._hyg.2941.2962
  (h_1 @Unit.unit)
  (fun (n_InitPrelude_hyg3937 : @Nat) ↦ succ n_InitPrelude_hyg3937)
wrong type:  h_1 Unit.unit  :  (fun (x : Nat) ↦ motive x) Nat.zero
inferred type:  motive n
Nat.zero  !=def  n
stuck on:  Nat.zero n
Nat.zero_le: (#0).0 (of class trepplein.Proj)
Nat.succ_le_succ: (#0).0 (of class trepplein.Proj)
PProd.fst: (#0).0 (of class trepplein.Proj)
Add.add: (#0).0 (of class trepplein.Proj)
HAdd.hAdd: (#0).0 (of class trepplein.Proj)
Nat.succ_le_succ.match_1: (#0).0 (of class trepplein.Proj)
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
Nat.not_lt_zero: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_zero: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_zero.match_2: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_zero.match_1: (#0).0 (of class trepplein.Proj)
Nat.not_succ_le_zero.match_3: (#0).0 (of class trepplein.Proj)
LE.le: (#0).0 (of class trepplein.Proj)
LT.lt: (#0).0 (of class trepplein.Proj)
OfNat.ofNat: (#0).0 (of class trepplein.Proj)
WellFoundedRelation.wf: (#0).1 (of class trepplein.Proj)
WellFoundedRelation.rel: (#0).0 (of class trepplein.Proj)
