condition not met for 
@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
        @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
  ((fun (x_InitPrelude_hyg3059 : @Nat)
      (x_InitPrelude_hyg5431 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059) n)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959
              x_InitPrelude_hyg29412962 :
              @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
        n) ↦ (fun (n_InitPrelude_hyg2985 : @Nat) ↦ (fun (a b : @Nat)
        (x_InitPrelude_hyg5431 :
          @Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
        (@PProd.fst.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                n_ih_0) @PUnit.{1}) b)
          (@PProd.fst.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) b)
              (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                    n_ih_0) @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431)
          a)) n n_InitPrelude_hyg2985) n) @Nat.zero @PUnit.unit.{max 1 1} 

@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
  ((fun (a : @Unit) ↦ @OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) @Unit.unit)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : @Nat) ↦ (fun (a : @Nat) ↦ a)
      n_InitPrelude_hyg3937) n)
  (@PProd.fst.{1 1}
    ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
          @Nat) , @Nat) @Nat.zero)
    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
        (@PProd.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) n) n_ih) @PUnit.{1}) @Nat.zero)
    (@PProd.fst.{1 1}
      (@PProd.{1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) @Nat.zero)
        (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
          (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n) n_ih) @PUnit.{1}) @Nat.zero)) @PUnit.{1}
      (@PProd.mk.{max 1 1 max 1 1}
        (@PProd.{1 max 1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) @Nat.zero)
          (@Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) @Nat.zero)) @PUnit.{max 1 1}
        (@Nat.rec.{max 1 1}
          (fun (t : @Nat) ↦ @PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) t)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) t))
          (@PProd.mk.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) @Nat.zero) @PUnit.{max 1 1}
            ((fun (x_InitPrelude_hyg5385 : @Nat)
                (f :
                  @Nat.below.{1}
                    (fun (x_InitPrelude_hyg2941 :
                        @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                    x_InitPrelude_hyg5385)
                (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
                (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                    @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
                x_InitPrelude_hyg5385
                (fun (x_InitPrelude_hyg3059 : @Nat)
                  (x_InitPrelude_hyg5431 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      n) ↦ x_InitPrelude_hyg3059)
                (fun (a b : @Nat)
                  (x_InitPrelude_hyg5431 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      (@Nat.succ b)) ↦ @Nat.pred
                  (@PProd.fst.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n) n_ih) @PUnit.{1}) b)
                    (@PProd.fst.{1 1}
                      (@PProd.{1 1}
                        ((fun (x_InitPrelude_hyg2941 :
                              @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                          b)
                        (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                          (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                            (@PProd.{1 1}
                              ((fun (x_InitPrelude_hyg2941 :
                                    @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                                    @Nat) , @Nat) n) n_ih) @PUnit.{1}) b))
                      @PUnit.{1} x_InitPrelude_hyg5431) a)) f) @Nat.zero
              @PUnit.unit.{max 1 1}) @PUnit.unit.{max 1 1})
          (fun (n : @Nat)
            (n_ih :
              @PProd.{1 max 1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                (@Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n)) ↦ @PProd.mk.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) (@Nat.succ n))
            (@PProd.{max 1 1 max 1 1}
              (@PProd.{1 max 1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                (@Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n))
              @PUnit.{max 1 1})
            ((fun (x_InitPrelude_hyg5385 : @Nat)
                (f :
                  @Nat.below.{1}
                    (fun (x_InitPrelude_hyg2941 :
                        @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                    x_InitPrelude_hyg5385)
                (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
                (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                    @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
                x_InitPrelude_hyg5385
                (fun (x_InitPrelude_hyg3059 : @Nat)
                  (x_InitPrelude_hyg5431 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      n) ↦ x_InitPrelude_hyg3059)
                (fun (a b : @Nat)
                  (x_InitPrelude_hyg5431 :
                    @Nat.below.{1}
                      (fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                      (@Nat.succ b)) ↦ @Nat.pred
                  (@PProd.fst.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n_0) n_ih_0) @PUnit.{1}) b)
                    (@PProd.fst.{1 1}
                      (@PProd.{1 1}
                        ((fun (x_InitPrelude_hyg2941 :
                              @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                          b)
                        (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                          (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                            (@PProd.{1 1}
                              ((fun (x_InitPrelude_hyg2941 :
                                    @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                                    @Nat) , @Nat) n_0) n_ih_0) @PUnit.{1}) b))
                      @PUnit.{1} x_InitPrelude_hyg5431) a)) f) (@Nat.succ n)
              (@PProd.mk.{max 1 1 max 1 1}
                (@PProd.{1 max 1 1}
                  ((fun (x_InitPrelude_hyg2941 :
                        @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                  (@Nat.below.{1}
                    (fun (x_InitPrelude_hyg2941 :
                        @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n))
                @PUnit.{max 1 1} n_ih @PUnit.unit.{max 1 1}))
            (@PProd.mk.{max 1 1 max 1 1}
              (@PProd.{1 max 1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                (@Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n))
              @PUnit.{max 1 1} n_ih @PUnit.unit.{max 1 1})) @Nat.zero)
        @PUnit.unit.{max 1 1})) (@Nat.succ n))

 argument sizes must match
condition not met for 
@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
        @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
  ((fun (x_InitPrelude_hyg3059 : @Nat)
      (x_InitPrelude_hyg5431 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059) n)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959
              x_InitPrelude_hyg29412962 :
              @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
        n) ↦ (fun (n_InitPrelude_hyg2985 : @Nat) ↦ (fun (a b : @Nat)
        (x_InitPrelude_hyg5431 :
          @Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
        (@PProd.fst.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                n_ih_0) @PUnit.{1}) b)
          (@PProd.fst.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) b)
              (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                    n_ih_0) @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431)
          a)) n n_InitPrelude_hyg2985) n) (@Nat.succ m)
  (@PProd.mk.{max 1 1 max 1 1}
    (@PProd.{1 max 1 1}
      ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) m)
      (@Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) m)) @PUnit.{max 1 1}
    (@Nat.rec.{max 1 1}
      (fun (t : @Nat) ↦ @PProd.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t)
        (@Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t))
      (@PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) @Nat.zero) @PUnit.{max 1 1}
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                      n_ih) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) @Nat.zero @PUnit.unit.{max 1 1})
        @PUnit.unit.{max 1 1})
      (fun (n : @Nat)
        (n_ih :
          @PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) ↦ @PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) (@Nat.succ n))
        (@PProd.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1})
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                        n_0) n_ih_0) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n_0) n_ih_0) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) (@Nat.succ n)
          (@PProd.mk.{max 1 1 max 1 1}
            (@PProd.{1 max 1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)
              (@Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
            @PUnit.unit.{max 1 1}))
        (@PProd.mk.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
          @PUnit.unit.{max 1 1})) m) @PUnit.unit.{max 1 1}) 

@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
  ((fun (a : @Unit) ↦ @OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) @Unit.unit)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : @Nat) ↦ (fun (a : @Nat) ↦ a)
      n_InitPrelude_hyg3937) n)
  (@HSub.hSub.{0 0 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat) n m)

 argument sizes must match
condition not met for 
@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
        @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat)
    (@OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) x)
  ((fun (x_InitPrelude_hyg3059 : @Nat)
      (x_InitPrelude_hyg5431 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059)
    (@OfNat.ofNat.{0} @Nat n (@instOfNatNat n)))
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959
              x_InitPrelude_hyg29412962 :
              @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat)
          (@OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) x)
        n) ↦ (fun (n_InitPrelude_hyg2985 : @Nat) ↦ (fun (a b : @Nat)
        (x_InitPrelude_hyg5431 :
          @Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
        (@PProd.fst.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                n_ih_0) @PUnit.{1}) b)
          (@PProd.fst.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) b)
              (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                    n_ih_0) @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431)
          a)) (@OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) n_InitPrelude_hyg2985)
    n) (@Nat.succ n)
  (@PProd.mk.{max 1 1 max 1 1}
    (@PProd.{1 max 1 1}
      ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) n)
      (@Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) n)) @PUnit.{max 1 1}
    (@Nat.rec.{max 1 1}
      (fun (t : @Nat) ↦ @PProd.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t)
        (@Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t))
      (@PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) @Nat.zero) @PUnit.{max 1 1}
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                      n_ih) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) @Nat.zero @PUnit.unit.{max 1 1})
        @PUnit.unit.{max 1 1})
      (fun (n : @Nat)
        (n_ih :
          @PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) ↦ @PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) (@Nat.succ n))
        (@PProd.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1})
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                        n_0) n_ih_0) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n_0) n_ih_0) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) (@Nat.succ n)
          (@PProd.mk.{max 1 1 max 1 1}
            (@PProd.{1 max 1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)
              (@Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
            @PUnit.unit.{max 1 1}))
        (@PProd.mk.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
          @PUnit.unit.{max 1 1})) n) @PUnit.unit.{max 1 1}) 

@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
  ((fun (a : @Unit) ↦ @OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) @Unit.unit)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : @Nat) ↦ (fun (a : @Nat) ↦ a)
      n_InitPrelude_hyg3937) n)
  (@HSub.hSub.{0 0 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat)
    (@OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) n)

 argument sizes must match
condition not met for 
@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
        @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) (@Nat.succ n) x)
  ((fun (x_InitPrelude_hyg3059 : @Nat)
      (x_InitPrelude_hyg5431 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059) (@Nat.succ n))
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959
              x_InitPrelude_hyg29412962 :
              @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat)
          (@Nat.succ n) x) n) ↦ (fun (n_InitPrelude_hyg2985 : @Nat) ↦ (fun (a
          b :
          @Nat)
        (x_InitPrelude_hyg5431 :
          @Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
        (@PProd.fst.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                n_ih_0) @PUnit.{1}) b)
          (@PProd.fst.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) b)
              (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                    n_ih_0) @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431)
          a)) (@Nat.succ n) n_InitPrelude_hyg2985) n) (@Nat.succ (@Nat.succ m))
  (@PProd.mk.{max 1 1 max 1 1}
    (@PProd.{1 max 1 1}
      ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) (@Nat.succ m))
      (@Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) (@Nat.succ m))) @PUnit.{max 1 1}
    (@Nat.rec.{max 1 1}
      (fun (t : @Nat) ↦ @PProd.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t)
        (@Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t))
      (@PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) @Nat.zero) @PUnit.{max 1 1}
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                      n_ih) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) @Nat.zero @PUnit.unit.{max 1 1})
        @PUnit.unit.{max 1 1})
      (fun (n : @Nat)
        (n_ih :
          @PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) ↦ @PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) (@Nat.succ n))
        (@PProd.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1})
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                        n_0) n_ih_0) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n_0) n_ih_0) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) (@Nat.succ n)
          (@PProd.mk.{max 1 1 max 1 1}
            (@PProd.{1 max 1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)
              (@Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
            @PUnit.unit.{max 1 1}))
        (@PProd.mk.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
          @PUnit.unit.{max 1 1})) (@Nat.succ m)) @PUnit.unit.{max 1 1}) 

@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
  ((fun (a : @Unit) ↦ @OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) @Unit.unit)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : @Nat) ↦ (fun (a : @Nat) ↦ a)
      n_InitPrelude_hyg3937) n)
  (@HSub.hSub.{0 0 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat)
    (@Nat.succ n) (@Nat.succ m))

 argument sizes must match
condition not met for 
@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
        @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
  ((fun (x_InitPrelude_hyg3059 : @Nat)
      (x_InitPrelude_hyg5431 :
        @Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) n) ↦ x_InitPrelude_hyg3059) n)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg29402959
              x_InitPrelude_hyg29412962 :
              @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg29412962) , @Nat) n x)
        n) ↦ (fun (n_InitPrelude_hyg2985 : @Nat) ↦ (fun (a b : @Nat)
        (x_InitPrelude_hyg5431 :
          @Nat.below.{1}
            (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) (@Nat.succ b)) ↦ @Nat.pred
        (@PProd.fst.{1 1}
          ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                @Nat) , @Nat) b)
          (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
            (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
              (@PProd.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                n_ih_0) @PUnit.{1}) b)
          (@PProd.fst.{1 1}
            (@PProd.{1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) b)
              (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n_0)
                    n_ih_0) @PUnit.{1}) b)) @PUnit.{1} x_InitPrelude_hyg5431)
          a)) n n_InitPrelude_hyg2985) n) (@Nat.succ m)
  (@PProd.mk.{max 1 1 max 1 1}
    (@PProd.{1 max 1 1}
      ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) m)
      (@Nat.below.{1}
        (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
            @Nat) , @Nat) m)) @PUnit.{max 1 1}
    (@Nat.rec.{max 1 1}
      (fun (t : @Nat) ↦ @PProd.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t)
        (@Nat.below.{1}
          (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) t))
      (@PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) @Nat.zero) @PUnit.{max 1 1}
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) n)
                      n_ih) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n : @Nat) (n_ih : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n) n_ih) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) @Nat.zero @PUnit.unit.{max 1 1})
        @PUnit.unit.{max 1 1})
      (fun (n : @Nat)
        (n_ih :
          @PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) ↦ @PProd.mk.{1 max 1 1}
        ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
              @Nat) , @Nat) (@Nat.succ n))
        (@PProd.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1})
        ((fun (x_InitPrelude_hyg5385 : @Nat)
            (f :
              @Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) x_InitPrelude_hyg5385)
            (x_InitPrelude_hyg5384 : @Nat) ↦ @Nat.mul.match_1.{1}
            (fun (x_InitPrelude_hyg29402959 x_InitPrelude_hyg29412962 :
                @Nat) ↦ ∀ (x_InitPrelude_hyg2988 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  x_InitPrelude_hyg29412962) , @Nat) x_InitPrelude_hyg5384
            x_InitPrelude_hyg5385
            (fun (x_InitPrelude_hyg3059 : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  n) ↦ x_InitPrelude_hyg3059)
            (fun (a b : @Nat)
              (x_InitPrelude_hyg5431 :
                @Nat.below.{1}
                  (fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                  (@Nat.succ b)) ↦ @Nat.pred
              (@PProd.fst.{1 1}
                ((fun (x_InitPrelude_hyg2941 :
                      @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                  (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                    (@PProd.{1 1}
                      ((fun (x_InitPrelude_hyg2941 :
                            @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                        n_0) n_ih_0) @PUnit.{1}) b)
                (@PProd.fst.{1 1}
                  (@PProd.{1 1}
                    ((fun (x_InitPrelude_hyg2941 :
                          @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat) b)
                    (@Nat.rec.{2} (fun (t : @Nat) ↦ Type 0) @PUnit.{1}
                      (fun (n_0 : @Nat) (n_ih_0 : Type 0) ↦ @PProd.{1 1}
                        (@PProd.{1 1}
                          ((fun (x_InitPrelude_hyg2941 :
                                @Nat) ↦ ∀ (a_InitPrelude_hyg2934 : @Nat) , @Nat)
                            n_0) n_ih_0) @PUnit.{1}) b)) @PUnit.{1}
                  x_InitPrelude_hyg5431) a)) f) (@Nat.succ n)
          (@PProd.mk.{max 1 1 max 1 1}
            (@PProd.{1 max 1 1}
              ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)
              (@Nat.below.{1}
                (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                    @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
            @PUnit.unit.{max 1 1}))
        (@PProd.mk.{max 1 1 max 1 1}
          (@PProd.{1 max 1 1}
            ((fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)
            (@Nat.below.{1}
              (fun (x_InitPrelude_hyg2941 : @Nat) ↦ ∀ (a_InitPrelude_hyg2934 :
                  @Nat) , @Nat) n)) @PUnit.{max 1 1} n_ih
          @PUnit.unit.{max 1 1})) m) @PUnit.unit.{max 1 1}) 

@Nat.rec.{1}
  (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
  ((fun (a : @Unit) ↦ @OfNat.ofNat.{0} @Nat n (@instOfNatNat n)) @Unit.unit)
  (fun (n : @Nat)
    (n_ih :
      (fun (x : @Nat) ↦ (fun (x_InitPrelude_hyg42494260 : @Nat) ↦ @Nat) x)
        n) ↦ (fun (n_InitPrelude_hyg3937 : @Nat) ↦ (fun (a : @Nat) ↦ a)
      n_InitPrelude_hyg3937) n)
  (@HSub.hSub.{0 0 0} @Nat @Nat @Nat (@instHSub.{0} @Nat @instSubNat) n m)

 argument sizes must match
-- successfully checked 320 declarations
