-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- how to do case disjunct on a negation

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  -- not (P ∧ Q) means (P ∧ Q) → false
  -- from here we can use and elim rules to get
  -- P → false and Q → false which will give 
  -- forward proof
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h, 
    -- (P ∧ Q → false)
    -- to get not p and not q you need to get disjunct
    have pornp := classical.em P,
    have qornq := classical.em Q,
    cases pornp with p pn,
    cases qornq with q qn,
    have pandq : P ∧ Q := begin 
      apply and.intro p q,
    end,
    have f:= h pandq,
    apply false.elim f,
    apply or.intro_right _ _,
    exact qn,
    apply or.intro_left _ _,
    exact pn,
  -- backward
    assume h,
    assume pandq,
    have p := and.elim_left pandq,
    have q := and.elim_right pandq,
    cases h,
    have f := h p,
    exact f,
    -- apply or.elim h,
    -- assume np,
    have f := h q,
    exact f,
    
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p pn,
  cases qornq with q qn,
  -- P ∨ Q → false
  have porq : P ∨ Q := or.inl p,
  have f := h porq,
  apply false.elim f,
  have porq : P ∨ Q := or.inl p,
  have f := h porq,
  apply false.elim f,
  cases qornq,
  have porq : P ∨ Q := or.inr qornq,
  have f := h porq,
  apply false.elim f,
  apply and.intro pn qornq,

end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume h1,
  apply or.elim h1,
  -- left disjunct
  assume p,
  apply or.intro_left Q p,
  -- right disjunct
  assume npandq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p pn,
  cases qornq with q qn,
  -- first case
  apply or.intro_left _ _,
  exact p,
  -- second case
  apply or.intro_left _ _,
  exact p,
  cases qornq,
  apply or.intro_right _ _,
  exact qornq,
  -- third case
  have q := and.elim_right npandq,
  apply or.intro_right _ _,
  exact q,
  -- backward
  assume h,
  cases h,
  -- first case
  apply or.intro_left _ _,
  exact h,
  -- second case
  have pornp := classical.em P,
  cases pornp with p pn,
  apply or.intro_left _ _,
  exact p,
  apply or.intro_right _ _,
  apply and.intro pn h,
 
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume h,
    have porq : P ∨  Q := and.elim_left h,
    have porr : P ∨ R := and.elim_right h,
    apply or.elim porq,
    -- left disjunct
      assume p,
      apply or.intro_left (Q ∧ R) p,
    -- right disjunct
      assume q,
      apply or.elim porr,
      assume p,
      apply or.intro_left (Q ∧ R) p,
      assume r,
      apply or.intro_right P _,
      apply and.intro q r,
  -- backward
    assume h,
    apply or.elim h,
    -- left disjunct
      assume p,
      apply and.intro _ _,
      apply or.intro_left Q p,
      apply or.intro_left R p,
    -- right disjunct
      assume qandr,
      have q: Q := and.elim_left qandr,
      have r: R := and.elim_right qandr,
      apply and.intro _ _,
      apply or.intro_right P q,
      apply or.intro_right P r,

end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  -- forward
  assume h,
  have porq : P ∨ Q := and.elim_left h,
  have rors : R ∨ S := and.elim_right h,
  apply or.elim porq,
    -- left disjunct
     assume p,
     apply or.elim rors,
      -- left disjunct using rors
        assume r,
        apply or.intro_left _ _,
        apply and.intro p r,
      -- right disjunct using rors
        assume s,
        apply or.intro_right _ _,
        apply or.intro_left _ _,
        apply and.intro p s,
    -- right disjunct
    assume q,
    apply or.elim rors,
      --left disjunct using rors
        assume r,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        apply or.intro_left _ _,
        apply and.intro q r,
      -- right disjunct using rors
        assume s,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        apply or.intro_right _ _,
        apply and.intro q s,
  -- backward
  assume h,
  apply or.elim h,
    -- left disjunct
    assume pandr,
    have p : P := and.elim_left pandr,
    have r: R := and.elim_right pandr,
    apply and.intro _ _,
    apply or.intro_left Q p,
    apply or.intro_left S r,
    -- right disjunct
    assume h1,
    apply or.elim h1,
    -- left disjunct using h1
    assume pands,
    have p : P := and.elim_left pands,
    have s: S := and.elim_right pands,
    apply and.intro _ _,
    apply or.intro_left Q p,
    apply or.intro_right R s,
    -- right disjunct using h1
    assume h2,
    apply or.elim h2,
    assume qandr,
    have q: Q := and.elim_left qandr,
    have r: R := and.elim_right qandr,
    apply and.intro _ _,
    apply or.intro_right P q,
    apply or.intro_left S r,
    assume qands,
    have q: Q := and.elim_left qands,
    have s: S := and.elim_right qands,
    apply and.intro _ _,
    apply or.intro_right P q,
    apply or.intro_right R s,

end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ ∀ (n : ℕ), n = 0 :=
begin
  assume n,
  -- find contradiction in a case where n is not equal zero, then say contradiction
  have contradictory := n 1,
  contradiction,

end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  have q := h p,
  apply or.intro_right _ _,
  exact q,
  apply or.intro_left _ _,
  exact pn,
  -- backward
  assume h,
  apply or.elim h,
  assume np,
  assume p,
  contradiction,
  assume q,
  assume p,
  exact q,

end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assume nq,
  assume p,
  have q := h p,
  contradiction,
  assume nq,
  assume p,
  contradiction,

end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p pn,
  cases qornq with q qn,
  assume qimp,
  exact p,
  assume qimp,
  exact p,
  assume qimp,
  have f := h pn,
  contradiction,
 
end

