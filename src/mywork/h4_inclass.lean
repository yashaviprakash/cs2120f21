/-

Introduction rules and Elimination rules

= (Equality):

introduction rule: axiom of the reflexivity of equality (eq.refl)
elimination rule:  axiom of substituability of equality (eq.subs)

∧ (And)

introduction rule: and.intro _ _
elimination rule: and.elim_left and and.elim_right

∨ (Or)

introduction rule: or.intro_left and or.intro_right
elimination rule: or.elim

∀ (For All)

introduction rule: assume, then show rest
elimination rule: apply

→ (Implies)

introduction rule: assume, then show rest
elimination rule: apply

¬ (Not)
introduction rule: P → false
elimination rule: haven't talked about it yet

↔ (If and only If)

∃ (Exists)

introduction rule: 
elimination rule: 

true

introduction rule: true.intro
elimination rule: no elimination rule for true, doesn't give you the opportunity to prove anythign else

false

introduction rule: no proofs, no introduction rules
elimination rule: false.elim

-/

--1 (notation means not 0=1, need to use proof by negation and negation intro)
example: 0 ≠ 1 :=
begin 
  -- ¬ (0=1)
  -- (0=1) → false
  assume h,
  cases h,

end

--2
/- whats the main connective? implication

if 0 does not equal 0, then 2 = 3-/
example: 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  --exact h(eq.refl 0) is what you want to say
  have f: false := h(eq.refl 0),
  exact false.elim (f),
  -- or exact false.elim(h(eq.refl 0))
end

--3 (use rain to help understand what you want to say)
--if my dog is blue then it's false that my dog is not blue
example: ∀ (P: Prop), P → ¬ ¬ P :=
begin
  assume P,
  -- ¬ ¬ P 
  -- ¬ P is P → false
  -- ¬ (P → false)
  assume (p: P),
  -- ¬ ¬ P means ¬ P → false
  -- this is the same as (P → false) → false
  -- implicaiton, so assume P → false then apply
  assume h,
  -- contradiction because you have a proof of P and a proof of not P
  -- contradictions are good because you can just stop
  --contradiction,
  -- alternative:
  -- h acts as a function, so you can apply h to proof p
  have f := h p,
  cases f,
  -- or exact false.elim f,

end