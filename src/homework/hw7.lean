import ..instructor.lectures.lecture_23

namespace relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  
-- Strangely Lean's library does define asymmetric, so here it is.
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

-- less than or equal is not asymmetric, because they could be reflexive
-- less than or equal is antisymmetric, if a is related to b and b is
-- related to a then they must be equal
-- for a relation to b reflexive, you have to have a pair for every value in that set

-- Prove both formally and in English.
-- if r is asymmetric than r is not reflexive
-- for every x y in the relation y x is not in the relation (asymm)
-- not refelxive means that there is at least one case in the relation where
-- x is not related to itself

-- it's the existence of a b that allowed this proof 
-- would give beta value to refl and would give that result to asymm
-- ask about empty set again
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume ex,
  assume asym,
  assume refl, -- proof by negation
  -- what if there is no x of type beta, what if x is an empty set
  cases ex with b pf,
  have rbb := refl b, -- apply universal generalization to refl
  have contra := asym rbb,
  contradiction,
end



/-
Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. Is it actually true?
If not, what condition needs to be added to make it true? See
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html
-/
-- if a relation is transitive, and it's reflexive, then it cannot be
-- antisymmetric at the same time
-- empty set will not give a way to prove contradiction
example : (∃ (b: β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume ex trans refl asymm,
  -- prove contradiction by showing a case where (a, b) relates to 
  -- r and (b, a) relates to r
  -- need to show that all three are inconsistent and that they lead to
  -- a contradiction
  /-
  if you don't have a beta, and you quanitfy over an empty set, you get true
  -/
  -- there's no way to derive a contradiction because there is no contradiction
  -- must add exists to make this statement true
  /-
  proof by contradiction is a form of proof that establishes the truth or the validity 
  of a proposition, by showing that assuming the proposition to be false leads to a contradiction.
  -/
  cases ex with b pf,
  have rbb := refl b,
  have contra := asymm rbb,
  contradiction,

end



/-
State and prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and then give
an informal proof, of this proposition. You may use the following
formal definition of the powerset of a given set, s. 
-/

def powerset (s : set β) := { s' | s' ⊆ s} -- the set of s prime which is the subset of s

-- want to show that the subset relation is antisymmetric
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), -- s1 and s2 are in poweret of s
            s1 ⊆ s2 → 
            s2 ⊆ s1 →  -- if subsets of each other
            s1 = s2 := -- sets must be equal
begin
  assume s s1 s2,
  assume ex_s1 ex_s2 s1setof s2setof,
  apply set.ext _,
  assume b,
  split,
  -- forward
    -- to prove b exists in s1 i have to prove that 
    assume bs1,
    exact (s1setof bs1),
  -- backward
    assume bs2,
    exact (s2setof bs2),

end

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#3: Formally state and prove each of the following propositions.
Remember that the ring tactic is useful for producing proofs of
algebraic equalities involving + and *. You can use the phrase,
"by basic algebra" when translating the use of this tactic into
English.
-/

-- 3a: For any n, 1 divides n.

example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro (n),
  ring,
end

-- 3b. For any n, n divides n

example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

-- #3c. divides is reflexive (use our reflexive predicate)

example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 

-- #3d. divides is transitive

example : ∀ h n k, divides h n → divides n k → divides h k :=
begin
  assume h n k,
  unfold divides,
  assume ex1 ex2,
  cases ex1 with k n,
  cases ex2 with k_1 n_1,
  apply exists.intro, 

end 

/- 
#3d. is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here

/- 
#3e. Prove that divides is antisymmetric. Use the
anti_symmetric predicate to state the proposition
formally.
-/
example : relations.anti_symmetric divides := 
begin
  unfold relations.anti_symmetric divides,
  assume x y kx ky,
  cases kx with kxv kxpf,
  cases ky with kyv kypf,
  rw kxpf at kypf,
  /-
  From kypf we can deduce by basic algebra
  that kyv = kxv = 1, and the rewriting kxv
  as 1 in kxpf, we get that y = x. The proof
  of the conclusion then follows by symmetry
  of equality. We don't yet quite have the
  tools to reason formally to the conlusion
  that kxv and kyv are both one, so we'll 
  just admit it as an axiom for now, using
  sorry to remind us to come back and visit
  this point again when we're equipped to 
  polish off the formal proof.
  -/
  sorry,  
end


example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume h x k,
  have nk := h k,
  contradiction,
end

example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive,
  assume h k,
  assume x y,
  assume rxy,
  assume nryx,
  have f := k rxy nryx,
  have nrxx := h x,
  contradiction,
end

example : (∃ (b: β), true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin

end



end relation