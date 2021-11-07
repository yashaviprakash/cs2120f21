import data.set

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}

<<<<<<< HEAD
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
=======

-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
>>>>>>> a31ae845118b6a7f2dfef98652b64d2ee9c26f87
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
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
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




<<<<<<< HEAD
def powerset (s : set β) := { s' | s' ⊆ s} -- the set of s prime which is the subset of s

-- want to show that the subset relation is antisymmetric
=======

/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
>>>>>>> a31ae845118b6a7f2dfef98652b64d2ee9c26f87
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
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
  
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
end

-- C
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
end


end relation
