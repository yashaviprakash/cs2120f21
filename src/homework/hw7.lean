import ..instructor.lectures.lecture_23

namespace relation

/-
Questions : 4b, 3d, 3e

5c, 5b, 4f, 4d
-/

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


/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
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
Proof: Given that there exists some object of type beta, we can show that the 
properties of reflexivity and asymmetry cannot be applied to the same relation, 
as there exists a contradiction in this conjecture. Formally, we showed that if a relation
were to relate to itself, then it could not be simultaneously be symmetric. This
concludes our proof by contradiction. QED.
-/



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
Proof: 
-/



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
Proof: For any two sets that exist in a power set, if the first
set is a subset of the second, and the second set is the subset of
the first, then we can conclude that both sets are equal. This proof
can be proven true using the set extensionality axiom, which restates
the proposition to be that any value that exists in the first subset, 
exists in the second and vice versa. Thus if every value that exists
in both sets are the same, then the subset relation is antisymmetric.
QED.
-/

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
  apply exists.intro (n),
  ring,
end
/-
Proof: To prove that 1 divides n, for any n, we must show there
exists some k for which n = k * 1. The only case that such proposition
can be true is if k = n. QED.
-/

-- B. For any n, n divides n

example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end
/-
Proof: To prove that n divides n, for any n, we must show there
exists some k for which n = k * n. The only case that such proposition
can be true is if k = 1. QED.
-/

-- C. divides is reflexive (use our reflexive predicate)

example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 
/-
Proof: To prove that divides is reflexive, we can understand that
every number is divisible by itself. To prove such proposition,
we must show that, for any x, there exists some k for which x = k * x. 
The only case that such proposition can be true is if k = 1. QED.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume h1 h2,
  cases h1 with w1 pf1,
  cases h2 with w2 pf2,
  apply exists.intro (w1 * w2), -- think about concrete example
  rw pf2,
  rw pf1,
  ring,
  
end 
/-
Proof: To prove that divides is transitive, we can understand that, for
any numbers x, y, and z, if y divides x, and z divides y, then z divides x.
To prove such proposition, we must show that for z divides y, there exists
some k such that z = k * x, such that y = k1 * x and z = k2 * y. The only case 
that such proposition can be true is if k = k1 * k2. QED.
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/- Divides is not symmetric. If we assume that m = 2 and n = 4,
then we understand that 4 = k * 2 does not equal 2 = k * 4. 
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin
  unfold anti_symmetric divides,
  assume x y h1 h2,
  cases h1 with w pf,
  cases h2 with w1 pf1,
  rw pf,
  rw pf1,
  have w : w = 1 := sorry,
  have w1 : w1 = 1 := sorry,
  rw w,
  rw w1,
  ring,
end
/-
Proof: To prove that divides is anti symmetric, we can understand that, for any
x and y, if y is divisible by x and x is divisible by y, then x = y. To prove x = y, 
then we must show that x divides y one time and y divides x one time. From here,
we must show that if y = k1 * x and x = k2 * y, then, by extension, x = (k1 * k2) * x. 
When we divide by x, then (k1 * k2) = 1. Because k1 and k2 are both natural numbers, then
k1 = k2 = 1. QED. 
-/

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
  unfold asymmetric irreflexive,
  assume h x rxx, -- giving a case of a reflexive proof
  have contra := h rxx, -- if symmetric, would relate back to itself, but it doesn't
  contradiction, -- proof by contradiction
end
/-
Proof: To prove that a relation is irreflexive if it is asymmetric, we must show 
a relation cannot be simultaneously reflexive and asymmetric. We can prove this
by contradiction, by using of our proof for reflexivity, and applying to our
proof for asymmetry. This will yield a proof that the relation is not reflexive.
The existence of both proofs allows to prove the original proposition by contradiction.
QED. 
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric, 
  assume irr trans x y,
  assume rxy ryx,
  have notrxx := irr x, -- rxx → false 
  have rxx := trans rxy ryx, -- note of this
  contradiction,

end
/-
Proof: To prove that a relation is asymmetric, it will suffice us to prove
that the relation is irreflexive and transitive. We can prove this by contradiction,
by showing a case where the relation is symmetric, and showing the relation cannot be
simultaneously irreflexive and transitive. By using our proof that the relation is
symmetric, we can derive a proof that the relation is reflexive through the proof
of transitivity. The simultaneous existence of an irreflexive and reflexive proof
allows us to prove the original proposition by contradiction. QED.
-/

-- C
example : (transitive r → ¬ symmetric r → ¬ irreflexive r) :=
begin
  _
end

/-
Explanation: This proposition is not provable because if a relation
was transitive and not symmetric, then the relation COULD be irreflexive.
When a relation is not symmetric, it could be the case that some sets
were symmetric and that some sets are not symmetric. It could also be 
the case that there are no symmetric case. In this instance, where
sets are transitive and not symmetric, sets are irreflexive. QED.

-/

end relation
