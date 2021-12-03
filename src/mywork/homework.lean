import data.set
import ..instructor.lectures.lecture_21

namespace hw_5

-- personal notes 

/-
EXISTS INTRO

* A predicate is a proposition with one or more parameters 
* The introducton rule for exists takes two arguments: a witness value, w, and 
a proof that the witness satisfies the predicate
* It's often clear and useful to apply the introduction rule to a witness, leaving
the proof that it satisfies teh predicate to a separate sub-goal/sub-task (notice how
the value of the parameter is incorporated into the final proposition to be proved: that
the value has the required property)

* dependely type pairs that constitute proofs of existential propositions <witness, proof>
* For existential propositions written like ∃ x y z, P x y z it's important to note that they
might hide a little bit of insight, which is that you do actually need to apply exists.intro to 
produce three different proofs here, one for each ∃ 

EXISTS ELIMINATION
* If you have a proof, ex, of ∃ (x: X), P x, you can apply exists.elim to ex, and (after a 
few more simple maneuvers) have yourself a specific value, (w: X), and a proof that w satisfies
P, i.e., (pf: P w)
-/

-- lecture 13 problems

-- A -- 
example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff, -- there is some value b such that it satisfies this predicate, b = ff, apply intro to witness
  exact rfl, -- leaving proof as a subgoal
end

-- B -- 
example : 
  (exists (b : bool), b && tt = ff) → -- if there exists some b such that it satisfies this predicate
  (∃ (b : bool), true) := -- then there exists a boolean value
begin
  assume h, -- assume premise
  cases h with w pf, -- exists elimination
  apply exists.intro w, -- introduce exists
  apply trivial, -- the rest is easy
  -- apply true.intro
end


/-
Beachballs! What could be more fun
-/

axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green
  (Red : Ball → Prop)     -- a Ball can be Red 
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red
  (b1g : Green b1)        -- b1 is green
  (b2r : Red b2)          -- b2 is red


/-
Translate the propositions into English, then
prove them formally.
If there's a Ball that's Red and Green then 
there is a ball that's Red.
-/
example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  -- around minute 13:30 - 14:00 
  assume h,               -- assume there's a red and green ball (assume premise)
  cases h with b rg,      -- get a name, b, for the ball and a proof about b
  apply exists.intro b _,   -- use b as a witness to the proposition to be proved
  exact rg.left,          -- the proof it's red is part of that it's red and green
end 

/- exists elim looks at premise, and does the same thing as cases-/

/-
If there's a ball, b, that's red or green
then there's a ball, b, that greed or red.
-/
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,             -- there's ball that's red or green
  cases h with w pf,    -- name it w with pf a proof of Red w ∨ Green w
  apply exists.intro w, -- use w as witness, need proof of Green w ∨ Red d
  cases pf,             -- basically proof of X ∨ Y → Y ∨ X at this point
  exact or.inr pf,
  exact or.inl pf,
end 

/-
How about this one? Translate it into Enlish. Do
you believe it?
-/
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with w pf,
  cases pf, 
  apply exists.intro w,
  assumption,
  apply exists.intro w,
  _
end 

/-
If there's a red ball then there's a ball that's red or green.
-/
example : -- be sure you can do this one yourself!
    (∃ (b : Ball), Red b) → 
    (∃ (b : Ball), Red b ∨ Green b) := 
begin
  assume h,
  cases h with b r,
  apply exists.intro b _,
  apply or.intro_left _ _,
  exact r,
end 

/-
Social Networks
-/

axioms
  (Person : Type)
  (Nice : Person → Prop) -- given a person, that person is nice
  (Likes : Person → Person → Prop) -- function that takes in two people and returns a proposition that the first person likes the second person

/-
What does this say, in English? It is true?
-/
example : 
  -- If there's a person, p1, who everyone likes,
  -- there exists a single person such that for all people, a person p2 (every person) likes p1
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  -- then everyone likes someone
  -- for every person, there exists a person that they like
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h, -- premise is a giant exists statement whereas right side of implication is a giant for all statement
  cases h with p pf, -- pf : particular proposition applies to particular person p
  assume e,
  apply exists.intro p,
  exact (pf e),
end

/-
CS2120 F21 HW5
The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:
(1) Write a fluent English-language statement
of the proposition to be proved. 
(2) Provide a formal proof of the proposition.
(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
turns an α value into a β value, then, for any α value, 
a proof of q applied to the β value using that function can
be derived given that that α value satisfies predicate p. 
Additionally, if there exists a value of type α  that satisfies predicate
p, then there exists a value of type β that satisifes predicate q.
-/


-- Give your formal proof here
begin
  assume h1 h2,
  cases h1 with w1 pf1,
  cases h2 with w2 pf2,
  have step_1 := pf1 w2,
  have step_2 := step_1 pf2,
  apply exists.intro (w1 w2),
  exact step_2,
end

-- Give your informal proof here
/-
To prove this proposition, the first and second premise must be assumed. Given 
that both premises are existential propositions, exists elimination using case 
analysis must be applied on both propositions. This yields the wtinesses (the function 
f that maps values of type α to values of type β and the value a of type α) 
and the proofs (the proof of the for all proposition and the proof that a satisfies
predicate p) for both propositions. This gives sufficient information to prove 
the implication that there exists an object of type β that satisfies predicate q. 

To prove the implication, the top-down approach can be employed on the application of
the introduction rule for exists. To obtain the witness, f can be applied to a (the first
witness can be applied to the second witness). 

To obtain the proof, a proof that the value f(a) satisifes the predicate q, 
the proof of the value a and the proof that a satisfies predicate p must be applied
to the for all proposition. This satisfies the proof. QED. 

-/

end hw_5


namespace hw_6

/- Set Extensionality 

We define the concept of a set
of values of type α as nothing
other than a predicate on values
of this type. (α → Prop)


And given any one-place predicate
on α, we can view it as defining
a set.


**def set_of {α : Type} (p : α → Prop) : set α := p**

  set.ext : 
    ∀ {α : Type u_1} {a b : set α}, 
    (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b

  
Here's the most important point: If we 
apply ext to a "hole" where the proof 
of the bi-implication should be, we will 
have our proof of L = X, with only the
proof of ∀ x, x ∈ L ↔ x ∈ X remaining 
to be produced. In this sense, applying
the axiom of set extensionality without
giving a proof of the bi-implication,
*reduces* the problem of proving L = X
to the problem of proving ∀ x, x ∈ L ↔ 
x ∈ X. And that is what we see next. 


To prove L = X, it will suffice to prove that
∀ x, x ∈ L ↔ x ∈ X
-/

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ (α : Type) (L: set α), L ∩ L = L :=
begin
  intros a L,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  exact h.left,
  -- backward
  assume l,
  exact and.intro l l,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

-- how to express commutativity
-- for sets (s1 ∪ s2 = s2 ∪ s1)
-- we use set extensionality because the only case
-- where this would be true is if it was written like:
/-
∀ x, (x ∈ (s1 ∪ s2)) ↔ (x ∈ (s2 ∪ s1))
-/
example : ∀ (α : Type) (L K : set α), L ∪ K = K ∪ L :=
begin
  intros a L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with l k,
    -- subgoal one
    apply or.inr l,
    -- subgoal two
    apply or.inl k,
  -- backward
  assume h,
  cases h with k l,
    -- subgoal one
    apply or.inr k,
    -- subgoal two 
    apply or.inl l,
end

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example : ∀ (α : Type), (∀ (a: set α), (a ⊆ a)) ∧ (∀ (H K L: set α) (a: H ⊆ K) (b: K ⊆ L), H ⊆ L):=
begin
  assume a,
  split,
  -- reflexive
  assume X, -- x ⊆ x is same as ∀ x, x ∈ X → x ∈ X
  assume x,
  assume h,
  exact h,
  -- transitive
  assume H L K hl kl, -- ∀ x, x ∈ H → x ∈ K
  assume x,
  assume h,
  have l := hl h,
  have k := kl l,
  exact k,

end

/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example : ∀ (α : Type) (H L K: set α), (H ∩ L) ∩ K = H ∩ (L ∩ K):=
begin
  intros a H L K,
  apply set.ext,
  assume x,
  split,
  -- forward 
  assume h,
  cases h with hl k,
  cases hl with h l,
  apply and.intro h (and.intro l k),
  -- backward
  assume h,
  cases h with h lk,
  cases lk with l k,
  apply and.intro (and.intro h l) k,
end

example : ∀ (α : Type) (H L K : set α), (H ∪ L) ∪ K = H ∪ (L ∪ K) :=
begin
  assume α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with hl k,
  cases hl with h l,
    -- first case
      apply or.intro_left _,
      exact h,
    -- second case
      apply or.intro_right _,
      apply or.intro_left _ ,
      exact l,
    -- third case
      apply or.intro_right _,
      apply or.intro_right _,
      exact k,
  -- backward
  assume h,
  cases h with h lk,
    -- first case
      apply or.intro_left _,
      apply or.intro_left _,
      exact h,
    cases lk with l k,
    -- first case
      apply or.intro_left _,
      apply or.intro_right _,
      exact l,
    -- second case
      apply or.intro_right _,
      exact k,

end

example : ∀ (α : Type) (H L K : set α), (H ∪ L) ∪ K = H ∪ (L ∪ K) :=
begin
  assume α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with hl k,
  cases hl with h l,
    -- first case
      apply or.intro_left _,
      exact h,
    -- second case
      apply or.intro_right _,
      apply or.intro_left _ ,
      exact l,
    -- third case
      apply or.intro_right _,
      apply or.intro_right _,
      exact k,
  -- backward
  assume h,
  cases h with h lk,
    -- first case
      apply or.intro_left _,
      apply or.intro_left _,
      exact h,
    cases lk with l k,
    -- first case
      apply or.intro_left _,
      apply or.intro_right _,
      exact l,
    -- second case
      apply or.intro_right _,
      exact k,

end


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


example : ∀ (α : Type) (H L K : set α), H ∪ (L ∩ K) = (H ∪ L) ∩ (H ∪ K):=
begin
  intros α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with h lk,
    -- case one
    apply and.intro _ _,
      -- subgoal one
        apply or.intro_left _,
        exact h,
      -- subgoal two
        apply or.intro_left _,
        exact h,
    -- case two
    cases lk with l k,
    apply and.intro _ _,
      -- subgoal one
        apply or.intro_right _,
        exact l,
      -- subgoal two
        apply or.intro_right _,
        exact k,
  -- backward
  assume h,
  cases h with hl hk,
  cases hl with h l,
  cases hk with h k,
    -- case one
      apply or.intro_left _,
      exact h,
    -- case two
      apply or.intro_left _,
      exact h,
    -- case three
      cases hk with h k,
      -- sub case one
        apply or.intro_left _,
        exact h,
      -- sub case two
        apply or.intro_right _,
        exact and.intro l k,

end

end hw_6

namespace hw_7

-- the pair (1,1) is in the <= relation
-- right side is a predicate (takes a pair) takes an argument and yields a proposition
example : (1, 1) ∈ { p : ℕ × ℕ | p.1 <= p.2 } :=
begin
  show { p : ℕ × ℕ | p.1 <= p.2 } (1, 1), -- apply predicate
  show 1 <= 1,                            -- proposition
  exact nat.less_than_or_equal.refl,      -- proof
  -- less than or equal relation has two proof rules/ introduction rules
  -- it's like eq.refl but its for the less than or equal relation

end

-- Proof by reflexivity of =.

example : (3, 10) ∈ { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin
  show 10 = 3 * 3,
  exact rfl, -- stuck
end

-- stuck (in fact it's provably false)

example : (3, 10) ∈ compl { p : ℕ × ℕ | p.2 = p.1 * p.1 } :=
begin -- little c is the standard notation for the complement of a set
  show ¬10=9,
  assume h,
  cases h,
end

-- Proof by negation and the reflexive property of =.
/-
In English, the proposition is true by the reflexive
property of =.
-/

example : ("Hello", 5) ∈ { p : string × ℕ | p.2 = string.length p.1} :=
begin
  exact rfl,
end

example : 0 ≤ 0 :=    -- nat.le 0 0
begin
  exact nat.less_than_or_equal.refl, -- anything is less than or equal to itself
end

example : nat.le 0 1 := 
begin
  apply nat.less_than_or_equal.step _, -- it will suffice to apply step intro rule to prove that 0 <= 0 to prove that 0 <= 1
  exact nat.less_than_or_equal.refl,
end

example : nat.le 0 2 := 
begin
  apply nat.less_than_or_equal.step _,
  apply nat.less_than_or_equal.step _,
  exact nat.less_than_or_equal.refl, -- the proof in itself is like this recursive data structure
end

-- equality relation on natural numbers is reflexive
-- @eq is shorthand for the equals sign
-- @ turns off implicit arguments
-- eq nat is a two place predicate on values of type nat
theorem eq_is_refl : reflexive (@eq nat) := -- eq is the equality predicate
-- proof below
/-
Let's unpack the notation, @eq α. When we 
write, 0 = 0, that's infix notation for
the term, eq 0 0 (the application of the
two-place predicate, eq, to 0 and 0. It
is the meaning of the notation 0 = 0.). 

But what (eq 0 0) means is (@eq nat 0 0). 
The first argument of eq is implicit, so 
is usually omitted from code and inferred
from the following values. But here we 
don't give such values. The @tells Lean
to let us write the implicit argument(s)
explicitly. 
-/
begin
  -- turns into @eq nat 0 0
  -- want to talk about the overall relation of equality on nats
  -- binary equality relation on nats
  -- the proposition that equality on natural numbers is reflexive
  -- expand expression: @reflexive nat (@eq nat) :=
  unfold reflexive, -- valuable to do bc it shows logical definition of set theory concept
  assume x,
  exact rfl,

end

/-
Here's an English version.

Theorem: Equality is reflexive.
Proof. Unfolding the definition of reflexive,
what we are to show is ∀ x, x = x. To prove it,
assume x is an arbitrary value and show x = x.
That's true by (application of) the introduction
rule for equality (to x). QED.
-/

/-This predicate picks out (logically) those that do. 
Building on our discussion of sets, it appears to
be the case, and it is, that it defines the set of
binary relations on β that are reflexive. We can
define this set explicitly by using reflexive as a
predicate on binary relations in a set builder
expression.
-/

def reflexive_relations := -- defined to be the sets of all objects r that are the two place predicates on β, such that r is reflexive
  { r : β → β → Prop | reflexive r }

  -- go back and look at definition of set membership
example : @eq nat ∈ @reflexive_relations nat := -- this relation is in the set of all reflexive relations
begin -- reflexive relations is a predicate is applied to equality on the nats
  show reflexive_relations (@eq nat),
  unfold reflexive_relations,
  show reflexive (@eq nat),
  exact eq_is_refl,      -- Already proved, use theorem!
end
-- You can just feel your brains getting bigger here!

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


-- HW 7 PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
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
example : transitive r → reflexive r → ¬ asymmetric r :=
begin
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
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

end hw_7