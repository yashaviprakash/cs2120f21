import data.set

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

-/


end hw_6