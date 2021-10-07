/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
            [q: Q]
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p2q,
  assume p,
  have q := p2q p,
  exact q,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- [Anything true needs a proof of true.]

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- [Given arbitrary but specific propositions P and Q, 
and proofs that P is true and Q is true, a proof can 
be derived such that both P and Q is true using the 
individual proofs of P (p) and Q (q).]

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.


(P Q : Prop) (pq : P ∧ Q) 
---------------------------- elim_left
            (p: P) 

(P Q : Prop) (pq : P ∧ Q) 
---------------------------- elim_right
            (q: Q) 

-- [Given a proof that P and Q is true by the and introduction
rule, we can derive a proof that P is true and that 
Q is true by using the left and right elimination rules.]
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q: Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume qandp,
  have p : P := and.elim_right qandp,
  exact p,
end



-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- [To prove Q, it must first be assumed that 
we have an arbitrary t of type T, then show that it 
applies for all objects of types T.]

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                     [pr: Q]

-- [If given a proof of a proposition that states that
for all objects of type T, a proof of Q can be derived, 
the proof of the for all proposition can be *applied* to 
another object of type T named t, by the elimination rule 
for for all (∀).] 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- [To derive a proof of Q, the the for all proposition pf
would need to be *applied* to the value t to obtain a proof of
Q.]

-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- (3) Lynn is a better computer scientist
  -- (4) If Lynn knows logic, then Lynn is a better computer scientist

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀ (Lynn : Person), KnowsLogic Lynn → BetterComputerScientist Lynn  := 
begin
  assume Lynn,
  apply LogicMakesYouBetterAtCS Lynn,
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden


/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/-
--[To prove by negation means to prove ¬P,
for some proposition P. To prove such a proposition, 
it is necessary first to recognize the definition of
¬P is essentially P → false. Because we see it as an 
implication, we must first assume the premise (that 
P is true), and show that it leads to a contradiction.
This can be done by performing case analysis on the assumed
proof, which will prove the beginning proposition as there
are no cases in which false is true.] 
-/ 

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume [¬ P] and show that [the assumption yields a contradiction].
From this derivation you can conclude [¬ ¬ P].
Then you apply the rule of negation [ elimination ]
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is [ classically ] valid, and that accepting the axiom
of the [ excluded middle ] suffices to establish negation
[ elimination ](better called double [negation elimination])
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q: Prop), (P ∧ Q) ↔ (Q ∧ P) :=
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume pandq,
    cases pandq with p q,
    apply and.intro q p,
  -- backward
    assume qandp,
    cases qandp with q p,
    apply and.intro p q,
    
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
/-
English Rendition: [Everybody likes anyone who is nice and talented.
John Lennon is a person who is liked by everyone because he is nice
and talented.]
-/
example : ELJL :=
begin
  intros,
  assume Person Nice Talented Likes elantp JohnLennon JLNT p,
  apply elantp JohnLennon _ _,
  -- subgoals
    -- subgoal 1 
      exact (and.elim_left JLNT), 
    -- subogal 2 
      exact (and.elim_right JLNT),

end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? [4 cases]
-- list the cases (informaly)
    -- [To prove this proposition, you will first have
    one case that concerns proving that every car is heavy and 
    red, a second case that concerns proving that every car is
    heavy and blue, a third case that concerns proving that every car is 
    light and red, and a fourth case that concerns proving that every 
    car is light and blue.]

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T: Type) (x y z : T), x = y → y = z → x = z 


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : ∀ (P : Prop), (¬¬P → P) = P ∨ ¬P := 
begin
  assume P,
  sorry,
end


/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]

my understanding : if loves is a symmetric relation,
then that is an axiom that I want to start with

-/

axiom Loves : Person → Person → Prop
axiom Loves_symm : ∀ (p e: Person), Loves e p → Loves p e

example : (∃ (p: Person), ∀ (e: Person), Loves e p) →
(∃ (p : Person), ∀ (e: Person), Loves p e) := 
begin
  assume h,
  -- exists elimination
  cases h with p pf,
  apply exists.intro p _,
  assume e,
  -- propose introduced fact that Loves p e
  have loves_pe : Loves p e := _,
  -- subgoal 1 : exact introduced fact
    exact loves_pe,
  -- subgoal 2: prove the introduced fact
    have symm_rel := Loves_symm p e, -- use axiom that states symmetric relation
    have proof := pf e, -- apply exists elim proof to a Person e
    have final_proof := symm_rel proof, -- derive proof using implies elimination
    exact final_proof, 
end
