namespace equality
/-
introduction rule: reflexive axiom of equality

-- states that every object, t, of every type T, is
equal to itself

elimination rule: the substitutability of equals

-- states that if you know that some object, x, has 
property P, and you also know that x = y, then you 
can conclude that y must also have property P (because
y *is equal* to x)
-/

end equality 

namespace reflexive_equality
-- introduction rule
#check eq.refl ℕ 

/-In English, this says, "if you give me 
*any* Type, T, and any object, t, of that
type, I will return you (and therefore 
there must be) a proof of the proposition, 
t = t; and the existence of this proof,
in turn, justifies the *judgment* that
the proposition, 1 = 1, is *true*.

Let's take another look at the axiom that
let's us *deduce* the *theorem* that 1 = 1.
Here it is: ∀ {T : Type} (t : T), t = t.
What that means is that if I choose any
type, T, say T = ℕ, and any value of that
type, say t = (1 : ℕ), then I should be 
able to apply the axiom to the argument
values, ℕ and 1, to get back a *proof* of
the proposition, 1 = 1. -/ 

#check eq.refl 1

-- refresher on lean syntax
/-
Each proceeding line of code has the following elements
- def: a keyword, binds the given identifer to the given value
- n, m, z, r, q: identifiers, a.k.a., variables or variable names
- : T, where T is ℕ, ℤ, ℝ, or ℚ: specifies the *type* of the value
- := 1.0: specifies the value, 1.0, to be bound to the identifier 
-/

def n : ℕ := 1    -- 1 specified to be a natural number (non-negative whole number)

example : 1 = 1 := 
  eq.refl 1   -- Lean inferns T = ℕ from 1

/-Proof: By the reflexive property of equality
(applied to the particular value, 1). QED." 


The QED, by the way, is short for quod est 
demonstratum, Latin for "it is shown." It is
a kind of traditional punctuation for natural
language proof descriptions that signals that 
the proof is complete.-/

/-
If you're getting the feeling that we are
pointing you a little bit to a computational
understand of what it means to construct or
to use proofs, you're right. To make the point
clearer, let's write our own proof-returning 
function@ We'll call it gimme_a_proof. It 
will take two arguments, a type, T, and a 
value, t, of that type; and it will return 
a proof of t = t, on the basis of which we
can render the judgment that t = t is *true*.
-/

def gimme_a_proof   -- function name
    (T : Type)      -- first argument
    (t : T)         -- second argument
    : t = t         -- return "type" 
    := eq.refl t    -- implementation

#check gimme_a_proof ℕ 9
#check gimme_a_proof bool tt
#check gimme_a_proof ℤ (-3)

/-
EXERCISE #2.
Give, below, a formal statement and proof of 
the proposition, 2 = 2. (See above for a good
example to follow!)
-/

example : 2 = 2 := @eq.refl ℕ 2


end reflexive_equality

namespace predicatesandpropositions

/-
We've seen the first (the reflexivity of equality).
In today's class, we'll quickly review the first,
then we'll introduce the second axiom. The comes
the real eye-opener: we will use these two axioms
to construct proofs of two theorems about equality:

- theorem: the equality relation is *symmetric*
- theorem: the equality relation is *transitive*
-/

/-
Symmetry:

Speaking informally, when we say that a relation,
R, such as equality, is *symmetric* we're mean that,
for *any* objects, x and y, if R relates x to y,
then R also relates y to x.

If the relation in question is equality, then what
it means for equality to be symmetric is that *if*
x = y (for *any* x and y), then it must also be
that y = x. (Otherwise R would not be symmetric.)

-/

/-
Transitivity:

When we say that a relation r, is transitive, we
mean that, for all objects, x, y, and z, if x is
related to y by r, and y is is related to z by r,
then x must be related to z by r (otherwise r is
not transitive).
-/

/-
Proposition:

A proposition is a "claim," an *assertion* that
some state of affairs holds. A proposition can
be *judged* to be true or false. In mathematical
logic, a conjecture--a proposition for which one
does not yet have a proof---asserts that some
mathematical formula is valid.

If one can produce a proof of the conjecture then
one can render the judgement that that proposition
is true. A proof of it establishes it as a theorem.
And from that point on, the theorem can be applied
as if it were just another axiom, in constructing
proofs of ever more elaborate conjectures.
-/

/-
Predicates:

A predicate is a parameterized proposition: a proposition with
*arguments* (just like a function has arguments). When you fill
in all of the arguments of a predicate, you have a proposition,
just like when you fill in all the arguments to a function call,
you get a result.

Speaking more formally, we represent a predicate exactly
as a function, from parameter values to propositions. In
the case of the predicate e3, it's a function that takes
a natural number, n, and returns the proposition, n = 3:
a proposition about n. Here's how we might define this
predicate/function in Lean.

def e3 (n : nat) : Prop := n = 3 **predicate that takes in a natural number, n, and produces a proposition that n = 3**

The syntax is pretty simple. First, def introduces a
new definition. What's being defined to have a value is
e3. The argument/parameter is a value, a natural number,
n. And what the function then returns is the proposition,
n = 3, for any value of n that is given as an argument.

-/

end predicatesandpropositions

namespace substitutability_of_equals

/-
introduction rules:

You've already learned the reflexivity axiom
for equality: ∀ (T : Type) (t : T), t = t.

This axiom provides a way to *construct* proofs
of equalities. If you "give it" a T and a t, it
gives back a proof of the proposition that t = t.

Such a proof-building axiom is said to be an
*introduction* rule (here, for equality). More
generally, introduction rules define mechanisms
that *construct* proofs of given kinds (e.g., of
equality propositions).

-/

axiom eq_subst :    -- arguments are assumptions!
  ∀ (T : Type)      -- if we're given, T, a type
    (P : T → Prop)  -- P, property of T objects (predicate)
    (x y : T)       -- x and y, objects of type T,
    (e : x = y)     -- e, a proof of x = y (we *use* an = proof)
    (px : P x),     -- a proof that x has property P
  P y               -- then we can have a proof of P y

/-
**you need five things for the axiom of substitutability**

**First you need to be given a type T**
**Second you need a property P of T objects (predicate)**
**Third you need two objects of type T**
**Fourth you need a proof that x=y**
**Fifth a proof that x has property P**

-/

/-
Given any type, T, ... and any *property*, P, of objects
of this type, (P : T \to Prop), ... if you know that an
object, x, of type T, has property P, i.e., (P x) and you
know that x = y, then you can deduce P y: that it must be
the case that y has property P, as well.

From these assumptions, can we prove P y? Indeed
we can, because what we've assumed are exactly all
of the argumented required to apply the axiom of
substitutability of equals. Here then is a formal
proof that, from the preceding axioms, we can prove
(P y).


example : P y := eq_subst T P x y e px

**english language proof eq subst**
English: From the assumptions that P x is true,
and x = y, we can deduce that P y must be true
by applying the axiom of the the substitutability
of equals. (Try to come close to memorizing that
while visualizing what it really means.)
-/

/- Theorem : Equality is symmetric

Theorem: the equality relation (on objects of
any given type) is symmetric.

**eq symm**
To prove that equality is symmetric, we must
prove that, for *any* objects, x and y (of a
given type), if x = y then y = x.

**english language proof**
Proof. We start by *assuming* that x and
y are objects of some type T. We also then
assume that x = y. On the assumption that
this is true, we must show is that y = x.
But by the substitutivity of equals, y = x
can be rewritten to y = y, *using the fact
that x = y*. The only thing that remains to
be proven now is that y = y, but that is an
easy proof by the reflexivity of equality.
QED.

Here's a less verbose proof.

Proof: By the substitutability of equals,
we can rewrite y = x as y = y (without any
change in meaning), but then this proposition
is true by the reflexivity of equality, so
the original y = x must be true as well. QED.
-/

/- Theorem: Equality is transitive

**english language proof**
Proof. We are given as assumptions that T is a
type; x, y, and z are values of this type; and
that x = y and y = z. In this context, we are to
show that x = z. We first apply substitutability
using our proof of x = y to rewrite the x in the
goal to y, yielding a new goal: y = z. But that
is something we've already assumed is true.

Or, if you prefer, in this last step, we can
use the assumption that y = z to apply the
axiom of the substitutability of equals to
rewrite the y in y = z to z, yielding z = z.
And that is proved from the reflexivity of
the equality relation on any type of objects.
QED.

-/


end substitutability_of_equals

namespace inferencerules_equality


/-
INFERENCE RULE #1/2: EQUALITY IS REFLEXIVE

Everything is equal to itself. A bit more formally,
if one is given a type, T, and a value, t, of this
type, then you may have a proof of t = t "for free."
-/

axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- the result type: proof of t = t

/-
INFERENCE RULE #2/2: SUBSTITUTION OF EQUALS FOR EQUALS

Given any type, T, of objects, and any *property*, P,
of objects of this type, if you know x has property P
(written as P x) and you know that x = y, then you can
deduce that y has property P.

*when you say that x has a property P, what would that mean?*
-/
axiom eq_subst : 
  ∀ (T : Type)      -- if T is a type
    (P : T → Prop)  -- and P is a property of T objects
    (x y : T)       -- and x and y are T objects
    (e : x = y)     -- and you have a proof that x = y
    (px : P x),     -- and you have a proof that x has property P
  P y               -- then you can deduce (and get a proof) of P y


end inferencerules_equality

namespace symm_trans


/-
From the axioms of reflexivity and substitutabilty
we now prove two *theorems*. A theorem is a proven
proposition. You can even think of the theorem as a
proof of a given proposition. A proof establishes a
conjecture as a theorem. And once it's a theorem,
you can use it like any other inference rule. In
this way, you can build up vast, layered libraries
of theorems. That's what we call mathematics. It's
what mathematicians do.

In this file, we provide both formal and informal
proofs of two theorems:

[1] Equality is symmetric.
[2] Equality is transitive.
-/


/-
Proofs
-/

/-
In the logic of Lean, a proposition is a type,
and the values of that type are its proofs. Just
as we can give an example value of an ordinary 
data type, such as ℕ, we can also give example
values of propositions acting as types, i.e., 
proofs.
-/

-- give a value of the nat type
example : ℕ := 5

-- give a proof of the proposition 1 = 1 
example : 1 = 1 := eq.refl 1

/-
We will now present formal proofs of our two 
theorems in this style.
-/

/-
Proof: equality is symmetric.
-/

-- We define eq_symm to be the proposition at issue
-- Note: Prop is the type of all propositions in Lean
-- And each proposition is itself a type: of it proofs
def eq_symm : Prop := 
  ∀ (T : Type) 
    (x y : T), 
    x = y → 
    y = x 

example : eq_symm :=
begin
  unfold eq_symm, -- replace name with definition
  assume T x y e, -- assume arbitrary values
  rw e,           -- rw uses eq.subst to replace x with y
                  -- and then applies eq.refl automatically
  -- QED.
end

/-
Proof: equality is transitive.
-/

-- We define eq_trans formally in the same basic way
def eq_trans : Prop := 
  ∀ (T : Type) 
    (x y z : T), 
    x = y → 
    y = z → 
    x = z

example : eq_trans := 
begin
  unfold eq_trans,
  assume T x y z,
  assume e1,
  assume e2,
  rw e1,
  exact e2,
end

/- Alternative proof for eq_symm-/
example : eq_symm :=
begin
  unfold eq_symm,   -- replace name with definition
  assume T x y e,   -- assume arbitrary values
  apply eq.subst e, -- apply axiom 2, substitutability
  exact eq.refl x,  -- apply axiom 1, reflexivity
  -- QED.
end

/-
There. That's a nice proof (script), as it closely
models a typical English language proof. To wit:

Theorem: Equality is symmetric.
Proof: Assume we're given arbitrary values of T, 
x, y, and a proof of x = y. What remains to be
proved is y = x. Apply substitutability to write
x as y or y as x. The result is trivially true 
by the reflexive property of equality.
-/

end symm_trans

namespace forall_implies

/-
We've seen that logics start with axioms that
can then be combined (with other information)
using *inference rules* to derive theorems. In
this file we review what we've covered so far
and then we introduce:

(1) The concept of introduction and elimination
rules for a given logical construct.
(2) We distinguish the reflexivity axiom as an
*introduction* rule (one that produces a proof
of an equality), and the substitutability of
equals as an *elimination* rule (one that uses,
or consumes) a proof of an equality to produce
some other kind of result.
(3) We explicitly identity the introduction 
rules for ∀ and for →. To produce a proof of
∀ (x : T), P x (where T is a type and P is a
predicate that asserts some property of x), we
*assume* that we're given an arbitrary but
specific (x : T) ["x of type T"], and then 
we prove (P x) *for that x*. Because we made
no assumptions whatsoever about x, if we can
show that (P x) is true, then it must be true
*for all* (x : T).
-/

/-
Practice
-/

example : ∀ (T : Type) (x y z : T), x = y → y = z → z = x :=
begin
  assume T x y z h1 h2, -- introduction rule for ∀ 
  apply eq.symm _,      -- application of symm *theorem*
  apply eq.trans h1 h2, -- application of trans theorem
end


/-
INTRODUCTION and ELIMINATION RULES
-/

/-
For =
  - introduction rule: eq.refl 
  - elimination rule: eq.subst
-/

/-
For ∀ x, P x
  - introduction rule: assume arbitrary x, then show P x
  - elimination rule: next time!
-/

/-
For P → Q
- introduction rule: assume arbitrary P, then show Q
- elimination rule: next time.
-/


end forall_implies


namespace hw1_2

/-
EQUALITY
-/

/- #1 
Suppose that x, y, z, and w are arbitrary objects of some type, 
T; and suppose further that we know (have proofs of the facts) 
that  x = y, y = z, and w = z. Give a very, very short English 
proof of the conjecture that z = w. You can use not only the 
axioms of equality, but either of the theorems about properties 
of equality that we have proven. Hint: There's something about
this question that makes it much easier to answer than it might
at first appear.

Answer: If we assume that w = z, we apply the symmetric property
of equality to w = z to prove z = w.

-/



/- #2
Give a formal statement of the conjecture (proposition) from
#1 by filling in the "hole" in the following definition. The
def is a keyword. The name you're binding to your proposition
is prop_1. The type of the value is Prop (which is the type of
all propositions in Lean). 
-/

def prop_1 : Prop := 
  ∀ (T: Type) (x y z w: T), x = y → y = z → w = z → z = w 
  

/- #3 (extra credit)
Give a formal proof of the proposition from #2 by filling in
the hole in this next definition. Hint: Use Lean's versions of
the axioms and basic theorems concerning equality. They are,
again, called eq.refl, eq.subst, eq.symm, eq.trans.

*in class note: proofs are data* 

/- #4
Give a very brief explanation in English of the introduction
rule for ∀. For example, suppose you need to prove (∀ x, P x);
what do you do? (I'm being a little informal in leaving out the
type of X.) 

Answer: Assume that you have an arbitrary x, and show predicate P 
must apply for all X's.
-/

/- #5
Suppose you have a proof, let's call it pf, of the proposition,
(∀ x, P x), and you need a proof of P t, for some particular t.
Write an expression then uses the elimination rule for ∀ to get
such a proof. Complete the answer by replacing the underscores
in the following expression: ( _ _ ). 

Apply the theorem (∀ x, P x) to t, to get a proof of P t.

This is called universal instantiation.
-/

axioms 
(Ball: Type) 
(blue : Ball → Prop) -- give me a ball i'll give you back a proposition about that ball
(allBallsBlue : ∀ (b : Ball), blue b)
(tomsBall : Ball) -- tom's ball is an object of type ball

-- want to prove as a theorem that tom's ball is blue
-- gives proposition that tom's ball is blue
-- universal generalization : if you have an example of something that can be generalized to everything like it 
theorem tomsBallIsBlue : blue tomsBall := allBallsBlue tomsBall

/-
IMPLIES: →
In the "code" that follows, we define two predicates, each 
taking one natural number as an argument. We call them ev and 
odd. When applied to any value, n, ev yields the proposition 
that n is even (n % 2 = 0), while odd yields the proposition
that n is odd (n % 2 = 1).

implies and for all are practically the same (for all practical purposes), you apply them the same
-/

def ev (n : ℕ) := n % 2 = 0 --evenness predicate that yields the proposition that n is even
def odd (n : ℕ) := n % 2 = 1 

/- #6
Write a formal version of the proposition that, for *any* 
natural number n, *if* n is even, *then* n + 1 is odd. Give 
your answer by filling the hole in the following definition. 
Hint: put parenthesis around "n + 1" in your answer.
-/

-- for all n type nat, it is the case that IF THEN (form of proposition is implication)
def successor_of_even_is_odd : Prop := 
  ∀ (n : ℕ ), ev n → odd (n + 1)

/- #7
Suppose that "its_raining" and "the_streets_are_wet" are
propositions. (We formalize these assumptions as axioms in
what follows. Then give a formal definition of the (larger)
proposition, "if it's raining out then the streets are wet")
by filling in the hole
-/

axioms (raining streets_wet : Prop)

axiom if_raining_then_streets_wet : raining → streets_wet -- have assumed this is true
  

/- #9
Now suppose that in addition, its_raining is true, and
we have a proof of it, pf_its_raining. Again, we again give
you this assumption formally as an axiom below. Finish
the formal proof that the streets must be wet. Hint: here
you are asked to use the elimination rule for →. 
-/

axiom pf_raining : raining -- have a proof that its raining

example : streets_wet := if_raining_then_streets_wet pf_raining

/- 
AND: ∧
-/

/- #10
In our last class, we proved that "∧ is *commutative*."
That is, for any given *propositions*, P and Q, (P ∧ Q) → 
(Q ∧ P). The way we proved it was to *assume* that we're 
given such a P, Q, and proof, pq, of (P ∧ Q) -- applying
the introduction rules for ∀ and →). In this context, we
*use* the proof, pq, to derive separate proofs, let's call
them p, a proof of P, and q, a proof of Q. With these in
hand, we then apply the introduction rule for ∧ to put 
them back together into a proof of (Q ∧ P). We give you
a formal version of this proof as a reminder, next.  
-/

theorem and_commutative : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q pq,
  apply and.intro _ _,
  exact (and.elim_right pq),
  exact (and.elim_left pq),
end

/-
Your task now is to prove the theorem, "∧ is *associative*."
What this means is that for arbitrary propositions, P, Q, and
R, if (P ∧ (Q ∧ R)) is true, then ((P ∧ Q) ∧ R) is true, *and
vice versa*. You just need to prove it in the first direction.
Hint, if you have a proof, p_qr, of (P ∧ (Q ∧ R)), then the
application of and.elim_left will give you a proof of P, and
and.elim_right will give you a proof of (Q ∧ R). 
To help you along, we give you the first part of the proof,
including an example of a new Lean tactic called have, which
allows you to give a name to a new value in the middle of a
proof script.

difference between example and theorem, theorem binds name to proof
but example just asks for proof
-/

theorem and_associative : 
  ∀ (P Q R : Prop),
  (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) :=
begin
  intros P Q R h, -- parenthesis goes away because and (and or) is right associative
  have p : P := and.elim_left h,
  have q : Q := (and.elim_right h).left,
  have r : R := (and.elim_right h).right,
  apply and.intro _ _,
  apply and.intro p q,
  exact r,
end

/- #11
Give an English language proof of the preceding
theorem. Do it by finishing off the following
partial "proof explanation."
Proof. We assume that P, Q, and R are arbitrary 
but specific propositions, and that we have a
proof, let's call it p_qr, of (P ∧ (Q ∧ R)) [by
application of ∧ and → introduction.] What now
remains to be proved is ((P ∧ Q) ∧ R). We can
construct a proof of this proposition by applying
_____ to a proof of (P ∧ Q) and a proof of R.
What remains, then, is to obtain these proofs.
But this is easily done by the application of
____ to ____. QED. 
-/


/-
Note that Lean includes versions of these
theorems (and many, many, many others) in 
its extensive library of formalized maths, 
as the following check commands reveal.
Note the difference in naming relative to
the definitions we give in this file.
-/
#check @and.comm
#check @and.assoc
-/
end hw1_2

namespace logical_connectives

-- EQUALITY (=)

/-
INTRODUCTION RULE
axiom or reflexivity of equality
-/
axiom eq_refl  : 
  ∀ (T : Type)  -- if T is any type (of thing)
    (t : T),    -- and t is thing of that type, T
  t = t         -- the result type: proof of t = t

/-
ELIMINATION RULE
axiom of substutability of equality
-/
axiom eq_subst :
  ∀ (T :Type) -- if T is a type
    (P : T → Prop) -- proposition P about T, basically saying that all objects of type T share a property P
    (x y : T)  -- and x and y are T objects
    (e : x = y) -- and you have a proof that x = y
    (px : P x), -- and you have a proof that x has property P
  P y -- then you can deduce (and get a proof) of P y

-- THEOREMS OF EQUALITY

theorem eq_symm: ∀ (T : Type) (x y: T), x = y → y = x :=
begin 
  assume T,
  assume x y, 
  assume xy, -- assume premise (left side of implication)
  apply eq.subst xy, -- saying that y has the same property as x
  apply eq.refl, -- everything equals to itself
end

theorem eq_trans : ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
begin
  assume T,
  assume x y z,
  assume xy yz,
  -- apply eq.subst yz,
  -- apply eq.subst xy,
  -- apply eq.refl,
  rw xy,
  exact yz,
end

-- FOR ALL (∀)

-- IMPLIES

-- AND IS COMMUTATIVE
-- question, why does and have P and Q as propositions but equality has types T
-- premise : a proposition that isn't the conclusion
-- google's definition : a previous statement or proposition from which another is inferred or follows as a conclusion.
theorem and_comm : ∀ (P Q : Prop), (P ∧ Q) → (Q ∧ P) :=
begin
  assume P Q,
  assume pandq,
  -- cases pandq with p q,
  -- apply and.intro q p,
  apply and.intro _ _,
  apply and.elim_right pandq,
  apply and.elim_left pandq,

end

-- AND IS ASSOCIATIVE
theorem and_asso1 : ∀ (P Q R: Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R):=
begin 
  assume P Q R h,
  cases h with pandq r,
  cases pandq with p q,
  apply and.intro p (and.intro q r),
end 

-- and is right associative...what does that mean?
theorem and_asso2 : ∀ (P Q R: Prop), P ∧ (Q ∧ R) → (P ∧ Q) ∧ R:=
begin 
  assume P Q R h,
  cases h with p qandr,
  cases qandr with q r,
  apply and.intro (and.intro p q) r,
end 

å
end logical_connectives

namespace hw_3

/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  -- assume P,
  -- apply iff.intro _ _,
  -- -- forward
  --   assume porp,
  --   cases porp with p p,
  --   -- left disjunct
  --   exact p,
  --   -- right disjunct
  --   exact p,
  -- -- backward
  --   assume p,
  --   apply or.intro_left P p,
  assume P,
  apply iff.intro _ _, 
  -- forward
    assume h,
    cases h with p p,
    repeat {exact p},
  -- backward
    assume p,
    apply or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandp,
    exact pandp.right,
  -- backward
    assume p,
    apply and.intro p p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume porq,
    cases porq with p q,
    -- left disjunct
    apply or.intro_right Q p,
    -- right disjunct
    apply or.intro_left P q,
  -- backward
    assume qorp,
    cases qorp with q p,
    -- left disjunct
    apply or.intro_right P q,
    -- right disjunct
    apply or.intro_left Q p, 
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
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

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume pandqorr,
    cases pandqorr with p qor,
    cases qor with q r,
    -- left disjunct
    apply or.intro_left _ _,
    apply and.intro p q,
    -- right disjunct
    apply or.intro_right _ _,
    apply and.intro p r,
  -- backward
    assume h,
    cases h with pandq pandr,
    -- left disjunct
    cases pandq with p q,
    apply and.intro _ _,
    exact p,
    apply or.intro_left R q,
    -- right disjunct
    cases pandr with p r,
    apply and.intro _ _,
    exact p,
    apply or.intro_right Q r,

end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p qandr,
    -- left disjunct
    apply and.intro _ _,
    apply or.intro_left Q p,
    apply or.intro_left R p,
    -- right disjunct
    cases qandr with q r,
    apply and.intro _ _,
    apply or.intro_right P q,
    apply or.intro_right P r,
  -- backward
    assume h,
    cases h with porq porr,
    cases porq with p q,
    -- left disjunct
    apply or.intro_left _ _,
    exact p,
    -- right disjunct
    cases porr with p r,
    apply or.intro_left _ _,
    exact p,
    apply or.intro_right P (and.intro q r),
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p porq,
    exact p,
  -- backward
    assume p,
    apply and.intro _ _,
    exact p,
    apply or.intro_left Q p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p pandq,
    -- left disjunct
    exact p,
    -- right disjunct
    cases pandq with p q,
    exact p,
  -- backward
    assume p,
    apply or.intro_left _ _,
    exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  -- assume P,
  -- apply iff.intro _ _,
  -- -- forward
  --   assume h,
  --   apply or.elim h,
  --   -- left disjunct
  --   assume p,
  --   apply true.intro,
  --   -- right disjunct
  --   assume t,
  --   exact t,
  -- -- backward
  --   assume t,
  --   apply or.intro_right P t,
  assume P,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p t,
    exact true.intro,
    exact t,
  -- backward
    assume t,
    apply or.intro_right P t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p f,
    -- left disjunct
    exact p,
    -- right disjunct
    apply false.elim f, -- ex falso
    --contradiction, is another way to solve this as you cannot prove something with a false proof
  -- backward
    assume p,
    apply or.intro_left false p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p t,
    exact p,
  -- backward
    assume p,
    apply and.intro _ _,
    exact p,
    apply true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h with p f,
    apply false.elim f,
  -- backward
    assume f,
    apply and.intro _ _,
    apply false.elim f,
    exact f,
end

end hw_3
 
namespace hw_4

-- 1
example : 0 ≠ 1 :=
begin
  -- -- ¬ (0 = 1)
  -- -- (0 = 1) → false
  -- assume h,
  -- cases h, -- how many different ways can h actually exist? 0
  -- /-
  -- can be solved using contradiction or trivial
  -- -/
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  -- assume h,
  -- have zeqz := eq.refl 0,
  -- contradiction, -- what's really going on with contradiction is the false elim strategy
  -- /-
  -- have f : false := h (eq.refl 0),
  -- exact false.elim (f),
  -- -/
  assume h,
  have f : false := h (eq.refl 0),
  apply false.elim f,
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  -- assume P,
  -- assume p,
  -- assume h,
  -- contradiction,
  -- -- ¬¬P
  -- -- ¬P → false
  -- -- (P → false) → false
  -- -- assume h,
  -- -- have f := h p,
  -- -- exact f,
  assume P,
  assume p,
  assume np,
  contradiction,
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
/-
proof by negation : trying to prove np
how do you prove np by negation? assume p, show false, shows that p implies false which is the negation of np

proof of contradiction : trying to prove p
how do you prove p by contradiction? assume np, show that that leads to a contradiction which shows nnp

classically proof by contradiction is valid through excluded middle of getting proof of disjunction and then perform case analysis
-/
-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  -- proof of negation on np to get nnp
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p np,
  assumption,
  contradiction, -- can use proof by contradiction when you already have a proof of false
  -- assume P,
  -- assume h,
  -- have pornp := classical.em P,
  -- cases pornp with p pn,
  -- assumption,
  -- contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  -- assume P Q,
  -- apply iff.intro _ _,
  -- -- forward
  --   assume h,
  --   have pornp := classical.em P,
  --   cases pornp with p np,
  --   have qornq := classical.em Q,
  --   cases qornq with q nq,
  --   -- case 1
  --     have pandq := and.intro p q,
  --     have f := h pandq,
  --     apply false.elim f,
  --   -- case 2
  --     apply or.intro_right _ _,
  --     assumption,
  --   -- case 3
  --     apply or.intro_left _ _,
  --     assumption,
  -- -- backward
  --   assume h, -- why did we do this and not classical elim
  --   assume pandq,
  --   cases pandq with p q,
  --   cases h,
  --   -- case 1
  --     have f := h p,
  --     exact f,
  --   -- case 2
  --     have f := h q,
  --     exact f,
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    have pornp := classical.em P,
    cases pornp with p np,
    have qornq := classical.em Q,
    cases qornq with q nq,
    -- case one
    have pandq := and.intro p q,
    contradiction,
    -- case two
    apply or.intro_right _ nq,
    -- case three
    apply or.intro_left _ np,
  -- backward
    assume h,
    assume pandq,
    cases pandq with p q,
    cases h,
    contradiction,
    contradiction,

  

    
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  -- assume P Q,
  -- assume h,
  -- have pornp := classical.em P,
  -- cases pornp with p np,
  -- have qornq := classical.em Q,
  -- cases qornq with q nq,
  -- -- case 1
  --   have porq := or.intro_left Q p,
  --   have f := h porq,
  --   apply false.elim f,
  -- -- case 2
  --   have porq := or.intro_left Q p,
  --   have f := h porq,
  --   apply false.elim f,
  -- -- case 3
  --   have qornq := classical.em Q,
  --   cases qornq with q nq,
  --   -- subgoal 1
  --     have porq := or.intro_right P q,
  --     have f := h porq,
  --     apply false.elim f,
  --   -- subgoal 2
  --     apply and.intro np nq,

  assume P Q,
  assume h,
  have pornp := classical.em P,
  cases pornp with p np,
  have qornq := classical.em Q,
  cases qornq with q nq,
  -- case one
  have porq := or.intro_left Q p,
  contradiction,
  -- case two
  have porq := or.intro_left Q p,
  contradiction,
  -- case three
  have qornq := classical.em Q,
  cases qornq with q nq,
    -- subgoal one
    have porq := or.intro_right P q,
    contradiction,
    -- subgoal two
    apply and.intro np nq,

    
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    cases h,
    -- case 1
      apply or.intro_left Q h,
    -- case 2
      have pornp := classical.em P,
      cases pornp with p np,
      have qornq := classical.em Q,
      cases qornq with q nq,
      -- subgoal 1
        apply or.intro_left Q p,
      -- subgoal 2
        apply or.intro_left Q p,
      -- subgoal 3
        have qornq := classical.em Q,
        cases qornq with q nq,
        -- subgoal 1
          apply or.intro_right P q,
        -- sugoal 2
          have q := and.elim_right h,
          contradiction,
  -- backward
    assume h,
    cases h,
    -- left disjunct
      apply or.intro_left _ _,
      exact h,
    -- right disjunct
      have pornp := classical.em P,
      cases pornp with p np,
      -- case 1
        apply or.intro_left _ _,
        exact p,
      -- case 2
        apply or.intro_right _ _,
        apply and.intro np h,
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
    cases h with porq porr,
    cases porq with p q,
    -- case 1
      apply or.intro_left _ _,
      exact p,
    -- case 2
      cases porr with p r,
      -- subgoal 1
        apply or.intro_left _ _,
        exact p,
      -- subgoal 2
        apply or.intro_right _ _,
        apply and.intro q r,
  -- backward
    assume h,
    cases h with p qandr,
    -- case 1
      apply and.intro _ _,
      apply or.intro_left Q p,
      apply or.intro_left R p,
    -- case 2
      cases qandr with q r,
      apply and.intro _ _,
      -- subgoal 1
        apply or.intro_right P q,
      -- subgoal 2
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
      cases h with porq rors,
      cases porq with p q,
      cases rors with r s,
      -- case 1
        apply or.intro_left _ _,
        apply and.intro p r,
      -- case 2
        apply or.intro_right _ _,
        apply or.intro_left _ _,
        apply and.intro p s,
      -- case 3
        cases rors with r s,
        -- subgoal 1
          apply or.intro_right _ _,
          apply or.intro_right _ _,
          apply or.intro_left _ _,
          apply and.intro q r,
        -- subgoal 2
          apply or.intro_right _ _,
          apply or.intro_right _ _,
          apply or.intro_right _ _,
          apply and.intro q s,
    -- backward
      assume h,
      cases h,
      -- case 1
        cases h with p r,
        apply and.intro _ _,
        apply or.intro_left Q p,
        apply or.intro_left S r,
      -- case 2
        cases h,
        cases h with p s,
        apply and.intro _ _,
        apply or.intro_left Q p,
        apply or.intro_right R s,
      -- case 3
        cases h, 
        cases h with q r,
        apply and.intro _ _,
        apply or.intro_right P q,
        apply or.intro_left S r,
      -- case 4
        cases h with q s,
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
  assume h,
  have f := h 1,
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
    cases pornp with p np,
    have qornq := classical.em Q,
    cases qornq with q nq,
    -- case 1
      apply or.intro_right _ _,
      exact q,
    -- case 2
      have q := h p,
      contradiction,
    -- case 3
      apply or.intro_left _ _,
      exact np,
  -- backward
    assume h,
    cases h,
    -- case 1
      assume p,
      contradiction,
    -- case 2
      assume p,
      exact h,
   
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume h,
  assume nq,
  assume p,
  have q := h p,
  contradiction,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,
  assume q,
  have pornp := classical.em P,
  cases pornp with p np,
  -- case 1
    exact p,
  -- case 2
    have q := h np,
    contradiction,
end

end hw_4 



