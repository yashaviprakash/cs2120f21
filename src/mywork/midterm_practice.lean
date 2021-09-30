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

def e3 (n : nat) : Prop := n = 3

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

English: From the assumptions that P x is true,
and x = y, we can deduce that P y must be true
by applying the axiom of the the substitutability
of equals. (Try to come close to memorizing that
while visualizing what it really means.)
-/

/- Theorem : Equality is symmetric

Theorem: the equality relation (on objects of
any given type) is symmetric.

To prove that equality is symmetric, we must
prove that, for *any* objects, x and y (of a
given type), if x = y then y = x.

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

namespace lecture_4


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
  

end lecture_4




