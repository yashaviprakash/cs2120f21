/- Hey everyone!-/

/-Here I'll summarize and put practice problems for retaining
the material from the past three weeks because there was definitely a lot to work with!-/

/-lecture 1 review-/

/-
-----------------------------------------------------------------
Reasoning:

Inductive, Abductive, Deductive

Inductive: 

-derive generalized predictive models from
given sets of observations, use a reasonable form of model
(often linear, y = mx+b)
-calibrate m and b coefficients to get a minimum-error fit of 
line to data
Is this form of reasoning *sound* or *not sound*?

Answer - 

Abductive:
-based on whatever information you have or can get, *guess* 
a good hypothesis

Deductive:
- assume that certain given propositions (axioms) are true 
(have proofs)
- Combine truths/proofs of smaller propositions into truths/proofs 
of bigger ones
-Formal rules of inference define how truthor proof values can be combined
-basically what we've been doing in class

-----------------------------------------------------------------
-/

/-
Axiom of Reflexivity:

Theorem: 1 = 1 (where 1 is a natural number)

Proof: By applciation of the *reflexive axiom of equality*.

What is this axiom? The *reflexive axiom of equality*, part of most
definitions of predicate logics, states that every object, t, of every
type, T, is equal to itself. We write this formally in the syntax of 
predicate logic we will use in this class, as follows:
-/

axiom eq_refl : ∀ (T: Type) (t: T), t = t /- specific wording in notes-/

#check eq.refl /- lean's reflexive axiom of equality-/


/-

Given that the axiom stiupates that every object of every type is 
equal to iteself, and given that 1 is an object of some type (ℕ), 
it must be that 1, *in particular*, is equal to itself. This reasoning
allows us to deduce not only that 1 = 1 is true, but now we also have a 
precise explanation why that is the case. This particular examle of reasoning
is called *universal elimination*

-----------------------------------------------------------------
-/