/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
**∀ P (P(0) ∧ ∀ n (P(n) → P(n+1))) → ∀n P(n)**

#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 

**Answer:**

We prove this by induction on n. To prove that the proposition 
holds of every natural number n, it would suffice to prove that 
the proposition holds of zero, and whenever it holds of some number 
n, it holds of n + 1.

In the base case, when n = 0, we have 0 = 0, as required. For the induction 
step, fix n, and assume the inductive hypothesis stated in this proposition.
To show that whenever the proposition holds of some number n, it holds of n + 1,
it's necessary to show that this same claim holds with n replaced by n + 1. 
To prove such, it must be shown that 

    0^3 + 1^3 +...(n+1)^3 = (1/4)(n+1)^2((n+1)+1)^2

is essentially the same as saying:

    0^3 + 1^3 + ... + (n)^3 + (n+1)^3 = (1/4)(n+1)^2((n+1)+1)^2

We need to show that this same claim holds with n replaced by n + 1. But that's 
just a calculation as shown:

    (0^3 + 1^3 + ... + (n)^3) + (n+1)^3 = (1/4)(n+1)^2((n+1)+1)^2
    (1/4)𝑛^2(𝑛+1)^2 + (n+1)^3 = (1/4)(n+1)^2((n+1)+1)^2

QED.


-/

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/