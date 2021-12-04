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

#3: Give a formal proof for #2 or #3.

#4: Formal or detailed informal proofs 10

Give an informal but detailed proof that for every natural number 𝑛, 
1⋅𝑛=𝑛, using a proof by induction, the definition of multiplication, 
and the theorems proved in

**Answer:**

We prove this by induction on n. To prove that the proposition 
holds of every natural number n, it would suffice to prove that 
the proposition holds of zero, and whenever it holds of some number 
n, it holds of n + 1.

In the base case, we have that if n = 0, then 1 * 0 = 0 by the first
defining clause for multiplacation (m * 0 = 0). 

To prove this proposition in the successor case, it would suffice to 
show that if this proposition holds for n then it holds for n + 1. To 
show this, it is necessary to use the second defining clause for 
multiplacation that m * succ(n) = m * n + m. Assuming this claim holds 
for n, we have

    1 * succ(n) = 1 * n + 1

We can understand this as:

    1 * succ(n) = 1 * n + 1 = succ(n)

Thus, proving the proposition using the inductive hypothesis and the 
definition of multiplacation.

QED.

#5: Formal or detailed informal proofs 11

#6: Formal or detailed informal proofs 12

#7: Formal or detailed informal proofs 13

#8: (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/