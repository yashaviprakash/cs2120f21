import algebra.algebra.basic
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

**Answer for #3:**

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

The rest is provable by simple algebra.

QED.


-/

/-
To test out of the final exam ...-/

/-#3: Give a formal proof for #2 or #3.-/

def power : ℕ → ℕ → ℕ 
| m 0 := nat.zero.succ 
| m (nat.succ(n')) := m * (power m n')

def s : ℕ → ℕ
| nat.zero := (nat.zero)
| (nat.succ(n')) := s n' + pow n'.succ 3

def P : ℕ → Prop :=
    λ n, 4 * (s n) = (power n 2) * (power (n+1) 2)

def conjecture := ∀ n, P n 

theorem ind_proof : conjecture :=
begin  
  assume n,
  unfold P,
  induction n with n' ih_n',

  -- P 0
  apply rfl,

  -- inductive step
  simp [s],
  simp[power],
  rw mul_add, 
  rw ih_n',
  simp[power],
  rw nat.succ_eq_add_one,
  
  -- by simple arithmetic
  sorry,

end

/-
#4: Formal or detailed informal proofs #10

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
-/ 

/-
#5: Formal or detailed informal proofs #11

Show that multiplication distributes over addition. In other words, 
prove that for natural numbers 𝑚, 𝑛, and 𝑘, 𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. You should 
use the definitions of addition and multiplication and facts proved 
in Section 17.4 (but nothing more).

**Answer:**

The proposition to be proven is the property of distributivity, m(n+k) = mn + mk.

To prove by induction, we fix n and k and use induction on m. To prove that
the proposition holds of every natural number m, it will suffice to 
prove that the proposition holds of zero, and whenever it holds of 
some number m, it holds of m + 1.

To prove the base case when m = 0, we use the first defining clause of 
multiplacation to easily solve that 0 = 0. 

    (n+k) * 0 = 0

In the inductive step, we have that:

    (n+k) * succ(m) = (n+k) * m + (n+k)
                    = (n+k) * (m + 1)
                    = (n+k) * (succ(m))
                    = (n * succ(m)) + (k * succ(m)) 
                    = (n(succ(m))) + (k(succ(m))) [end goal]

We can understand that this end goal is equivalent to our inductive step using 
the second defining clause of multiplacation. This gives that:

                    = mn + mk 
                    = (n * m + n) + (k * m + k)
                    = (n(m + 1)) + (k( m + 1))
                    = (n(succ(m))) + (k(succ(m)))


QED.
           
-/

/-
#6: Formal or detailed informal proofs #12

Prove the multiplication is associative, in the same way. You can use any 
of the facts proved in Section 17.4 and the previous exercise.

**Answer:**

The proposition to be proven is the associativity of multiplacation,
represented as m * (n * k) = (m * n) * k.

To prove by induction, we fix n and k and use induction on m. To prove that
the proposition holds of every natural number m, it will suffice to 
prove that the proposition holds of zero, and whenever it holds of 
some number m, it holds of m + 1.

To prove the base case when m = 0, we use the first defining clause of 
multiplacation to easily solve that 0 = 0. 

    (n*k) * 0 = 0
 
In the inductive step, we have that:

    (n*k) * succ(m) = (n*k) * m + (n*k)
                    = (n*k) * succ(m)
                    = (succ(m) * n) * (succ(m) * k)
                    = (m) * succ(n*k)

   
-/

#check nat.mul

/-
#7: Formal or detailed informal proofs #13

Prove that multiplication is commutative.

**Answer:**

The proposition to be proven is the commutativity of multiplacation,
represented as n * m = m * n.

To prove by induction, we fix n and use induction on m. To prove that
the proposition holds of every natural number m, it will suffice to 
prove that the proposition holds of zero, and whenever it holds of 
some number m, it holds of m + 1.

To prove the base case when m = 0, we use the first defining clause of 
multiplacation to easily solve that 0 = 0. 

    n * 0 = 0

In the inductive step, we have that:

    n * succ(m) = n * m + n
                = m * n + n
                = (m + 1) * n
                = succ(m) * n


-/

/-
#8: (Extra Credit): #5 or #9

NOT FINALIZED. ADVISORY. 
-/
