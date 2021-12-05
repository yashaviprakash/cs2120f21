import tactic.ring

/-
Induction Principle:

∀ a : α, P a

For any type alpha, prove that P satisfies objects of that type

have to prove two lemmas:

P 0

∀ n', P n' → P (n' + 1)

**∀ a: nat, a = a**
**α → Type**
**P : α → Prop**

**base case:**

0=0

**inductive step:**

∀ n', n' = n' → n'.succ = n'.succ

-/

#check @nat.rec

/-

nat.rec :
  Π {motive : ℕ → Sort u_1}, 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  Π (n : ℕ), motive n

for any property of natural numbers, if zero has that property,
then if it's the case that for every natural number n, then the 
successor has that property, then every number has that property.

-/

#check @nat.rec_on

/-
in lean there's a second version of this induction principle

nat.rec_on :
  Π {motive : ℕ → Sort u_1} (n : ℕ), 
  motive 0 → 
  (Π (n : ℕ), motive n → motive n.succ) → 
  motive n

This one takes a natural number as a parameter

-/

-- a predicate defines a property
def P : ℕ → Prop := 
  λ (n: nat), n = n

#reduce P 3 -- returns the proposition that 3 = 3

-- now what we want to know is if the property holds for all natural numbers

example: ∀ n, P n :=
begin
  assume n,
  apply nat.rec_on n, -- takes 3 arguments (an arbitrary n and proofs of these two lemmas)
  
  -- n = 0
  unfold P, 

  -- inductive step
  unfold P,
  assume n' ih_n', -- assume n' is an arbitrary natural number and I assume I have proof of the property for n' (this is the induction hypothesis)

  

end

example : ∀ n, P n :=
begin
  assume n,
  induction n with n' ih_n',

  -- P 0
  apply rfl,

  -- inductive step
  unfold P,

  
end

/-
Prove question from last class

-/
def power : ℕ → ℕ → ℕ 
| m 0 := nat.zero.succ 
| m (nat.succ(n')) := m * (power m n')

def pow2 := power 2 -- turns it into a one argument function

def s : ℕ → ℕ
| nat.zero := (nat.zero).succ
| (nat.succ(n')) := s n' + pow2 (n'.succ)

#eval pow2 3
#reduce s 4

def Pn : ℕ → Prop :=
  λ n, s n = (pow2 (n.succ) - 1)

example : ∀ n, Pn n :=
begin
  assume n,
  unfold Pn,
  induction n with n' ih_n',

  -- P 0
  apply rfl,

  -- inductive step
  -- simp [s], -- successor calls the recursive call which the ih_n', answer for n' + 1 turns into answer for n
  -- rw ih_n',

  -- simp[pow2, power], -- can simplify using pow2

  simp[s, pow2, power],
  rw ih_n',
  simp[pow2],
  simp[power],
  
  -- by simple arithmetic
  sorry,
  
end

/-
English Language proof:

Let s(n) equal the sum of all the numbers from 2^0 to 2^n. Let P n
be the property that s(n) equals 2^(n + 1) - 1. We're to prove that
every natural number has this propert, ∀ n, P n. By induction for the
natural numbers, it will suffice to show P 0 and ∀ n', P n' → P (n' + 1).
To prove this we'll assume we're given n' and a proof that P n' to prove
P (n' + 1). By the definition of s, we can simplify the current goal to
using s and that allows us to rewrite the lefthand side. 

-/