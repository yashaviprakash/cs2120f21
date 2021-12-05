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