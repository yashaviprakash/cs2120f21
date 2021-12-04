import algebra.algebra.basic tactic.ring
namespace hidden
def sum_to : ℕ → ℕ
| (nat.zero)    := nat.zero                 -- base
| (nat.succ n')  := (sum_to n') + (n'.succ)
 
def pow : ℕ → ℕ → ℕ
| m 0        := 1
| m (n + 1)  := m * pow m n
 
def dec : nat → nat
| (nat.zero) := nat.zero --all Lean functions must be total (err if this is the only arg)
| (nat.succ n') := n'
 
def P : ℕ → Prop :=
  λ n, sum_to (pow 2 n) = dec (pow 2 (n+1))
 
  -- 2 to the 3 (2^0 + 2^1 + 2^2 + 2^3 = 15), 2 to the 4 - 1 (16-1=15)
 
example : ∀ n, P n :=
begin
  unfold P,
  assume n,
  induction n with n' ih_n', -- sum_to
  apply rfl,
  -- in our context: n' (nat), h (# of elems in a set of size n'+1 is 2 to the n'+1)
  simp [pow],
  ring_nf,
end
end hidden