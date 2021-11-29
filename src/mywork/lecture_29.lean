import algebra.algebra.basic tactic.ring 

namespace hidden

/-
define data types using inductive defintions in constructive logic

if we wanted a data type to represent employees then we would have fields that define employees
-/

/-
natural numbers: data type

we need some notion that we can repeatedly build up larger values which is where truly
recursive/inductive notions come to play
-/
 -- keyword for defining new datatype in logic of lean is inductive
 inductive nat : Type -- declaring that nat lives in Type
 | zero : nat
 | succ (n' : nat) : nat -- constructor takes an argument of type nat and gives one bigger value of type nat


def z := nat.zero 
#reduce z

def o := (z).succ
#reduce o

def t := (o).succ
#reduce t

def f : nat := -- have to include type of f
begin
  exact nat.succ (nat.succ t), -- what this shows you is that you can use either terms or proof scripts and their interchangeable
end 

#reduce f -- four successors applied to zero

/- what about functions involving natural numbers? -/

-- increment function (type is nat to nat)
def inc : nat → nat :=
begin
  assume n,
  apply nat.succ n,
end

#reduce inc f -- incrementation of four returns five

def inc' : nat → nat
  | n := nat.succ n

#reduce inc'(f)

def dec : nat → nat -- our two cases are zero and the successor of something
| nat.zero := nat.zero -- in the natural numbers
| (nat.succ n') := n'

def add : nat → nat → nat -- way you do addition is by iterating increment function
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)-- answer for n', if i add 3 and 4 that's the successor of adding 2 and 4 and the successor of adding 1 and 4 which is the successor of adding 0 and 4
-- we're adding (1 + n') to m
-- we assume that we have an ability to instantly get an answer for n' + m 

#reduce add f t

def mul : nat → nat → nat -- multiplacation is iterating the addition of the second argument (3 * 4 is four 3 times which is 4 + 4 + 4 which is 4 + 2 * 4 which is 4 + 1 * 4 which is 4 + 0 * 4)
|(nat.zero) (m) := nat.zero
|(nat.succ n') (m) := add (m) (mul n' m)-- we know m and n', and we can also by induction 

#reduce mul f t

-- exponentiation is iterative multiplacation

def sum_to : nat → nat 
| nat.zero := nat.zero
| (nat.succ n') := add (sum_to(n')) (inc' n')-- assume you have answer for n' and express that assumption by calling that assumption recursively

#reduce sum_to f

end hidden