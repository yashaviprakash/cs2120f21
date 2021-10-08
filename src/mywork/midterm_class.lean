/-
arrow is a shorthand for for all

P → Q is the same thing as saying that ∀ (p: P), Q

If you have a proof of an implication P→Q which is a function, 
a funciton has to be total

Given any proof of P, youc an get back a proof of Q
-/

/- given any natural number, you can return a natural number-/
def func : ∀ (n : ℕ ), ℕ :=
begin
 assume n,
 exact n,
end

#reduce func 3
#reduce func 0
#reduce func 100

/- two proofs of the same proposition are always defined to be
equal in lean

proof irrelevance (idk is that what he said??)

tt : bool and ff :bool is not equal

true does not imply false
some truth does not imply false
-/
