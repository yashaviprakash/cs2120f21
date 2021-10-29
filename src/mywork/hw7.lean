def cong_mod (n a b: ℤ ) : Prop :=
∃ k, a - b = k * n 

def cong_mod_n_is_equiv_relation (n: ℤ ) : Prop :=
equivalence (cong_mod n )

#reduce cong_mod (4 : ℤ)
#reduce cong_mod (4 : ℤ) (6: ℤ) (10: ℤ)
/- 
funciton that takes two arguments a and b, and it yields a proposition that there exists some integer k, 
such that if you subtract b from a, this equals k * the integer version of the natural number 4
-/

-- Let's 
example : cong_mod (4 : ℤ) (6: ℤ) (14: ℤ) :=
begin
  unfold cong_mod, 
  apply exists.intro (-2 : ℤ) _,
  exact rfl,
  
end