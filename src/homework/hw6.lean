import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/

example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  intros α L,
  apply set.ext _ ,
  assume x,
  split,
  assume h,
  --apply and.elim_left h,
  exact h.left,
  assume k,
  apply and.intro k k,

end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/

example : ∀ (α : Type) (L K : set α), L ∪ K = K ∪ L :=
begin
  intros α L K,
  apply set.ext _ ,
  assume x, 
  split, 
  -- forward
  assume h,
  cases h with left right,
  -- left
  apply or.intro_right _,
  exact left,
  -- right
  apply or.intro_left _,
  exact right,
  -- backward
  assume h,
  cases h with left right,
  apply or.intro_right _ ,
  exact left,
  apply or.intro_left _ ,
  exact right,
  
end 


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/

example :∀ (α : Type), (∀ (a : set α), (a ⊆ a)) ∧ (∀ (H K L : set α ) (a: H ⊆ K) (b: K ⊆ L), H ⊆ L) :=
begin
  assume α,
  apply and.intro _ _,
  -- left
  assume a,
  assume x,
  assume h,
  exact h,
  -- right
  assume H K L a b,
  assume x,
  assume h,
  have k := a h,
  have l := b k,
  exact l,
  
end  


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/

example : ∀ (α : Type) (H L K : set α), (H ∩ L) ∩ K = H ∩ (L ∩ K) :=
begin
  intros α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with hl k,
  cases hl with h l,
  apply and.intro _ _,
  exact h,
  exact and.intro l k,
  -- backward
  assume h,
  cases h with h lk,
  cases lk with l k,
  apply and.intro _ _,
  exact and.intro h l,
  exact k,

end

example : ∀ (α : Type) (H L K : set α), (H ∪ L) ∪ K = H ∪ (L ∪ K) :=
begin
  assume α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with hl k,
  cases hl with h l,
  apply or.intro_left _,
  exact h,
  apply or.intro_right _,
  apply or.intro_left _ ,
  exact l,
  apply or.intro_right _,
  apply or.intro_right _,
  exact k,
  -- backward
  assume h,
  cases h with h lk,
  apply or.intro_left _,
  apply or.intro_left _,
  exact h,
  cases lk with l k,
  apply or.intro_left _,
  apply or.intro_right _,
  exact l,
  apply or.intro_right _,
  exact k,



end


/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


