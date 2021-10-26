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
    cases h with l k,
    -- left
      apply or.intro_right _,
      exact l,
    -- right
      apply or.intro_left _,
      exact k,
  -- backward
    assume h,
    cases h with k l,
    -- left
      apply or.intro_right _ ,
      exact k,
    -- right
      apply or.intro_left _ ,
      exact l,
  
end 

/-
informal proof: First, we can assume that L and K are arbitrary but specific 
sets of type α to prove that the set from the union of L and K is equal 
to the set from the union of K and L. To, prove this proposition, the 
axiom of set extensionality must be applied to expand this proposition and show
such set equality as a biimplication. From here, the arbitrary but specific value
x of type α can be assumed, and the biimplication can be split. To solve the forward
proof, the premise that x exists in L and K must be assumed true. Seeing that this
is a disjunction, case analysis can be applied on the premise, let's call it h, to
prove the implication as true through two cases: 1) x exists in L or 2) x exists in K. 
The implication can be proven in the first case by applying the right or introduction
rule, and it can be proven in the second case by applying the left or introduction rule.
To solve the backward proof, the premise that x exists in K and L must be assumed true.
Similar to the forward proof, case analysis can be applied on the disjunction, let's call
it h, to prove teh implication as true through two cases: 1) x exists in K or 2) x exists
in L. The implication can be proven in the first case by applying the right or introduction
rule, and it can be proven in teh second case by applying the left or introductino rule. 
QED.
-/


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

example : ∀ (α : Type) (H L K : set α), H ∩ (L ∩ K) = (H ∩ L) ∩ (H ∩ K) :=
begin
  intros α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  apply and.intro _ _,
  -- subgoal 1
  apply and.intro _ _,
  exact h.elim_left,
  have right := h.elim_right,
  have left := right.elim_left,
  exact left,
  -- subgoal 2
  have left := h.elim_left,
  have right := (h.elim_right).elim_right,
  exact and.intro left right,
  -- backward
  assume h,
  apply and.intro _ _,
  exact (h.elim_left).elim_left,
  have left := (h.elim_left).elim_right,
  have right := (h.elim_right).elim_right,
  apply and.intro left right,

end

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/

example : ∀ (α : Type) (H L K : set α), H ∪ (L ∩ K) = (H ∪ L) ∩ (H ∪ K):=
begin
  intros α H L K,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  cases h with h lk,
  apply and.intro _ _,
  apply or.intro_left _,
  exact h,
  apply or.intro_left _,
  exact h,
  cases lk with l k,
  apply and.intro _ _,
  apply or.intro_right _,
  exact l,
  apply or.intro_right _,
  exact k,
  -- backward
  assume h,
  cases h with hl hk,
  cases hl with h l,
  cases hk with h k,
  apply or.intro_left _,
  exact h,
  apply or.intro_left _,
  exact h,
  cases hk with h k,
  apply or.intro_left _,
  exact h,
  apply or.intro_right _,
  exact and.intro l k,

end


