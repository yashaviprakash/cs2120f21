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
Informal Proof: First, we can assume that L and K are arbitrary but specific 
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
rule, and it can be proven in the second case by applying the left or introductino rule. 
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
  -- left : prove that ⊆ is reflexive
  assume a,
  assume x,
  assume h,
  exact h,
  -- right : prove that ⊆ is transitive
  assume H K L a b,
  assume x,
  assume h,
  have k := a h,
  have l := b k,
  exact l,
  
end  

/-
Informal Proof: First, we can assume that α is a specific type for the proposition. 
Seeing as the proposition is a conjunction, the introduction rule for and can be applied
with placeholders to further break down the propositions to prove. To prove the left
proposition that ⊆ is reflexive, it must first be assumed that a is an arbitrary but 
specific set of type α. Because we understand set equality as an implication that if 
a value of the same type exists in one set then it must exist in another, we must first
assume that we have a value, x, that is an arbitrary but specific value of type α. From here,
we can assume the premise that x exists in a. Seeing that the proof is true and ⊆ is indeed
reflexive, the exact proof of the implication is found in the premise. To prove the right
proposition that ⊆ is transitive, it must first be assumed that H K and L are arbitrary but
specific sets of type α, and that H ⊆ K and K ⊆ L are both true to prove that H ⊆ L. From here, 
using our same understanding of set equality, it can be assumed that x is an arbitrary but specific 
value x of type α. From here, the premise that x exists in H must be assumed true. To prove that
x exists in L, our understanding of the transitive proprerty of equality can similiarly be applied
to our understanding of the transitive property of ⊆ such that x exists in L if x exists in K first 
given our proof that x exists in H. To derive the proof that x exists in K, the proof that H ⊂ K must
be applied to our proof that x exists in H. From here, we can derive an exact proof that x exists in 
L by applying the proof that K ⊆ L to our proof that x exists in K. This concludes the proof, and
proves that ⊆ has the property of being both reflexive and transitive. QED. 
-/


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
    -- left
      exact h,
    -- right
      exact and.intro l k,
  -- backward
  assume h,
  cases h with h lk,
  cases lk with l k,
  apply and.intro _ _,
    -- left
      exact and.intro h l,
    -- right
      exact k,

end

/-
Informal Proof: First, it must be assumed that H L and K are arbitrary but specific sets of type α, 
such that ∩ is associative in the context of these three sets. To begin to prove such proposition, the
use of set equality must be recognized to apply the axiom of set extensionality must be applied to expand 
this proposition and show such set equality as a biimplication. From here, the arbitrary but specific value
x of type α can be assumed, and the biimplication can be split. To prove the forward proof, it must first
be assumed that the premise that x exists in (H ∩ L) ∩ K is true. Seeing as this is a conjunction, case analysis
can be applied to obtain The proofs that x exists in H ∩ L and x exists in K. To further break down the conjunction
of H ∩ L, case ansalysis can be applieda gain to obtain the proofs that x exists in H and x exists in L. From here, 
we can recognize the goal that x exists in H ∩ (L ∩ K) in the form of a conjunction, the introduction rule for and 
can be applied with placeholders to further break down the proofs. The exact proof of the left conjunct can be obtained 
using the proof that x exists in H, and the exact proof of the right conjunct can be obtained using the introduction
rule for and using the proof that x exists in L and that x exists in K. To prove the backward proof, the premise that 
x exists in H ∩ (L ∩ K) must be assumed true. Seeing as this premise is in the form of a conjunction, the case analysis
can be applied twice the same way as the forward proof to prove that x exists in h, x exists in l, and x exists in h. 
Seeing that the goal is also in the form of a conjunction, it can be simplified by applying the introduction ruel for
and using placeholders to further simplify the proofs. The exact proof of the left conjunct can be obtained using
the introduction rule for and using the proofs that x exists in H and x exists in L, and the exact proof of the right 
conjunct can be obtained using the proof that x exists in K. QED. 
-/

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
    -- first case
      apply or.intro_left _,
      exact h,
    -- second case
      apply or.intro_right _,
      apply or.intro_left _ ,
      exact l,
    -- third case
      apply or.intro_right _,
      apply or.intro_right _,
      exact k,
  -- backward
  assume h,
  cases h with h lk,
    -- first case
      apply or.intro_left _,
      apply or.intro_left _,
      exact h,
    cases lk with l k,
    -- first case
      apply or.intro_left _,
      apply or.intro_right _,
      exact l,
    -- second case
      apply or.intro_right _,
      exact k,

end

/-
Informal Proof: First, it must be assumed that H, L, and K are arbitrary but specific sets
of type α, such that ∪ is associative in the context of these three sets. To begin to prove such proposition, the
use of set equality must be recognized to apply the axiom of set extensionality must be applied to expand 
this proposition and show such set equality as a biimplication. From here, the arbitrary but specific value
x of type α can be assumed, and the biimplication can be split. To begin the forward proof, the premise that 
x exists in (H ∪ L) ∪ K must first be assumed true. Seeing as this is a disjunct, two case analyses can be applied
on the premise and the disjunct within the premise to create three total cases to be considered for the proof. The 
first case can be proven by using the exact proof given in the case analysis that x exists in H using the left or
introduction rule. The second proof can be proven using our proof that x exists in L. To be able to use said proof, 
the right or introduction rule followed by the left or introduction rule can be applied to isolate that part of the 
implication where the proof that x exists in L can be used to prove the implication true. The third proof can 
be proven using our proof that x exists in K, and it can be used similar to the second proof. The double application 
of the right or introduction rule to the proof that x exists in K will prove the forward proof. To begin the
backward proof, the premise that x exists in H ∪ (L ∪ K) must be assumed true. Seeing that this is a disjunct, case 
analysis can be applied on the premise to create two cases where x exists in H and where x exists in (L ∪ K). To prove 
the first case, the double application of the left or introduction rule can be applied to the proof that x exists in H 
to prove the implication that x exists in H ∪ (L ∪ K). To prove the next case, it must be recognized that the proof
that x exists in (L ∪ K) must be further simplified to create more cases using case analysis as this disjunct is not 
presented with each other in the implication. These cases will represent proofs where x exists in L and one where
x exists in K. To prove the goal using the first case, the application of the left or introduction rule followed by
the right or introduction rule must be applied to the goal to isolate the part of the goal we have a proof for: x exists
in L. To rpove the goal using the second case, the right or introduction rule must be applied to the proof that x exists
in K to conclude the backward proof. QED.

-/


/-
Assignment: read (at least skim) the Sections 1 and 
2 of the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state, and prove both formally and 
informally, that ∩ is left-distributive over ∩.
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
    -- subgoal 1 of subgoal 1
      exact h.elim_left,
    -- subgoal 2 of subgoal 1
      have lk := h.elim_right,
      have l := lk.elim_left,
      exact l,
  -- subgoal 2
    have h_2 := h.elim_left,
    have k := (h.elim_right).elim_right,
    exact and.intro h_2 k,
  -- backward
  assume h,
  apply and.intro _ _,
    -- subgoal 1
      exact (h.elim_left).elim_left,
    -- subgoal 2
      have l := (h.elim_left).elim_right,
      have k := (h.elim_right).elim_right,
      apply and.intro l k,

end

/-
Informal Proof: First, it must be assumed that H L and K are arbitrary but specific sets
of type α, such that H ∩ (L ∩ K) = (H ∩ L) ∩ (H ∩ K) and ∩ is left-distributive over
∩. o begin to prove such proposition, the use of set equality must be recognized to apply the 
axiom of set extensionality must be applied to expand this proposition and show such set equality 
as a biimplication. From here, the arbitrary but specific value x of type α can be assumed, and the 
biimplication can be split. To begin the forward proof, the premise that x exists in H ∩ (L ∩ K)
must be assumed to be true. Seeing as the proposition is a conjunction, the introduction rule for 
and can be applied with placeholders to further break down the propositions to prove. To prove the 
first subgoal that x exists in H ∩ L, the introduction rule for and can be applied once more with 
placeholders to further break down the goal. From here, we can solve the first goal of the subgoal 
that x exists in H using the left elimination rule applied to the premise. To solve the second goal 
of the first subgoal that x exists in L, the premise can be broken down using right elimination rule
for and followed by the left elimination rule for and for the exact proof of the goal. To solve the 
second subgoal that x exists in H ∩ K, we can use the left elimination rule for and to obtain the proof
for h, and we can use the double application fo the right elimination rule for and to obtain teh proof
for k. From here, we can receive the exact proof of the intersection using the introduction rule for and
and the proofs of H and K. This concludes the forward proof. To begin the backward proof, the premise
that x exists in (H ∩ L) ∩ (H ∩ K) must be assumed true. Seeing as the proposition is a conjunction, 
the introduction rule for and can be applied with placeholders to further break down the propositions 
to prove. To obtain the exact proof for the first subgoal, we can use the double application of the
left elimination rule on the premise to obtain the proof that x exists in H. To obtain the proof for
the second subgoal that x exists in L ∩ K, we can use the left and elimination rule followed by the
right and elimination rule to obtain the proof for L, and we can use the double application of the
right elimination rule to obtain the proof for K. With these proofs, we can use the introduction rule
for and to create a conjunction to solve the goal. QED.

-/

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
    -- case one
    apply and.intro _ _,
      -- subgoal one
        apply or.intro_left _,
        exact h,
      -- subgoal two
        apply or.intro_left _,
        exact h,
    -- case two
    cases lk with l k,
    apply and.intro _ _,
      -- subgoal one
        apply or.intro_right _,
        exact l,
      -- subgoal two
        apply or.intro_right _,
        exact k,
  -- backward
  assume h,
  cases h with hl hk,
  cases hl with h l,
  cases hk with h k,
    -- case one
      apply or.intro_left _,
      exact h,
    -- case two
      apply or.intro_left _,
      exact h,
    -- case three
      cases hk with h k,
      -- sub case one
        apply or.intro_left _,
        exact h,
      -- sub case two
        apply or.intro_right _,
        exact and.intro l k,

end

/-
Informal Proof: First, it must be assumed that H L and K are arbitrary but specific sets
of type α, such that H ∪ (L ∩ K) = (H ∪ L) ∩ (H ∪ K) and ∪ is left-distributive over
∩. o begin to prove such proposition, the use of set equality must be recognized to apply the 
axiom of set extensionality must be applied to expand this proposition and show such set equality 
as a biimplication. From here, the arbitrary but specific value x of type α can be assumed, and the 
biimplication can be split. To prove the forward proof, it must first be assumed that the premise 
that H ∪ (L ∩ K) is true. Seeing that the premise is a disjunct, case analysis can be applied on the 
the premise to create two cases: 1) that x exists in H, and 2) that x exists in L ∩ K. To begin case 
one, it must first be recognized that goal is a conjunction and can be broken down into smaller, simpler
subgoals using the application of the introduction rule for and using placeholders. To solve the first 
subgoal, the application of the left introduction rule for or can be applied using the exact proof that
x exists in H. the second subgoal can be solved the saem way. To begin case two, it can be recognized that
L ∩ K is a conjunction, and can be broken down to two individual proofs that x exists in L and that x exists
in K using the cases tactic. From here, we can simplify the goal using the application of the introduction
rule for and with placeholders to create smaller subgoals. To solve the first subgoal, the application of
the right introduction rule for or can be applied using the exact proof that x exists in L. The second
subgoal will also be proven using the application of the right introduction rule to the exact proof that 
x exists in K. To begin the backward proof, the premise that (H ∪ L) ∩ (H ∪ K) must be assumed to be true. 
Seeing that the premise is a conjunction, the cases tactic can be used to break down the conjunction. From here,
we can see that each conjunct is actually a disjunct. From here, we can use case analysis twice to generate
three cases to solve the backward proof. To begin the first case, we can prove that x exists in H ∪ (L ∩ K)
using the left or introduction rule and the exact proof that x exists in H. The second case can be solved
the same way. For the third case, we can regcognize it as being capable of being broken down further as we 
have recognized that x exists in H ∪ K is a disjunct that can produce two subcases via case analysis. 
Using this approach, we can solve the first subcase using the left or introduction rule using the exact proof of H. 
We can then solve the second subcase using the application of the right or introduction rule to the proof of the
conjunction using the individual proofs of L and K. QED.

-/




