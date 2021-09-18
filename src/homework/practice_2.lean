/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

/- 
false is uninhabited proposition type, a type with no values at all, no way to construct a proof of false
for an proposition to be false, there is no proof of it (true propositions have a truth to it)
-/
example : false :=    -- trick question? why? yes, bc there is no proof of false. 

/- for any propposition P, P or P is true if and only if P is true-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
    assume P, 
    apply iff.intro _ _,
    -- forward
      assume porp, 
      apply or.elim porp,
      -- left disjunct is true
        assume p,
        exact p,
      -- right disjunct is true
        assume p,
        exact p,
  -- backwards
    assume p, 
    exact or.intro_left P p, /- or intor rule takes two arguments, a propostion and a proof-/
end
/- english language prooof:

if p or p is true, then eiether p is true or p is true. 
do case disjuction analysis on left side and on right side.-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandp,
    apply and.elim_left pandp,
  -- backward
    assume p,
    exact and.intro p p,

end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume porq,
    apply or.elim porq,
    assume p,
    apply or.intro_right Q p,
    assume q,
    apply or.intro_left P q,
  -- backward
    assume porq,
    apply or.elim porq,
    assume q,
    apply or.intro_right P q,
    assume p,
    apply or.intro_left Q p, 
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q, 
  apply iff.intro _ _,
  -- forward
    assume h,
    apply and.intro _ _,
    apply and.elim_right h,
    apply and.elim_left h,
  -- backward
    assume h,
    apply and.intro _ _,
    apply and.elim_right h,
    apply and.elim_left h,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume port,
    apply or.elim port,
    assume p,
    apply true.intro,
    
  -- backward
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porf,
    apply or.elim porf,
    assume p,
    exact p,
    /- anything false has on proof, do i just leave it blank?-/
  -- backward


end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
end


