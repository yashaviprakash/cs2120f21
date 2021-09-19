/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

/- 1 (solved)-/
example : true := true.intro
/-English Language Proof: Anything true needs a proof of true, 
and that is done by the introduction rule for true.-/

/- 
false is uninhabited proposition type, a type with no values at all, no way to construct a proof of false
for an proposition to be false, there is no proof of it (true propositions have a truth to it)
-/
/- 2 (solved)-/
example : false :=   -- trick question? why? yes, bc there is no proof of false. 
/-English Language Proof: If anything true means that it needs
a proof of true, anything false will need a proof of false as well.-/

/- for any propposition P, P or P is true if and only if P is true-/
/- 3 (solved)-/
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
    exact or.intro_left P p,
end
/- english language prooof: We prove 

if p or p is true, then eiether p is true or p is true. 
do case disjuction analysis on left side and on right side.-/
/- 4 (solved)-/
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

/- 5 (solved)-/
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

/- 6 (solved)-/
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

/- 7 -/
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume h,
    have qr : Q ∨ R := and.elim_right h,
    have p: P := and.elim_left h,
    
  -- backward
end

 
/- 8 -/
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
end

/- 9 (solved)-/
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    have p: P := and.elim_left h,
    exact p,
  -- backwrad
    assume p,
    apply and.intro _ _,
    exact p,
    apply or.intro_left Q p,
end

/- 10 (solved)-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume porpq,
  apply or.elim porpq,
  assume p,
  exact p,
  assume h,
  exact and.elim_left h,
  --backward
  assume p,
  apply or.intro_left (P ∧ Q) p,
end

/- 11 (solved)-/
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume port,
    apply or.elim port,
    assume p,
    apply true.intro,
    assume t,
    exact t,
  -- backward
    assume t,
    apply or.intro_right P t,
end

/- 12 (solved)-/
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
    /- have no idea how i answered this????????-/
    assume f,
    apply false.elim,
    exact f,
  -- backward
    assume p,
    apply or.intro_left false p,
    
end

/- 13 (solved)-/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pant,
    apply and.elim_left pant,
  -- backward
    assume p,
    apply and.intro _ _,
    exact p,
    apply true.intro,
end

/- 14 (solved)-/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandf,
    apply and.elim_right pandf,
  -- backward
    assume f,
    apply and.intro _ _,
    apply false.elim,
    exact f,
    exact f,
end


