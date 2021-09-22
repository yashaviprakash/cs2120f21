

example : true := true.intro


example : false :=   -- trick question? why? yes, bc there is no proof of false. 


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


example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pandp,
    have p: P := and.elim_left pandp,
    exact p,
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
    -- left disjunct
    assume p,
    apply or.intro_right Q p,
    -- right disjunct
    assume q,
    apply or.intro_left P q,
  -- backward
    assume qorp,
    apply or.elim qorp,
    --left disjunct
    assume q,
    apply or.intro_right P q,
    --right disjunct
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
  assume P Q R,
  apply iff.intro _ _,
  -- forward
    assume h,
    have qr : Q ∨ R := and.elim_right h,
    have p: P := and.elim_left h,
    apply or.elim qr,
    --left disjunct
    assume q,
    apply or.intro_left (P ∧ R) _,
    apply and.intro p q,
    -- right disjunct
    assume r,
    apply or.intro_right (P ∧ Q) _,
    apply and.intro p r,
  -- backward
    assume h,
    apply or.elim h,
    --left disjunct
    assume pandq,
    have p: P := and.elim_left pandq,
    have q: Q := and.elim_right pandq,
    apply and.intro _ _,
    exact p,
    apply or.intro_left R q,
    --right disjunct
    assume pandr,
    have p: P := and.elim_left pandr,
    have r: R := and.elim_right pandr,
    apply and.intro _ _,
    exact p,
    apply or.intro_right Q r,
end


example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
    assume h,
    apply or.elim h,
    -- left disjunct
    assume p,
    apply and.intro _ _,
    apply or.intro_left Q p,
    apply or.intro_left R p,
    --right disjunct
    assume h,
    have q : Q := and.elim_left h,
    have r : R := and.elim_right h,
    apply and.intro _ _,
    apply or.intro_right P q,
    apply or.intro_right P r,
  --backward
    assume h,
    have porq : P ∨ Q := and.elim_left h,
    have porr : P ∨ R := and.elim_right h,
    apply or.elim porq,
    --left disjunct
    assume p,
    apply or.intro_left (Q ∧ R) p,
    --right disjunct
    assume q,
    apply or.elim porr,
      -- left disjunct of porr
      assume p,
      apply or.intro_left (Q ∧ R) p,
      --right disjunct of porr
      assume r,
      apply or.intro_right P _,
      apply and.intro q r,
end



example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
    assume h,
    have p: P := and.elim_left h,
    exact p,
  -- backward
    assume p,
    apply and.intro _ _,
    exact p,
    apply or.intro_left Q p,
end


example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume porpq,
  apply or.elim porpq,
  -- left disjunct
  assume p,
  exact p,
  -- right disjunct
  assume h,
  exact and.elim_left h,
  --backward
  assume p,
  apply or.intro_left (P ∧ Q) p,
end



example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume port,
    apply or.elim port,
    -- left disjunct
    assume p,
    apply true.intro,
    -- right disjunct
    assume t,
    exact t,
  -- backward
    assume t,
    apply or.intro_right P t,
end



example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porf,
    apply or.elim porf,
    -- left disjunct
    assume p,
    exact p,
    -- right disjunct
    assume f,
    cases f,
  -- backward
    assume p,
    apply or.intro_left false p,  
end



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
    cases f,
    exact f,
end



