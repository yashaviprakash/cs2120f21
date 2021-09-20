/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

/- 1 (solved)-/
example : true := true.intro
/-Proof: Anything true needs a proof of true, 
and that is done by the introduction rule 
for true. QED. -/

/- 
false is uninhabited proposition type, a type with no values at all, no way to construct a proof of false
for an proposition to be false, there is no proof of it (true propositions have a truth to it)
-/

/- 2 (solved)-/
example : false :=   -- trick question? why? yes, bc there is no proof of false. 
/-Proof: If anything true means that it needs
a proof of true, anything false will need a 
proof of false as well. Therefore, a proof
of false must be empty as any proof of it
would result in it having a truth value. QED.-/

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
/- Proof : First, we assume that P is an 
arbitrary, but specific proposition. Then, 
we must apply the introduction rule of if 
and only if, to prove the beginning proposition 
in two ways: forwards and backwards. For the
forwards proposition, we must prove that P or P 
implies theproposition P. To do so, it is 
necessary first to assume that P or P is true 
(let's call it porp), and, from there it is 
necessary to split up the proof with a left disjunct 
and a right disjunct by the application of the or 
elimination rule. With the left disjunct, a proof of 
P can be assumed, which gives an exact proof of the 
implication, thus accomplishing our goal for the left 
disjunct. The same can be applied to the right disjunct, 
as well. Now, addressing the backwards proof, a proof 
of P must be assumed, and to prove that P implies 
P or P, a single proof of P can be applied to the left 
proposition of the or proposition to fully accomplish 
the intial goal of proving the beginning proposition. 
QED.-/

/-if p or p is true, then eiether p is true or p is true. 
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
/-Proof: First, we assume that P is an arbitrary, but
specific proposition. Then,to prove that if and only if 
P and P implies P then P implies P and P, it is necessary 
to apply the introduction rule for if and only if to construct 
a forward proof and a backward proof. To prove the forward 
proof that P and P implies P, it must be assumed that P and P 
is true. By the application left elimination rule for and, the 
implication of P can be proven true. To prove the backward proof 
that P implies P and P, it must be assumed that P is true, from 
which we can construct a proof for P and P by the use of the and 
introduction rule using the proof of P. QED. -/

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
    assume qorp,
    apply or.elim qorp,
    assume q,
    apply or.intro_right P q,
    assume p,
    apply or.intro_left Q p, 
end
/-Proof: First, we assume that P and Q are arbitrary, but specific propositions.
 To prove that if and only if P or Q is true, then Q or P is also true, it is 
 necessary to apply the introduction rule for the if and only if introduction
 rule to construct forward and backward proofs. To construct a forward proof,
 it is necessary to assume that P or Q is true (let's call it porq). To construct 
 a proof that Q or P is true, it is necessary to use the elimination rules 
 for or to conduct a case disjunct analysis, then apply the right and left or introduction
 rule to apply to Q or P to construct a proof for the implication that
 Q or P is true. To construct a backward proof that if Q or P is true then, by
 implication, P or Q is true, it is necessary to first assume that Q or P is 
 true (let's call it qorp). To prove that P or Q is true, it is necessary
 to use the or elimination rule to split up the solutions and conduct a 
 case disjunct analysis, which will prove the left disjunct and the right disjunct. 
 To do so, the use of the right and left or introduction rules are brought in to 
 result in a proof of true for the backwards proof. QED.-/

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
    cases f,
    exact f,
end


