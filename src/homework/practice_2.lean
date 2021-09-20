/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

/- 1 (solved with proof)-/
example : true := true.intro
/-Proof: Anything true needs a proof of true, 
and that is done by the introduction rule 
for true. QED. -/

/- 
false is uninhabited proposition type, a type with no values at all, no way to construct a proof of false
for an proposition to be false, there is no proof of it (true propositions have a truth to it)
-/

/- 2 (solved with proof)-/
example : false :=   -- trick question? why? yes, bc there is no proof of false. 
/-Proof: If anything true means that it needs
a proof of true, anything false will need a 
proof of false as well. Therefore, a proof
of false must be empty as any proof of it
would result in it having a truth value. QED.-/

/- for any propposition P, P or P is true if and only if P is true-/

/- 3 (solved with proof)-/
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
/- Proof : First, we assume that P is an arbitrary, but specific proposition. Then, 
we must apply the introduction rule of if and only if, to prove the beginning proposition 
(if and only if P ∨ P implies P then P implies P ∨ P) in two ways: forwards and backwards. 
To construct the forwards proof, it is necessary first to assume that P or P is true 
(let's call it porp) by the introduction rule for implies, and, from there it is necessary to 
split up the proof with a left disjunct and a right disjunct by the application of the or elimination rule. 
With the left disjunct, a proof of P can be assumed true by the introduction rule for applies (let's call this p), 
which gives an exact proof of the implication, thus accomplishing our goal for the left disjunct. 
The same proof can be applied to the right disjunct, as well. Now, addressing the backwards proof, a proof 
of P must be assumed by the introduction rule for implies (let's call it p), and to prove that P implies 
P or P, an exact proof of P ∨ P can be made using proof p by the left or introduction rule, thus
accomplishing the goal of the beginning proposition. QED.-/

/-if p or p is true, then eiether p is true or p is true. 
do case disjuction analysis on left side and on right side.-/

/- 4 (solved with proof)-/
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
/-Proof: First, we assume that P is an arbitrary, but
specific proposition. Then,to prove that if and only if 
P and P implies P then P implies P ∧ P, it is necessary 
to apply the introduction rule for if and only if to construct 
a forward proof and a backward proof. To prove the forward 
proof, it must be assumed that P ∧ P is true by the introduction 
rule for implies. By the application left elimination rule for and, we can
derive a proof of proposition P (let's call it p). This proof gives the exact proof of the
implication, which accomplishes the goals of the forward proof. To prove the backward proof 
that P implies P ∧ P, it must be assumed that P is true by the introduction rule
for implies (let's call this p), from which we can construct a proof for P ∧ P by the use 
of the and introduction rule using the proof p. QED. -/

/- 5 (solved with proof)-/
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
/-Proof: First, we assume that P and Q are arbitrary, but specific propositions.
 To prove that if and only if P or Q is true, then Q or P is also true, it is 
 necessary to apply the if and only if introduction rule to construct forward 
 and backward proofs. To construct a forward proof,
 it is necessary to assume that P or Q is true (let's call it porq) by the 
 introduction rule for implies. To construct a proof that Q or P is true, it is 
 necessary to use the or elimination rules to porq to conduct a case disjunct analysis. 
 To prove the left disjunct, it must first be assumed that there is a proof of proposition P
 (let's call it p) to prove the disjunct by applying left or introduction rule using proof p.
 To prove the right disjjunct, it must first be assumed that there is a proof of proposition Q
 (let's call it q) to prove the disjunct by applying the right or introduction rule using proof q.
 To construct a backward proof that if Q or P is true then, by
 implication, P or Q is true, it is necessary to first assume that Q or P is 
 true (let's call it qorp) by the introduction rule for implies. To prove that P or Q is true, it is necessary
 to use the or elimination rule to conduct a case disjunct analysis, which will help construct
 proofs of the left disjunct and the right disjunct. To prove the left disjunct, it must first be 
 assumed that there is a proof of proposition Q (let's call it q) to prove the disjunct by 
 applying right or introduction rule using proof q. To prove the right disjunct, it must first 
 be assumed that there is a proof of proposition P (let's call it p) to prove the disjunct by 
 applying the right or introduction rule using proof p. QED.-/

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
/-Proof: First, we must assume that P and Q are arbitrary, but specific 
propositions. To prove that if and only if P ∧ Q is true then Q ∧ P is 
true as well, we must apply the introduction rule for if and only if
to create a backwards and forward proposition to prove. To begin the
forward proposition that P ∧ Q → Q ∧ P, we must first assume that P ∧ Q
is true (let's call this h). To construct a proof of Q ∧ P, we must first split up 
the and proposition and find individual proofs of propositions P and Q that 
can be made possible by the usage of the and introduction rule and and elimination rule, respectively.
First, with the application of the introduction rule for and, we are given the two propositions
that make up P ∧ Q. Then with the application fo the right elimination rule and the left
elimination rule, we can construct a proof of Q ∧ P using the proofs of Q and P individually
using teh elimination rules. To begin with the backward proposition, the same rules apply
such that it can first be assumed that Q ∧ P is true to construct a proof that P ∧ Q is true.
By the use of the and introduction rule and the right and left and elimination rule, the proof
of P ∧ Q can be constructed. QED. 
-/

/- 7 -/
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
    apply or.intro_left (P ∧ R) (q ∧ P),
    
    
  -- backward
end

/- 8 -/
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
    assume p,
    apply or.intro_left (Q ∧ R) p,
    apply or.elim porr,
    
end

/- 9 (solved with proof)-/
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
/-Proof: First, we must assume that P and Q are arbitrary but specific propositions.
To construct a proof that if and only if P ∧ (P ∨ Q) implies P then P implies P ∧ (P ∨ Q), 
the if and only if introduction rule must be applied to construct forwards and backwards 
proofs. To begin constructing the forward proof, it must first be assumed that P ∧ (P ∨ Q) is true
by the introduction rule for implies (let's call it h). From here, we can create a proof 
for p by the left and elimination rule to h (let's call it p). This proof of P can be applied 
to the right of the implciation (which is proposition P) by the elimination rule for 
implies to accomplish the goals for the forward proof. To begin the backward proof, 
it can first be assumed that P is true (let's call it p) by the introduction rule for implies. 
To construct the proof of P ∧ (P ∨ Q), the application of the and
introduction rule is necessary to create a top-down approach to proving the implication.
This can be proved by applying the proof p to the proposition P as the elimination rule
for implies, and by applying the left introduction rule of or to the proposition Q using
the proof p. QED. 
-/

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


