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

/- 6 (solved with proof)-/
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
that make up P ∧ Q. Then with the application of the right elimination rule and the left
elimination rule, we can construct a proof of Q ∧ P using the proofs of Q and P individually
using teh elimination rules. To begin with the backward proposition, the same rules apply
such that it can first be assumed that Q ∧ P is true to construct a proof that P ∧ Q is true.
By the use of the and introduction rule and the right and left and elimination rule, the proof
of P ∧ Q can be constructed. QED. 
-/

/- 7 (solved)-/
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
    --left disjunct
    assume p,
    apply or.intro_left (Q ∧ R) p,
    --right disjunct
    assume q,
    apply or.intro_right P _,
    apply and.intro q _,


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

/- 10 (solved with proof)-/
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
/-Proof: We must first assume that P and Q are arbitrary but specific propositions. 
To prove that if and only if P ∨ (P ∧ Q) implies P then P implies P ∨ (P ∧ Q), the 
application of the if and only if introduction rule can be applied to construct
forwards and backwards proofs to prove the beginning proposition. To construct the
forward proof, it must first be assumed that P ∨ (P ∧ Q) is true by the introduction
rule for implies. To construct a proof that P ∨ (P ∧ Q) is true, it is 
necessary to use the or elimination rules to porq to conduct a case disjunct analysis. 
This will help to construct a proof of the left disjunct and the right disjunct. To prove
the left disjunct, the proposition P must be assumed true by the usage of the
introduction rule of implies (let's call it p). This produces an exact proof of the 
implication which accomplishes the goal of the left disjunct. To prove the
right disjunct, the proposition P ∧ Q must be assumed true by the usage of the
introduction rule for implies. The left and elimination rule to h produces the exact proof
of the proposition P, thus accomplishing the goals fo the right disjunct and the forward
proof. To begin the backward proof, it must first be assumed that the proposition P is true
by the usage of the introduction rule for implies (let's call it p). The application of
the left or itnroduction rule to P ∧ Q using the proof p will construct the backward proof 
and proving the beginning proposition. QED. -/

/- 11 (solved with proof)-/
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
/-Proof: We must first assume that P is an arbitrary but specific proposition. To prove that
if and only if P ∨ true implies true then true implies P ∨ true, the introduction rule
for if and only if must be applied to construct forward and backward proof. To begin the forward
proof, we must first assume that the proposition P ∨ true is true by the introduction rule
for implies. To construct a proof that P ∨ true is true, it is 
necessary to use the or elimination rules to porq to conduct a case disjunct analysis. This
will help to construct a left disjunct and right disjunct. To begin the left disjunct, it must
first be that the prosition P is true by the usage of the introduction rule for implies (let's call it p). To 
imply that P is true, the introduction rule for true can be implied to accomplish the 
goals of the left disjunct. To begin the right disjunct, it can be assumed that true is true
by the usage of the introduction rule for implies (let's call it t), which produces the exact proof of the
implication and the right disjunct. To begin the backward proof, it must be assumed
that true is true by the introduction rule for implies (let's call it t). This proof of t 
can be applied to the right or introduction rule to prove P ∨ true by the introduction rule 
for or. This will accomplish the goal of the backwrad proof nad the prove beginning proposition. 
QED.
-/

/- 12 (solved with proof)-/
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
/-Proof: We must first assume that P is an arbitrary but specific proposition. To prove that
if and only if P ∨ false implies P then P implies P ∨ false, the introduction rule
for if and only if must be applied to construct forward and backward proof. To begin the 
forward proof, it must first be assumed that P ∨ false is true by the usage of the introduction
rule for implies (let's call it porq). To construct a proof that P ∨ false is true, it is 
necessary to use the or elimination rules to porq to conduct a case disjunct analysis. This
will help to construct a left disjunct and right disjunct. To begin the left disjunct, it must
firs tbe assumed that the proposition P is true by the usage of the introduction rule for implies
(let's call it p), which produces an exact proof of the implication of the left disjunct.
To begin the right disjunct, it must be assumed that false is true by the use of the introduction
rule for implies. As there can be no proofs for false, it must first be asked from lean how 
many case analysis there can be to prove that false is true. The absence of any accomplishes the
goal for the right disjunct. To prove the backwards proof, it must first be assumed that the 
proposition P is true (let's call it p) by the introduction rule for implies. To prove that 
P ∨ false is true the proof of p must be applied using the left or introduction rule. This 
proves the backward proof and the beginning proposition. QED.
-/

/- 13 (solved with proof)-/
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
/-Proof: We must first assume that P is an arbitrary but specific proposition. To prove that
if and only if P ∧ true implies P then P implies P ∧ true, the introduction rule
for if and only if must be applied to construct forward and backward proof. To begin the 
forward proof, it must first be assumed that P ∧ true is true by the usage of the introduction
rule for implies. To begin constructing the forward proof, it must be assumed that P ∧ true
is true by the usage of the introduction rule for implies (let's call it pant). The proof
of P can thus be proved by the application fot he left and elimination rule, which concludes
the forward proof. To begin the backward proof, it must first be assumed that the proposition P
is true (let's call it p). Then by the top-down approach, the application of the and introduction
rule can construct a proof that P ∧ true is true. The proposition P can be true as it is an exact
proof of proof p that was intially assumed. The proposition true can be true by the application
of the introduction rule of true, thus proving the backward proof and the beginning proposition. QED.
-/


/- 14 (solved with proof)-/
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
/-Proof: We must first assume that P is an arbitrary but specific proposition. To prove that
if and only if P ∧ false implies false then false implies P ∧ false, the introduction rule
for if and only if must be applied to construct forward and backward proof. To begin the 
forward proof, it must first be assumed that P ∧ false is true by the usage of the introduction
rule for implies (let's call it pandf). The proof of the implication false can be proven by the
the application of the right and elimination rule to pandf. This concludes and proves the forward
proof. To begin the backward proof, it must first be assumed that false is true by the usage of the introduction
rule for implies (let's call it f). From there a top-down approach can be implemented, by applying
the and introduction rule. By the top-down approach, the implication of P can be proven true
by asking lean to assess the case analysis of the proposition. As there can be no proofs for false, 
it must first be asked from lean how many case analysis there can be to prove that false is true. The absence of
any cases accomplishes the goal of filling in the left proof of the and introduction rule. Lastly, 
to prove that false → false in the backward proof, exact can be used as the intital assumption that
false is true produces the exact proof of the implication, thus completing the backward proof and proving 
the beginning proposition. QED.
-/



