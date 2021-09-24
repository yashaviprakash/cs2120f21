/-

Introduction rules and Elimination rules

= (Equality):

introduction rule: axiom of the reflexivity of equality (eq.refl)
elimination rule:  axiom of substituability of equality (eq.subs)

∧ (And)

introduction rule: and.intro _ _
elimination rule: and.elim_left and and.elim_right

∨ (Or)

introduction rule: or.intro_left and or.intro_right
elimination rule: or.elim

∀ (For All)

introduction rule: assume, then show rest
elimination rule: apply

→ (Implies)

introduction rule: assume, then show rest
elimination rule: apply

¬ (Not)
introduction rule: P → false
elimination rule: haven't talked about it yet

↔ (If and only If)

∃ (Exists)

introduction rule: 
elimination rule: 

true

introduction rule: true.intro
elimination rule: no elimination rule for true, doesn't give you the opportunity to prove anythign else

false

introduction rule: no proofs, no introduction rules
elimination rule: false.elim

-/