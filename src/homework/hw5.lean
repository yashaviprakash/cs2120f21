import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a  : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- If there's a function that maps/takes every α value that provides
a proof for a β value, then a proof of q can be derived using that function
given that every α value satisfies predicate p. Additionally, if there exists 
a value of type α that satisfies predicate p, then there exists a value of type 
β that satisfies predicate q. 
-/

/- 
to clarify: before I was determining the witness was something that was correct
but not directly provided by earlier premises. This method will make sure that everything
that was directly provided by teh earlier premise stands. 
-/
-- Give your formal proof here
begin 
  assume h, -- first premise
  assume e, -- second premise
  cases h with atob f_all, -- split up h to receive witness and proof
  cases e with a ptoa, -- split up e to receive witness and proof
  apply exists.intro (atob a) _, -- top down approach to solve implication
  -- witness
    --exact atob a, 
  -- proof
    have pa_imp := f_all a,
    have q_b := pa_imp ptoa,
    exact q_b,  
  
end

-- informal proof of the proposition
/-
To prove this proposition, the first and second premise must be assumed. Given 
that both premises are existential propositions, exists elimination using case 
analysis must be applied on both propositions. This yields the wtinesses (the function 
f of α → β and the value a of type α) 
and the proofs (the proof of the for all proposition and the proof that a satisfies
predicate p) for both propositions. This gives sufficient information to prove 
the implication that there exists an object of type β that satisfies predicate q. 
To prove the implication, the top-down approach can be employed on the application of
the introduction rule for exists. 

To obtain the witness, f can be applied to a. To obtain the proof, a proof that the value f(a) satisifes the predicate q, 
the proof of the value a and the proof that a satisfies predicate p must be applied
to the for all proposition. This satisfies the proof. QED. 

-/
