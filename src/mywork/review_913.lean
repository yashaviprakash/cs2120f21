namespace Implies
 
axioms (P Q : Prop) /- abstract names for ordinary propositions -/
 
def if_P_is_true_then_so_is_Q: Prop := P → Q /- if you know that P implies Q and P is true, then you know that Q is true-/
 
axiom p : P
-- asume P is true
-- assume we have a proof of P (p)
 
axiom pq : P → Q /- how we knwo that P implies Q is true-/
-- assume that we have a proof, pq, of P → Q
-- type of P → Q is a proposition, P is a proposition, and Q is a proposition
 
-- intro for implies: assume premise, show conclusion
-- elimination rule for implies: (how do we use a proof of an implication) apply a proof of P → Q to a proof of P, the result of that is Q
-- apply pq to a proof of P to derive a proof of Q
 
#check pq
#check p
#check (pq p) /- applciation of proof of implies prop to proof of P will derive a proof of Q-/
/- english language proof: by the elimination rule for implies, we have derived the proof of Q-/
 
/-
Suppose P and Q are propostiions and you
know that P → Q and that Q are both true
Show that Q is true.
 
Proof: Apply the truth of P → Q to the truth
of P to derive the truth of Q
 
Proof: By the elimination rule for implies with
pq applied to p
 
Proof: By "modus ponens". QED (philosophical approach)
-/
 
end Implies
 
namespace ForAll
 
axioms
 (T: Type)
 (P: T → Prop) /-prdicate of Type T that takes value of Type T and gives proposition-/
 (t: T)
 (a: ∀ (x: T), P x) /-assume that for any object of Type T has property P, this is a proof-/
 
-- Now want proof that little t has property P
-- Does t have property P? Yes, because every object of type T has property P, and t is of type T.
 
-- Elimination rule: allows you to make a statement of a specific object of a particular type by assuming somethiing is true of an arbitrary value of that type
 
 
example: P t := a t
#check a t
 
/- type of a t (function applied to a value) is P t (t has property P), result of function is using elimination rule of for all
by applying proof of for all to a specific object to a proof of a t-/
 
/- a t is a value of this type P t, P is a predicate (this whole thing is a proposition)-/
 
end ForAll
 
/-
AND & →
 
-/
 
axioms (PQ : Prop)
 
/-
Want a proof of P ∧ Q
Main takeaway:
If P ∧ Q is true, I'm saying that P is true and Q is true
If P implies q is true, I'm saying IF P is true THEN Q is true
-/
