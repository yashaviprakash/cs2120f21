
/-
A simple predicate.

introduction rule for exists: need to give a pair (a witness and a proof)

A predicate is a proposition with a parameter
(ev: ℕ → Prop) a proposition that claims that natural number is even
need notion of predicates in mind to show that that makes sense

this predicate is a predicate that defines the set of even numbers
predicated describe properties and properties represent sets

in what sense does this predicate define a set?
answer: it creates a group for which this
predicate might be true for, creates a membership,
in that way a predicate picks out a set
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists

∃ n , ev n (exists on left, and predicate on right)

mean there is some end that satisfies this predicate

there exists some natural number that satisfies the proposition of evenness

what does proof of this look like?

Element : < 4 (witness), a proof that 4 is even> or <4, rfl>

colon Prop means returns a proposition
-/

def pythagorean_triple (a b c: ℕ): Prop := a * a + b * b = c * c

example: ∃ (a b c : ℕ), pythagorean_triple a b c := 
begin

end

example : pythagorean_triple 3 4 5 :=
begin
  unfold pythagorean_triple,
  apply rfl,
end

example : pythagorean_triple 3 4 6 :=
begin
  unfold pythagorean_triple,
  
end

example : exists (n : ℕ), ev n :=
begin

end

example : exists n, ev n := _


example : exists (a b c : ℕ), a*a + b*c = c*c := 
_


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end