/-
Negation
-/

/-Given a proposition, P, we can form a new
proposition, usually written as ¬ P, which we 
pronounce as "not P", and which we define in
such as way as to assert that P is not true-/

/-
So what does it mean when we say that *it is
true that P is not true*

It means you have to have a proof of not P
-/

/-
First, if ¬P is true, there should be a proof
of it. Second what that proof should show is
that *there can be no proof of P*

If a proposition is false, it means that there
are no proofs of it. If you say that not P is true
you can say that P has no proofs.
-/

/-
So the way we're going to say ¬P is true is to say
if P were true then something that is completely
impossible would happen. Because the impossible
cannot happen, therefore there msut be no proof of 
P. 
-/

/-
What we're gongi take as "the impossible thing"
is that there is a proof of false. Have defined 
false to be exactly a proposition with no proofs
(otherwise it'd be true), so to have ea proof of
false is an impossibility.
-/

/-
If P implies false, if there is a proof of P then 
can derive a proof of false, what can you say about P?
It shouldn't have a proof. To prove that P implies
false, you've proved that P has no proofs. To say that
P is false is the same as saying that P implies false, if
it's true that P implies false, it tells you that P has 
no proof.
-/

/-Can you prove that false implies false?-/
example : false → false :=
begin 
  assume f,
  exact f,
end

/-Now we have proven that false implies true
If you have true on the right-hand side of implication,
you can ignore left and apply true.intro-/
example : false → true :=
begin
  assume f,
  exact true.intro,
end

example : true → true :=
begin
  assume t,
  exact true.intro,
end

example : true → false :=
begin
  assume t,
  /- no proof, this proposition is false-/
  --stuck
end

/-
It's this analysis that leads to the definition
of ¬ P. For any propoosition P, we define ¬ P to
be the proposition, P → false. What this means
is that if there is a proof of P → false, then 
you can conclude (by definition) ¬ P. This is the
introduction rule for ¬ 

*If your goal is not P, that means P immplies
false. The same strategy applies for any implication
Assume p is true, and show that that leads to a contradiciton
to a posibility for it to be false.*
-/

def x (P: Prop):= ¬ P
#check not -- see definition in Lean Library

/-
So how do you prove P → false? It's just like any other
implication: assume that P is true adn show that
with that you can construct a proof of false.
-/

/-
Example. Prove ¬ 0 = 1
-/
example : false :=
begin
end

/- not false means that false implies false-/
example : ¬ false :=
begin
  assume f,
  exact f,
end

/- if you've made an assumption of something that's
false, you do a case analysis on that proof, and if you do that 
in this case that there will be nothing left to prove-/
example : ¬ (0 = 1) := -- no way to construct this proof
begin
  assume h,
  cases h, 
end

example: false → false :=
begin
  assume f,
  cases f,
end

/- showed elimination rule for false,
if you found yourself in a situation that doesn't
exist that's false elimination-/
example: false → false :=
begin
  assume f,
  exact false.elim f,
end

/- if you assume you're given a proof of false that can return a proposition P-/
theorem false_elim (P: Prop) (f : false) : P :=
begin
  cases f,
end

/-
To undersatnd how to finish off this last
proof, we need to talk more canse anlysis again. 
Remember that we've used it to reason from a 
proof of a disjunction. Suppose we want to know
that P ∨ Q → R
-/

example : ∀ (P Q R : Prop ), P ∨ Q → R :=
begin
    assume P Q R, 
    assume pq,
    -- or elimination
    cases pq, /-case anlysis shows that there were two ways i could've built that proof of P ∨ Q-/
end

example : true → true :=
begin
  assume t, 
  cases t,
end




