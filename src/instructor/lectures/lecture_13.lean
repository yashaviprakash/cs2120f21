/-
UPDATE: Test distributed after class on 
Monday. Monday will be a review day. The
test is due back Wednesday before class.
In class Wednesday we will have at least
a short quiz to sanity check what you will
have submitted for the test. We reserve the
right to do follow-on in-person testing if
the results indicate a possible problem.
-/

/-
REVIEW: Last time we focused on the question, 
how do we construct a proof of ∃ x, P x.  
(a proposition that there exists some x that satisifes this predicate P or exists some x with property P)
Pick value for x, and show that that value has particular property x
witness is particular value for x

To do so, you apply the introduction rule for
exists. It's called exists.intro in Lean. You
apply it to two arguments: a specific value, w,
in place of x, and a proof that that particular
w satisfies the predicate, P, i.e., that there 
is a proof of the proposition, P w. 

In other words, you can think of a proof of
∃ x, P x, as a pair, ⟨w, pf ⟩, where w is a
witness and pf is a proof of P w.
-/

/-
Today we'll delve deeper into the mysteries
of exists elimination, or how you can *use*
a proof of ∃ x, P x.

Here's the idea: If you have a proof, ex, of
of ∃ (x : X), P x, you can apply exists.elim
to ex, and (after a few more simple maneuvers)
have yourself a specific value, (w : X), and 
a proof that w satisfies P, i.e., (pf : P w). 
The idea is that you can then uses the values
in your subsequent proof steps.

exists elimination rule takes you to having
two things a particular value w and a corresponding proof

Why does this rule make sense? Consider a very
simple example. If I tell you there exists some
green ball, you can say, "well, call it b," and
give that we know it's green, we also know that
it satisfies the isGreen _ predicate, so we can
also assume we have a proof of (isGreen b). In
this example, b is a witness to the fact that
some object satisfies the predicate. The proof
then shows for sure that that is so.

-/

-- exists some boolean where the proposition results in false
example : ∃ (b : bool), b && tt = ff :=
begin
  apply exists.intro ff,
  exact rfl, -- infers type of value you're looking at and specific value in lean
end

-- if there exists a boolean b that satisifes the constraint
-- then there exists a bool b that satisfies the true predicate
example : 
  (exists (b : bool), b && tt = ff) → 
  (∃ (b : bool), true) :=
begin
  assume h,
  cases h with w pf, -- what comes out of it is the names for the two components of that pair
  apply exists.intro w, -- show that w has the property that you care about
  trivial, -- tries a couple of simple things like applying eq.refl and some other things
end


/-
Let's set up some assumptions so that 
we can explore their consequences when
it comes to existentially quantified
propositions.
-/

/-
Beachballs! What could be more fun
-/

axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green (green as properties of balls)
  (Red : Ball → Prop)     -- a Ball can be Red (red as properties of balls)
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red (I have a proof and therefore it must be true that b1 is red)
  (b1g : Green b1)        -- b1 is green (same as above)
  (b2r : Red b2)          -- b2 is red (same as above)


-- if there exists a ball b that is red and green then there exists a ball that is red
-- prof way of saying it : if there is a ball that is red and green then it is red
example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with b rg,
  apply exists.intro b, -- applying elimination rule is what makes it possible to apply introduction rule
  exact rg.left, 
end 

-- if there is a ball that is red or green then there is a ball that is green or red
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,
  cases h with b rg,
  apply exists.intro b,
  -- or is commutative
  --apply or.elim rg,
  cases rg,
  

end 

-- just because you know something red or green it doesn't mean that it's red
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,
  cases h with w pf,
  cases pf,
  apply exists.intro w,
  assumption,
  apply exists.intro w,
  -- stuck
  
end 

example : 
    (∃ (b : Ball), Red b) → 
    (∃ (b : Ball), Red b ∨ Green b) := 
begin
  assume h,

end 

/-
Social Networks
-/

axioms 
  (Person : Type)
  (Nice : Person → Prop)
  (Likes : Person → Person → Prop)

-- if there is a person p1 such that every person p2 likes p1
-- then everybody likes somebody
example : 
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h,
  assume e,
  cases h with p pf,
  -- have our person p1
  apply exists.intro p,
  exact (pf e),
end

/-
Write formal expressions for each of the following
English language sentences.
-/

-- Everyone likes him or herself

-- Someone doesn't like him or herself

-- There is someone likes someone else

-- No one likes anyone who dislikes them

-- Everyone likes anyone who is nice

-- No one likes anyone who is not nice


/-
If everyone who's nice likes someone, then
there is someone whom everyone who is nice 
likes.
-/