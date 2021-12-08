/- Existential Quantification -/

/- Exists Intro

Introduction Rule : Takes two arguments: a witness value, w,
                    and a proof that witness satisfies the 
                    predicate. 

-/

def ev (n : ℕ) : Prop := n % 2 = 0

example : ∃ (n: ℕ), ev n :=
begin
  apply exists.intro 4 _, 
  -- notice how the value of the parameter is incorporated into the final 
  --proposition, that that value has the required property
  unfold ev, 
  exact rfl,
end

example : ∃ (n : ℕ), ev n := 
  ⟨ 4, rfl ⟩  -- notation

/- Exists Elimination

Main question: How can we *use* a proof of ∃ x, P x

If you have a proof, ex, of ∃ (x : X), P x, you can apply
exists.elim to ex, and (after a few more simple maneuvers)
have yourself a specific value, (w : X) and a proof that w 
satisfies P, i.e., (pf : P w)

-/

example : 
  (exists (b : bool), b && tt = ff) → 
  (∃ (b : bool), true) :=
begin
 assume h,              -- assume premise
 cases h with w pf,     -- eliminate exists
 apply exists.intro w,  -- introduce exists
 trivial,               -- the rest is easy
end


axioms 
  (Ball : Type)           -- There are balls
  (Green : Ball → Prop)   -- a Ball can be Green
  (Red : Ball → Prop)     -- a Ball can be Red 
  (b1 b2 : Ball)          -- b1 and b2 are balls
  (b1r : Red b1)          -- b1 is red
  (b1g : Green b1)        -- b1 is green
  (b2r : Red b2)          -- b2 is red


/-
Translate the propositions into English, then
prove them formally.
If there's a Ball that's Red and Green then 
there is a ball that's Red.
-/
example : 
  (∃ (b : Ball), Red b ∧ Green b) → 
  (∃ (b : Ball), Red b) :=
begin
  assume h,               -- assume there's a red and green ball (assume premise)
  cases h with b rg,      -- get a name, b, for the ball and a proof about b
  apply exists.intro b _,   -- use b as a witness to the proposition to be proved
  exact rg.left,          -- the proof it's red is part of that it's red and green
end 

/-
If there's a ball, b, that's red or green
then there's a ball, b, that greed or red.
-/
example : 
  (∃ (b : Ball), Red b ∨ Green b) → 
  (∃ (b : Ball), Green b ∨ Red b) :=
begin
  assume h,             -- there's ball that's red or green
  cases h with w pf,    -- name it w with pf a proof of Red w ∨ Green w
  apply exists.intro w, -- use w as witness, need proof of Green w ∨ Red d
  cases pf,             -- basically proof of X ∨ Y → Y ∨ X at this point
  exact or.inr pf,
  exact or.inl pf,
end 

/-
How about this one? Translate it into Enlish. Do
you believe it?
-/
-- if there's a ball that's red or green, then there's a ball that's red
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
  _ -- there are two cases for the disjunction, and we have no proof that when the ball is green, it's red, so it's not provable
end 

/-
Social Networks
-/

axioms
  (Person : Type)
  (Nice : Person → Prop) -- given a person, that person is nice
  (Likes : Person → Person → Prop) -- function that takes in two people and returns a proposition that the first person likes the second person

/-
What does this say, in English? It is true?
-/
example : 
  -- If there's a person, p1, who everyone likes,
  -- there exists a single person such that for all people, a person p2 (every person) likes p1
  (∃ (p1 : Person), ∀ (p2 : Person), Likes p2 p1) → 
  -- then everyone likes someone
  -- for every person, there exists a person that they like
  (∀ (e : Person), ∃ (s : Person), Likes e s) :=
begin
  assume h, -- premise is a giant exists statement whereas right side of implication is a giant for all statement
  cases h with p pf, -- pf : particular proposition applies to particular person p
  assume e,
  apply exists.intro p,
  exact (pf e),
end
