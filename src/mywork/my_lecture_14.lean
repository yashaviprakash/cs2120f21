/-
Challenge #1 : Set up the domain model and then
express the proposition about it. In this case, 
the domain model includes people and a binary likes
relation "over" people.
-/

/- uninhabited type: if type has no value (if false)-/

axioms 
  (Person: Type)
  (Likes : Person → Person → Prop ) -- property of pairs, set of pairs

/- assuming Likes is a binary relation, and what we're
doing is using a two place predicate to represent a binary
relation-/

-- if this then that then vice versa
/- if it's not the case that every person p likes themselves, then
it's the case that there exists some person p that doesn't like themsevles, 
and vice versa

if there exists a person that doesn't like themselves then it's not the
case that every person does not like themselves-/
example : ¬ (∀ p: Person, Likes p p) ↔ (∃ p : Person, ¬ Likes p p) :=
begin 
  apply iff.intro _ _,
  -- forward
    assume h,
    -- logical sequence consistency (h and goal)
    -- in this case, it checks out
    have em := classical.em (∃ (p : Person), ¬Likes p p), -- assume that the goal is either true or false
    -- if you assume that it's not true, you have to ask where that gets us
    cases em,
      -- case 1 : either there is a person that dislikes themselves
      assumption,
      -- case 2 : or there doesn't exist a person that dislikes themselves
      -- propose new fact, proof to be constructed int his contradiction
      have contra : ∀ (p: Person), Likes p p := _,
      -- prove current goal using proposed fact
      contradiction,
      -- still have to prove supposition
      assume p, -- for all!! you have to first assume the arbitrary but specific proposition!
      have em_2 := classical.em (Likes p p), -- can do case analysis on any proposition
      -- this time trying to do case analysis on whether it's true or false that p likes p
      cases em_2,
      -- first case
      assumption,
      -- second case contradicts with f
      -- what happens when you have a witness and proof you can use exists.intro
      -- all you have is a property of a person not liking themselves, you have to show that
      -- there exists some person where this is true:
      have a : ∃ (p: Person), ¬ Likes p p := exists.intro p em_2,
      contradiction, -- immediate contradiction with em
  -- backward
    assume h,
    cases h with p pf,
    assume p2,
    have contra := p2 p,
    contradiction,
end