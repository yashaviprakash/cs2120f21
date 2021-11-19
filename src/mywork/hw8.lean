import ..instructor.lectures.lecture_26
import data.set


/-
EXERCISE #1: Prove that the inverse of a 
bijective function is a function. Ok, yes, 
we will work this one out for you! But you
should really read and understand it. Then
the rest shouldn't be too bad.
-/

example : bijective r → function (inverse r) :=
begin
  /-
    Assume hypothesis
  -/
  assume r_bij,

  /-
  Unfold definitions and, from definitions,
  deduce all the basic facts we'll have to
  work with.
  -/
  cases r_bij with r_sur r_inj, -- injective and surjective
  cases r_inj with r_tot r_one_to_one, -- dividing injective definition
  cases r_sur with r_tot r_onto, -- dividing surjective definition
  unfold total_function at r_tot, -- unfolding the definition of total
  cases r_tot with r_fun alldef, -- divides the definition of total
  unfold function at r_fun, -- says that a function is single valued
  unfold single_valued at r_fun, -- unfolds single valued
  unfold defined at alldef, -- unfolds the definition of defined

  /-
  What remains to be shown is that the
  inverse of r is function. Expanding 
  the definition of function, that means
  r inverse is single-valued. Let's see. 
  -/
  unfold function,
  unfold single_valued,
  /-
  To show that r inverse (mapping β values
  back to α values) r is single-valued, 
  assume that b is some value of type β 
  (in the codomain of r) and show that if 
  r inverse maps b is mapped to both a1 and 
  a2 then a1 = a2.
  -/
  assume b a1 a2 irba1 irba2,
  /-
  Key insight: (inverse r) b a means r a b. 
  In other words, r b a is in r inverse (it
  contains the pair (b, a)) if and only if 
  (a, b) is in r, i.e., r a b.
  -/
  unfold inverse at irba1 irba2,
  /-
  With those pairs now turned around, by the 
  injectivity of r, we're there!
  -/
  apply r_one_to_one irba1 irba2,
end 

/-
Just to set expectations: The reality is that
I explored numerous ways of writing this proof.
Often a first proof will be confusing, messy,
etc. Most proofs of theorems you see in most
mathematics books are gems, polished in their
presentations by generations of mathematicians.
It took me a little while to get to this proof
script and the sequence of reasoning steps and
intermediate proof states it traverses. 
-/


/- INJECTIVE AND SURJECTIVE *PARTIAL* FUNCTIONS

Okay, we actually are now able to to define just
what is means for a *partial* function to be
injective, surjective, bijective, which is that 
it is so when its domain is restricted to its 
domain of definition, rendering it total (at 
which point the preceding definition applies). 
-/

def injectivep := function r ∧ injective (dom_res r (dom_of_def r))
def surjectivep := function r ∧ surjective (dom_res r (dom_of_def r))
def bijectivep := function r ∧ bijective (dom_res r (dom_of_def r))




-- EXERCISE #2: Prove that the inverse of a bijective function is bijective.
example : bijective r → bijective (inverse r) :=
begin
  assume bij,
  
  /- a bijective function must be surjective and injective-/
  cases bij with r_sur r_inj, -- injective and surjective
  cases r_inj with r_tot r_one_to_one, -- dividing injective definition
  cases r_sur with r_tot r_onto, -- dividing surjective definition

  /- both surjective and injective must be strongly connected, reduce that next-/
  unfold total_function at r_tot, -- unfolding the definition of total
  cases r_tot with r_fun alldef, -- divides the definition of total

  /- unfold what it means to be a function and single valued-/
  unfold function at r_fun, -- says that a function is single valued
  unfold single_valued at r_fun, -- unfolds single valued

  /- unfold defined -/
  unfold defined at alldef, -- unfolds the definition of defined

  /-
  What remains to be shown is that the
  inverse of r is bijective. Expanding 
  the definition of bijective, that means
  r inverse is surjective and injective. 
  -/
  unfold bijective,
  split,

  /-  solve that the inverse of r is surjective -/
  unfold surjective,
  split,
    /- solve that the inverse of r is a total function -/
    unfold total_function function single_valued,
    split,
      /- solve that the inverse of r is a single-valued function-/
      assume x y z invrxy invryx,
      unfold inverse at invrxy invryx,
      apply r_one_to_one invrxy invryx, --using second conjunction in definition of surjective functions
      /- solve that the inverse of r is defined-/
      unfold defined inverse,
      assume a,
      have ex_pf := r_onto a, 
      exact ex_pf,
    /- solve that for every alpha value, there exists a b such that its the inverse of r a b-/
    unfold inverse,
    assume b,
    have ex_pf := alldef b,
    exact ex_pf, 

/- solve that the inverse of r is injective-/
unfold injective,
split,
  /- solve that the inverse of r is a total function -/
  unfold total_function function single_valued,
  split,
    /- solve that the inverse of r is a single_valued function -/
    assume x y z invrxy invrxz,
    unfold inverse at invrxy invrxz,
    apply r_one_to_one invrxy invrxz, -- using second conjunction in definition of injective functions
    /- solve that hte inverse of r is defined -/
    unfold defined inverse,
    assume a,
    have ex_pf := r_onto a,
    exact ex_pf,
  /- solve that the inverse of the function is injective-/
  unfold inverse,
  assume x y z rzx rzy,
  apply r_fun rzx rzy,

end


/-
EXERCISE #3: Prove that the inverse of the inverse of a bijective
function is that function.
-/
example : bijective r → (r = inverse (inverse r)) :=
begin
  assume bij,
  apply rfl,
  
end

/-
EXERCISE  #4: Formally state and prove that every injective function 
has a *function* as an inverse.
-/
example : injective r → function (inverse r) :=
begin
 -- hint: remember recent work
 assume inj,
 
 cases inj with tot injr,

 unfold function single_valued defined inverse,

 assume x y z ryx rzx,

 apply injr ryx rzx,

end


/-
EXERCISE #5. Is bijectivity transitive? In other words, if the
relations, s and r, are both bijective, then is the
composition, s after r, also always bijective? Now
we'll see.
-/

open relations    -- for definition of composition

/-
Check the following proposition. True? prove it for all.
False? Present a counterexample.
-/
def bij_trans (s : β → γ → Prop)  (r : α → β → Prop) :
  bijective r → bijective s → bijective (composition s r) := 
begin 
  assume bijr bijs,

  /- unfold every definition in bijective r-/
  unfold bijective at bijr,
  cases bijr with surrr injrr,
  unfold surjective total_function at surrr,
  unfold injective total_function at injrr,
  cases injrr with fanddr injr,
  cases surrr with fanddr surr,
  cases fanddr with funcr defir,
  unfold defined at defir,
  unfold function single_valued at funcr,
  unfold function single_valued defined at fanddr,

  /- unfold every definition in bijective s-/
  unfold bijective at bijs,
  cases bijs with surrs injrs,
  unfold surjective total_function at surrs,
  unfold injective total_function at injrs,
  cases injrs with fandds injs,
  cases surrs with fandds surs,
  cases fandds with funcs defis,
  unfold defined at defis,
  unfold function single_valued at funcs,
  unfold function single_valued defined at fandds,
  
  /- start solving -/
  unfold bijective surjective injective composition,
  split,
  split,

  unfold total_function function single_valued defined,
  split,

    -- first case
    assume x y z ex1 ex2,
    cases ex1 with w1 pf1,
    cases ex2 with w2 pf2,
    cases pf1 with one two,
    cases pf2 with three four,
    have w_same : w1 = w2 := begin
      apply funcr two four,
    end,
    rw w_same at one,
    apply funcs one three,

    -- second case
    assume a,
    have h1 := defir a,
    cases h1 with w pf,
    have h2 := defis w,
    cases h2 with w2 pf2,
    apply exists.intro w2,
    apply exists.intro w (and.intro pf2 pf),


  assume g,
  have h1 := surs g,
  cases h1 with w pf,
  have h2 := surr w,
  cases h2 with w2 pf2,
  apply exists.intro w2,
  apply exists.intro w (and.intro pf pf2),

  split,

    -- first case
    unfold total_function function single_valued defined,
    split,
      -- subcase one
      assume x y z ex1 ex2,
      cases ex1 with w1 pf1,
      cases ex2 with w2 pf2,
      cases pf1 with one two,
      cases pf2 with three four,
      have w_same : w1 = w2 := begin
        apply funcr two four,
      end,
      rw w_same at one,
      apply funcs one three,
      -- subcase two
      assume a,
      have h1 := defir a,
      cases h1 with w1 pf1,
      have h2 := defis w1,
      cases h2 with w2 pf2,
      apply exists.intro w2,
      apply exists.intro w1 (and.intro pf2 pf1),

  assume x y z ex1 ex2,
  cases ex1 with w1 pf1,
  cases ex2 with w2 pf2,
  cases pf1 with one two,
  cases pf2 with three four,
  have w_same : w1 = w2 := begin 
    apply injs one three,
  end,
  rw w_same at two,
  apply injr two four,

end 

