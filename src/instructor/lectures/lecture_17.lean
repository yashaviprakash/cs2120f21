import data.set

/-
We formally define two predicates on
natural numbers.
-/
def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n -- even is not true


/-
We now formally represent some sets.
Bear in mind that we represent a set
as a predicate, applicable to a value
of the member type, and "reducing to"
a proposition, possibly "about" that
value.
-/

/-
SET NOTATIONS
-/


/-
Display notation. We can represent
a finite set of values by listing them,
comma-separated, within curly braces.
-/
def one_to_four : set ℕ := { 1, 2, 3, 4 }
def some_strings : set string := {"Hello", "World!"}

/-
Set comprehension notation
-/

def empte : set ℕ := { n : ℕ | false } -- no natural numbers for which this proposition is true

def complete : set ℕ := { n : ℕ | true } -- all natural numbers

def evens : set ℕ := { n : ℕ | ev n } -- predicate for which all possible values for n are even and true

def ods : set ℕ := { n : ℕ | ¬ (ev n) } 

def evens_union_ods : set ℕ := { n : ℕ | ev n ∨ od n } -- set union: disjunction of the membership predicates

def evens_intersect_ods : set ℕ  := { n : ℕ | ev n ∧ od n }

def evens_complement : set ℕ := { n : ℕ | od n } -- or ¬ (ev n)

def ods_complement : set ℕ := { n : ℕ | ev n } -- or ¬ (od n)

def evens_intersect_empty : set ℕ := {n : ℕ | ev n ∧ false } -- n ∈ (in) empty set also this will basically be the empty set

def evens_intersect_complete : set ℕ := {n : ℕ | ev n }

def evens_union_empty : set ℕ := {n : ℕ | ev n ∨ n ∈ empte} -- this reduces to even

def evens_union_complete : set ℕ := {n : ℕ | ev n ∨ n ∈ complete} -- this reduces to true
-- If T is any type and P is any predicate on T
axioms (T : Type) (P : T → Prop)

-- The this is the set of T values that satisfy P
#check { t : T | P t}



-- fill in additional interesting combinations


/-
MORE SET THEORY NOTATIONS
-/

/- empty set

Sometimes people use ∅ to represent the empty set
-/

#check ( ∅ : set ℕ )

/- set membership (an example is ev n)

A (membership) predicate applied to a value
yields a proposition: one that is true for
values in the set. The ∈ notation is just 
a shorthand for application of a membership
predicate to a value, but it gives a sense
of "inclusion" of a value in a collection
of values. (ℕ → Prop)
of the "inclusion" of a value in a collection
of values.
-/
#check evens 0    -- predicate applied to value
#check 0 ∈ evens  -- equivalent proposition
#check 1 ∈ evens  -- another proposition

/- set difference

The difference between sets s1 and s2, 
written s1 \ s2, is the set of values
that are in s1 but not in s2. You can
think of this as the set s1 with the
elements in s2 "taken away." Sometimes
people use subtraction notation for
set difference: s1 - s2.
-/
#check evens \ ods -- evens
#check evens \ evens -- empty
#check evens \ empte -- evens
#check evens \ complete -- empty


/- complement

The complement of a set s is the set of all
values in the "universe of discourse" (in Lean,
a type) that are not in s. Lean doesn't provide
a notation, so we have to define it ourselves.
Here we define compl as the complement of a 
set of natural numbers.
-/

def compl_nat (s : set ℕ ) : set ℕ :=
{a | a ∉ s}

#check compl_nat evens

/- union
The union of two sets, s1 and s2, written
as s1 ∪ s2, is the set of elements that are 
in s1 or s2. 
-/

#check ods ∪ complete
#check ods ∪ empte
#check ods ∪ evens


/- intersection 

The intersection of two sets, s1 and s2, written
as s1 ∩ s2, is the set of elements that are in s1
and in s2.
-/

#check ods ∩ empte
#check evens ∩ complete
#check ods ∩ evens

/- product 

The product of two sets, (s1 : set T) and
(s2 : set V) is the set of all pairs (t, v),
where t ∈ s1 and v ∈ t2. People sometimes
use × to represent the set product operation.
In Lean we have to define it ourselves.
-/

def prodset {T V : Type} (s1 : set T) (s2 : set V) := 
  { pr : T × V | pr.1 ∈ s1 ∧ pr.2 ∈ s2 }

#check prodset evens empte
#check prodset evens ods 


/- subset

Given two sets, s1 and s2, of objects of some type 
T, we say that s1 is a subset of s2, written s1 ⊆ s2,
if every element in s1 is in s2. We say that s1 is a
proper subset of s2, written s1 ⊂ s2, if every value
in s1 is in s2 and some value in s2 is not in s1. 
-/

#check evens ⊆ evens -- even is a subset of even
#check evens ⊂ evens
#check evens ⊆ complete
#check evens ⊂ complete
#check evens ⊂ empte
#check ∀ (s : set ℕ), empte ⊆ s


/- powerset

The powerset of a set, s, written 𝒫 s, is 
the set of all subsets of s. This makes the 
powerset a "set of sets". 
-/

#check (𝒫 { 1, 2, 3} : set (set ℕ))
#check 𝒫 evens


/-
Now let's state and prove some theorems.
-/


example : ∀ (n : ℕ), evens_union_ods n ↔ complete n := 
begin
  assume n,
  split,
  -- forward
  unfold evens_union_ods complete,
  assume h,
  
end


example : ∀ (n : ℕ), (n ∈ evens_union_ods) ↔ (n ∈ complete) := 
_


/-
Now we are in a position to see formal 
definitions of all of the preceding set
theory concepts.
-/

def pSet  : set nat := { n : ℕ | P n}
def qSet  : set nat := { n : ℕ | Q n}

#reduce 0 ∈ pSet
#reduce pSet ∪ qSet
#reduce pSet ∩ qSet
#reduce pSet \ qSet
#reduce pSet ⊆ qSet
#reduce 𝒫 pSet      -- harder to decipher


/-
Now that we understand these operations and
their corresponding notations in set theory,
we can start to state and prove theorems!
-/

/-
Personal Class Notes:

* a set is defined as a membership predicate

Two different notations when talking about sets: 
* Display Notation (want to represent a small set of values
where you can enumerate all values in a set)
* Comprehension Notation (we're defining the set of values
n of type ℕ such that -- place predicate here -- )

the product of two sets is a set of pairs
-/

-- Display notation
def one_to_four : set ℕ := {1, 2, 3, 4}

-- set of natural numbers N such that and predicate for values n of that set
-- excludes every natural number for the set
def emptee : set ℕ := {n: ℕ | false }

