import data.set

/- Sets -/

/- Operations on Sets

**Membership**

(s : set T) (v : T) : is v in s?

This is defined by a predicate : one that's satisfied by
all and only the element values considered to be "in" s

When we talk about sets, it's interesting that we refer to
values being "in" a set. Now that we've defined set membership
as being defined by their predicate, we can understand that the
action of being "in" a set is simply just a matter of satisfying 
a predicate. Therefore, v ∈ pred can also be rewritten as 
pred v (the predicate applied to v). 

Moving, on, let's write in English how we can define even_nat_set
in english. 

def ev (n : ℕ) : Prop := n % 2 = 0

def even_nat_set : set ℕ := { n : ℕ | ev n }

We define even_nat_set to be (bound to) a value of type, 
set ℕ, representing a set of natural numbers, namely the
set of values, n, of type nat, such that ev n (is true). 

In other words, we define even_nat_set as the set of natural 
numbers that satisfy the (ev _) predicate.

This means that the set can also be defined as ℕ → Prop!

def mem (a : α) (s : set α) :=
s a

**Empty Set**

The empty set of values of a given type T is the set
containing no elements. It must thus be defined by a
one-place predicate that is not satisfied by *any* 
values of the element type.

The proposition that must be satisfied to be in the empty 
set is the false proposition, as no objects of any type for 
which this proposition is true. 

**Complete Set**

The complete set of values of a given type T is the set
containing all elements. So, if the proposition for the empty
set is false, what must the proposition be for the complete
set? 

True!

**Complement**

The complement of a set s is the set of all values in the 
"universe of discourse" that are not in s. 

We can write this as :

def compl_nat (s : set ℕ ) : set ℕ :=
{a | a ∉ s}

**Subset**

Given two sets, s1 and s2, of objects of some type T, we say that
s1 is a subset of s2, written as s1 ⊆ s2, if every element
in s1 is in s2

We say that s1 is a proper subset of s2, written as s1 ⊂ s2, if every
value in s1 is in s2 and some value in s2 is not in s1

def subset (s₁ s₂ : set α) :=
∀ ⦃a : α⦄, a ∈ s₁ → a ∈ s₂ 

**Difference**

The difference between sets s1 and s2 written s1 \ s2, is the 
set of values that are in s1 but not in s2. 

In other words, the set s1 with the elements in s2 "taken away"

evens \ ods -- evens
evens \ evens -- empty
evens \ empte -- evens
evens \ complete -- empty

def diff (s t : set α) : set α :=
{ v | v ∈ s ∧ v ∉ t}

**Union**

The union of two sets, s1 and s2, written as s1 ∪ s2, is the set
of elements that are in s1 or s2

def union (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∨ a ∈ s₂}

**Intersection**

The intersection of two sets, s1 and s2, written as s1 ∩ s2, is the
set of elements that are in s1 and s2

def inter (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∧ a ∈ s₂}

**Product**

THe product of two sets, (s1: set T) and (s2: set V) is the set of all
pairs (t, v), where t ∈ s1 and v ∈ s2. 

Another way to think of it is all the ordered pairs. 

def powerset (s : set α) : set (set α) :=
{t | t ⊆ s}

**Power**

The powerset of aset, s, written 𝒫 s, is the set of all subsets of
s. This makes the powerset a "set of sets". 

**Image**

The image of a set, s, under a function f, is the set of values obtained by
applying f to every value in s

Think casting a flashlight over a set? Which values in the set
do you see with this specific flashlight? That's the main idea. 

def image (f : α → β) (s : set α) : set β :=
{b | ∃ a, a ∈ s ∧ f a = b} -- and means for which (for which f applied to a equals b)
-/

/- each definition formalized -/

def ev (n : ℕ) : Prop := n % 2 = 0
def od (n : ℕ) : Prop := ¬ ev n


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

/- Set Equality

When we look at the concept of set equality, what do we mean?

To show that two sets are equal, L = X, we need to show that a value
is in L if and only if it's in X, which is the same as showing 
L ⊆ X ∧ X ⊆ L. 

Takeaway : To prove two sets equal, you can prove that each is a subset
of the other. 

There is a more clear way to express this conjunction, though. When we expand
this definition, we get:
  ∀ x, 
    (x ∈ L → x ∈ X) ∧
    (x ∈ X → x ∈ L)
which we can also write as
  ∀ x, x ∈ L ↔ x ∈ X.

This means that to prove L = X it will suffice us to prove that for any element, the
if the element is a subset of L and it's a subset of X, then L = X. 

The way we can go about formalizing this is using the set extensionality axiom in Lean. 
It just says that if we prove ∀ x, x ∈ L ↔ x ∈ X then we can, by applying the axiom, 
deduce that L = X.

-/

-- sample proof: if L is a subset of X then the intersection of L and X is L

example : ∀ {α : Type} (L X : set α), L ⊆ X → ((L ∩ X) = L) := 
begin
  intros α L X h,
  apply set.ext _,  -- reduce = to ↔ by set extensionality
  /- 
  That's the whole proof as long as we can fill in the _
  That's what the rest of this proof script then does. 
  Notice again how "applying an implication theorem" 
  can be used to reduce a current proof goal to goals 
  the satisfaction of which "will suffice" to enable
  construction of the proof that's needed.
  -/
  assume x,
  split,
  -- forward
  assume h,
  /- 
  Remember, h is a proof of a conjunction
  so "cases h" really does and elimination 
  giving us the left and right subproofs as
  the arguments that must have been given as
  arguments to the and.intro that must have
  been used to construct such a proof in 
  the first place.
  -/
  cases h with l r,
  exact l,
  -- quiz: would "exact h.left" have worked?
  -- predict the answer before checking

  -- backward
  assume k,
  have r := h k,
  apply and.intro k r,
  /-
  So this last "proof move" will take a little
  time to think about. Look at the goal and think
  for yourself what you really need to prove here.
  Go back to the definitions! x ∈ L ∩ X really 
  just means L x ∧ X x. Does this help you to see
  why and.intro is required here, and what each 
  of the terms in the preceding expression must
  means?
  -/
end 

