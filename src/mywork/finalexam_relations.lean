/- Relations -/

/- Shifting Gears from Sets

If a one-place predicate can represent a set of
individual values, a two-place predicate can 
represent a set of pairs of values

A three-place predicate can represent a set of 
3-tuples of values. We call such sets *relations*

Here's an example: consider the set of 
pairs of natural numbers, where in each
pair the second number is exactly one more
than the first number, and where the first
numbers are 0, 1, and 2. The set of pairs 
that satisfies this specifications is 
{ (0, 1), (1, 2), (2, 3) }.

The idea that you should now have in mind
is that we can represent a "binary relation
on α ⨯ β", which mathematically is a set of
α-β pairs, as a two-place predicate. We can
then *verify* that any given pair is in the
relation (if it is) by producing a proof of
that fact.

Notice how we have defined a binary relation as
a set of α-β pairs that is made up by a two-place
predicate. Does that sound familiar? It does! It
sounds like the relation was constructed by a two
place predicate on the *power set* of α and β sets. 

Connections, people! Connections!

How has Professor Sullivan defined it in lecture 20?

  Let's now visualize the set of all pairs 
  of type ℕ ⨯ ℕ. Again, ℕ ⨯ ℕ is a type. It
  is the type of *pairs*, such as (p.1, p.2),
  where each of p.1 and p.2 are of type ℕ. 

  Just think of a 2-D table, with natural 
  numbers going up from zero across the top 
  and the same down the left side. The pairs
  correspond to the cells where the rows and
  columns intersect in the table. Eventually
  every possible pair appears in the table. 

  A relation is a *subset* of all such pairs,
  namely all and only those pairs that satisfy
  the membership predicate for the relation:
  just as with sets! In mathematical writing
  we will therefore often see definitions 
  like this:

        Let R ⊆ ℕ × ℕ be a binary relation such 
        that ∀ (n m ∈ ℕ), (m, n) ∈ R ↔ n = m + 1.
        Note that we're using "ordered pair notation"
        to represent pairs, i.e., values in ℕ × ℕ 
        in this case. Lean supports these standard
        notations. 

-/

/- Properties of Relations

**Reflexivity**

"a relation, ≺, is reflexive if 
it relates every value, x, to itself.""

def reflexive := ∀ x, x ≺ x

If we fill in the implicit arguments and unfold
the notation, we get a fuller picture on how to
understand this relation:

def reflexive' 
  {β : Type} 
  {r : β → β → Prop} := 
  ∀ x, r x  x

These definitions are parameterized by a
type, β, and a (binary) relation, r, on β
(r ⊆ β × β), and the yield *propositions*,
that every value of a type β is related to
itself by r.

*See the proof below for the reflexivity relation*

**Symmetric**

def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

**Transitive**

def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

-/

-- equality relation on natural numbers is reflexive

theorem eq_is_refl : reflexive (@eq nat) := -- eq is the equality predicate
begin
  -- expand expression: @reflexive nat (@eq nat) :=
  unfold reflexive, -- valuable to do bc it shows logical definition of set theory concept
  assume x,
  exact rfl,

end
/-
English Proof : 
    Theorem: Equality is reflexive.
    Proof. Unfolding the definition of reflexive,
    what we are to show is ∀ x, x = x. To prove it,
    assume x is an arbitrary value and show x = x.
    That's true by (application of) the introduction
    rule for equality (to x). QED.
-/

/-
Exercise: prove that = is symmetric. And
answer the question, is ≤ symmetric, and
give a brief defense of your answer.
-/

theorem eq_is_symm : symmetric (@eq nat) :=
begin
  unfold symmetric,
  assume x y,
  assume h,
  rw h,
end

/-
English Proof : 

    Theorem: Equality is symmetric. Proof. Unfolding
    the definnition of symmetric, what we are to show
    is ∀ (x y: α), x = y → y = x. To prove it, we must
    assume x and y are arbitrary values of type α and 
    show that  x = y → y = x. To do so, assume the premise
    and apply the substitutability of equality axiom by
    rewriting the proosition. QED.

-/

example : transitive (@eq nat) :=
begin
  unfold transitive,
  assume x y z h1 h2,
  exact eq.trans h1 h2,
end

/- Other Relations

**Equivalence**

A relation is said to be an equivalence relation if 
it is reflexive, symmetric, and transitive. 

def equivalence := reflexive r ∧ symmetric r ∧ transitive r

**Empty Relation**

def empty_relation := λ a₁ a₂ : α, false

**Full Relation**

def full_relation := λ a₁ a₂ : α, true

**Identity Relation**

def id_relation :=  λ a₁ a₂ : α, a₁ = a₂ 

**Subrelation**

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

**Total Relation**

def total := ∀ x y, x ≺ y ∨ y ≺ x

**Anti-Reflexive**

def anti_reflexive := ∀ x, ¬ x ≺ x

**Irreflexive**

def irreflexive := anti_reflexive r

**Anti-Symmetric**

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

**Asymmetric**

def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x

-/

/- Closure Operations on Relations

Given a relation, r, the reflexive, symmetric, or
transitive closure of r is the smallest relation that
(1) contains r, and (2) contains any additional pairs
needed to make the resulting relation reflexive, or
symmetric, or transitive, respectively. 

Reflexive and Symmetric Closures:

def reflexive_closure := λ (a b : β), (r a b) ∨ (a = b)
def symmetric_closure := λ (a b : β), (r a b) ∨ (r b a)

A wonderful resource to understand this is:

https://www.youtube.com/watch?v=VSq7O10IllI

Transitive Closure:


What set of pairs is this? Well, (1) it contains every
pair in r, and (2) if (a,b) is in (tc r) and if (b, c)
is in (tc r), then (a, c) must also be in r. The way we
will say this formally uses what we call an inductive
definition. Inductive definitions allow for "bigger"
things to be built whenever there are smaller things
of the right kind.

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

A wonderful resource to understand this is:

https://www.youtube.com/watch?v=jnw02y63I-o

-/

/- Universal Quantification Over an Empty Set is True

Here's a way to think about it. Suppose we had 
a set with two balls in it: { b1, b2 }. To show that 
every ball is red, we could use case analysis: break
the task into two cases: show that b1 is red, AND 
show that all balls in the remaining set, { b2 }, are
red. 

To prove the latter, we'd show that b2 is red, and 
that all balls in the remaining set, {}, are red. 
So we have that all balls are red if (red b1) ∧ 
(red b2) ∧ "all balls in {} are red". 

When applied to zero arguments, the answer 
really has to be true, otherwise this operation would
*always* produce propositions that are ultimately false.  

-/

axioms (Ball : Type) (red : Ball → Prop)
def empty_bucket := ({} : set Ball)

lemma  allBallsInEmptyBucketAreRed : 
  ∀ (b : Ball), b ∈ empty_bucket → red b := 
begin
  assume b h,
  cases h,             -- finish off this proof
end

