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

/- Ordering Relations

**Ordering**

How do we define ordering? 

An ordering is any relation in which 

(1) every object a is related to itself 
(think "less then or equal" to), and 

(2) if an object a is "less than or equal to" 
an object b, and b is less than or equal to c, 
then a is "less than or equal to c", and 

(3) crucially, if a is "less than or equal
to b" then the only way b can also be "less than
or equal to a is if and and b are in fact equal."
It's the anti_symmetry that prevents the case in
which you have both a ≺ b and b ≺ a where a ≠ b.

def ordering := 
  reflexive r ∧ transitive r ∧ anti_symmetric r

**Other Types of Ordering Relations**

I apologize for no explicit definitions LMAO, I'M TIRED!!!

def partial_order :=    ordering r ∧ ¬strongly_connected r
def total_order :=      ordering r ∧ strongly_connected r
def strict_ordering :=  asymmetric r ∧ transitive r
def well_order := total_order r ∧ (∀ (s : set β),       -- for every
                                    ∃ (b : β), b ∈ s →  -- non-empty set s
                                      ∃ (b : β),        -- there is an element
                                        b ∈ s ∧         -- in s
                                          ∀ b' : β,     -- smaller than every other element in s 
                                            b' ∈ s →     
                                            b ≺ b')  

**Focus on Well-Order**       

a well order, aka wellorder, wellordering.
It's a combination of a total order (like ≤ but not
⊆) and this property that in any set of values there
is always a least element.

The nats are well ordered under ≤. Intuitively, every
possible set of natural numbers (even an infinite set)
will have a least element. The very least element of 
all is 0, so no matter what set one picks, it will have
either zero or some direct or indirect successor of 0
as its least element.

This concept is important in enabling one to prove
that recursive functions are well founded: that no
matter what finite input they are given they will
stop running after some finite number of steps: i.e.,
they won't call themselves recursively without end.

The idea will be to show that each recursive call 
that a function makes is given an argument value 
that is "smaller" than the one that the function
received in the first place. As long as each time
an argument from a well ordered set is passed it 
is smaller than the one that was received, then in
some finite number of recursive calls, a "least"
argument value will be encountered for which no
yet "smaller" value exits.
-/

/- Specific Terms and Concepts for Relations

**Domain and Codomain**

We will call the set of all α values the "domain"
of the relation r, and we will call the set of all 
β values the "codomain" of r.

def dom (r : α → β → Prop) : set α := { a : α | true } 
def codom (r : α → β → Prop) : set β := { b : β | true }

**Domain of Definition and Codomain**

-- subset of doman and codomain respectively
def dom_of_def (r : α → β → Prop) : set α := { a : α | ∃ b, r a b } -- set of alpha values for which there's some b so that the given alpha value is related to that b in the codomain
def range (r : α → β → Prop) : set β := { b : β | ∃ a , r a b  } 

**Restriction of a Relation**

It will often be useful to consider the
subrelation obtained by restricting the
domain of a relation to elements of a 
set, s. 

If a relation relates three cats, c1, c2, 
and c3, to their ages, say a1, a2 and a3,
respectively, then restricting the domain
of r to the set, s = {c1, c3}, would give
the relation associating c1 and c3 with
corresponding ages, but there would be no
(c2, a2) pair in the restricted relation
because c2 ∉ s.

def dom_res 
  (r : α → β → Prop) 
  (s : set α) : 
  α → β → Prop := 
λ a b, a ∈ s ∧ r a b   

def ran_res 
  (r : α → β → Prop) 
  (s : set β) : 
  α → β → Prop := 
λ a b, b ∈ s ∧ r a b     -- homework

-/

-- circle relation gives back -1 and 1 if a = 0
-- domain restriction gives me the pairs (0, 1) and (0, -1)
-- if i apply relation r to a i get back set β 
-- set of beta values for which a is related to b
def image_val (a : α) : set β :=
{ b : β | a ≺ b } 

-- image of a set, s, under r
-- get back a set of beta values for which there is some 
-- alpha value in s such that r is related to a and b
def image_set (s : set α) : set β :=
{ b : β | ∃ a : α, a ∈ s ∧ a ≺ b }

/-
**Inverse**

-- inverse of r
def inverse : β → α → Prop :=
λ (b : β) (a : α), r a b

**Composition**

Takes two relations as arguments and glues them
together into a new end-to-end relation: the
*composition* of s with r. 

The result of applying this relation to an (a : α) 
is the (c : γ) that is obtained by applying the 
relation s to the result of applying the relation 
r to a. We can thus call the resulting relation "s after r."

def composition (s : β → γ → Prop) (r : α → β → Prop):=
  λ a c, (∃ b, s b c ∧ r a b) -- names a new binary relation
  -- have a pair alpha or a,c whenever there's some b in the middle
  -- r on the left takes a to b and relation in middle takes it to c on the right

example : 

i : id → name
s : id → salary

x : name → salary --[Goal]

How do we find the composition then?

i inverse : name → id -- find the inverse
s : id → salary

-/

/- Single Valued Binary Relation

def single_valued := 
  ∀ {x : α} {y z : β}, r x y → r x z → y = z

-/