/- Introduction & Elimination Rules -/

-- definition of introduction rule : produce proofs of *insert here* (how many proofs can we produce?)
-- definition of elimination rules : uses/consumes that proof (how many ways can we consume it?)

/- Equality (=) 

Introduction Rule : Axiom of Reflexivity

                    ∀ (T: Type) (t: Type), t = t

Elimination Rule : Axiom of Substitutivity 

                    ∀ (T : Type) (P : Prop) (x y : T) (e : x = y) (p : P x), P y

**What theorems can we get given these two axioms?**

-- (1) Theorem of Symmetry

Speaking informally, when we say that a relation,
R, such as equality, is *symmetric* we're mean that,
for *any* objects, x and y, if R relates x to y,
then R also relates y to x.

If the relation in question is equality, then what
it means for equality to be symmetric is that *if*
x = y (for *any* x and y), then it must also be
that y = x. (Otherwise R would not be symmetric.)

-- (2) Theorem of Transitivity

When we say that a relation r, is transitive, we
mean that, for all objects, x, y, and z, if x is
related to y by r, and y is is related to z by r,
then x must be related to z by r (otherwise r is
not transitive).

-/

/- For all (∀) (**special predicate**)

Introduction Rule : ∀ (x : Type), P x

                    *assume* we're given an arbitrary but specific 
                    x : T, then we prove P x

                    **important distinction here**

                    Note that we have made no assumptions about x. 
                    What this means is that we can prove P x,
                    then we can apply a universal generalization 
                    to all objects of that type.

Elimination Rule : *apply* this proof of ∀ x, P x to a function of 
                    a specific value of x, say k, to produce a proof
                    that P k

                    Note that universal generalization is very clear 
                    here.

-/

/- Implies (→)

Introduction Rule : P → Q
                    
                    *assume* arbitrary P, then show Q. In other words, 
                    to prove Q, it will suffice to prove P.

Elimination Rule : *apply* a proof of P → Q as a kind of function to any proof
                    of P to derive Q.

                    A great example of this being done is HW 5

-/

/-
**Notice the similarities between ∀ and →**

As stated before, HW 5 is a great source for seeing these introduction and
elimination rules take place.

-/

/- And (∧)

Introduction Rule : ∀ {a b : Prop}, a → b → a ∧ b

                    For any arbitrary but specific propositions a and b, 
                    if a is true, and b is true, then a ∧ b is true

                    If it takes a true proof of two propositions to construct
                    this proof, then how many ways can we consume it?

Elimination Rule (Left) : ∀ {a b : Prop}, a ∧ b → a

                          For any arbitrary but specific propositions a and b,
                          if the conjunction of a and b is true, then a is true. 

Elimination Rule (Right) : ∀ {a b : Prop}, a ∧ b → b

                          For any arbitrary but specific propositions a and b,
                          if the conjunction of a and b is true, then b is true.

-/

/- Or (∨)

It's important to note that for an Or logical connective, it can be the case that
either of the propositions that make up the proof can be true. Therefore, we 
have two ways to construct this proof and *two* introduction rules. 

Introduction Rule (Left) :  ∀ {a : Prop} (b : Prop), a → a ∨ b

                            For any arbitrary but specific propositions a and b, if given 
                            a proof of a, then a ∨ b is true. 

Introduction Rule (Right) : ∀ (a : Prop) {b : Prop}, b → a ∨ b

                            For any arbitrary but specific propositions a and b, if given 
                            a proof of b, then a ∨ b is true.

Elimination Rule : ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c

                  For any arbitrary but specific propositions a, b, and c, if given a proof
                  of the disjunction of a or b, then if given a proof that a proof of a yields
                  a proof of c, then if given a proof that a proof of b yields a proof of c, then
                  a proof of c is derived. 

-/


