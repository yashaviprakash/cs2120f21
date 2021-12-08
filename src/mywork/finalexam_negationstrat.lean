/- Negation Proof Strategies -/

-- pause! let's review negation first:

/- Negation (¬ P, P → false)

Given a proposition, P, we can form a new proposition,
written as ¬P, which we pronounce as "not P", and which 
we define in such as way as to assert that P is not true

What does it mean to say that P is false?

We mean that there are no proofs of P, so we
have to *judge* it to be logically false

How can we show that there are no proofs of P?

This is the trick. We prove it somewhat indirectly
by proving P → false. 

Suppose P → false is true. What this says is that
if P is true then false is true, which is absurd 
because we've defined false to the proposition with
no proofs, so it can't be true. 

So, if P → false is true, then the consequence of that 
is that there *can be no proofs of P*.

How do we prove that P → false?

*assume* that P is true and show that with that you can
construct a proof of false
-/

/- Meaning of ¬ P

For any proposition, P, we *define* ¬P to be the 
proposition, P → false. So ¬P is true exactly when
P → false is true, and that is true exactly when P 
is false, when there are no proofs of it. If you
can produce a proof of P → false, then you can conclude
¬P. This is the introduction rule for ¬. 

-/

-- Example. Prove ¬ (0=1)

/-
How should we see this?

To prove ¬(0=1), we must assume that 0=1 and show that
no proofs can come from it. 

-/

example : ¬ (0=1) :=
begin
  assume h, -- assume 0=1 is true
  cases h, -- what have I done here? Look below.
end

/- Case Analysis

So, how did I solve that last proof with case analysis?

The general principle of case analsys is : if we have an assumed/arbitrary proof of X
                                           and need to show Y, we can try to do this by
                                           doing case analysis on the proof of X. If we
                                           can show that Y is true *in all cases* (in a
                                           context in which we have *some* proof of X), 
                                           then we have shown that Y must be true in this
                                           context.

The most interesting example of the preceding prinicple occurs when you're given or you can 
derive a proof of false. For then all you have to do is show that some proposition, P, follows
is to show that it's true for all possible wya sin which that proof of false could
have been constructed. There are *zero* way sto construct proof, so there are zero cases to 
consider! The truth of your conclusion follows automatically!

Going back to the previous example, how many ways can 0=1 be proven true?

None! 

-/

-- now we can go on to discuss proof strategies involving negation!

/- Proof by Negation

The first, proof by negation, says that from a proof of P → false
you can derive a proof of ¬P. 

  (P : Prop) (np : P → false)
  --------------------------- [by defn'n]
            (pf : ¬P)

This rule is the foundation for "proof by negation". To prove ¬P you
first assume P, is true, then you show that in this context you can 
derive a contradiction. What you have then shown, of course, is P → false.

Thus, to prove ¬P you prove P → false. Another way
to read P → false is that, if we assume that P is
true, we can derive a contradiction, proof of false 
that cannot exist, so P must not be true. MEMORIZE
THIS REASONING.

-/

/- Proof by Negation vs Proof by Contradiction

To prove ¬P, assume P and show that in this context 
there is a contradiction. This is proof by negation.

It is *entirely* different from Proof by Contradiction!

-/

/- Proof by Contradiction

You can use this approach to a proposition, P, by assuming
¬P and showing that this assumption leads to a contradiction.

That proves ¬¬P. Then you use the *independent* axiom of negation
elimination to infer P from ¬¬P

-/

/- False Elimination

The second rule says that if you have a proof of false and any other
proposition, P, the logic is useless and so you might as well just 
admit that P is true.

Why is the logic useless?

Well if false is true then there's no longer a difference!

A contradiction makes a logic inconsistent.

  (P : Prop) (f : false)
  ---------------------- (false_elim f)
        (pf : P)

This can be further expressed as: ∀ (P : Prop), false → P
-/

/- Excluded Middle

Any proposition is either true or false, there is no middle ground.

But in the constructive logic of Lean, this isn't true.

To prove P ∨ ¬P, as you recall, we need to have 
either a proof of P (in this case  use or.intro_left)
or a proof of ¬P, in which case we use or.intro_right
to prove P ∨ ¬P. But what if we don't have a proof
either way?

Instead, this is *classically* true (in classical logic).

How can we *use* the excluded middle?

The real power is in how we *use* this new axiom.
You give it a proposition, P, it gives you a proof
of a disjunction (P ∨ ¬P). Well, what do you do with
a proof of a disjunction? Answer: a case analysis. 

-/

