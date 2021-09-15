/-
 
important quote: if something is true of an arbitrary object of a specific kind, it must be true of all objects of a specific kind. Introduction rule for for all
 
e: x = y is to assume you have a proof of x = y, the e variable name is
 
by making assumptions one after another we built up a context where we now need to produce a proof that y = x
 
rw e= rewrite using the equality e
 
Full question for what this mean sat minute 23
 
a theorem is nothing different than a definition, it can be used interchangeably
-/
def x: ℕ := 1
 
theorem eq_symm :
 ∀ (T:Type) (x y : T), x = y → y = x :=
 begin
   assume (T: Type),
   assume (x y: T),
   assume (e : x = y),
   rw e,
 end
 
/-
 
English language proof
 
Theorem: Equality is symmetric. In other words
∀ (T:Type) (x y : T), x = y → y = x.
 
 
Proof: First we'll assume that T is any type and we have objects x and y of this type. what remains to be shown
is that if x = y → y = x. To prove this, we'll assume the premise, that x = y, and
in this context we need to prove y = x. But by the axiom of substitutability of equals, and using the fact x = y, we can rewrite x in the goal as y, yielding y = y
as our new proof goal. This is true by the axiom of reflexivity of equality. QED. 
-/
 
/-
Prove that equality is transitive.
-/
 
theorem eq_trans:
 ∀ (T:Type) (x y z: T), x = y → y = z → x = z :=
 begin
   assume T,
   assume x y z,
   assume e1,
   assume e2,
   rw e1,
   exact e2,
 
 end
 
 /-
 exercise: if x = y, y=z, prove z=x	
 Top down approach
 -/
 
 theorem eq_transsub:
 ∀ (T : Type) (x y z : T), x = y → y = z → z = x :=
 begin
   assume T x y z h1 h2, -- introduction rule for ∀
   apply eq.symm _,      -- application of symm *theorem* turns z=x to x=z
   apply eq.trans h1 h2, -- application of trans theorem, can nowuse trans eq
 end
