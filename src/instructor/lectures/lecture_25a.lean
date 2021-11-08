import .lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def strict_ordering :=  asymmetric r ∧ transitive r -- asymmetric is stronger than antisymmetric, less than is an example


def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r


def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬strongly_connected r -- not total


def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

/-
Well Order

A relation r is a well ordering of a set if it's a total order, and if you pick
any subset of a set on which you have a relation, any subset has to have a least 
element
-/

def well_ordering := total_order r ∧ (∀ (s : set β), ∃ (b : β), ∀ (b' : β), b' ∈ s → b < b')
end relation
end relations
