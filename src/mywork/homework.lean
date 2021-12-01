namespace hw_5

-- personal notes 

/-
EXISTS INTRO

* A predicate is a proposition with one or more parameters 
* The introducton rule for exists takes two arguments: a witness value, w, and 
a proof that the witness satisfies the predicate
* It's often clear and useful to apply the introduction rule to a witness, leaving
the proof that it satisfies teh predicate to a separate sub-goal/sub-task (notice how
the value of the parameter is incorporated into the final proposition to be proved: that
the value has the required property)

* dependely type pairs that constitute proofs of existential propositions <witness, proof>
* For existential propositions written like ∃ x y z, P x y z it's important to note that they
might hide a little bit of insight, which is that you do actually need to apply exists.intro to 
produce three different proofs here, one for each ∃ 

EXISTS ELIMINATION
* If you have a proof, ex, of ∃ (x: X), P x, you can apply exists.elim to ex, and (after a 
few more simple answers)

 

-/


end hw_5


namespace hw_6

end hw_6