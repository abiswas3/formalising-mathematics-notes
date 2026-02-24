/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro nt 
  change True -> False at nt 
  apply nt 
  trivial 




example : False → ¬True := by
  intro h 
  change True -> False 
  trivial 


example : ¬False → True := by
  intro h 
  trivial 

example : True → ¬False := by
  intro h 
  change False -> False 
  trivial 

example : False → ¬P := by
  intro h
  change P -> False 
  by_contra _ 
  exact h 


example :  P → ¬P → False := by
  intro p np 
  change P-> False at np 
  apply np p 


example : P → ¬¬P := by
  intro p
  change (P -> False)->False 
  intro hp 
  apply hp p 


example : (P → Q) → ¬Q → ¬P := by
  intro pq nq 
  change P->False
  intro p 
  change Q -> False at nq 
  apply nq 
  apply pq p 

example : ¬¬False → False := by
  intro h 
  change (False -> False)->False at h 
  apply h 
  trivial 

example : ¬¬P → P := by
  intro hp 
  change (¬ P )->False at hp 
  -- Goal is now P 
  by_contra h 
  -- goal is now false and my assumotion h is not P 
  apply hp h 


example : (¬Q → ¬P) → P → Q := by
  intro a b 
  by_contra h 
  specialize a h 
  change P-> False at * 
  change Q-> False at * 
  apply a b 

