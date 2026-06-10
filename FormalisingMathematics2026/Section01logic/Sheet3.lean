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
  intro h 
  change (True -> False) at h 
  apply h 
  trivial

example : False → ¬True := by
  intro h 
  change (True -> False) 
  by_contra h1 
  exact h

example : ¬False → True := by
  intro h 
  change (False -> False) at h 
  by_contra h1 
  change (True -> False) at h1 
  apply h1
  trivial 

example : True → ¬False := by
  intro h 
  change (False -> False)
  by_contra h1 
  exact h1 

example : False → ¬P := by
  intro h 
  change (P -> False) 
  by_contra h1 
  assumption 

example : P → ¬P → False := by
  intro p np
  apply np p 

example : P → ¬¬P := by
  intro p 
  change (¬P -> False) 
  change ((P -> False) -> False)
  by_contra h 
  apply h p 

example : (P → Q) → ¬Q → ¬P := by
  intro pq nq 
  change (P -> False) 
  change (Q->False) at nq 
  intro p
  apply nq 
  apply pq p 

example : ¬¬False → False := by
  intro nnfalse 
  change (¬(False -> False)) at nnfalse
  change (False -> False) -> False at nnfalse 
  apply nnfalse 
  intro h 
  exact h 

example : ¬¬P → P := by
  intro nnp 
  change (P -> False )-> False at nnp 
  by_contra h 
  specialize nnp h 
  assumption

example : (¬Q → ¬P) → P → Q := by
  intro nqnp p 
  by_contra h 
  specialize nqnp h 
  change (P -> False) at nqnp 
  apply nqnp p 
