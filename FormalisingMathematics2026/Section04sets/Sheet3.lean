/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by 
  intro h h'
  contradiction

example : x ∈ A → x ∉ A → False := by 
  intro h h' 
  contradiction

example : A ⊆ B → x ∉ B → x ∉ A := by 
  intro hab hx
  change (x ∈ A) -> False
  intro ha 
  specialize hab ha 
  contradiction

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by 
  change (x ∈ ∅) -> False
  intro h 
  have h: True := by trivial 
  trivial

example : x ∈ Aᶜ ↔ x ∉ A := by 
  constructor
  · intro h 
    exact h 
  · intro h 
    exact h


example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by 
  constructor
  · intro h1 h2 
    rcases h2 with ⟨z, hz⟩
    specialize h1 z 
    contradiction
  · intro h1 z
    by_contra hzn 
    apply h1
    use z
    intro hz 
    apply h1 
    exact ⟨z, hzn⟩


