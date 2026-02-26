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
  intro a 
  rw [Not] at a 
  exact a 

example : x ∈ A → x ∉ A → False := by 
  intro a b 
  rw [Not] at b 
  apply b a 

example : A ⊆ B → x ∉ B → x ∉ A := by 
  intro ab b 
  rw [Not] at * 
  rw [subset_def] at ab 
  intro a 
  specialize ab x a 
  apply b ab 

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by 
  rw [Not] 
  intro h 
  cases h 



example : x ∈ Aᶜ ↔ x ∉ A := by 
  rfl 

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by 
  constructor
  . intro a b 
    rcases b with ⟨ xb, hxb ⟩ 
    apply hxb 
    specialize a xb 
    assumption
  . intro h x   
    by_contra ha_not 
    apply h 
    use x 
    exact ha_not


example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by 
  constructor
  . intro hx hy 
    rcases hx with ⟨ a, ha⟩
    specialize hy a 
    apply hy ha  
  . intro h 
    by_contra h1 
    apply h 
    intro x hx 
    apply h1 
    use x 
