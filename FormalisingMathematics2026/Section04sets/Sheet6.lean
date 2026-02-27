/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by 
  intro a ha
  rw [Set.mem_preimage, Set.mem_image]
  -- |⊢ ∃ x ∈ S, f x = f a
  use a  -- why did this work


example : f '' (f ⁻¹' T) ⊆ T := by 
 intro y hy
 -- rcases hy with ⟨x, hx⟩ -- hx : x ∈ f ⁻¹' T ∧ (f x = y)  and the goal |- y ∈ T 
 rcases hy with ⟨x, hx, rfl⟩ -- hx : x ∈ f ⁻¹' T  and goal |- f x ∈ T (using the rfl) 
 rw [Set.mem_preimage] at hx 
 exact hx

-- `exact?` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by 
  constructor 
  . intro h s sx  
    rw [Set.subset_def] at *
    rw [Set.mem_preimage] 
    apply h
    rw [Set.mem_image]
    use s 
  . intro h y hy 
    rw [Set.subset_def] at *
    rw [Set.mem_image] at * 
    rcases hy with ⟨ a, b, rfl⟩
    specialize h a b
    rw [Set.mem_preimage] at * 
    exact h

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by 
  ext x 
  constructor 
  . intro h 
    rw[Set.mem_preimage] at h 
    exact h
  . intro h
    rw[Set.mem_preimage] at *
    exact h 

-- pushforward is a little trickier. You might have to `ext x`, `constructor`.
example : id '' S = S := by 
  ext x 
  constructor
  . intro h 
    rw [Set.mem_image] at h 
    obtain ⟨a , h1, rfl⟩ := h
    exact h1 
  . intro h
    rw [Set.mem_image] 
    use x
    constructor
    . exact h 
    . rfl 
    
-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- TODO: I get so bored by the end -- i should stop now 27/2/2026
-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by aesop 
-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by aesop 
