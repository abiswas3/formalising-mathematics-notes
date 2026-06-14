/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by 
  ext x 
  constructor
  · intro h 
    rw [Set.union_self A] at h 
    exact h 
  · intro h 
    simp only [A.union_self] 
    exact h

example : A ∩ A = A := by 
  ext 
  simp only [Set.inter_self]

example : A ∩ ∅ = ∅ := by 
  simp only [Set.inter_empty]

example : A ∪ univ = univ := by  
  simp only [Set.union_univ]

example : A ⊆ B → B ⊆ A → A = B := by 
  intro ab ba 
  ext x 
  constructor
  · intro hx  
    specialize ab hx
    exact ab
  · intro hx 
    apply  ba at hx 
    exact hx 

example : A ∩ B = B ∩ A := by
  ext x 
  constructor
  · intro hz
    change (x ∈ A ∧ x ∈ B) at hz 
    constructor
    · exact hz.right 
    · exact hz.left
  · intro hz 
    change (x ∈ B ∧ x ∈ A) at hz 
    constructor
    · exact hz.right 
    · exact hz.left 

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by 
  exact?

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by 
exact?

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by 
  exact?

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by 
  exact inter_union_distrib_left A B C
