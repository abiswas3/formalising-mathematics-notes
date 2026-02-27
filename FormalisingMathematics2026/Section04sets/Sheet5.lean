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
  . intro h 
    rcases h with l | r 
    . assumption
    . assumption
  . intro h 
    left 
    exact h 


example : A ∩ A = A := by 
  ext a
  constructor 
  . intro ha 
    exact ha.left 
  . intro ha 
    rw [mem_inter_iff] 
    constructor
    . exact ha 
    . exact ha 



example : A ∩ ∅ = ∅ := by 
  ext a 
  constructor
  . intro ha 
    rw [mem_inter_iff] at ha 
    exact ha.right
  . intro ha 
    rw [mem_inter_iff] 
    constructor 
    . by_contra hb 
      apply ha
    . assumption

example : A ∪ univ = univ := by 
  ext x 
  constructor 
  . intro h
    rcases h with h | h
    . trivial  
    . exact h 
  . intro h 
    right; exact h 

example : A ⊆ B → B ⊆ A → A = B := by 
  intro h h1
  ext x 
  constructor 
  . intro ha 
    rw [subset_def] at h
    specialize h x ha 
    exact h
  . intro hb 
    rw [subset_def] at h1
    specialize h1 x hb
    exact h1

-- TODO: I'll do this later.

example : A ∩ B = B ∩ A := by 
  ext x 
  constructor 
  . intro h 
    constructor 
    . exact h.right 
    . exact h.left
  . intro h 
    constructor 
    . exact h.right 
    . exact h.left 

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by 
  ext x 
  constructor 
  . intro h 
    have h1: x ∈ A := h.left 
    have h2: x ∈ B := (h.right).left 
    have h3: x ∈ C := (h.right).right 
    constructor 
    . constructor <;> assumption
    . exact h3
  . intro h 
    have h1: x ∈ C := h.right 
    have h2: x ∈ B := h.left.right
    constructor 
    . exact (h.left).left  
    . constructor <;> assumption

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by 
  ext x 
  constructor 
  . intro h 
    rcases h with h' | h' | h'
    . left; left; assumption 
    . left; right; assumption 
    . right; assumption 
  . intro h 
    rcases h with h' | h' 
    . rcases h' with h'' | h''
      . left; assumption
      . right; left; assumption 
    . right; right; assumption 

-- TODO: I am really really bored -- aesop is super smart simp 
example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by aesop
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by aesop
