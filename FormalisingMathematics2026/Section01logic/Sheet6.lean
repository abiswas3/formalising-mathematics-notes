/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  sorry

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => sorry
  | inr h => sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · sorry
  · sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · intro pr qr 
    apply pr h 
  · intro pq qr 
    apply qr h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h1 
  obtain h | h := h1
  . right 
    assumption
  . left 
    assumption
  
-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . intro pq
    obtain h | h := pq 
    . obtain h'|h' := h
      . left 
        exact h'
      . right 
        left 
        exact h' 
    . right 
      right 
      exact h 
  . intro h 
    obtain h' | h' := h 
    . left 
      left 
      assumption
    . obtain h2 | h2 := h'
      . left 
        right 
        assumption
      . right 
        assumption
    
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro pr qs pOq 
  obtain p | q := pOq 
  . left 
    apply pr p 
  . right 
    apply qs 
    assumption

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro pq pOr 
  obtain p | r := pOr
  . left 
    apply pq p 
  . right 
    exact r 

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro pr qs 
  constructor
  . intro h -- =>
    obtain p | q := h 
    . rw [pr] at p
      left 
      assumption
    . rw [qs] at q 
      right 
      assumption
  . intro h  -- <=
    obtain r | s := h 
    . rw [<- pr] at r
      left 
      assumption
    . rw [<- qs] at s 
      right 
      assumption
  

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h 
    change ( P ∨ Q ) -> False at h 
    constructor
    . change P -> False 
      intro p 
      apply h 
      left 
      assumption
    . change Q -> False
      intro q 
      apply h 
      right 
      assumption
  . intro h 
    change (P ∨ Q) -> False 
    intro pOrq 
    rcases h with ⟨ nP, nQ ⟩
    change P -> False at nP
    change Q -> False at nQ 
    obtain p | q := pOrq
    . apply nP p 
    . apply nQ q 

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h -- h: ¬ (P ∧ Q) and |- ¬ P ∨ Q 
    by_cases hP : P -- assume P is true 
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left -- assume Not ¬ P 
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ

