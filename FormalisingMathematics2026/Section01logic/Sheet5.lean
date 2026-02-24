/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl 

example : (P ↔ Q) → (Q ↔ P) := by
  intro h 
  rw [<- h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro pq 
  rw [pq]
  intro qp 
  rw[qp] 

  

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro pq qr 
  rw [<- qr]
  rw [pq]
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro h 
  constructor 
  exact h.right 
  exact h.left 
  intro h 
  constructor
  exact h.right
  exact h.left 

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  . intro h 
    rcases h with ⟨ pq, r⟩ 
    rcases pq with ⟨p, q⟩ 
    constructor
    . assumption
    . constructor
      . assumption
      . assumption
  . intro h 
    rcases h with ⟨ p, qr⟩ 
    rcases qr with ⟨q, r⟩ 
    constructor
    . constructor
      . assumption
      . assumption
    . assumption
 

example : P ↔ P ∧ True := by
  constructor
  . intro p 
    constructor
    . exact p 
    . trivial 
  . rintro ⟨ p, t⟩ 
    exact p 
     

example : False ↔ P ∧ False := by
  constructor
  . rintro ⟨ p, f⟩ 
  . rintro ⟨ p, f⟩ 
    trivial 

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro pq rs 
  constructor
  . rintro ⟨ p, r ⟩ 
    constructor
    . rw [<- pq]
      exact p
    . rw [<- rs]
      exact r 
  . rintro ⟨ q, s ⟩ 
    constructor
    . rw [<- pq] at q 
      assumption
    . rw [<- rs ] at s 
      assumption

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬ P) -> False 
  -- h1: P -> ¬ P 
  -- h2: ¬ P -> P  
  rintro ⟨ h1, h2 ⟩ 
  change P-> (P->False) at h1 
  change (P->False)->P at h2 
  apply h1 
  apply h2 
  intro p 
  apply h1 
  assumption
  assumption

  apply h2 
  intro p 
  apply h1 
  all_goals assumption
  


  
