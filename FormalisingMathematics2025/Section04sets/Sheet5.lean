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
  simp

example : A ∩ A = A := by
  simp

example : A ∩ ∅ = ∅ := by
  simp

example : A ∪ univ = univ := by
  simp

example : A ⊆ B → B ⊆ A → A = B := by
  intro h h1
  ext t
  rw [subset_def] at h
  specialize h t
  rw [subset_def] at h1
  specialize h1 t
  constructor <;> assumption

example : A ∩ B = B ∩ A := by
  ext t
  repeat rw [inter_def]
  change t ∈ A ∧ t ∈ B ↔ t ∈ B ∧ t ∈ A
  constructor
  intro h
  cases' h with ha hb
  constructor <;> assumption
  intro h
  cases' h with hb ha
  constructor <;> assumption

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext t
  repeat rw [inter_def]
  change t ∈ A ∧ t ∈ B ∧ t ∈ C ↔ (t ∈ A ∧ t ∈ B) ∧ t ∈ C
  constructor
  rintro ⟨ha, ⟨hb, hc⟩⟩
  exact ⟨⟨ha, hb⟩, hc⟩
  rintro ⟨⟨ha, hb⟩, hc⟩
  exact ⟨ha, ⟨hb, hc⟩⟩

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext t
  repeat rw [union_def]
  change t ∈ A ∨ (t ∈ B ∨ t ∈ C) ↔ (t ∈ A ∨ t ∈ B) ∨ t ∈ C
  rw [or_assoc]

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext t
  repeat rw [union_def]
  repeat rw [inter_def]
  change t ∈ A ∨ (t ∈ B ∧ t ∈ C) ↔ (t ∈ A ∨ t ∈ B) ∧ (t ∈ A ∨ t ∈ C)
  exact or_and_left

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext t
  repeat rw [union_def]
  repeat rw [inter_def]
  change t ∈ A ∧ (t ∈ B ∨ t ∈ C) ↔ t ∈ A ∧ t ∈ B ∨ t ∈ A ∧ t ∈ C
  exact and_or_left
