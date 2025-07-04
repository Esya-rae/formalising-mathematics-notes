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
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  assumption
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  intro h2 h3
  cases hPoQ with
  | inl h =>
    apply h2
    assumption
  | inr h =>
    apply h3
    assumption
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl h =>
    right
    assumption
  | inr h =>
    left
    assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro h
  cases' h with h1 h2
  cases' h1 with h3 h4
  left
  assumption
  right
  left
  assumption
  right
  right
  assumption
  intro h
  cases' h with hP h2
  left
  left
  assumption
  cases' h2 with hQ hR
  left
  right
  assumption
  right
  assumption
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro h1 h2 h3
  cases' h3 with hP hQ
  left
  apply h1
  assumption
  right
  apply h2
  assumption
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro h1 h2
  cases' h2 with hP hR
  left
  apply h1
  assumption
  right
  assumption
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro h1 h2
  rw [h1, h2]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      assumption
    · intro hQ
      apply h
      right
      assumption
  · intro h h2
    cases' h with hnP hnQ
    cases' h2 with hnP2 hnQ2
    apply hnP
    assumption
    apply hnQ
    assumption
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    right
    intro hQ
    apply h
    constructor <;> assumption
    left
    assumption
  · intro h h2
    cases' h2 with hP hQ
    cases' h with hnP hnQ
    apply hnP
    assumption
    apply hnQ
    assumption
  done
