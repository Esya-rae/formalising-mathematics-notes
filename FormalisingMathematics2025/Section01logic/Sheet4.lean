/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases h with
  | intro left right => exact left
  done

example : P ∧ Q → Q := by
  intro h
  cases h with
  | intro left right => exact right
  done

example : (P → Q → R) → P ∧ Q → R := by
  intro h h2
  cases' h2 with hP hQ
  apply h
  <;> assumption
  done

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption
  -- · assumption
  -- · assumption
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases' h with hP hQ
  constructor <;> assumption
  done

example : P → P ∧ True := by
  intro hP
  constructor
  exact hP
  trivial
  done

example : False → P ∧ False := by
  intro h
  exfalso
  exact h
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPQ hQR
  cases' hPQ with hP hQ
  cases' hQR with hQ2 hR
  constructor <;> assumption
  done

example : (P ∧ Q → R) → P → Q → R := by
  intro h hP hQ
  apply h
  constructor <;> assumption
  done
