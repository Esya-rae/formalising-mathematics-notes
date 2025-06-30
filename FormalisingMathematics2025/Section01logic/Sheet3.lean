/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  trivial
  done

example : False → ¬True := by
  trivial
  done

example : ¬False → True := by
  trivial
  done

example : True → ¬False := by
  trivial
  done

example : False → ¬P := by
  intro h
  exfalso
  exact h
  done

example : P → ¬P → False := by
  intro hP
  intro h
  trivial
  done

example : P → ¬¬P := by
  intro hP
  by_contra hnP
  trivial
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  by_contra hP
  apply hPQ at hP
  trivial
  done

example : ¬¬False → False := by
  intro h
  by_contra h2
  trivial
  done

example : ¬¬P → P := by
  intro h
  by_contra h2
  trivial
  done

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  by_contra hnQ
  apply h at hnQ
  trivial
  done
