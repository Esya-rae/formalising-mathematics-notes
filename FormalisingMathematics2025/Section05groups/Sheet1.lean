/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_cancel g`.
-/
  inv_mul_cancel g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

-- can alternatively be found with `apply?` if you didn't know the answer already
-- or `rw?`
-- or `simp?`
example (a : G) : a * 1 = a := by
  rw [@mul_right_eq_self]

-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  simp only [one_mul]

example (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_cancel a

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  exact inv_mul_cancel_left a b

example : a * (a⁻¹ * b) = b := by
  exact mul_inv_cancel_left a b

example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  have h: b * (a * c) = (b * a) * c := by exact Eq.symm (mul_assoc b a c)
  rw [h1, h2] at h
  simp at h
  assumption

example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  intro h
  have h1: a⁻¹ * (a * b) = a⁻¹ := by exact mul_right_eq_self.mpr h
  rw [inv_mul_cancel_left a b] at h1
  exact id (Eq.symm h1)
  intro h
  rw [←h]
  exact mul_inv_cancel a

example : (1 : G)⁻¹ = 1 := by
  exact inv_one

example : a⁻¹⁻¹ = a := by
  exact DivisionMonoid.inv_inv a

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  exact DivisionMonoid.mul_inv_rev a b

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g t : G, g * t = t * g := by
  intro g t
  have hg: g * g = 1 := by exact h g
  have ht: t * t = 1 := by exact h t
  have htg: (t * g) * (t * g) = 1 := by exact h (t * g)
  have h1: (g * 1) = g := by exact MulOneClass.mul_one g
  have h2: (g * 1) * g = g * g := by exact mul_right_cancel_iff.mpr h1
  rw [←ht] at h2
  rw [←mul_assoc, mul_assoc, hg, ←htg] at h2
  have h3: g * t * (t * g) * (t * g) = t * g * (t * g) * (t * g) :=
  by exact congrFun (congrArg HMul.hMul h2) (t * g)
  rw [mul_assoc] at h3
  nth_rewrite 3 [mul_assoc] at h3
  rw [htg] at h3
  repeat rw [mul_one] at h3
  assumption
