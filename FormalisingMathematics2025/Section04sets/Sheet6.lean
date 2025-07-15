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
  change ∀ x, x ∈ S → x ∈ f ⁻¹' (f '' S)
  intro x h
  change x ∈ {x : X | f x ∈ f '' S}
  change f x ∈ f '' S
  change f x ∈ {y : Y | ∃ x : X, x ∈ S ∧ f x = y}
  change ∃ a : X, a ∈ S ∧ f a = f x
  use x

example : f '' (f ⁻¹' T) ⊆ T := by
  change ∀ x, x ∈ f '' (f ⁻¹' T) → x ∈ T
  intro x h
  change x ∈ {y : Y | ∃ x : X, x ∈ (f ⁻¹' T) ∧ f x = y} at h
  change ∃ a : X, a ∈ (f ⁻¹' T) ∧ f a = x at h
  change ∃ a : X, a ∈ {x : X | f x ∈ T} ∧ f a = x at h
  change ∃ a : X, (f a ∈ T) ∧ f a = x at h
  rcases h with ⟨a, haT, hfa⟩
  rw [←hfa]
  assumption

-- `exact?` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  change {y : Y | ∃ x : X, x ∈ S ∧ f x = y} ⊆ T ↔ S ⊆ {x : X | f x ∈ T}
  change (∀ t, (∃ a ∈ S, f a = t) → t ∈ T) ↔ ∀ x, x ∈ S → f x ∈ T
  constructor
  intro h
  intro x
  intro hs
  let y:= f x
  specialize h y
  apply h
  use x
  intro h
  intro t
  intro h1
  cases' h1 with a ha
  cases' ha with h1 h2
  apply h at h1
  rw [h2] at h1
  assumption

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext t
  change t ∈ {x : X | id x ∈ S}  ↔ t ∈ S
  change id t ∈ S ↔ t ∈ S
  have h: id t = t := by rfl
  rw [h]


-- pushforward is a little trickier. You might have to `ext x`, `constructor`.
example : id '' S = S := by
  ext t
  change t ∈ {y : X | ∃ x : X, x ∈ S ∧ id x = y}  ↔ t ∈ S
  change  (∃ x ∈ S, id x = t) ↔ t ∈ S
  change  (∃ x ∈ S, x = t) ↔ t ∈ S
  constructor
  intro h
  cases' h with x hx
  cases' hx with hs ht
  rw [ht] at hs
  assumption
  intro h
  use t


-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext t
  let R := g ⁻¹' U
  change t ∈ {x : X | (g ∘ f) x ∈ U} ↔ t ∈ {x : X | f x ∈ R}
  change t ∈ {x : X | g (f x) ∈ U} ↔ t ∈ {x : X | f x ∈ {y : Y | g y ∈ U}}
  change g (f t) ∈ U ↔ f t ∈ {y : Y | g y ∈ U}
  change g (f t) ∈ U ↔ g (f t) ∈ U
  trivial


-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext t
  let R:= f '' S
  change t ∈ {y : Z | ∃ x : X, x ∈ S ∧ g (f x) = y} ↔ t ∈ {y : Z | ∃ x : Y, x ∈ R ∧ g x = y}
  change (∃ x : X, x ∈ S ∧ g (f x) = t) ↔
  (∃ x : Y, x ∈ {y : Y | ∃ x : X, x ∈ S ∧ f x = y} ∧ g x = t)
  change (∃ x : X, x ∈ S ∧ g (f x) = t) ↔ (∃ x : Y, (∃ a : X, a ∈ S ∧ f a = x) ∧ g x = t)
  constructor
  intro h
  cases' h with a ha
  cases' ha with h1 h2
  let x:= f a
  use x
  constructor
  use a
  change g (f a) = t
  assumption
  intro h
  cases' h with x hx
  cases' hx with h1 h2
  cases' h1 with a ha
  cases' ha with h3 h4
  use a
  rw [h4]
  constructor <;> assumption
