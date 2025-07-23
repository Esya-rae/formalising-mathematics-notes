/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/

theorem self_inf_sup_eq_self (L : Type) [Lattice L] : (∀ a b : L, a ⊓ b ⊔ a = a)  := by
  intro a b
  apply le_antisymm
  · apply sup_le
    exact inf_le_left
    exact Preorder.le_refl a
  · exact le_sup_right

example (L : Type) [Lattice L] : (∀ a : L, a = a⊓ a) := by exact fun a ↦ Eq.symm (inf_idem a)


example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  · intro h
    intro a b c
    apply le_antisymm
    · have h1: a ⊓ c ⊔ a ⊓ b = a ⊓ b ⊔ a ⊓ c := by exact sup_comm (a ⊓ c) (a ⊓ b)
      rw [←h1]
      rw [h (a ⊓ c) a b]
      rw [self_inf_sup_eq_self]
      have h2: a ⊓ b ⊔ a ⊓ a ≤ a ⊓ (b ⊔ a) := by apply le_inf_sup
      have h3: a ⊓ a = a := by exact inf_idem a
      calc
      a ⊓ (b ⊔ c) = (b ⊔ c) ⊓ a := by exact Eq.symm (inf_comm (b ⊔ c) a)
      _ = (b ⊔ c) ⊓ (a ⊓ b ⊔ a) := by rw [self_inf_sup_eq_self]
      _ = (b ⊔ c) ⊓ (a ⊓ b ⊔ (a ⊓ a)) := by rw [h3]
      _ ≤  (b ⊔ c) ⊓ (a ⊓ (b ⊔ a)) := by exact inf_le_inf_left (b ⊔ c) h2
      _ = (b ⊔ c) ⊓ a ⊓ (b ⊔ a) := by exact Eq.symm (inf_assoc (b ⊔ c) a (b ⊔ a))
      _ = a ⊓ (b ⊔ c) ⊓ (b ⊔ a) := by rw [inf_comm a (b ⊔ c)]
      _ = a ⊓ ((b ⊔ c) ⊓ (b ⊔ a)) := by exact inf_assoc a (b ⊔ c) (b ⊔ a)
      _ =  a ⊓ (b ⊔ c ⊓ a):= by rw [h]
      _ =  a ⊓ (b ⊔ a ⊓ c):= by rw [inf_comm a c]
      _ = a ⊓ (a ⊓ c ⊔ b) := by rw [sup_comm]

    . exact le_inf_sup
  · intro h
    intro a b c
    apply le_antisymm
    · exact sup_inf_le
    · have h1: ((a ⊔ c) ⊔ (b ⊓ c)) ⊓ a ≤ a := by exact inf_le_right
      have h2: b ⊓ (a ⊔ (b ⊓ c)) ≤ (a ⊔ (b ⊓ c)) := by exact inf_le_right
      calc
      (a ⊔ b) ⊓ (a ⊔ c) ≤  (a ⊔ b) ⊓ (a ⊔ c) ⊔  (a ⊔ b) ⊓ (b ⊓ c):= by exact le_sup_left
      _ = (a ⊔ b) ⊓ ((a ⊔ c) ⊔ (b ⊓ c)) := by rw [h (a ⊔ b) (a ⊔ c) (b ⊓ c)]
      _ = ((a ⊔ c) ⊔ (b ⊓ c)) ⊓ (a ⊔ b):= by exact inf_comm (a ⊔ b) (a ⊔ c ⊔ b ⊓ c)
      _ = (((a ⊔ c) ⊔ (b ⊓ c)) ⊓ a) ⊔ (((a ⊔ c) ⊔ (b ⊓ c)) ⊓ b) := by exact h (a ⊔ c ⊔ b ⊓ c) a b
      _ ≤ a ⊔ (((a ⊔ c) ⊔ (b ⊓ c)) ⊓ b) := by exact sup_le_sup_right h1 ((a ⊔ c ⊔ b ⊓ c) ⊓ b)
      _ = a ⊔ ((c ⊔ a ⊔ (b ⊓ c)) ⊓ b) := by rw [sup_comm c a]
      _ = a ⊔ (b ⊓ (c ⊔ a ⊔ (b ⊓ c))) := by rw [inf_comm (c ⊔ a ⊔ (b ⊓ c)) b]
      _ = a ⊔ (b ⊓ (c ⊔ (a ⊔ (b ⊓ c)))) := by rw [sup_assoc c a (b ⊓ c)]
      _ = a ⊔ ((b ⊓ c) ⊔ b ⊓ (a ⊔ (b ⊓ c))) := by  rw [h b c (a ⊔ (b ⊓ c))]
      _ = a ⊔ (b ⊓ c) ⊔ b ⊓ (a ⊔ (b ⊓ c)) := by rw [@sup_assoc]
      _ ≤  a ⊔ (b ⊓ c) ⊔ (a ⊔ (b ⊓ c)):= by exact sup_le_sup_left h2 (a ⊔ b ⊓ c)
      _ = a ⊔ (b ⊓ c) := by exact sup_idem (a ⊔ b ⊓ c)
