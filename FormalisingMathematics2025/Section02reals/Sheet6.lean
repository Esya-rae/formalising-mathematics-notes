/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2025.Solutions.Section02reals.Sheet5
-- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/



theorem div_mul_rw (a b: ℝ) (hb: b ≠ 0): a / b * b = a :=  by
  rw [div_eq_mul_inv, mul_assoc]
  rw [inv_mul_cancel₀ hb, mul_one]

theorem abs_mul_pos (a b: ℝ) (hb: b > 0): |a| * b = |a * b| :=  by
  have hb2: b = |b| := by exact Eq.symm (abs_of_pos hb)
  nth_rewrite 1 [hb2]
  exact Eq.symm (abs_mul a b)



/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  rw [tendsTo_def] at h
  have hε2 : ε / c > 0 := by exact div_pos hε hc
  specialize h (ε / c) hε2
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  have h3 : |a n - t| * c < (ε / c) * c:= by exact (mul_lt_mul_right hc).mpr hB
  simp
  rw [div_mul_rw, abs_mul_pos, mul_comm, mul_sub_left_distrib c (a n) t] at h3
  assumption
  assumption
  exact Ne.symm (ne_of_lt hc)


theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  apply tendsTo_pos_const_mul
  assumption
  norm_num

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
    apply tendsTo_neg at h
    apply tendsTo_pos_const_mul at h
    let b := -c
    have hb : b > 0 := neg_pos.mpr hc
    specialize h hb
    change TendsTo (fun n ↦ (-c) * -a n) ((-c) * -t) at h
    simp at h
    assumption

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  by_cases h2: c > 0
  apply tendsTo_pos_const_mul
  <;> assumption
  apply le_of_not_gt at h2
  apply lt_or_eq_of_le at h2
  cases' h2 with h3 h4
  apply tendsTo_neg_const_mul
  <;> assumption
  rw [h4]
  simp
  apply tendsTo_const

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  apply tendsTo_const_mul c at h
  intro ε hε
  rw [tendsTo_def] at h
  specialize h ε hε
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  simp
  rw [mul_comm (a n) c, mul_comm t c]
  assumption


-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  intro h
  apply tendsTo_add_const (-t) at h
  simp at h
  change TendsTo (fun n ↦ a n - t) 0 at h
  assumption
  intro h
  apply tendsTo_add_const t at h
  simp at h
  assumption

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  rw [tendsTo_def] at ha
  rw [tendsTo_def] at hb
  rw [tendsTo_def]
  intro ε hε
  have hε2 : Real.sqrt ε > 0 := by exact Real.sqrt_pos_of_pos hε
  specialize ha (Real.sqrt ε) hε2
  specialize hb (Real.sqrt ε) hε2
  cases' ha with A hA
  cases' hb with B hB
  use max A B
  intro n hn
  apply sup_le_iff.mp at hn
  cases' hn with ha hb
  specialize hA n ha
  specialize hB n hb
  simp at hA
  simp at hB
  simp
  rw [abs_mul (a n) (b n)]
  by_cases h3: |a n| = 0
  rw [h3]
  simp
  assumption
  change |a n| ≠ 0 at h3
  apply abs_ne_zero.mp at h3
  apply abs_pos.mpr at h3
  apply (mul_lt_mul_iff_of_pos_right hε2).mpr at hA
  apply (mul_lt_mul_iff_of_pos_left h3).mpr at hB
  have h4: √ε * √ε = ε := by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hε2).mp rfl
  rw [h4] at hA
  exact lt_trans hB hA

/-- If `a(n)` tends to 0 but `b(n)` both tends to u, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo {a b : ℕ → ℝ} (t u: ℝ) (ht: t = 0) (ha : TendsTo a 0)
 (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  rw [tendsTo_def] at ha
  rw [tendsTo_def] at hb
  rw [tendsTo_def]
  intro ε hε
  let ε1 := ε / (|u| + ε)
  have h0_0: |u| ≥ 0:= by exact abs_nonneg u
  have h0: |u| + ε > 0 := by exact add_pos_of_nonneg_of_pos h0_0 hε
  have hε1: ε1 > 0 := by exact div_pos hε h0
  specialize ha ε1 hε1
  specialize hb ε hε
  cases' ha with A hA
  cases' hb with B hB
  use max A B
  intro n hn
  apply sup_le_iff.mp at hn
  cases' hn with ha hb
  specialize hA n ha
  specialize hB n hb
  simp at hA
  simp

  have h1_1: |b n| - |u| ≤ |b n - u| := by exact abs_sub_abs_le_abs_sub (b n) u
  have h1_2: |b n| - |u| < ε := by exact lt_of_le_of_lt h1_1 hB
  have h1: |b n| < |u| + ε := by exact lt_add_of_tsub_lt_left h1_2
  clear h1_1 h1_2



  rw [abs_mul (a n) (b n)]
  have h2_1: |a n| ≥ 0:= by exact abs_nonneg (a n)
  have h2: |a n| * |b n| ≤ |a n| * (|u| + ε):= by exact
    Mathlib.Tactic.LinearCombination.mul_const_lt_weak h1 h2_1
  have h3: |a n| * (|u| + ε) < ε1 * (|u| + ε):=
  by exact
    (mul_lt_mul_iff_of_pos_right h0).mpr hA
  change |a n| * (|u| + ε) < (ε / (|u| + ε)) * (|u| + ε) at h3
  rw [div_mul_rw] at h3
  exact lt_of_le_of_lt h2 h3
  exact Ne.symm (ne_of_lt h0)




/-- If `a(n)` tends to nonzero, then their product tends t * u. -/
theorem tendsTo_nonzero_mul_tendsTo (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t)
    (hb : TendsTo b u) (ht: t ≠ 0):
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_def] at ha
  rw [tendsTo_def] at hb
  rw [tendsTo_def]

  intro ε hε
  let ε1 := ε / (2 * |u| + ε / |t|)
  have h0: |t| > 0:= by exact abs_pos.mpr ht
  have h0_2: ε / |t| > 0:= by exact div_pos hε h0
  have h0_3: 0 ≤ |u| := by exact abs_nonneg u
  have h0_4: (2: ℝ) > 0 := by exact two_pos
  have h0_5: 2 * |u| ≥ 0 := by exact (mul_nonneg_iff_of_pos_left h0_4).mpr h0_3
  have h0_6: 2 * |u| + ε / |t| > 0:= by exact add_pos_of_nonneg_of_pos h0_5 h0_2
  have h0_7: ε / (2 * |u| + ε / |t|) > 0:= by exact div_pos hε h0_6
  have h0_8: 2 * |t| > 0 := by exact mul_pos h0_4 h0
  have h0_9: ε / (2 * |t|) > 0:= by exact div_pos hε h0_8
  have h0_10: |u| + ε / (2 * |t|) > 0:= by exact add_pos_of_nonneg_of_pos h0_3 h0_9
  have h0_11: |u| + ε / (2 * |t|) ≠ 0 := by exact Ne.symm (ne_of_lt h0_10)
  have h0_12: |t| ≠ 0:= by exact abs_ne_zero.mpr ht
  have hε1 : ε1 > 0 := by exact h0_7


  let ε2 := ε / (2 * |t|)
  have h0_8: 2 * |t| >  0:= by exact mul_pos h0_4 h0
  have h0_9: ε / (2 * |t|) > 0:= by exact div_pos hε h0_8
  have hε2 : ε2 > 0 := by exact h0_9
  clear h0_2 h0_3 h0_4 h0_5 h0_6 h0_7 h0_8 h0_9 h0_10

  specialize ha ε1 hε1
  specialize hb ε2 hε2
  cases' ha with A hA
  cases' hb with B hB
  use max A B
  intro n hn
  apply sup_le_iff.mp at hn
  cases' hn with ha hb
  specialize hA n ha
  specialize hB n hb

  have h1: |a n * b n - t * u| = |(a n * b n - b n * t) + (b n * t - t * u)| := by simp
  rw [h1]
  have h2: |(a n * b n - b n * t) + (b n * t - t * u)| = |b n  * (a n - t) + t * (b n - u)| :=
  by ring_nf
  rw [h2]
  clear h1 h2

  have h3: |b n  * (a n - t) + t * (b n - u)| ≤ |b n  * (a n - t)| + |t * (b n - u)| :=
  by exact abs_add_le (b n * (a n - t)) (t * (b n - u))
  have h4_0: |b n  * (a n - t)| = |b n| * |a n - t|:= by exact abs_mul (b n) (a n - t)
  have h4_1: |t * (b n - u)| = |t| * |b n - u| := by exact abs_mul t (b n - u)
  have h4: |b n  * (a n - t)| + |t * (b n - u)| = |b n|  * |a n - t| + |t| * |b n - u| :=
  by exact
    Mathlib.Tactic.LinearCombination.add_eq_eq h4_0 h4_1
  clear h4_0 h4_1
  have h5: |b n  * (a n - t) + t * (b n - u)| ≤ |b n|  * |a n - t| + |t| * |b n - u| :=
  by exact le_of_le_of_eq h3 h4
  clear h3 h4

  have h6_0: |b n|  ≥ 0:= by exact abs_nonneg (b n)
  have h6_1: |b n|  * |a n - t| ≤ |b n| * ε1:= by exact
    Mathlib.Tactic.LinearCombination.mul_const_lt_weak hA h6_0
  have h6_2: |t| * |b n - u| < |t| * ε2 := by exact (mul_lt_mul_left h0).mpr hB
  have h6: |b n|  * |a n - t| + |t| * |b n - u| < |b n| * ε1 + |t| * ε2 :=
  by exact
    add_lt_add_of_le_of_lt h6_1 h6_2
  clear h6_0 h6_1 h6_2

  have h7: |b n  * (a n - t) + t * (b n - u)| < |b n| * ε1 + |t| * ε2 :=
  by exact lt_of_le_of_lt h5 h6
  clear h5 h6

  have h8_1: |b n| - |u| ≤ |b n - u| := by exact abs_sub_abs_le_abs_sub (b n) u
  have h8_2: |b n| - |u| < ε2 := by exact lt_of_le_of_lt h8_1 hB
  have h8: |b n| < |u| + ε2 := by exact lt_add_of_tsub_lt_left h8_2
  clear h8_1 h8_2


  have h9_1: |b n| * ε1 < (|u| + ε2) * ε1 := by exact (mul_lt_mul_iff_of_pos_right hε1).mpr h8
  have h9: |b n| * ε1 + |t| * ε2 < (|u| + ε2) * ε1 + |t| * ε2 :=
  by exact
    (add_lt_add_iff_right (|t| * ε2)).mpr h9_1
  clear h9_1


  change |b n| * ε1 + |t| * ε2 < (|u| + ε2) * ε1 + |t| * (ε / (2 * |t|)) at h9

  have h10: |t| * (ε / (2 * |t|)) = (ε / (2 * |t|)) * |t|:=
  by exact CommMonoid.mul_comm |t| (ε / (2* |t|))
  have h11_1: ε / (2 * |t|) = (ε / 2) / |t|:= by exact div_mul_eq_div_div ε 2 |t|
  have h11: (ε / (2 * |t|)) * |t| = (ε / 2) / |t| * |t| :=
  by exact
    congrFun (congrArg HMul.hMul h11_1) |t|
  clear h11_1
  rw [div_mul_rw] at h11
  rw [h11] at h10
  nth_rewrite 2 [h10] at h9
  change |b n| * ε1 + |t| * ε2 < (|u| + ε / (2 * |t|)) * (ε / (2 * |u| + ε / |t|))+ ε / 2 at h9


  have h12_1: 2 / 2 * ε / |t| = ε / |t| := by simp
  have h12_2: 2 * ε / 2 / |t| = 2 / 2 * ε / |t|:= by simp
  have h12_3: (2 * ε) / (2 * |t|) = 2 * ε / 2 / |t| := by exact Eq.symm (div_div (2 * ε) 2 |t|)
  have h12_4: 2 * (ε / (2 * |t|)) = (2 * ε) / (2 * |t|):=
  by exact
    Eq.symm (mul_div_assoc 2 ε (2 * |t|))
  rw [h12_3] at h12_4
  rw [h12_2] at h12_4
  rw [h12_1] at h12_4
  clear h12_1 h12_2 h12_3
  have h12_5: 2 * |u| + ε / |t| = 2 * |u| + 2 * (ε / (2 * |t|)):=
  by exact
    congrArg (HAdd.hAdd (2 * |u|)) (id (Eq.symm h12_4))
  have h12_6: 2 * |u| + 2 * (ε / (2 * |t|)) = 2 * (|u| + ε / (2 * |t|)):=
  by exact
    Eq.symm (LeftDistribClass.left_distrib 2 |u| (ε / (2 * |t|)))
  have h12_7: 2 * |u| + ε / |t| = 2 * (|u| + ε / (2 * |t|)) :=
  by exact
    Eq.symm (CancelDenoms.add_subst rfl h12_4)
  clear h12_5 h12_6 h12_4
  have h12_8: (|u| + ε / (2 * |t|)) * (ε / (2 * |u| + ε / |t|)) =
  (|u| + ε / (2 * |t|)) * (ε / (2 * (|u| + ε / (2 * |t|)))):=
  by exact
    congrArg (HMul.hMul (|u| + ε / (2 * |t|))) (congrArg (HDiv.hDiv ε) h12_7)
  have h12_9: (|u| + ε / (2 * |t|)) * (ε / (2 * (|u| + ε / (2 * |t|)))) =
  (ε / (2 * (|u| + ε / (2 * |t|)))) * (|u| + ε / (2 * |t|)):=
  by exact
    CommMonoid.mul_comm (|u| + ε / (2 * |t|)) (ε / (2 * (|u| + ε / (2 * |t|))))
  have h12_10: (ε / (2 * (|u| + ε / (2 * |t|)))) = (ε / 2) / (|u| + ε / (2 * |t|)):=
  by exact
    div_mul_eq_div_div ε 2 (|u| + ε / (2 * |t|))
  have h12_11: (ε / (2 * (|u| + ε / (2 * |t|)))) * (|u| + ε / (2 * |t|)) =
  (ε / 2) / (|u| + ε / (2 * |t|)) * (|u| + ε / (2 * |t|)) :=
  by exact
    congrFun (congrArg HMul.hMul h12_10) (|u| + ε / (2 * |t|))

  rw [div_mul_rw] at h12_11
  rw [←h12_9, ←h12_8] at h12_11
  have h12: (|u| + ε / (2 * |t|)) * (ε / (2 * |u| + ε / |t|)) = ε / 2 := by exact h12_11
  rw [h12] at h9
  clear h8 h10 h11 h12 h12_11 h12_10 h12_9 h12_8 h12_7

  have h13: ε / 2 + ε / 2 = ε := by exact add_halves ε
  have h15: |b n| * ε1 + |t| * ε2 < ε := by exact lt_of_lt_of_eq h9 h13
  clear h9
  exact gt_trans h15 h7
  assumption
  assumption





theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  by_cases ht: t ≠ 0
  apply tendsTo_nonzero_mul_tendsTo
  <;> assumption
  have ht2 : t = 0 := by exact not_not.mp ht
  rw [ht2]
  simp
  apply tendsTo_zero_mul_tendsTo
  exact ht2
  rw [ht2] at ha
  exact ha
  exact hb



-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  rw [tendsTo_def] at hs
  rw [tendsTo_def] at ht
  by_contra h
  change s ≠ t at h
  have h1: |s - t| > 0 := by exact abs_sub_pos.mpr h
  have h2: |s - t| / 2 > 0 := by exact half_pos h1
  let ε2 := |s - t| / 2
  specialize hs ε2 h2
  specialize ht ε2 h2
  cases' hs with B hB
  cases' ht with A hA
  specialize hB (max A B)
  specialize hA (max A B)
  have hA2: A ≤ max A B := by exact Nat.le_max_left A B
  apply hA at hA2
  have hB2: B ≤ max A B := by exact Nat.le_max_right A B
  apply hB at hB2
  have h3: |a (A ⊔ B) - t| + |a (A ⊔ B) - s| < ε2 + ε2:= by exact add_lt_add hA2 hB2
  rw [Eq.symm (abs_neg (a (A ⊔ B) - s)),  Eq.symm (mul_two ε2)] at h3
  have h4: |a (A ⊔ B) - t + (-(a (A ⊔ B) - s))| ≤ |a (A ⊔ B) - t| + |(-(a (A ⊔ B) - s))|:=
  by exact abs_add_le (a (A ⊔ B) - t) (-(a (A ⊔ B) - s))
  have hF: |a (A ⊔ B) - t + (-(a (A ⊔ B) - s))| < ε2 * 2:= by exact lt_of_le_of_lt h4 h3
  simp at hF
  change |s - t| < |s - t| / 2 * 2 at hF
  rw [div_mul_rw] at hF
  apply ne_of_lt at hF
  trivial
  exact Ne.symm (NeZero.ne' 2)

end Section2sheet6
