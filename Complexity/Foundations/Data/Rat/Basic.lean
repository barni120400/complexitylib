/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth, OpenAI
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Rat/Lemmas.lean`)

public import Complexity.Init
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Properties of integer quotients `Rat.divInt`

Elementary properties of `Rat.divInt a b`: the reduced numerator magnitude, denominator, and
sign in terms of `Nat.gcd a.natAbs b.natAbs`, and magnitude bounds.

## Main results

* `Rat.divInt_num_natAbs`: numerator magnitude for `b ≠ 0`.
* `Rat.divInt_den_of_ne_zero`: denominator for `b ≠ 0`.
* `Rat.divInt_sign`: sign condition for `b ≠ 0`.
* `Rat.divInt_num_natAbs_eq`: unconditional numerator magnitude.
* `Rat.divInt_den_eq`: unconditional denominator.
* `Rat.divInt_sign_eq`: unconditional sign condition.
* `Rat.divInt_num_natAbs_le`: numerator magnitude bound `|num| ≤ |a|`.
* `Rat.divInt_den_le`: denominator bound `den ≤ |b|`.
-/

@[expose] public section

namespace Rat

/-- Reduced numerator magnitude of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_num_natAbs (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs = a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  rw [Rat.num_divInt,
    Int.natAbs_ediv_of_dvd (dvd_mul_of_dvd_right (Int.gcd_dvd_right b a) b.sign),
    Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hb, Int.natAbs_natCast, one_mul]
  simp only [Int.gcd, Nat.gcd_comm]

/-- Reduced denominator of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_den_of_ne_zero (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).den = b.natAbs / Nat.gcd a.natAbs b.natAbs := by
  simp [Rat.den_divInt, hb, Int.gcd, Nat.gcd_comm]

/-- Sign bit of `Rat.divInt a b` for `b ≠ 0`. -/
theorem divInt_sign (a b : ℤ) (hb : b ≠ 0) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  have hs : (Rat.divInt a b).num < 0 ↔ (a : ℚ) / (b : ℚ) < 0 := by
    rw [← Rat.num_neg, Rat.divInt_eq_div]
  simp only [hs]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    rcases lt_or_gt_of_ne ha with hna | hpa <;> rcases lt_or_gt_of_ne hb with hnb | hpb
    · have hp : (0 : ℚ) < (a : ℚ) / (b : ℚ) :=
        div_pos_of_neg_of_neg (by exact_mod_cast hna) (by exact_mod_cast hnb)
      simp [hna, hnb, not_lt_of_ge hp.le]
    · have hn : (a : ℚ) / (b : ℚ) < 0 :=
        div_neg_of_neg_of_pos (by exact_mod_cast hna) (by exact_mod_cast hpb)
      simp [hna, not_lt_of_gt hpb, hn]
    · have hn : (a : ℚ) / (b : ℚ) < 0 :=
        div_neg_of_pos_of_neg (by exact_mod_cast hpa) (by exact_mod_cast hnb)
      simp [not_lt_of_gt hpa, hnb, hn]
    · have hp : (0 : ℚ) < (a : ℚ) / (b : ℚ) :=
        div_pos (by exact_mod_cast hpa) (by exact_mod_cast hpb)
      simp [not_lt_of_gt hpa, not_lt_of_gt hpb, not_lt_of_ge hp.le]

/-- Reduced numerator magnitude of `Rat.divInt a b` for arbitrary integers `a, b`. -/
theorem divInt_num_natAbs_eq (a b : ℤ) :
    (Rat.divInt a b).num.natAbs =
      if b = 0 then 0 else a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, divInt_num_natAbs a b hb]

/-- Reduced denominator of `Rat.divInt a b` for arbitrary integers `a, b`. -/
theorem divInt_den_eq (a b : ℤ) :
    (Rat.divInt a b).den =
      if b = 0 then 1 else b.natAbs / Nat.gcd a.natAbs b.natAbs := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, divInt_den_of_ne_zero a b hb]

/-- Sign bit of `Rat.divInt a b` for arbitrary integers `a, b`. -/
theorem divInt_sign_eq (a b : ℤ) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else if b = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp only [hb, ↓reduceIte, divInt_sign a b hb]

/-- Reduced numerator magnitude of `Rat.divInt a b` is bounded by `|a|`. -/
theorem divInt_num_natAbs_le (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

/-- Reduced denominator of `Rat.divInt a b` is bounded by `|b|`. -/
theorem divInt_den_le (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).den ≤ b.natAbs := by
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

end Rat
