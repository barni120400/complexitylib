/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Data/Nat/Defs.lean` or cslib)

public import Complexity.Init

/-!
# Dividing repeatedly by a power and quotient-remainder arithmetic

Facts about `n / b ^ j` for the stages of an argument that divides a quantity by `b` at each step,
and exact quotient identities for division by `m` with remainder strictly below `m`.

## Main results

* `Nat.le_div_pow_of_mul_pow_le`: lower bound on `n / b ^ j` when `a * b ^ d ≤ n` and `j ≤ d`.
* `Nat.mul_div_pow_succ_le`: `b * (n / b ^ (j + 1)) ≤ n / b ^ j`.
* `Nat.mul_add_div_of_lt`, `Nat.add_mul_div_of_lt`: dividing `k * m + i` or `i + k * m` by `m`
  when `i < m` yields `k`.
* `Nat.mul_add_div_fin`, `Nat.add_mul_div_fin`: the same for `i : Fin m`.
-/

@[expose] public section

namespace Nat

/-- If `a b ^ d ≤ n`, then `a ≤ n / b ^ j` for every `j ≤ d`. -/
theorem le_div_pow_of_mul_pow_le {a b d j n : ℕ} (hb : 0 < b) (hj : j ≤ d) (h : a * b ^ d ≤ n) :
    a ≤ n / b ^ j := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hb)]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb hj)) h

/-- Dividing by one more power of `b`: `b (n / b ^ (j + 1)) ≤ n / b ^ j`. -/
theorem mul_div_pow_succ_le (n b j : ℕ) : b * (n / b ^ (j + 1)) ≤ n / b ^ j := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

/-- Dividing `k * m + i` by `m` when `i < m` yields `k`. -/
theorem mul_add_div_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (k * m + i) / m = k := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi,
    Nat.zero_add]

/-- Dividing `i + k * m` by `m` when `i < m` yields `k`. -/
theorem add_mul_div_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (i + k * m) / m = k := by
  rw [Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.zero_add]

/-- Dividing `m * k + i` by `m` when `i < m` yields `k`. -/
theorem mul_add_div_left_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (m * k + i) / m = k := by
  rw [Nat.mul_comm m k, mul_add_div_of_lt k hi]

/-- Dividing `i + m * k` by `m` when `i < m` yields `k`. -/
theorem add_mul_div_left_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (i + m * k) / m = k := by
  rw [Nat.mul_comm m k, add_mul_div_of_lt k hi]

/-- Dividing `k * m + i` by `m` for `i : Fin m` yields `k`. -/
theorem mul_add_div_fin (k : ℕ) {m : ℕ} (i : Fin m) : (k * m + i) / m = k :=
  mul_add_div_of_lt k i.isLt

/-- Dividing `i + k * m` by `m` for `i : Fin m` yields `k`. -/
theorem add_mul_div_fin (k : ℕ) {m : ℕ} (i : Fin m) : (i + k * m) / m = k :=
  add_mul_div_of_lt k i.isLt

end Nat
