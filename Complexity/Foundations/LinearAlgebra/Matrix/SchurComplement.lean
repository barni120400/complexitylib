/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Invertibility and Schur complements for 2×2 block matrices over general rings

This module establishes invertibility criteria, factorizations, and explicit inverses for 2×2
block matrices over arbitrary (possibly noncommutative) rings `R`.

Mathlib's `Mathlib.LinearAlgebra.Matrix.SchurComplement` proves analogous results for commutative
rings (`[CommRing α]`). The lemmas here generalize those results to arbitrary rings `[Ring R]`,
which is required when the matrix entries themselves are matrices (e.g. in rational circuit
evaluations).

## Main results

* `Matrix.isUnit_fromBlocks_one_zero₂₁`: an upper unitriangular block matrix is invertible.
* `Matrix.isUnit_fromBlocks_one_zero₁₂`: a lower unitriangular block matrix is invertible.
* `Matrix.isUnit_fromBlocks_diagonal_iff`: a block diagonal matrix is invertible iff both diagonal
  blocks are.
* `Matrix.fromBlocks_zero₂₂_schur_factor`: Schur factorization of a block matrix with a zero
  corner and an invertible corner.
* `Matrix.isUnit_fromBlocks_zero₂₂_iff`: invertibility of a block matrix with a zero corner via
  its Schur complement.
* `Matrix.fromBlocks_zero₂₂_inverse`: explicit inverse for a block matrix with a zero corner.

## References

* [OpenAI2026RationalHitting]
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- An upper unitriangular block matrix is invertible. -/
theorem isUnit_fromBlocks_one_zero₂₁ (B : Matrix ι κ R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) B 0 (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 (-B) 0 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A lower unitriangular block matrix is invertible. -/
theorem isUnit_fromBlocks_one_zero₁₂ (C : Matrix κ ι R) :
    IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 0 (-C) 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- A block diagonal matrix is invertible exactly when both diagonal blocks are. -/
theorem isUnit_fromBlocks_diagonal_iff (A : Matrix ι ι R) (D : Matrix κ κ R) :
    IsUnit (fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  constructor
  · rintro ⟨u, hu⟩
    have hh := u.val_inv
    have hh' := u.inv_val
    rw [hu] at hh hh'
    refine ⟨isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁, ?_, ?_⟩,
      isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂, ?_, ?_⟩⟩
    · have h := congrArg Matrix.toBlocks₁₁ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₁₁ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
  · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
    apply isUnit_iff_exists.mpr
    refine ⟨fromBlocks (↑u⁻¹) 0 0 (↑v⁻¹), ?_, ?_⟩ <;>
      simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- The Schur factorization of a block matrix with a zero corner and an invertible corner. -/
theorem fromBlocks_zero₂₂_schur_factor (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    fromBlocks A B C 0 =
      fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-C * A' * B) *
      fromBlocks 1 (A' * B) 0 1 := by
  simp only [fromBlocks_multiply, add_zero, zero_add,
    one_mul, mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc A A' B, hAA', Matrix.one_mul, Matrix.mul_assoc C A' A, hA'A,
    Matrix.mul_one]
  simp [Matrix.mul_assoc, Matrix.neg_mul]

/-- A block matrix with a zero corner and an invertible corner is invertible exactly when its
Schur complement is. -/
theorem isUnit_fromBlocks_zero₂₂_iff (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    IsUnit (fromBlocks A B C 0) ↔ IsUnit (C * A' * B) := by
  rw [fromBlocks_zero₂₂_schur_factor A A' B C hAA' hA'A]
  obtain ⟨u, hu⟩ := isUnit_fromBlocks_one_zero₂₁ (A' * B)
  obtain ⟨v, hv⟩ := isUnit_fromBlocks_one_zero₁₂ (C * A')
  rw [← hu, ← hv, Units.isUnit_mul_units, Units.isUnit_units_mul, isUnit_fromBlocks_diagonal_iff]
  have hA : IsUnit A := isUnit_iff_exists.mpr ⟨A', hAA', hA'A⟩
  simp [hA, Matrix.neg_mul, IsUnit.neg_iff]

/-- An inverse of a block matrix with a zero corner and an invertible corner, whose corner block
is the inverse of the Schur complement. -/
theorem fromBlocks_zero₂₂_inverse (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (a b : Matrix κ κ R) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (ha : C * A' * B = a) (hab : a * b = 1) (hba : b * a = 1) :
    ∃ M : Matrix (ι ⊕ κ) (ι ⊕ κ) R,
      fromBlocks A B C 0 * M = 1 ∧ M * fromBlocks A B C 0 = 1 ∧
      fromCols (0 : Matrix κ ι R) (-1) * M *
        fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R) = b := by
  let U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 0 (C * A') 1, fromBlocks 1 0 (-(C * A')) 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let V : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 (A' * B) 0 1, fromBlocks 1 (-(A' * B)) 0 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let D : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks A 0 0 (-a), fromBlocks A' 0 0 (-b),
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, hAA', hab],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, hA'A, hba]⟩
  have hS : (↑(U * D * V) : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = fromBlocks A B C 0 := by
    change fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-a) *
      fromBlocks 1 (A' * B) 0 1 = _
    rw [← ha]
    simpa [Matrix.neg_mul] using (fromBlocks_zero₂₂_schur_factor A A' B C hAA' hA'A).symm
  refine ⟨↑(U * D * V)⁻¹, ?_, ?_, ?_⟩
  · rw [← hS]; exact (U * D * V).mul_inv
  · rw [← hS]; exact (U * D * V).inv_mul
  · change fromCols (0 : Matrix κ ι R) (-1) *
      (V.inv * (D.inv * U.inv)) * fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R) = b
    simp [V, D, U, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.fromCols_mul_fromBlocks, fromCols_mul_fromRows,
      Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

end Matrix
