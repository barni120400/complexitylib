/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Matrix/Basic.lean`)

public import Complexity.Init
public import Mathlib.Data.Matrix.Basic

/-!
# Matrix reindexing by permutations

Identities for `Matrix.reindex` when acting symmetrically on rows and columns by permutations:
composition with respect to permutation multiplication, identity action, and pointwise
characterization.

## Main results

* `Matrix.reindex_mul`: `reindex (σ * τ) (σ * τ) M = reindex σ σ (reindex τ τ M)`.
* `Matrix.reindex_one`: `reindex 1 1 M = M`.
* `Matrix.reindex_eq_iff`: `reindex τ τ A = M ↔ ∀ i j, M (τ i) (τ j) = A i j`.
-/

@[expose] public section

namespace Matrix

variable {m α : Type*}

/-- Relabelling a square matrix by a product of permutations is relabelling twice. -/
theorem reindex_mul (σ τ : Equiv.Perm m) (M : Matrix m m α) :
    Matrix.reindex (σ * τ) (σ * τ) M = Matrix.reindex σ σ (Matrix.reindex τ τ M) :=
  (DFunLike.congr_fun (Matrix.reindex_trans τ τ σ σ) M).symm

/-- Relabelling by the identity permutation does nothing. -/
theorem reindex_one (M : Matrix m m α) : Matrix.reindex 1 1 M = M :=
  Matrix.reindex_refl_refl M

/-- `Matrix.reindex τ τ A = M` says that `τ` carries `A` to `M`. -/
theorem reindex_eq_iff {τ : Equiv.Perm m} {A M : Matrix m m α} :
    Matrix.reindex τ τ A = M ↔ ∀ i j, M (τ i) (τ j) = A i j := by
  constructor
  · rintro rfl i j
    simp
  · intro h
    ext i j
    simpa using (h (τ.symm i) (τ.symm j)).symm

end Matrix
