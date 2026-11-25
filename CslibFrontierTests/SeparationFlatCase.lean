/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkProjection
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube

/-! Tests of the network polynomial in the flat case, as a client that sees only the public
statements.

* What the node `0` of two nodes sees, a variable of the network polynomial on the views; circuits
  for that polynomial are circuits for the network polynomial.
* Lemma E.3: the network polynomial on two nodes with one bit is an affine projection of the
  Hamiltonian cycle polynomial, so circuits for that family give circuits for it; and a circuit
  for a permanent gives one with five times as many nodes.
* The tensor `T_{2,1}`: its entry is `1` where both ends of the wire hold the same string and `0`
  otherwise; the support point is `1` at it and at the tensor of Lemma A.3 for its two ends.
* Balanced sets of three nodes. A variable is computed with one node, so the tensor of its
  coefficients on the ends of the network on two nodes is covered by the hub tensors.
* Proposition E.5, also for the polynomial on the views as printed in the paper; Theorem E.6, and
  with Definition D.1: over `ℚ`, either the permanent has no circuits of polynomial size or `ℚ` is
  in the contracting case. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatCase

open Finset MvPolynomial Cslib Cslib.PartyTensor Cslib.Circuits.Arithmetic
  Cslib.Circuits.Arithmetic.Separation.Flat Cslib.Circuits.Arithmetic.Separation.TwoCases

/-- The wire of the complete network on two nodes. -/
private def wire01 : Pair 2 := ⟨0, 1, by decide⟩

/-- The node `0` sees the string `true` on its wire to the node `1`. -/
example : NodeView 2 1 := ⟨0, ![fun _ => false, fun _ => true], rfl⟩

/-- A circuit for the network polynomial on the views is one for the network polynomial. -/
example {s : ℕ} (h : ComputedWithin (networkPolynomialOnViews ℚ 2 1) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) s :=
  rename_networkPolynomialOnViews ℚ ▸ h.rename _

/-- Lemma E.3 with the Hamiltonian cycle polynomial, which is complete for grid sums with blow-up
`40`: `f_{2,1}` is an affine projection of the Hamiltonian cycle polynomial on
`40 · 2³ · 1 · 2² = 1280` vertices. -/
example : IsAffineProjection (networkPolynomial ℚ 2 1) ((hcFamily ℚ).poly 1280) :=
  isAffineProjection_networkPolynomial gridComplete_hcFamily le_rfl le_rfl le_rfl

/-- A circuit for the Hamiltonian cycle polynomial on `1280` vertices gives one for `f_{2,1}`
with five times as many nodes. -/
example {s : ℕ} (hs : ComputedWithin ((hcFamily ℚ).poly 1280) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) (5 * s) :=
  hs.of_isAffineProjection
    (isAffineProjection_networkPolynomial gridComplete_hcFamily le_rfl le_rfl le_rfl)

/-- Lemma E.3: over `ℚ`, a circuit for `PERM_96` gives one for `f_{2,1}`, since
`3 · 2³ · 1 · 2² = 96`. -/
example {s : ℕ} (hs : ComputedWithin ((permFamily ℚ).poly 96) s) :
    ComputedWithin (networkPolynomial ℚ 2 1) (5 * s) :=
  computedWithin_networkPolynomial two_ne_zero le_rfl le_rfl le_rfl hs

/-- The entry of `T_{2,1}` where both ends of the wire hold the string `0` is `1`. -/
example : (networkTensor ℤ 2 1).entry (fun _ => (0 : Fin (2 ^ 1))) = 1 := by
  rw [networkTensor_entry, coeff_networkPolynomial, ite_eq_left fun _ => rfl]

/-- The string `0` at the end `false` of every wire and the string `1` at the end `true`. -/
private def differentEnds : (Σ _ : Pair 2, Bool) → Fin (2 ^ 1) := fun a => if a.2 then 1 else 0

/-- The entry of `T_{2,1}` where the ends of the wire hold different strings is `0`. -/
example : (networkTensor ℤ 2 1).entry differentEnds = 0 := by
  rw [networkTensor_entry, coeff_networkPolynomial, ite_eq_right]
  intro h
  exact absurd (congrArg (BitString.equivFin 1) (h wire01)) (by simp [differentEnds])

/-- The support point has wire exponents `0`, so it is `1` at `T_{2,1}` with its ends as parties.
-/
example : SpectralPoint.support ℚ (Σ _ : Pair 2, Bool) (push id (networkTensor ℚ 2 1)) = 1 := by
  rw [apply_push_networkTensor]
  simp [SpectralPoint.wireExponent_support]

/-- The support point is `1` at the tensor of Lemma A.3 for the ends of `T_{2,1}`, the set `{0}`,
the hubs `o₁ = ⟨wire01, false⟩` and `o₂ = ⟨wire01, true⟩`, and a wire of dimension `3`. -/
example : SpectralPoint.support ℚ (Σ _ : Pair 2, Bool)
    (hubTensor ℚ 1 3 id {0} ⟨wire01, false⟩ ⟨wire01, true⟩) = 1 := by
  rw [apply_hubTensor _ (by norm_num : 1 ≤ 3)]
  simp [SpectralPoint.wireExponent_support]

/-- A set of one of three nodes is balanced, the empty set is not. -/
example : {0} ∈ balancedSets 3 ∧ ∅ ∉ balancedSets 3 := by simp

/-- The tensor of the coefficients of the variable `x_{0,ρ}`, for the view `ρ` of the zero
strings, on the ends of the network on two nodes with one bit, is covered by the hub tensors of
the balanced sets, with a wire of dimension `1` between the hubs. -/
example :
    (push id ((networkTensor ℚ 2 1).withEntry fun z =>
      (X (0, fun _ _ => false) : MvPolynomial (Fin 2 × (Fin 2 → BitString 1)) ℚ).coeff
        (blockMonomial Prod.fst univ (BlockChoice.ofProd univ
          (assemble fun e d => (BitString.equivFin 1).symm (z ⟨e, d⟩)))))).CoveredBy
      fun S : balancedSets 2 => hubTensor ℚ 1 1 id S ⟨wire01, false⟩ ⟨wire01, true⟩ :=
  coveredBy_hubTensor (computedWithin_X _) le_rfl id (fun _ => ⟨wire01, false⟩)
    fun _ => ⟨wire01, true⟩

/-- Proposition E.5 for the network polynomial on the views, with its variables as printed. -/
example {K : Type} [Field K] (hK : FlatCase K) {k : ℕ} (hk : 2 ≤ k) :
    ∃ ℓ₀ : ℕ, ∀ ℓ ≥ ℓ₀, ∀ s : ℕ, ComputedWithin (networkPolynomialOnViews K k ℓ) s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 6) ≤ s := by
  obtain ⟨ℓ₀, h⟩ := networkPolynomial_size_ge hK hk
  exact ⟨ℓ₀, fun ℓ hℓ s hs => h ℓ hℓ s (rename_networkPolynomialOnViews K ▸ hs.rename _)⟩

/-- Theorem E.6 and Definition D.1: over `ℚ`, either no circuit with at most `m ^ 3` nodes
computes `PERM_m` for all large `m`, or `ℚ` is in the contracting case. -/
example : (∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ ComputedWithin ((permFamily ℚ).poly m) (m ^ 3)) ∨
    ContractingCase ℚ :=
  (flatCase_or_contractingCase ℚ).imp
    (fun hK => not_computedWithin_permFamily hK two_ne_zero 3) id

end CslibFrontierTests.SeparationFlatCase
