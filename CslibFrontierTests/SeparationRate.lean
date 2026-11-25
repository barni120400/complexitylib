/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Permanent
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Rate
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.MainTheorem
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube

/-! Tests of the rate in the flat case (Proposition E.10, Theorem E.11) and of the main theorems
(Theorems L.1, L.2, Corollary L.3), as a client that sees only the public statements.

* Proposition E.10 over `ℚ` at `k = 4` and `ℓ = 200 = 100 √4`: `ℚ` is in the contracting case, or
  circuits for `f_{4,200}` have at least `2 ^ 100` nodes.
* Theorem E.11 over `ℚ`, and the flat case for the Hamiltonian cycle polynomial with one `m₀` for
  all fields in the flat case.
* From Proposition E.10 to the bound in `log m`, for the sizes `s ≥ 2 ^ m`.
* Theorems L.1 and L.2 and Corollary L.3 over `ℝ` as stated in the paper, and Corollary L.3 over
  `ZMod 2` with the Hamiltonian cycle polynomial. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationRate

open Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Flat Cslib.Circuits.Arithmetic.Separation.TwoCases

/-! ### The flat case -/

/-- **Proposition E.10 over `ℚ`** at `k = 4` and `ℓ = 200 = 100 √4`: `ℚ` is in the contracting
case, or every circuit for `f_{4,200}` has at least `2 ^ (200 · 4 ^ (3/2) / 16) = 2 ^ 100`
nodes. -/
example : ContractingCase ℚ ∨
    ∀ s : ℕ, ComputedWithin (networkPolynomial ℚ 4 200) s → (2 : ℝ) ^ (100 : ℝ) ≤ s := by
  refine (flatCase_or_contractingCase ℚ).symm.imp_right fun hK s hs => ?_
  have h4 : ((4 : ℕ) : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  have h := networkPolynomial_size_ge_of_sqrt_le hK (by norm_num)
    (by rw [h4, Real.rpow_two, Real.sqrt_sq zero_le_two]; norm_num) hs
  rwa [h4, ← Real.rpow_mul zero_le_two, show (2 : ℝ) * (3 / 2) = 3 by norm_num,
    show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num, show ((200 : ℕ) : ℝ) * 8 / 16 = 100 by norm_num] at h

/-- **Theorem E.11 over `ℚ`**: the permanent has more than `2 ^ ((log m)^{4/3} / 1600²)` nodes for
large `m`, or `ℚ` is in the contracting case. -/
example : (∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin ((permFamily ℚ).poly m) s →
    (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s) ∨ ContractingCase ℚ :=
  (flatCase_or_contractingCase ℚ).imp (fun hK => hK.perm_size_gt two_ne_zero) id

/-- **The flat case for the Hamiltonian cycle polynomial**, which is complete for grid sums with
blow-up `40`, with one `m₀` for all fields in the flat case. -/
example : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], FlatCase K → ∀ m ≥ m₀, ∀ s,
    ComputedWithin ((hcFamily K).poly m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s :=
  let ⟨m₀, h⟩ := size_gt_of_gridComplete 40
  ⟨m₀, fun K _ hK => h K hK _ gridComplete_hcFamily⟩

/-- **From Proposition E.10 to the bound in `log m`**, for the sizes `s ≥ 2 ^ m`: these satisfy
the bound of Proposition E.10 for `5 s` when `k³ ℓ 2^{kℓ} ≤ m`, as `ℓ k^{3/2} / 16 ≤ k³ ℓ ≤ m`. -/
example : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ, 2 ^ m ≤ s →
    (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := exists_two_rpow_lt_of_networkPolynomial 1
  refine ⟨m₀, h _ fun k ℓ m s hk _ _ hm hs => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have h1 : (ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16 ≤ m := by
    have h2 := Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num : (3 / 2 : ℝ) ≤ (3 : ℕ))
    have h3 : (k : ℝ) ^ 3 * ℓ ≤ m := by
      exact_mod_cast (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans (by simpa using hm)
    rw [Real.rpow_natCast] at h2
    nlinarith [Nat.cast_nonneg (α := ℝ) ℓ]
  calc (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 16) ≤ 2 ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two h1
    _ ≤ ((5 * s : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hs.trans (Nat.le_mul_of_pos_left s (by norm_num))

/-! ### The main theorems -/

/-- **Theorem L.1 as stated**: there are `c > 0` and `m₀` such that for `m ≥ m₀` every circuit
over `ℝ` for `PERM_m` has more than `m ^ (c (log m)^{1/3})` nodes; here `c = 1 / 1600²`. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s : ℕ,
    ComputedWithin ((permFamily ℝ).poly m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s := by
  obtain ⟨m₀, h⟩ := GridComplete.size_gt (gridComplete_permFamily (two_ne_zero (α := ℝ)))
  exact ⟨1 / 1600 ^ 2, by norm_num, m₀, fun m hm s hs => by
    rw [one_div_mul_eq_div]
    exact h m hm s hs⟩

/-- **Theorem L.2 as stated**: for every `C` there is `m₀` such that for `m ≥ m₀` no circuit over
`ℝ` with at most `m ^ C` nodes computes `PERM_m`. -/
example (C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ ComputedWithin ((permFamily ℝ).poly m) (m ^ C) :=
  GridComplete.not_computedWithin_pow (gridComplete_permFamily two_ne_zero) C

/-- **Corollary L.3 as stated**: over `ℝ`, `VP` is a proper subset of `VNP`. -/
example : VP ℝ ⊂ VNP ℝ :=
  GridComplete.VP_ssubset_VNP (gridComplete_permFamily two_ne_zero) permFamily_mem_VNP

/-- **Corollary L.3 in characteristic `2`**, with the Hamiltonian cycle polynomial in place of the
permanent: over `ZMod 2`, `VP` is a proper subset of `VNP`. -/
example : VP (ZMod 2) ⊂ VNP (ZMod 2) :=
  GridComplete.VP_ssubset_VNP gridComplete_hcFamily hcFamily_mem_VNP

end CslibFrontierTests.SeparationRate
