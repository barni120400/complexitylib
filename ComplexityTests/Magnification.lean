/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.Magnification

/-!
# Tests for Hardness Magnification via Circuit-Min-Merge

Signature checks and concrete examples for `MCSPAt`, `validCert`, `evalCert`, `inSubcube`,
`agreesOnPoint`, `CircuitMinMergeLanguage`, and the McKay–Murray–Williams magnification theorems.
-/

namespace Cslib.MCSP.Tests.Magnification

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Cslib.MCSP Turing.MultiTapeTM

/-! ### Signature checks -/

example : (ℕ → ℕ) → Language Bool := MCSPAt

example (hNP : NP encBits ⊆ PPolyOn encBits) :
    CircuitMinMergeLanguage ∈ PPolyOn encMerge :=
  circuitMinMergeLanguage_mem_PPolyOn hNP

example (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ c > 0, ∀ (s : ℕ → ℕ) (n : ℕ),
      complexity interpretation (single ((MCSPAt s).slice (2 ^ n))) ≤
        2 ^ n * c * (n + s n + 1) ^ c :=
  exists_complexity_MCSPAt_le_of_NP_subset_PPoly hNP

example (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) :
    ∃ c > 0, ∀ n : ℕ,
      complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n))) ≤
        2 ^ n * c * (n + 1) ^ c :=
  exists_complexity_MCSPAt_pow_le_of_NP_subset_PPoly hNP k

example
    (h : ∀ c > 0, ∃ (s : ℕ → ℕ) (n : ℕ),
      2 ^ n * c * (n + s n + 1) ^ c <
        complexity interpretation (single ((MCSPAt s).slice (2 ^ n)))) :
    ¬ (NP encBits ⊆ PPolyOn encBits) :=
  not_NP_subset_PPoly_of_MCSPAt_hard h

example
    (h : ∀ c > 0, ∃ (s : ℕ → ℕ) (n : ℕ),
      2 ^ n * c * (n + s n + 1) ^ c <
        complexity interpretation (single ((MCSPAt s).slice (2 ^ n)))) :
    P encBits ≠ NP encBits :=
  P_ne_NP_of_MCSPAt_hard h

example (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ,
      2 ^ n * c * (n + 1) ^ c <
        complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n)))) :
    ¬ (NP encBits ⊆ PPolyOn encBits) :=
  not_NP_subset_PPoly_of_MCSPAt_pow_hard k h

example (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ,
      2 ^ n * c * (n + 1) ^ c <
        complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n)))) :
    P encBits ≠ NP encBits :=
  P_ne_NP_of_MCSPAt_pow_hard k h

/-! ### Concrete checks -/

-- The projection `x ↦ x 0` on 1 input has circuit complexity 0, so its truth table lies in
-- `MCSPAt (fun _ => 0)`.
example : List.ofFn (truthTable 1 (fun x : BitString 1 => x 0)) ∈ MCSPAt (fun _ => 0) := by
  rw [ofFn_mem_MCSPAt_iff, Equiv.symm_apply_apply, complexity_single_proj]

-- At size 0 on 1 input, `[false]` is the valid certificate for the projection `x ↦ x 0`.
example : validCert 1 0 [false] = true := by decide
example : evalCert 1 0 [false] [false] = false := by decide
example : evalCert 1 0 [false] [true] = true := by decide

-- Subcube membership and point agreement on 2-bit inputs.
example : inSubcube [true] [true, false] = true := by decide
example : inSubcube [true] [false, false] = false := by decide
example : agreesOnPoint 2 0 [true] [false, false] [false, false] [false, false] [true, false] =
    true := by decide

-- A concrete yes-instance of `CircuitMinMergeLanguage` at `n = 1, s = 0, p = [], j = 0`:
-- both child certificates `[false]` compute `x ↦ x 0` on `[false]` and `[true]`, and `[false]` is
-- the unique valid size-0 certificate on 1 input.
example : (((1, 0), ([], 0)), [true, false, true, false]) ∈ CircuitMinMergeLanguage := by
  refine ⟨rfl, rfl, [false], ⟨⟨by decide, fun x hx => ?_⟩, fun w' hw' hmerged => ?_⟩, rfl⟩
  · rcases List.length_eq_one_iff.1 hx with ⟨b, rfl⟩
    cases b <;> decide
  · rcases List.length_eq_one_iff.1 hw' with ⟨b, rfl⟩
    cases b <;> decide

end Cslib.MCSP.Tests.Magnification
