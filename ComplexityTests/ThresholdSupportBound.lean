/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.SupportBoundAsymptotics
import Complexity.Computability.Circuit.Frontier.TwoSidedWitness

/-! A quantitative regression separating the new direct-support bound from the old balanced-cut
bound. The rectangle-free hypothesis is witnessed at exactly the dimension and threshold used.
This witness is existential and makes no claim of efficient evaluation. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

-- The hypotheses used in the large finite lower-bound client below are jointly satisfiable.
example : ∃ f : Cslib.BooleanFunction 2000000,
    ∀ b : Bool, Frontier.RectangleFree {x | f x = b} 32000016 := by
  simpa using Frontier.exists_twoSided_rectangleFree 2000000

-- The old bound is compatible with 1,050,000 input-reading gates.
example : 2000000 ≤ 2 * (1050000 + 25) := by norm_num

-- The new theorem rules out that budget and in fact forces at least 1,052,028 gates.
example {g : ℕ} (p : Program signature 2000000 g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction 2000000}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} 32000016)
    (hsupport : ∀ gate, (inputSupport p gate).card ≤ 3) :
    1052028 ≤ (inputGates p).card := by
  have h := le_inputGates_of_inputSupport_card_le p readout hreadout hf hsupport 39
    (k := 25) (by norm_num)
  norm_num at h
  have hsqrt : Real.sqrt 4000000 = 2000 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [hsqrt] at h
  by_contra! hsmall
  have hq : (inputGates p).card ≤ 1052027 := by omega
  have hqR : ((inputGates p).card : ℝ) ≤ 1052027 := by exact_mod_cast hq
  linarith

-- The three-input coefficient is a strict improvement over one half.
example : (1 : ℝ) / (2 * (1 - (1 / 2 : ℝ) ^ 3)) = 4 / 7 ∧ (1 / 2 : ℝ) < 4 / 7 := by
  norm_num
