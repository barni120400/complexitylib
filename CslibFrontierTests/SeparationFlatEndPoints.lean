/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.EndPoints
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Tests of the ends of the complete network, as a client that sees only the public statements:
the two ends of the wire between two nodes, the two hubs for one of three nodes, and the fact
that two hubs always cost less than the wires. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatEndPoints

open Finset Cslib.Circuits.Arithmetic.Separation.Flat

/-- The two ends of the wire between the two nodes of the complete network on two nodes. -/
example : dist (endPoint (0 : Fin 2) 1) (endPoint 1 0) = 1 := dist_endPoint (by decide)

/-- Three nodes and the set `{0}`: the six ends reach two hubs of norm `1 / (6 √3)` with total
length at most `3 - 1 / 4`, where the three wires have total length `3`. -/
example : ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 / (6 * √(3 : ℕ)) ∧
    ∑ a, ∑ b, (if a = b then 0 else dist (endPoint a b) (if a ∈ ({0} : Finset (Fin 3)) then x
      else -x)) ≤ ((3 : ℕ) : ℝ) * ((3 : ℕ) - 1) / 2 - (3 : ℕ) / 12 :=
  exists_norm_eq_sum_dist_endPoint_le (by decide) {0} (by decide) (by decide)

/-- For a balanced set, two hubs cost less than the `k (k - 1) / 2` wires of length one. -/
example {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin k)) (h1 : k ≤ 3 * A.card)
    (h2 : 3 * A.card ≤ 2 * k) : ∃ x : EuclideanSpace ℝ (Fin k),
    ∑ a, ∑ b, (if a = b then 0 else dist (endPoint a b) (if a ∈ A then x else -x)) <
      (k : ℝ) * (k - 1) / 2 := by
  obtain ⟨x, -, hx⟩ := exists_norm_eq_sum_dist_endPoint_le hk A h1 h2
  have : (0 : ℝ) < k := by exact_mod_cast hk
  exact ⟨x, by linarith⟩

end CslibFrontierTests.SeparationFlatEndPoints
