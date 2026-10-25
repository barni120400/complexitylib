/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.CorrelatedSampling

/-! # Correlated sampling

Parties holding the same distribution always agree, and every party samples its own distribution.
For a point mass against a uniform bit, the agreement bound is `1/3`.
-/

namespace ComplexityTests.CorrelatedSampling

open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

/-- A point mass on `true` and a uniform bit. -/
noncomputable def P : Bool → PMF Bool
  | false => PMF.pure true
  | true => Cslib.Probability.PMF.uniformOfFintype Bool

-- Each party samples its own distribution.
example (i : Bool) : (shared P).map (sample P i) = P i := map_sample i

-- Parties with the same distribution agree with probability one.
example (i : Bool) : 1 ≤ ((shared P).toOuterMeasure {l | sample P i l = sample P i l}).toReal := by
  simpa using agree_ge (P := P) i i

-- The point mass and the uniform bit are at distance `1/2`, so they agree with probability at
-- least `(1 - 1/2) / (1 + 1/2) = 1/3`.
example : 1 / 3 ≤
    ((shared P).toOuterMeasure {l | sample P false l = sample P true l}).toReal := by
  have hd : dist (P false) (P true) = 1 / 2 := by
    rw [Cslib.Probability.PMF.dist_eq]
    simp [P, Cslib.Probability.PMF.uniformOfFintype_apply]
    norm_num
  have h := agree_ge (P := P) false true
  rw [hd] at h
  norm_num at h ⊢
  exact h

/--
info: 'Cslib.Probability.CorrelatedSampling.map_firstIn_weightedOrder' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms map_firstIn_weightedOrder

/--
info: 'Cslib.Probability.CorrelatedSampling.map_sample' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms map_sample

/--
info: 'Cslib.Probability.CorrelatedSampling.agree_ge' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms agree_ge

/--
info: 'Cslib.Probability.CorrelatedSampling.disagree_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms disagree_le

end ComplexityTests.CorrelatedSampling
