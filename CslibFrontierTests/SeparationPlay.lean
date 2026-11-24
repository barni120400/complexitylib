/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Groups
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Tests of the play: the hypotheses of `Play.value_move` hold for the simplest move, which cuts
one current unit by summing over its common content, and `Play.value_groups` with every party in
its own group cuts every unit between two different parties. -/

namespace CslibFrontierTests.SeparationPlay

open Finset Cslib.Circuits.Arithmetic.Separation.Play

variable {F A U W : Type} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U] [Fintype W]
  [DecidableEq W]

/-- Cutting one current unit `u`, with no new units: the condition that its two copies agree is
the sum, over a content `o`, of the table "both copies are `o`". -/
example [Semiring F] (h : U → Bool → A) (e : W) {Seen Cur : Finset U} {u : U} (hu : u ∈ Cur)
    (hCur : Cur ⊆ Seen) (E : (A → U → W) → F) :
    value h e Seen Cur E = ∑ o : W, value h e Seen (Cur \ {u}) fun y =>
      E y * if y (h u false) u = o ∧ y (h u true) u = o then 1 else 0 := by
  have hext : ∀ (y : A → U → W) (z : U → W), extend h ∅ y z = y := fun y z => by
    funext a v
    simp [extend]
  have hcommon : common e (∅ : Finset U) = {fun _ => e} := by
    ext z
    simp [funext_iff]
  have key := value_move h e (singleton_subset_iff.2 hu) hCur (fun _ : W => ∅)
    (fun _ => disjoint_empty_right _) E (fun _ y z => by rw [hext])
    (fun o y => if y (h u false) u = o ∧ y (h u true) u = o then 1 else 0)
    (fun y _ _ => by
      simp only [hcommon, sum_singleton, hext, Agree, mem_singleton, forall_eq]
      by_cases hy : y (h u false) u = y (h u true) u
      · simp [hy]
      · have hne : ∀ o, ¬(y (h u false) u = o ∧ y (h u true) u = o) :=
          fun o ho => hy (ho.1.trans ho.2.symm)
        simp [hy, hne])
  simpa using key

/-- With every party in its own group, the cut units are the current units between two different
parties. -/
example (h : U → Bool → A) (Cur : Finset U) (u : U) :
    u ∈ cutUnits h id Cur ↔ u ∈ Cur ∧ h u false ≠ h u true :=
  mem_cutUnits

end CslibFrontierTests.SeparationPlay
