/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.Sigma

/-!
# Uniqueness of indexed literal occurrences

## Main results

* `Cslib.Logic.PL.occurrences_nodup`: clause and literal indices distinguish all occurrences.
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- Clause and literal indices distinguish every source occurrence, including repeated literals. -/
theorem occurrences_nodup {V : Type*} (φ : CNF V) : (occurrences φ).Nodup := by
  rw [occurrences, List.nodup_flatMap]
  constructor
  · intro c _
    apply List.Nodup.of_map (f := fun o : Occurrence V => o.2.1)
    simpa only [List.map_map, Function.comp_def] using List.nodup_zipIdx_map_snd c.1
  · have h : φ.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
      simpa only [List.Nodup, List.pairwise_map] using List.nodup_zipIdx_map_snd φ
    apply h.imp
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hx
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hy
    exact hab (congrArg (fun o : Occurrence V => o.1) (hi.trans hj.symm))

end Cslib.Logic.PL

