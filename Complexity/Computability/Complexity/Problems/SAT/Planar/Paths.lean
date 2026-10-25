/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Logics.Propositional.CNF.Occurrence
import Mathlib.Data.List.GetD

/-!
# Occurrence order of the actual planarization paths

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.occurrencePaths_eq_paths`: indexed source occurrences
  select exactly the emitted canonical paths in their original order.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL

/-- Enumerating source occurrences selects all actual paths in their original order. -/
theorem occurrencePaths_eq_paths (φ : CNF ℕ) :
    (Cslib.Logic.PL.occurrences φ).map (occurrencePath φ) = paths φ := by
  have hlen : (Cslib.Logic.PL.occurrences φ).length = (paths φ).length := by
    simp [paths, SAT.incidenceGraph]
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    rw [List.getElem_map]
    unfold occurrencePath
    rw [(Cslib.Logic.PL.occurrences_nodup φ).idxOf_getElem i (by simpa using hi),
      List.getD_eq_getElem _ _ hj]

end Cslib.Complexity.SAT.PlanarCompile
