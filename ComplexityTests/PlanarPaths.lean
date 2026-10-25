/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy

/-! Source occurrence indices retain multiplicity and literal order. -/

open Cslib.Logic.PL Cslib.Complexity.SAT.PlanarCompile

private def repeated : CNF ℕ := [[(0, true), (0, false), (0, true)], []]

example : (Cslib.Logic.PL.occurrences repeated).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences repeated).length = 3 := by decide

example : (Cslib.Logic.PL.occurrences repeated).map (occurrencePath repeated) = paths repeated :=
  occurrencePaths_eq_paths _

example : (Cslib.Logic.PL.occurrences ([] : CNF ℕ)).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences ([[]] : CNF ℕ)).map (occurrencePath [[]]) = paths [[]] :=
  occurrencePaths_eq_paths _

-- This client imports no global Geometry or degree-count module.
private def single : CNF ℕ := [[(0, true)]]

private theorem single_width : ∀ c ∈ single, c.length ≤ 3 := by
  intro c hc
  simp only [single, List.mem_singleton] at hc
  subst c
  decide

private theorem single_count : ∀ v, single.vars.count v ≤ 3 := by
  intro v
  by_cases hv : v = 0
  · subst v
    decide
  · simp [single, CNF.vars, Ne.symm hv]

example : ((paths single).filter fun r => r.contains (3, 4)).length ≤ 1 :=
  paths_filter_length_le_one single_width single_count (by decide +kernel) (by decide)

example : ((paths single).filter fun r => r.contains (3, 4)).length = 1 := by decide +kernel
