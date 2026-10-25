/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths

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
