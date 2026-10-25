/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Occurrence

/-! Literal-position counting regressions for actual planarization paths. -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity.SAT.PlanarCompile Cslib.Orthogonal

private def repeated : CNF ℕ := [[(0, true), (0, false), (0, true)]]

example : (Cslib.Logic.PL.occurrences repeated).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences repeated).map (occurrencePath repeated) = paths repeated :=
  occurrencePaths_eq_paths _

example : (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 2 := by decide

example : (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((0, 0), none) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count
    ((1, 0), some (Crossover.splitTerminal 0)) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count
    ((1, 0), some (Crossover.splitTerminal 1)) = 1 := by decide

example : (pathSignals [(1, 0)] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 0 := by decide

example (positive : Bool) :
    (CNF.vars ((links [] positive [(0, 0), (1, 0), (2, 0)]).map Prod.fst)).count ((1, 0), none) +
      [(lastLiteral [] [(0, 0), (1, 0), (2, 0)] positive).1.1].count ((1, 0), none) ≤ 2 := by
  simpa only [show (pathSignals [] [(0, 0), (1, 0), (2, 0)]).count ((1, 0), none) = 2 by decide]
    using count_links_lastLiteral_le [] positive [(0, 0), (1, 0), (2, 0)] (by decide) ((1, 0), none)

example (i : Fin 4) : Crossover.splitFormula.vars.count (Crossover.splitTerminal i) = 2 :=
  count_vars_splitTerminal i

example (v : Crossover.SplitVariable) : Crossover.splitFormula.vars.count v ≤ 3 :=
  count_vars_splitFormula v
