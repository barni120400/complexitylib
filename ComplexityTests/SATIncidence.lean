/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Incidence

/-! Concrete incidence records, including parallel literal incidences and isolated clauses. -/

namespace ComplexityTests.SATIncidence

open Cslib.Complexity Cslib.Logic.PL

-- Vertex names depend on the number of distinct variables, not their numeric magnitudes.
example : SAT.incidenceGraph
    ([[(17, true), (17, false)], [], [(100000000000000000000, false)]] : CNF ℕ) =
    ([0, 1, 2, 3, 4], [(0, 2), (0, 2), (1, 4)]) := by decide

-- An empty clause remains an isolated clause vertex. Repeated clauses have distinct vertices.
example : SAT.incidenceGraph ([[], []] : CNF ℕ) = ([0, 1], []) := by decide

example : SAT.incidenceGraph ([] : CNF ℕ) = ([], []) := by decide

-- The construction works for ordinary finite variable types too.
example : SAT.incidenceGraph ([[(true, false)], [(false, true)]] : CNF Bool) =
    ([0, 1, 2, 3], [(0, 2), (1, 3)]) := by decide

end ComplexityTests.SATIncidence
