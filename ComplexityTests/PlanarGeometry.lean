/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Geometry
import Mathlib.Tactic.NormNum

/-! Actual cell-access routes and compaction with repeated structured variable names. -/

namespace ComplexityTests.PlanarGeometry

open Cslib.Logic.PL Cslib.Orthogonal Cslib.Complexity
open SAT.PlanarCompile

example : IsOrthogonal (access [] (-1, -2) (0, -2)) := access_orthogonal _ _ _
example : IsSimple (access [(-1, -2)] (-1, -2) (-1, -3)) := access_simple _ _ _

example : IsSimple (center (-1, -3) :: access [(-1, -2)] (-1, -2) (-1, -3)) :=
  finalRoute_simple _ (by decide)

example : wireLength (access [(-1, -2)] (-1, -2) (-1, -3)) = 20 := by
  simpa using access_wireLength [(-1, -2)] (-1, -2) (-1, -3)

example : wireLength (center (-1, -3) :: access [] (-1, -2) (-1, -3)) ≤ 240 :=
  finalRoute_wireLength_le _ (by decide)

example : ∀ r ∈ routes [[(7, true)]], IsOrthogonal r ∧ IsSimple r := routes_regular _

example : (routes [[(7, true)]]).length =
    (SAT.incidenceGraph (formula [[(7, true)]])).2.length := routes_length _

example : (occurrencePath [[(7, true)]] (0, 0, (7, true))).Nodup :=
  occurrencePath_nodup (by decide)

-- Even three repeated incidences between the same original vertices use distinct cell ports.
example :
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.flatMap fun e =>
        [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]).Nodup := by
  apply pathPorts_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

example :
    ((paths [[(7, true), (7, false), (7, true)]]).flatMap fun r =>
      r.consecutivePairs.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
  apply pathMidpoints_nodup
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    decide
  · intro v
    exact List.count_le_length.trans (by decide)

example : cellPort 120 (-1, -2) (side (-1, -2) (0, -2)) =
    cellPort 120 (0, -2) (side (0, -2) (-1, -2)) := shared_cellPort (by decide)

example : Disjoint (support (access [(0, 0)] (0, 0) (-1, 0)))
    (support (access [(0, 0)] (0, 0) (0, 1))) :=
  crossing_access_disjoint (by decide) _ _ (by decide)

example : ((180.5 : ℝ), (120 : ℝ)) ∈ support (access [] (0, 0) (1, 0)) := by
  rw [access_eq_pair, support_cons_cons]
  apply Or.inl
  norm_num [cellPort, cellOrigin, side, variablePosition, signal, Cslib.Orthogonal.segment,
    realPoint, mem_horizontal, Set.mem_uIcc]

private def repeatedNames : CNF Variable :=
  [[(((0, 0), none), true), (((0, 0), none), false), (((1, 0), none), true)]]

-- Compact names are first literal positions, whereas graph indices count distinct variables.
example : repeatedNames.compact.distinctVars = [0, 2] := by decide
example : repeatedNames.compact.distinctVars.idxOf (repeatedNames.vars.idxOf ((1, 0), none)) =
    repeatedNames.distinctVars.idxOf ((1, 0), none) :=
  CNF.idxOf_distinctVars_compact _ (by decide)

example : repeatedNames.compact.vars.count (repeatedNames.vars.idxOf ((0, 0), none)) =
    repeatedNames.vars.count ((0, 0), none) := CNF.count_vars_compact _ (by decide)

example {k : ℕ} (h : ∀ v, repeatedNames.vars.count v ≤ k) :
    ∀ i, repeatedNames.compact.vars.count i ≤ k := CNF.count_vars_compact_le _ h

example : SAT.incidenceGraph repeatedNames.compact = SAT.incidenceGraph repeatedNames :=
  SAT.incidenceGraph_compact _

example : (positions [[(7, true)]]).getD
    ((formula [[(7, true)]]).distinctVars.idxOf
      ((rawFormula [[(7, true)]]).vars.idxOf ((4, 4), none))) (0, 0) =
    variablePosition ((4, 4), none) := by
  apply positions_getD_variable
  decide +kernel

end ComplexityTests.PlanarGeometry
