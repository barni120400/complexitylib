/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath

/-! Concrete finite occupancy and crossing-neighborhood regressions. -/

open Cslib.Complexity Cslib.Orthogonal

private def exampleGraph : Graph := ([0, 1, 2, 3, 4, 5], [(0, 2), (1, 3), (4, 5)])

private theorem declared : ∀ e ∈ exampleGraph.2, e.1 ∈ exampleGraph.1 ∧ e.2 ∈ exampleGraph.1 := by
  intro e he
  simp only [exampleGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem loopless : ∀ e ∈ exampleGraph.2, e.1 ≠ e.2 := by
  intro e he
  simp only [exampleGraph, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> decide

private theorem degree : ∀ v, exampleGraph.incidenceVertices.count v ≤ 3 := by
  have hn : exampleGraph.incidenceVertices.Nodup := by decide
  exact fun v => (List.nodup_iff_count_le_one.1 hn v).trans (by decide)

private def crossing : Point := (10, 50)

private theorem first_member : crossing ∈ exampleGraph.unitPath 0 := by decide

private theorem second_member : crossing ∈ exampleGraph.unitPath 1 := by decide

private theorem not_center : crossing ∉ exampleGraph.orthogonalPositions := by decide

private theorem strict_crossing : exampleGraph.BridgeStemCrossing 0 1 false crossing := by
  change Transverse (2, 50) (18, 50) (10, 12) (10, 52) (realPoint (10, 50))
  norm_num [Transverse, realPoint]

example : exampleGraph.unitPaths.length = 3 := by decide

example : exampleGraph.unitPath 3 = [] := by decide

example : (exampleGraph.unitPath 0).head? = some (4, 4) ∧
    (exampleGraph.unitPath 0).getLast? = some (20, 20) := by decide

example : StraightThrough (exampleGraph.unitPath 0) crossing (1, 0) ∧
    StraightThrough (exampleGraph.unitPath 1) crossing (0, 1) :=
  strict_crossing.neighbors declared loopless (by decide) (by decide)

example : crossing ∉ exampleGraph.unitPath 2 := by
  intro h
  have hindex := Graph.unitPath_atMostTwo exampleGraph declared loopless degree
    (by decide : 0 < exampleGraph.2.length) (by decide : 1 < exampleGraph.2.length)
    (by decide : 2 < exampleGraph.2.length) (by decide) not_center first_member second_member h
  omega

example : Layout.center 2 ∉ exampleGraph.unitPath 1 := by
  rw [Graph.unitPath_center_iff exampleGraph declared loopless (by decide) (by decide)]
  decide

example : (exampleGraph.unitPath 0).getD 55 crossing = crossing - (1, 0) ∧
    (exampleGraph.unitPath 0).getD 57 crossing = crossing + (1, 0) := by decide

example : (exampleGraph.unitPath 1).getD 39 crossing = crossing - (0, 1) ∧
    (exampleGraph.unitPath 1).getD 41 crossing = crossing + (0, 1) := by decide

example : 0 < 56 ∧ 56 + 1 < (exampleGraph.unitPath 0).length ∧
    (((exampleGraph.unitPath 0).getD 55 crossing = crossing - (1, 0) ∧
      (exampleGraph.unitPath 0).getD 57 crossing = crossing + (1, 0)) ∨
      ((exampleGraph.unitPath 0).getD 55 crossing = crossing + (1, 0) ∧
        (exampleGraph.unitPath 0).getD 57 crossing = crossing - (1, 0))) :=
  (strict_crossing.neighbors declared loopless (by decide) (by decide)).1.getD_neighbors
    (Graph.unitPath_nodup exampleGraph declared loopless (by decide))
    (k := 56) (by decide) (by decide)

example : crossing ∉ (exampleGraph.orthogonalRoutes exampleGraph.canonicalPorts)[0] ∧
    crossing ∉ (exampleGraph.orthogonalRoutes exampleGraph.canonicalPorts)[1] :=
  strict_crossing.not_listed declared (by decide) (by decide)

example : (exampleGraph.unitPath 0).head? ≠ some crossing ∧
    (exampleGraph.unitPath 0).getLast? ≠ some crossing :=
  Graph.unitPath_not_endpoints exampleGraph declared loopless (by decide) not_center

-- The ordinary elbow cell has distinct unit neighbors even though it is a bend.
example : length ((exampleGraph.unitPath 0).getD 1 (2, 4)) (2, 4) = 1 ∧
    length (2, 4) ((exampleGraph.unitPath 0).getD 3 (2, 4)) = 1 :=
  Graph.unitPath_neighbor_lengths exampleGraph declared loopless (by decide)
    (k := 2) (by decide) (by decide) (by decide)

example : (exampleGraph.unitPath 0).getD 1 (2, 4) ≠
    (exampleGraph.unitPath 0).getD 3 (2, 4) :=
  Graph.unitPath_neighbors_distinct exampleGraph declared loopless (by decide)
    (k := 2) (by decide) (by decide) (by decide)

example : crossing ∈ exampleGraph.crossingCandidates exampleGraph.canonicalPorts :=
  Graph.unitPath_shared_mem_crossingCandidates exampleGraph declared loopless degree
    (by decide) (by decide) (by decide) not_center first_member second_member

private def reverseGraph : Graph := ([0, 1, 2, 3, 4, 5], [(2, 0), (3, 1), (4, 5)])

-- Reversing endpoints reverses traversal order while keeping the same horizontal/vertical cell.
example : (reverseGraph.unitPath 0).getD 39 crossing = crossing + (1, 0) ∧
    (reverseGraph.unitPath 0).getD 41 crossing = crossing - (1, 0) := by decide

example : (reverseGraph.unitPath 1).getD 43 crossing = crossing + (0, 1) ∧
    (reverseGraph.unitPath 1).getD 45 crossing = crossing - (0, 1) := by decide

private def star : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3)])

-- A declared source center can have three paths; the nonvertex hypothesis is essential.
example : Layout.center 0 ∈ star.unitPath 0 ∧ Layout.center 0 ∈ star.unitPath 1 ∧
    Layout.center 0 ∈ star.unitPath 2 := by decide
