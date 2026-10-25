/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Geometry of the actual finite planar SAT compiler

The lemmas refer to the executable routes and positions in `PlanarCompile` and to their
complete real supports. Cell-local statements cover both the fixed crossover access and
ordinary center spokes. Their translated supports are confined to the corresponding square.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.access_eq_pair`: the actual access route endpoints.
* `Cslib.Complexity.SAT.PlanarCompile.access_orthogonal`,
  `Cslib.Complexity.SAT.PlanarCompile.access_simple`: local route certificates.

## References

The global assembly and coordinate arguments are original. The fixed crossover and its
continuous certificates are credited in `CrossoverLayout`.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- The fixed gadget and cell API use the same four geometric boundary points. -/
theorem cellPort_eq_boundaryPort (p : Point) (s : Fin 4) :
    cellPort 120 p s = cellOrigin 120 p + Crossover.boundaryPort s := by
  fin_cases s <;> rfl

/-- Every actual access route is a single segment from its cell port to its signal variable. -/
theorem access_eq_pair (sites : List Point) (p q : Point) :
    access sites p q = [cellPort 120 p (side p q), variablePosition (signal sites p q)] := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, Crossover.accessRoute, translate, List.map_cons,
      List.map_nil, signal, variablePosition, Option.elim_some, cellPort_eq_boundaryPort]
    simp only [add_comm]
  · simp [access, hp, signal, variablePosition, center]

private theorem spoke_orthogonal (s : Fin 4) :
    IsOrthogonal [Crossover.boundaryPort s, (120, 120)] := by
  fin_cases s <;> norm_num [IsOrthogonal, List.consecutivePairs, AxisAligned,
    Crossover.boundaryPort]

private theorem pair_simple (a b : Point) (h : a ≠ b) : IsSimple [a, b] := by
  simp [IsSimple, List.consecutivePairs, h]

/-- Ordinary access spokes are translates of the same four local straight segments. -/
theorem access_eq_spoke {sites : List Point} {p : Point} (hp : p ∉ sites) (q : Point) :
    access sites p q = translate (cellOrigin 120 p)
      [Crossover.boundaryPort (side p q), (120, 120)] := by
  simp [access, hp, translate, cellPort_eq_boundaryPort, center, add_comm]

/-- The actual access route is proper and orthogonal in both kinds of occupied cell. -/
theorem access_orthogonal (sites : List Point) (p q : Point) :
    IsOrthogonal (access sites p q) := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, isOrthogonal_translate_iff]
    exact (Crossover.access_endpoints (side p q)).1
  · rw [access_eq_spoke hp, isOrthogonal_translate_iff]
    exact spoke_orthogonal _

/-- The actual access route is continuously simple in both kinds of occupied cell. -/
theorem access_simple (sites : List Point) (p q : Point) : IsSimple (access sites p q) := by
  rw [access_eq_pair]
  apply pair_simple
  have h := access_orthogonal sites p q
  rw [access_eq_pair] at h
  exact (h (cellPort 120 p (side p q), variablePosition (signal sites p q))
    (by simp [List.consecutivePairs])).2

/-- Every structured output variable is strictly inside the cell named by its first coordinate.
This includes all gadget variables, not only those selected as access terminals. -/
theorem variablePosition_mem_openCell (v : Variable) :
    realPoint (variablePosition v) ∈ openCell 120 v.1 := by
  rcases v with ⟨p, v⟩
  cases v with
  | none => exact center_mem_openCell (by decide) p
  | some v =>
    rw [variablePosition, Option.elim_some, realPoint_add, add_comm,
      mem_openCell_add_origin_iff]
    have h := Crossover.variable_bounds v
    simp only [realPoint]
    norm_num
    exact_mod_cast (show 0 < (Crossover.variablePosition v).1 ∧
      (Crossover.variablePosition v).1 < 240 ∧ 0 < (Crossover.variablePosition v).2 ∧
      (Crossover.variablePosition v).2 < 240 by omega)

/-- Every translated fixed-gadget incidence stays in the open cell of that gadget. -/
theorem crossingRoute_mem_openCell {e : ℕ × Crossover.SplitVariable × Route}
    (he : e ∈ Crossover.incidenceRoutes) (c : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (translate (cellOrigin 120 c) e.2.2)) : p ∈ openCell 120 c := by
  rw [support_translate] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  rw [mem_openCell_add_origin_iff]
  simpa only [Int.reduceMul, Int.cast_ofNat] using Crossover.core_support_interior he hp

/-- Unit-adjacent integer cells differ by exactly one of the four cardinal displacements. -/
theorem unit_neighbor_cases {p q : Point} (h : Orthogonal.length p q = 1) :
    q = p + (-1, 0) ∨ q = p + (1, 0) ∨ q = p + (0, -1) ∨ q = p + (0, 1) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [Orthogonal.length] at h
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  omega

/-- Neighboring unit cells use exactly the same geometric midpoint for their shared port. -/
theorem shared_cellPort {p q : Point} (h : Orthogonal.length p q = 1) :
    cellPort 120 p (side p q) = cellPort 120 q (side q p) := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    norm_num [side, cellPort, cellOrigin, Prod.ext_iff] <;> omega

private theorem mem_support_pair {a b : Point} {p : ℝ × ℝ} :
    p ∈ support [a, b] ↔ p ∈ segment a b := by
  rw [support_cons_cons]
  have hs : p ∈ support [b] ↔ p = realPoint b := by
    simp [support, List.consecutivePairs]
  rw [Set.mem_union, hs]
  exact ⟨fun h => h.elim id (fun h => h ▸ _root_.right_mem_segment ℝ _ _), Or.inl⟩

private theorem spoke_boundary_isolation (s : Fin 4) {p : ℝ × ℝ}
    (hp : p ∈ support [Crossover.boundaryPort s, (120, 120)]) :
    0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (Crossover.boundaryPort s)) := by
  rw [mem_support_pair] at hp
  fin_cases s <;>
    norm_num [Crossover.boundaryPort, Orthogonal.segment, realPoint, mem_horizontal,
      mem_vertical, Set.mem_uIcc] at hp ⊢
  all_goals
    rcases hp with ⟨heq, hlo, hhi⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    intro h
    rcases h with h | h | h | h <;> apply Prod.ext <;> norm_num <;> linarith

private theorem access_eq_translate (sites : List Point) (p q : Point) :
    access sites p q = translate (cellOrigin 120 p)
      (if p ∈ sites then Crossover.accessRoute (side p q)
        else [Crossover.boundaryPort (side p q), (120, 120)]) := by
  by_cases hp : p ∈ sites
  · simp [access, hp]
  · simpa only [hp, ↓reduceIte] using access_eq_spoke hp q

/-- The actual access has no boundary contact except its designated midpoint port. -/
theorem access_support_cell (sites : List Point) (c q : Point) {p : ℝ × ℝ}
    (hp : p ∈ support (access sites c q)) :
    p ∈ closedCell 120 c ∧
      (p ∈ openCell 120 c ∨ p = realPoint (cellPort 120 c (side c q))) := by
  rw [access_eq_translate, support_translate] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  have hb : 0 ≤ p.1 ∧ p.1 ≤ 240 ∧ 0 ≤ p.2 ∧ p.2 ≤ 240 ∧
      (p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240 →
        p = realPoint (Crossover.boundaryPort (side c q))) := by
    by_cases hc : c ∈ sites
    · simp only [hc, ↓reduceIte] at hp
      exact Crossover.access_boundary_isolation hp
    · simp only [hc, ↓reduceIte] at hp
      exact spoke_boundary_isolation _ hp
  constructor
  · rw [mem_closedCell_add_origin_iff]
    norm_num
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1⟩
  · by_cases h : p.1 = 0 ∨ p.1 = 240 ∨ p.2 = 0 ∨ p.2 = 240
    · right
      rw [hb.2.2.2.2 h, cellPort_eq_boundaryPort, realPoint_add, add_comm]
    · left
      rw [mem_openCell_add_origin_iff]
      norm_num
      push Not at h
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h.1), lt_of_le_of_ne hb.2.1 h.2.1,
        lt_of_le_of_ne hb.2.2.1 (Ne.symm h.2.2.1), lt_of_le_of_ne hb.2.2.2.1 h.2.2.2⟩

/-- Access routes from distinct cells can meet only at their two equal designated ports. -/
theorem access_contact_of_distinct_cells (sites otherSites : List Point)
    {c d : Point} (hcd : c ≠ d)
    (a b : Point) {p : ℝ × ℝ}
    (hc : p ∈ support (access sites c a)) (hd : p ∈ support (access otherSites d b)) :
    p = realPoint (cellPort 120 c (side c a)) ∧
      p = realPoint (cellPort 120 d (side d b)) := by
  obtain ⟨hcclosed, hcopen | hcport⟩ := access_support_cell sites c a hc
  · exact False.elim (Set.disjoint_left.mp
      (disjoint_openCell_closedCell (by decide) hcd) hcopen
      (access_support_cell otherSites d b hd).1)
  · refine ⟨hcport, ?_⟩
    obtain ⟨_, hdopen | hdport⟩ := access_support_cell otherSites d b hd
    · exact False.elim (Set.disjoint_left.mp
        (disjoint_openCell_closedCell (by decide) hcd.symm) hdopen hcclosed)
    · exact hdport

private theorem spoke_contact_check : ∀ i j : Fin 4, i ≠ j →
    routeContactCheck [(120, 120)] [Crossover.boundaryPort i, (120, 120)]
      [Crossover.boundaryPort j, (120, 120)] = true := by decide

/-- Distinct sides of an ordinary cell contact only at its signal center. -/
theorem ordinary_access_contact {sites : List Point} {c : Point} (hc : c ∉ sites)
    (a b : Point) (hs : side c a ≠ side c b) {p : ℝ × ℝ}
    (ha : p ∈ support (access sites c a)) (hb : p ∈ support (access sites c b)) :
    p = realPoint (center c) := by
  rw [access_eq_spoke hc, support_translate] at ha
  obtain ⟨p, ha, rfl⟩ := ha
  rw [access_eq_spoke hc] at hb
  have hb' := (mem_support_translate_iff _ _ _).mp hb
  obtain ⟨q, hq, hpq⟩ := routeContactCheck_sound
    (spoke_contact_check _ _ hs) ha hb'
  have : q = (120, 120) := List.mem_singleton.mp hq
  subst q
  rw [hpq, center, realPoint_add, add_comm]

/-- Distinct access sides of a crossing cell have disjoint real supports. -/
theorem crossing_access_disjoint {sites : List Point} {c : Point} (hc : c ∈ sites)
    (a b : Point) (hs : side c a ≠ side c b) :
    Disjoint (support (access sites c a)) (support (access sites c b)) := by
  rw [Set.disjoint_left]
  intro p ha hb
  simp only [access, hc, ↓reduceIte] at ha hb
  have ha' := (mem_support_translate_iff (cellOrigin 120 c) (Crossover.accessRoute (side c a))
    (p - realPoint (cellOrigin 120 c))).mp
    (by simpa only [sub_add_cancel] using ha)
  have hb' := (mem_support_translate_iff (cellOrigin 120 c) (Crossover.accessRoute (side c b))
    (p - realPoint (cellOrigin 120 c))).mp
    (by simpa only [sub_add_cancel] using hb)
  exact Set.disjoint_left.mp (Crossover.access_disjoint hs) ha' hb'

/-- Compact labels retain the compiler's structured variable order and displayed positions. -/
theorem positions_getD_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    (positions φ).getD ((formula φ).distinctVars.idxOf ((rawFormula φ).vars.idxOf v)) (0, 0) =
      variablePosition v := by
  rw [formula, CNF.idxOf_distinctVars_compact _ hv]
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  rw [positions, List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

end Cslib.Complexity.SAT.PlanarCompile
