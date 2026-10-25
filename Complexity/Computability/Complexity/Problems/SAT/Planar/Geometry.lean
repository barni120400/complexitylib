/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Compact
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Forall2
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
* `Cslib.Complexity.SAT.PlanarCompile.routes_regular`: all actual emitted routes are simple
  and orthogonal.
* `Cslib.Complexity.SAT.PlanarCompile.routes_length`,
  `Cslib.Complexity.SAT.PlanarCompile.positions_length`: counts match the final incidence graph.
* `Cslib.Complexity.SAT.PlanarCompile.variablePosition_injOn_rawVars`: distinct actual variable
  names have distinct displayed positions.
* `Cslib.Complexity.SAT.PlanarCompile.pathPorts_nodup`: all directed unit-cell ports of the
  actual paths are distinct under the source width and occurrence bounds.
* `Cslib.Complexity.SAT.PlanarCompile.positions_nodup`: every actual output vertex has a
  distinct displayed position under those same source bounds.

* `Cslib.Complexity.SAT.PlanarCompile.routes_endpoints`: actual incidence-order endpoints,
  including repeated literal occurrences and compact variable indices.

These results do not yet certify the complete planar drawing: nonincident-vertex avoidance and
global route contacts remain to be proved.

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

private theorem three_simple {a b c : Point} (hn : [a, b, c].Nodup)
    (hc : segmentContactCheck [b] a b b c = true) : IsSimple [a, b, c] := by
  have hcontact : EndpointContacts a b b c := by
    intro p hp hq
    obtain ⟨q, hq, hpq⟩ := segmentContactCheck_sound hc hp hq
    have hqb : q = b := List.mem_singleton.mp hq
    exact ⟨Or.inr (hqb ▸ hpq), Or.inl (hqb ▸ hpq)⟩
  refine ⟨hn, ?_⟩
  intro e he f hf hne
  simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact False.elim (hne rfl)
  · exact hcontact
  · exact hcontact.symm
  · exact False.elim (hne rfl)

private def finalLocalRoute (s : Fin 4) (crossing : Bool) : Route :=
  [2 • Crossover.boundaryPort s - (120, 120), Crossover.boundaryPort s,
    if crossing then Crossover.variablePosition (Crossover.splitTerminal s) else (120, 120)]

private theorem finalLocalRoute_simple (s : Fin 4) (crossing : Bool) :
    IsSimple (finalLocalRoute s crossing) := by
  unfold finalLocalRoute
  apply three_simple
  · fin_cases s <;> cases crossing <;> decide
  · fin_cases s <;> cases crossing <;> decide

private theorem finalLocalRoute_orthogonal (s : Fin 4) (crossing : Bool) :
    IsOrthogonal (finalLocalRoute s crossing) := by
  fin_cases s <;> cases crossing <;>
    norm_num [finalLocalRoute, Crossover.boundaryPort, Crossover.variablePosition,
      Crossover.splitTerminal, IsOrthogonal, List.consecutivePairs, AxisAligned]

private theorem neighbor_center {p q : Point} (h : Orthogonal.length p q = 1) :
    center q = 2 • Crossover.boundaryPort (side p q) - (120, 120) + cellOrigin 120 p := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases h with rfl | rfl | rfl | rfl <;>
    norm_num [center, side, Crossover.boundaryPort, cellOrigin, two_nsmul,
      Prod.ext_iff] <;> omega

/-- The final-literal route is a translated straight three-point route for every unit step. -/
private theorem finalRoute_eq_translate (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    center q :: access sites p q = translate (cellOrigin 120 p)
      (finalLocalRoute (side p q) (decide (p ∈ sites))) := by
  rw [neighbor_center h]
  by_cases hp : p ∈ sites <;>
    simp [access, hp, translate, finalLocalRoute, Crossover.accessRoute,
      cellPort_eq_boundaryPort, center, add_comm]

/-- The actual final incidence across a unit step is continuously simple. -/
theorem finalRoute_simple (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) : IsSimple (center q :: access sites p q) := by
  rw [finalRoute_eq_translate sites h, isSimple_translate_iff]
  exact finalLocalRoute_simple _ _

/-- The actual final incidence across a unit step is proper and orthogonal. -/
theorem finalRoute_orthogonal (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) : IsOrthogonal (center q :: access sites p q) := by
  rw [finalRoute_eq_translate sites h, isOrthogonal_translate_iff]
  exact finalLocalRoute_orthogonal _ _

/-- Access length is exactly 20 inside a crossing cell and 120 inside an ordinary cell. -/
theorem access_wireLength (sites : List Point) (p q : Point) :
    wireLength (access sites p q) = if p ∈ sites then 20 else 120 := by
  by_cases hp : p ∈ sites
  · simp only [access, hp, ↓reduceIte, wireLength_translate]
    exact (Crossover.access_route_sizes _).2
  · rw [access_eq_spoke hp, wireLength_translate]
    simp only [hp, ↓reduceIte]
    generalize side p q = s
    fin_cases s <;> decide

/-- A final literal route across one unit step uses at most 240 units of wire. -/
theorem finalRoute_wireLength_le (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    wireLength (center q :: access sites p q) ≤ 240 := by
  rw [finalRoute_eq_translate sites h, wireLength_translate]
  generalize side p q = s
  generalize decide (p ∈ sites) = crossing
  fin_cases s <;> cases crossing <;> decide

/-- A final literal route is the ordinary clause-cell spoke followed by its neighbor's access.
This equality concerns the full real supports and includes the shared boundary midpoint. -/
theorem support_finalRoute (sites : List Point) {p q : Point}
    (h : Orthogonal.length p q = 1) :
    support (center q :: access sites p q) =
      support (access [] q p) ∪ support (access sites p q) := by
  rw [access_eq_pair sites p q, access_eq_pair [] q p, support_cons_cons]
  have hs (a b : Point) : support [a, b] = segment a b :=
    Set.ext fun _ => mem_support_pair
  rw [hs (cellPort 120 q (side q p))]
  simp only [signal, List.not_mem_nil, ↓reduceIte, variablePosition, Option.elim_none]
  rw [← shared_cellPort h]
  congr 1
  exact _root_.segment_symm ℝ _ _

/-- The final route starts at its original clause center and ends at the presented signal. -/
theorem finalRoute_endpoints (sites : List Point) (p q : Point) :
    (center q :: access sites p q).head? = some (center q) ∧
      (center q :: access sites p q).getLast? =
        some (variablePosition (signal sites p q)) := by
  rw [access_eq_pair]
  exact ⟨rfl, rfl⟩

/-- The two binary-link incidences are simple actual access routes. -/
theorem link_routes_simple (sites : List Point) (positive : Bool) (p q : Point) :
    ∀ r ∈ (link sites positive p q).2.2, IsSimple r := by
  cases positive <;> simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;>
    exact ⟨access_simple _ _ _, access_simple _ _ _⟩

/-- The two binary-link incidences are proper actual orthogonal access routes. -/
theorem link_routes_orthogonal (sites : List Point) (positive : Bool) (p q : Point) :
    ∀ r ∈ (link sites positive p q).2.2, IsOrthogonal r := by
  cases positive <;> simp only [link, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;>
    exact ⟨access_orthogonal _ _ _, access_orthogonal _ _ _⟩

/-- Literal and route ordering in an actual binary link gives the declared geometric endpoints. -/
theorem link_endpoints (sites : List Point) (positive : Bool) {p q : Point}
    (h : Orthogonal.length p q = 1) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ (link sites positive p q).1.zip (link sites positive p q).2.2) :
    r.head? = some (link sites positive p q).2.1 ∧
      r.getLast? = some (variablePosition l.1) := by
  cases positive <;>
    simp only [link, Bool.false_eq_true, ↓reduceIte, List.zip_cons_cons, List.zip_nil_right,
      List.mem_cons, List.not_mem_nil, or_false] at hlr ⊢ <;>
    rcases hlr with e | e <;> cases e <;>
    simp [access_eq_pair, ← shared_cellPort h]

/-- An ordinary signal name occurs exactly in an ordinary cell. -/
theorem signal_none_iff (sites : List Point) (p q : Point) :
    (signal sites p q).2 = none ↔ p ∉ sites := by
  simp [signal]

/-- Every variable actually emitted by the compiler has the appropriate cell kind.
In particular, the ordinary center name is never emitted inside a crossover cell. -/
theorem raw_variable_cell_kind (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.2 = none ↔ v.1 ∉ crossingSites φ := by
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, hp, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hv
    obtain ⟨lj, _, rfl⟩ := List.mem_map.mp hlr
    have heq := congrArg Prod.fst hlreq
    simp only [lastLiteral] at heq
    subst v
    exact signal_none_iff _ _ _
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hv
    have heq := congrArg Prod.fst hl
    dsimp only at heq
    subst v
    simp [hp]
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hv <;>
      rcases hv with hv | hv <;>
      have heq := congrArg Prod.fst hv <;> dsimp only at heq <;> subst v <;>
      exact signal_none_iff _ _ _

/-- Actual structured variable names have distinct positions, including across different cells. -/
theorem variablePosition_injOn_rawVars (φ : CNF ℕ) :
    Set.InjOn variablePosition {v | v ∈ (rawFormula φ).vars} := by
  intro v hv w hw heq
  have hreal := congrArg realPoint heq
  have hvcell := variablePosition_mem_openCell v
  have hwcell := variablePosition_mem_openCell w
  rw [← hreal] at hwcell
  have hcell : v.1 = w.1 := cell_eq_of_mem_open_closed (by decide) hvcell
    ⟨hwcell.1.le, hwcell.2.1.le, hwcell.2.2.1.le, hwcell.2.2.2.le⟩
  rcases v with ⟨p, v⟩
  rcases w with ⟨q, w⟩
  change p = q at hcell
  subst q
  have hvkind := raw_variable_cell_kind φ hv
  have hwkind := raw_variable_cell_kind φ hw
  cases v <;> cases w
  · rfl
  · cases hwkind.mpr (hvkind.mp rfl)
  · cases hvkind.mpr (hwkind.mp rfl)
  · simp only [variablePosition, Option.elim_some, add_right_inj] at heq
    exact congrArg (fun x => (p, some x)) (Crossover.variablePosition_injective heq)

private theorem idxOf_range_eq {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

/-- Every route actually emitted by the compiler is proper, orthogonal and continuously simple.
The source degree bounds are needed for global separation, not for this local certificate. -/
theorem routes_regular (φ : CNF ℕ) :
    ∀ r ∈ routes φ, IsOrthogonal r ∧ IsSimple r := by
  intro r hr
  obtain ⟨pc, hpc, hr⟩ := List.mem_flatMap.mp hr
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hr
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ := by
      exact List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    dsimp only [lastLiteral] at hlreq
    subst r
    exact ⟨finalRoute_orthogonal _ (occurrencePath_last_unit ho),
      finalRoute_simple _ (occurrencePath_last_unit ho)⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have he' := (List.mem_filter.mp he).1
    exact ⟨(isOrthogonal_translate_iff _ _).mpr (Crossover.incidence_orthogonal e he'),
      (isSimple_translate_iff _ _).mpr (Crossover.incidence_isSimple he')⟩
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    exact ⟨link_routes_orthogonal _ _ _ _ r hr, link_routes_simple _ _ _ _ r hr⟩

private theorem crossing_route_count : ∀ i : Fin 74,
    (Crossover.incidenceRoutes.filter fun e => e.1 == i.val).length =
      (Crossover.splitFormula.getD i.val []).length := by decide +kernel

/-- Every actual placed clause supplies exactly one route for each of its literal occurrences. -/
theorem placedClause_route_count (φ : CNF ℕ) :
    ∀ pc ∈ placedClauses φ, pc.2.2.length = pc.1.length := by
  intro pc hpc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, _, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    simp
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    have hi : ci.2 < 74 := by
      have h := (List.mem_zipIdx hci).2.1
      simpa only [Nat.zero_add, Crossover.length_splitFormula] using h
    have hc := (List.mem_zipIdx hci).2.2
    simp only [Nat.sub_zero] at hc
    have hcount := crossing_route_count ⟨ci.2, hi⟩
    rw [List.getD_eq_getElem Crossover.splitFormula []
      (by simpa only [Crossover.length_splitFormula] using hi)] at hcount
    simpa only [List.length_map, Clause.length_relabel, hc] using hcount
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    cases o.2.2.2 <;> rfl

/-- The actual route count matches the listed edges of the final compact incidence graph. -/
theorem routes_length (φ : CNF ℕ) :
    (routes φ).length = (SAT.incidenceGraph (formula φ)).2.length := by
  rw [SAT.length_edges_incidenceGraph]
  rw [formula, CNF.compact, CNF.vars_relabel, List.length_map]
  simp only [routes, List.length_flatMap, CNF.vars, List.length_map,
    List.length_flatten, rawFormula, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  exact fun pc hpc => placedClause_route_count φ pc hpc

/-- The actual position list has exactly the final compact graph's declared vertex count. -/
theorem positions_length (φ : CNF ℕ) :
    (positions φ).length = (SAT.incidenceGraph (formula φ)).1.length := by
  simp [positions, SAT.incidenceGraph, formula, CNF.distinctVars_compact, rawFormula]

/-- The final compact output has exactly the same ordered incidence graph as the raw output. -/
theorem incidenceGraph_formula (φ : CNF ℕ) :
    SAT.incidenceGraph (formula φ) = SAT.incidenceGraph (rawFormula φ) :=
  SAT.incidenceGraph_compact _

/-- The actual displayed variable positions have no repetitions. -/
theorem variablePositions_nodup (φ : CNF ℕ) :
    ((rawFormula φ).distinctVars.map variablePosition).Nodup :=
  (CNF.nodup_distinctVars _).map_on (fun _ hv _ hw =>
    variablePosition_injOn_rawVars φ (CNF.mem_distinctVars.mp hv) (CNF.mem_distinctVars.mp hw))

/-- Every geometric side midpoint lies in its own closed real cell. -/
theorem cellPort_mem_closedCell (c : Point) (s : Fin 4) :
    realPoint (cellPort 120 c s) ∈ closedCell 120 c := by
  rw [cellPort_eq_boundaryPort, realPoint_add, add_comm, mem_closedCell_add_origin_iff]
  fin_cases s <;> norm_num [Crossover.boundaryPort, realPoint]

/-- A geometric side midpoint is outside every open cell, including both cells sharing it. -/
theorem cellPort_not_mem_openCell (c d : Point) (s : Fin 4) :
    realPoint (cellPort 120 c s) ∉ openCell 120 d := by
  intro hp
  have heq : d = c := cell_eq_of_mem_open_closed (by decide) hp (cellPort_mem_closedCell c s)
  subst d
  rw [cellPort_eq_boundaryPort, realPoint_add, add_comm, mem_openCell_add_origin_iff] at hp
  fin_cases s <;> norm_num [Crossover.boundaryPort, realPoint] at hp

/-- No binary-link clause position is a variable position, even in a neighboring cell. -/
theorem link_position_ne_variable (sites : List Point) (positive : Bool) (p q : Point)
    (v : Variable) : (link sites positive p q).2.1 ≠ variablePosition v := by
  intro h
  apply cellPort_not_mem_openCell p v.1 (side p q)
  rw [show cellPort 120 p (side p q) = variablePosition v from h]
  exact variablePosition_mem_openCell v

/-- Every translated crossover clause position lies strictly inside its gadget cell. -/
theorem crossingClause_mem_openCell {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) : realPoint pc.2.1 ∈ openCell 120 c := by
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : ci.2 < Crossover.clausePositions.length := by
    have h := (List.mem_zipIdx hci).2.1
    simpa only [Nat.zero_add, Crossover.length_splitFormula, Crossover.drawing_sizes.1] using h
  have hp : Crossover.clausePositions.getD ci.2 (0, 0) ∈ Crossover.clausePositions := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hb := Crossover.clause_bounds _ hp
  rw [realPoint_add, add_comm, mem_openCell_add_origin_iff]
  simp only [realPoint]
  norm_num
  exact_mod_cast (show 0 < (Crossover.clausePositions.getD ci.2 (0, 0)).1 ∧
    (Crossover.clausePositions.getD ci.2 (0, 0)).1 < 240 ∧
      0 < (Crossover.clausePositions.getD ci.2 (0, 0)).2 ∧
      (Crossover.clausePositions.getD ci.2 (0, 0)).2 < 240 by omega)

private theorem consecutivePair_index {r : Route} {a b : Point}
    (h : (a, b) ∈ r.consecutivePairs) :
    ∃ (k : ℕ) (hk : k + 1 < r.length), r[k] = a ∧ r[k + 1] = b := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp h
  have hk' : k + 1 < r.length := by
    simpa only [List.consecutivePairs, List.length_zip, List.length_tail,
      min_eq_right (Nat.sub_le _ _), Nat.lt_sub_iff_add_lt] using hk
  simp only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] at heq
  exact ⟨k, hk', congrArg Prod.fst heq, congrArg Prod.snd heq⟩

private theorem mem_of_adjacent {r : Route} {p q : Point}
    (h : (p, q) ∈ r.consecutivePairs ∨ (q, p) ∈ r.consecutivePairs) : p ∈ r := by
  rcases h with h | h
  · exact (List.of_mem_zip h).1
  · exact List.mem_of_mem_tail (List.of_mem_zip h).2

private theorem neighbor_of_straight {r : Route} {p q d : Point}
    (ht : StraightThrough r p d) (hn : r.Nodup)
    (h : (p, q) ∈ r.consecutivePairs ∨ (q, p) ∈ r.consecutivePairs) :
    q = p - d ∨ q = p + d := by
  rcases h with h | h
  · obtain ⟨k, hk, hp, hq⟩ := consecutivePair_index h
    have hh := ht.getD_neighbors hn (by omega) hp
    have hd : r.getD (k + 1) p = q := by rw [List.getD_eq_getElem _ _ hk]; exact hq
    rcases hh.2.2 with ⟨_, hnext⟩ | ⟨_, hnext⟩
    · exact Or.inr (hd.symm.trans hnext)
    · exact Or.inl (hd.symm.trans hnext)
  · obtain ⟨k, hk, hq, hp⟩ := consecutivePair_index h
    have hh := ht.getD_neighbors hn hk hp
    have hd : r.getD (k + 1 - 1) p = q := by
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by omega)]
      exact hq
    rcases hh.2.2 with ⟨hprev, _⟩ | ⟨hprev, _⟩
    · exact Or.inl (hd.symm.trans hprev)
    · exact Or.inr (hd.symm.trans hprev)

private theorem horizontal_vertical_neighbors {p q : Point}
    (hx : q = p - (1, 0) ∨ q = p + (1, 0))
    (hy : q = p - (0, 1) ∨ q = p + (0, 1)) : False := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    have h := hx.symm.trans hy <;>
    have h' := congrArg Prod.fst h <;> simp at h'

private theorem canonical_neighbor_unique (G : Graph)
    (hG : ∀ e ∈ G.2, e.1 ∈ G.1 ∧ e.2 ∈ G.1)
    (hloop : ∀ e ∈ G.2, e.1 ≠ e.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p q : Point}
    (hcenter : p ∉ G.orthogonalPositions)
    (hiadj : (p, q) ∈ (G.unitPath i).consecutivePairs ∨
      (q, p) ∈ (G.unitPath i).consecutivePairs)
    (hjadj : (p, q) ∈ (G.unitPath j).consecutivePairs ∨
      (q, p) ∈ (G.unitPath j).consecutivePairs) : False := by
  have hn := Graph.unitPath_nodup G hG hloop hi
  have hm := Graph.unitPath_nodup G hG hloop hj
  rcases Graph.unitPath_crossing_neighbors G hG hloop hdeg hi hj hij hcenter
      (mem_of_adjacent hiadj) (mem_of_adjacent hjadj) with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact horizontal_vertical_neighbors (neighbor_of_straight hx hn hiadj)
      (neighbor_of_straight hy hm hjadj)
  · exact horizontal_vertical_neighbors (neighbor_of_straight hx hm hjadj)
      (neighbor_of_straight hy hn hiadj)

private theorem unit_not_both_centers (G : Graph) {p q : Point}
    (hunit : Orthogonal.length p q = 1) (hp : p ∈ G.orthogonalPositions)
    (hq : q ∈ G.orthogonalPositions) : False := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
  simp only [Orthogonal.length, Layout.center] at hunit
  omega

/-- Two actual canonical paths cannot share a unit grid edge, even in opposite directions.
This count-free uniqueness statement also applies to the final step into a clause cell. -/
theorem paths_shared_step_index {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    {i j : ℕ} (hi : i < (paths φ).length) (hj : j < (paths φ).length) {p q : Point}
    (he : (p, q) ∈ ((paths φ).getD i []).consecutivePairs)
    (hf : (p, q) ∈ ((paths φ).getD j []).consecutivePairs ∨
      (q, p) ∈ ((paths φ).getD j []).consecutivePairs) : i = j := by
  by_contra hij
  have hi' : i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have hj' : j < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hj
  change (p, q) ∈ ((SAT.incidenceGraph φ).unitPath i).consecutivePairs at he
  change (p, q) ∈ ((SAT.incidenceGraph φ).unitPath j).consecutivePairs ∨
    (q, p) ∈ ((SAT.incidenceGraph φ).unitPath j).consecutivePairs at hf
  have hG : ∀ e ∈ (SAT.incidenceGraph φ).2,
      e.1 ∈ (SAT.incidenceGraph φ).1 ∧ e.2 ∈ (SAT.incidenceGraph φ).1 :=
    fun _ => SAT.incidenceGraph_endpoints
  have hloop : ∀ e ∈ (SAT.incidenceGraph φ).2, e.1 ≠ e.2 :=
    fun _ => SAT.incidenceGraph_loopless
  have hdeg := SAT.incidenceGraph_degree_le hw hv
  by_cases hp : p ∈ (SAT.incidenceGraph φ).orthogonalPositions
  · have hq : q ∉ (SAT.incidenceGraph φ).orthogonalPositions := fun hq =>
      unit_not_both_centers _ (Graph.unitPath_unit _ hG hloop hi' he) hp hq
    exact canonical_neighbor_unique _ hG hloop hdeg hi' hj' hij hq (Or.inr he) hf.symm
  · exact canonical_neighbor_unique _ hG hloop hdeg hi' hj' hij hp (Or.inl he) hf

/-- At a unit neighbor, the facing side determines the neighbor itself. -/
theorem side_injective_on_unit_neighbors {p q t : Point}
    (hq : Orthogonal.length p q = 1) (ht : Orthogonal.length p t = 1)
    (hside : side p q = side p t) : q = t := by
  rcases p with ⟨px, py⟩
  rcases unit_neighbor_cases hq with rfl | rfl | rfl | rfl <;>
    rcases unit_neighbor_cases ht with rfl | rfl | rfl | rfl <;>
    first | rfl | norm_num [side] at hside

private def stepPorts (e : Point × Point) : List (Point × Fin 4) :=
  [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]

private theorem unit_reverse {p q : Point} (h : Orthogonal.length p q = 1) :
    Orthogonal.length q p = 1 := by
  simp only [Orthogonal.length] at h ⊢
  omega

private theorem stepPorts_inter {e f : Point × Point} {x : Point × Fin 4}
    (he : Orthogonal.length e.1 e.2 = 1) (hf : Orthogonal.length f.1 f.2 = 1)
    (hx : x ∈ stepPorts e) (hy : x ∈ stepPorts f) :
    e = f ∨ e = (f.2, f.1) := by
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  simp only [stepPorts, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst c
    have hb := side_injective_on_unit_neighbors he hf hs
    exact Or.inl (Prod.ext rfl hb)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst d
    have hb := side_injective_on_unit_neighbors he (unit_reverse hf) hs
    exact Or.inr (Prod.ext rfl hb)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst c
    have ha := side_injective_on_unit_neighbors (unit_reverse he) hf hs
    exact Or.inr (Prod.ext ha rfl)
  · obtain ⟨h, hs⟩ := Prod.mk.inj hy
    subst d
    have ha := side_injective_on_unit_neighbors (unit_reverse he) (unit_reverse hf) hs
    exact Or.inl (Prod.ext ha rfl)

private theorem routePorts_nodup {r : Route} (hn : r.Nodup)
    (hu : ∀ e ∈ r.consecutivePairs, Orthogonal.length e.1 e.2 = 1) :
    (r.consecutivePairs.flatMap stepPorts).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    have hne := (axisAligned_of_length_eq_one (hu e he)).2
    simp only [stepPorts, List.nodup_cons, List.not_mem_nil, List.nodup_nil,
      List.mem_singleton, not_false_eq_true, and_true]
    exact fun h => hne (congrArg Prod.fst h)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx hy
    have hi' : i + 1 < r.length := by
      simp only [List.consecutivePairs, List.length_zip, List.length_tail] at hi
      omega
    have hj' : j + 1 < r.length := by
      simp only [List.consecutivePairs, List.length_zip, List.length_tail] at hj
      omega
    rcases stepPorts_inter (hu _ (List.getElem_mem hi)) (hu _ (List.getElem_mem hj)) hx hy
        with heq | heq
    · have heq' : r[i] = r[j] := by
        simpa only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] using
          congrArg Prod.fst heq
      have := hn.eq_of_getElem_eq (by omega) (by omega) heq'
      omega
    · have heq' : r[i] = r[j + 1] := by
        simpa only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] using
          congrArg Prod.fst heq
      have := hn.eq_of_getElem_eq (by omega) hj' heq'
      omega

/-- All directed cell ports in the actual canonical paths are distinct. Both halves of every
unit step are included, even the final clause-directed half. No path witness is assumed. -/
theorem pathPorts_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
      [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]).Nodup := by
  have hi_edge {i : ℕ} (hi : i < (paths φ).length) :
      i < (SAT.incidenceGraph φ).2.length := by
    simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
  have hn {i : ℕ} (hi : i < (paths φ).length) : ((paths φ)[i]).Nodup := by
    have h := Graph.unitPath_nodup (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) (hi_edge hi)
    change ((paths φ).getD i []).Nodup at h
    rwa [List.getD_eq_getElem _ _ hi] at h
  have hu {i : ℕ} (hi : i < (paths φ).length) {e : Point × Point}
      (he : e ∈ ((paths φ)[i]).consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
    apply Graph.unitPath_unit (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) (hi_edge hi)
    change e ∈ ((paths φ).getD i []).consecutivePairs
    rwa [List.getD_eq_getElem _ _ hi]
  change ((paths φ).flatMap fun r => r.consecutivePairs.flatMap stepPorts).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    exact routePorts_nodup (hn hi) (fun _ he => hu hi he)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx hy
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨f, hf, hy⟩ := List.mem_flatMap.mp hy
    have hi_step : e ∈ ((paths φ).getD i []).consecutivePairs := by
      rwa [List.getD_eq_getElem _ _ hi]
    have hj_step : (e.1, e.2) ∈ ((paths φ).getD j []).consecutivePairs ∨
        (e.2, e.1) ∈ ((paths φ).getD j []).consecutivePairs := by
      rw [List.getD_eq_getElem _ _ hj]
      rcases stepPorts_inter (hu hi he) (hu hj hf) hx hy with heq | heq
      · exact Or.inl (heq.symm ▸ hf)
      · exact Or.inr (by simpa only [heq] using hf)
    have := paths_shared_step_index hw hv hi hj hi_step hj_step
    omega

/-- Equal boundary midpoints identify the same unordered unit grid edge. -/
theorem cellPort_step_eq_cases {p q a b : Point}
    (hpq : Orthogonal.length p q = 1) (hab : Orthogonal.length a b = 1)
    (h : cellPort 120 p (side p q) = cellPort 120 a (side a b)) :
    (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
  rcases p with ⟨px, py⟩
  rcases a with ⟨ax, ay⟩
  rcases unit_neighbor_cases hpq with rfl | rfl | rfl | rfl <;>
    rcases unit_neighbor_cases hab with rfl | rfl | rfl | rfl <;>
    norm_num [side, cellPort, cellOrigin, Prod.ext_iff] at h ⊢ <;> omega

/-- One geometric midpoint per actual unit step gives a duplicate-free list.
This includes final steps, so any prefix selection used for binary clauses remains distinct. -/
theorem pathMidpoints_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((paths φ).flatMap fun r => r.consecutivePairs.map fun e =>
      cellPort 120 e.1 (side e.1 e.2)).Nodup := by
  let steps := (paths φ).flatMap List.consecutivePairs
  have hu {e : Point × Point} (he : e ∈ steps) : Orthogonal.length e.1 e.2 = 1 := by
    obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < (SAT.incidenceGraph φ).2.length := by
      simpa only [paths_eq_unitPaths, Graph.unitPaths_length] using hi
    apply Graph.unitPath_unit (SAT.incidenceGraph φ)
      (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi'
    change e ∈ ((paths φ).getD i []).consecutivePairs
    rwa [List.getD_eq_getElem _ _ hi]
  have hp : (steps.flatMap stepPorts).Nodup := by
    have h := pathPorts_nodup hw hv
    change ((paths φ).flatMap fun r => r.consecutivePairs.flatMap stepPorts).Nodup at h
    simpa only [steps, List.flatMap_assoc] using h
  have hpair := (List.nodup_flatMap.mp hp).2
  have hmid : (steps.map fun e => cellPort 120 e.1 (side e.1 e.2)).Nodup := by
    apply List.pairwise_map.mpr
    apply hpair.imp_of_mem
    intro e f he hf hd heq
    have hx : (e.1, side e.1 e.2) ∈ stepPorts e := by simp [stepPorts]
    rcases cellPort_step_eq_cases (hu he) (hu hf) heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have heq' : e = f := Prod.ext h₁ h₂
      exact hd hx (heq' ▸ hx)
    · have heq' : e = (f.2, f.1) := Prod.ext h₁ h₂
      exact hd hx (by simp [stepPorts, heq'])
  simpa only [steps, List.map_flatMap] using hmid

/-- Distinct integer cells have distinct displayed centers. -/
theorem center_injective : Function.Injective center := by
  intro p q h
  have hp := center_mem_openCell (r := 120) (by decide) p
  have hq := center_mem_openCell (r := 120) (by decide) q
  change realPoint (center p) ∈ openCell 120 p at hp
  change realPoint (center q) ∈ openCell 120 q at hq
  rw [← h] at hq
  exact cell_eq_of_mem_open_closed (by decide) hp
    ⟨hq.1.le, hq.2.1.le, hq.2.2.1.le, hq.2.2.2.le⟩

/-- Original clause cells are declared source centers and are never selected as crossings. -/
theorem clause_cell_not_mem_crossingSites (φ : CNF ℕ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ crossingSites φ := by
  intro h
  apply ((mem_crossingSites φ _).mp h).2.1
  refine List.mem_map.mpr ⟨φ.distinctVars.length + i, List.mem_range.mpr ?_, rfl⟩
  simp only [SAT.incidenceGraph, List.length_range]
  omega

/-- Original clause positions are pairwise distinct, including repeated and empty clauses. -/
theorem originalPositions_nodup (φ : CNF ℕ) (sites : List Point) :
    ((originalClauses φ sites).map fun pc => pc.2.1).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [originalClauses, List.getElem_map, List.getElem_zipIdx] at heq
  have hc := center_injective heq
  have hx := congrArg Prod.fst hc
  simp only [Layout.center] at hx
  omega

/-- Each translated crossover keeps the fixed clause-position order. -/
theorem crossingClause_positions (c : Point) :
    (crossingClauses c).map (fun pc => pc.2.1) =
      Crossover.clausePositions.map (cellOrigin 120 c + ·) := by
  apply List.ext_getElem
  · simp [crossingClauses, Crossover.length_splitFormula, Crossover.drawing_sizes.1]
  · intro i hi hj
    simp only [crossingClauses, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj)]

/-- Every crossover has pairwise distinct actual clause positions. -/
theorem crossingClause_positions_nodup (c : Point) :
    ((crossingClauses c).map fun pc => pc.2.1).Nodup := by
  rw [crossingClause_positions]
  exact Crossover.clausePositions_nodup.map (fun _ _ h => add_left_cancel h)

/-- Different selected crossing cells contribute disjoint lists of interior clause positions. -/
theorem crossingPositions_nodup {sites : List Point} (hn : sites.Nodup) :
    ((sites.flatMap crossingClauses).map fun pc => pc.2.1).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  refine ⟨fun c _ => crossingClause_positions_nodup c, hn.imp ?_⟩
  intro c d hcd p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  have hc := crossingClause_mem_openCell hpc
  have hd := crossingClause_mem_openCell hpd
  rw [heq] at hd
  exact Set.disjoint_left.mp (disjoint_openCell (by decide) hcd) hc hd

/-- Original and crossover clause positions cannot coincide. -/
theorem original_crossing_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      (((crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨c, hc, hpd⟩ := List.mem_flatMap.mp hpd
  have hpos := crossingClause_mem_openCell hpd
  rw [heq] at hpos
  have hcenter := center_mem_openCell (r := 120) (by decide)
    (Layout.center (φ.distinctVars.length + ci.2))
  have hcell := cell_eq_of_mem_open_closed (by decide) hcenter
    ⟨hpos.1.le, hpos.2.1.le, hpos.2.2.1.le, hpos.2.2.2.le⟩
  have hi : ci.2 < φ.length := by simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
  exact clause_cell_not_mem_crossingSites φ hi (hcell ▸ hc)

private theorem consecutivePairs_dropLast (r : Route) :
    r.dropLast.consecutivePairs = r.consecutivePairs.dropLast := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      cases r with
      | nil => rfl
      | cons c r =>
        simp only [List.dropLast_cons_cons, List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons] at ih ⊢
        exact congrArg ((a, b) :: ·) ih

/-- Binary-clause positions are a sublist of the distinct actual unit-step midpoints. -/
theorem linkPositions_sublist_midpoints (φ : CNF ℕ) :
    (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1).Sublist
    ((paths φ).flatMap fun r => r.consecutivePairs.map fun e =>
      cellPort 120 e.1 (side e.1 e.2)) := by
  rw [← occurrencePaths_eq_paths φ, List.flatMap_map]
  simp only [List.map_flatMap, links, List.map_map, Function.comp_def, link]
  apply List.Sublist.flatMap_right
  intro o _
  apply List.Sublist.map
  rw [consecutivePairs_dropLast]
  exact List.dropLast_sublist _

/-- All actual binary-link clauses have distinct positions, including between parallel paths. -/
theorem linkPositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
      links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1)).Nodup :=
  (pathMidpoints_nodup hw hv).sublist (linkPositions_sublist_midpoints φ)

private theorem link_position_not_open {sites : List Point} {positive : Bool} {r : Route}
    {pc : PlacedClause} (hpc : pc ∈ links sites positive r) (c : Point) :
    realPoint pc.2.1 ∉ openCell 120 c := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
  exact cellPort_not_mem_openCell _ c _

private theorem original_link_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((originalClauses φ (crossingSites φ)).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd (Layout.center (φ.distinctVars.length + ci.2))
  rw [heq]
  exact center_mem_openCell (by decide) _

private theorem crossing_link_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint (((crossingSites φ).flatMap crossingClauses).map fun pc => pc.2.1)
      (((Cslib.Logic.PL.occurrences φ).flatMap fun o =>
        links (crossingSites φ) o.2.2.2 (occurrencePath φ o)).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hp
  obtain ⟨pd, hpd, heq⟩ := List.mem_map.mp hq
  obtain ⟨c, _, hpc⟩ := List.mem_flatMap.mp hpc
  obtain ⟨_, _, hpd⟩ := List.mem_flatMap.mp hpd
  apply link_position_not_open hpd c
  rw [heq]
  exact crossingClause_mem_openCell hpc

/-- All actual output clauses have distinct displayed positions. Boundary clauses, interior
crossover clauses and original source clauses are separated in the full real-cell geometry. -/
theorem clausePositions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) :
    ((placedClauses φ).map fun pc => pc.2.1).Nodup := by
  simp only [placedClauses, List.map_append]
  apply List.Nodup.append
  · exact (originalPositions_nodup φ _).append
      (crossingPositions_nodup (crossingSites_nodup φ)) (original_crossing_positions_disjoint φ)
  · exact linkPositions_nodup hw hv
  · intro p hp hq
    rcases List.mem_append.mp hp with hp | hp
    · exact original_link_positions_disjoint φ hp hq
    · exact crossing_link_positions_disjoint φ hp hq

private theorem penultimate_mem_dropLast {r : Route} (h : 2 ≤ r.length) :
    r.getD (r.length - 2) (0, 0) ∈ r.dropLast := by
  have hk : r.length - 2 < r.dropLast.length := by simp only [List.length_dropLast]; omega
  rw [List.getD_eq_getElem _ _ (by omega), ← List.getElem_dropLast hk]
  exact List.getElem_mem hk

/-- Every emitted variable cell is a selected crossing or lies before the final clause point
of an actual source occurrence path. -/
theorem raw_variable_cell_membership (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    v.1 ∈ crossingSites φ ∨ ∃ o ∈ Cslib.Logic.PL.occurrences φ,
      v.1 ∈ (occurrencePath φ o).dropLast := by
  obtain ⟨c, hc, b, hv⟩ := CNF.mem_vars.mp hv
  obtain ⟨pc, hpc, rfl⟩ := List.mem_map.mp hc
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨p, hp, hpc⟩) | ⟨o, ho, hpc⟩
  · obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨lr, hlr, hlreq⟩ := List.mem_map.mp hv
    obtain ⟨lj, hlj, rfl⟩ := List.mem_map.mp hlr
    have ho : (ci.2, lj.2, lj.1) ∈ Cslib.Logic.PL.occurrences φ :=
      List.mem_flatMap.mpr ⟨ci, hci, List.mem_map.mpr ⟨lj, hlj, rfl⟩⟩
    have heq := congrArg Prod.fst hlreq
    dsimp only [lastLiteral] at heq
    subst v
    exact Or.inr ⟨_, ho, penultimate_mem_dropLast (occurrencePath_length_ge_two ho)⟩
  · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hpc
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hv
    have heq := congrArg Prod.fst hl
    dsimp only at heq
    subst v
    exact Or.inl hp
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    cases hpos : o.2.2.2 <;>
      simp only [link, hpos, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at hv <;>
      rcases hv with hv | hv <;>
      have heq := congrArg Prod.fst hv <;> dsimp only at heq <;> subst v
    all_goals first
      | exact Or.inr ⟨o, ho, (List.of_mem_zip he).1⟩
      | exact Or.inr ⟨o, ho, List.mem_of_mem_tail (List.of_mem_zip he).2⟩

private theorem occurrencePath_clause_center_iff {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∈ occurrencePath φ o ↔ i = o.1 := by
  have hoidx := occurrence_index_lt ho
  have h := Graph.unitPath_center_iff (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hoidx
    (w := φ.distinctVars.length + i) (by simp only [SAT.incidenceGraph, List.length_range]; omega)
  have he : (SAT.incidenceGraph φ).2[(Cslib.Logic.PL.occurrences φ).idxOf o] =
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]
  have hb := SAT.incidenceGraph_bipartite (List.getElem_mem hoidx)
  rw [he] at hb h
  change Layout.center (φ.distinctVars.length + i) ∈ occurrencePath φ o ↔
    φ.distinctVars.length + i = (List.range _).idxOf (φ.distinctVars.idxOf o.2.2.1) ∨
      φ.distinctVars.length + i = (List.range _).idxOf (φ.distinctVars.length + o.1) at h
  rw [idxOf_range_eq (by omega), idxOf_range_eq hb.2.2] at h
  exact h.trans (by omega)

/-- No source clause center is used as a signal cell before a path's final endpoint. -/
theorem clause_cell_not_mem_path_dropLast {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {i : ℕ} (hi : i < φ.length) :
    Layout.center (φ.distinctVars.length + i) ∉ (occurrencePath φ o).dropLast := by
  intro hp
  have hi' := (occurrencePath_clause_center_iff ho hi).mp
    ((List.dropLast_sublist _).subset hp)
  subst i
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hp
  have hlen := occurrencePath_length_ge_two ho
  have hend := (occurrencePath_endpoints ho).2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hend
  have hk' : k < (occurrencePath φ o).length := by
    simp only [List.length_dropLast] at hk
    omega
  have heq : (occurrencePath φ o)[k] =
      (occurrencePath φ o)[(occurrencePath φ o).length - 1] := by
    rw [Option.some.inj hend]
    simpa only [List.getElem_dropLast] using hget
  have hidx := (occurrencePath_nodup ho).eq_of_getElem_eq hk' (by omega) heq
  simp only [List.length_dropLast] at hk
  omega

/-- Actual output variables never occupy a source clause cell. -/
theorem raw_variable_not_clause_cell {φ : CNF ℕ} {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) {i : ℕ} (hi : i < φ.length) :
    v.1 ≠ Layout.center (φ.distinctVars.length + i) := by
  intro h
  rcases raw_variable_cell_membership φ hv with hsite | ⟨o, ho, hp⟩
  · exact clause_cell_not_mem_crossingSites φ hi (h ▸ hsite)
  · exact clause_cell_not_mem_path_dropLast ho hi (h ▸ hp)

private theorem crossing_position_ne_raw_variable {φ : CNF ℕ} {c : Point}
    (hc : c ∈ crossingSites φ) {pc : PlacedClause} (hpc : pc ∈ crossingClauses c)
    {v : Variable} (hv : v ∈ (rawFormula φ).vars) : pc.2.1 ≠ variablePosition v := by
  intro hpos
  have hpcopen := crossingClause_mem_openCell hpc
  have hvopen := variablePosition_mem_openCell v
  rw [hpos] at hpcopen
  have hcell : c = v.1 := cell_eq_of_mem_open_closed (by decide) hpcopen
    ⟨hvopen.1.le, hvopen.2.1.le, hvopen.2.2.1.le, hvopen.2.2.2.le⟩
  rcases v with ⟨p, v⟩
  change c = p at hcell
  subst p
  cases v with
  | none => exact (raw_variable_cell_kind φ hv).mp rfl hc
  | some v =>
    have hmem : pc.2.1 ∈ (crossingClauses c).map (fun pc => pc.2.1) :=
      List.mem_map_of_mem hpc
    rw [crossingClause_positions] at hmem
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
    have heq' : q = Crossover.variablePosition v := add_left_cancel (heq.trans hpos)
    exact Crossover.variablePosition_not_mem_clauses v (heq' ▸ hq)

/-- The actual variable and clause position lists are disjoint. This includes empty original
clauses and excludes variable vertices from all binary-clause boundary positions. -/
theorem variable_clause_positions_disjoint (φ : CNF ℕ) :
    List.Disjoint ((rawFormula φ).distinctVars.map variablePosition)
      ((placedClauses φ).map fun pc => pc.2.1) := by
  intro p hp hq
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  have hv' := CNF.mem_distinctVars.mp hv
  obtain ⟨pc, hpc, hpos⟩ := List.mem_map.mp hq
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨c, hc, hpc⟩) | ⟨o, _, hpc⟩
  · obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
    dsimp only at hpos
    have hcenter := center_mem_openCell (r := 120) (by decide)
      (Layout.center (φ.distinctVars.length + i))
    change realPoint (center (Layout.center (φ.distinctVars.length + i))) ∈ _ at hcenter
    rw [hpos] at hcenter
    have hvopen := variablePosition_mem_openCell v
    have hcell : Layout.center (φ.distinctVars.length + i) = v.1 :=
      cell_eq_of_mem_open_closed (by decide) hcenter
        ⟨hvopen.1.le, hvopen.2.1.le, hvopen.2.2.1.le, hvopen.2.2.2.le⟩
    have hi : i < φ.length := by
      simpa only [Nat.zero_add] using (List.mem_zipIdx hci).2.1
    exact raw_variable_not_clause_cell hv' hi hcell.symm
  · exact crossing_position_ne_raw_variable hc hpc hv' hpos
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hpc
    exact link_position_ne_variable _ _ _ _ v hpos

/-- All actual displayed output vertices have distinct integer positions. -/
theorem positions_nodup {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3) : (positions φ).Nodup :=
  (variablePositions_nodup φ).append (clausePositions_nodup hw hv)
    (variable_clause_positions_disjoint φ)

private theorem originalClause_endpoints {φ : CNF ℕ} {sites : List Point}
    {pc : PlacedClause} (hpc : pc ∈ originalClauses φ sites)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  dsimp only at hlr ⊢
  rw [← List.zip_of_prod rfl rfl] at hlr
  obtain ⟨⟨sourceLiteral, j⟩, hlj, heq⟩ := List.mem_map.mp hlr
  have ho : (i, j, sourceLiteral) ∈ Cslib.Logic.PL.occurrences φ :=
    List.mem_flatMap.mpr ⟨(c, i), hci, List.mem_map.mpr ⟨(sourceLiteral, j), hlj, rfl⟩⟩
  dsimp only [lastLiteral] at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hlast : (occurrencePath φ (i, j, sourceLiteral)).getLastD (0, 0) =
      Layout.center (φ.distinctVars.length + i) := by
    rw [List.getLastD_eq_getLast?, (occurrencePath_endpoints ho).2]
    rfl
  simpa only [hlast] using finalRoute_endpoints sites
    ((occurrencePath φ (i, j, sourceLiteral)).getD
      ((occurrencePath φ (i, j, sourceLiteral)).length - 2) (0, 0))
    ((occurrencePath φ (i, j, sourceLiteral)).getLastD (0, 0))

private theorem crossing_literal_routes_cover : ∀ i : Fin 74,
    ((Crossover.splitFormula.getD i.val []).zip
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i.val).map fun e => e.2.2)).all
        (fun lr => decide ((i.val, lr.1.1, lr.2) ∈ Crossover.incidenceRoutes)) = true := by
  decide +kernel

private theorem crossingClause_endpoints {c : Point} {pc : PlacedClause}
    (hpc : pc ∈ crossingClauses c) {l : Literal Variable} {r : Route}
    (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  obtain ⟨⟨sourceClause, i⟩, hci, rfl⟩ := List.mem_map.mp hpc
  have hi : i < 74 := by
    simpa only [Nat.zero_add, Crossover.length_splitFormula] using (List.mem_zipIdx hci).2.1
  have hc : sourceClause = Crossover.splitFormula.getD i [] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [Crossover.length_splitFormula] using hi)]
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hci).2.2
  change (l, r) ∈
    (sourceClause.map (Prod.map (fun v => (c, some v)) id)).zip
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map
        (fun e => translate (cellOrigin 120 c) e.2.2)) at hlr
  have hmap : ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map
      (fun e => translate (cellOrigin 120 c) e.2.2)) =
      ((Crossover.incidenceRoutes.filter fun e => e.1 == i).map fun e => e.2.2).map
        (translate (cellOrigin 120 c)) := by rw [List.map_map]; rfl
  rw [hmap, List.zip_map] at hlr
  obtain ⟨⟨oldLiteral, oldRoute⟩, hold, heq⟩ := List.mem_map.mp hlr
  rw [hc] at hold
  have he : (i, oldLiteral.1, oldRoute) ∈ Crossover.incidenceRoutes :=
    of_decide_eq_true (List.all_eq_true.mp (crossing_literal_routes_cover ⟨i, hi⟩) _ hold)
  change (((c, some oldLiteral.1), oldLiteral.2),
    translate (cellOrigin 120 c) oldRoute) = (l, r) at heq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  have hend := Crossover.incidence_endpoints _ he
  constructor
  · simp only [translate, List.head?_map, hend.2.1, Option.map_some]
    congr 1
    exact add_comm _ _
  · simp only [translate, List.getLast?_map, hend.2.2, Option.map_some,
      variablePosition, Option.elim_some]
    congr 1
    exact add_comm _ _

/-- Every literal/route pair in every actual placed clause has the declared endpoints.
The statement retains literal order, including all original repeated literal occurrences. -/
theorem placedClause_endpoints (φ : CNF ℕ) {pc : PlacedClause} (hpc : pc ∈ placedClauses φ)
    {l : Literal Variable} {r : Route} (hlr : (l, r) ∈ pc.1.zip pc.2.2) :
    r.head? = some pc.2.1 ∧ r.getLast? = some (variablePosition l.1) := by
  simp only [placedClauses, List.mem_append, List.mem_flatMap] at hpc
  rcases hpc with (hpc | ⟨_, _, hpc⟩) | ⟨o, ho, hpc⟩
  · exact originalClause_endpoints hpc hlr
  · exact crossingClause_endpoints hpc hlr
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpc
    have he' : e ∈ (occurrencePath φ o).consecutivePairs := by
      rw [consecutivePairs_dropLast] at he
      exact (List.dropLast_sublist _).subset he
    exact link_endpoints _ _ (occurrencePath_unit ho he') hlr

private theorem positions_getD_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    (positions φ).getD ((rawFormula φ).distinctVars.idxOf v) (0, 0) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  rw [positions, List.getD_append _ _ _ _ (by simpa only [List.length_map] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
  congr 1
  exact List.getElem_idxOf hi

/-- The graph's actual variable vertex index resolves to its emitted structured position. -/
theorem drawingPosition_raw_variable (φ : CNF ℕ) {v : Variable}
    (hv : v ∈ (rawFormula φ).vars) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.idxOf v) = variablePosition v := by
  have hi := List.idxOf_lt_length_of_mem (CNF.mem_distinctVars.mpr hv)
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.idxOf v))
    (0, 0) = _
  rw [idxOf_range_eq (by omega)]
  exact positions_getD_raw_variable φ hv

/-- The graph's actual clause vertex index resolves to the placed clause at that index. -/
theorem drawingPosition_raw_clause (φ : CNF ℕ) {i : ℕ} (hi : i < (placedClauses φ).length) :
    Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ)) (positions φ, routes φ)
      ((rawFormula φ).distinctVars.length + i) = ((placedClauses φ)[i]).2.1 := by
  change (positions φ).getD ((List.range _).idxOf ((rawFormula φ).distinctVars.length + i))
    (0, 0) = _
  have hlen : (rawFormula φ).length = (placedClauses φ).length := by
    simp only [rawFormula, List.length_map]
  rw [idxOf_range_eq (by omega), positions,
    List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]

private theorem forall₂_flatMap_same {A B C : Type*} {R : B → C → Prop}
    (xs : List A) (f : A → List B) (g : A → List C)
    (h : ∀ a ∈ xs, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons a xs ih =>
    exact List.rel_append (h a List.mem_cons_self)
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem map_zipIdx_ignore {A B : Type*} (xs : List A) (f : A → B) :
    (xs.zipIdx.map fun a => f a.1) = xs.map f := by
  calc
    _ = (xs.zipIdx.map Prod.fst).map f := by rw [List.map_map]; rfl
    _ = _ := by rw [List.zipIdx_map_fst]

private theorem raw_edges_eq (φ : CNF ℕ) :
    (SAT.incidenceGraph (rawFormula φ)).2 =
      (placedClauses φ).zipIdx.flatMap fun pci => pci.1.1.map fun l =>
        ((rawFormula φ).distinctVars.idxOf l.1, (rawFormula φ).distinctVars.length + pci.2) := by
  simp only [SAT.incidenceGraph, Cslib.Logic.PL.occurrences, rawFormula, List.zipIdx_map,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq, List.idxOf, beq_eq_decide]
  congr 1
  funext pci
  simpa only [rawFormula, List.idxOf, beq_eq_decide] using
    map_zipIdx_ignore pci.1.1 (fun l =>
      ((rawFormula φ).distinctVars.idxOf l.1, (rawFormula φ).distinctVars.length + pci.2))

private theorem raw_routes_eq (φ : CNF ℕ) :
    routes φ = (placedClauses φ).zipIdx.flatMap (fun pci => pci.1.2.2) := by
  calc
    _ = ((placedClauses φ).zipIdx.map Prod.fst).flatMap (fun pc => pc.2.2) := by
      rw [List.zipIdx_map_fst]
      rfl
    _ = _ := by rw [List.flatMap_map]

private theorem raw_routes_endpoints (φ : CNF ℕ) :
    List.Forall₂ (fun e r =>
      r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.2) ∧
      r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
        (positions φ, routes φ) e.1))
      (SAT.incidenceGraph (rawFormula φ)).2 (routes φ) := by
  rw [raw_edges_eq, raw_routes_eq]
  apply forall₂_flatMap_same
  intro pci hpci
  rcases pci with ⟨pc, i⟩
  have hpc := List.fst_mem_of_mem_zipIdx hpci
  have hi : i < (placedClauses φ).length := by
    simpa only [Nat.zero_add] using (List.mem_zipIdx hpci).2.1
  have hget : pc = (placedClauses φ)[i] := by
    simpa only [Nat.sub_zero] using (List.mem_zipIdx hpci).2.2
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_iff_zip.mpr
  refine ⟨(placedClause_route_count φ pc hpc).symm, ?_⟩
  intro l r hlr
  have hends := placedClause_endpoints φ hpc hlr
  have hvar : l.1 ∈ (rawFormula φ).vars := by
    exact CNF.mem_vars.mpr ⟨pc.1, List.mem_map_of_mem hpc, l.2, (List.of_mem_zip hlr).1⟩
  change r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.length + i)) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (rawFormula φ))
      (positions φ, routes φ) ((rawFormula φ).distinctVars.idxOf l.1))
  rw [drawingPosition_raw_clause φ hi, drawingPosition_raw_variable φ hvar, ← hget]
  exact hends

/-- Every actual indexed route has its actual incident graph vertices as endpoints, in
clause-to-variable order. Compaction and repeated edge occurrences preserve that order. -/
theorem routes_endpoints (φ : CNF ℕ) {i : ℕ}
    (hi : i < (SAT.incidenceGraph (formula φ)).2.length) :
    let r := (routes φ).getD i []
    r.head? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].2) ∧
    r.getLast? = some (Graph.drawingPosition (SAT.incidenceGraph (formula φ))
      (positions φ, routes φ) (SAT.incidenceGraph (formula φ)).2[i].1) := by
  simp only [incidenceGraph_formula] at hi ⊢
  have hir : i < (routes φ).length := by
    rwa [routes_length, incidenceGraph_formula]
  have h := (raw_routes_endpoints φ).get hi hir
  simpa only [List.get_eq_getElem, List.getD_eq_getElem _ _ hir] using h

end Cslib.Complexity.SAT.PlanarCompile
