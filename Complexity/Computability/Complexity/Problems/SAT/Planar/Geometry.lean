/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Compile
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalDrawing
public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalPath
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Compact
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
* `Cslib.Complexity.SAT.PlanarCompile.routes_regular`: all actual emitted routes are simple
  and orthogonal.
* `Cslib.Complexity.SAT.PlanarCompile.routes_length`,
  `Cslib.Complexity.SAT.PlanarCompile.positions_length`: counts match the final incidence graph.
* `Cslib.Complexity.SAT.PlanarCompile.variablePosition_injOn_rawVars`: distinct actual variable
  names have distinct displayed positions.

These results do not yet certify the complete planar drawing: all clause positions and global
incidence contacts must also be separated.

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

/-- The executable compiler uses exactly the canonical unit paths certified by the layout API. -/
theorem paths_eq_unitPaths (φ : CNF ℕ) : paths φ = (SAT.incidenceGraph φ).unitPaths := rfl

/-- Literal-occurrence indexing selects the same path in the compiler and canonical layout. -/
theorem occurrencePath_eq_unitPath (φ : CNF ℕ) (o : Occurrence ℕ) :
    occurrencePath φ o =
      (SAT.incidenceGraph φ).unitPath ((Cslib.Logic.PL.occurrences φ).idxOf o) := rfl

private theorem occurrence_index_lt {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (Cslib.Logic.PL.occurrences φ).idxOf o < (SAT.incidenceGraph φ).2.length := by
  simpa only [SAT.incidenceGraph, List.length_map] using List.idxOf_lt_length_of_mem ho

/-- Every actual occurrence path is duplicate-free, without an extra supplied path witness. -/
theorem occurrencePath_nodup {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : (occurrencePath φ o).Nodup := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_nodup _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

/-- Every consecutive step in the actual compiler path is a unit grid displacement. -/
theorem occurrencePath_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) {e : Point × Point}
    (he : e ∈ (occurrencePath φ o).consecutivePairs) : Orthogonal.length e.1 e.2 = 1 := by
  rw [occurrencePath_eq_unitPath] at he
  exact Graph.unitPath_unit _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho) he

/-- Every actual selected path contains at least one point. -/
theorem occurrencePath_ne_nil {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : occurrencePath φ o ≠ [] := by
  rw [occurrencePath_eq_unitPath]
  exact Graph.unitPath_ne_nil _ (fun _ => SAT.incidenceGraph_endpoints)
    (fun _ => SAT.incidenceGraph_loopless) (occurrence_index_lt ho)

private theorem idxOf_range_eq {i n : ℕ} (hi : i < n) : (List.range n).idxOf i = i := by
  have h := (List.nodup_range : (List.range n).Nodup).idxOf_getElem i
    (by simpa only [List.length_range] using hi)
  rw [List.getElem_range] at h
  exact h

/-- Actual occurrence paths start at the variable's source-grid center and end at their clause. -/
theorem occurrencePath_endpoints {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    (occurrencePath φ o).head? = some (Layout.center (φ.distinctVars.idxOf o.2.2.1)) ∧
      (occurrencePath φ o).getLast? = some (Layout.center (φ.distinctVars.length + o.1)) := by
  have hi := occurrence_index_lt ho
  have h := Graph.unitPath_endpoints (SAT.incidenceGraph φ)
    (fun _ => SAT.incidenceGraph_endpoints) (fun _ => SAT.incidenceGraph_loopless) hi
  have he : (SAT.incidenceGraph φ).2[(Cslib.Logic.PL.occurrences φ).idxOf o] =
      (φ.distinctVars.idxOf o.2.2.1, φ.distinctVars.length + o.1) := by
    simp only [SAT.incidenceGraph, List.getElem_map]
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem ho)]
  have hb := SAT.incidenceGraph_bipartite (List.getElem_mem hi)
  rw [he] at hb
  simp only [Graph.edgeEndpoint, Bool.false_eq_true, ↓reduceIte] at h
  simp only [List.getD_eq_getElem _ _ hi, he] at h
  change (occurrencePath φ o).head? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.idxOf o.2.2.1))) ∧
    (occurrencePath φ o).getLast? =
      some (Layout.center ((List.range _).idxOf (φ.distinctVars.length + o.1))) at h
  rw [idxOf_range_eq (by omega), idxOf_range_eq hb.2.2] at h
  exact h

/-- Actual literal paths contain at least one unit step, so final-literal lookups are in range. -/
theorem occurrencePath_length_ge_two {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) : 2 ≤ (occurrencePath φ o).length := by
  have hne := occurrencePath_ne_nil ho
  have hend := occurrencePath_endpoints ho
  have hi : φ.distinctVars.idxOf o.2.2.1 < φ.distinctVars.length := by
    apply List.idxOf_lt_length_of_mem
    apply CNF.mem_distinctVars.mpr
    rw [← Cslib.Logic.PL.map_occurrences]
    exact List.mem_map_of_mem ho
  have hcenters : Layout.center (φ.distinctVars.idxOf o.2.2.1) ≠
      Layout.center (φ.distinctVars.length + o.1) := by
    intro heq
    have hx := congrArg Prod.fst heq
    simp only [Layout.center] at hx
    omega
  cases hr : occurrencePath φ o with
  | nil => exact False.elim (hne hr)
  | cons p r =>
    cases r with
    | nil =>
      simp only [hr, List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hend
      exact False.elim (hcenters (hend.1.symm.trans hend.2))
    | cons q r => simp

/-- The last two actual unit-path points are adjacent, including with the compiler's defaults. -/
theorem occurrencePath_last_unit {φ : CNF ℕ} {o : Occurrence ℕ}
    (ho : o ∈ Cslib.Logic.PL.occurrences φ) :
    let r := occurrencePath φ o
    Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1 := by
  have hlen := occurrencePath_length_ge_two ho
  dsimp only
  apply occurrencePath_unit ho (e :=
    ((occurrencePath φ o).getD ((occurrencePath φ o).length - 2) (0, 0),
      (occurrencePath φ o).getLastD (0, 0)))
  rw [List.consecutivePairs]
  let r := occurrencePath φ o
  have hrlen : 2 ≤ r.length := hlen
  have hk : r.length - 2 < (r.zip r.tail).length := by
    simp only [List.length_zip, List.length_tail]
    dsimp only [r]
    omega
  have heq : (r.zip r.tail)[r.length - 2] =
      (r.getD (r.length - 2) (0, 0), r.getLastD (0, 0)) := by
    rw [List.getElem_zip]
    apply Prod.ext
    · rw [List.getD_eq_getElem _ _ (by dsimp only [r]; omega)]
    · rw [List.getElem_tail]
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
      change r[r.length - 2 + 1] = r[r.length - 1]
      congr 1
      omega
  rw [← heq]
  exact List.getElem_mem hk

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

end Cslib.Complexity.SAT.PlanarCompile
