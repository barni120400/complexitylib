/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT.Planar.Geometry
public import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths
public import Complexity.Computability.Complexity.Problems.SAT.Incidence.Degree
public import Complexity.Logics.Propositional.CNF.Compact.Relabel
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

/-!
# Literal occurrences in the actual planarization output

All bounds count literal positions, including repetitions within one clause. External incidences
are compared with the directed halves of the actual canonical unit paths. The final clause-cell
half is permitted in this comparison, so the comparison only overcounts the emitted variables.

## Main definitions

* `Cslib.Complexity.SAT.PlanarCompile.pathHalfEdges`: both directed halves of each unit step.
* `Cslib.Complexity.SAT.PlanarCompile.pathSignals`: signal names presented by these halves.

## Main results

* `Cslib.Complexity.SAT.PlanarCompile.count_links_lastLiteral_le`: every emitted external literal
  is bounded by the corresponding actual path halves.
-/

@[expose] public section

namespace Cslib.Complexity.SAT.PlanarCompile

open Cslib.Logic.PL Cslib.Logic.PL.CNF Orthogonal

/-- Both directed cell halves of every consecutive step, in path order. -/
def pathHalfEdges (r : Route) : List (Point × Point) :=
  r.consecutivePairs.flatMap fun e => [e, e.swap]

/-- The actual signal presented by every directed cell half of a path. -/
def pathSignals (sites : List Point) (r : Route) : List Variable :=
  (pathHalfEdges r).map fun e => signal sites e.1 e.2

private theorem pathSignals_cons_cons (sites : List Point) (a b : Point) (r : Route) :
    pathSignals sites (a :: b :: r) =
      [signal sites a b, signal sites b a] ++ pathSignals sites (b :: r) := rfl

private theorem links_cons_cons_cons (sites : List Point) (positive : Bool)
    (a b c : Point) (r : Route) :
    links sites positive (a :: b :: c :: r) =
      link sites positive a b :: links sites positive (b :: c :: r) := rfl

private theorem lastLiteral_cons_cons_cons (sites : List Point) (positive : Bool)
    (a b c : Point) (r : Route) :
    lastLiteral sites (a :: b :: c :: r) positive =
      lastLiteral sites (b :: c :: r) positive := by
  simp [lastLiteral]

private theorem count_link (sites : List Point) (positive : Bool) (a b : Point) (v : Variable) :
    ((link sites positive a b).1.map Prod.fst).count v =
      ([signal sites a b, signal sites b a]).count v := by
  cases positive <;> simp [link, List.count_cons, Nat.add_comm]

/-- Links and the final original literal use only the corresponding actual path halves.
The unused reverse half at the original clause center is intentionally retained on the right. -/
theorem count_links_lastLiteral_le (sites : List Point) (positive : Bool) (r : Route)
    (hlen : 2 ≤ r.length) (v : Variable) :
    (CNF.vars ((links sites positive r).map Prod.fst)).count v +
      [(lastLiteral sites r positive).1.1].count v ≤ (pathSignals sites r).count v := by
  induction r with
  | nil => simp at hlen
  | cons a r ih =>
    cases r with
    | nil => simp at hlen
    | cons b r =>
      cases r with
      | nil =>
        simp [links, lastLiteral, pathSignals, pathHalfEdges, List.consecutivePairs,
          CNF.vars, List.count_cons]
      | cons c r =>
        have ht := ih (by simp : 2 ≤ (b :: c :: r).length)
        rw [links_cons_cons_cons, List.map_cons, CNF.vars, List.flatten_cons,
          List.map_append, List.count_append, lastLiteral_cons_cons_cons,
          pathSignals_cons_cons, List.count_append]
        change ((link sites positive a b).1.map Prod.fst).count v +
          (CNF.vars ((links sites positive (b :: c :: r)).map Prod.fst)).count v +
          [(lastLiteral sites (b :: c :: r) positive).1.1].count v ≤ _
        rw [count_link]
        omega

private theorem signal_eq_none_iff (sites : List Point) (a b p : Point) :
    signal sites a b = (p, none) ↔ a = p ∧ p ∉ sites := by
  by_cases h : a = p
  · subst a
    simp [signal]
  · simp [signal, Prod.mk.injEq, h]

private theorem signal_beq_none (sites : List Point) (a b p : Point) (hp : p ∉ sites) :
    (signal sites a b == (p, none)) = (a == p) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, signal_eq_none_iff, hp, not_false_eq_true, and_true]

/-- Ordinary-cell path occurrences are exactly its incoming and outgoing adjacency positions. -/
theorem count_pathSignals_none (sites : List Point) (r : Route) (p : Point) (hp : p ∉ sites) :
    (pathSignals sites r).count (p, none) = r.dropLast.count p + r.tail.count p := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => simp [pathSignals, pathHalfEdges, List.consecutivePairs]
    | cons b r =>
      rw [pathSignals_cons_cons, List.count_append]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, signal_beq_none sites _ _ p hp,
        List.dropLast_cons_cons, List.tail_cons] at *
      omega

/-- A simple path contributes at most two literal halves at one ordinary cell. -/
theorem count_pathSignals_none_le_two (sites : List Point) (r : Route) (p : Point)
    (hp : p ∉ sites) (hn : r.Nodup) : (pathSignals sites r).count (p, none) ≤ 2 := by
  rw [count_pathSignals_none sites r p hp]
  have hd := List.nodup_iff_count_le_one.mp (hn.sublist (List.dropLast_sublist _)) p
  have ht := List.nodup_iff_count_le_one.mp hn.tail p
  omega

private theorem vars_originalClauses (φ : CNF ℕ) (sites : List Point) :
    CNF.vars ((originalClauses φ sites).map Prod.fst) =
      (Cslib.Logic.PL.occurrences φ).map
        (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1) := by
  simp [originalClauses, Cslib.Logic.PL.occurrences, CNF.vars, List.map_flatten,
    List.map_map, Function.comp_def, List.flatMap_def]

private theorem vars_crossingClauses (p : Point) :
    CNF.vars ((crossingClauses p).map Prod.fst) =
      Crossover.splitFormula.vars.map (fun v => (p, some v)) := by
  have h : (crossingClauses p).map Prod.fst =
      Crossover.splitFormula.relabel (fun v => (p, some v)) := by
    simpa only [crossingClauses, CNF.relabel, List.map_map, Function.comp_def] using
      congrArg (List.map (fun c : Clause Crossover.SplitVariable =>
        c.relabel (fun v => (p, some v))))
        (List.zipIdx_map_fst (l := Crossover.splitFormula) 0)
  rw [h, CNF.vars_relabel]

private theorem count_vars_append (φ ψ : CNF Variable) (v : Variable) :
    (φ ++ ψ).vars.count v = φ.vars.count v + ψ.vars.count v := by
  simp [CNF.vars]

private theorem count_external_blocks_le {φ : CNF ℕ} (sites : List Point) (os : List (Occurrence ℕ))
    (hpaths : ∀ o ∈ os, 2 ≤ (occurrencePath φ o).length) (v : Variable) :
    (CNF.vars ((os.flatMap fun o => links sites o.2.2.2 (occurrencePath φ o)).map
      Prod.fst)).count v +
      (os.map (fun o => (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1)).count v ≤
      (os.flatMap fun o => pathSignals sites (occurrencePath φ o)).count v := by
  induction os with
  | nil => simp [CNF.vars]
  | cons o os ih =>
    have ht := ih (fun a ha => hpaths a (List.mem_cons_of_mem _ ha))
    have ho := count_links_lastLiteral_le sites o.2.2.2 (occurrencePath φ o)
      (hpaths o List.mem_cons_self) v
    rw [List.flatMap_cons, List.map_append, count_vars_append, List.map_cons,
      List.count_cons, List.flatMap_cons, List.count_append]
    have hc : [(lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1].count v =
        if (lastLiteral sites (occurrencePath φ o) o.2.2.2).1.1 == v then 1 else 0 := by
      simp [List.count_cons]
    rw [hc] at ho
    omega

/-- Internal variable names supplied by all selected translated crossover templates. -/
def crossingSignals (φ : CNF ℕ) : List Variable :=
  (crossingSites φ).flatMap fun p => Crossover.splitFormula.vars.map (fun v => (p, some v))

/-- Both directed halves of every actual source incidence path. -/
def allPathSignals (φ : CNF ℕ) : List Variable :=
  (Cslib.Logic.PL.occurrences φ).flatMap fun o =>
    pathSignals (crossingSites φ) (occurrencePath φ o)

/-- Every directed cell side in the actual source paths, including clause endpoints. -/
def allPathPorts (φ : CNF ℕ) : List (Point × Fin 4) :=
  (paths φ).flatMap fun r => r.consecutivePairs.flatMap fun e =>
    [(e.1, side e.1 e.2), (e.2, side e.2 e.1)]

private def portSignal (sites : List Point) (e : Point × Fin 4) : Variable :=
  (e.1, if e.1 ∈ sites then some (Crossover.splitTerminal e.2) else none)

private theorem allPathSignals_eq_map (φ : CNF ℕ) :
    allPathSignals φ = (allPathPorts φ).map (portSignal (crossingSites φ)) := by
  have h : allPathSignals φ =
      ((Cslib.Logic.PL.occurrences φ).map (occurrencePath φ)).flatMap
        (pathSignals (crossingSites φ)) := by
    rw [List.flatMap_map]
    rfl
  rw [h, occurrencePaths_eq_paths]
  unfold pathSignals pathHalfEdges allPathPorts portSignal signal
  simp [List.map_flatMap]

private theorem splitTerminal_injective : Function.Injective Crossover.splitTerminal := by decide

private theorem count_portSignal_terminal (sites : List Point) (p : Point) (i : Fin 4)
    (hp : p ∈ sites) (l : List (Point × Fin 4)) :
    (l.map (portSignal sites)).count (p, some (Crossover.splitTerminal i)) = l.count (p, i) := by
  have he (e : Point × Fin 4) :
      (portSignal sites e == (p, some (Crossover.splitTerminal i))) = (e == (p, i)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rcases e with ⟨q, j⟩
    by_cases hq : q = p
    · subst q
      simp [portSignal, hp, splitTerminal_injective.eq_iff]
    · simp [portSignal, Prod.mk.injEq, hq]
  induction l with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, List.count_cons, he, ih]

/-- A selected crossover terminal has at most one external literal half in the actual paths. -/
theorem count_allPathSignals_terminal_le_one {φ : CNF ℕ}
    (hw : ∀ c ∈ φ, c.length ≤ 3) (hv : ∀ v, φ.vars.count v ≤ 3)
    (p : Point) (i : Fin 4) (hp : p ∈ crossingSites φ) :
    (allPathSignals φ).count (p, some (Crossover.splitTerminal i)) ≤ 1 := by
  rw [allPathSignals_eq_map, count_portSignal_terminal _ _ _ hp]
  exact List.nodup_iff_count_le_one.mp (pathPorts_nodup hw hv) _

private theorem tagged_template_count (p q : Point) (v : Crossover.SplitVariable) :
    (Crossover.splitFormula.vars.map (fun w => (q, some w))).count (p, some v) =
      if q = p then Crossover.splitFormula.vars.count v else 0 := by
  by_cases h : q = p
  · subst q
    rw [ite_eq_left rfl]
    exact List.count_map_of_injective _ (fun w => (p, some w))
      (fun _ _ he => Option.some.inj (congrArg Prod.snd he)) _
  · rw [ite_eq_right h, List.count_eq_zero]
    intro hm
    obtain ⟨w, _, he⟩ := List.mem_map.mp hm
    exact h (congrArg Prod.fst he)

private theorem count_tagged_templates (ps : List Point) (p : Point)
    (v : Crossover.SplitVariable) :
    (ps.flatMap fun q => Crossover.splitFormula.vars.map (fun w => (q, some w))).count
      (p, some v) = ps.count p * Crossover.splitFormula.vars.count v := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    rw [List.flatMap_cons, List.count_append, tagged_template_count, List.count_cons, ih]
    by_cases h : q = p <;> simp [h, beq_iff_eq, Nat.add_mul, Nat.add_comm]

/-- Translated templates have the exact literal counts of one template at a selected site. -/
theorem count_crossingSignals_some (φ : CNF ℕ) (p : Point) (v : Crossover.SplitVariable) :
    (crossingSignals φ).count (p, some v) =
      (crossingSites φ).count p * Crossover.splitFormula.vars.count v :=
  count_tagged_templates _ _ _

/-- Ordinary signal names never occur inside a crossover template. -/
theorem count_crossingSignals_none (φ : CNF ℕ) (p : Point) :
    (crossingSignals φ).count (p, none) = 0 := by
  rw [List.count_eq_zero]
  simp [crossingSignals]

/-- The comparison uses the actual emitted formula. It only adds unused clause-cell halves. -/
theorem count_vars_rawFormula_le (φ : CNF ℕ) (v : Variable) :
    (rawFormula φ).vars.count v ≤ (crossingSignals φ).count v + (allPathSignals φ).count v := by
  have he := count_external_blocks_le (φ := φ) (crossingSites φ)
    (Cslib.Logic.PL.occurrences φ) (fun _ => occurrencePath_length_ge_two) v
  have hc : (CNF.vars (((crossingSites φ).flatMap crossingClauses).map Prod.fst)).count v =
      (crossingSignals φ).count v := by
    unfold crossingSignals
    induction crossingSites φ with
    | nil => simp [CNF.vars]
    | cons p ps ih =>
      rw [List.flatMap_cons, List.map_append, count_vars_append, vars_crossingClauses,
        List.flatMap_cons, List.count_append, ih]
  simp only [rawFormula, placedClauses, List.map_append, count_vars_append,
    vars_originalClauses, hc]
  unfold allPathSignals
  omega

/-- The fixed template has at most three literal positions per internal variable. -/
theorem count_vars_splitFormula : ∀ v, Crossover.splitFormula.vars.count v ≤ 3 := by
  decide +kernel

/-- Every terminal has exactly two internal literal positions, leaving one external incidence. -/
theorem count_vars_splitTerminal :
    ∀ i, Crossover.splitFormula.vars.count (Crossover.splitTerminal i) = 2 := by
  decide +kernel

end Cslib.Complexity.SAT.PlanarCompile
