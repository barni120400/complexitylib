/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Incident

/-!
# The tree of the tower plan

The nodes of the tree of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module
`Nc.Tow.Tree`) are the chambers of all levels and a root. For loads on the edges of every level,
a chamber of the level `j` has as its parent the host of its vertex of the chosen type, the first
type whose edges have the least sum of the squares of their loads, and the units between a
chamber and its parent are the loads of the edges at the chamber.

## Main definitions

* `edgeLoads`: the loads of the edges of every level, from the loads of the targets.
* `chosenType`, `parentChamber`, `parentUnits`: the chosen type of a level, the parent of a
  chamber, and the units between a chamber and its parent.
* `Node.lift`: a function on the nodes from functions on the chambers of every level.

## Main results

* `edgeLoads_of_lt`, `Node.lift_ofChamber`: the values of `edgeLoads` and `Node.lift`.
* `isChosenType_iff`: the chosen type of a stage is `chosenType` of the loads of its edges.
* `card_children`: a chamber has at most `b` children.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(a), p. 45, and its proof ("One stage" and "Bounds", p. 47); module `Nc.Tow.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

variable {h b D J r m A : ℕ} {T : Tower h b D J r}

/-- The loads of the edges of the level `j`, from the loads of the targets; `0` above the last
level. -/
@[expose] def edgeLoads (L : Target T m A → ℕ) (j : ℕ) : T.Ed j → ℕ :=
  fun e => if hj : j < J + 1 then L (.edge ⟨j, hj⟩ e) else 0

/-- The loads of the edges of a level `j ≤ J`. -/
theorem edgeLoads_of_lt (L : Target T m A → ℕ) {j : ℕ} (hj : j < J + 1) (e : T.Ed j) :
    edgeLoads L j e = L (.edge ⟨j, hj⟩ e) :=
  dite_eq_left hj

/-- The sum of the squares of the loads of the edges of the type `i` at the level `j`. -/
private def sqSum (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) (i : Fin h) : ℕ :=
  ∑ e : T.Ed j, if T.ty e = i then Lf j e ^ 2 else 0

private theorem nonempty_minimizers (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) :
    (univ.filter fun i : Fin h => ∀ i', sqSum Lf j i ≤ sqSum Lf j i').Nonempty := by
  obtain ⟨i, -, hi⟩ := exists_min_image univ (sqSum Lf j) ⟨⟨0, hh⟩, mem_univ _⟩
  exact ⟨i, mem_filter.2 ⟨mem_univ _, fun i' => hi i' (mem_univ _)⟩⟩

variable (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ)

/-- The chosen type at the level `j` for the loads `Lf` on the edges: the first type whose edges
have the least sum of the squares of their loads. -/
noncomputable def chosenType (j : ℕ) : Fin h :=
  (univ.filter fun i : Fin h => ∀ i', sqSum Lf j i ≤ sqSum Lf j i').min'
    (nonempty_minimizers hh Lf j)

/-- The chosen type of a stage (`IsChosenType`) is the chosen type of the loads of its edges. -/
theorem isChosenType_iff {L : Target T m A → ℕ} {j : Fin (J + 1)} {i : Fin h} :
    IsChosenType L j i ↔ i = chosenType hh (edgeLoads L) j := by
  have hL (e : T.Ed j) : edgeLoads L j e = L (.edge j e) := edgeLoads_of_lt L j.2 e
  have h1 : IsChosenType L j (chosenType hh (edgeLoads L) j) := by
    simpa [IsChosenType, sqLoad, chosenType, sqSum, hL] using
      isLeast_min' _ (nonempty_minimizers hh (edgeLoads L) j)
  exact ⟨fun hi => hi.unique h1, fun hi => hi ▸ h1⟩

/-- The parent of a chamber of the level `j`: the host of its vertex of the chosen type. -/
@[expose] noncomputable def parentChamber {j : ℕ} (c : T.X j) : T.X (j + 1) :=
  T.hostOf (chosenType hh Lf j) c

/-- The units between a chamber of the level `j` and its parent: the loads of the edges at the
chamber. -/
abbrev parentUnits (j : ℕ) (c : T.X j) : ℕ := T.incidentSum (Lf j) c

/-- A chamber of a level `j + 1 ≤ J` has at most `b` children. -/
theorem card_children {j : ℕ} (hj : j < J) (c' : T.X (j + 1)) :
    (univ.filter fun c : T.X j => parentChamber hh Lf c = c').card ≤ b := by
  refine (card_le_card_of_injOn (T.co (chosenType hh Lf j)) (fun _ _ => mem_univ _)
    fun c hc c₁ hc₁ hco => ?_).trans (card_univ.trans T.card_fl).le
  simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hc hc₁
  exact (T.vx_co hj.le _).1 (Prod.ext (T.host_inj hj _ (hc.trans hc₁.symm)) hco)

/-- A function on the nodes from a function on the chambers of every level and a value at the
root. -/
@[expose] def Node.lift {α : Type*} (f : ∀ j, T.X j → α) (a : α) : Node T → α
  | .root => a
  | .chamber j c => f j c

/-- The value of `Node.lift` at a chamber. -/
@[simp]
theorem Node.lift_ofChamber {α : Type*} (f : ∀ j, T.X j → α) (a : α) {j : ℕ} (hj : j ≤ J)
    (c : T.X j) : Node.lift f a (.ofChamber hj c) = f j c :=
  rfl

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
