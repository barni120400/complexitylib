/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Chamber
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Incident
import Mathlib.Tactic.DeriveFintype

/-!
# The tree of a tower

The proof of Theorem H.2 of [AnthropicVPVNP2026] gathers units in a tree whose nodes
(`Cslib.CoveringTower.Tower.Node`) are the chambers of all levels of a
`Cslib.CoveringTower.Tower` and a root. For loads `Lf` on the edges of every level, the chosen
type of a level is the first type whose edges have the least sum of the squares of their loads;
the parent of a chamber of the level `j` is the host of its vertex of the chosen type, a chamber
of the level `j + 1`, and the units between a chamber and its parent are the loads of the edges
at the chamber. The hosts of a type are injective below the level `J`, so a chamber has at most
`b` children: at most one at every place.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], modules `Nc.Tow.Net` and `Nc.Tow.Tree`.

## Main definitions

* `Cslib.CoveringTower.Tower.Node`, `Cslib.CoveringTower.Tower.Node.ofChamber`: the nodes of the
  tree.
* `Cslib.CoveringTower.Tower.Node.lift`: a function on the nodes from functions on the chambers
  of every level.
* `Cslib.CoveringTower.Tower.chosenType`, `Cslib.CoveringTower.Tower.parentChamber`,
  `Cslib.CoveringTower.Tower.parentUnits`: the chosen type of a level, the parent of a chamber,
  and the units between a chamber and its parent.

## Main results

* `Cslib.CoveringTower.Tower.isLeast_chosenType`: the chosen type is the first type with the
  least sum of the squares of the loads of its edges.
* `Cslib.CoveringTower.Tower.card_children`: a chamber has at most `b` children.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(a), p. 45, and its proof ("One stage" and "Bounds", p. 47); modules `Nc.Tow.Net`,
  `Nc.Tow.Tree`
-/

public section

namespace Cslib.CoveringTower.Tower

open Finset

variable {h b D J r : ℕ}

/-- The nodes of the tree: the root, and the chambers of all levels of the tower. -/
inductive Node (T : Tower h b D J r) where
  /-- The root. -/
  | root
  /-- A chamber of the level `j`. -/
  | chamber (j : Fin (J + 1)) (c : T.X j)
  deriving DecidableEq, Fintype

variable {T : Tower h b D J r} {j j' : ℕ}

namespace Node

/-- The node of a chamber of the level `j ≤ J`. -/
@[expose] def ofChamber (hj : j ≤ J) (c : T.X j) : T.Node := .chamber ⟨j, Nat.lt_succ_of_le hj⟩ c

@[simp]
theorem ofChamber_inj {hj hj' : j ≤ J} {c c' : T.X j} :
    ofChamber hj c = ofChamber hj' c' ↔ c = c' := by
  simp [ofChamber]

theorem ofChamber_ne_of_ne (hjj : j ≠ j') {hj : j ≤ J} {hj' : j' ≤ J} {c : T.X j} {c' : T.X j'} :
    ofChamber hj c ≠ ofChamber hj' c' := by
  simp [ofChamber, hjj]

@[simp]
theorem ofChamber_ne_root {hj : j ≤ J} {c : T.X j} : ofChamber hj c ≠ root := by
  simp [ofChamber]

/-- A function on the nodes from a function on the chambers of every level and a value at the
root. -/
@[expose] def lift {α : Type*} (f : ∀ j, T.X j → α) (a : α) : T.Node → α
  | .root => a
  | .chamber j c => f j c

/-- The value of `Node.lift` at a chamber. -/
@[simp]
theorem lift_ofChamber {α : Type*} (f : ∀ j, T.X j → α) (a : α) (hj : j ≤ J) (c : T.X j) :
    (ofChamber hj c).lift f a = f j c :=
  rfl

end Node

/-- The sum of the squares of the loads of the edges of the type `i` at the level `j`. -/
private def sqSum (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) (i : Fin h) : ℕ :=
  ∑ e : T.Ed j, if T.ty e = i then Lf j e ^ 2 else 0

private theorem nonempty_minimizers (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) :
    (univ.filter fun i : Fin h => ∀ i', sqSum Lf j i ≤ sqSum Lf j i').Nonempty := by
  obtain ⟨i, -, hi⟩ := exists_min_image univ (sqSum Lf j) ⟨⟨0, hh⟩, mem_univ _⟩
  exact ⟨i, mem_filter.2 ⟨mem_univ _, fun i' => hi i' (mem_univ _)⟩⟩

variable (T) (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ)

/-- The chosen type at the level `j` for the loads `Lf` on the edges: the first type whose edges
have the least sum of the squares of their loads. -/
noncomputable def chosenType (j : ℕ) : Fin h :=
  (univ.filter fun i : Fin h => ∀ i', sqSum Lf j i ≤ sqSum Lf j i').min'
    (nonempty_minimizers hh Lf j)

/-- The parent of a chamber of the level `j`: the host of its vertex of the chosen type. -/
@[expose] noncomputable def parentChamber {j : ℕ} (c : T.X j) : T.X (j + 1) :=
  T.hostOf (T.chosenType hh Lf j) c

/-- The units between a chamber of the level `j` and its parent: the loads of the edges at the
chamber. -/
abbrev parentUnits (j : ℕ) (c : T.X j) : ℕ := T.incidentSum (Lf j) c

variable {T}

/-- The chosen type is the first type whose edges have the least sum of the squares of their
loads. -/
theorem isLeast_chosenType (j : ℕ) :
    IsLeast {i | ∀ i', ∑ e : T.Ed j, (if T.ty e = i then Lf j e ^ 2 else 0) ≤
      ∑ e : T.Ed j, if T.ty e = i' then Lf j e ^ 2 else 0} (T.chosenType hh Lf j) := by
  exact ⟨(mem_filter.1 (min'_mem _ _)).2, fun i hi => min'_le _ _ (mem_filter.2 ⟨mem_univ _, hi⟩)⟩

/-- A chamber of a level `j + 1 ≤ J` has at most `b` children. -/
theorem card_children {j : ℕ} (hj : j < J) (c' : T.X (j + 1)) :
    (univ.filter fun c : T.X j => T.parentChamber hh Lf c = c').card ≤ b := by
  refine (card_le_card_of_injOn (T.co (T.chosenType hh Lf j)) (fun _ _ => mem_univ _)
    fun c hc c₁ hc₁ hco => ?_).trans (card_univ.trans T.card_fl).le
  simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hc hc₁
  exact (T.vx_co hj.le _).1 (Prod.ext (T.host_inj hj _ (hc.trans hc₁.symm)) hco)

end Cslib.CoveringTower.Tower
