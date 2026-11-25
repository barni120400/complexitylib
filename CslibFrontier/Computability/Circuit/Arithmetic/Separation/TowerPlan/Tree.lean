/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts

/-!
# The tree of the tower plan

The tree of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; module `Nc.Tow.Tree`)
is the tree of the tower (`Cslib.CoveringTower.Tower.Node`) for the loads of the edges of every
level, which the plan reads off the loads of its targets (`edgeLoads`). The chosen type of a stage
(`IsChosenType`) is then the chosen type of the tree (`Cslib.CoveringTower.Tower.chosenType`).

## Main definitions

* `edgeLoads`: the loads of the edges of every level, from the loads of the targets.

## Main results

* `edgeLoads_of_lt`: the loads of the edges of a level `j ≤ J`.
* `isChosenType_iff`: the chosen type of a stage is `chosenType` of the loads of its edges.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(a), p. 45, and its proof ("One stage" and "Bounds", p. 47); module `Nc.Tow.Tree`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Cslib.CoveringTower

variable {h b D J r m A : ℕ} {T : Tower h b D J r}

/-- The loads of the edges of the level `j`, from the loads of the targets; `0` above the last
level. -/
@[expose] def edgeLoads (L : Target T m A → ℕ) (j : ℕ) : T.Ed j → ℕ :=
  fun e => if hj : j < J + 1 then L (.edge ⟨j, hj⟩ e) else 0

/-- The loads of the edges of a level `j ≤ J`. -/
theorem edgeLoads_of_lt (L : Target T m A → ℕ) {j : ℕ} (hj : j < J + 1) (e : T.Ed j) :
    edgeLoads L j e = L (.edge ⟨j, hj⟩ e) :=
  dite_eq_left hj

/-- The chosen type of a stage (`IsChosenType`) is the chosen type of the loads of its edges. -/
theorem isChosenType_iff (hh : 0 < h) {L : Target T m A → ℕ} {j : Fin (J + 1)} {i : Fin h} :
    IsChosenType L j i ↔ i = T.chosenType hh (edgeLoads L) j := by
  have hL (e : T.Ed j) : edgeLoads L j e = L (.edge j e) := edgeLoads_of_lt L j.2 e
  have h1 : IsChosenType L j (T.chosenType hh (edgeLoads L) j) := by
    simpa [IsChosenType, sqLoad, hL] using Tower.isLeast_chosenType hh (edgeLoads L) j
  exact ⟨fun hi => hi.unique h1, fun hi => hi ▸ h1⟩

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
