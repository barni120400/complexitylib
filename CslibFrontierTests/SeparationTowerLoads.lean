/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Capacity

/-! Tests of the loads and capacities of the tower plan, as a client that sees only the public
statements.

* `Tower.incidentSum` on a tower with one chamber on every level and no edges.
* `startBound` and `moveCap` on small numbers, for that tower and laws without slots.
* `towerPlan_ok_moveCap` for an arbitrary tower, under its hypotheses: a slot is given at most
  `moveCap` units. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTowerLoads

open Finset Cslib Cslib.CoveringTower Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Cut Cslib.Circuits.Arithmetic.Separation.TowerPlan

/-- One chamber on every level, no edges, no types. -/
private def pointTower (r : ℕ) : Tower 0 1 1 0 r where
  X _ := Unit
  Ed _ := Empty
  V _ _ := Empty
  Fl := Unit
  Nr := Empty
  e0 e := e.elim
  e1 e := e.elim
  e_ne e := e.elim
  ty e := e.elim
  card_ed _ _ i := i.elim0
  deg _ _ _ i := i.elim0
  vx i := i.elim0
  co i := i.elim0
  vx_co _ i := i.elim0
  card_fl := rfl
  cN ν := ν.elim
  dN ν := ν.elim
  n_ne ν := ν.elim
  nr _ i := i.elim0
  nr_vx0 _ i := i.elim0
  nr_vx1 _ i := i.elim0
  nr_co _ i := i.elim0
  π c := c
  πE e := e
  πV v := v
  π_ends _ e := e.elim
  π_ty _ e := e.elim
  card_X _ hj := absurd hj (Nat.not_lt_zero _)
  fibre hj := absurd hj (Nat.not_lt_zero _)
  π_vx _ i := i.elim0
  π_co _ i := i.elim0
  host i := i.elim0
  host_inj _ i := i.elim0
  host_vx _ i := i.elim0

/-- A law with one role and neither slots nor channels. -/
private def pointLaw (F : Type) [CommSemiring F] : Law F where
  Role := Unit
  Slot := Empty
  Channel := Empty
  Index := Unit
  slotEnd e := e.elim
  slotEnd_ne e := e.elim
  channelEnd ν := ν.elim
  channelEnd_ne ν := ν.elim
  labelLength := 1
  label _ _ := false
  label_injective _ _ _ := rfl
  length _ ν := ν.elim
  table _ _ _ _ := 1
  identity X := by simp
  connected _ _ _ _ := rfl

/-- The laws at the vertices of the tower without edges, with scale `1` and contraction `0`. -/
private def pointLaws (F : Type) [CommSemiring F] (r : ℕ) : VertexLaws F (pointTower r) where
  Kind := Unit
  law _ := pointLaw F
  place _ := Equiv.refl Unit
  nearPair _ := Equiv.refl Empty
  place_channelEnd _ ν := ν.elim
  labelLength_pos _ := le_rfl
  nonempty_index _ := ⟨()⟩
  scale := 1
  scale_pos := Nat.one_pos
  contraction := 0
  contraction_nonneg := le_rfl
  lengthBound := 0
  lengthBound_le := by simp
  exists_le_card_slot _ _ _ :=
    ⟨(), fun q hq => absurd (Sym2.ind (fun _ _ => Sym2.mk_isDiag_iff.2 rfl) q) hq⟩
  sum_length_sq_le _ _ := by
    have : IsEmpty (pointLaw F).Channel := inferInstanceAs (IsEmpty Empty)
    simp

/-! ### The tower without edges -/

/-- Without edges, every chamber has no units towards its parent. -/
example (n : (pointTower 2).Ed 0 → ℕ) : (pointTower 2).incidentSum n () = 0 :=
  sum_eq_zero fun e _ => (e : Empty).elim

/-- After the start, an edge carries at most `3 * (5 / 1 + 2 * 2) = 27` units, for routes that
use every edge at most `3` times, `2` base parties and `5` initial units per base party. -/
example : startBound (pointTower 1) 3 2 5 = 27 := by
  rw [startBound, @Fintype.card_unique _ (inferInstanceAs (Unique Unit))]

/-- The laws without slots have no contraction and the tower has no types, so the norms of the
loads are bounded by `0` and a move uses at most `U0 + 2` units. -/
example : moveCap (pointLaws ℕ 1) 5 3 2 7 = 7 := by
  simp [moveCap, normBound, pointLaws]

/-! ### The rules with the capacity, for an arbitrary tower -/

variable {F : Type} [CommSemiring F] {h b D J r m Uu A A' U0 U1 lhat : ℕ}

/-- If the parameters of the tower and the laws allow a rate `ρ ≤ 1`, a slot of the tower plan is
given at most `moveCap` units. -/
example {T : Tower h b D J r} (R : Routes T m Uu) {ch : Fin A ↪ T.X 0} (FL : VertexLaws F T)
    (Pl : Placement T ch A') {ρ : ℝ} (hρ : StageRate FL ρ) (hρ1 : ρ ≤ 1)
    (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)
    (z : (moves R FL Pl).Slot) :
    ((towerPlan R FL Pl lhat U0 U1).given n o z).card ≤ moveCap FL U0 Uu A lhat :=
  have hP := towerPlan_ok_moveCap (R := R) (Pl := Pl) (lhat := lhat) (U1 := U1) hρ hρ1
  (hP.card_given_le n o z).trans (hP.count_le n o z.1)

end CslibFrontierTests.SeparationTowerLoads
