/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Capacity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EndUnits
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.EverHeld

/-! Tests of the units that the nodes of the tower plan ever hold and of the units in the end, as
a client that sees only the public statements.

* A tower with one type, one chamber on every one of two levels and no edges: the parents of its
  chambers and the units between the children of a chamber and the chamber.
* The node below the parent on a channel of a relay after the last stage.
* For an arbitrary tower, under the hypotheses of the statements: the units that a party ever
  holds, exactly, and those that a node ever holds, the units between a chamber and its parent in
  the end, the alive units in the end, and the possible outcomes in the form that
  `Cut.Plan.value_moves` needs. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTowerEnds

open Finset Cslib Cslib.CoveringTower Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Cut Cslib.Circuits.Arithmetic.Separation.TowerPlan

/-- One type, one chamber and one vertex on each of the levels `0` and `1`, no edges. -/
private def unitTower : Tower 1 1 1 1 0 where
  X _ := Unit
  Ed _ := Empty
  V _ _ := Unit
  Fl := Unit
  Nr := Empty
  e0 e := e.elim
  e1 e := e.elim
  e_ne e := e.elim
  ty e := e.elim
  card_ed _ _ _ := by simp
  deg _ _ _ _ := by simp
  vx _ _ := ()
  co _ _ := ()
  vx_co _ _ := ⟨fun _ _ _ => rfl, fun _ => ⟨(), rfl⟩⟩
  card_fl := rfl
  cN ν := ν.elim
  dN ν := ν.elim
  n_ne ν := ν.elim
  nr _ _ := ⟨fun e => e.1.elim, fun p => p.2.elim, fun e => e.1.elim, fun p => p.2.elim⟩
  nr_vx0 _ _ e := e.1.elim
  nr_vx1 _ _ e := e.1.elim
  nr_co _ _ e := e.1.elim
  π _ := ()
  πE e := e
  πV _ := ()
  π_ends _ e := e.elim
  π_ty _ e := e.elim
  card_X _ _ := rfl
  fibre _ e := e.elim
  π_vx _ _ _ := rfl
  π_co _ _ _ := rfl
  host _ _ := ()
  host_inj _ _ _ _ _ := rfl
  host_vx _ _ _ := rfl

/-! ### The tower with two levels -/

/-- The chamber of the level `0` has the chamber of the level `1` as its parent, and that one
the root. -/
example (Lf : ∀ j, unitTower.Ed j → ℕ) :
    (.ofChamber (Nat.zero_le 1) () : unitTower.Node).parent Nat.one_pos Lf =
      .ofChamber le_rfl () ∧
    (.ofChamber le_rfl () : unitTower.Node).parent Nat.one_pos Lf = .root :=
  ⟨rfl, rfl⟩

/-- Without edges, there are no units between the child of the chamber of the level `1` and that
chamber. -/
example (Lf : ∀ j, unitTower.Ed j → ℕ) : unitTower.childUnits Nat.one_pos Lf 1 () = 0 :=
  sum_eq_zero fun _ _ => sum_eq_zero fun e _ => (e : Empty).elim

/-! ### Relays and nodes in an arbitrary tower -/

variable {F : Type} [CommSemiring F] {h b D J r m Uu A A' U0 U1 lhat : ℕ}

/-- The node below the parent on the second channel of a relay after the last stage is the second
end of its edge, and the units of that channel are done. -/
example {T : Tower h b D J r} (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T)
    (e : T.Ed J) :
    (Relay.final e : Relay T m A).child R ch true = .ofChamber le_rfl (T.e1 e) ∧
      IsChild (.ofChamber le_rfl (T.e1 e))
        (⟨.relay (.final e) trivial, true⟩ : MoveChannel R ch FL) :=
  ⟨rfl, rfl, rfl⟩

/-! ### The units of the plan in an arbitrary tower -/

section

variable {T : Tower h b D J r} {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}
  {Pl : Placement T ch A'} (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)

/-- Under the conditions `StageRate`, the alive units between a chamber and its parent in the end
are at most `edgeUnitBound`. -/
example {ρ : ℝ} (hρ : StageRate FL ρ) {j : ℕ} (hj : j ≤ J) (c : T.X j) :
    (assignedUnits R FL Pl lhat n o (.ofChamber hj c)).card ≤ edgeUnitBound FL Uu A lhat ρ :=
  (card_assignedUnits_le _).trans (parentUnits_le hρ hj c)

/-- An alive unit of a channel that is current in the end is done: a channel of a law move is
never done. -/
example (l : VertexMove FL) (c : (FL.law l.kind).Channel) (ν : (moves R FL Pl).Channel)
    (hν : moveChannelEquiv R FL Pl ν = ⟨.vertex l, c⟩) (k : Fin U1)
    (hu : (.new ν k : PlanUnit R FL Pl U0 U1) ∈
      (towerPlan R FL Pl lhat U0 U1).cur n o (Fintype.card (Move R ch FL))) :
    ¬ IsAlive R FL Pl lhat n o (.new ν k) := fun ha => by
  have := unitTarget_eq_done_of_mem_cur hu ha
  rw [show unitTarget R FL Pl (.new ν k : PlanUnit R FL Pl U0 U1) =
    (moveChannelEquiv R FL Pl ν).1.target (moveChannelEquiv R FL Pl ν).2 from rfl, hν] at this
  simp [Move.target] at this

/-- A new unit between a node and its parent is alive. -/
example {P : T.Node} {ν : (moves R FL Pl).Channel} {k : Fin U1}
    (hu : (.new ν k : PlanUnit R FL Pl U0 U1) ∈ assignedUnits R FL Pl lhat n o P) :
    IsAlive R FL Pl lhat n o (.new ν k) := (new_mem_assignedUnits.1 hu).1

/-- No initial unit is between a node and its parent. -/
example {P : T.Node} (a c : Fin A) (k : Fin U0) :
    (.init a c k : PlanUnit R FL Pl U0 U1) ∉ assignedUnits R FL Pl lhat n o P := by
  simp

/-- The units that a party ever holds, exactly: the initial units of its strings and, for every
end of a channel at it, the outcome of the channel and one more unit. -/
example (p : Fin (A + A')) :
    heldCount R FL Pl n o p =
      (∑ a, ∑ b, if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then (n a b : ℕ) else 0) +
        ∑ ν with (ν.1 : ℕ) < Fintype.card (Move R ch FL),
          ∑ d, if (moves R FL Pl).channelParty ν d = p then (o ν : ℕ) + 1 else 0 :=
  Plan.card_filter_holds_seenAt _ p

/-- Possible outcomes are good, in the form of the hypothesis of `Cut.Plan.value_moves`. -/
example {ub : ℕ} (hub : 0 < ub) :
    ∀ n o x, (towerPlan R FL Pl lhat U0 U1).Possible n o ub x →
      (towerPlan R FL Pl lhat U0 U1).Good n o x :=
  fun _ _ _ => towerPlan_good_of_possible hub

/-- For good outcomes, what the party of a node ever holds alone is bounded by the bound for what
it holds and reads. -/
example (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hg : ∀ x, (towerPlan R FL Pl lhat U0 U1).Good n o x)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) {Sm : ℕ}
    (hSm : ∀ d, Fintype.card (FL.law d).Slot ≤ Sm) {ℓf : ℕ} (c : T.X J)
    (hini : ∀ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = .ofChamber le_rfl c →
      ∑ c', ((n a c' : ℕ) + n c' a) ≤ ℓf) :
    heldCount R FL Pl n o (Pl.party (.ofChamber le_rfl c)) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = .ofChamber le_rfl c then
        ℓf + 8 * m * lhat else 0) +
        channelEndCount R FL Pl (Pl.party (.ofChamber le_rfl c)) +
        (4 + (2 * Fintype.card T.Nr * FL.lengthBound + 1 + Sm) * Fintype.card FL.Kind) *
          (8 * T.parentUnits (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o))) J c +
            3 * T.childUnits hh (edgeLoads (load lhat (initialCounts n) (outcomeOf R FL Pl o)))
              J c) :=
  le_self_add.trans (heldCount_add_sum_roleUnits_le hr hb hh hg hnr hSm _ hini)

end

end CslibFrontierTests.SeparationTowerEnds
