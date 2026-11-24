/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Rules
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-! Tests of the tower plan, as a client that sees only the public statements.

* The relay law: its tables, its identity for one bit, and `Cut.Law.pow` for `B` bits.
* The times and the targets of relays in an arbitrary tower.
* A tower with one chamber on every level and no edges, with routes, laws at its vertices and a
  placement: this shows that `VertexLaws` and `Placement` are inhabited. Its plan has no moves, so
  `towerPlan_ok` applies to it with the bound `0`.
* `towerPlan_ok` for an arbitrary tower, under its hypotheses: a slot is given at most `cap`
  units. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationTowerPlan

open Finset Cslib Cslib.CoveringTower Cslib.Circuits.Arithmetic.Separation
  Cslib.Circuits.Arithmetic.Separation.Cut Cslib.Circuits.Arithmetic.Separation.TowerPlan

variable {F : Type} [CommSemiring F] {h b D J r m Uu A A' U0 U1 lhat cap : ℕ}

/-! ### The relay law -/

/-- The middle role of a relay accepts equal bits on its two channels, and only those. -/
example : relayTable ℕ 1 (fun _ => true) (fun _ _ => false) = 1 := by simp [relayTable]

example : relayTable ℕ 1 (fun _ => true) (fun ν _ => ν.1) = 0 := by simp [relayTable]

example : relayChannelEnd true false = 1 ∧ relaySlotEnd () true = 2 := by decide

/-- The identity of the relay for one bit: if the two copies agree, exactly one choice of the two
bits on the channels passes all three tables. -/
example (X : Fin 3 → Unit → Bool) (hX : X 0 () = X 2 ()) :
    ∑ _i : Unit, ∑ g : Bool → BitString 1,
      ∏ p, relayTable F p (fun e => X p e.1) (fun ν => g ν.1) = 1 :=
  ((relayLaw F).identity X).symm.trans (ite_eq_left fun _ => hX)

/-- The power of the relay law: `B` bits shared by the roles `0` and `2` are led through the
role `1`. -/
example (B : ℕ) (X : Fin 3 → Fin B → Unit → Bool) :
    (if ∀ e k, X 0 k e = X 2 k e then (1 : F) else 0) =
      ∑ _i : Fin B → Unit, ∑ g : Bool → (k : Fin B) → BitString 1,
        ∏ p, ∏ k, relayTable F p (fun e => X p k e.1) fun ν => g ν.1 k :=
  (relayLaw F).pow B X

example : (relayLaw F).LengthLE 1 := fun _ _ => le_rfl

/-! ### Relays and targets in an arbitrary tower -/

example : endTime 2 3 = 19 := by decide

section

variable {T : Tower h b D J r} (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (e : T.Ed J)

/-- The relay of an edge of the last stage goes through the root, at the last time, and its
units stay where they are. -/
example : (Relay.final e : Relay T m A).party R ch 1 = .root := rfl

example : (Relay.final e : Relay T m A).time m + 1 = endTime J m := rfl

example : (Relay.final e : Relay T m A).input = .edge (Fin.last J) e := rfl

example (d : Bool) : (Relay.final e : Relay T m A).target R ch d = .done := rfl

/-- The two ends of an edge of the last stage are different nodes. -/
example : Node.ofChamber le_rfl (T.e0 e) ≠ Node.ofChamber le_rfl (T.e1 e) := fun he =>
  absurd (Relay.party_injective (R := R) (ch := ch) (x := .final e) trivial (a₁ := 0) (a₂ := 2) he)
    (by decide)

/-- The units of a channel of a relay are given later than the relay. -/
example (x : Relay T m A) (d : Bool) (y : Relay T m A) (hy : x.target R ch d = .relay y) :
    x.time m < y.time m := by
  simpa [hy, Target.time] using x.time_lt_time_target (R := R) (ch := ch) d

end

/-! ### A tower without edges -/

/-- One chamber on every level, no edges, no types. -/
def pointTower (r : ℕ) : Tower 0 1 1 0 r where
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

/-- The empty routes of the tower without edges. -/
def pointRoutes (r m : ℕ) : Routes (pointTower r) m 0 where
  rt _ _ := []
  walk _ _ := rfl
  len _ _ := Nat.zero_le _
  use e := e.elim

/-- A law with one role and neither slots nor channels: its identity is `1 = 1`. -/
def pointLaw (F : Type) [CommSemiring F] : Law F where
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

/-- The laws at the vertices of the tower without edges: there are no pairs of different places,
so the law without slots serves every load. -/
def pointLaws (F : Type) [CommSemiring F] (r : ℕ) : VertexLaws F (pointTower r) where
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

/-- The one base party at the one chamber of the level `0`. -/
def pointBase (r : ℕ) : Fin 1 ↪ (pointTower r).X 0 :=
  ⟨fun _ => (), fun _ _ _ => Subsingleton.elim _ _⟩

/-- The chamber is at the base party, and the root at the extra party. -/
def pointPlacement (r : ℕ) : Placement (pointTower r) (pointBase r) 1 where
  party :=
    { toFun := fun | .root => 1 | .chamber _ _ => 0
      invFun := fun i => if i = 0 then .chamber 0 () else .root
      left_inv := by
        rintro (_ | ⟨j, c⟩)
        · rfl
        · obtain rfl : j = 0 := Fin.ext (Nat.lt_one_iff.1 j.2)
          rfl
      right_inv := by rintro ⟨_ | _ | i, hi⟩ <;> first | rfl | omega }
  party_base a := by
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl

/-- The plan of the tower without edges has no moves, and it obeys the rules with the bound
`0`. -/
example (hr : 0 < r) :
    (towerPlan (pointRoutes r m) (pointLaws F r) (pointPlacement r) lhat U0 U1).Ok 0 :=
  towerPlan_ok hr Nat.one_pos fun n o mv => by
    rcases mv with ⟨x, hx⟩ | l
    · rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
      · exact absurd (Subsingleton.elim a c) hx.1
      · exact j.elim0
      · exact j.elim0
      · exact e.elim
    · exact l.stage.elim0

/-! ### The rules for an arbitrary tower -/

/-- In the tower plan a slot is given at most `cap` units, if every move uses at most `cap`
units. The bound `hcap` is a hypothesis here. -/
example {T : Tower h b D J r} (R : Routes T m Uu) {ch : Fin A ↪ T.X 0} (FL : VertexLaws F T)
    (Pl : Placement T ch A') (hr : 0 < r) (hb : 0 < b)
    (hcap : ∀ (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1) mv,
      moveCount lhat (initialCounts n) (outcomeOf R FL Pl o) mv ≤ cap)
    (n : Fin A → Fin A → Fin (U0 + 1)) (o : (moves R FL Pl).Channel → Fin U1)
    (z : (moves R FL Pl).Slot) : ((towerPlan R FL Pl lhat U0 U1).given n o z).card ≤ cap :=
  have hP := towerPlan_ok hr hb hcap
  (hP.card_given_le n o z).trans (hP.count_le n o z.1)

end CslibFrontierTests.SeparationTowerPlan
