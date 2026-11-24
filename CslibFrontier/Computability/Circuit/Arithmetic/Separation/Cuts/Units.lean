/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Pad10Star
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.FixedWidth

/-!
# Units of a bit string

The cutting argument of [AnthropicVPVNP2026] (Appendix J; module `Nc.Cut.Units`) writes the
strings that parties exchange on *units* of `ub` bits: a `1` and then zeros are appended to the
string, and the result is cut into blocks of `ub` bits. This is the padding
`Cslib.BitString.pad10star` followed by `Cslib.BitString.toBlocks`
(`Separation.unitsOf_eq_getElem?_toBlocks`), so the string can be recovered from its units
(`Separation.unitsOf_injective`).

A word over an alphabet whose letters are coded by `c` bits each is first turned into a bit
string (`Separation.bitsOf`), from which it can be recovered as well.

## Main definitions

* `Separation.UnitContent`: the content of a unit, absent or `ub` bits.
* `Separation.unitCount`, `Separation.unitsOf`: the number of units of a bit string, and its
  units.
* `Separation.bitsOf`: the bits of a word under a code of fixed width.

## Main results

* `Separation.unitsOf_injective`: a bit string is determined by its units.
* `Separation.bitsOf_injective`: a word is determined by its bits.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix J; module `Nc.Cut.Units`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation

variable {ub : ℕ} {L : List Bool} {k : ℕ}

/-- The content of a unit: absent, or `ub` bits. -/
abbrev UnitContent (ub : ℕ) : Type := Option (BitString ub)

/-- The number of units of a bit string: its blocks of `ub` bits after a `1` and zeros have been
appended. -/
@[expose] def unitCount (ub : ℕ) (L : List Bool) : ℕ := L.length / ub + 1

/-- The units of a bit string: unit `k` is the `k`-th block of `ub` bits of the string followed
by a `1` and zeros, and it is absent from `unitCount ub L` on. -/
@[expose] def unitsOf (ub : ℕ) (L : List Bool) (k : ℕ) : UnitContent ub :=
  if k < unitCount ub L then some fun b : Fin ub => (L ++ [true]).getD (k * ub + b) false else none

theorem unitsOf_of_lt (h : k < unitCount ub L) :
    unitsOf ub L k = some fun b : Fin ub => (L ++ [true]).getD (k * ub + b) false :=
  ite_eq_left h

theorem unitsOf_eq_none : unitsOf ub L k = none ↔ unitCount ub L ≤ k := by
  simp [unitsOf]

/-- The units of a bit string are the blocks of its padding. -/
theorem unitsOf_eq_getElem?_toBlocks (hub : 0 < ub) (L : List Bool) (k : ℕ) :
    unitsOf ub L k = (BitString.toBlocks ub (BitString.pad10star ub L))[k]? := by
  simp only [BitString.getElem?_toBlocks, BitString.length_pad10star_div hub,
    BitString.getD_pad10star]
  rfl

/-- A bit string is determined by its units. -/
theorem unitsOf_injective (hub : 0 < ub) : Function.Injective (unitsOf ub) := fun L L' h =>
  BitString.toBlocks_pad10star_injective hub <| List.ext_getElem? fun k => by
    rw [← unitsOf_eq_getElem?_toBlocks hub, ← unitsOf_eq_getElem?_toBlocks hub, h]

section Words

variable {Γ : Type*} {c : ℕ}

/-- The bits of a word whose letters are coded by `c` bits each. -/
@[expose] def bitsOf (cb : Γ → BitString c) (X : List Γ) : List Bool :=
  X.flatMap fun a => List.ofFn (cb a)

theorem length_bitsOf (cb : Γ → BitString c) (X : List Γ) :
    (bitsOf cb X).length = X.length * c :=
  List.length_flatMap_of_forall_length_eq fun _ _ => List.length_ofFn

/-- A word is determined by its bits, for an injective code of positive width. -/
theorem bitsOf_injective {cb : Γ → BitString c} (hcb : Function.Injective cb) (hc : 0 < c) :
    Function.Injective (bitsOf cb) :=
  List.flatMap_injective_of_forall_length_eq hc (fun _ => List.length_ofFn)
    (List.ofFn_injective.comp hcb)

end Words

end Cslib.Circuits.Arithmetic.Separation
