/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.GenericRAM.Native.Nat

/-!
# Native bounded-natural certificate data preservation

Private test-only snapshots retain the old six raw proofs and twelve witness repackagings.
They register no certificates and export no compatibility interface. Kernel rfl checks compare
whole certificates and exposed time/space, rather than only their propositions.
-/

public section

namespace ComplexityTests.NativeNatConsumer
open Cslib.GenericRAM Turing.MultiTapeTM Cslib.GenericRAM.BoundedNat

namespace Old
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A literal is checked at every runtime bound, including zero. -/
private theorem constant_polyTime (c : ℕ) :
    ComputableTidilyInPolyTime (model.checkedConstant c) encNat (encOption encNat) := by
  change ComputableTidilyInPolyTime
    (fun k => if decide (c < k) then some c else none) _ _
  simpa only [decide_eq_true_eq, Function.comp_def] using
    (binary_lt.comp ((const c).prod (of_eq (encIn := encNat) fun _ => rfl))).ite_decide
      (const (some c)) (const none)

/-- Addition checks its result before accepting it. -/
private theorem operation_polyTime (op : model.operations.Op) :
    ComputableTidilyInPolyTime (model.checkedOp op)
      (encPair encNat (encPi encNat)) (encOption encNat) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encNat (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encNat (encPi encNat))
  have hadd := binary_add.comp (hx.prod hy)
  change ComputableTidilyInPolyTime
    (fun p : ℕ × (Fin 2 → ℕ) => if decide (p.2 0 + p.2 1 < p.1)
      then some (p.2 0 + p.2 1) else none)
    (encPair encNat (encPi encNat (Index := Fin 2))) (encOption encNat)
  simp only [decide_eq_true_eq]
  exact (binary_lt.comp (hadd.prod (fst encNat (encPi encNat)))).ite_decide
      ((optionSome encNat).comp hadd) (const none)

/-- Tests distinguish a false result from rejection of either invalid operand. -/
private theorem test_polyTime (t : model.tests.Op) :
    ComputableTidilyInPolyTime (fun p => model.evalTest p.1 t p.2)
      (encPair encNat (encPi encNat)) (encOption encBool) := by
  have hx := (pi_apply encNat (0 : Fin 2)).comp (snd encNat (encPi encNat))
  have hy := (pi_apply encNat (1 : Fin 2)).comp (snd encNat (encPi encNat))
  have hk := fst encNat (encPi encNat (Index := Fin 2))
  exact (binary_lt.comp (hx.prod hk)).ite_decide
    ((binary_lt.comp (hy.prod hk)).ite_decide
      ((optionSome encBool).comp (binary_lt.comp (hx.prod hy))) (const none)) (const none)

/-- Address extraction checks the runtime bound. -/
private theorem address_polyTime :
    ComputableTidilyInPolyTime (fun p => model.address p.1 p.2)
      (encPair encNat encNat) (encOption encNat) :=
  (binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))).ite_decide
    ((optionSome encNat).comp (snd encNat encNat)) (const none)

/-- Existing values are checked independently of newly produced values. -/
private theorem validMove_polyTime :
    ComputableTidilyInPolyTime (fun p => model.validMove p.1 p.2)
      (encPair encNat encNat) encBool :=
  binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))

/-- Both current and continuing control labels use this checked predicate. -/
private theorem validPC_polyTime :
    ComputableTidilyInPolyTime (fun p => model.validPC p.1 p.2)
      (encPair encNat encNat) encBool :=
  binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat))

/-- Complete native scalar evidence; no field assumes a RAM simulator. -/
private noncomputable def oldNativePrimitives : model.NativePrimitives encoding where
  constant c := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := constant_polyTime c
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  operation op := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := operation_polyTime op
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  test t := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := test_polyTime t
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  address := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := address_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  validMove := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := validMove_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  validPC := .ofPolyTime (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := validPC_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)

/-- The bounded-natural primitive bundle has polynomial resource bounds in all fields. -/
private theorem oldNativePrimitives_isPolynomial : oldNativePrimitives.IsPolynomial where
  constant c := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := constant_polyTime c
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  operation op := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := operation_polyTime op
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  test t := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := test_polyTime t
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  address := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := address_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  validMove := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := validMove_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)
  validPC := NativeCertificate.ofPolyTime_isPolynomial (by
    obtain ⟨t, s, ⟨T, hT, ht⟩, ⟨S, hS, hs⟩, k, Q, hfin, tm, htm⟩ := validPC_polyTime
    exact ⟨T, S, hT, hS, k, Q, hfin, tm,
      fun a => ((htm a).mono (ht a) (hs a)).computesInTimeAndSpace⟩)


end Old

/-- The resource selector cannot distinguish proofs of the same plain proposition. -/
public theorem ofPolyTime_data_eq {α β : Type} {f : α → β} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    (h₁ h₂ : ComputableInPolyTime f ei eo) :
    NativeCertificate.ofPolyTime h₁ = NativeCertificate.ofPolyTime h₂ := rfl

example : Old.oldNativePrimitives = nativePrimitives := rfl

example (c : ℕ) :
    (Old.oldNativePrimitives.constant c) = (nativePrimitives.constant c) := rfl
example (c : ℕ) :
    (Old.oldNativePrimitives.constant c).time = (nativePrimitives.constant c).time := rfl
example (c : ℕ) :
    (Old.oldNativePrimitives.constant c).space = (nativePrimitives.constant c).space := rfl

example (op : model.operations.Op) :
    (Old.oldNativePrimitives.operation op) = (nativePrimitives.operation op) := rfl
example (op : model.operations.Op) :
    (Old.oldNativePrimitives.operation op).time = (nativePrimitives.operation op).time := rfl
example (op : model.operations.Op) :
    (Old.oldNativePrimitives.operation op).space = (nativePrimitives.operation op).space := rfl

example (t : model.tests.Op) :
    (Old.oldNativePrimitives.test t) = (nativePrimitives.test t) := rfl
example (t : model.tests.Op) :
    (Old.oldNativePrimitives.test t).time = (nativePrimitives.test t).time := rfl
example (t : model.tests.Op) :
    (Old.oldNativePrimitives.test t).space = (nativePrimitives.test t).space := rfl

example :
    (Old.oldNativePrimitives.address) = (nativePrimitives.address) := rfl
example :
    (Old.oldNativePrimitives.address).time = (nativePrimitives.address).time := rfl
example :
    (Old.oldNativePrimitives.address).space = (nativePrimitives.address).space := rfl

example :
    (Old.oldNativePrimitives.validMove) = (nativePrimitives.validMove) := rfl
example :
    (Old.oldNativePrimitives.validMove).time = (nativePrimitives.validMove).time := rfl
example :
    (Old.oldNativePrimitives.validMove).space = (nativePrimitives.validMove).space := rfl

example :
    (Old.oldNativePrimitives.validPC) = (nativePrimitives.validPC) := rfl
example :
    (Old.oldNativePrimitives.validPC).time = (nativePrimitives.validPC).time := rfl
example :
    (Old.oldNativePrimitives.validPC).space = (nativePrimitives.validPC).space := rfl

end ComplexityTests.NativeNatConsumer
