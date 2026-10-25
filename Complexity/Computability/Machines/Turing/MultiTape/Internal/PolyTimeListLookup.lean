/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Index
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import Mathlib.Data.List.GetD

/-! # Direct plain list lookup and first occurrence

Unary dropping uses the existing full-prefix fold and the codec's bare tail machine.
Fixed-default lookup uses the bare head machine, without an inhabitedness assumption.
First occurrence uses the original credited Boolean/counter fold.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime
open Cslib Internal.ListIndex
variable {α : Type} {encA : α ↪ List Bool}

private theorem tailPlain {encL : List α ↪ List Bool} [ListEncoding encA encL] :
    ComputableInPolyTime List.tail encL encL := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.tail (enc₁ := encA) (enc := encL)
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => (htm l).computesInTimeAndSpace⟩

private theorem headPlain {encL : List α ↪ List Bool} [ListEncoding encA encL] (d : α) :
    ComputableInPolyTime (fun l : List α => l.headD d) encL encA := by
  obtain ⟨c, k, Q, hfin, tm, htm⟩ := ListEncoding.headD (enc₁ := encA) (enc := encL) d
  exact ⟨fun n => c * (n + 1), fun n => c * (n + 1), by fun_prop, by fun_prop,
    k, Q, hfin, tm, fun l => (htm l).computesInTimeAndSpace⟩

/-- Drop a unary number of elements, retaining arbitrary sized list encodings. -/
theorem dropUnary {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.drop p.2)
      (encPair encL encUnary) encL := by
  have heq (l : List α) (n : ℕ) :
      (List.replicate n true).foldl (fun acc _ => acc.tail) l = l.drop n := by
    simp [List.foldl_const, List.tail_iterate]
  have h := foldl' (encA := encBool) (encL := encBits)
    (list := fun p : List α × ℕ => List.replicate p.2 true) (step := fun acc _ => acc.tail)
    ((of_eq (encIn := encUnary) (encOut := encBits) fun _ => rfl).comp (snd encL encUnary))
    (fst encL encUnary) ((tailPlain (encA := encA) (encL := encL)).comp (fst encL encBool))
    (B := fun p => (encPair encL encUnary p).length) .self (fun p i _ => by
      rw [List.take_replicate, heq]
      have := SizedListEncoding.length_drop_le (encA := encA) (encL := encL) p.1 (min i p.2)
      simp only [length_encPair]
      omega)
  simpa only [heq] using h

/-- Lookup with an explicit default and unary index, in any sized list encoding. -/
@[fun_prop]
theorem listGetD {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] (d : α) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.getD p.2 d)
      (encPair encL encUnary) encA := by
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using (headPlain d).comp (dropUnary (encA := encA))

/-- The first occurrence, or the list length when absent; the returned index is unary. -/
@[fun_prop]
theorem idxOf [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × α => p.1.idxOf p.2)
      (encPair (encList enc) enc) encUnary := by
  have heq : ComputableInPolyTime (fun p : α × α => decide (p.1 = p.2))
      (encPair enc enc) encBool := (ComputableInO.eq enc).computableInPolyTime
    (.of_forall_le 1 2 fun p => by simp only [length_encPair]; nlinarith) .self
  have hor : ComputableInPolyTime (fun p : Bool × Bool => p.1 || p.2)
      (encPair encBool encBool) encBool := of_finite _
  have hstep : ComputableInPolyTime
      (fun q : (α × (Bool × ℕ)) × α => idxStep q.1.1 q.1.2 q.2)
      (encPair (encPair enc (encPair encBool encUnary)) enc) (encPair encBool encUnary) := by
    have hq := fst (encPair enc (encPair encBool encUnary)) enc
    have hn := hq.snd'.snd'
    have ha := snd (encPair enc (encPair encBool encUnary)) enc
    exact (hor.comp (hq.snd'.fst'.prod (heq.comp (ha.prod hq.fst')))).ite
      ((const true).prod hn) ((const false).prod (unary_succ.comp hn))
  have h := foldlWith_of_bounded_growth (snd (encList enc) enc) (fst (encList enc) enc)
    (const (false, 0)) hstep
    (growth := fun _ => 1) (.const 1) (by
      intro p state value _
      unfold idxStep
      split <;> simp)
  simpa only [Function.comp_def, foldl_idxStep, Bool.false_eq_true, ite_false, Nat.zero_add]
    using (snd encBool encUnary).comp h

end Turing.MultiTapeTM.ComputableInPolyTime
