/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import Lean.Elab.Command

/-! Plain-field total decoder clients, preserving malformed-word and independent-degree scope. -/
open Turing.MultiTapeTM
example : Decoder.bits.decode [] = [] := rfl
example (w : List Bool) : Decoder.bits.decode w = w := rfl
example : Decoder.bool.decode [] = false := rfl
example (w : List Bool) : Decoder.bool.decode (true :: w) = true := rfl
example : Decoder.unary.decode [false, true, false] = 3 := rfl
example (n : ℕ) : Decoder.unary.decode (encUnary n) = n := Decoder.unary.decode_enc n
example : ComputableInPolyTime Decoder.bool.decode encBits encBool :=
  Decoder.bool.computableInPolyTime
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    ∃ d e, ComputableInDegree D.decode encBits a d e := D.computable
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    ComputableInPolyTime D.decode encBits a := by fun_prop
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    (Decoder.map D id id (fun _ => rfl) (fun _ => rfl)).decode = D.decode := rfl

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

-- Both degrees may be zero; the field does not impose an output charge on workspace.
example {α : Type} (a : α ↪ List Bool) (decode : List Bool → α)
    (hround : ∀ x, decode (a x) = x) (h : ComputableInDegree decode encBits a 0 0) :
    Decoder a := ⟨decode, hround, 0, 0, h⟩
