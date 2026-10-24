/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Total decoders with plain degree certificates

A decoder is total on every word, inverts its encoding, and carries independent cost and encoded
output degrees. These definitions and the independent constructors are moved from Decoder;
compound encodings are reexported by that original module.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- A total decoder with polynomial cost and encoded-output growth on every input word. -/
structure Decoder {α : Type} (enc : α ↪ List Bool) where
  /-- The decoded value of any word. -/
  decode : List Bool → α
  /-- Decoding inverts the encoding. -/
  decode_enc (a : α) : decode (enc a) = a
  /-- Decoding has independent cost and encoded-output degrees, including zero. -/
  computable : ∃ d e, ComputableInDegree decode encBits enc d e

namespace Decoder
variable {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool}

/-- Every total decoder has a plain polynomial-time certificate. -/
@[fun_prop]
theorem computableInPolyTime (D : Decoder enc) : ComputableInPolyTime D.decode encBits enc := by
  obtain ⟨_, _, h⟩ := D.computable
  exact h.computableInPolyTime

/-- Bit strings are their own encoding. -/
def bits : Decoder encBits where
  decode := id
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bits_degree⟩

/-- Unary numbers are decoded by the length of the word. -/
def unary : Decoder encUnary where
  decode w := w.length
  decode_enc n := by simp
  computable := ⟨1, 1, Internal.DecoderWords.unary_degree⟩

/-- Booleans are decoded from the first symbol. -/
def bool : Decoder encBool where
  decode w := w.headD false
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bool_degree⟩

/-- Transport a decoder along an encoding equality and a right inverse. -/
def map (D : Decoder enc) (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b)
    (henc : ∀ a, enc' (f a) = enc a) : Decoder enc' where
  decode w := f (D.decode w)
  decode_enc b := by
    conv_lhs => rw [← hfg b, henc, D.decode_enc]
    exact hfg b
  computable :=
    let ⟨d, e, h⟩ := D.computable
    ⟨d, e, h.of_enc_eq fun w => henc _⟩

end Decoder
end Turing.MultiTapeTM
