/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderWordMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List

/-! # Direct certificates for total decoder leaves

These witnesses apply to every input word, with the original independent degree-one cost and
output bounds. The type-indexed Decoder field can reuse them without a higher tidy calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.DecoderWords

/-- A runtime word decodes to itself. -/
theorem bits_degree : ComputableInDegree id encBits encBits 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- The unary decoder counts every symbol, including malformed false symbols. -/
theorem unary_degree : ComputableInDegree List.length encBits encUnary 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, unaryLengthT.toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show unaryLengthT.q₀ = () from rfl, unaryLengthT_run, encUnary_apply,
    encBits, Function.Embedding.refl_apply] using
    unaryLengthT.computesInTimeAndSpace_toTM w

/-- The Boolean decoder returns false on empty input and the first symbol otherwise. -/
theorem bool_degree : ComputableInDegree (fun w : List Bool => w.headD false)
    encBits encBool 1 1 := by
  refine ⟨⟨fun w => 2 * w.length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one, encBits, Function.Embedding.refl_apply]; omega⟩,
    DegreeBounded.const 0, 0, _, inferInstance, (headDefaultT false).toTM, fun w => ?_⟩,
    ⟨1, fun w => by simp⟩⟩
  simpa only [show (headDefaultT false).q₀ = false from rfl, headDefaultT_run,
    encBool_apply, encBits, Function.Embedding.refl_apply] using
    (headDefaultT false).computesInTimeAndSpace_toTM w

end Turing.MultiTapeTM.Internal.DecoderWords
