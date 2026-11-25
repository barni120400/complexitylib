/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Machine

/-!
# Reading a tree as a formula, by cases on the opcode

`Interpreter.Fm.ofTree` is defined by well-founded recursion, so it does not unfold by itself.
This file states its two defining equations: the empty tree is `quote nil`, and a tree
`cons o a` is read according to the length of `o`. A statement about `Fm.ofTree c = F` for a
given `F` follows by `cases c`, rewriting, `split` and `cases`.

## Main results

* `Interpreter.Fm.ofTree_nil`, `Interpreter.Fm.ofTree_cons`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix I (the proof of Proposition I.1), module `Nc.Uni.EvThm` (which has eleven inversion
  lemmas `inv_quote`, …, `inv_mul` instead)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter.Fm

@[simp] theorem ofTree_nil : ofTree .nil = quote .nil := by rw [ofTree]

/-- The formula coded by `cons o a`, by cases on the opcode `o.len`. -/
theorem ofTree_cons (o a : Tree) : ofTree (.cons o a) =
    match o.len with
    | 0 => quote a
    | 1 => id
    | 2 => hd (ofTree a)
    | 3 => tl (ofTree a)
    | 4 => cons (ofTree a.hd) (ofTree a.tl)
    | 5 => ite (ofTree a.hd) (ofTree a.tl.hd) (ofTree a.tl.tl)
    | 6 => run (ofTree a.hd) (ofTree a.tl)
    | 7 => guess
    | 8 => fail
    | 9 => theta (ofTree a)
    | 10 => mul (ofTree a)
    | _ => fail := by
  rw [ofTree]
  rfl

end Cslib.Circuits.Arithmetic.Separation.Interpreter.Fm
