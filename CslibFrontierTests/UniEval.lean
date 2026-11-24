/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Bounds
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.OfTree
import Mathlib.Algebra.Ring.Int.Defs

/-! Tests of the correctness of the universal machine under ordinary imports:

* the input word of a tree, the cost of a step of the evaluation and the number of steps;
* the formula coded by a tree, by its opcode;
* the accepting runs of the machine on a plain instance, as a client uses them: checked globally
  (`Mach.GV`), with weights that sum to the plain sum, and of at most `runLength` steps. -/

set_option linter.privateModule false

namespace CslibFrontierTests.UniEval

open Cslib.Circuits.Arithmetic.Separation Uni Interpreter

/-- The word of a tree lists its brackets in preorder. -/
example : treeWord (.cons .nil (.cons .nil .nil)) = [true, false, true, false, false] := rfl

/-- Names of the support `{[true], [true, false, true]}` have at most three bits, so a step of
the evaluation costs at most `40 + 2 * 3` steps of the machine. -/
example : nameLength {[true], [true, false, true]} = 3 ∧
    codeCost {[true], [true, false, true]} = 46 := by decide

example : runLength {[true], [true, false, true]} 5 7 = 3 * 7 + 46 * 5 + 10 := by decide

/-- The opcode `2` is `hd`. -/
example (a : Tree) : Fm.ofTree (.cons (Tree.num 2) a) = .hd (Fm.ofTree a) := by
  simp [Fm.ofTree_cons]

/-- Numbers from `11` on are no opcodes: the formula fails. -/
example (a : Tree) : Fm.ofTree (.cons (Tree.num 11) a) = .fail := by
  simp [Fm.ofTree_cons]

/-- The accepting runs of the universal machine on a plain instance. -/
example {θ : List Bool → ℤ} (hθ : ∀ q, q ∉ ({[true]} : Finset (List Bool)) → θ q = 0) {τ : ℕ}
    {z : Tree} (h : Plain θ τ z) :
    ∃ R : Finset (List (universalMachine θ {[true]}).Step),
      (∀ tr, tr ∈ R ↔ Mach.GV (initState {[true]} z) tr) ∧ ∑ tr ∈ R, Mach.wts tr = pv θ z ∧
        ∀ tr ∈ R, tr.length ≤ runLength {[true]} τ z.size := by
  obtain ⟨R, h₁, h₂, h₃⟩ := sumTo_universalMachine hθ h
  refine ⟨R, fun tr => ?_, h₂, fun tr htr => ?_⟩
  · rw [h₁, Mach.gv_iff (closed_initState z)]
  · have := h₃ tr htr
    rw [← natCast_runLength] at this
    exact_mod_cast this

end CslibFrontierTests.UniEval
