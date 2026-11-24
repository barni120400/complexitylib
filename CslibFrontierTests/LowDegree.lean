/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize
import Mathlib.Data.Rat.Init

/-! Tests of the low-degree layer:

* the gate list of a circuit (`ComputedWithin.exists_steps`);
* polynomials along a line;
* full tries of constants. -/

namespace CslibFrontierTests.LowDegree

open MvPolynomial Cslib.Circuits.Arithmetic Cslib.Circuits.Arithmetic.Separation.Interpreter

/-- A variable is computed with one node, so the gate list has it at entry `0`. -/
example : ∃ l : ℕ → MvPolynomial (Fin 1) ℚ, l 0 = X 0 := by
  obtain ⟨l, -, k, hk, e⟩ := (computedWithin_X (K := ℚ) (0 : Fin 1)).exists_steps
  obtain rfl : k = 0 := by omega
  exact ⟨l, e⟩

/-- Every entry of the gate list of `X 0 * X 0` is a variable, a constant, or the sum or product of
two earlier entries. -/
example : ∃ l : ℕ → MvPolynomial (Fin 1) ℚ, (∀ k < 3, (∃ i, l k = X i) ∨ (∃ a, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
    ∃ k < 3, l k = X 0 * X 0 :=
  ((computedWithin_X (K := ℚ) (0 : Fin 1)).mul (computedWithin_X 0)).exists_steps

/-- Along a line, the value at `u` of a polynomial of degree at most `1` is the sum of its first two
coefficients. -/
example (u : Fin 1 → ℚ) : ∑ i ∈ Finset.range 2, (line u (X 0 : MvPolynomial (Fin 1) ℚ)).coeff i =
    u 0 := by
  rw [sum_coeff_line_eq_eval (d := 1) _ _ (by simp) (by norm_num)]
  simp

/-- The full trie of depth `1` has the constant `f [true]` at the name `true, false`. -/
example (f : List Bool → ℚ) : (KT.full 1 f).lk ([true] ++ [false]) = f [true] :=
  KT.lk_full f rfl

end CslibFrontierTests.LowDegree
