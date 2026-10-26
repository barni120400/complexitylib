/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.TranscriptTree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! Native scalar-stage clients: composition, sparse padding, ties and repeated wires. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

private def root : Program signature 2 2 :=
  ScalarStage.append Program.empty (Fin.elim0 : Fin 0 → Fin 0)
    (fun (_ : Fin 1) (_ : Fin 0) => false) (fun _ => 1) (fun _ => 2) 3

private theorem root_eval (x : Fin 2 → Bool) :
    root.eval interpretation x 1 = (x 0 && x 1) := by
  change (ScalarStage.append _ _ _ _ _ _).eval interpretation x (Fin.last 1) = _
  rw [ScalarStage.eval_append_last]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Fin.sum_univ_two, funext_iff, h0, h1]

private theorem root_readers : (inputGates root).card = 1 := by
  rw [root, ScalarStage.card_inputGates_append]
  norm_num [inputGates, funext_iff]

-- The root's true branch has terminated. Only its false prefix gets a second-stage flag.
private def child : Program signature 2 4 :=
  ScalarStage.append root (fun _ : Fin 1 => 1)
    (fun (_ : Fin 1) (_ : Fin 1) => false) (fun _ => 1) (fun _ => 1) 3

private theorem child_eval (x : Fin 2 → Bool) :
    child.eval interpretation x 3 = (x 0 ^^ x 1) := by
  change (ScalarStage.append _ _ _ _ _ _).eval interpretation x (Fin.last 3) = _
  rw [ScalarStage.eval_append_last]
  simp only [root_eval]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [Fin.sum_univ_two, funext_iff, h0, h1]

private theorem child_root_eval (x : Fin 2 → Bool) :
    child.eval interpretation x 1 = root.eval interpretation x 1 := by
  exact ScalarStage.eval_append_castSucc root (fun _ : Fin 1 => 1)
    (fun (_ : Fin 1) (_ : Fin 1) => false) (fun _ => 1) (fun _ => 1) 3 x 1

example : (inputGates child).card = 2 := by
  rw [child, ScalarStage.card_inputGates_append, root_readers]
  norm_num [funext_iff]

-- The two native input-reading queries never fire together.
example (x : Fin 2 → Bool) :
    (child.eval interpretation x 1).toNat + (child.eval interpretation x 3).toNat ≤ 1 := by
  rw [child_root_eval, root_eval, child_eval]
  cases x 0 <;> cases x 1 <;> decide

-- Attach a native input-free OR readout. This is a real Circuit, not a semantic readout function.
private def orProgram : Program signature 2 5 :=
  child.gate (ScalarStage.queryLine (fun _ => 0)
    (fun j : Fin 2 => if j = 0 then 1 else 3) (fun _ => 1) 1)

private def orCircuit : Circuit signature 2 1 :=
  ⟨orProgram, fun _ => .gate 4⟩

example : orCircuit.size = 5 := rfl

example (x : Fin 2 → Bool) : orCircuit.eval interpretation x 0 = (x 0 || x 1) := by
  change orProgram.eval interpretation x (Fin.last 4) = _
  rw [orProgram, Program.eval_gate_last, ScalarStage.queryLine_eval]
  simp only [Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, zero_mul, zero_add, one_mul]
  rw [child_root_eval, root_eval, child_eval]
  cases x 0 <;> cases x 1 <;> norm_num

-- Repeated reads with contradictory requested bits must give a false indicator.
example (x : Fin 2 → Bool) (z : Fin 1 → Bool) :
    (ScalarStage.prefixLine (fun _ : Fin 2 => (0 : Fin 1))
      (fun j : Fin 2 => decide (j = 0))).eval interpretation x z = false := by
  cases hz : z 0 <;>
    norm_num [ScalarStage.prefixLine, Line.eval, interpretation,
      Fin.sum_univ_two, Function.comp_def, hz]

-- Empty prefixes produce the true flag even in dimension zero.
example : (ScalarStage.prefixLine (n := 0) (g := 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun _ => false)).eval interpretation
      (fun _ => false) (fun _ => false) = true := by
  rw [ScalarStage.prefixLine_eval]
  simp

-- Empty banks still emit a query. A nonzero direct vector is counted even when padding is false.
private def padded : Program signature 1 1 :=
  ScalarStage.append Program.empty (Fin.elim0 : Fin 0 → Fin 0)
    (Fin.elim0 : Fin 0 → Fin 0 → Bool) (fun _ => 1) Fin.elim0 2

example (x : Fin 1 → Bool) : padded.eval interpretation x 0 = false := by
  change (ScalarStage.append _ _ _ _ _ _).eval interpretation x (Fin.last 0) = _
  rw [ScalarStage.eval_append_last]
  cases hx : x 0 <;> norm_num [hx]

example : (inputGates padded).card = 1 := by
  rw [padded, ScalarStage.card_inputGates_append]
  norm_num [inputGates, funext_iff]

-- A zero direct vector, in contrast, adds no reader regardless of the helper bank.
example : (inputGates (ScalarStage.append (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
      (fun _ => 0) (fun _ => -1) 3)).card = 0 := by
  rw [ScalarStage.card_inputGates_append]
  simp [inputGates]

private noncomputable def signedWeight (i : Fin 2) : ℝ :=
  if i = 0 then -1 else 1 / 2

-- A fractional threshold is attained exactly; negative coefficients are allowed.
example : (ScalarStage.append (Program.empty : Program signature 2 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 1) (_ : Fin 0) => false)
      signedWeight (fun _ => 1 / 2) 3).eval interpretation
        (fun i => decide (i = 1)) (Fin.last 1) = true := by
  rw [ScalarStage.eval_append_of_match _ _ _ _ _ _ _ 0
    (fun _ _ _ => Subsingleton.elim _ _) (Subsingleton.elim _ _)]
  norm_num [signedWeight, Fin.sum_univ_two]

-- Without distinct patterns, two matching flags blend their adjustments. The selector theorem
-- correctly requires injectivity: here score 1 passes although either individual threshold is 2.
example : (ScalarStage.append (Program.empty : Program signature 1 0)
    (Fin.elim0 : Fin 0 → Fin 0) (fun (_ : Fin 2) (_ : Fin 0) => false)
      (fun _ => 1) (fun _ => 2) 3).eval interpretation
        (fun _ => true) (Fin.last 2) = true := by
  rw [ScalarStage.eval_append_last]
  norm_num [Fin.sum_univ_two, funext_iff]
