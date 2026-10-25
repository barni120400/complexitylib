/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.CircuitEvaluation
public import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized.Evaluation.PolyTime
public import Complexity.Computability.Circuit.Boolean.Layered.PolyTime
public import Complexity.Computability.Circuit.Boolean.Layered.Compile.PolyTime
public import Complexity.Computability.Circuit.Boolean.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Data.List.GetD

/-!
# Uniform native GSW circuit evaluation

The layered evaluator has one uniform polynomial clock in its full encoded input: the unary
dimensions, the circuit code and every input ciphertext. Copies are cut to the ciphertext width
and constants and NAND outputs have exactly that width, so every layer's encoding is bounded by
its node count times the ciphertext width, even on malformed circuits, references and words.
No correctness, key or noise hypothesis is used.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.computableInPolyTime_constSerialized`: noiseless constants.
* `Cslib.Crypto.Homomorphic.GSW.computableInPolyTime_evaluateNode`,
  `.computableInPolyTime_evaluateLayer`, `.computableInPolyTime_evaluateLayers`: layers.
* `Cslib.Crypto.Homomorphic.GSW.computableInPolyTime_evaluateCircuit`: compile and evaluate a
  circuit, including the selection of its output wire.

## References

* [C. Gentry, A. Sahai and B. Waters, Section 3.3][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Circuits Circuits.Boolean Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool} {n w : α → ℕ}

private theorem native_constSerialized {μ : α → Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hμ : ComputableTidilyInPolyTime μ input encBool) :
    ComputableTidilyInPolyTime (fun a => constSerialized (n a) (w a) (μ a)) input encBits := by
  unfold constSerialized
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply flatMapToBitsWithInput (range.comp (by fun_prop))
  apply bitsLow (by fun_prop)
  have hi : ComputableTidilyInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => p.1.1.2)
      (encPair (encPair (encPair input encUnary) encUnary) encUnary) encUnary := by fun_prop
  have hj : ComputableTidilyInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => p.2)
      (encPair (encPair (encPair input encUnary) encUnary) encUnary) encUnary := by fun_prop
  have hk : ComputableTidilyInPolyTime (fun p : ((α × ℕ) × ℕ) × ℕ => p.1.2)
      (encPair (encPair (encPair input encUnary) encUnary) encUnary) encUnary := by fun_prop
  have hgadget : ComputableTidilyInPolyTime
      (fun p : ((α × ℕ) × ℕ) × ℕ =>
        if p.1.1.2 = p.2 then (μ p.1.1.1).toNat * 2 ^ p.1.2 else 0)
      (encPair (encPair (encPair input encUnary) encUnary) encUnary) encNat := by
    simpa only [Function.comp_apply, beq_iff_eq] using (unary_beq hi hj).ite'
      (binary_mul' (unary_to_binary.comp (bool_toUnary.comp (by fun_prop)))
        (binary_pow' (const 2) hk)) (const 0)
  exact binary_mod' hgadget (binary_pow' (const 2) (by fun_prop))

/-- Write a noiseless constant ciphertext, charging every output bit. -/
@[fun_prop]
theorem computableInPolyTime_constSerialized {μ : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hμ : ComputableInPolyTime μ input encBool) :
    ComputableInPolyTime (fun a => constSerialized (n a) (w a) (μ a)) input encBits :=
  .of_tidy (native_constSerialized hn.tidy hw.tidy hμ.tidy)

private theorem native_evaluateNode {wires : α → List (List Bool)} {node : α → Layered.Node}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hwires : ComputableTidilyInPolyTime wires input (encList encBits))
    (hnode : ComputableTidilyInPolyTime node input Layered.encNode) :
    ComputableTidilyInPolyTime (fun a => evaluateNode (n a) (w a) (wires a) (node a))
      input encBits := by
  have hcode := Layered.computableInPolyTime_nodeCode.tidy.comp hnode
  have hfirst : ComputableTidilyInPolyTime
      (fun a => (wires a).getD (node a).code.2.1 []) input encBits :=
    listGetD_binary (encA := encBits) [] hwires (by fun_prop)
  have hsecond : ComputableTidilyInPolyTime
      (fun a => (wires a).getD (node a).code.2.2 []) input encBits :=
    listGetD_binary (encA := encBits) [] hwires (by fun_prop)
  have hnand := (computableInPolyTime_nandSerialized (.of_tidy hn) (.of_tidy hw)
    (.of_tidy hfirst) (.of_tidy hsecond)).tidy
  have hwidth : ComputableTidilyInPolyTime (fun a => ((n a + 1) * w a) ^ 2) input encUnary := by
    fun_prop
  have hcopy := bitsTake.comp (hfirst.prod hwidth)
  have hconst := native_constSerialized hn hw hcode.fst'.snd'
  have h : ComputableTidilyInPolyTime (fun a =>
      if (node a).code.1.1 then
        if (node a).code.1.2 then
          nandSerialized (n a) (w a) ((wires a).getD (node a).code.2.1 [])
            ((wires a).getD (node a).code.2.2 [])
        else ((wires a).getD (node a).code.2.1 []).take (((n a + 1) * w a) ^ 2)
      else constSerialized (n a) (w a) (node a).code.1.2) input encBits :=
    hcode.fst'.fst'.cond (hcode.fst'.snd'.cond hnand hcopy) hconst
  convert h using 1
  funext a
  cases node a <;> rfl

/-- Evaluate one node on arbitrary wires, including invalid binary references. -/
@[fun_prop]
theorem computableInPolyTime_evaluateNode {wires : α → List (List Bool)}
    {node : α → Layered.Node}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hwires : ComputableInPolyTime wires input (encList encBits))
    (hnode : ComputableInPolyTime node input Layered.encNode) :
    ComputableInPolyTime (fun a => evaluateNode (n a) (w a) (wires a) (node a))
      input encBits :=
  .of_tidy (native_evaluateNode hn.tidy hw.tidy hwires.tidy hnode.tidy)

private theorem native_evaluateLayer {wires : α → List (List Bool)}
    {layer : α → List Layered.Node}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hwires : ComputableTidilyInPolyTime wires input (encList encBits))
    (hlayer : ComputableTidilyInPolyTime layer input (encList Layered.encNode)) :
    ComputableTidilyInPolyTime (fun a => evaluateLayer (n a) (w a) (wires a) (layer a))
      input (encList encBits) := by
  unfold evaluateLayer
  exact mapWithInput hlayer (native_evaluateNode (by fun_prop) (by fun_prop) (by fun_prop)
    (snd input Layered.encNode))

/-- Evaluate every node of a computed layer, charging the complete output list. -/
@[fun_prop]
theorem computableInPolyTime_evaluateLayer {wires : α → List (List Bool)}
    {layer : α → List Layered.Node}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hwires : ComputableInPolyTime wires input (encList encBits))
    (hlayer : ComputableInPolyTime layer input (encList Layered.encNode)) :
    ComputableInPolyTime (fun a => evaluateLayer (n a) (w a) (wires a) (layer a))
      input (encList encBits) :=
  .of_tidy (native_evaluateLayer hn.tidy hw.tidy hwires.tidy hlayer.tidy)

/-- Every node output has at most the square ciphertext width, on arbitrary wires. -/
theorem length_evaluateNode_le (n w : ℕ) (wires : List (List Bool)) (node : Layered.Node) :
    (evaluateNode n w wires node).length ≤ ((n + 1) * w) ^ 2 := by
  cases node with
  | const μ => exact (length_constSerialized n w μ).le
  | copy i => exact List.length_take_le _ _
  | nand i j => exact (length_nandSerialized n w _ _).le

private theorem length_encList_evaluateLayer_le (n w : ℕ) (wires : List (List Bool))
    (layer : List Layered.Node) :
    (encList encBits (evaluateLayer n w wires layer)).length ≤
      layer.length * (2 * ((n + 1) * w) ^ 2 + 1) := by
  rw [length_encList]
  calc
    ((evaluateLayer n w wires layer).map fun c => 2 * (encBits c).length + 1).sum ≤
        ((evaluateLayer n w wires layer).map fun _ => 2 * ((n + 1) * w) ^ 2 + 1).sum := by
      apply List.sum_le_sum
      intro c hc
      obtain ⟨node, _, rfl⟩ := List.mem_map.mp hc
      have := length_evaluateNode_le n w wires node
      simp only [encBits_apply]
      omega
    _ = layer.length * (2 * ((n + 1) * w) ^ 2 + 1) := by
      simp [evaluateLayer, Function.comp_def, List.map_const', List.sum_replicate]

private theorem native_evaluateLayers {wires : α → List (List Bool)}
    {layers : α → List (List Layered.Node)}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hwires : ComputableTidilyInPolyTime wires input (encList encBits))
    (hlayers : ComputableTidilyInPolyTime layers input (encList (encList Layered.encNode))) :
    ComputableTidilyInPolyTime (fun a => evaluateLayers (n a) (w a) (wires a) (layers a))
      input (encList encBits) := by
  let growth (a : α) := (encList (encList Layered.encNode) (layers a)).length *
    (2 * ((n a + 1) * w a) ^ 2 + 1)
  have hencoded : ComputableTidilyInPolyTime
      (fun a => (encList (encList Layered.encNode) (layers a)).length) input encUnary :=
    (ComputableTidilyInPolyTime.length (encL := encBits) encBool).comp hlayers.encoded
  have hgrowth : ComputableTidilyInPolyTime growth input encUnary := by
    dsimp only [growth]
    fun_prop
  have hstep : ComputableTidilyInPolyTime
      (fun p : (α × List (List Bool)) × List Layered.Node =>
        evaluateLayer (n p.1.1) (w p.1.1) p.1.2 p.2)
      (encPair (encPair input (encList encBits)) (encList Layered.encNode))
      (encList encBits) :=
    native_evaluateLayer (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold evaluateLayers
  refine foldlWithInput_of_bounded_growth (step := fun a => evaluateLayer (n a) (w a)) hwires
    ⟨hlayers, hstep, inferInstance, inferInstance⟩ ⟨hgrowth.polyBounded, ?_⟩
  intro a state layer hlayer
  have hrow := length_encList_evaluateLayer_le (n a) (w a) state layer
  have hle : layer.length ≤ (encList (encList Layered.encNode) (layers a)).length :=
    (length_le_length_encList Layered.encNode _).trans
      (length_le_encList_of_mem (encList Layered.encNode) hlayer)
  have := Nat.mul_le_mul_right (2 * ((n a + 1) * w a) ^ 2 + 1) hle
  dsimp only [growth]
  omega

/-- Evaluate all layers in order, with a uniform polynomial clock on arbitrary inputs. -/
@[fun_prop]
theorem computableInPolyTime_evaluateLayers {wires : α → List (List Bool)}
    {layers : α → List (List Layered.Node)}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hwires : ComputableInPolyTime wires input (encList encBits))
    (hlayers : ComputableInPolyTime layers input (encList (encList Layered.encNode))) :
    ComputableInPolyTime (fun a => evaluateLayers (n a) (w a) (wires a) (layers a))
      input (encList encBits) :=
  .of_tidy (native_evaluateLayers hn.tidy hw.tidy hwires.tidy hlayers.tidy)

/-- Compile a circuit given by its unary arity and code, evaluate it on arbitrary ciphertext
words and select its first designated output, in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_evaluateCircuit {C : α → Σ k, Circuit signature k 1}
    {inputs : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encUnary)
    (hC : ComputableInPolyTime C input (encCircuit 1))
    (hinputs : ComputableInPolyTime inputs input (encList encBits)) :
    ComputableInPolyTime (fun a => evaluateCircuit (n a) (w a) (C a) (inputs a))
      input encBits := by
  have hview : ComputableTidilyInPolyTime
      (fun D : Σ k, Circuit signature k 1 => (D.1, D.2.code))
      (encCircuit 1) (encPair encUnary encCode) := .of_eq fun _ => rfl
  have hv := hview.comp hC.tidy
  have hcompiled := (Layered.computableInPolyTime_compile (.of_tidy hv.fst')
    (.of_tidy hv.snd')).tidy
  have hlayers := native_evaluateLayers hn.tidy hw.tidy hinputs.tidy hcompiled.fst'
  have hindex : ComputableTidilyInPolyTime
      (fun a => (Layered.compile (C a).1 (C a).2.code).2.headD 0) input encNat :=
    listHeadDWithInput 0 hcompiled.snd'
  exact .of_tidy (listGetD_binary (encA := encBits) [] hlayers hindex)

end Cslib.Crypto.Homomorphic.GSW
