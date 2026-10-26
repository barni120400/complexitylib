/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Cut
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.Combinatorics.HypergraphCut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Threshold lower bounds from bounded direct input support

The bounds in this module restrict the number of original input coordinates read by each
gate. Internal predecessor fan-in, circuit depth, and real coefficient magnitudes remain
unrestricted. High-incidence input coordinates can be fixed before applying a random cut.

If both Boolean fibers are `K`-rectangle-free with `K ≤ 2 ^ k`, a program with `q`
input-reading gates and at most `d` original inputs per gate satisfies, for every natural `T`,
`n ≤ (2 * (1 - 2⁻ᵈ) + d / (T + 1)) * q + 2 * k + (T + 1) * √(2 * n)`.
The support restriction concerns aggregated coefficients, so repeated wires and cancellation
are handled by the existing native circuit semantics.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.inputDegree`: the number of input-reading gates
  that have a nonzero effective coefficient on a given original input.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.sum_inputDegree`: incidence double counting.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_fixed_inputs_of_inputSupport_card_le`:
  fixing coordinates of degree above `T` costs at most `d * q / (T + 1)` coordinates.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_inputGates_of_bounded_incidence`:
  the finite lower bound after fixing an arbitrary set of high-incidence inputs.
* `Cslib.Circuits.Boolean.WeightedThreshold.le_inputGates_of_inputSupport_card_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_le_of_inputSupport_card_le`:
  the finite support bound for programs and circuits.

## References

The lower-bound refinement combines the existing fixed-coordinate rectangle
lemma from [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*]
[Schlesinger2026Algebraic] with a random partition of the direct input supports.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-- The number of gates reading an original input with nonzero effective coefficient. -/
noncomputable def inputDegree (p : Program signature n g) (i : Fin n) : ℕ :=
  open scoped Classical in
  (univ.filter fun gate : inputGates p => i ∈ inputSupport p gate.val).card

/-- Counting direct input incidences either by input or by gate gives the same total. -/
theorem sum_inputDegree (p : Program signature n g) :
    ∑ i, inputDegree p i = ∑ gate : inputGates p, (inputSupport p gate.val).card := by
  classical
  simp only [inputDegree, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro gate _
  rw [← card_filter]
  simp [inputSupport]

/-- Fixing high-incidence coordinates leaves degree at most `T`; their number times `T + 1`
is at most the total direct input incidence bound. -/
theorem exists_fixed_inputs_of_inputSupport_card_le (p : Program signature n g)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d) (T : ℕ) :
    ∃ F : Finset (Fin n), (∀ i, i ∉ F → inputDegree p i ≤ T) ∧
      (T + 1) * F.card ≤ d * (inputGates p).card := by
  classical
  let F := univ.filter fun i => T < inputDegree p i
  refine ⟨F, ?_, ?_⟩
  · intro i hi
    simpa [F] using hi
  · calc
      (T + 1) * F.card = ∑ _i ∈ F, (T + 1) := by simp [mul_comm]
      _ ≤ ∑ i ∈ F, inputDegree p i := sum_le_sum fun i hi =>
        (mem_filter.mp hi).2
      _ ≤ ∑ i, inputDegree p i := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
      _ = ∑ gate : inputGates p, (inputSupport p gate.val).card := sum_inputDegree p
      _ ≤ ∑ _gate : inputGates p, d := sum_le_sum fun gate _ => hd gate.val
      _ = d * (inputGates p).card := by simp [mul_comm]

private noncomputable def residualSupport (p : Program signature n g)
    (F : Finset (Fin n)) (gate : Fin g) : Finset ↥Fᶜ :=
  open scoped Classical in
  (inputSupport p gate).subtype (fun i => i ∈ Fᶜ)

private theorem mem_residualSupport (p : Program signature n g) (F : Finset (Fin n))
    (gate : Fin g) (i : ↥Fᶜ) :
    i ∈ residualSupport p F gate ↔ i.val ∈ inputSupport p gate := by
  classical
  simp [residualSupport]

private theorem card_residualSupport_le (p : Program signature n g) (F : Finset (Fin n))
    (gate : Fin g) :
    (residualSupport p F gate).card ≤ (inputSupport p gate).card := by
  classical
  rw [residualSupport, card_subtype]
  exact card_filter_le _ _

private theorem card_filter_inputGates (p : Program signature n g) (P : Fin g → Prop)
    [DecidablePred P] (hP : ∀ gate, P gate → gate ∈ inputGates p) :
    (univ.filter fun gate : inputGates p => P gate.val).card = (univ.filter P).card := by
  classical
  rw [← card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext gate
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hgate
    exact ⟨⟨gate, hP gate hgate⟩, hgate, rfl⟩

private theorem cut_deficit_lt_of_rectangleFree (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (U A B : Finset (Fin n)) (hA : A ⊆ U) (hB : B ⊆ Uᶜ) :
    U.card - A.card < (univ.filter fun j => ¬ inputSupport p j ∩ U ⊆ A).card + k ∨
      Uᶜ.card - B.card < (univ.filter fun j => ¬ inputSupport p j ∩ Uᶜ ⊆ B).card + k := by
  classical
  by_contra h
  push Not at h
  obtain ⟨P, Q, v, hv, hP, hQ⟩ := exists_rectangle_of_cut_with_fixed p U A B hA hB
  have hPK := le_card_of_pow_le hP h.1 hK
  have hQK := le_card_of_pow_le hQ h.2 hK
  have hmono : ∀ x ∈ P, ∀ y ∈ Q, f (glue U x y) = readout v := by
    intro x hx y hy
    rw [← hreadout, hv x hx y hy]
  rcases card_lt_or_card_lt_of_rectangleFree hf U P Q (readout v) hmono with h | h <;> omega

private theorem residual_deficit_lt (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) (hK : K ≤ 2 ^ k)
    (F : Finset (Fin n)) (U : Finset ↥Fᶜ) :
    (U.card : ℝ) - (univ.filter fun gate : inputGates p =>
      ¬ Disjoint (residualSupport p F gate.val) U).card < k ∨
      (Uᶜ.card : ℝ) - (univ.filter fun gate : inputGates p =>
        ¬ Disjoint (residualSupport p F gate.val) Uᶜ).card < k := by
  classical
  let V : Finset (Fin n) := U.image Subtype.val
  have hV : V.card = U.card := card_image_of_injective _ Subtype.val_injective
  have hFV : Disjoint F V := by
    rw [disjoint_left]
    intro i hiF hiV
    obtain ⟨j, _, rfl⟩ := mem_image.mp hiV
    exact (mem_compl.mp j.property) hiF
  have hFsub : F ⊆ Vᶜ := subset_compl_iff_disjoint_right.mpr hFV
  have hcards : V.card + F.card ≤ n := by
    rw [← card_union_of_disjoint hFV.symm]
    simpa using card_le_univ (V ∪ F)
  have hVc : Vᶜ.card - F.card = Uᶜ.card := by
    rw [card_compl, card_compl, Fintype.card_coe, card_compl, Fintype.card_fin]
    omega
  have hleft (gate : Fin g) :
      (inputSupport p gate ∩ V ⊆ ∅) ↔ Disjoint (residualSupport p F gate) U := by
    constructor
    · intro h
      rw [disjoint_left]
      intro i hi hiU
      simpa using h (mem_inter.mpr
        ⟨(mem_residualSupport p F gate i).mp hi, mem_image.mpr ⟨i, hiU, rfl⟩⟩)
    · intro h i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp (mem_inter.mp hi).2
      exact False.elim ((disjoint_left.mp h)
        ((mem_residualSupport p F gate j).mpr (mem_inter.mp hi).1) hj)
  have hright (gate : Fin g) :
      (inputSupport p gate ∩ Vᶜ ⊆ F) ↔ Disjoint (residualSupport p F gate) Uᶜ := by
    constructor
    · intro h
      rw [disjoint_left]
      intro i hi hiU
      have hiV : i.val ∈ Vᶜ := by
        rw [mem_compl]
        intro hiV
        obtain ⟨j, hj, hji⟩ := mem_image.mp hiV
        have : j = i := Subtype.ext hji
        exact (mem_compl.mp hiU) (this ▸ hj)
      exact (mem_compl.mp i.property)
        (h (mem_inter.mpr ⟨(mem_residualSupport p F gate i).mp hi, hiV⟩))
    · intro h i hi
      by_contra hiF
      let j : ↥Fᶜ := ⟨i, mem_compl.mpr hiF⟩
      have hjU : j ∈ Uᶜ := by
        rw [mem_compl]
        intro hj
        exact (mem_compl.mp (mem_inter.mp hi).2) (mem_image.mpr ⟨j, hj, rfl⟩)
      exact (disjoint_left.mp h)
        ((mem_residualSupport p F gate j).mpr (mem_inter.mp hi).1) hjU
  have hmem (gate : Fin g) (W : Finset ↥Fᶜ)
      (h : ¬ Disjoint (residualSupport p F gate) W) : gate ∈ inputGates p := by
    apply (mem_inputGates_iff_inputSupport_nonempty p gate).mpr
    by_contra hempty
    have hempty' : inputSupport p gate = ∅ := not_nonempty_iff_eq_empty.mp hempty
    apply h
    rw [disjoint_left]
    intro i hi _
    have hi' := (mem_residualSupport p F gate i).mp hi
    simp [hempty'] at hi'
  have hLc : (univ.filter fun j => ¬ inputSupport p j ∩ V ⊆ ∅).card =
      (univ.filter fun gate : inputGates p =>
        ¬ Disjoint (residualSupport p F gate.val) U).card := by
    simp_rw [hleft]
    exact (card_filter_inputGates p _ (fun gate => hmem gate U)).symm
  have hRc : (univ.filter fun j => ¬ inputSupport p j ∩ Vᶜ ⊆ F).card =
      (univ.filter fun gate : inputGates p =>
        ¬ Disjoint (residualSupport p F gate.val) Uᶜ).card := by
    simp_rw [hright]
    exact (card_filter_inputGates p _ (fun gate => hmem gate Uᶜ)).symm
  have h := cut_deficit_lt_of_rectangleFree p readout hreadout hf hK V ∅ F
    (empty_subset _) hFsub
  rw [card_empty, Nat.sub_zero, hV, hVc, hLc, hRc] at h
  rcases h with h | h
  · left
    have h' : (U.card : ℝ) <
        (univ.filter fun gate : inputGates p =>
          ¬ Disjoint (residualSupport p F gate.val) U).card + k :=
      by exact_mod_cast h
    linarith
  · right
    have h' : (Uᶜ.card : ℝ) <
        (univ.filter fun gate : inputGates p =>
          ¬ Disjoint (residualSupport p F gate.val) Uᶜ).card + k :=
      by exact_mod_cast h
    linarith

/-- After fixing `F`, bounded incidence gives a support-sensitive lower bound. Only effective
coefficients on original input coordinates are counted. -/
theorem le_inputGates_of_bounded_incidence (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d)
    (F : Finset (Fin n)) (D : ℕ)
    (hD : ∀ i, i ∉ F → inputDegree p i ≤ D) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ 2 * (1 - (1 / 2 : ℝ) ^ d) * (inputGates p).card + F.card +
      2 * k + (D + 1 : ℝ) * Real.sqrt (2 * n) := by
  classical
  have h := Cslib.HypergraphCut.card_le_of_deficit
    (fun gate : inputGates p => residualSupport p F gate.val)
    (fun gate => (card_residualSupport_le p F gate.val).trans (hd gate.val))
    (fun i => by
      simpa only [mem_residualSupport, inputDegree] using
        hD i.val (mem_compl.mp i.property))
    (residual_deficit_lt p readout hreadout hf hK F)
  have hcard : Fintype.card ↥Fᶜ + F.card = n := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using card_compl_add_card F
  have hcardR : (Fintype.card ↥Fᶜ : ℝ) + F.card = n := by exact_mod_cast hcard
  have hle : (Fintype.card ↥Fᶜ : ℝ) ≤ n := by
    linarith [show (0 : ℝ) ≤ F.card by positivity]
  have hroot : 2 * Real.sqrt (Fintype.card ↥Fᶜ / 2) ≤ Real.sqrt (2 * (n : ℝ)) := by
    have hleft := Real.sq_sqrt (show 0 ≤ (Fintype.card ↥Fᶜ : ℝ) / 2 by positivity)
    have hright := Real.sq_sqrt (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg ((Fintype.card ↥Fᶜ : ℝ) / 2),
      Real.sqrt_nonneg (2 * (n : ℝ))]
  have hmul := mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ D + 1 by positivity)
  rw [Fintype.card_coe (inputGates p)] at h
  nlinarith

/-- A weighted threshold program whose gates each read at most `d` original inputs satisfies
`n ≤ (2 (1 - 2⁻ᵈ) + d / (T + 1)) q + 2 k + (T + 1) √(2 n)` for every `T`, where `q` is
the number of input-reading gates and both output fibers are `K`-rectangle-free with `K ≤ 2^k`.
There is no restriction on internal predecessor fan-in or real coefficient magnitudes. -/
theorem le_inputGates_of_inputSupport_card_le (p : Program signature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport p gate).card ≤ d)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ (2 * (1 - (1 / 2 : ℝ) ^ d) + (d : ℝ) / (T + 1)) *
      (inputGates p).card + 2 * k + (T + 1 : ℝ) * Real.sqrt (2 * n) := by
  classical
  obtain ⟨F, hdegree, hF⟩ := exists_fixed_inputs_of_inputSupport_card_le p hd T
  have h := le_inputGates_of_bounded_incidence p readout hreadout hf hd F T hdegree hK
  have hFR : (F.card : ℝ) ≤ (d : ℝ) / (T + 1) * (inputGates p).card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < T + 1)]
    have h' : ((T + 1 : ℕ) : ℝ) * F.card ≤ (d : ℝ) * (inputGates p).card :=
      by exact_mod_cast hF
    push_cast at h'
    nlinarith
  nlinarith

/-- The support-sensitive bound for a native single-output threshold circuit whose output
selects a gate. -/
theorem circuit_le_of_inputSupport_card_le (c : Circuit signature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K k : ℕ}
    (hcomputes : ∀ x, c.eval interpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K)
    {d : ℕ} (hd : ∀ gate, (inputSupport c.program gate).card ≤ d)
    (T : ℕ) (hK : K ≤ 2 ^ k) :
    (n : ℝ) ≤ (2 * (1 - (1 / 2 : ℝ) ^ d) + (d : ℝ) / (T + 1)) *
      (inputGates c.program).card + 2 * k + (T + 1 : ℝ) * Real.sqrt (2 * n) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply le_inputGates_of_inputSupport_card_le c.program (fun z => z gate) ?_ hf hd T hK
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

end Cslib.Circuits.Boolean.WeightedThreshold
