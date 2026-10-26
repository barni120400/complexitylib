/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Powerset
import Complexity.Foundations.BooleanAnalysis.Bernoulli
import Complexity.Foundations.BooleanAnalysis.Influence
import Complexity.Foundations.Data.BitString.Weight

/-!
# Simultaneous deficits across a hypergraph cut

For a family of supports of size at most `d`, a uniformly random set meets each support with
probability at most `1 - 2⁻ᵈ`. If each coordinate occurs in at most `D` supports, changing one
coordinate changes the number of selected coordinates minus the number of supports met by at
most `D + 1`. The Boolean Poincaré inequality therefore controls the variance of this deficit.

If every cut has a side whose deficit is below `k`, symmetry between a cut and its complement
forces the mean deficit below `k + (D + 1) √(|ι| / 2)`.

## Main results

* `Cslib.HypergraphCut.card_le_of_deficit`: a finite support-sensitive bound from a deficit
  obstruction on every cut.

## References

The cut bound applies the Boolean Poincaré inequality
[O'Donnell, Section 2.3][ODonnell2014].
-/

@[expose] public section

namespace Cslib.HypergraphCut

open Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

private noncomputable def hits (s : Finset ι) (x : ι → Bool) : ℝ :=
  if ∃ i ∈ s, x i = true then 1 else 0

private noncomputable def deficit (S : κ → Finset ι) (x : ι → Bool) : ℝ :=
  (BitString.weight x : ℝ) - ∑ j, hits (S j) x

private theorem expect_hits (s : Finset ι) :
    (𝔼 x : ι → Bool, hits s x) = 1 - (1 / 2 : ℝ) ^ s.card := by
  classical
  have h := BitString.bernoulliAverage_hits (1 / 2 : ℝ) (fun i => decide (i ∈ s))
  rw [BitString.bernoulliAverage_one_half,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  simpa [BitString.weight, hits] using h

private theorem expect_deficit (S : κ → Finset ι) :
    (𝔼 x, deficit S x) = (Fintype.card ι : ℝ) / 2 -
      ∑ j, (1 - (1 / 2 : ℝ) ^ (S j).card) := by
  have hweight := BitString.bernoulliAverage_weight (ι := ι) (1 / 2 : ℝ)
  rw [BitString.bernoulliAverage_one_half] at hweight
  simp only [deficit, expect_sub_distrib, expect_sum_comm, expect_hits]
  rw [hweight]
  ring

omit [Fintype ι] in
private theorem abs_hits_update_sub_le (s : Finset ι) (i : ι) (x : ι → Bool) :
    |hits s (Function.update x i false) - hits s (Function.update x i true)| ≤
      if i ∈ s then (1 : ℝ) else 0 := by
  classical
  by_cases hi : i ∈ s
  · simp only [hi, ite_true, hits]
    split_ifs <;> norm_num
  · have hsame : (∃ j ∈ s, Function.update x i false j = true) ↔
        (∃ j ∈ s, Function.update x i true j = true) := by
      constructor <;> rintro ⟨j, hj, h⟩
      · have hji : j ≠ i := fun hji => hi (hji ▸ hj)
        exact ⟨j, hj, by simpa [Function.update_of_ne hji] using h⟩
      · have hji : j ≠ i := fun hji => hi (hji ▸ hj)
        exact ⟨j, hj, by simpa [Function.update_of_ne hji] using h⟩
    simp only [hi, ite_false, hits, hsame, sub_self, abs_zero, le_refl]

private theorem abs_deficit_update_sub_le (S : κ → Finset ι) {D : ℕ}
    (hD : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ D) (i : ι) (x : ι → Bool) :
    |deficit S (Function.update x i false) - deficit S (Function.update x i true)| ≤ D + 1 := by
  classical
  have hw : (BitString.weight (Function.update x i true) : ℝ) =
      BitString.weight (Function.update x i false) + 1 := by
    have h := BitString.weight_update_true (x := Function.update x i false)
      (i := i) (by simp)
    simp only [Function.update_idem] at h
    exact_mod_cast h
  have hsum : |∑ j, (hits (S j) (Function.update x i false) -
      hits (S j) (Function.update x i true))| ≤ D := by
    calc
      _ ≤ ∑ j, |hits (S j) (Function.update x i false) -
          hits (S j) (Function.update x i true)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, if i ∈ S j then (1 : ℝ) else 0 :=
        sum_le_sum fun j _ => abs_hits_update_sub_le (S j) i x
      _ = ((univ.filter fun j => i ∈ S j).card : ℝ) := by rw [sum_boole]
      _ ≤ D := by exact_mod_cast hD i
  have heq : deficit S (Function.update x i false) - deficit S (Function.update x i true) =
      -1 - ∑ j, (hits (S j) (Function.update x i false) -
        hits (S j) (Function.update x i true)) := by
    rw [deficit, deficit, sum_sub_distrib, hw]
    ring
  rw [heq]
  calc
    _ ≤ |-1| + |∑ j, (hits (S j) (Function.update x i false) -
        hits (S j) (Function.update x i true))| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-1 : ℝ) (-∑ j, (hits (S j) (Function.update x i false) -
          hits (S j) (Function.update x i true)))
    _ ≤ D + 1 := by norm_num only [abs_neg, abs_one]; linarith

private theorem variance_deficit_le (S : κ → Finset ι) {D : ℕ}
    (hD : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ D) :
    (𝔼 x, (deficit S x - 𝔼 y, deficit S y) ^ 2) ≤
      Fintype.card ι * (D + 1 : ℝ) ^ 2 / 4 := by
  refine (BitString.expect_sub_expect_sq_le_totalInfluence (deficit S)).trans ?_
  have hi (i : ι) : BitString.influence i (deficit S) ≤ (D + 1 : ℝ) ^ 2 / 4 := by
    unfold BitString.influence
    calc
      _ ≤ 𝔼 x : ι → Bool, (D + 1 : ℝ) ^ 2 / 4 := by
        refine expect_le_expect fun x _ => ?_
        have h := abs_deficit_update_sub_le S hD i x
        have hsq := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (D + 1 : ℝ)) |>.mpr h
        rw [sq_abs] at hsq
        unfold BitString.derivative
        nlinarith
      _ = _ := Fintype.expect_const _
  calc
    BitString.totalInfluence (deficit S) ≤ ∑ _i : ι, (D + 1 : ℝ) ^ 2 / 4 :=
      sum_le_sum fun i _ => hi i
    _ = _ := by simp; ring

private theorem mean_le_of_complement_obstruction (f : (ι → Bool) → ℝ) {k V : ℝ}
    (hV : (𝔼 x, (f x - 𝔼 y, f y) ^ 2) ≤ V)
    (h : ∀ x, f x < k ∨ f (fun i => !x i) < k) :
    (𝔼 x, f x) ≤ k + Real.sqrt (2 * V) := by
  let μ := 𝔼 x, f x
  by_cases hk : μ ≤ k
  · exact hk.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hk' : 0 ≤ μ - k := by linarith
  have heq : (𝔼 x : ι → Bool, (f (fun i => !x i) - μ) ^ 2) =
      𝔼 x, (f x - μ) ^ 2 := by
    let e : Equiv.Perm (ι → Bool) := Function.Involutive.toPerm
      (fun (x : ι → Bool) i => !x i) (fun x => by funext i; simp)
    exact Fintype.expect_equiv e _ _ fun _ => rfl
  have hpt (x : ι → Bool) : (μ - k) ^ 2 ≤ (f x - μ) ^ 2 +
      (f (fun i => !x i) - μ) ^ 2 := by
    rcases h x with hx | hx
    · have hh : 0 ≤ μ - f x := by linarith
      have hs := sq_le_sq₀ hk' hh |>.mpr (by linarith : μ - k ≤ μ - f x)
      nlinarith [sq_nonneg (f (fun i => !x i) - μ)]
    · have hh : 0 ≤ μ - f (fun i => !x i) := by linarith
      have hs := sq_le_sq₀ hk' hh |>.mpr
        (by linarith : μ - k ≤ μ - f (fun i => !x i))
      nlinarith [sq_nonneg (f x - μ)]
  have havg := expect_le_expect (s := univ) (fun x _ => hpt x)
  rw [Fintype.expect_const, expect_add_distrib, heq] at havg
  have hsq : (μ - k) ^ 2 ≤ 2 * V := by change _ ≤ V at hV; linarith
  have hroot := Real.le_sqrt_of_sq_le hsq
  change μ ≤ _
  linarith

/-- If every cut of a finite support family has a side whose number of coordinates exceeds the
number of supports it meets by less than `k`, then the family must be large. Supports have size
at most `d`, and every coordinate belongs to at most `D` supports. -/
theorem card_le_of_deficit (S : κ → Finset ι) {d D : ℕ} {k : ℝ}
    (hd : ∀ j, (S j).card ≤ d)
    (hD : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ D)
    (hcut : ∀ U : Finset ι,
      (U.card : ℝ) - (univ.filter fun j => ¬Disjoint (S j) U).card < k ∨
      (Uᶜ.card : ℝ) - (univ.filter fun j => ¬Disjoint (S j) Uᶜ).card < k) :
    (Fintype.card ι : ℝ) / 2 ≤
      (1 - (1 / 2 : ℝ) ^ d) * Fintype.card κ + k +
        (D + 1 : ℝ) * Real.sqrt (Fintype.card ι / 2) := by
  classical
  have hdef (x : ι → Bool) : deficit S x =
      ((univ.filter fun i => x i = true).card : ℝ) -
        (univ.filter fun j => ¬Disjoint (S j) (univ.filter fun i => x i = true)).card := by
    simp only [deficit, BitString.weight, hits]
    congr 1
    rw [← sum_boole]
    refine sum_congr rfl fun j _ => ?_
    congr 1
    simp [Finset.not_disjoint_iff]
  have hnot (x : ι → Bool) : (univ.filter fun i => (!x i) = true) =
      (univ.filter fun i => x i = true)ᶜ := by
    ext i
    cases x i <;> simp
  have hm := mean_le_of_complement_obstruction (deficit S) (variance_deficit_le S hD)
    (k := k) (fun x => by simpa only [hdef, hnot] using hcut (univ.filter fun i => x i = true))
  have hs : (∑ j, (1 - (1 / 2 : ℝ) ^ (S j).card)) ≤
      (1 - (1 / 2 : ℝ) ^ d) * Fintype.card κ := by
    calc
      _ ≤ ∑ _j : κ, (1 - (1 / 2 : ℝ) ^ d) :=
        sum_le_sum fun j _ => sub_le_sub_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hd j)) 1
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  have hroot : Real.sqrt (2 * ((Fintype.card ι : ℝ) * (D + 1 : ℝ) ^ 2 / 4)) =
      (D + 1 : ℝ) * Real.sqrt (Fintype.card ι / 2) := by
    rw [show 2 * ((Fintype.card ι : ℝ) * (D + 1 : ℝ) ^ 2 / 4) =
      (D + 1 : ℝ) ^ 2 * (Fintype.card ι / 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [expect_deficit, hroot] at hm
  linarith

end Cslib.HypergraphCut
