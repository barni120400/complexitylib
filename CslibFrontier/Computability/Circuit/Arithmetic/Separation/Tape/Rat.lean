/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Rep
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-!
# Rational series of bounded dimension

Closure properties of `Tape.RatLe n f` (series realized by a linear representation of dimension at
most `n`) and the normal form with a single initial and single final state (`RatLe.normal`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Rat`.

## Main definitions

* `Tape.RatLe`: bounded-dimension rational series.
* `Tape.Series.letter`: indicator series of a single letter.

## Main results

* `Tape.RatLe.add`, `Tape.RatLe.mul`, `Tape.RatLe.kstar`, `Tape.RatLe.smul`, `Tape.RatLe.sum`.
* `Tape.RatLe.letter`: single-letter series has dimension at most `2`.
* `Tape.RatLe.normal`: normal form with one initial and one final state matching on non-empty words.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset Matrix

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- The series has a linear representation of dimension at most `n`. -/
@[expose] def RatLe (n : ℕ) (f : Series F Ω) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (r : Rep F Ω Q), Fintype.card Q ≤ n ∧ r.series = f

namespace RatLe

theorem mono {n m : ℕ} {f : Series F Ω} (h : RatLe n f) (hm : n ≤ m) : RatLe m f := by
  obtain ⟨Q, _, r, h1, h2⟩ := h
  exact ⟨Q, _, r, h1.trans hm, h2⟩

theorem zero : RatLe 0 (0 : Series F Ω) :=
  ⟨Empty, inferInstance, ⟨0, 0, 0⟩, by simp, by ext o; simp [Rep.series]⟩

theorem add {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (f + g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.add r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.add_series r₁ r₂ o

theorem mul {n m : ℕ} {f g : Series F Ω} (hf : RatLe n f) (hg : RatLe m g) :
    RatLe (n + m) (Series.mul f g) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  obtain ⟨Q₂, _, r₂, h2, rfl⟩ := hg
  refine ⟨Q₁ ⊕ Q₂, inferInstance, r₁.mul r₂, by simp; omega, ?_⟩
  ext o
  exact Rep.mul_series r₁ r₂ o

theorem kstar {n : ℕ} {f : Series F Ω} (hf : RatLe n f) : RatLe (n + 1) (Series.kstar f) := by
  obtain ⟨Q₁, _, r₁, h1, rfl⟩ := hf
  refine ⟨Unit ⊕ Q₁, inferInstance, r₁.star, by simp; omega, ?_⟩
  ext o
  exact Rep.star_series r₁ o

theorem smul {n : ℕ} {f : Series F Ω} (c : F) (hf : RatLe n f) : RatLe n (c • f) := by
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  refine ⟨Q, _, ⟨c • r.lam, r.mu, r.gam⟩, h1, ?_⟩
  ext o
  have htail : ∀ o, (⟨c • r.lam, r.mu, r.gam⟩ : Rep F Ω Q).tail o = r.tail o := by
    intro o
    induction o with
    | nil => rfl
    | cons a o ih => simp [Rep.tail, ih]
  simp [Rep.series, htail]

theorem one : RatLe 1 (Series.one : Series F Ω) := by
  refine ⟨Unit, inferInstance, ⟨1, 0, 1⟩, by simp, ?_⟩
  ext o
  cases o with
  | nil => simp [Rep.series, Rep.tail, Series.one]
  | cons a o => simp [Rep.series, Rep.tail, Series.one]

theorem sum {ι : Type*} (s : Finset ι) (n : ι → ℕ) (f : ι → Series F Ω)
    (h : ∀ i ∈ s, RatLe (n i) (f i)) :
    RatLe (∑ i ∈ s, n i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end RatLe

/-- The indicator series of a single letter `a`. -/
@[expose] def Series.letter [DecidableEq Ω] (a : Ω) : Series F Ω :=
  fun o => if o = [a] then 1 else 0

theorem RatLe.letter [DecidableEq Ω] (a : Ω) :
    RatLe 2 (Series.letter a : Series F Ω) := by
  refine ⟨Bool, inferInstance, ⟨fun q => if q then 0 else 1,
    fun b => Matrix.of fun q q' => if b = a ∧ q = false ∧ q' = true then 1 else 0,
    fun q => if q then 1 else 0⟩, by simp, ?_⟩
  ext o
  match o with
  | [] => simp [Rep.series, Rep.tail, Series.letter, dotProduct]
  | [b] =>
    by_cases h : b = a <;>
      simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec, h]
  | b :: c :: o =>
    simp [Rep.series, Rep.tail, Series.letter, dotProduct, Matrix.mulVec]

/-- Normal form: one initial and one final state, giving the same values at non-empty words. -/
theorem RatLe.normal {n : ℕ} {f : Series F Ω} (hf : RatLe n f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Ω → Matrix Q Q F) (i e : Q),
      Fintype.card Q ≤ n + 2 ∧ ∀ o : List Ω, o ≠ [] → (o.map mu).prod i e = f o := by
  classical
  obtain ⟨Q, _, r, h1, rfl⟩ := hf
  let mu : Ω → Matrix (Option (Option Q)) (Option (Option Q)) F :=
    fun a => Matrix.of fun q q' =>
      match q, q' with
      | none, none => 0
      | none, some none => r.lam ⬝ᵥ (r.mu a *ᵥ r.gam)
      | none, some (some q') => (r.lam ᵥ* r.mu a) q'
      | some none, _ => 0
      | some (some _), none => 0
      | some (some q), some none => (r.mu a *ᵥ r.gam) q
      | some (some q), some (some q') => r.mu a q q'
  have hsink : ∀ o : List Ω, o ≠ [] → (o.map mu).prod (some none) (some none) = 0 := by
    intro o ho
    obtain ⟨b, o', rfl⟩ := List.exists_cons_of_ne_nil ho
    rw [List.map_cons, List.prod_cons, Matrix.mul_apply]
    simp [mu]
  refine ⟨Option (Option Q), inferInstance, inferInstance, mu, none, some none,
    by simp; omega, ?_⟩
  have key : ∀ o : List Ω, ∀ q, o ≠ [] →
      (o.map mu).prod (some (some q)) (some none) = r.tail o q := by
    intro o
    induction o with
    | nil => simp
    | cons a o ih =>
      intro q _
      rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option,
        Fintype.sum_option]
      by_cases ho : o = []
      · subst ho
        simp [mu, Rep.tail]
      · simp only [mu, Matrix.of_apply, zero_mul, zero_add]
        rw [hsink o ho, mul_zero, zero_add, Rep.tail, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun q' _ => by rw [ih q' ho]
  intro o ho
  obtain ⟨a, o, rfl⟩ := List.exists_cons_of_ne_nil ho
  rw [List.map_cons, List.prod_cons, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_option]
  by_cases ho : o = []
  · subst ho
    simp [mu, Rep.series, Rep.tail]
  · rw [Finset.sum_congr rfl fun q' _ => by rw [key o q' ho]]
    simp only [mu, Matrix.of_apply, zero_mul, zero_add]
    rw [hsink o ho, mul_zero, zero_add, Rep.series, Rep.tail, Matrix.dotProduct_mulVec]
    rfl

end Cslib.Circuits.Arithmetic.Separation.Tape
