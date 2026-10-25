/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Restriction
public import Complexity.Computability.Languages.Slice
public import Complexity.Computability.MCSP.Partial
public import Complexity.Computability.MCSP.SuccinctNP
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Sum

/-!
# Formula and Zero-Error Hardness Magnification for Succinct and Partial MCSP

This module formalizes the De Morgan formula hardness magnification theorems of
Oliveira and Santhanam [OliveiraSanthanam2018, Lemma 16, Theorem 1(1), and Theorem 2 / Remark 1]
connecting `Cslib.SuccinctMCSP` and `Cslib.PartialMCSP` (`MCSP*`) to `Cslib.GapMCSP`:

1. **Word-level projections of `SuccinctMCSP.enc` (`succinctWord`)**:
   For any fixed arity `n`, sample domain `S : Finset (BitString n)`, and threshold `s`, the encoded
   instance `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s)`
   has fixed length `SuccinctMCSP.ofFunctionEncLength n S.card s = 4 * n + 3 + S.card * (8 * n + 10)
   + s`, and each bit of this word is computed from the truth table `T : BitString (2 ^ n)` by a
   De Morgan formula of leaf size at most `1` (either a constant formula or a single input leaf
   `Formula.input (BitString.equivFin n y)`). Substituting these leaf-size-`≤ 1` formulas into an
   optimal formula for the corresponding slice of `SuccinctMCSP.enc '' SuccinctMCSP` produces a
   formula on `2 ^ n` variables of no greater leaf size (`exists_formula_ofFunction_SuccinctMCSP`).

2. **Zero-error / deterministic multi-query formula magnification
   ([OliveiraSanthanam2018, Theorem 2 / Remark 1])**:
   Given any deterministic list `qs : List (Finset (BitString n) × ℕ)` of query sets and thresholds
   such that every `s₁ n`-yes truth table satisfies `p.2 ≥ s₁ n` and every `s₂ n`-no truth table
   fails at least one query in `qs`, taking the conjunction of the substituted slice formulas
   separates `GapMCSP.yesSet s₁` from `GapMCSP.noSet s₂` on `2 ^ n`-bit inputs with leaf size at
   most the sum of the slice formula sizes (`exists_formula_separating_gapMCSP_of_queryList`,
   `exists_mem_lt_formulaSize_succinctMCSP_of_queryList`).

3. **One-sided randomized amplification and OS18 Lemma 16 / Theorem 1(1) / Theorem 17**:
   If a finite probability space `Ω` of sample sets `S : Ω → Finset (BitString n)` rejects each
   `T ∈ GapMCSP.noSet s₂` (i.e. `Instance.ofFunction ((MCSP.truthTable n).symm T) (S ω) s ∉
   SuccinctMCSP`) on at least a `1 / k`-fraction (or `δ`-fraction for `δ > 0`) of seeds `ω : Ω`,
   then by Adleman's counting argument (`exists_seed_tuple_of_one_sided_error`, using the elementary
   inequality `2 ^ N * (k - 1) ^ (k * (N + 1)) < k ^ (k * (N + 1))`) there exist `k * (2 ^ n + 1)`
   fixed seeds whose conjunction separates `GapMCSP.yesSet s₁` from `GapMCSP.noSet s₂` on `2 ^ n`
   bits with leaf size at most `k * (2 ^ n + 1) * L`
   (`exists_formula_separating_gapMCSP_of_succinctMCSP`,
   `exists_lt_formulaSize_succinctMCSP_of_gapMCSP`,
   `exists_lt_formulaSize_succinctMCSP_of_yesSet`).
   Furthermore, for average-case `(1, 1 - 1 / k)-MCSP[s]` (`ApproxMCSP.noSet`), drawing
   `q = k n * (M + 2)` uniform samples rejects every no-instance with probability at least `1 / 2`
   whenever `(computableFunctions n (s n)).card ≤ 2 ^ M`
   (`card_le_two_mul_filter_notMem_succinctMCSP`), completing the two-stage magnification proof end
   to end (`exists_formula_separating_approxMCSP_of_succinctMCSP`,
   `exists_lt_formulaSize_succinctMCSP_of_approxMCSP`).

4. **Bridge to `PartialMCSP` (`MCSP*`)**:
   Restricting a truth table `T : BitString (2 ^ n)` to `S : Finset (BitString n)` produces a
   `PartialMCSP.Instance` (`PartialMCSP.Instance.restrictTable T S s`) whose `toSuccinct` image is
   definitionally `SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s`, transferring
   the magnification theorems directly to `PartialMCSP`
   (`exists_formula_separating_gapMCSP_of_partialMCSP`).

## Main definitions

* `Cslib.SuccinctMCSP.ofFunctionEncLength`: the exact length of
  `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction f S s)`.
* `Cslib.Circuits.Boolean.evalWord`, `Cslib.Circuits.Boolean.succinctWord`: word-level formula
  projections for `SuccinctMCSP.enc`.
* `Cslib.ApproxMCSP.noSet`: the no-instances of `(1, 1 - 1 / k)-MCSP[s]`.
* `Cslib.PartialMCSP.Instance.restrictTable`: the `PartialMCSP` instance obtained by keeping a
  subset `S` of entries of a truth table `T` and setting all other entries to `none` (`*`).

## Main results

* `Cslib.SuccinctMCSP.rawSamples_ofFunction`, `Cslib.SuccinctMCSP.length_enc_ofFunction`: canonical
  sample enumeration and encoded length of `Instance.ofFunction`.
* `Cslib.Circuits.Boolean.evalWord_succinctWord`,
  `Cslib.Circuits.Boolean.leafSize_le_one_of_mem_succinctWord`,
  `Cslib.Circuits.Boolean.exists_formula_ofFunction_SuccinctMCSP`: leaf-size-preserving substitution
  into a slice formula of `SuccinctMCSP`.
* `Cslib.Circuits.Boolean.exists_formula_all_ofFunction_SuccinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_queryList`,
  `Cslib.Circuits.Boolean.exists_mem_lt_formulaSize_succinctMCSP_of_queryList`: deterministic /
  zero-error multi-query formula magnification [OliveiraSanthanam2018, Theorem 2].
* `Cslib.Circuits.Boolean.two_pow_mul_pred_pow_lt`,
  `Cslib.Circuits.Boolean.exists_seed_tuple_of_one_sided_error`,
  `Cslib.Circuits.Boolean.exists_seed_tuple_of_one_sided_error_real`: finite-probability Adleman
  derandomization lemma.
* `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_succinctMCSP_real`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_gapMCSP`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_yesSet`: Oliveira–Santhanam
  Lemma 16 and Theorem 1(1).
* `Cslib.Circuits.Boolean.card_le_two_mul_filter_notMem_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_formula_separating_approxMCSP_of_succinctMCSP`,
  `Cslib.Circuits.Boolean.exists_lt_formulaSize_succinctMCSP_of_approxMCSP`: Stage 1 random
  sampling and end-to-end `(1, 1 - 1 / k)-MCSP` formula magnification
  [OliveiraSanthanam2018, Lemma 16 / Theorem 17].
* `Cslib.PartialMCSP.restrictTable_mem_iff`,
  `Cslib.Circuits.Boolean.exists_formula_separating_gapMCSP_of_partialMCSP`: `PartialMCSP` bridge.

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
* [I. C. Oliveira, J. Pich, R. Santhanam, *Hardness Magnification near State-Of-The-Art Lower
  Bounds*][OliveiraPichSanthanam2019]
-/

@[expose] public section

namespace Cslib

open Circuits Circuits.Boolean Turing.MultiTapeTM

namespace SuccinctMCSP

/-- The sample set of `Instance.ofFunction f S s` has the same cardinality as `S`. -/
@[simp] theorem card_samples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.ofFunction f S s).samples.card = S.card :=
  Finset.card_image_of_injective S fun _ _ h => (Prod.mk.inj h).1

private theorem filter_flatMap_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (l : List (BitString n)) :
    (l.flatMap fun y => [(y, false), (y, true)]).filter
        (· ∈ S.image fun x => (x, f x)) =
      (l.filter (· ∈ S)).map fun y => (y, f y) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append,
      List.filter_cons, List.filter_cons, List.filter_cons, ih]
    by_cases hy : y ∈ S <;> cases hfy : f y <;> simp [hy, hfy]

/-- For `Instance.ofFunction f S s`, the canonical sample enumeration `rawSamples` visits the
inputs of `S` in the order of `BitString.enum n`, paired with their values under `f`. -/
theorem rawSamples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    rawSamples (Instance.ofFunction f S s) =
      ((BitString.enum n).filter (· ∈ S)).map fun y => (List.ofFn y, f y) := by
  unfold rawSamples Instance.ofFunction enumSamples
  dsimp only
  rw [filter_flatMap_ofFunction, List.map_map]
  rfl

/-- The exact bit length of `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction f S s)` when
`S.card = q`: the framed unary arity `n`, the twice-framed list of `q` samples of length `n` + `1`,
and the unary threshold `s`. -/
def ofFunctionEncLength (n q s : ℕ) : ℕ :=
  4 * n + 3 + q * (8 * n + 10) + s

private theorem length_encList_rawSamples_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (encList (encPair encBits encBool)
      (rawSamples (Instance.ofFunction f S s))).length = S.card * (4 * n + 5) := by
  have hlen : ((BitString.enum n).filter (· ∈ S)).length = S.card := by
    have h := length_rawSamples (Instance.ofFunction f S s)
    rwa [rawSamples_ofFunction, List.length_map, card_samples_ofFunction] at h
  rw [rawSamples_ofFunction, length_encList, List.map_map]
  have hconst : ((fun a => 2 * (encPair encBits encBool a).length + 1) ∘
      fun y : BitString n => (List.ofFn y, f y)) = fun _ => 4 * n + 5 := by
    funext y
    simp only [Function.comp_apply, length_encPair, encBits_apply, List.length_ofFn,
      encBool_apply, List.length_singleton]
    omega
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, hlen]

/-- The encoded length of `Instance.ofFunction f S s` under `SuccinctMCSP.enc` depends only on the
arity `n`, the sample count `S.card`, and the threshold `s`. -/
@[simp] theorem length_enc_ofFunction {n : ℕ} (f : BooleanFunction n)
    (S : Finset (BitString n)) (s : ℕ) :
    (enc (Instance.ofFunction f S s)).length = ofFunctionEncLength n S.card s := by
  rw [enc_apply, toRaw_apply, length_encPair, length_encPair,
    length_encList_rawSamples_ofFunction]
  simp only [Instance.ofFunction, encUnary_apply, List.length_replicate, ofFunctionEncLength]
  ring

/-- Any subset of samples from a function of circuit complexity at most `s` forms a yes-instance of
`SuccinctMCSP` at threshold `s`. -/
theorem ofFunction_mem_of_complexity_le {n s : ℕ} {f : BooleanFunction n}
    (hf : complexity interpretation (single f) ≤ s) (S : Finset (BitString n)) :
    Instance.ofFunction f S s ∈ SuccinctMCSP :=
  ofFunction_mem_iff.mpr (complexityOn_le_complexity.trans hf)

/-- For `Instance.ofFunction f S s`, membership in `SuccinctMCSP` is equivalent to the existence of
some function `g ∈ computableFunctions n s` agreeing with `f` on `S`. -/
theorem ofFunction_mem_iff_exists_mem_computableFunctions {n s : ℕ} {f : BooleanFunction n}
    {S : Finset (BitString n)} :
    Instance.ofFunction f S s ∈ SuccinctMCSP ↔
      ∃ g ∈ computableFunctions n s, ∀ x ∈ S, g x = f x := by
  rw [mem_iff_exists_mem_computableFunctions]
  exact exists_congr fun g => and_congr_right fun _ =>
    ⟨fun h x hx => h (x, f x) (Finset.mem_image_of_mem _ hx), fun h p hp => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact h x hx⟩

end SuccinctMCSP

namespace Circuits.Formula

/-- The leaf size of `andList l` is at most the sum of the leaf sizes of the formulas in `l`. -/
theorem leafSize_andList_le {N : ℕ} (l : List (Formula signature N)) :
    (andList l).leafSize ≤ (l.map leafSize).sum := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · exact (leafSize_balanced (const true) hl).le

/-- The leaf size of `orList l` is at most the sum of the leaf sizes of the formulas in `l`. -/
theorem leafSize_orList_le {N : ℕ} (l : List (Formula signature N)) :
    (orList l).leafSize ≤ (l.map leafSize).sum := by
  rcases eq_or_ne l [] with rfl | hl
  · simp
  · exact (leafSize_balanced (const false) hl).le

end Circuits.Formula

namespace Circuits.Boolean

/-! ### Word-level projections by leaf-size-`≤ 1` De Morgan formulas -/

/-- Evaluate a list of De Morgan formulas on a bitstring `T` to produce a binary word. -/
def evalWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) : List Bool :=
  fs.map fun F => F.eval interpretation T

@[simp] theorem evalWord_nil {N : ℕ} (T : BitString N) :
    evalWord ([] : List (Formula signature N)) T = [] :=
  rfl

@[simp] theorem evalWord_cons {N : ℕ} (F : Formula signature N)
    (fs : List (Formula signature N)) (T : BitString N) :
    evalWord (F :: fs) T = F.eval interpretation T :: evalWord fs T :=
  rfl

@[simp] theorem evalWord_append {N : ℕ} (fs₁ fs₂ : List (Formula signature N)) (T : BitString N) :
    evalWord (fs₁ ++ fs₂) T = evalWord fs₁ T ++ evalWord fs₂ T := by
  simp only [evalWord, List.map_append]

@[simp] theorem length_evalWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) :
    (evalWord fs T).length = fs.length := by
  simp only [evalWord, List.length_map]

/-- A fixed binary word `w` lifted to a list of constant De Morgan formulas on `N` inputs. -/
def constWord (N : ℕ) (w : List Bool) : List (Formula signature N) :=
  w.map Formula.const

@[simp] theorem evalWord_constWord {N : ℕ} (w : List Bool) (T : BitString N) :
    evalWord (constWord N w) T = w := by
  simp only [evalWord, constWord, List.map_map, Function.comp_def, Formula.eval_const, List.map_id']

/-- Lift `Turing.MultiTapeTM.frame` to a list of De Morgan formulas: each formula `F` becomes
`[Formula.const true, F]`, terminated by `[Formula.const false]`. -/
def frameWord {N : ℕ} (fs : List (Formula signature N)) : List (Formula signature N) :=
  fs.flatMap (fun F => [Formula.const true, F]) ++ [Formula.const false]

@[simp] theorem evalWord_frameWord {N : ℕ} (fs : List (Formula signature N)) (T : BitString N) :
    evalWord (frameWord fs) T = frame (evalWord fs T) := by
  induction fs with
  | nil => rfl
  | cons F fs ih =>
    have hcons : frameWord (F :: fs) = Formula.const true :: F :: frameWord fs := rfl
    rw [hcons, evalWord_cons, evalWord_cons, Formula.eval_const, ih, evalWord_cons, frame_cons]

/-- Lift `Turing.MultiTapeTM.encPair` to two lists of De Morgan formulas. -/
def pairWord {N : ℕ} (fs₁ fs₂ : List (Formula signature N)) : List (Formula signature N) :=
  frameWord fs₁ ++ fs₂

@[simp] theorem evalWord_pairWord {N : ℕ} (fs₁ fs₂ : List (Formula signature N))
    (T : BitString N) :
    evalWord (pairWord fs₁ fs₂) T = frame (evalWord fs₁ T) ++ evalWord fs₂ T := by
  simp only [pairWord, evalWord_append, evalWord_frameWord]

/-- The formula word on `2 ^ n` variables encoding a single sample `(List.ofFn y, f y)` where
`f = (MCSP.truthTable n).symm T`: the input bits `List.ofFn y` are constants and the output bit
`f y = T (BitString.equivFin n y)` is a single input leaf. -/
def sampleWord (n : ℕ) (y : BitString n) : List (Formula signature (2 ^ n)) :=
  pairWord (constWord (2 ^ n) (List.ofFn y)) [Formula.input (BitString.equivFin n y)]

@[simp] theorem evalWord_sampleWord (n : ℕ) (y : BitString n) (T : BitString (2 ^ n)) :
    evalWord (sampleWord n y) T =
      encPair encBits encBool (List.ofFn y, ((MCSP.truthTable n).symm T) y) := by
  simp only [sampleWord, evalWord_pairWord, evalWord_constWord, evalWord_cons, evalWord_nil,
    Formula.eval_input, encPair_apply, encBits_apply, encBool_apply, MCSP.truthTable_symm_apply]

/-- The formula word on `2 ^ n` variables whose evaluation on a truth table `T` equals
`SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s)`. -/
def succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ) : List (Formula signature (2 ^ n)) :=
  pairWord
    (pairWord (constWord (2 ^ n) (encUnary n))
      (((BitString.enum n).filter (· ∈ S)).flatMap fun y => frameWord (sampleWord n y)))
    (constWord (2 ^ n) (encUnary s))

private theorem evalWord_flatMap_sampleWord (n : ℕ) (l : List (BitString n))
    (T : BitString (2 ^ n)) :
    evalWord (l.flatMap fun y => frameWord (sampleWord n y)) T =
      encList (encPair encBits encBool)
        (l.map fun y => (List.ofFn y, ((MCSP.truthTable n).symm T) y)) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.flatMap_cons, evalWord_append, evalWord_frameWord, evalWord_sampleWord, ih,
      List.map_cons, encList_cons]

/-- Evaluating `succinctWord n S s` on a truth table `T : BitString (2 ^ n)` produces the exact
encoding `SuccinctMCSP.enc (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s)`. -/
@[simp] theorem evalWord_succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ)
    (T : BitString (2 ^ n)) :
    evalWord (succinctWord n S s) T =
      SuccinctMCSP.enc
        (SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s) := by
  rw [SuccinctMCSP.enc_apply, SuccinctMCSP.toRaw_apply, SuccinctMCSP.rawSamples_ofFunction]
  simp only [succinctWord, evalWord_pairWord, evalWord_constWord, evalWord_flatMap_sampleWord,
    encPair_apply, SuccinctMCSP.Instance.ofFunction]

private theorem leafSize_le_one_of_mem_constWord {N : ℕ} {w : List Bool}
    {F : Formula signature N} (hF : F ∈ constWord N w) : F.leafSize ≤ 1 := by
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hF
  simp

private theorem leafSize_le_one_of_mem_frameWord {N : ℕ} {fs : List (Formula signature N)}
    (hfs : ∀ G ∈ fs, G.leafSize ≤ 1) {F : Formula signature N} (hF : F ∈ frameWord fs) :
    F.leafSize ≤ 1 := by
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨G, hG, hFG⟩ := List.mem_flatMap.mp hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hFG
    rcases hFG with rfl | rfl
    · simp
    · exact hfs F hG
  · simp only [List.mem_singleton] at hF
    subst hF
    simp

private theorem leafSize_le_one_of_mem_pairWord {N : ℕ} {fs₁ fs₂ : List (Formula signature N)}
    (h₁ : ∀ G ∈ fs₁, G.leafSize ≤ 1) (h₂ : ∀ G ∈ fs₂, G.leafSize ≤ 1)
    {F : Formula signature N} (hF : F ∈ pairWord fs₁ fs₂) : F.leafSize ≤ 1 := by
  rcases List.mem_append.mp hF with hF | hF
  · exact leafSize_le_one_of_mem_frameWord h₁ hF
  · exact h₂ F hF

private theorem leafSize_le_one_of_mem_sampleWord {n : ℕ} {y : BitString n}
    {F : Formula signature (2 ^ n)} (hF : F ∈ sampleWord n y) : F.leafSize ≤ 1 := by
  refine leafSize_le_one_of_mem_pairWord (fun _ h => leafSize_le_one_of_mem_constWord h)
    (fun G hG => ?_) hF
  simp only [List.mem_singleton] at hG
  subst hG
  simp

/-- Every formula in `succinctWord n S s` has leaf size at most `1` (it is either a constant or a
single input leaf). -/
theorem leafSize_le_one_of_mem_succinctWord {n : ℕ} {S : Finset (BitString n)} {s : ℕ}
    {F : Formula signature (2 ^ n)} (hF : F ∈ succinctWord n S s) : F.leafSize ≤ 1 := by
  refine leafSize_le_one_of_mem_pairWord
    (fun G hG => leafSize_le_one_of_mem_pairWord
      (fun _ h => leafSize_le_one_of_mem_constWord h)
      (fun H hH => ?_) hG)
    (fun _ h => leafSize_le_one_of_mem_constWord h) hF
  obtain ⟨y, -, hHy⟩ := List.mem_flatMap.mp hH
  exact leafSize_le_one_of_mem_frameWord (fun _ h => leafSize_le_one_of_mem_sampleWord h) hHy

/-- The length of `succinctWord n S s` is `SuccinctMCSP.ofFunctionEncLength n S.card s`. -/
@[simp] theorem length_succinctWord (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    (succinctWord n S s).length = SuccinctMCSP.ofFunctionEncLength n S.card s := by
  have h := congrArg List.length (evalWord_succinctWord n S s (fun _ => false))
  simpa only [length_evalWord, SuccinctMCSP.length_enc_ofFunction] using h

open Classical in
/-- **Leaf-size-preserving substitution into a language slice.** If every formula in
`fs : List (Formula signature N)` has leaf size at most `1`, then membership of `evalWord fs T` in
any language `L : Set (List Bool)` is computed by a De Morgan formula on `N` variables of leaf size
at most `formulaSize (Language.slice L fs.length)`. -/
theorem exists_formula_of_evalWord {N : ℕ} (fs : List (Formula signature N))
    (hfs : ∀ F ∈ fs, F.leafSize ≤ 1) (L : Set (List Bool)) :
    ∃ F : Formula signature N,
      (∀ T : BitString N, F.eval interpretation T = decide (evalWord fs T ∈ L)) ∧
      F.leafSize ≤ formulaSize (Language.slice L fs.length) := by
  obtain ⟨G, hG, hGleaf⟩ := exists_computes_leafSize_eq (Language.slice L fs.length)
  let sub : Fin fs.length → Formula signature N := fun i => fs[i.1]'i.2
  refine ⟨G.bind sub, fun T => ?_, ?_⟩
  · rw [Formula.eval_bind, hG]
    have heq : (List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T) =
        evalWord fs T := by
      calc (List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T)
          = (List.ofFn sub).map (fun F => F.eval interpretation T) :=
            (List.map_ofFn (f := sub) (g := fun F => F.eval interpretation T)).symm
        _ = fs.map (fun F => F.eval interpretation T) := by
            rw [show List.ofFn sub = fs from List.ofFn_getElem]
        _ = evalWord fs T := rfl
    change decide ((List.ofFn fun i : Fin fs.length => (sub i).eval interpretation T) ∈ L) = _
    rw [heq]
  · exact (G.leafSize_bind_le fun i => hfs (sub i) (List.getElem_mem i.2)).trans hGleaf.le

open Classical in
/-- **Single-query `SuccinctMCSP` formula projection.** For any `n`, `S : Finset (BitString n)`, and
`s`, there is a De Morgan formula `F` on `2 ^ n` variables that decides whether
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP` and has leaf
size at most the formula size of the `(ofFunctionEncLength n S.card s)`-bit slice of
`SuccinctMCSP.enc '' SuccinctMCSP`. -/
theorem exists_formula_ofFunction_SuccinctMCSP (n : ℕ) (S : Finset (BitString n)) (s : ℕ) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
          (SuccinctMCSP.ofFunctionEncLength n S.card s)) := by
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_of_evalWord (succinctWord n S s)
    (fun _ h => leafSize_le_one_of_mem_succinctWord h)
    (SuccinctMCSP.enc '' SuccinctMCSP)
  refine ⟨F, fun T => ?_, ?_⟩
  · rw [hFeval T, evalWord_succinctWord, SuccinctMCSP.enc.injective.mem_set_image]
  · rwa [length_succinctWord] at hFleaf

/-! ### Zero-error / deterministic multi-query formula magnification -/

open Classical in
/-- **Multi-query `SuccinctMCSP` conjunction formula.** Given any list
`qs : List (Finset (BitString n) × ℕ)` of sample sets and thresholds, there is a De Morgan formula
on `2 ^ n` variables that decides whether all queries `(S, s) ∈ qs` are in `SuccinctMCSP` and has
leaf size at most the sum of the corresponding slice formula sizes. -/
theorem exists_formula_all_ofFunction_SuccinctMCSP (n : ℕ)
    (qs : List (Finset (BitString n) × ℕ)) :
    ∃ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n),
        F.eval interpretation T =
          decide (∀ p ∈ qs, SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) p.1 p.2 ∈ SuccinctMCSP)) ∧
      F.leafSize ≤
        (qs.map fun p =>
          formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
            (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum := by
  induction qs with
  | nil =>
    refine ⟨Formula.const true, fun T => ?_, by simp⟩
    simp
  | cons q qs ih =>
    obtain ⟨F₁, hF₁eval, hF₁leaf⟩ := exists_formula_ofFunction_SuccinctMCSP n q.1 q.2
    obtain ⟨F₂, hF₂eval, hF₂leaf⟩ := ih
    refine ⟨F₁.and F₂, fun T => ?_, ?_⟩
    · rw [Formula.eval_and, hF₁eval T, hF₂eval T]
      simp
    · simp only [Formula.leafSize_and, List.map_cons, List.sum_cons]
      exact Nat.add_le_add hF₁leaf hF₂leaf

/-- **Zero-error / deterministic multi-query formula upper bound for `GapMCSP`
[OliveiraSanthanam2018, Theorem 2 / Remark 1].** If a deterministic list `qs` of `(S, s)` queries
has `s₁ n ≤ s` for every `(S, s) ∈ qs` and rejects every `T ∈ GapMCSP.noSet s₂` on at least one
query in `qs`, and each queried slice of `SuccinctMCSP` has formula size at most `L`, then
`GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`qs.length * L`. -/
theorem exists_formula_separating_gapMCSP_of_queryList {s₁ s₂ : ℕ → ℕ} {n L : ℕ}
    (qs : List (Finset (BitString n) × ℕ))
    (hs : ∀ p ∈ qs, s₁ n ≤ p.2)
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      ∃ p ∈ qs, SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) p.1 p.2 ∉ SuccinctMCSP)
    (hL : ∀ p ∈ qs,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ qs.length * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  classical
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_all_ofFunction_SuccinctMCSP n qs
  have hsum : (qs.map fun p =>
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum ≤ qs.length * L := by
    have hmap := List.sum_le_length_nsmul
      (qs.map fun p => formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))) L (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hL p hp)
    simpa only [List.length_map, smul_eq_mul] using hmap
  refine ⟨F, hFleaf.trans hsum, fun T hyes => ?_, fun T hnoT => ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    intro p hp
    have hcomp : complexity interpretation (single ((MCSP.truthTable n).symm T)) ≤ p.2 :=
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes).trans (hs p hp)
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le hcomp p.1
  · rw [hFeval T, decide_eq_false_iff_not, not_forall]
    obtain ⟨p, hp, hnot⟩ := hno T hnoT
    exact ⟨p, fun h => hnot (h hp)⟩

/-- **Contrapositive zero-error formula magnification [OliveiraSanthanam2018, Theorem 2].** If every
De Morgan formula separating `GapMCSP.yesSet s₁` and `GapMCSP.noSet s₂` on `2 ^ n`-bit inputs has
leaf size strictly greater than `qs.length * L`, then at least one query `p ∈ qs` maps to a slice of
`SuccinctMCSP` with formula size strictly greater than `L`. -/
theorem exists_mem_lt_formulaSize_succinctMCSP_of_queryList {s₁ s₂ : ℕ → ℕ} {n L : ℕ}
    (qs : List (Finset (BitString n) × ℕ))
    (hs : ∀ p ∈ qs, s₁ n ≤ p.2)
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      ∃ p ∈ qs, SuccinctMCSP.Instance.ofFunction
        ((MCSP.truthTable n).symm T) p.1 p.2 ∉ SuccinctMCSP)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) →
      qs.length * L < F.leafSize) :
    ∃ p ∈ qs,
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2)) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno'⟩ :=
    exists_formula_separating_gapMCSP_of_queryList qs hs hno hle
  exact (hged F hyes hno').not_ge hFleaf

/-- Querying the full domain `Finset.univ` shows that the `2 ^ n`-bit slice of `GapMCSP.yesSet s`
has formula size no larger than the `(ofFunctionEncLength n (2 ^ n) (s n))`-bit slice of
`SuccinctMCSP.enc '' SuccinctMCSP`. -/
theorem formulaSize_slice_yesSet_le (s : ℕ → ℕ) (n : ℕ) :
    formulaSize ((GapMCSP.yesSet s).slice (2 ^ n)) ≤
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (2 ^ n) (s n))) := by
  classical
  obtain ⟨F, hFeval, hFleaf⟩ :=
    exists_formula_ofFunction_SuccinctMCSP n (Finset.univ : Finset (BitString n)) (s n)
  have hcard : (Finset.univ : Finset (BitString n)).card = 2 ^ n := by
    simp [BitString]
  rw [hcard] at hFleaf
  refine (formulaSize_le fun T => ?_).trans hFleaf
  rw [Bool.eq_iff_iff, hFeval T, Language.slice_eq_true_iff, decide_eq_true_iff,
    SuccinctMCSP.ofFunction_univ_mem_iff, GapMCSP.ofFn_mem_yesSet_iff]
  simp [MCSP.mem_iff, MCSP.Instance.function]

/-! ### Finite-probability Adleman amplification and OS18 Lemma 16 / Theorem 1(1) -/

private theorem two_mul_pow_le_succ_pow (m : ℕ) :
    2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1) := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.cast_id]
  have h1 : m ^ (m + 1) * 1 ^ (m + 1 - (m + 1)) * (m + 1).choose (m + 1) = m ^ (m + 1) := by
    simp
  have h2 : m ^ m * 1 ^ (m + 1 - m) * (m + 1).choose m = m ^ (m + 1) + m ^ m := by
    have hsub : m + 1 - m = 1 := Nat.add_sub_cancel_left m 1
    rw [hsub, Nat.choose_succ_self_right, one_pow, mul_one, mul_add, mul_one, pow_succ]
  rw [h1, h2]
  omega

/-- **Elementary exponential inequality for Adleman amplification:** for every `k ≥ 1` and `N : ℕ`,
`2 ^ N * (k - 1) ^ (k * (N + 1)) < k ^ (k * (N + 1))`, corresponding to the real inequality
`2 ^ N * (1 - 1 / k) ^ (k * (N + 1)) < 1`. -/
theorem two_pow_mul_pred_pow_lt {N k : ℕ} (hk : 1 ≤ k) :
    2 ^ N * (k - 1) ^ (k * (N + 1)) < k ^ (k * (N + 1)) := by
  set m := k - 1
  have hm : m + 1 = k := Nat.sub_add_cancel hk
  have hbase : 2 * m ^ k ≤ k ^ k := by
    simpa only [hm] using two_mul_pow_le_succ_pow m
  have hpow : (2 * m ^ k) ^ (N + 1) ≤ (k ^ k) ^ (N + 1) :=
    Nat.pow_le_pow_left hbase (N + 1)
  rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
  rcases eq_or_ne m 0 with hm0 | hm0
  · have hkt : k * (N + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero N)
    rw [hm0, zero_pow hkt, mul_zero]
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  · have hmpos : 0 < m ^ (k * (N + 1)) := Nat.pos_of_ne_zero (pow_ne_zero _ hm0)
    have h2pos : 0 < 2 ^ N := by positivity
    have hlt : 2 ^ N * m ^ (k * (N + 1)) < 2 ^ (N + 1) * m ^ (k * (N + 1)) := by
      rw [pow_succ]
      nlinarith
    exact hlt.trans_le hpow

/-- **Finite-probability Adleman amplification lemma.** If `no ⊆ BitString N` is a set of negative
inputs and, for every `T ∈ no`, at least a `1 / k`-fraction of the seeds `ω : Ω` satisfy
`Good T ω` (`Fintype.card Ω ≤ k * (Finset.univ.filter (Good T)).card`), then there exists a tuple
`ωs : Fin (k * (N + 1)) → Ω` of `k * (N + 1)` seeds such that every `T ∈ no` is witnessed by at
least one `ωs j`. -/
theorem exists_seed_tuple_of_one_sided_error {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {N k : ℕ} (hk : 1 ≤ k) (no : Finset (BitString N))
    (Good : BitString N → Ω → Prop) [∀ T ω, Decidable (Good T ω)]
    (hgood : ∀ T ∈ no, Fintype.card Ω ≤ k * (Finset.univ.filter (Good T)).card) :
    ∃ ωs : Fin (k * (N + 1)) → Ω, ∀ T ∈ no, ∃ j : Fin (k * (N + 1)), Good T (ωs j) := by
  classical
  set t := k * (N + 1)
  let Bad (T : BitString N) : Finset Ω := Finset.univ.filter fun ω => ¬Good T ω
  let BadTuple (T : BitString N) : Finset (Fin t → Ω) :=
    Fintype.piFinset fun _ : Fin t => Bad T
  have hBad_le (T : BitString N) (hT : T ∈ no) :
      k * (Bad T).card ≤ (k - 1) * Fintype.card Ω := by
    have hpart : (Finset.univ.filter (Good T)).card + (Bad T).card = Fintype.card Ω := by
      simpa only [Bad, Finset.card_univ] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := Good T)
    have hg := hgood T hT
    have hk1 : k * Fintype.card Ω = (k - 1) * Fintype.card Ω + Fintype.card Ω := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, add_mul, one_mul]
    have hadd : k * (Finset.univ.filter (Good T)).card + k * (Bad T).card =
        k * Fintype.card Ω := by
      rw [← mul_add, hpart]
    omega
  have hBadTuple_le (T : BitString N) (hT : T ∈ no) :
      k ^ t * (BadTuple T).card ≤ (k - 1) ^ t * (Fintype.card Ω) ^ t := by
    have hcard : (BadTuple T).card = (Bad T).card ^ t := by
      simp [BadTuple, Fintype.card_piFinset]
    rw [hcard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (hBad_le T hT) t
  have hno_card : no.card ≤ 2 ^ N := by
    calc no.card ≤ (Finset.univ : Finset (BitString N)).card := Finset.card_le_univ no
      _ = 2 ^ N := by simp [BitString]
  have hΩpos : 0 < (Fintype.card Ω) ^ t := pow_pos Fintype.card_pos t
  have hlt : k ^ t * (no.biUnion BadTuple).card < k ^ t * (Fintype.card Ω) ^ t := by
    calc k ^ t * (no.biUnion BadTuple).card
        ≤ k ^ t * ∑ T ∈ no, (BadTuple T).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ T ∈ no, k ^ t * (BadTuple T).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _T ∈ no, (k - 1) ^ t * (Fintype.card Ω) ^ t :=
          Finset.sum_le_sum fun T hT => hBadTuple_le T hT
      _ = no.card * ((k - 1) ^ t * (Fintype.card Ω) ^ t) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = no.card * (k - 1) ^ t * (Fintype.card Ω) ^ t := by ring
      _ ≤ 2 ^ N * (k - 1) ^ t * (Fintype.card Ω) ^ t :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hno_card)
      _ < k ^ t * (Fintype.card Ω) ^ t :=
          Nat.mul_lt_mul_of_pos_right (two_pow_mul_pred_pow_lt hk) hΩpos
  have hcard_lt : (no.biUnion BadTuple).card < (Finset.univ : Finset (Fin t → Ω)).card := by
    have hlt' : (no.biUnion BadTuple).card < (Fintype.card Ω) ^ t :=
      lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
    simpa [Fintype.card_pi] using hlt'
  obtain ⟨ωs, -, hωs⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  refine ⟨ωs, fun T hT => ?_⟩
  have hnotBad : ωs ∉ BadTuple T := fun hmem => hωs (Finset.mem_biUnion.mpr ⟨T, hT, hmem⟩)
  simpa only [BadTuple, Fintype.mem_piFinset, Bad, Finset.mem_filter, Finset.mem_univ,
    true_and, not_forall, Classical.not_not] using hnotBad

/-- **Real-parameter Adleman amplification lemma.** If `0 < δ` and every `T ∈ no` satisfies
`δ * Fintype.card Ω ≤ (Finset.univ.filter (Good T)).card`, then `⌈1 / δ⌉₊ * (N + 1)` seeds suffice
to witness every `T ∈ no`. -/
theorem exists_seed_tuple_of_one_sided_error_real {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {N : ℕ} {δ : ℝ} (hδ : 0 < δ) (no : Finset (BitString N))
    (Good : BitString N → Ω → Prop) [∀ T ω, Decidable (Good T ω)]
    (hgood : ∀ T ∈ no, δ * (Fintype.card Ω : ℝ) ≤ ((Finset.univ.filter (Good T)).card : ℝ)) :
    ∃ ωs : Fin (⌈1 / δ⌉₊ * (N + 1)) → Ω,
      ∀ T ∈ no, ∃ j : Fin (⌈1 / δ⌉₊ * (N + 1)), Good T (ωs j) := by
  have hk : 1 ≤ ⌈1 / δ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  refine exists_seed_tuple_of_one_sided_error hk no Good fun T hT => ?_
  have hceil : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil (1 / δ)
  have h1 : (1 : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at hceil
  have h2 : (Fintype.card Ω : ℝ) ≤ (⌈1 / δ⌉₊ : ℝ) * ((Finset.univ.filter (Good T)).card : ℝ) := by
    calc (Fintype.card Ω : ℝ)
        = 1 * (Fintype.card Ω : ℝ) := (one_mul _).symm
      _ ≤ ((⌈1 / δ⌉₊ : ℝ) * δ) * (Fintype.card Ω : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ = (⌈1 / δ⌉₊ : ℝ) * (δ * (Fintype.card Ω : ℝ)) := by ring
      _ ≤ (⌈1 / δ⌉₊ : ℝ) * ((Finset.univ.filter (Good T)).card : ℝ) :=
          mul_le_mul_of_nonneg_left (hgood T hT) (Nat.cast_nonneg _)
  exact_mod_cast h2

open Classical in
/-- **Oliveira–Santhanam Lemma 16 / Theorem 1(1) (integer amplification parameter `k`).**
Suppose `s₁ n ≤ s`, `S : Ω → Finset (BitString n)` is a family of sample sets indexed by a finite
nonempty seed space `Ω` such that for every `T : BitString (2 ^ n)` with
`List.ofFn T ∈ GapMCSP.noSet s₂`, at least a `1 / k`-fraction of the seeds `ω : Ω` yield a
no-instance `SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP`,
and each queried slice of `SuccinctMCSP` has formula size at most `L`. Then `GapMCSP[s₁, s₂]` on
`2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`k * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_succinctMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card)
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ k * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ GapMCSP.noSet s₂
  obtain ⟨ωs, hωs⟩ := exists_seed_tuple_of_one_sided_error hk noFinset
    (fun T ω => SuccinctMCSP.Instance.ofFunction
      ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP)
    (fun T hT => hno T (Finset.mem_filter.mp hT).2)
  let qs : List (Finset (BitString n) × ℕ) := List.ofFn fun j => (S (ωs j), s)
  have hlen : qs.length = k * (2 ^ n + 1) := List.length_ofFn
  rw [← hlen]
  refine exists_formula_separating_gapMCSP_of_queryList qs
    (fun p hp => ?_) (fun T hnoT => ?_) (fun p hp => ?_)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hs
  · have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs T hmem
    exact ⟨(S (ωs j), s), List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hL (ωs j)

open Classical in
/-- **Oliveira–Santhanam Lemma 16 / Theorem 1(1) (real error parameter `δ > 0`).**
If `S : Ω → Finset (BitString n)` rejects each `T ∈ GapMCSP.noSet s₂` with probability at least
`δ > 0` over a uniform seed `ω ∈ Ω`, and every queried slice of `SuccinctMCSP` has formula size at
most `L`, then `GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf
size at most `⌈1 / δ⌉₊ * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_succinctMCSP_real
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s L : ℕ} {δ : ℝ} (hδ : 0 < δ) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      δ * (Fintype.card Ω : ℝ) ≤
        ((Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card : ℝ))
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ ⌈1 / δ⌉₊ * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ GapMCSP.noSet s₂
  obtain ⟨ωs, hωs⟩ := exists_seed_tuple_of_one_sided_error_real hδ noFinset
    (fun T ω => SuccinctMCSP.Instance.ofFunction
      ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP)
    (fun T hT => hno T (Finset.mem_filter.mp hT).2)
  let qs : List (Finset (BitString n) × ℕ) := List.ofFn fun j => (S (ωs j), s)
  have hlen : qs.length = ⌈1 / δ⌉₊ * (2 ^ n + 1) := List.length_ofFn
  rw [← hlen]
  refine exists_formula_separating_gapMCSP_of_queryList qs
    (fun p hp => ?_) (fun T hnoT => ?_) (fun p hp => ?_)
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hs
  · have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs T hmem
    exact ⟨(S (ωs j), s), List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hL (ωs j)

open Classical in
/-- **Contrapositive formula hardness magnification for `GapMCSP[s₁, s₂]`
[OliveiraSanthanam2018, Lemma 16 / Theorem 1(1)].** If every De Morgan formula separating
`GapMCSP.yesSet s₁` and `GapMCSP.noSet s₂` on `2 ^ n`-bit inputs has leaf size strictly greater
than `k * (2 ^ n + 1) * L`, then some seed `ω : Ω` produces a slice of `SuccinctMCSP` with formula
size strictly greater than `L`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_gapMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s ∉ SuccinctMCSP).card)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) →
      k * (2 ^ n + 1) * L < F.leafSize) :
    ∃ ω : Ω,
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno'⟩ :=
    exists_formula_separating_gapMCSP_of_succinctMCSP hk hs S hno hle
  exact (hged F hyes hno').not_ge hFleaf

open Classical in
/-- **Exact-decision formula hardness magnification for `MCSP` (`s₁ = s₂`)
[OliveiraSanthanam2018, Theorem 1(1)].** If the `2 ^ n`-bit slice of `GapMCSP.yesSet s` has formula
size strictly greater than `k * (2 ^ n + 1) * L`, and `S : Ω → Finset (BitString n)` rejects every
`T ∈ GapMCSP.noSet s` at threshold `s' ≥ s n` on at least a `1 / k`-fraction of `ω : Ω`, then some
seed `ω : Ω` produces a slice of `SuccinctMCSP` with formula size strictly greater than `L`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_yesSet {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s : ℕ → ℕ} {n s' k L : ℕ} (hk : 1 ≤ k) (hs : s n ≤ s')
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          SuccinctMCSP.Instance.ofFunction
            ((MCSP.truthTable n).symm T) (S ω) s' ∉ SuccinctMCSP).card)
    (hged : k * (2 ^ n + 1) * L < formulaSize ((GapMCSP.yesSet s).slice (2 ^ n))) :
    ∃ ω : Ω,
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s')) := by
  refine exists_lt_formulaSize_succinctMCSP_of_gapMCSP hk hs S hno fun F hyes hnoF => ?_
  have hFcomp : F.Computes interpretation ((GapMCSP.yesSet s).slice (2 ^ n)) := by
    intro T
    by_cases hT : List.ofFn T ∈ GapMCSP.yesSet s
    · rw [hyes T hT, eq_comm, Language.slice_eq_true_iff]
      exact hT
    · have hnoT : List.ofFn T ∈ GapMCSP.noSet s := by
        rw [GapMCSP.ofFn_mem_noSet_iff]
        rw [GapMCSP.ofFn_mem_yesSet_iff, not_le] at hT
        exact hT
      rw [hnoF T hnoT, eq_comm, Bool.eq_false_iff, Ne, Language.slice_eq_true_iff]
      exact hT
  exact hged.trans_le (formulaSize_le hFcomp)

end Circuits.Boolean

/-! ### Average-case `(1, 1 - 1 / k)-MCSP` and Stage 1 random-sampling projection -/

namespace ApproxMCSP

open MCSP Circuits.Boolean

/-- The no-instances of `(1, 1 - 1 / k)-MCSP[s]` [OliveiraSanthanam2018, Section 2.1 / Theorem 17]:
the truth tables of `n`-input Boolean functions `f` such that every function `g` of circuit
complexity at most `s n` agrees with `f` on at most a `(1 - 1 / k n)`-fraction of inputs
(`k n * (Finset.univ.filter fun x => g x = f x).card ≤ (k n - 1) * 2 ^ n`). -/
def noSet (s k : ℕ → ℕ) : Language Bool :=
  truthTableLanguage fun n =>
    {f | ∀ g ∈ computableFunctions n (s n),
      k n * (Finset.univ.filter fun x => g x = f x).card ≤ (k n - 1) * 2 ^ n}

/-- A `2 ^ n`-bit truth table `T` belongs to `ApproxMCSP.noSet s k` if and only if every
`g ∈ computableFunctions n (s n)` agrees with `(MCSP.truthTable n).symm T` on at most a
`(1 - 1 / k n)`-fraction of inputs. -/
@[simp] theorem ofFn_mem_noSet_iff {s k : ℕ → ℕ} {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ noSet s k ↔
      ∀ g ∈ computableFunctions n (s n),
        k n * (Finset.univ.filter fun x => g x = (truthTable n).symm T x).card ≤
          (k n - 1) * 2 ^ n :=
  ofFn_mem_truthTableLanguage

/-- When `1 ≤ k n`, every `(1, 1 - 1 / k)-MCSP[s]` no-instance on `2 ^ n` bits is also a worst-case
`GapMCSP.noSet s` no-instance. -/
theorem ofFn_mem_gapMCSP_noSet_of_mem_noSet {s k : ℕ → ℕ} {n : ℕ} (hk : 1 ≤ k n)
    {T : BitString (2 ^ n)} (hT : List.ofFn T ∈ noSet s k) :
    List.ofFn T ∈ GapMCSP.noSet s := by
  rw [GapMCSP.ofFn_mem_noSet_iff]
  by_contra! hle
  have hmem : (truthTable n).symm T ∈ computableFunctions n (s n) :=
    mem_computableFunctions_iff_complexity_le.mpr hle
  have hcard := ofFn_mem_noSet_iff.mp hT _ hmem
  have hall : (Finset.univ.filter fun x : BitString n =>
      (truthTable n).symm T x = (truthTable n).symm T x).card = 2 ^ n := by
    simp [BitString]
  rw [hall] at hcard
  have h2pos : 0 < 2 ^ n := by positivity
  have hk1 : k n * 2 ^ n = (k n - 1) * 2 ^ n + 2 ^ n := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, add_mul, one_mul]
  omega

end ApproxMCSP

namespace Circuits.Boolean

open Classical in
/-- **Oliveira–Santhanam Stage 1: random-sampling union bound over `computableFunctions n s`
[OliveiraSanthanam2018, Lemma 16 / Theorem 17].**
Suppose `1 ≤ k`, `(computableFunctions n s).card ≤ 2 ^ M`, and `q = k * (M + 2)`. If every function
`g ∈ computableFunctions n s` agrees with `f : BooleanFunction n` on at most a
`(1 - 1 / k)`-fraction of inputs
(`k * (Finset.univ.filter fun x => g x = f x).card ≤ (k - 1) * 2 ^ n`), then at least half of all
`q`-tuples `ω : Fin q → BitString n` yield a no-instance
`SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP`. -/
theorem card_le_two_mul_filter_notMem_succinctMCSP {n s k M : ℕ} (hk : 1 ≤ k)
    (hcard : (computableFunctions n s).card ≤ 2 ^ M)
    {f : BooleanFunction n}
    (hf : ∀ g ∈ computableFunctions n s,
      k * (Finset.univ.filter fun x => g x = f x).card ≤ (k - 1) * 2 ^ n) :
    Fintype.card (Fin (k * (M + 2)) → BitString n) ≤
      2 * (Finset.univ.filter fun ω : Fin (k * (M + 2)) → BitString n =>
        SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP).card := by
  classical
  set q := k * (M + 2)
  let Agree (g : BooleanFunction n) : Finset (BitString n) :=
    Finset.univ.filter fun x => g x = f x
  let BadFor (g : BooleanFunction n) : Finset (Fin q → BitString n) :=
    Fintype.piFinset fun _ : Fin q => Agree g
  let Bad : Finset (Fin q → BitString n) :=
    Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP
  let Good : Finset (Fin q → BitString n) :=
    Finset.univ.filter fun ω : Fin q → BitString n =>
      SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∉ SuccinctMCSP
  have hsub : Bad ⊆ (computableFunctions n s).biUnion BadFor := by
    intro ω hω
    have hmem : SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP :=
      (Finset.mem_filter.mp hω).2
    obtain ⟨g, hg, hag⟩ :=
      SuccinctMCSP.ofFunction_mem_iff_exists_mem_computableFunctions.mp hmem
    refine Finset.mem_biUnion.mpr ⟨g, hg, Fintype.mem_piFinset.mpr fun i => ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hag (ω i) (Finset.mem_image_of_mem ω (Finset.mem_univ i))⟩
  have hBadFor_le (g : BooleanFunction n) (hg : g ∈ computableFunctions n s) :
      k ^ q * (BadFor g).card ≤ (k - 1) ^ q * (2 ^ n) ^ q := by
    have hc : (BadFor g).card = (Agree g).card ^ q := by
      simp [BadFor, Fintype.card_piFinset]
    rw [hc, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (hf g hg) q
  have hBad_le : k ^ q * Bad.card ≤ 2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q := by
    calc k ^ q * Bad.card
        ≤ k ^ q * ((computableFunctions n s).biUnion BadFor).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ k ^ q * ∑ g ∈ computableFunctions n s, (BadFor g).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ g ∈ computableFunctions n s, k ^ q * (BadFor g).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _g ∈ computableFunctions n s, (k - 1) ^ q * (2 ^ n) ^ q :=
          Finset.sum_le_sum fun g hg => hBadFor_le g hg
      _ = (computableFunctions n s).card * ((k - 1) ^ q * (2 ^ n) ^ q) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (computableFunctions n s).card * (k - 1) ^ q * (2 ^ n) ^ q := by ring
      _ ≤ 2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard)
  have hΩpos : 0 < (2 ^ n) ^ q := by positivity
  have hlt : k ^ q * (2 * Bad.card) < k ^ q * (2 ^ n) ^ q := by
    calc k ^ q * (2 * Bad.card)
        = 2 * (k ^ q * Bad.card) := by ring
      _ ≤ 2 * (2 ^ M * (k - 1) ^ q * (2 ^ n) ^ q) := Nat.mul_le_mul_left 2 hBad_le
      _ = 2 ^ (M + 1) * (k - 1) ^ (k * ((M + 1) + 1)) * (2 ^ n) ^ q := by
          rw [pow_succ']
          ring
      _ < k ^ (k * ((M + 1) + 1)) * (2 ^ n) ^ q :=
          Nat.mul_lt_mul_of_pos_right (two_pow_mul_pred_pow_lt (N := M + 1) hk) hΩpos
      _ = k ^ q * (2 ^ n) ^ q := rfl
  have h2Bad : 2 * Bad.card < Fintype.card (Fin q → BitString n) := by
    have hlt' : 2 * Bad.card < (2 ^ n) ^ q := lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
    simpa [Fintype.card_pi, BitString] using hlt'
  have hpart : Bad.card + Good.card = Fintype.card (Fin q → BitString n) := by
    simpa only [Bad, Good, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun ω : Fin q → BitString n =>
          SuccinctMCSP.Instance.ofFunction f (Finset.univ.image ω) s ∈ SuccinctMCSP)
  change Fintype.card (Fin q → BitString n) ≤ 2 * Good.card
  omega

/-- **End-to-end Oliveira–Santhanam formula construction for `(1, 1 - 1 / k)-MCSP`
[OliveiraSanthanam2018, Lemma 16 / Theorem 17].**
Suppose `1 ≤ k n`, `s₁ n ≤ s₂ n`, `(computableFunctions n (s₂ n)).card ≤ 2 ^ M`, and every
`(ofFunctionEncLength n m (s₂ n))`-bit slice of `SuccinctMCSP.enc '' SuccinctMCSP` with
`m ≤ k n * (M + 2)` has De Morgan formula size at most `L`. Then there exists a De Morgan formula
`F` on `2 ^ n` variables of leaf size at most `2 * (2 ^ n + 1) * L` that separates
`GapMCSP.yesSet s₁` from `ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit truth tables. -/
theorem exists_formula_separating_approxMCSP_of_succinctMCSP
    {s₁ s₂ k : ℕ → ℕ} {n M L : ℕ} (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n)
    (hcard : (computableFunctions n (s₂ n)).card ≤ 2 ^ M)
    (hL : ∀ m ≤ k n * (M + 2),
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ 2 * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  classical
  set q := k n * (M + 2)
  let noFinset : Finset (BitString (2 ^ n)) :=
    Finset.univ.filter fun T => List.ofFn T ∈ ApproxMCSP.noSet s₂ k
  obtain ⟨ωs, hωs⟩ := exists_seed_tuple_of_one_sided_error
    (Ω := Fin q → BitString n) (by decide : 1 ≤ 2) noFinset
    (fun T ω => SuccinctMCSP.Instance.ofFunction
      ((MCSP.truthTable n).symm T) (Finset.univ.image ω) (s₂ n) ∉ SuccinctMCSP)
    (fun T hT => card_le_two_mul_filter_notMem_succinctMCSP hk hcard
      (ApproxMCSP.ofFn_mem_noSet_iff.mp (Finset.mem_filter.mp hT).2))
  let qs : List (Finset (BitString n) × ℕ) :=
    List.ofFn fun j => (Finset.univ.image (ωs j), s₂ n)
  obtain ⟨F, hFeval, hFleaf⟩ := exists_formula_all_ofFunction_SuccinctMCSP n qs
  have hsum : (qs.map fun p =>
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))).sum ≤ 2 * (2 ^ n + 1) * L := by
    have hmap := List.sum_le_length_nsmul
      (qs.map fun p => formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n p.1.card p.2))) L (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
      refine hL (Finset.univ.image (ωs j)).card ?_
      calc (Finset.univ.image (ωs j)).card
          ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _ = q := by simp)
    simpa only [qs, List.length_map, List.length_ofFn, smul_eq_mul] using hmap
  refine ⟨F, hFleaf.trans hsum, fun T hyes => ?_, fun T hnoT => ?_⟩
  · rw [hFeval T, decide_eq_true_eq]
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    have hcomp : complexity interpretation (single ((MCSP.truthTable n).symm T)) ≤ s₂ n :=
      (GapMCSP.ofFn_mem_yesSet_iff.mp hyes).trans hs
    exact SuccinctMCSP.ofFunction_mem_of_complexity_le hcomp _
  · rw [hFeval T, decide_eq_false_iff_not, not_forall]
    have hmem : T ∈ noFinset := Finset.mem_filter.mpr ⟨Finset.mem_univ T, hnoT⟩
    obtain ⟨j, hj⟩ := hωs T hmem
    exact ⟨(Finset.univ.image (ωs j), s₂ n), fun h => hj (h (List.mem_ofFn.mpr ⟨j, rfl⟩))⟩

/-- **Contrapositive end-to-end formula hardness magnification for `(1, 1 - 1 / k)-MCSP`
[OliveiraSanthanam2018, Lemma 16 / Theorem 17].**
If `1 ≤ k n`, `s₁ n ≤ s₂ n`, `(computableFunctions n (s₂ n)).card ≤ 2 ^ M`, and every De Morgan
formula separating `GapMCSP.yesSet s₁` and `ApproxMCSP.noSet s₂ k` on `2 ^ n`-bit truth tables has
leaf size strictly greater than `2 * (2 ^ n + 1) * L`, then there exists `m ≤ k n * (M + 2)` such
that the `(ofFunctionEncLength n m (s₂ n))`-bit slice of `SuccinctMCSP.enc '' SuccinctMCSP` has
De Morgan formula size strictly greater than `L`. -/
theorem exists_lt_formulaSize_succinctMCSP_of_approxMCSP
    {s₁ s₂ k : ℕ → ℕ} {n M L : ℕ} (hk : 1 ≤ k n) (hs : s₁ n ≤ s₂ n)
    (hcard : (computableFunctions n (s₂ n)).card ≤ 2 ^ M)
    (hged : ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      2 * (2 ^ n + 1) * L < F.leafSize) :
    ∃ m ≤ k n * (M + 2),
      L < formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n m (s₂ n))) := by
  by_contra! hle
  obtain ⟨F, hFleaf, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_succinctMCSP hk hs hcard hle
  exact (hged F hyes hno).not_ge hFleaf

end Circuits.Boolean

/-! ### Bridge to `PartialMCSP` (`MCSP*`) -/

namespace PartialMCSP

/-- Restrict a total truth table `T : BitString (2 ^ n)` to a subset `S : Finset (BitString n)` of
defined inputs at threshold `s`, setting all entries outside `S` to `none` (`*`). -/
def Instance.restrictTable {n : ℕ} (T : BitString (2 ^ n)) (S : Finset (BitString n)) (s : ℕ) :
    Instance where
  arity := n
  table i := if (BitString.equivFin n).symm i ∈ S then some (T i) else none
  threshold := s

@[simp] theorem Instance.arity_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).arity = n :=
  rfl

@[simp] theorem Instance.threshold_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).threshold = s :=
  rfl

@[simp] theorem Instance.partialFunction_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) (y : BitString n) :
    (Instance.restrictTable T S s).partialFunction y =
      if y ∈ S then some (T (BitString.equivFin n y)) else none := by
  change (if (BitString.equivFin n).symm (BitString.equivFin n y) ∈ S then
    some (T (BitString.equivFin n y)) else none) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem Instance.definedFinset_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).definedFinset = S := by
  change Finset.univ.filter
    (fun z : BitString n => ((Instance.restrictTable T S s).partialFunction z).isSome) = S
  ext y
  simp

/-- Viewing `Instance.restrictTable T S s` as a `SuccinctMCSP.Instance` via `Instance.toSuccinct`
yields `SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s`. -/
@[simp] theorem Instance.toSuccinct_restrictTable {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    (Instance.restrictTable T S s).toSuccinct =
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s := by
  unfold Instance.toSuccinct SuccinctMCSP.Instance.ofFunction
  simp only [Instance.arity_restrictTable, Instance.definedFinset_restrictTable,
    Instance.threshold_restrictTable]
  congr 1
  refine Finset.image_congr fun y hy => ?_
  have hyS : y ∈ S := Finset.mem_coe.mp hy
  simp [Instance.completion, hyS]

/-- The partial truth table `Instance.restrictTable T S s` is in `PartialMCSP` if and only if
`SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s` is in `SuccinctMCSP`. -/
@[simp] theorem restrictTable_mem_iff {n : ℕ} (T : BitString (2 ^ n))
    (S : Finset (BitString n)) (s : ℕ) :
    Instance.restrictTable T S s ∈ PartialMCSP ↔
      SuccinctMCSP.Instance.ofFunction ((MCSP.truthTable n).symm T) S s ∈ SuccinctMCSP := by
  rw [← toSuccinct_mem_iff, Instance.toSuccinct_restrictTable]

end PartialMCSP

namespace Circuits.Boolean

open Classical in
/-- **Oliveira–Santhanam Lemma 16 / Theorem 1(1) phrased via `PartialMCSP` (`MCSP*`).**
If `s₁ n ≤ s`, `S : Ω → Finset (BitString n)` rejects every `T : BitString (2 ^ n)` with
`List.ofFn T ∈ GapMCSP.noSet s₂` in the sense that
`PartialMCSP.Instance.restrictTable T (S ω) s ∉ PartialMCSP` on at least a `1 / k`-fraction of
`ω : Ω`, and every queried slice of `SuccinctMCSP` has formula size at most `L`, then
`GapMCSP[s₁, s₂]` on `2 ^ n`-bit inputs is separated by a De Morgan formula of leaf size at most
`k * (2 ^ n + 1) * L`. -/
theorem exists_formula_separating_gapMCSP_of_partialMCSP {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {s₁ s₂ : ℕ → ℕ} {n s k L : ℕ} (hk : 1 ≤ k) (hs : s₁ n ≤ s)
    (S : Ω → Finset (BitString n))
    (hno : ∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
      Fintype.card Ω ≤
        k * (Finset.univ.filter fun ω =>
          PartialMCSP.Instance.restrictTable T (S ω) s ∉ PartialMCSP).card)
    (hL : ∀ ω : Ω,
      formulaSize (Language.slice (SuccinctMCSP.enc '' SuccinctMCSP)
        (SuccinctMCSP.ofFunctionEncLength n (S ω).card s)) ≤ L) :
    ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ k * (2 ^ n + 1) * L ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.noSet s₂ →
        F.eval interpretation T = false) := by
  refine exists_formula_separating_gapMCSP_of_succinctMCSP hk hs S (fun T hT => ?_) hL
  simpa only [PartialMCSP.restrictTable_mem_iff] using hno T hT

end Circuits.Boolean

end Cslib
