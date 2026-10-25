/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.PH.KarpLipton
public import Complexity.Computability.MCSP.Basic
public import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Computability.Circuit.Boolean.EvaluationTime
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Circuit.Boolean.Substitution
import Complexity.Computability.MCSP.NP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.BitString.List
import Mathlib.Data.Fintype.Order
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Hardness Magnification for MCSP via Circuit-Min-Merge

Slightly superlinear circuit lower bounds for `MCSP[s]` imply `NP ⊄ P/poly` and `P ≠ NP`
[McKay, Murray, and Williams, Lemma 3.1 and Theorem 1.4 (third bullet)][McKayMurrayWilliams2019].

Assuming `NP ⊆ P/poly`, the polynomial-hierarchy language `CIRCUIT-MIN-MERGE`
(`Cslib.MCSP.CircuitMinMergeLanguage`) has polynomial-size circuits: given two subcube circuit
certificates `w₀` and `w₁` for the half-subcubes `p ++ [false]` and `p ++ [true]` of `{0, 1} ^ n`,
it outputs the lexicographically first (`Cslib.BitString.wordLt`) size-`s` circuit certificate `w`
that agrees with `w₀` on `p ++ [false]` and with `w₁` on `p ++ [true]`, together with a validity
bit. Composing this merge circuit across the `2 ^ n` nodes of the full binary tree of subcubes of
`{0, 1} ^ n` produces a circuit of size `2 ^ n · poly(n, s(n))` deciding the `2 ^ n`-bit slice of
`MCSP[s]` (`Cslib.MCSP.exists_complexity_MCSPAt_le_of_NP_subset_PPoly`). Taking the contrapositive
magnifies `2 ^ n · poly(n, s(n))` circuit lower bounds for `MCSP[s]` to `NP ⊄ P/poly` and `P ≠ NP`.

## Main definitions

* `Cslib.MCSP.MCSPAt`: `MCSP[s]` as a language of truth tables (`GapMCSP.yesSet s`).
* `Cslib.MCSP.validCert`, `Cslib.MCSP.evalCert`: validity and evaluation of canonical circuit
  certificates of length `certLength n s`.
* `Cslib.MCSP.inSubcube`, `Cslib.MCSP.agreesOnPoint`, `Cslib.MCSP.AgreesWithChildren`: subcube
  prefix membership and child-agreement predicates.
* `Cslib.MCSP.IsMergedCert`, `Cslib.MCSP.IsMinMergedCert`: valid and lexicographically minimal
  merged certificates.
* `Cslib.MCSP.CircuitMinMergeLanguage`: the `CIRCUIT-MIN-MERGE` decision problem.

## Main results

* `Cslib.MCSP.circuitMinMergeLanguage_mem_PPolyOn`: under `NP ⊆ P/poly`,
  `CircuitMinMergeLanguage ∈ PPolyOn encMerge`.
* `Cslib.MCSP.exists_complexity_MCSPAt_le_of_NP_subset_PPoly`: **MMW19 Lemma 3.1**, under
  `NP ⊆ P/poly`, `MCSP[s]` has circuits of size `2 ^ n · c · (n + s n + 1) ^ c` on `2 ^ n`-bit
  truth tables.
* `Cslib.MCSP.exists_complexity_MCSPAt_pow_le_of_NP_subset_PPoly`: specialization to polynomial
  schedules `s(n) = n ^ k`.
* `Cslib.MCSP.not_NP_subset_PPoly_of_MCSPAt_hard`, `Cslib.MCSP.P_ne_NP_of_MCSPAt_hard`,
  `Cslib.MCSP.not_NP_subset_PPoly_of_MCSPAt_pow_hard`, `Cslib.MCSP.P_ne_NP_of_MCSPAt_pow_hard`:
  **MMW19 Theorem 1.4 (third bullet)**, circuit lower bounds for `MCSP[s]` imply `NP ⊄ P/poly`
  and `P ≠ NP`.

## References

* [D. McKay, C. D. Murray, R. R. Williams, *Weak Lower Bounds on Resource-Bounded Compression
  Imply Strong Separations of Complexity Classes*][McKayMurrayWilliams2019]
-/

@[expose] public section

namespace Cslib.MCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-! ### `MCSP[s]` as a truth-table language -/

/-- **`MCSP[s]`**, the Minimum Circuit Size Problem with threshold schedule `s : ℕ → ℕ`: the
language of truth tables (of length `2 ^ n` for some `n`) of `n`-variable Boolean functions with
circuit complexity at most `s n`, defined as `GapMCSP.yesSet s` [McKayMurrayWilliams2019]. -/
abbrev MCSPAt (s : ℕ → ℕ) : Language Bool := GapMCSP.yesSet s

/-- A `2 ^ n`-bit truth table `T` belongs to `MCSPAt s` iff its function has circuit complexity at
most `s n`. -/
theorem ofFn_mem_MCSPAt_iff {s : ℕ → ℕ} {n : ℕ} {T : BitString (2 ^ n)} :
    List.ofFn T ∈ MCSPAt s ↔
      complexity interpretation (single ((truthTable n).symm T)) ≤ s n :=
  GapMCSP.ofFn_mem_yesSet_iff

/-- The `2 ^ n`-bit slice of `MCSPAt s` evaluates to `true` on `T` iff the function of `T` has
circuit complexity at most `s n`. -/
theorem slice_MCSPAt_eq_true_iff {s : ℕ → ℕ} {n : ℕ} {T : BitString (2 ^ n)} :
    (MCSPAt s).slice (2 ^ n) T = true ↔
      complexity interpretation (single ((truthTable n).symm T)) ≤ s n := by
  rw [Language.slice_eq_true_iff, ofFn_mem_MCSPAt_iff]

/-! ### Lexicographic minimum on fixed-length bit lists -/

/-- Every nonempty property on bit lists of length `m` has a `BitString.wordLt`-least element. -/
private theorem exists_wordLt_min {m : ℕ} {P : List Bool → Prop}
    (h : ∃ w : List Bool, w.length = m ∧ P w) :
    ∃ w : List Bool, w.length = m ∧ P w ∧
      ∀ w' : List Bool, w'.length = m → P w' → BitString.wordLt w' w = false := by
  classical
  let S : Finset (Lex (BitString m)) :=
    Finset.univ.filter fun x => P (List.ofFn (ofLex x))
  obtain ⟨w₀, hw₀, hPw₀⟩ := h
  have hS : S.Nonempty := by
    refine ⟨toLex (BitString.ofList m w₀), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    simp only [ofLex_toLex, BitString.ofFn_ofList hw₀, hPw₀]
  let x_min := S.min' hS
  have hx_mem : x_min ∈ S := Finset.min'_mem S hS
  refine ⟨List.ofFn (ofLex x_min), List.length_ofFn, (Finset.mem_filter.1 hx_mem).2,
    fun w' hw' hPw' => ?_⟩
  have hy_mem : toLex (BitString.ofList m w') ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [ofLex_toLex, BitString.ofFn_ofList hw', hPw']
  have hle : x_min ≤ toLex (BitString.ofList m w') := Finset.min'_le S _ hy_mem
  rw [← BitString.ofFn_ofList hw', Bool.eq_false_iff, ne_eq, BitString.wordLt_ofFn_iff]
  exact not_lt_of_ge hle

/-- Antisymmetry of `BitString.wordLt` on bit lists of equal length `m`. -/
private theorem eq_of_wordLt_eq_false {m : ℕ} {w₁ w₂ : List Bool}
    (hw₁ : w₁.length = m) (hw₂ : w₂.length = m)
    (h₁₂ : BitString.wordLt w₁ w₂ = false) (h₂₁ : BitString.wordLt w₂ w₁ = false) :
    w₁ = w₂ := by
  rw [← BitString.ofFn_ofList hw₁, ← BitString.ofFn_ofList hw₂] at h₁₂ h₂₁ ⊢
  have h1 : ¬ (toLex (BitString.ofList m w₁) < toLex (BitString.ofList m w₂)) := by
    rw [← BitString.wordLt_ofFn_iff, h₁₂]
    decide
  have h2 : ¬ (toLex (BitString.ofList m w₂) < toLex (BitString.ofList m w₁)) := by
    rw [← BitString.wordLt_ofFn_iff, h₂₁]
    decide
  exact congrArg (List.ofFn ∘ ofLex) (le_antisymm (not_lt.1 h2) (not_lt.1 h1))

/-! ### Canonical circuit certificates -/

/-- Whether `w` is a canonical certificate of length `certLength n s` encoding a valid `n`-input
circuit of size at most `s`. -/
def validCert (n s : ℕ) (w : List Bool) : Bool :=
  decide (w.length = certLength n s) &&
    codeCheck n (readCertificate n s w).1 &&
    decide ((readCertificate n s w).2 < n + (readCertificate n s w).1.length)

/-- Evaluate the circuit certificate `w` (for `n` inputs and gate budget `s`) on input `x`. -/
def evalCert (n s : ℕ) (w x : List Bool) : Bool :=
  evalOutput x (readCertificate n s w).1 (readCertificate n s w).2

/-- A valid certificate for `(n, s)` has length `certLength n s`. -/
theorem length_of_validCert {n s : ℕ} {w : List Bool} (hw : validCert n s w = true) :
    w.length = certLength n s := by
  simp only [validCert, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1.1

/-- Soundness of `validCert`: a valid certificate decodes to a circuit of size at most `s` whose
evaluation agrees with `evalCert`. -/
theorem exists_circuit_of_validCert {n s : ℕ} {w : List Bool} (hw : validCert n s w = true) :
    ∃ C : Circuit signature n 1, C.size ≤ s ∧
      ∀ x : BitString n, C.eval interpretation x 0 = evalCert n s w (List.ofFn x) := by
  have hcheck : checkCertificate (fun y out => out == evalCert n s w y) n s w = true := by
    simp only [validCert, Bool.and_eq_true] at hw
    simp [checkCertificate, evalCert, hw.1.2, hw.2]
  obtain ⟨C, hcS, heval⟩ := exists_circuit_of_checkCertificate hcheck
  exact ⟨C, hcS, fun x => beq_iff_eq.1 (heval x)⟩

/-- Completeness of `validCert`: every circuit of size at most `s` on `n` inputs has a valid
certificate whose `evalCert` agrees with the circuit on all `n`-bit inputs. -/
theorem exists_validCert_of_circuit {n s : ℕ} (C : Circuit signature n 1) (hcS : C.size ≤ s) :
    ∃ w : List Bool, validCert n s w = true ∧
      ∀ x : BitString n, evalCert n s w (List.ofFn x) = C.eval interpretation x 0 := by
  obtain ⟨w, hlen, hcheck⟩ := exists_checkCertificate_append
    (accept := fun y out => out == C.eval interpretation (BitString.ofList n y) 0) hcS
    (fun y => by simp)
  have hw := hcheck []
  rw [List.append_nil] at hw
  simp only [checkCertificate, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hw
  refine ⟨w, ?_, fun x => ?_⟩
  · simp [validCert, hlen, hw.1.1, hw.1.2]
  · simpa [evalCert] using hw.2 (List.ofFn x) (BitString.mem_enumList.2 List.length_ofFn)

open ComputableTidilyInPolyTime in
/-- `validCert` is computable in polynomial time when `n` and `s` are given in unary. -/
@[fun_prop]
theorem computableInPolyTime_validCert {γ : Type} {encIn : γ ↪ List Bool}
    {n s : γ → ℕ} {w : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => validCert (n a) (s a) (w a)) encIn encBool := by
  refine .of_tidy ?_
  have hn_t := hn.tidy
  have hs_t := hs.tidy
  have hw_t := hw.tidy
  have hc := (computableInPolyTime_readCertificate hn hs hw).tidy
  have hcert : ComputableTidilyInPolyTime (fun a => certLength (n a) (s a)) encIn encUnary := by
    unfold certLength
    fun_prop
  have hlen : ComputableTidilyInPolyTime
      (fun a => decide ((w a).length = certLength (n a) (s a))) encIn encBool :=
    decide_eq' (length_bits.comp hw_t) hcert
  have hcode := (computableInPolyTime_codeCheck hn (.of_tidy hc.fst')).tidy
  have hbound : ComputableTidilyInPolyTime
      (fun a => decide ((readCertificate (n a) (s a) (w a)).2 <
        n a + (readCertificate (n a) (s a) (w a)).1.length))
      encIn encBool :=
    binary_lt' hc.snd' (unary_to_binary.comp (unary_add.comp
      (hn_t.prod ((length_list encGate).comp hc.fst'))))
  unfold validCert
  exact bool_and' (bool_and' hlen hcode) hbound

/-- `evalCert` is computable in polynomial time when `n` and `s` are given in unary. -/
@[fun_prop]
theorem computableInPolyTime_evalCert {γ : Type} {encIn : γ ↪ List Bool}
    {n s : γ → ℕ} {w x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime (fun a => evalCert (n a) (s a) (w a) (x a)) encIn encBool := by
  have hc := (computableInPolyTime_readCertificate hn hs hw).tidy
  exact computableInPolyTime_evalOutput hx (.of_tidy hc.fst') (.of_tidy hc.snd')

/-! ### Subcubes and child-agreement predicates -/

/-- Whether `p` is a prefix of `x`, i.e., `x.take p.length == p`. For `x` of length `n`, this tests
membership in the subcube of `{0, 1} ^ n` with fixed prefix `p`. -/
def inSubcube (p x : List Bool) : Bool :=
  x.take p.length == p

@[simp] theorem inSubcube_nil (x : List Bool) : inSubcube [] x = true := by
  simp [inSubcube]

theorem inSubcube_of_length_eq {p x : List Bool} (hp : p.length = x.length) :
    inSubcube p x = true ↔ x = p := by
  simp [inSubcube, hp]

theorem inSubcube_append_singleton {p x : List Bool} {b : Bool} (hp : p.length < x.length) :
    inSubcube (p ++ [b]) x = true ↔ inSubcube p x = true ∧ x.getD p.length false = b := by
  simp only [inSubcube, List.length_append, List.length_singleton, beq_iff_eq,
    List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some, List.getD_eq_getElem _ _ hp]
  have hlen : (x.take p.length).length = p.length := List.length_take_of_le hp.le
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h hlen
    exact ⟨h1, List.singleton_injective h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- Whether the candidate circuit `w` agrees at point `x` in the subcube `p` with the child
certificate `w₀` (if `x[p.length] = false`) or `w₁` (if `x[p.length] = true`). -/
def agreesOnPoint (n s : ℕ) (p w₀ w₁ w x : List Bool) : Bool :=
  !inSubcube p x ||
    (evalCert n s w x ==
      if x.getD p.length false then evalCert n s w₁ x else evalCert n s w₀ x)

open ComputableTidilyInPolyTime in
/-- `agreesOnPoint` is computable in polynomial time when `n` and `s` are given in unary. -/
theorem computableInPolyTime_agreesOnPoint {γ : Type} {encIn : γ ↪ List Bool}
    {n s : γ → ℕ} {p w₀ w₁ w x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hs : ComputableInPolyTime s encIn encUnary)
    (hp : ComputableInPolyTime p encIn encBits)
    (hw₀ : ComputableInPolyTime w₀ encIn encBits)
    (hw₁ : ComputableInPolyTime w₁ encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => agreesOnPoint (n a) (s a) (p a) (w₀ a) (w₁ a) (w a) (x a)) encIn encBool := by
  refine .of_tidy ?_
  have hp_t := hp.tidy
  have hx_t := hx.tidy
  have hin : ComputableTidilyInPolyTime (fun a => inSubcube (p a) (x a)) encIn encBool :=
    (bitsTakeWithInput hx_t (length_bits.comp hp_t)).beq hp_t
  have hbit : ComputableTidilyInPolyTime
      (fun a => (x a).getD (p a).length false) encIn encBool :=
    bitsGetDWithInput hx_t (length_bits.comp hp_t) false
  have hew := (computableInPolyTime_evalCert hn hs hw hx).tidy
  have hew₀ := (computableInPolyTime_evalCert hn hs hw₀ hx).tidy
  have hew₁ := (computableInPolyTime_evalCert hn hs hw₁ hx).tidy
  unfold agreesOnPoint
  exact bool_or.comp ((bool_not.comp hin).prod (hew.beq (hbit.cond hew₁ hew₀)))

/-- Whether the candidate circuit `w` agrees on the subcube `p` with the child certificates `w₀`
(on `p ++ [false]`) and `w₁` (on `p ++ [true]`) at every `n`-bit input. -/
def AgreesWithChildren (n s : ℕ) (p w₀ w₁ w : List Bool) : Prop :=
  ∀ x : List Bool, x.length = n → agreesOnPoint n s p w₀ w₁ w x = true

/-- `w` is a valid size-`s` circuit certificate on `n` inputs that agrees with `w₀` on
`p ++ [false]` and with `w₁` on `p ++ [true]`. -/
def IsMergedCert (n s : ℕ) (p w₀ w₁ w : List Bool) : Prop :=
  validCert n s w = true ∧ AgreesWithChildren n s p w₀ w₁ w

/-- `w` is the lexicographically smallest (`BitString.wordLt`) certificate satisfying
`IsMergedCert n s p w₀ w₁`. -/
def IsMinMergedCert (n s : ℕ) (p w₀ w₁ w : List Bool) : Prop :=
  IsMergedCert n s p w₀ w₁ w ∧
    ∀ w' : List Bool, w'.length = certLength n s →
      IsMergedCert n s p w₀ w₁ w' → BitString.wordLt w' w = false

/-! ### `CIRCUIT-MIN-MERGE` and nonuniform quantifier elimination -/

/-- The width `certLength n s + 1` of a child state vector `(ok, w)`, consisting of one validity
bit followed by a certificate of length `certLength n s`. -/
def stateWidth (n s : ℕ) : ℕ := certLength n s + 1

/-- The fixed parameters `((n, s), (p, j))` of a query to `CircuitMinMergeLanguage`: arity `n` and
size bound `s` in unary, subcube prefix `p`, and output bit index `j` in unary. -/
abbrev MergeHeader : Type := (ℕ × ℕ) × (List Bool × ℕ)

/-- Encoding of `MergeHeader` with `n, s, j` in unary and `p` as raw bits. -/
def encHeader : MergeHeader ↪ List Bool :=
  encPair (encPair encUnary encUnary) (encPair encBits encUnary)

/-- An input `(((n, s), (p, j)), v)` to `CircuitMinMergeLanguage`, where `v` concatenates the two
child state vectors `(ok₀, w₀)` and `(ok₁, w₁)` of width `stateWidth n s`. -/
abbrev MergeInput : Type := MergeHeader × List Bool

/-- Encoding of `MergeInput` as `encPair encHeader encBits`, so `encMerge (hdr, v) =
frame (encHeader hdr) ++ v`. -/
def encMerge : MergeInput ↪ List Bool :=
  encPair encHeader encBits

/-- Extract the left child validity bit `ok₀` from a `MergeInput`. -/
def mergeOk₀ (a : MergeInput) : Bool := a.2.getD 0 false

/-- Extract the left child certificate `w₀` of length `certLength n s` from a `MergeInput`. -/
def mergeCert₀ (a : MergeInput) : List Bool :=
  (a.2.drop 1).take (certLength a.1.1.1 a.1.1.2)

/-- Extract the right child validity bit `ok₁` from a `MergeInput`. -/
def mergeOk₁ (a : MergeInput) : Bool :=
  a.2.getD (stateWidth a.1.1.1 a.1.1.2) false

/-- Extract the right child certificate `w₁` of length `certLength n s` from a `MergeInput`. -/
def mergeCert₁ (a : MergeInput) : List Bool :=
  (a.2.drop (stateWidth a.1.1.1 a.1.1.2 + 1)).take (certLength a.1.1.1 a.1.1.2)

/-- **The `CIRCUIT-MIN-MERGE` language** [McKayMurrayWilliams2019, Proof of Lemma 3.1]: given
parameters `((n, s), (p, j))` and concatenated child states `v` representing `(ok₀, w₀)` and
`(ok₁, w₁)`, accepts when `ok₀ = true`, `ok₁ = true`, and there is a lexicographically minimum
merged certificate `w` (`IsMinMergedCert n s p w₀ w₁ w`) whose `j`-th output bit (`true` at `j = 0`,
and bit `j - 1` of `w` at `j > 0`) is `true`. -/
def CircuitMinMergeLanguage : Set MergeInput :=
  {a | mergeOk₀ a = true ∧ mergeOk₁ a = true ∧
    ∃ w : List Bool, IsMinMergedCert a.1.1.1 a.1.1.2 a.1.2.1 (mergeCert₀ a) (mergeCert₁ a) w ∧
      (a.1.2.2 == 0 || w.getD (a.1.2.2 - 1) false) = true}

private theorem PPolyOn_of_computableInPolyTime {α : Type} {enc : α ↪ List Bool}
    {f : α → Bool} (hf : ComputableInPolyTime f enc encBool) :
    {a : α | f a = true} ∈ PPolyOn enc :=
  P_subset_PPolyOn ⟨f, hf, fun _ => Iff.rfl⟩

private theorem PPolyOn_inter {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hA : A ∈ PPolyOn enc) (hB : B ∈ PPolyOn enc) : (A ∩ B : Set α) ∈ PPolyOn enc := by
  obtain ⟨LA, hLA, hA⟩ := hA
  obtain ⟨LB, hLB, hB⟩ := hB
  exact ⟨LA ⊓ LB, PPoly.inf hLA hLB, fun a => by rw [Set.mem_inter_iff, hA a, hB a]; rfl⟩

private theorem PPolyOn_union {α : Type} {enc : α ↪ List Bool} {A B : Set α}
    (hA : A ∈ PPolyOn enc) (hB : B ∈ PPolyOn enc) : (A ∪ B : Set α) ∈ PPolyOn enc := by
  obtain ⟨LA, hLA, hA⟩ := hA
  obtain ⟨LB, hLB, hB⟩ := hB
  exact ⟨LA ⊔ LB, PPoly.sup hLA hLB, fun a => by rw [Set.mem_union, hA a, hB a]; rfl⟩

private theorem PPolyOn_imp {α : Type} {enc : α ↪ List Bool} {P Q : α → Prop}
    (hP : {a | P a} ∈ PPolyOn enc) (hQ : {a | Q a} ∈ PPolyOn enc) :
    {a | P a → Q a} ∈ PPolyOn enc := by
  have h : {a | P a → Q a} = {a | P a}ᶜ ∪ {a | Q a} := by
    ext a
    simp [imp_iff_not_or]
  rw [h]
  exact PPolyOn_union (PPolyOn.compl hP) hQ

private theorem PPolyOn_exists_of_computableInPolyTime_length {α : Type} {enc : α ↪ List Bool}
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∃ u : List Bool, u.length = N a ∧ P a u} ∈ PPolyOn enc := by
  let B : Set (α × List Bool) := {p | P p.1 (p.2.take (N p.1))}
  have hred : PolyTimeReducible (encPair enc encBits) (encPair enc encBits)
      B {p : α × List Bool | P p.1 p.2} := by
    refine ⟨fun p => (p.1, p.2.take (N p.1)), ?_, fun _ => Iff.rfl⟩
    exact .of_tidy ((ComputableTidilyInPolyTime.fst enc encBits).prod
      (ComputableTidilyInPolyTime.bitsTakeWithInput
        (ComputableTidilyInPolyTime.snd enc encBits)
        (hN.tidy.comp (ComputableTidilyInPolyTime.fst enc encBits))))
  obtain ⟨M, hM, hBM⟩ := hred.mem_PPolyOn hP
  obtain ⟨p, hp⟩ := hN.tidy.polyBounded.exists_polynomial
  refine ⟨{x : List Bool | ∃ w : List Bool, w.length = p.eval x.length ∧ frame x ++ w ∈ M},
    mem_PPoly_of_exists_frame_append hNP hM p, fun a => ?_⟩
  have hle : N a ≤ p.eval (enc a).length := hp a
  constructor
  · rintro ⟨u, hu, hPu⟩
    refine ⟨u ++ List.replicate (p.eval (enc a).length - N a) false,
      by rw [List.length_append, List.length_replicate, hu, Nat.add_sub_cancel' hle], ?_⟩
    have htake : (u ++ List.replicate (p.eval (enc a).length - N a) false).take (N a) = u := by
      rw [← hu, List.take_left]
    have hmem : (a, u ++ List.replicate (p.eval (enc a).length - N a) false) ∈ B := by
      change P a ((u ++ List.replicate (p.eval (enc a).length - N a) false).take (N a))
      rwa [htake]
    simpa [encPair_apply, encBits_apply] using (hBM _).1 hmem
  · rintro ⟨w, hw, hwM⟩
    have hmem : (a, w) ∈ B :=
      (hBM (a, w)).2 (by simpa [encPair_apply, encBits_apply] using hwM)
    refine ⟨w.take (N a), ?_, hmem⟩
    rw [List.length_take, hw, Nat.min_eq_left hle]

private theorem PPolyOn_forall_of_computableInPolyTime_length {α : Type} {enc : α ↪ List Bool}
    (hNP : NP encBits ⊆ PPolyOn encBits) {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {P : α → List Bool → Prop}
    (hP : {p : α × List Bool | P p.1 p.2} ∈ PPolyOn (encPair enc encBits)) :
    {a : α | ∀ u : List Bool, u.length = N a → P a u} ∈ PPolyOn enc := by
  have hex : {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u} ∈ PPolyOn enc :=
    PPolyOn_exists_of_computableInPolyTime_length hNP hN (PPolyOn.compl hP)
  have h_eq : {a : α | ∀ u : List Bool, u.length = N a → P a u} =
      {a : α | ∃ u : List Bool, u.length = N a ∧ ¬ P a u}ᶜ := by
    ext a
    simp
  rw [h_eq]
  exact PPolyOn.compl hex

open ComputableTidilyInPolyTime in
private theorem computableInPolyTime_mergeCert₀ :
    ComputableInPolyTime mergeCert₀ encMerge encBits := by
  refine .of_tidy ?_
  have hn : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.1) encMerge encUnary :=
    (fst encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hs : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.2) encMerge encUnary :=
    (snd encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hcert : ComputableTidilyInPolyTime
      (fun a : MergeInput => certLength a.1.1.1 a.1.1.2) encMerge encUnary := by
    unfold certLength
    fun_prop
  unfold mergeCert₀
  exact bitsTakeWithInput (bitsDropWithInput (snd encHeader encBits) (const 1)) hcert

open ComputableTidilyInPolyTime in
private theorem computableInPolyTime_mergeCert₁ :
    ComputableInPolyTime mergeCert₁ encMerge encBits := by
  refine .of_tidy ?_
  have hn : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.1) encMerge encUnary :=
    (fst encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hs : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.2) encMerge encUnary :=
    (snd encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hcert : ComputableTidilyInPolyTime
      (fun a : MergeInput => certLength a.1.1.1 a.1.1.2) encMerge encUnary := by
    unfold certLength
    fun_prop
  have hdrop : ComputableTidilyInPolyTime
      (fun a : MergeInput => stateWidth a.1.1.1 a.1.1.2 + 1) encMerge encUnary := by
    unfold stateWidth
    fun_prop
  unfold mergeCert₁
  exact bitsTakeWithInput (bitsDropWithInput (snd encHeader encBits) hdrop) hcert

open ComputableTidilyInPolyTime in
private theorem isMergedCert_mem_PPolyOn (hNP : NP encBits ⊆ PPolyOn encBits) :
    {q : MergeInput × List Bool |
      IsMergedCert q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 (mergeCert₀ q.1) (mergeCert₁ q.1) q.2} ∈
      PPolyOn (encPair encMerge encBits) := by
  let encQ := encPair encMerge encBits
  have hq1 : ComputableTidilyInPolyTime (fun q : MergeInput × List Bool => q.1) encQ encMerge :=
    fst encMerge encBits
  have hn : ComputableInPolyTime (fun q : MergeInput × List Bool => q.1.1.1.1) encQ encUnary :=
    .of_tidy ((fst encUnary encUnary).comp ((fst _ _).comp ((fst encHeader encBits).comp hq1)))
  have hs : ComputableInPolyTime (fun q : MergeInput × List Bool => q.1.1.1.2) encQ encUnary :=
    .of_tidy ((snd encUnary encUnary).comp ((fst _ _).comp ((fst encHeader encBits).comp hq1)))
  have hp : ComputableInPolyTime (fun q : MergeInput × List Bool => q.1.1.2.1) encQ encBits :=
    .of_tidy ((fst encBits encUnary).comp ((snd _ _).comp ((fst encHeader encBits).comp hq1)))
  have hw₀ : ComputableInPolyTime (fun q : MergeInput × List Bool => mergeCert₀ q.1) encQ encBits :=
    computableInPolyTime_mergeCert₀.comp (.of_tidy hq1)
  have hw₁ : ComputableInPolyTime (fun q : MergeInput × List Bool => mergeCert₁ q.1) encQ encBits :=
    computableInPolyTime_mergeCert₁.comp (.of_tidy hq1)
  have hw : ComputableInPolyTime (fun q : MergeInput × List Bool => q.2) encQ encBits :=
    .of_tidy (snd encMerge encBits)
  have hvalid : {q : MergeInput × List Bool | validCert q.1.1.1.1 q.1.1.1.2 q.2 = true} ∈
      PPolyOn encQ :=
    PPolyOn_of_computableInPolyTime (computableInPolyTime_validCert hn hs hw)
  let encQX := encPair encQ encBits
  have hqx1 : ComputableInPolyTime (fun r : (MergeInput × List Bool) × List Bool => r.1)
      encQX encQ := .of_tidy (fst encQ encBits)
  have hagrees_pt : {r : (MergeInput × List Bool) × List Bool |
      agreesOnPoint r.1.1.1.1.1 r.1.1.1.1.2 r.1.1.1.2.1
        (mergeCert₀ r.1.1) (mergeCert₁ r.1.1) r.1.2 r.2 = true} ∈ PPolyOn encQX :=
    PPolyOn_of_computableInPolyTime (computableInPolyTime_agreesOnPoint
      (hn.comp hqx1) (hs.comp hqx1) (hp.comp hqx1) (hw₀.comp hqx1) (hw₁.comp hqx1)
      (hw.comp hqx1) (.of_tidy (snd encQ encBits)))
  have hagrees : {q : MergeInput × List Bool |
      AgreesWithChildren q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 (mergeCert₀ q.1) (mergeCert₁ q.1) q.2} ∈
      PPolyOn encQ :=
    PPolyOn_forall_of_computableInPolyTime_length hNP hn hagrees_pt
  exact PPolyOn_inter hvalid hagrees

open ComputableTidilyInPolyTime in
private theorem isMinMergedCert_mem_PPolyOn (hNP : NP encBits ⊆ PPolyOn encBits) :
    {q : MergeInput × List Bool |
      IsMinMergedCert q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 (mergeCert₀ q.1) (mergeCert₁ q.1) q.2} ∈
      PPolyOn (encPair encMerge encBits) := by
  let encQ := encPair encMerge encBits
  let encQW := encPair encQ encBits
  have hmerged := isMergedCert_mem_PPolyOn hNP
  have hmerged' : {r : (MergeInput × List Bool) × List Bool |
      IsMergedCert r.1.1.1.1.1 r.1.1.1.1.2 r.1.1.1.2.1
        (mergeCert₀ r.1.1) (mergeCert₁ r.1.1) r.2} ∈ PPolyOn encQW := by
    have hred : PolyTimeReducible encQW encQ
        {r : (MergeInput × List Bool) × List Bool |
          IsMergedCert r.1.1.1.1.1 r.1.1.1.1.2 r.1.1.1.2.1
            (mergeCert₀ r.1.1) (mergeCert₁ r.1.1) r.2}
        {q : MergeInput × List Bool |
          IsMergedCert q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 (mergeCert₀ q.1) (mergeCert₁ q.1) q.2} :=
      ⟨fun r => (r.1.1, r.2),
        .of_tidy (((fst encMerge encBits).comp (fst encQ encBits)).prod (snd encQ encBits)),
        fun _ => Iff.rfl⟩
    exact hred.mem_PPolyOn hmerged
  have hwordLt : {r : (MergeInput × List Bool) × List Bool |
      BitString.wordLt r.2 r.1.2 = false} ∈ PPolyOn encQW := by
    have hcomp : ComputableInPolyTime
        (fun r : (MergeInput × List Bool) × List Bool => !BitString.wordLt r.2 r.1.2)
        encQW encBool :=
      .of_tidy (bool_not.comp (bitsWordLt
        (snd encQ encBits) ((snd encMerge encBits).comp (fst encQ encBits))))
    simpa [Bool.not_eq_true'] using PPolyOn_of_computableInPolyTime hcomp
  have hcert_q : ComputableInPolyTime
      (fun q : MergeInput × List Bool => certLength q.1.1.1.1 q.1.1.1.2) encQ encUnary := by
    refine .of_tidy ?_
    have hq1 : ComputableTidilyInPolyTime (fun q : MergeInput × List Bool => q.1) encQ encMerge :=
      fst encMerge encBits
    have hn : ComputableTidilyInPolyTime (fun q : MergeInput × List Bool => q.1.1.1.1)
        encQ encUnary :=
      (fst encUnary encUnary).comp ((fst _ _).comp ((fst encHeader encBits).comp hq1))
    have hs : ComputableTidilyInPolyTime (fun q : MergeInput × List Bool => q.1.1.1.2)
        encQ encUnary :=
      (snd encUnary encUnary).comp ((fst _ _).comp ((fst encHeader encBits).comp hq1))
    unfold certLength
    fun_prop
  have hforall : {q : MergeInput × List Bool |
      ∀ w' : List Bool, w'.length = certLength q.1.1.1.1 q.1.1.1.2 →
        IsMergedCert q.1.1.1.1 q.1.1.1.2 q.1.1.2.1 (mergeCert₀ q.1) (mergeCert₁ q.1) w' →
          BitString.wordLt w' q.2 = false} ∈ PPolyOn encQ :=
    PPolyOn_forall_of_computableInPolyTime_length hNP hcert_q (PPolyOn_imp hmerged' hwordLt)
  exact PPolyOn_inter hmerged hforall

open ComputableTidilyInPolyTime in
/-- **Under `NP ⊆ P/poly`, `CircuitMinMergeLanguage` has polynomial-size circuits.** Since
`CircuitMinMergeLanguage` is defined by bounded existential and universal quantifiers over
polynomial-time predicates, nonuniform quantifier elimination puts it in `PPolyOn encMerge`
[McKayMurrayWilliams2019, Proof of Lemma 3.1]. -/
theorem circuitMinMergeLanguage_mem_PPolyOn (hNP : NP encBits ⊆ PPolyOn encBits) :
    CircuitMinMergeLanguage ∈ PPolyOn encMerge := by
  let encQ := encPair encMerge encBits
  have hn_a : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.1) encMerge encUnary :=
    (fst encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hs_a : ComputableTidilyInPolyTime (fun a : MergeInput => a.1.1.2) encMerge encUnary :=
    (snd encUnary encUnary).comp ((fst _ _).comp (fst encHeader encBits))
  have hcert_a : ComputableInPolyTime
      (fun a : MergeInput => certLength a.1.1.1 a.1.1.2) encMerge encUnary := by
    refine .of_tidy ?_
    unfold certLength
    fun_prop
  have hok : {a : MergeInput | mergeOk₀ a = true ∧ mergeOk₁ a = true} ∈ PPolyOn encMerge := by
    have hok₀ : ComputableTidilyInPolyTime mergeOk₀ encMerge encBool :=
      bitsGetDWithInput (snd encHeader encBits) (const 0) false
    have hsw : ComputableTidilyInPolyTime
        (fun a : MergeInput => stateWidth a.1.1.1 a.1.1.2) encMerge encUnary := by
      unfold stateWidth certLength
      fun_prop
    have hok₁ : ComputableTidilyInPolyTime mergeOk₁ encMerge encBool :=
      bitsGetDWithInput (snd encHeader encBits) hsw false
    simpa [Bool.and_eq_true] using
      PPolyOn_of_computableInPolyTime (.of_tidy (bool_and' hok₀ hok₁))
  have hj_q : ComputableTidilyInPolyTime
      (fun q : MergeInput × List Bool => q.1.1.2.2) encQ encUnary :=
    (snd encBits encUnary).comp ((snd _ _).comp
      ((fst encHeader encBits).comp (fst encMerge encBits)))
  have hbit_q : {q : MergeInput × List Bool |
      (q.1.1.2.2 == 0 || q.2.getD (q.1.1.2.2 - 1) false) = true} ∈ PPolyOn encQ := by
    have hj0 : ComputableTidilyInPolyTime
        (fun q : MergeInput × List Bool => q.1.1.2.2 == 0) encQ encBool :=
      hj_q.beq (const 0)
    have hget : ComputableTidilyInPolyTime
        (fun q : MergeInput × List Bool => q.2.getD (q.1.1.2.2 - 1) false) encQ encBool :=
      bitsGetDWithInput (snd encMerge encBits) (unary_sub.comp (hj_q.prod (const 1))) false
    exact PPolyOn_of_computableInPolyTime (.of_tidy (bool_or.comp (hj0.prod hget)))
  have hex : {a : MergeInput | ∃ w : List Bool, w.length = certLength a.1.1.1 a.1.1.2 ∧
      (IsMinMergedCert a.1.1.1 a.1.1.2 a.1.2.1 (mergeCert₀ a) (mergeCert₁ a) w ∧
        (a.1.2.2 == 0 || w.getD (a.1.2.2 - 1) false) = true)} ∈ PPolyOn encMerge :=
    PPolyOn_exists_of_computableInPolyTime_length hNP hcert_a
      (PPolyOn_inter (isMinMergedCert_mem_PPolyOn hNP) hbit_q)
  have h_eq : CircuitMinMergeLanguage =
      {a : MergeInput | mergeOk₀ a = true ∧ mergeOk₁ a = true} ∩
      {a : MergeInput | ∃ w : List Bool, w.length = certLength a.1.1.1 a.1.1.2 ∧
        (IsMinMergedCert a.1.1.1 a.1.1.2 a.1.2.1 (mergeCert₀ a) (mergeCert₁ a) w ∧
          (a.1.2.2 == 0 || w.getD (a.1.2.2 - 1) false) = true)} := by
    ext a
    simp only [CircuitMinMergeLanguage, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => exists_congr fun w => ?_
    exact ⟨fun ⟨hmin, hbit⟩ => ⟨length_of_validCert hmin.1.1, hmin, hbit⟩,
      fun ⟨_, hmin, hbit⟩ => ⟨hmin, hbit⟩⟩
  rw [h_eq]
  exact PPolyOn_inter hok hex

/-! ### Subcube certificates and semantic tree synthesis -/

/-- `w` is a valid size-`s` circuit certificate on `n` inputs that computes `f` on every point in
the subcube `p`. -/
def IsSubcubeCert (n s : ℕ) (f : BooleanFunction n) (p w : List Bool) : Prop :=
  validCert n s w = true ∧
    ∀ x : BitString n, inSubcube p (List.ofFn x) = true → evalCert n s w (List.ofFn x) = f x

/-- `w` is the lexicographically smallest (`BitString.wordLt`) certificate satisfying
`IsSubcubeCert n s f p`. -/
def IsMinSubcubeCert (n s : ℕ) (f : BooleanFunction n) (p w : List Bool) : Prop :=
  IsSubcubeCert n s f p w ∧
    ∀ w' : List Bool, w'.length = certLength n s →
      IsSubcubeCert n s f p w' → BitString.wordLt w' w = false

private theorem exists_isMinSubcubeCert_iff {n s : ℕ} {f : BooleanFunction n} {p : List Bool} :
    (∃ w, IsMinSubcubeCert n s f p w) ↔ ∃ w, IsSubcubeCert n s f p w := by
  refine ⟨fun ⟨w, hw, _⟩ => ⟨w, hw⟩, fun ⟨w₀, hw₀⟩ => ?_⟩
  obtain ⟨w, _, hPw, hmin⟩ :=
    exists_wordLt_min ⟨w₀, length_of_validCert hw₀.1, hw₀⟩
  exact ⟨w, hPw, hmin⟩

private theorem isMinSubcubeCert_unique {n s : ℕ} {f : BooleanFunction n} {p w₁ w₂ : List Bool}
    (h₁ : IsMinSubcubeCert n s f p w₁) (h₂ : IsMinSubcubeCert n s f p w₂) :
    w₁ = w₂ :=
  eq_of_wordLt_eq_false (length_of_validCert h₁.1.1) (length_of_validCert h₂.1.1)
    (h₂.2 w₁ (length_of_validCert h₁.1.1) h₁.1)
    (h₁.2 w₂ (length_of_validCert h₂.1.1) h₂.1)

private theorem isSubcubeCert_append_of_isSubcubeCert {n s : ℕ} {f : BooleanFunction n}
    {p w : List Bool} (hp : p.length < n) (hw : IsSubcubeCert n s f p w) (b : Bool) :
    IsSubcubeCert n s f (p ++ [b]) w := by
  refine ⟨hw.1, fun x hx => hw.2 x ?_⟩
  have hx' : p.length < (List.ofFn x).length := by simpa using hp
  exact ((inSubcube_append_singleton hx').1 hx).1

private theorem isMergedCert_iff_isSubcubeCert {n s : ℕ} {f : BooleanFunction n}
    {p w₀ w₁ w : List Bool} (hp : p.length < n)
    (hw₀ : IsSubcubeCert n s f (p ++ [false]) w₀)
    (hw₁ : IsSubcubeCert n s f (p ++ [true]) w₁) :
    IsMergedCert n s p w₀ w₁ w ↔ IsSubcubeCert n s f p w := by
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have hpt := h (List.ofFn x) List.length_ofFn
    simp only [agreesOnPoint, hx, Bool.not_true, Bool.false_or, beq_iff_eq] at hpt
    have hlen : p.length < (List.ofFn x).length := by simpa using hp
    cases hb : (List.ofFn x).getD p.length false
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hpt
      exact hpt.trans (hw₀.2 x ((inSubcube_append_singleton hlen).2 ⟨hx, hb⟩))
    · simp only [hb, ↓reduceIte] at hpt
      exact hpt.trans (hw₁.2 x ((inSubcube_append_singleton hlen).2 ⟨hx, hb⟩))
  · obtain ⟨y, rfl⟩ : ∃ y : BitString n, List.ofFn y = x :=
      ⟨BitString.ofList n x, BitString.ofFn_ofList hx⟩
    have hlen : p.length < (List.ofFn y).length := by simpa using hp
    simp only [agreesOnPoint, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    cases hin : inSubcube p (List.ofFn y)
    · left; rfl
    · right
      rw [h y hin]
      cases hb : (List.ofFn y).getD p.length false
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact (hw₀.2 y ((inSubcube_append_singleton hlen).2 ⟨hin, hb⟩)).symm
      · simp only [↓reduceIte]
        exact (hw₁.2 y ((inSubcube_append_singleton hlen).2 ⟨hin, hb⟩)).symm

private theorem isMinMergedCert_iff_isMinSubcubeCert {n s : ℕ} {f : BooleanFunction n}
    {p w₀ w₁ w : List Bool} (hp : p.length < n)
    (hw₀ : IsSubcubeCert n s f (p ++ [false]) w₀)
    (hw₁ : IsSubcubeCert n s f (p ++ [true]) w₁) :
    IsMinMergedCert n s p w₀ w₁ w ↔ IsMinSubcubeCert n s f p w := by
  have hiff := fun w' => isMergedCert_iff_isSubcubeCert hp hw₀ hw₁ (w := w')
  exact and_congr (hiff w) (forall_congr' fun w' => imp_congr_right fun _ =>
    imp_congr_left (hiff w'))

open Classical in
/-- The `stateWidth n s`-bit state vector of subcube `p` for `f`: bit `0` records whether a size-`s`
circuit certificate exists for `f` on `p`, and bits `1 .. certLength n s` record the
lexicographically smallest such certificate (or all `false` if none exists). -/
noncomputable def subcubeState (n s : ℕ) (f : BooleanFunction n) (p : List Bool) :
    BitString (stateWidth n s) :=
  fun j => decide (∃ w : List Bool, IsMinSubcubeCert n s f p w ∧
    ((j : ℕ) == 0 || w.getD ((j : ℕ) - 1) false) = true)

private theorem subcubeState_eq_true_iff (n s : ℕ) (f : BooleanFunction n) (p : List Bool)
    (j : Fin (stateWidth n s)) :
    subcubeState n s f p j = true ↔
      ∃ w : List Bool, IsMinSubcubeCert n s f p w ∧
        ((j : ℕ) == 0 || w.getD ((j : ℕ) - 1) false) = true :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

private theorem getD_zero_ofFn_subcubeState_eq_true_iff (n s : ℕ) (f : BooleanFunction n)
    (p : List Bool) :
    (List.ofFn (subcubeState n s f p)).getD 0 false = true ↔ ∃ w, IsSubcubeCert n s f p w := by
  have h0 : 0 < (List.ofFn (subcubeState n s f p)).length := by
    rw [List.length_ofFn, stateWidth]
    omega
  rw [List.getD_eq_getElem _ _ h0, List.getElem_ofFn, subcubeState_eq_true_iff]
  simp [exists_isMinSubcubeCert_iff]

private theorem drop_one_ofFn_subcubeState_eq {n s : ℕ} {f : BooleanFunction n}
    {p w : List Bool} (hw : IsMinSubcubeCert n s f p w) :
    (List.ofFn (subcubeState n s f p)).drop 1 = w := by
  have hwlen : w.length = certLength n s := length_of_validCert hw.1.1
  have hdlen : ((List.ofFn (subcubeState n s f p)).drop 1).length = w.length := by
    rw [List.length_drop, List.length_ofFn, stateWidth, hwlen]
    omega
  refine List.ext_getElem hdlen fun i h1 h2 => ?_
  rw [List.getElem_drop, List.getElem_ofFn, Bool.eq_iff_iff, subcubeState_eq_true_iff]
  have hi : i < w.length := h2
  have h1i : ((1 + i : ℕ) == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have hsub : 1 + i - 1 = i := by omega
  simp only [h1i, Bool.false_or, hsub]
  constructor
  · rintro ⟨w', hw', hbit⟩
    obtain rfl : w' = w := isMinSubcubeCert_unique hw' hw
    rwa [List.getD_eq_getElem _ _ hi] at hbit
  · intro hbit
    refine ⟨w, hw, ?_⟩
    rwa [List.getD_eq_getElem _ _ hi]

private theorem mergeOk₀_append_subcubeState (n s : ℕ) (f : BooleanFunction n) (p : List Bool)
    (j : ℕ) :
    mergeOk₀ (((n, s), (p, j)),
      List.ofFn (Fin.append (subcubeState n s f (p ++ [false]))
        (subcubeState n s f (p ++ [true])))) =
      (List.ofFn (subcubeState n s f (p ++ [false]))).getD 0 false := by
  simp only [mergeOk₀, List.ofFn_fin_append]
  have hlen0 : (List.ofFn (subcubeState n s f (p ++ [false]))).length = certLength n s + 1 :=
    List.length_ofFn
  have hlen : 0 < (List.ofFn (subcubeState n s f (p ++ [false]))).length := by omega
  have htot : 0 < (List.ofFn (subcubeState n s f (p ++ [false])) ++
      List.ofFn (subcubeState n s f (p ++ [true]))).length := by
    rw [List.length_append]
    omega
  rw [List.getD_eq_getElem _ _ htot, List.getElem_append_left hlen,
    List.getD_eq_getElem _ _ hlen]

private theorem mergeOk₁_append_subcubeState (n s : ℕ) (f : BooleanFunction n) (p : List Bool)
    (j : ℕ) :
    mergeOk₁ (((n, s), (p, j)),
      List.ofFn (Fin.append (subcubeState n s f (p ++ [false]))
        (subcubeState n s f (p ++ [true])))) =
      (List.ofFn (subcubeState n s f (p ++ [true]))).getD 0 false := by
  simp only [mergeOk₁, List.ofFn_fin_append]
  have hlen0 : (List.ofFn (subcubeState n s f (p ++ [false]))).length = stateWidth n s :=
    List.length_ofFn
  have hlen1' : (List.ofFn (subcubeState n s f (p ++ [true]))).length = certLength n s + 1 :=
    List.length_ofFn
  have hlen1 : 0 < (List.ofFn (subcubeState n s f (p ++ [true]))).length := by omega
  have htot : stateWidth n s < (List.ofFn (subcubeState n s f (p ++ [false])) ++
      List.ofFn (subcubeState n s f (p ++ [true]))).length := by
    rw [List.length_append, hlen0]
    omega
  rw [List.getD_eq_getElem _ _ htot,
    List.getElem_append_right (by omega), List.getD_eq_getElem _ _ hlen1]
  simp [hlen0]

private theorem mergeCert₀_append_subcubeState (n s : ℕ) (f : BooleanFunction n) (p : List Bool)
    (j : ℕ) :
    mergeCert₀ (((n, s), (p, j)),
      List.ofFn (Fin.append (subcubeState n s f (p ++ [false]))
        (subcubeState n s f (p ++ [true])))) =
      (List.ofFn (subcubeState n s f (p ++ [false]))).drop 1 := by
  simp only [mergeCert₀, List.ofFn_fin_append]
  have hlen0 : (List.ofFn (subcubeState n s f (p ++ [false]))).length = certLength n s + 1 :=
    List.length_ofFn
  rw [List.drop_append_of_le_length (by omega), List.take_left' (by simp [hlen0])]

private theorem mergeCert₁_append_subcubeState (n s : ℕ) (f : BooleanFunction n) (p : List Bool)
    (j : ℕ) :
    mergeCert₁ (((n, s), (p, j)),
      List.ofFn (Fin.append (subcubeState n s f (p ++ [false]))
        (subcubeState n s f (p ++ [true])))) =
      (List.ofFn (subcubeState n s f (p ++ [true]))).drop 1 := by
  simp only [mergeCert₁, List.ofFn_fin_append]
  have hlen0 : (List.ofFn (subcubeState n s f (p ++ [false]))).length = stateWidth n s :=
    List.length_ofFn
  have hlen1 : (List.ofFn (subcubeState n s f (p ++ [true]))).length = certLength n s + 1 :=
    List.length_ofFn
  have hdrop : stateWidth n s + 1 =
      (List.ofFn (subcubeState n s f (p ++ [false]))).length + 1 := by rw [hlen0]
  rw [hdrop, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left, List.take_of_length_le (by simp [hlen1])]

/-- The multi-output merge step obtained by hardwiring the header `((n, s), (p, j))` into the
slices of a language `L` for each output bit `j : Fin (stateWidth n s)`. -/
private noncomputable def mergeVec (L : Language Bool) (n s : ℕ) (p : List Bool)
    (y : BitString (stateWidth n s + stateWidth n s)) : BitString (stateWidth n s) :=
  fun j =>
    let f := frame (encHeader ((n, s), (p, (j : ℕ))))
    L.slice (f.length + (stateWidth n s + stateWidth n s))
      (substitute (prependInputs (BitString.ofList f.length f)) y)

private theorem mergeVec_eq_subcubeState {L : Language Bool}
    (hL : ∀ a : MergeInput, a ∈ CircuitMinMergeLanguage ↔ encMerge a ∈ L)
    {n s : ℕ} (f : BooleanFunction n) {p : List Bool} (hp : p.length < n) :
    mergeVec L n s p
      (Fin.append (subcubeState n s f (p ++ [false])) (subcubeState n s f (p ++ [true]))) =
      subcubeState n s f p := by
  funext j
  set y := Fin.append (subcubeState n s f (p ++ [false])) (subcubeState n s f (p ++ [true]))
  set hdr : MergeHeader := ((n, s), (p, (j : ℕ)))
  set fh := frame (encHeader hdr)
  have hofFn : List.ofFn (substitute (prependInputs (BitString.ofList fh.length fh)) y) =
      encMerge (hdr, List.ofFn y) := by
    rw [substitute_prependInputs, List.ofFn_fin_append, BitString.ofFn_ofList rfl]
    rfl
  rw [Bool.eq_iff_iff]
  change L.slice (fh.length + (stateWidth n s + stateWidth n s))
      (substitute (prependInputs (BitString.ofList fh.length fh)) y) = true ↔
    subcubeState n s f p j = true
  rw [Language.slice_eq_true_iff, hofFn, ← hL (hdr, List.ofFn y), subcubeState_eq_true_iff]
  simp only [CircuitMinMergeLanguage, Set.mem_ofPred_eq, hdr, y, mergeOk₀_append_subcubeState,
    mergeOk₁_append_subcubeState, mergeCert₀_append_subcubeState, mergeCert₁_append_subcubeState,
    getD_zero_ofFn_subcubeState_eq_true_iff]
  constructor
  · rintro ⟨h0, h1, w, hmin, hbit⟩
    obtain ⟨w₀, hw₀⟩ := exists_isMinSubcubeCert_iff.2 h0
    obtain ⟨w₁, hw₁⟩ := exists_isMinSubcubeCert_iff.2 h1
    rw [drop_one_ofFn_subcubeState_eq hw₀, drop_one_ofFn_subcubeState_eq hw₁] at hmin
    exact ⟨w, (isMinMergedCert_iff_isMinSubcubeCert hp hw₀.1 hw₁.1).1 hmin, hbit⟩
  · rintro ⟨w, hmin, hbit⟩
    have h0 : ∃ w₀, IsSubcubeCert n s f (p ++ [false]) w₀ :=
      ⟨w, isSubcubeCert_append_of_isSubcubeCert hp hmin.1 false⟩
    have h1 : ∃ w₁, IsSubcubeCert n s f (p ++ [true]) w₁ :=
      ⟨w, isSubcubeCert_append_of_isSubcubeCert hp hmin.1 true⟩
    obtain ⟨w₀, hw₀⟩ := exists_isMinSubcubeCert_iff.2 h0
    obtain ⟨w₁, hw₁⟩ := exists_isMinSubcubeCert_iff.2 h1
    refine ⟨h0, h1, w, ?_, hbit⟩
    rw [drop_one_ofFn_subcubeState_eq hw₀, drop_one_ofFn_subcubeState_eq hw₁]
    exact (isMinMergedCert_iff_isMinSubcubeCert hp hw₀.1 hw₁.1).2 hmin

private theorem complexity_mergeVec_le (L : Language Bool) (n s : ℕ) (p : List Bool) {M : ℕ}
    (hM : ∀ j : Fin (stateWidth n s),
      complexity interpretation
        (single (L.slice ((frame (encHeader ((n, s), (p, (j : ℕ))))).length +
          (stateWidth n s + stateWidth n s)))) ≤ M) :
    complexity interpretation (mergeVec L n s p) ≤ stateWidth n s * (M + 2) := by
  refine (complexity_pi_le (fun j y => mergeVec L n s p y j)).trans ?_
  calc ∑ j : Fin (stateWidth n s),
        complexity interpretation (single fun y => mergeVec L n s p y j)
      ≤ ∑ _j : Fin (stateWidth n s), (M + 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact (complexity_substitute_le _ _).trans (Nat.add_le_add_right (hM j) 2)
    _ = stateWidth n s * (M + 2) := by simp

private theorem complexity_single_comp_proj_le {m : ℕ} (g : Bool → Bool) (i₀ : Fin m) :
    complexity interpretation (single fun x : BitString m => g (x i₀)) ≤ 1 := by
  cases h0 : g false <;> cases h1 : g true
  · have h : (fun x : BitString m => g (x i₀)) = fun _ => false := by
      funext x; cases x i₀ <;> assumption
    rw [h]
    exact (Synthesis.of_forall_eq_const (s := inputs m) false (fun _ => rfl)).complexity_le
  · have h : (fun x : BitString m => g (x i₀)) = fun x => x i₀ := by
      funext x; cases x i₀ <;> assumption
    rw [h, complexity_single_proj]
    omega
  · have h : (fun x : BitString m => g (x i₀)) = fun x => !(x i₀) := by
      funext x; cases x i₀ <;> simp [h0, h1]
    rw [h]
    simpa [complexity_single_proj] using complexity_not_le (fun x : BitString m => x i₀)
  · have h : (fun x : BitString m => g (x i₀)) = fun _ => true := by
      funext x; cases x i₀ <;> assumption
    rw [h]
    exact (Synthesis.of_forall_eq_const (s := inputs m) true (fun _ => rfl)).complexity_le

private theorem isSubcubeCert_of_length_eq {n s : ℕ} {f : BooleanFunction n} {p w : List Bool}
    (hp : p.length = n) :
    IsSubcubeCert n s f p w ↔
      validCert n s w = true ∧ evalCert n s w p = f (BitString.ofList n p) := by
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h (BitString.ofList n p)
      (by simp [inSubcube, BitString.ofFn_ofList hp])
    rwa [BitString.ofFn_ofList hp] at h1
  · have hx' : List.ofFn x = p :=
      (inSubcube_of_length_eq (hp.trans List.length_ofFn.symm)).1 hx
    have hxy : x = BitString.ofList n p := by
      rw [← hx', BitString.ofList_ofFn]
    rw [hx', hxy, h]

private theorem subcubeState_congr_of_length_eq {n s : ℕ} {f₁ f₂ : BooleanFunction n}
    {p : List Bool} (hp : p.length = n)
    (hf : f₁ (BitString.ofList n p) = f₂ (BitString.ofList n p)) :
    subcubeState n s f₁ p = subcubeState n s f₂ p := by
  have hsub : ∀ w, IsSubcubeCert n s f₁ p w ↔ IsSubcubeCert n s f₂ p w := fun w => by
    rw [isSubcubeCert_of_length_eq hp, isSubcubeCert_of_length_eq hp, hf]
  have hmin : ∀ w, IsMinSubcubeCert n s f₁ p w ↔ IsMinSubcubeCert n s f₂ p w := fun w =>
    and_congr (hsub w) (forall_congr' fun w' => imp_congr_right fun _ =>
      imp_congr_left (hsub w'))
  funext j
  rw [Bool.eq_iff_iff, subcubeState_eq_true_iff, subcubeState_eq_true_iff]
  exact exists_congr fun w => and_congr_left fun _ => hmin w

private theorem complexity_subcubeState_leaf_le {n s : ℕ} {p : List Bool} (hp : p.length = n) :
    complexity interpretation
      (fun T : BitString (2 ^ n) => subcubeState n s ((truthTable n).symm T) p) ≤
      stateWidth n s := by
  let i₀ : Fin (2 ^ n) := BitString.equivFin n (BitString.ofList n p)
  have heq : (fun T : BitString (2 ^ n) => subcubeState n s ((truthTable n).symm T) p) =
      fun T j => subcubeState n s (fun _ => T i₀) p j := by
    funext T j
    exact congrFun
      (subcubeState_congr_of_length_eq (f₁ := (truthTable n).symm T) (f₂ := fun _ => T i₀) hp rfl) j
  rw [heq]
  refine (complexity_pi_le (fun j (T : BitString (2 ^ n)) =>
    subcubeState n s (fun _ => T i₀) p j)).trans ?_
  calc ∑ j : Fin (stateWidth n s),
        complexity interpretation (single fun T : BitString (2 ^ n) =>
          subcubeState n s (fun _ => T i₀) p j)
      ≤ ∑ _j : Fin (stateWidth n s), 1 :=
        Finset.sum_le_sum fun j _ =>
          complexity_single_comp_proj_le (fun b => subcubeState n s (fun _ => b) p j) i₀
    _ = stateWidth n s := by simp

private theorem complexity_subcubeState_tree_le {L : Language Bool}
    (hL : ∀ a : MergeInput, a ∈ CircuitMinMergeLanguage ↔ encMerge a ∈ L)
    {n s M : ℕ}
    (hM : ∀ p : List Bool, p.length ≤ n → ∀ j : Fin (stateWidth n s),
      complexity interpretation
        (single (L.slice ((frame (encHeader ((n, s), (p, (j : ℕ))))).length +
          (stateWidth n s + stateWidth n s)))) ≤ M) :
    ∀ (k : ℕ) (p : List Bool), p.length + k = n →
      complexity interpretation
        (fun T : BitString (2 ^ n) => subcubeState n s ((truthTable n).symm T) p) ≤
        2 ^ k * stateWidth n s + (2 ^ k - 1) * (stateWidth n s * (M + 2))
  | 0, p, hp => by
    have hp' : p.length = n := by omega
    simpa using complexity_subcubeState_leaf_le hp'
  | k + 1, p, hp => by
    have hlt : p.length < n := by omega
    have hp0 : (p ++ [false]).length + k = n := by simp; omega
    have hp1 : (p ++ [true]).length + k = n := by simp; omega
    have ih0 := complexity_subcubeState_tree_le hL hM k (p ++ [false]) hp0
    have ih1 := complexity_subcubeState_tree_le hL hM k (p ++ [true]) hp1
    have hmerge : (fun T : BitString (2 ^ n) => subcubeState n s ((truthTable n).symm T) p) =
        mergeVec L n s p ∘ fun T =>
          Fin.append (subcubeState n s ((truthTable n).symm T) (p ++ [false]))
            (subcubeState n s ((truthTable n).symm T) (p ++ [true])) := by
      funext T
      exact (mergeVec_eq_subcubeState hL ((truthTable n).symm T) hlt).symm
    rw [hmerge]
    have hcomp := (complexity_comp_le (I := interpretation)
      (fun T : BitString (2 ^ n) =>
        Fin.append (subcubeState n s ((truthTable n).symm T) (p ++ [false]))
          (subcubeState n s ((truthTable n).symm T) (p ++ [true])))
      (mergeVec L n s p)).trans
      (Nat.add_le_add (complexity_append_le _ _) (complexity_mergeVec_le L n s p (hM p hlt.le)))
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hpow' : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    calc complexity interpretation (mergeVec L n s p ∘ fun T =>
          Fin.append (subcubeState n s ((truthTable n).symm T) (p ++ [false]))
            (subcubeState n s ((truthTable n).symm T) (p ++ [true])))
        ≤ (2 ^ k * stateWidth n s + (2 ^ k - 1) * (stateWidth n s * (M + 2))) +
            (2 ^ k * stateWidth n s + (2 ^ k - 1) * (stateWidth n s * (M + 2))) +
            stateWidth n s * (M + 2) :=
          hcomp.trans (Nat.add_le_add_right (Nat.add_le_add ih0 ih1) _)
      _ = 2 ^ (k + 1) * stateWidth n s + (2 ^ (k + 1) - 1) * (stateWidth n s * (M + 2)) := by
          zify [hpow, hpow']
          ring

private theorem isSubcubeCert_nil_iff {n s : ℕ} {f : BooleanFunction n} :
    (∃ w, IsSubcubeCert n s f [] w) ↔ complexity interpretation (single f) ≤ s := by
  constructor
  · rintro ⟨w, hvalid, heval⟩
    obtain ⟨C, hcS, hC⟩ := exists_circuit_of_validCert hvalid
    refine complexity_le_iff.2 ⟨C, Circuit.computes_single_iff.2 fun x => ?_, hcS⟩
    rw [hC x, heval x (inSubcube_nil _)]
  · intro h
    obtain ⟨C, hC, hcS⟩ := complexity_le_iff.1 h
    obtain ⟨w, hvalid, heval⟩ := exists_validCert_of_circuit C hcS
    exact ⟨w, hvalid, fun x _ => (heval x).trans (Circuit.computes_single_iff.1 hC x)⟩

private theorem subcubeState_nil_zero_eq_slice_MCSPAt (s : ℕ → ℕ) (n : ℕ) (T : BitString (2 ^ n)) :
    subcubeState n (s n) ((truthTable n).symm T) [] ⟨0, Nat.succ_pos _⟩ =
      (MCSPAt s).slice (2 ^ n) T := by
  rw [Bool.eq_iff_iff, slice_MCSPAt_eq_true_iff, ← isSubcubeCert_nil_iff,
    ← exists_isMinSubcubeCert_iff, subcubeState_eq_true_iff]
  simp

private theorem length_frame_encHeader_add_le {n s : ℕ} {p : List Bool} (hp : p.length ≤ n)
    (j : Fin (stateWidth n s)) :
    (frame (encHeader ((n, s), (p, (j : ℕ))))).length + (stateWidth n s + stateWidth n s) ≤
      48 * (n + s + 1) ^ 2 := by
  have hj : (j : ℕ) < stateWidth n s := j.isLt
  have hcert : certLength n s ≤ 5 * (n + s + 1) ^ 2 := by
    unfold certLength
    nlinarith
  have hsw : stateWidth n s ≤ 5 * (n + s + 1) ^ 2 + 1 := by
    unfold stateWidth
    omega
  simp only [encHeader, length_frame, length_encPair, encUnary_apply, List.length_replicate,
    encBits_apply]
  nlinarith

/-! ### Main theorems: MMW19 Lemma 3.1 and Theorem 1.4 (third bullet) -/

/-- **McKay–Murray–Williams, Lemma 3.1** [McKayMurrayWilliams2019]: if `NP ⊆ P/poly`, then there
is a constant `c > 0` such that for every size schedule `s : ℕ → ℕ` and every `n`, the `2 ^ n`-bit
slice of `MCSP[s]` has circuit complexity at most `2 ^ n * c * (n + s n + 1) ^ c`. -/
theorem exists_complexity_MCSPAt_le_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) :
    ∃ c > 0, ∀ (s : ℕ → ℕ) (n : ℕ),
      complexity interpretation (single ((MCSPAt s).slice (2 ^ n))) ≤
        2 ^ n * c * (n + s n + 1) ^ c := by
  obtain ⟨L, hL_PPoly, hL⟩ := circuitMinMergeLanguage_mem_PPolyOn hNP
  obtain ⟨c₀, hc₀⟩ := mem_PPoly_iff_exists_mem_SIZE.1 hL_PPoly
  let C₁ : ℕ := 6 * (c₀ * 49 ^ c₀ + 3) + 1
  let D₁ : ℕ := 2 * c₀ + 2
  let c : ℕ := max C₁ D₁
  have hc_pos : 0 < c := by unfold c C₁; omega
  refine ⟨c, hc_pos, fun s n => ?_⟩
  let N : ℕ := n + s n + 1
  have hN_pos : 1 ≤ N := by unfold N; omega
  let M : ℕ := c₀ * (48 * N ^ 2 + 1) ^ c₀
  have hM (p : List Bool) (hp : p.length ≤ n) (j : Fin (stateWidth n (s n))) :
      complexity interpretation
        (single (L.slice ((frame (encHeader ((n, s n), (p, (j : ℕ))))).length +
          (stateWidth n (s n) + stateWidth n (s n))))) ≤ M := by
    set m := (frame (encHeader ((n, s n), (p, (j : ℕ))))).length +
      (stateWidth n (s n) + stateWidth n (s n))
    have hm : m ≤ 48 * N ^ 2 := length_frame_encHeader_add_le hp j
    exact (hc₀ m).trans (Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left (by omega) c₀))
  have htree : complexity interpretation
      (fun T : BitString (2 ^ n) => subcubeState n (s n) ((truthTable n).symm T) []) ≤
      2 ^ n * (stateWidth n (s n) * (M + 3)) := by
    refine (complexity_subcubeState_tree_le hL hM n [] (by simp)).trans ?_
    have hle : 2 ^ n - 1 ≤ 2 ^ n := Nat.sub_le _ _
    have hmul := Nat.mul_le_mul_right (stateWidth n (s n) * (M + 2)) hle
    nlinarith
  have hslice : single ((MCSPAt s).slice (2 ^ n)) =
      (single fun v : BitString (stateWidth n (s n)) => v ⟨0, Nat.succ_pos _⟩) ∘
        fun T => subcubeState n (s n) ((truthTable n).symm T) [] := by
    funext T i
    rw [Subsingleton.elim i 0]
    exact (subcubeState_nil_zero_eq_slice_MCSPAt s n T).symm
  have hcomp : complexity interpretation (single ((MCSPAt s).slice (2 ^ n))) ≤
      2 ^ n * (stateWidth n (s n) * (M + 3)) := by
    rw [hslice]
    have h0 := complexity_comp_le (I := interpretation)
      (fun T : BitString (2 ^ n) => subcubeState n (s n) ((truthTable n).symm T) [])
      (single fun v : BitString (stateWidth n (s n)) => v ⟨0, Nat.succ_pos _⟩)
    rw [complexity_single_proj, Nat.add_zero] at h0
    exact h0.trans htree
  have hsw : stateWidth n (s n) ≤ 6 * N ^ 2 := by
    unfold stateWidth certLength N
    nlinarith
  have h48 : 48 * N ^ 2 + 1 ≤ 49 * N ^ 2 := by nlinarith
  have hM_le : M + 3 ≤ (c₀ * 49 ^ c₀ + 3) * (N ^ 2) ^ c₀ := by
    have h1 : M ≤ c₀ * 49 ^ c₀ * (N ^ 2) ^ c₀ := by
      calc M ≤ c₀ * (49 * N ^ 2) ^ c₀ :=
            Nat.mul_le_mul_left c₀ (Nat.pow_le_pow_left h48 c₀)
        _ = c₀ * 49 ^ c₀ * (N ^ 2) ^ c₀ := by rw [Nat.mul_pow, Nat.mul_assoc]
    have hpow_pos : 1 ≤ (N ^ 2) ^ c₀ := Nat.one_le_pow _ _ (by nlinarith)
    nlinarith
  have hprod : stateWidth n (s n) * (M + 3) ≤ C₁ * N ^ D₁ := by
    calc stateWidth n (s n) * (M + 3)
        ≤ (6 * N ^ 2) * ((c₀ * 49 ^ c₀ + 3) * (N ^ 2) ^ c₀) := Nat.mul_le_mul hsw hM_le
      _ = 6 * (c₀ * 49 ^ c₀ + 3) * (N ^ 2 * (N ^ 2) ^ c₀) := by ring
      _ ≤ C₁ * N ^ D₁ := by
        rw [← Nat.pow_mul, ← pow_add, show 2 + 2 * c₀ = D₁ by unfold D₁; omega]
        exact Nat.mul_le_mul_right _ (by unfold C₁; omega)
  have hCD : C₁ * N ^ D₁ ≤ c * N ^ c :=
    Nat.mul_le_mul (le_max_left C₁ D₁) (Nat.pow_le_pow_right hN_pos (le_max_right C₁ D₁))
  calc complexity interpretation (single ((MCSPAt s).slice (2 ^ n)))
      ≤ 2 ^ n * (stateWidth n (s n) * (M + 3)) := hcomp
    _ ≤ 2 ^ n * (c * N ^ c) := Nat.mul_le_mul_left (2 ^ n) (hprod.trans hCD)
    _ = 2 ^ n * c * (n + s n + 1) ^ c := by rw [Nat.mul_assoc]

/-- **McKay–Murray–Williams, Lemma 3.1 for polynomial schedules**: if `NP ⊆ P/poly`, then for every
degree `k`, there is `c > 0` such that the `2 ^ n`-bit slice of `MCSP[n ^ k]` has circuit
complexity at most `2 ^ n * c * (n + 1) ^ c`. -/
theorem exists_complexity_MCSPAt_pow_le_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) :
    ∃ c > 0, ∀ n : ℕ,
      complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n))) ≤
        2 ^ n * c * (n + 1) ^ c := by
  obtain ⟨c₀, hc₀_pos, hc₀⟩ := exists_complexity_MCSPAt_le_of_NP_subset_PPoly hNP
  let C₁ : ℕ := c₀ * 2 ^ c₀
  let D₁ : ℕ := (k + 1) * c₀
  let c : ℕ := max C₁ (max D₁ 1)
  refine ⟨c, by positivity, fun n => ?_⟩
  have hbase : n + n ^ k + 1 ≤ 2 * (n + 1) ^ (k + 1) := by
    have h1 : n + 1 ≤ (n + 1) ^ (k + 1) :=
      Nat.le_self_pow (by omega) (n + 1)
    have h2 : n ^ k ≤ (n + 1) ^ (k + 1) :=
      (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))
    omega
  have hpow : (n + n ^ k + 1) ^ c₀ ≤ 2 ^ c₀ * (n + 1) ^ D₁ := by
    calc (n + n ^ k + 1) ^ c₀
        ≤ (2 * (n + 1) ^ (k + 1)) ^ c₀ := Nat.pow_le_pow_left hbase c₀
      _ = 2 ^ c₀ * (n + 1) ^ D₁ := by rw [Nat.mul_pow, ← Nat.pow_mul]
  have hC : C₁ ≤ c := le_max_left _ _
  have hD : D₁ ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  calc complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n)))
      ≤ 2 ^ n * c₀ * (n + n ^ k + 1) ^ c₀ := hc₀ (fun m => m ^ k) n
    _ ≤ 2 ^ n * c₀ * (2 ^ c₀ * (n + 1) ^ D₁) := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ n * (C₁ * (n + 1) ^ D₁) := by unfold C₁; ring
    _ ≤ 2 ^ n * (c * (n + 1) ^ c) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) hD))
    _ = 2 ^ n * c * (n + 1) ^ c := by rw [Nat.mul_assoc]

/-- **Hardness magnification for `MCSP[s]` against `NP ⊆ P/poly`**
[McKayMurrayWilliams2019, Theorem 1.4, third bullet]: if for every `c > 0` there exist a schedule
`s` and input arity `n` such that the `2 ^ n`-bit slice of `MCSP[s]` requires more than
`2 ^ n * c * (n + s n + 1) ^ c` gates, then `NP ⊄ P/poly`. -/
theorem not_NP_subset_PPoly_of_MCSPAt_hard
    (h : ∀ c > 0, ∃ (s : ℕ → ℕ) (n : ℕ),
      2 ^ n * c * (n + s n + 1) ^ c <
        complexity interpretation (single ((MCSPAt s).slice (2 ^ n)))) :
    ¬ (NP encBits ⊆ PPolyOn encBits) := by
  intro hNP
  obtain ⟨c, hc_pos, hub⟩ := exists_complexity_MCSPAt_le_of_NP_subset_PPoly hNP
  obtain ⟨s, n, hlb⟩ := h c hc_pos
  exact (lt_irrefl _) ((hub s n).trans_lt hlb)

/-- **Hardness magnification for `MCSP[s]` to `P ≠ NP`**
[McKayMurrayWilliams2019, Theorem 1.4, third bullet]: if for every `c > 0` there exist a schedule
`s` and input arity `n` such that the `2 ^ n`-bit slice of `MCSP[s]` requires more than
`2 ^ n * c * (n + s n + 1) ^ c` gates, then `P ≠ NP`. -/
theorem P_ne_NP_of_MCSPAt_hard
    (h : ∀ c > 0, ∃ (s : ℕ → ℕ) (n : ℕ),
      2 ^ n * c * (n + s n + 1) ^ c <
        complexity interpretation (single ((MCSPAt s).slice (2 ^ n)))) :
    P encBits ≠ NP encBits := by
  intro hEq
  refine not_NP_subset_PPoly_of_MCSPAt_hard h ?_
  rw [← hEq]
  exact P_subset_PPolyOn

/-- **Hardness magnification for `MCSP[n ^ k]` against `NP ⊆ P/poly`**
[McKayMurrayWilliams2019, Theorem 1.4, third bullet]: if for some `k` and every `c > 0`, there is
`n` such that the `2 ^ n`-bit slice of `MCSP[n ^ k]` requires more than
`2 ^ n * c * (n + 1) ^ c` gates, then `NP ⊄ P/poly`. -/
theorem not_NP_subset_PPoly_of_MCSPAt_pow_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ,
      2 ^ n * c * (n + 1) ^ c <
        complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n)))) :
    ¬ (NP encBits ⊆ PPolyOn encBits) := by
  intro hNP
  obtain ⟨c, hc_pos, hub⟩ := exists_complexity_MCSPAt_pow_le_of_NP_subset_PPoly hNP k
  obtain ⟨n, hlb⟩ := h c hc_pos
  exact (lt_irrefl _) ((hub n).trans_lt hlb)

/-- **Hardness magnification for `MCSP[n ^ k]` to `P ≠ NP`**
[McKayMurrayWilliams2019, Theorem 1.4, third bullet]: if for some `k` and every `c > 0`, there is
`n` such that the `2 ^ n`-bit slice of `MCSP[n ^ k]` requires more than
`2 ^ n * c * (n + 1) ^ c` gates, then `P ≠ NP`. -/
theorem P_ne_NP_of_MCSPAt_pow_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ,
      2 ^ n * c * (n + 1) ^ c <
        complexity interpretation (single ((MCSPAt fun m => m ^ k).slice (2 ^ n)))) :
    P encBits ≠ NP encBits := by
  intro hEq
  refine not_NP_subset_PPoly_of_MCSPAt_pow_hard k h ?_
  rw [← hEq]
  exact P_subset_PPolyOn

end Cslib.MCSP
