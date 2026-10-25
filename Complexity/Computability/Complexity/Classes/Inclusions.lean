/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.PP.Closure
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Classes.Space.Closure
public import Complexity.Computability.Complexity.Classes.Space.Savitch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
import Complexity.Computability.Complexity.Classes.Hierarchy.Time
import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Inclusions between complexity classes

The inclusions between the standard classes that papers cite in their preliminaries
[Arora and Barak, Chapters 2, 4, 5 and 7][AroraBarak09], [Sipser, Chapters 8 and 10][Sipser2013].
This module proves the inclusions that need several classes at once and imports the narrower
modules for the others: `P ⊆ BPP` is in `Complexity.Computability.Complexity.Classes.BPP`, the
closure properties of `PP` in `Complexity.Computability.Complexity.Classes.PP.Closure`, and those
of `PSPACE` in `Complexity.Computability.Complexity.Classes.Space.Closure`.

* `P ⊆ BPP` (`Cslib.Complexity.P_subset_BPP`): a decider ignores its random string.
* `NP ⊆ PP` (`Cslib.Complexity.NP_subset_PP`): accept on half of the random strings outright, and
  on the other half run the verifier, so the majority accepts exactly when some certificate does.
* `PP` is closed under complement (`Cslib.Complexity.compl_mem_PP`): with two more random bits,
  accept on a quarter of the random strings and one more, and on half of them reject what the
  verifier accepts; the majority accepts exactly when the verifier accepts at most half of its
  random strings.
* `NP ⊆ PSPACE` (`Cslib.Complexity.NP_subset_PSPACE`): a nondeterministic machine visits at most
  one new cell per step on each work tape (`Turing.MultiTapeNTM.RunsInTime.runsInSpace`), so `NP`
  is within `NPSPACE`, which is `PSPACE` by Savitch's theorem
  (`Cslib.Complexity.NPSPACE_subset_PSPACE`).
* `PSPACE ⊆ EXP` (`Cslib.Complexity.PSPACE_subset_EXP`): Savitch's decider runs within time
  exponential in a polynomial (`Cslib.Reachability.computableTidilyInO_savitch`).
* `PH ⊆ PSPACE` (`Cslib.Complexity.PH_subset_PSPACE`): `PSPACE` contains `P`, is closed under
  complement (`Cslib.Complexity.compl_mem_PSPACE`), under polynomial-time reductions
  (`Cslib.Complexity.PolyTimeReducible.mem_PSPACE`) and under polynomially bounded existential
  quantification (`Cslib.Complexity.setOf_exists_mem_PSPACE`), so it evaluates the alternating
  quantifiers of every level of the hierarchy one at a time. The existential quantifier over the
  words `w` of length `ℓ` is reachability within two steps from the all-zero word to the all-one
  word of width `ℓ + 1`, along edges to `true :: w` for the accepted `w` and from every word
  starting with `true` to the all-one word; Savitch's algorithm decides it at depth `1`,
  enumerating the candidates in place and reusing the space of the decider for each.

With `Cslib.Complexity.P_subset_NP`, these give the chain `P ⊆ NP ⊆ PSPACE ⊆ EXP`. The other
inclusions of the chains are elsewhere: `P ⊆ PSPACE` (`Cslib.Complexity.P_subset_PSPACE`),
`NPSPACE = PSPACE` (`Cslib.Complexity.NPSPACE_eq_PSPACE`), `RP ⊆ NP`
(`Cslib.Complexity.RP_subset_NP`), `BPP ⊆ PP` (`Cslib.Complexity.BPP_subset_PP`), `BPP ⊆ Σ₂ ∩ Π₂`
(`Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two`), `L ⊆ NL ⊆ P`
(`Cslib.Complexity.L_subset_NL`, `Cslib.Complexity.NL_subset_P`), `P ⊆ EXP` and its strictness
(`Cslib.Complexity.P_subset_EXP`, `Cslib.Complexity.P_ssubset_EXP`).

## Main results

* `Cslib.Complexity.NP_subset_NPSPACE`, `Cslib.Complexity.NP_subset_PSPACE`.
* `Cslib.Complexity.PSPACE_subset_EXP`, `Cslib.Complexity.NP_subset_EXP`.
* `Cslib.Complexity.not_NEXP_subset_NP`, `Cslib.Complexity.NP_ssubset_NEXP`.
* `Cslib.Complexity.SigmaP_subset_PSPACE`, `Cslib.Complexity.PH_subset_PSPACE`.
* `Cslib.Complexity.SigmaP_subset_EXP`, `Cslib.Complexity.SigmaP_subset_NEXP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Space -/

/-- **`NP ⊆ NPSPACE`**: a nondeterministic machine deciding a problem in polynomial time visits at
most polynomially many work-tape cells. -/
theorem NP_subset_NPSPACE : NP enc ⊆ NPSPACE enc := by
  intro A hA
  obtain ⟨t, ht, k, State, hfinite, ntm, hdec⟩ := decidableInPolyTime_of_mem_NP hA
  exact ⟨k, State, hfinite, ntm, fun a => k * (t a + 1), (PolyBounded.const k).mul
    (ht.add (.const 1)), hdec.decidesInSpace⟩

/-- **`NP ⊆ PSPACE`** [Arora and Barak, Theorem 4.2][AroraBarak09]: `NP ⊆ NPSPACE`, and
`NPSPACE = PSPACE` by Savitch's theorem. -/
theorem NP_subset_PSPACE : NP enc ⊆ PSPACE enc :=
  NP_subset_NPSPACE.trans NPSPACE_subset_PSPACE

/-- A polynomial plus `2` to a polynomial times a polynomial is eventually below `2 ^ n ^ K`. -/
private theorem exists_eventually_le_two_pow_pow {P Q R : ℕ → ℕ} (hP : PolynomiallyBounded P)
    (hQ : PolynomiallyBounded Q) (hR : PolynomiallyBounded R) :
    ∃ K, ∀ᶠ n in atTop, P n + 2 ^ Q n * R n ≤ 2 ^ n ^ K := by
  obtain ⟨K, hK⟩ : PolynomiallyBounded fun n => Q n + n + 1 := by fun_prop
  refine ⟨K, ?_⟩
  filter_upwards [hP.eventually_lt_two_pow, hR.eventually_lt_two_pow, hK] with n h₁ h₂ h₃
  have h₄ : 1 ≤ 2 ^ Q n := Nat.one_le_two_pow
  calc P n + 2 ^ Q n * R n ≤ 2 ^ n * 2 ^ Q n + 2 ^ Q n * 2 ^ n :=
        Nat.add_le_add (h₁.le.trans (Nat.le_mul_of_pos_right _ h₄))
          (Nat.mul_le_mul_left _ h₂.le)
    _ = 2 ^ (Q n + n + 1) := by ring
    _ ≤ 2 ^ n ^ K := Nat.pow_le_pow_right (by norm_num) h₃

/-- **`PSPACE ⊆ EXP`** [Arora and Barak, Theorem 4.2][AroraBarak09],
[Sipser, Section 8.2][Sipser2013]: a problem in `PSPACE` is decided by a nondeterministic machine
within polynomial space (`Cslib.Complexity.PSPACE_subset_NPSPACE`), and Savitch's decider for it
runs within time exponential in a polynomial: its codes have polynomial width `w`, and it runs
`2 ^ ((w + 2) * (w + 1))` rounds of polynomial cost
(`Cslib.Reachability.computableTidilyInO_savitch`). -/
theorem PSPACE_subset_EXP : PSPACE enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, State, hfinite, ntm, s, hs, hAn⟩ := PSPACE_subset_NPSPACE hA
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  -- the inputs and the edge test of Savitch's decider are polynomial-time
  have hwidth := MultiTapeNTM.computableTidilyInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  have hcodes : ComputableTidilyInPolyTime
      (fun a => 2 * ntm.codeWidth c d (enc a) + 2) enc encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp ((ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hwidth)).prod (ComputableTidilyInPolyTime.const 2))
  have hedge : ComputableTidilyInPolyTime
      (fun q : Unit × List Bool × List Bool => (fun _ => ntm.codeEdge) q.1 q.2.1 q.2.2)
      (encPair (encFinEnum Unit) (encPair encBits encBits)) encBool :=
    ntm.computableTidilyInPolyTime_codeEdge ((ComputableTidilyInPolyTime.fst _ _).comp (.snd _ _))
      ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _))
  have hin : ComputableTidilyInPolyTime
      (fun a => ((), 2 * ntm.codeWidth c d (enc a) + 2, 2 * ntm.codeWidth c d (enc a) + 2,
        MultiTapeNTM.viewCode (ntm.codeWidth c d (enc a)) (ntm.initView (enc a)),
        MultiTapeNTM.acceptCode (ntm.codeWidth c d (enc a)))) enc
      (Cslib.Reachability.encArgs (encFinEnum Unit)) :=
    (ComputableTidilyInPolyTime.const ()).prod (hcodes.prod (hcodes.prod
      ((MultiTapeNTM.computableTidilyInPolyTime_viewCode_initView hwidth (.encode enc)).prod
        (MultiTapeNTM.computableTidilyInPolyTime_acceptCode hwidth))))
  obtain ⟨te, se, hte, -, he⟩ := hedge
  obtain ⟨ti, si, hti, -, hi⟩ := hin
  have hedgeO : ComputableTidilyInO _ _ encBool te se :=
    ⟨1, he.mono (fun _ => by omega) fun _ => by omega, fun _ => by simp⟩
  have hinO : ComputableTidilyInO _ enc (Cslib.Reachability.encArgs (encFinEnum Unit)) ti
      fun a => ti a + si a :=
    ⟨1, hi.mono (fun _ => by omega) fun _ => by dsimp only; omega, fun a => by
      have := hi.length_le a
      dsimp only
      omega⟩
  have h := Cslib.Reachability.computableTidilyInO_savitch (edge := fun _ => ntm.codeEdge)
    (par := fun _ => ()) hedgeO hinO
    (fun _ => MultiTapeNTM.length_viewCode (Nat.le_add_right _ _)) fun _ => List.length_replicate ..
  -- polynomial bounds on the width, the inputs and the edge test
  obtain ⟨cW, dW, hW⟩ := hwidth.polyBounded_length.exists_le
  obtain ⟨cT, dT, hT⟩ := hti.exists_le
  obtain ⟨cE, dE, hE⟩ := hte.exists_le
  set L := (encFinEnum Unit ()).length
  have hedgeMax (w : ℕ) : Cslib.Reachability.edgeMax te () w ≤ cE * (2 * L + 3 * w + 3) ^ dE :=
    listMax_le fun u hu => listMax_le fun v hv => by
      refine (hE _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left ?_ dE))
      simp only [length_encPair, encBits_apply, Cslib.BitString.mem_enumList.mp hu,
        Cslib.BitString.mem_enumList.mp hv]
      omega
  set B : ℕ → ℕ := fun n => 2 * (cW * (n + 1) ^ dW) + 2
  obtain ⟨K, hK⟩ := exists_eventually_le_two_pow_pow (P := fun n => cT * (n + 1) ^ dT)
    (Q := fun n => (B n + 2) * (B n + 1))
    (R := fun n => ((B n + 1) * (B n + B n + 1) + L + 1) ^ 2 + cE * (2 * L + 3 * B n + 3) ^ dE)
    (by fun_prop) (by simp only [B]; fun_prop) (by simp only [B]; fun_prop)
  have hmem := setOf_mem_DTIME_of_computableInO (.of_tidy h)
    (t := fun n => cT * (n + 1) ^ dT + 2 ^ ((B n + 2) * (B n + 1)) *
      (((B n + 1) * (B n + B n + 1) + L + 1) ^ 2 + cE * (2 * L + 3 * B n + 3) ^ dE))
    fun a => by
      have hw : 2 * ntm.codeWidth c d (enc a) + 2 ≤ B (enc a).length := by
        have := hW a
        simp only [encUnary_apply, List.length_replicate] at this
        simp only [B]
        omega
      gcongr
      · exact hT a
      · exact (hedgeMax _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left (by omega) dE))
  have hA' : A = {a | ntm.savitchDecide c d (enc a) = true} := Set.ext fun a =>
    (hAn.recognizesInSpace a).2.trans
      (MultiTapeNTM.savitchDecide_eq_true_iff (hAn.recognizesInSpace a).1 (hcd a)).symm
  rw [hA']
  exact mem_EXP_iff.mpr ⟨K, DTIME_mono_of_eventually_le hK hmem⟩

/-- **`NP ⊆ EXP`**, through `PSPACE`. -/
theorem NP_subset_EXP : NP enc ⊆ EXP enc :=
  NP_subset_PSPACE.trans PSPACE_subset_EXP

/-! ### The polynomial hierarchy -/

/-- The pairs `(a, u)` from which alternating quantifiers over blocks of certificates of the
lengths `ps`, starting with `∃` if `q` is `true`, lead to `V (a, u ++ w) = true`. -/
private def alternationSet (enc : α ↪ List Bool) (q : Bool) (ps : List (Polynomial ℕ))
    (V : α × List Bool → Bool) : Set (α × List Bool) :=
  {x | Alternation q (ps.map fun p => p.eval (enc x.1).length) fun w => V (x.1, x.2 ++ w) = true}

/-- Alternating quantifiers over a polynomial-time verifier are decided in polynomial space, one
quantifier at a time: an existential block by `Cslib.Complexity.setOf_exists_mem_PSPACE`, a
universal block as the complement of an existential block for the negated verifier. -/
private theorem alternationSet_mem_PSPACE (ps : List (Polynomial ℕ)) :
    ∀ (q : Bool) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool →
        alternationSet enc q ps V ∈ PSPACE (encPair enc encBits) := by
  induction ps with
  | nil =>
    intro q V hV
    exact P_subset_PSPACE ⟨V, .of_tidy hV, fun x => by simp [alternationSet]⟩
  | cons p ps ih =>
    have hex (V : α × List Bool → Bool)
        (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) :
        alternationSet enc true (p :: ps) V ∈ PSPACE (encPair enc encBits) := by
      -- the remaining quantifiers, after the first block of certificates
      have hB : {y : (α × List Bool) × List Bool | (y.1.1, y.1.2 ++ y.2) ∈
          alternationSet enc false ps V} ∈ PSPACE (encPair (encPair enc encBits) encBits) :=
        PolyTimeReducible.mem_PSPACE ⟨fun y => (y.1.1, y.1.2 ++ y.2),
          .of_tidy (((ComputableTidilyInPolyTime.fst _ _).comp (.fst _ _)).prod
            (ComputableTidilyInPolyTime.bitsAppend
              ((ComputableTidilyInPolyTime.snd _ _).comp (.fst _ _)) (.snd _ _))),
          fun _ => Iff.rfl⟩ (ih false V hV)
      have hℓ : ComputableTidilyInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
          (encPair enc encBits) encUnary :=
        ((ComputableTidilyInPolyTime.unary_eval p).comp
          (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
      convert setOf_exists_mem_PSPACE hB (.of_tidy hℓ) using 1
      ext x
      simp only [alternationSet, List.map_cons, alternation_true_cons, Set.mem_ofPred_eq,
        List.append_assoc]
    intro q V hV
    cases q
    · -- a universal block is the complement of an existential block
      convert compl_mem_PSPACE (hex (fun x => !V x) (ComputableTidilyInPolyTime.bool_not.comp hV))
        using 1
      ext x
      simp only [alternationSet, Set.mem_ofPred_eq, Set.mem_compl_iff, not_alternation,
        Bool.not_true]
      exact alternation_congr fun w => by simp
    · exact hex V hV

/-- **Every level of the polynomial hierarchy is within `PSPACE`.** -/
theorem SigmaP_subset_PSPACE (k : ℕ) : SigmaP k enc ⊆ PSPACE enc := by
  rintro A ⟨ps, V, -, hV, hA⟩
  refine PolyTimeReducible.mem_PSPACE ⟨fun a => (a, []),
    ComputableInPolyTime.id'.prod (.const []), fun a => ?_⟩
    (alternationSet_mem_PSPACE ps true V hV.tidy)
  simp [alternationSet, hA a]

/-- **`PH ⊆ PSPACE`** [Arora and Barak, Chapter 5][AroraBarak09],
[Stockmeyer][Stockmeyer1976]: the quantifiers of a level of the hierarchy are evaluated one at a
time, reusing the space for every certificate. -/
theorem PH_subset_PSPACE : PH enc ⊆ PSPACE enc :=
  Set.iUnion_subset SigmaP_subset_PSPACE

/-- **Every level of the polynomial hierarchy lies in `EXP`**, via `Σₖ ⊆ PSPACE ⊆ EXP`. -/
theorem SigmaP_subset_EXP (k : ℕ) : SigmaP k enc ⊆ EXP enc :=
  (SigmaP_subset_PSPACE k).trans PSPACE_subset_EXP

/-- **Every level of the polynomial hierarchy lies in `NEXP`**, via `Σₖ ⊆ EXP ⊆ NEXP`. -/
theorem SigmaP_subset_NEXP (k : ℕ) : SigmaP k enc ⊆ NEXP enc :=
  (SigmaP_subset_EXP k).trans EXP_subset_NEXP

/-! ### Strict containment `NP ⊂ NEXP` -/

private theorem timeDiagonal_two_pow_two_pow_bound (n : ℕ) :
    (n + 1) ^ 5 * (2 ^ (2 ^ n) + 1) ^ 3 ≤ 2 ^ (2 ^ (n + 4)) := by
  have h₁ : n + 1 ≤ 2 ^ (2 ^ n) := by
    calc n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
  have h₂ : (n + 1) ^ 5 ≤ 2 ^ (5 * 2 ^ n) := by
    calc (n + 1) ^ 5 ≤ (2 ^ (2 ^ n)) ^ 5 := Nat.pow_le_pow_left h₁ 5
      _ = 2 ^ (5 * 2 ^ n) := by rw [← Nat.pow_mul, mul_comm]
  have h₃ : 2 ^ (2 ^ n) + 1 ≤ 2 ^ (2 * 2 ^ n) := by
    have hp₁ : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_two_pow
    have hp₂ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc 2 ^ (2 ^ n) + 1 ≤ 2 * 2 ^ (2 ^ n) := by omega
      _ = 2 ^ (2 ^ n + 1) := (pow_succ' 2 (2 ^ n)).symm
      _ ≤ 2 ^ (2 * 2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₄ : (2 ^ (2 ^ n) + 1) ^ 3 ≤ 2 ^ (6 * 2 ^ n) := by
    calc (2 ^ (2 ^ n) + 1) ^ 3 ≤ (2 ^ (2 * 2 ^ n)) ^ 3 := Nat.pow_le_pow_left h₃ 3
      _ = 2 ^ (6 * 2 ^ n) := by rw [← Nat.pow_mul]; ring_nf
  calc (n + 1) ^ 5 * (2 ^ (2 ^ n) + 1) ^ 3
      ≤ 2 ^ (5 * 2 ^ n) * 2 ^ (6 * 2 ^ n) := Nat.mul_le_mul h₂ h₄
    _ = 2 ^ (11 * 2 ^ n) := by rw [← Nat.pow_add]; ring_nf
    _ ≤ 2 ^ (16 * 2 ^ n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (2 ^ (n + 4)) := by rw [Nat.pow_add, mul_comm (2 ^ n) (2 ^ 4)]

/-- **`NEXP` is not contained in `NP`** on bitstrings [Arora and Barak, Theorem 3.2][AroraBarak09]:
if `NEXP ⊆ NP`, then the doubly-exponential clocked diagonal language, which lies in
`NTIME (2 ^ (2 ^ (n + 4)))`, reduces in two exponential-padding stages through `NEXP ⊆ NP` to a
language in `NP ⊆ EXP`, contradicting the deterministic time hierarchy theorem against `EXP`. -/
theorem not_NEXP_subset_NP : ¬ (NEXP encBits ⊆ NP encBits) := by
  intro hSub
  let J (n : ℕ) : ℕ := 2 ^ (2 ^ n)
  let L : Set (List Bool) := {x | timeDiagonal J x = true}
  have hL_NTIME : L ∈ NTIME encBits fun n => 2 ^ (2 ^ (n + 4)) :=
    DTIME_subset_NTIME (DTIME_mono timeDiagonal_two_pow_two_pow_bound
      (setOf_timeDiagonal_mem_DTIME timeConstructible_two_pow_two_pow))
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hL_NTIME
  set c := Nat.card (Turing.Action k Bool State) * (c₁ + c₂)
  let h₁ (y : List Bool) : List Bool := y ++ List.replicate (2 ^ y.length) true
  let g₂ (x : List Bool) : List Bool := frame x ++ List.replicate (2 ^ (x.length + 4)) true
  have hB₁ : h₁ ⁻¹' ntm.padded c ∈ NP encBits :=
    hSub (preimage_append_two_pow_mem_NEXP (ntm.padded_mem_NP c))
  have hf_add : ComputableInPolyTime (fun n : ℕ => n + 4) encUnary encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_add.comp
      (ComputableTidilyInPolyTime.id'.prod (ComputableTidilyInPolyTime.const 4)))
  have hB₂ : g₂ ⁻¹' (h₁ ⁻¹' ntm.padded c) ∈ NEXP encBits :=
    preimage_pad_mem_NEXP hB₁ hf_add fun n => Nat.le_add_right n 4
  have hL_eq : L = g₂ ⁻¹' (h₁ ⁻¹' ntm.padded c) := by
    ext x
    change x ∈ L ↔ h₁ (g₂ x) ∈ ntm.padded c
    have hpad_eq : h₁ (g₂ x) =
        frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true) := by
      simp [h₁, g₂, List.append_assoc]
    rw [hpad_eq]
    refine (hdec.frame_append_mem_padded_iff (a := x) ?_).symm
    change Nat.card (Turing.Action k Bool State) * (c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂) ≤
      c * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
        List.replicate (2 ^ (g₂ x).length) true)).length
    have hM : 2 ^ (x.length + 4) ≤ (g₂ x).length := by
      simp only [g₂, List.length_append, length_frame, List.length_replicate]
      omega
    have hpow_le : 2 ^ (2 ^ (x.length + 4)) ≤ 2 ^ (g₂ x).length :=
      Nat.pow_le_pow_right (by norm_num) hM
    have hlen_ge : 2 ^ (2 ^ (x.length + 4)) + 1 ≤
        (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true)).length := by
      simp only [List.length_append, length_frame, List.length_replicate]
      calc 2 ^ (2 ^ (x.length + 4)) + 1
          ≤ 2 ^ (g₂ x).length + 1 := Nat.add_le_add_right hpow_le 1
        _ ≤ 2 * x.length + 1 + (2 ^ (x.length + 4) + 2 ^ (g₂ x).length) := by
            have := Nat.zero_le (2 ^ (x.length + 4))
            omega
    have hmul : c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂ ≤
        (c₁ + c₂) * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
          List.replicate (2 ^ (g₂ x).length) true)).length := by
      calc c₁ * 2 ^ (2 ^ (x.length + 4)) + c₂
          ≤ c₁ * (2 ^ (2 ^ (x.length + 4)) + 1) + c₂ * (2 ^ (2 ^ (x.length + 4)) + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left c₁ (Nat.le_succ _))
              (Nat.le_mul_of_pos_right c₂ (Nat.succ_pos _))
        _ = (c₁ + c₂) * (2 ^ (2 ^ (x.length + 4)) + 1) := (Nat.add_mul _ _ _).symm
        _ ≤ (c₁ + c₂) * (frame x ++ (List.replicate (2 ^ (x.length + 4)) true ++
            List.replicate (2 ^ (g₂ x).length) true)).length :=
            Nat.mul_le_mul_left _ hlen_ge
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hmul
  have hL_EXP : L ∈ EXP encBits := hL_eq ▸ NP_subset_EXP (hSub hB₂)
  obtain ⟨d, hd⟩ := mem_EXP_iff.mp hL_EXP
  refine setOf_timeDiagonal_notMem_DTIME (f := fun n => 2 ^ n ^ d) (J := J) (fun C => ?_) hd
  have hpoly : PolynomiallyBounded fun n => n ^ d + n + 1 := by fun_prop
  filter_upwards [hpoly.eventually_lt_two_pow, eventually_ge_atTop (C + 1)] with n hn hC
  have h₁ : 2 * C ≤ 2 ^ (n + 1) := by
    have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    rw [pow_succ']
    omega
  have h₂ : 1 ≤ 2 ^ n ^ d := Nat.one_le_two_pow
  calc C * 2 ^ n ^ d + C
      ≤ 2 * C * 2 ^ n ^ d := by nlinarith
    _ ≤ 2 ^ (n + 1) * 2 ^ n ^ d := Nat.mul_le_mul_right _ h₁
    _ = 2 ^ (n ^ d + n + 1) := by rw [← Nat.pow_add]; ring_nf
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) hn.le

/-- **`NP` is strictly contained in `NEXP`** on bitstrings
[Arora and Barak, Theorem 3.2][AroraBarak09]. -/
theorem NP_ssubset_NEXP : NP encBits ⊂ NEXP encBits :=
  NP_subset_NEXP.ssubset_of_ne fun h => not_NEXP_subset_NP h.ge

end Cslib.Complexity
