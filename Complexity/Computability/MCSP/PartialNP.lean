/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.MCSP.NP
public import Complexity.Computability.MCSP.Partial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD

/-!
# Partial MCSP (`MCSP*`) is in NP

We define standard string encodings for instances of the Partial Minimum Circuit Size Problem
(`Cslib.PartialMCSP.Instance`) and prove that `PartialMCSP` belongs to `NP` under both encodings:
* `Cslib.PartialMCSP.enc`: encodes the $2^n$-entry truth table over `Option Bool` using
  `encList (encOption encBool)` followed by the threshold in unary (`encUnary`), matching
  [Hirahara2022, ECCC TR22-119, Definition 8.4, p. 30].
* `Cslib.PartialMCSP.encBinary`: encodes the $2^n$-entry truth table over `Option Bool` using
  `encList (encOption encBool)` followed by the threshold in binary (`encNat`), matching
  `Cslib.MCSP.encInstance` and [Ilango2020FOCS, Section II.B; ECCC TR20-183, Section 2.2].

A certificate for `PartialMCSP` is a circuit with at most `MCSP.budget n s` gates, in the format
of `Cslib.Circuits.Boolean.readCertificate`, since any partial truth table on `n` variables can be
extended to a total Boolean function `x.completion` of complexity at most $2^n (2 n + 3) + 1$
(`complexity_le_two_pow_mul_add_one`). The verifier evaluates the decoded circuit on every input
$y \in \{0, 1\}^n$ and checks that whenever the partial truth table specifies `some b` at `y`, the
circuit outputs `b`.

We also prove that the embedding `PartialMCSP.Instance.ofTotal : MCSP.Instance →
PartialMCSP.Instance` is computable in polynomial time (`computableInPolyTime_ofTotal_encBinary`),
giving a polynomial-time many-one reduction from `MCSP` to `PartialMCSP`
(`polyTimeReducible_MCSP_PartialMCSP_encBinary`).

## Main definitions

* `Cslib.PartialMCSP.toRaw`: raw data of an instance as a truth table list and a threshold.
* `Cslib.PartialMCSP.enc`: encoding of `PartialMCSP.Instance` with unary threshold.
* `Cslib.PartialMCSP.encBinary`: encoding of `PartialMCSP.Instance` with binary threshold.
* `Cslib.PartialMCSP.tableEntry`: lookup of an input bitstring in a partial truth-table list.
* `Cslib.PartialMCSP.verifier`, `Cslib.PartialMCSP.tableVerifier`: the NP verifiers.

## Main results

* `Cslib.PartialMCSP.mem_of_verifier_eq_true`, `Cslib.PartialMCSP.exists_verifier_append`:
  soundness and padded completeness of `PartialMCSP.verifier`.
* `Cslib.PartialMCSP.isVerifier`, `Cslib.PartialMCSP.isVerifier_encBinary`: verifier correctness.
* `Cslib.PartialMCSP.computableInPolyTime_tableEntry`: table entry lookup is polynomial-time.
* `Cslib.PartialMCSP.computableInPolyTime_verifier`,
  `Cslib.PartialMCSP.computableInPolyTime_verifier_encBinary`: plain polynomial-time certificates
  for the verifiers.
* `Cslib.PartialMCSP.mem_NP`, `Cslib.PartialMCSP.mem_NP_encBinary`: `PartialMCSP ∈ NP`.
* `Cslib.PartialMCSP.computableInPolyTime_ofTotal_encBinary`,
  `Cslib.PartialMCSP.polyTimeReducible_MCSP_PartialMCSP_encBinary`: polynomial-time reduction from
  `MCSP` to `PartialMCSP`.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

@[expose] public section

namespace Cslib.PartialMCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-- The raw data of a partial MCSP instance as a truth table list and a threshold. -/
def toRaw : Instance ↪ List (Option Bool) × ℕ :=
  ⟨fun x => (List.ofFn x.table, x.threshold), by
    rintro ⟨n, T, s⟩ ⟨n', T', s'⟩ h
    obtain ⟨hT, hs⟩ := Prod.ext_iff.1 h
    obtain rfl : n = n' := Nat.pow_right_injective le_rfl (by simpa using congrArg List.length hT)
    obtain rfl := List.ofFn_injective hT
    obtain rfl : s = s' := hs
    rfl⟩

theorem toRaw_apply (x : Instance) : toRaw x = (List.ofFn x.table, x.threshold) := rfl

/-- Instances of `PartialMCSP` encoded by the framed list of `Option Bool` truth-table entries
followed by the threshold in unary [Hirahara2022, ECCC TR22-119, Definition 8.4, p. 30]. -/
def enc : Instance ↪ List Bool :=
  toRaw.trans (encPair (encList (encOption encBool)) encUnary)

theorem enc_apply (x : Instance) :
    enc x = encPair (encList (encOption encBool)) encUnary (List.ofFn x.table, x.threshold) :=
  rfl

/-- Instances of `PartialMCSP` encoded by the framed list of `Option Bool` truth-table entries
followed by the threshold in binary [Ilango2020FOCS, Section II.B; ECCC TR20-183, Section 2.2]. -/
def encBinary : Instance ↪ List Bool :=
  toRaw.trans (encPair (encList (encOption encBool)) encNat)

theorem encBinary_apply (x : Instance) :
    encBinary x = encPair (encList (encOption encBool)) encNat (List.ofFn x.table, x.threshold) :=
  rfl

private theorem two_pow_le_length_encList_table (x : Instance) :
    2 ^ x.arity ≤ (encList (encOption encBool) (List.ofFn x.table)).length := by
  have h := SizedListEncoding.length_le (encA := encOption encBool)
    (encL := encList (encOption encBool)) (List.ofFn x.table)
  simpa using h

private theorem two_pow_le_length_enc_of_encT (encT : ℕ ↪ List Bool) (x : Instance) :
    2 ^ x.arity ≤ (encPair (encList (encOption encBool)) encT (toRaw x)).length := by
  have h := two_pow_le_length_encList_table x
  rw [toRaw_apply, length_encPair]
  dsimp only
  omega

private theorem two_pow_le_length_enc (x : Instance) :
    2 ^ x.arity ≤ (enc x).length :=
  two_pow_le_length_enc_of_encT encUnary x

private theorem two_pow_le_length_encBinary (x : Instance) :
    2 ^ x.arity ≤ (encBinary x).length :=
  two_pow_le_length_enc_of_encT encNat x

/-- The entry of a partial truth-table list at the input with bits `y` (`none` if out of bounds). -/
def tableEntry (table : List (Option Bool)) (y : List Bool) : Option Bool :=
  table.getD (BitString.boundedBinaryValue table.length y.reverse) none

/-- The verifier reads the partial function of an instance from its truth table. -/
theorem tableEntry_ofFn (x : Instance) (y : BitString x.arity) :
    tableEntry (List.ofFn x.table) (List.ofFn y) = x.partialFunction y := by
  have hlt := (BitString.equivFin x.arity y).isLt
  rw [tableEntry, BitString.boundedBinaryValue_eq, BitString.binaryValue_reverse_ofFn,
    List.length_ofFn, Nat.min_eq_right hlt.le, List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]
  rfl

/-- An optional truth-table entry `entry` agrees with a circuit output bit `out` iff
`entry.getD out == out` holds. -/
private theorem getD_beq_self_eq_true_iff (entry : Option Bool) (out : Bool) :
    (entry.getD out == out) = true ↔ ∀ b, entry = some b → out = b := by
  cases entry with
  | none => simp
  | some b =>
    simp only [Option.getD_some, beq_iff_eq, Option.some.injEq, forall_eq']
    exact eq_comm

/-- The verifier for `PartialMCSP`: the certificate must describe a circuit on `n` inputs with at
most `MCSP.budget n s` gates (`readCertificate`) whose output agrees with the partial truth table on
all defined entries among the `2 ^ n` inputs. -/
def verifier (p : Instance × List Bool) : Bool :=
  MCSP.checkCertificate
    (fun y out => (tableEntry (List.ofFn p.1.table) y).getD out == out)
    p.1.arity (MCSP.budget p.1.arity p.1.threshold) p.2

/-! ### Correctness -/

private theorem certLength_le_enc_of_encT (encT : ℕ ↪ List Bool) (x : Instance) :
    certLength x.arity (MCSP.budget x.arity x.threshold) ≤
      MCSP.certPolynomial.eval (encPair (encList (encOption encBool)) encT (toRaw x)).length := by
  set L := (encPair (encList (encOption encBool)) encT (toRaw x)).length
  have hT := two_pow_le_length_enc_of_encT encT x
  have hn : x.arity ≤ L := (Nat.lt_two_pow_self).le.trans hT
  have hS : MCSP.budget x.arity x.threshold ≤ L * (2 * L + 3) + 1 :=
    (Nat.min_le_right _ _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul hT (by omega)) 1)
  simp only [MCSP.certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

private theorem certLength_le_enc (x : Instance) :
    certLength x.arity (MCSP.budget x.arity x.threshold) ≤
      MCSP.certPolynomial.eval (enc x).length :=
  certLength_le_enc_of_encT encUnary x

private theorem certLength_le_encBinary (x : Instance) :
    certLength x.arity (MCSP.budget x.arity x.threshold) ≤
      MCSP.certPolynomial.eval (encBinary x).length :=
  certLength_le_enc_of_encT encNat x

/-- **Soundness of the verifier.** An instance with an accepted certificate, of any length, is in
`PartialMCSP`. -/
theorem mem_of_verifier_eq_true {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    x ∈ PartialMCSP := by
  obtain ⟨c, hcS, hall⟩ := MCSP.exists_circuit_of_checkCertificate hw
  refine mem_iff_exists_circuit.2 ⟨c, hcS.trans (Nat.min_le_left _ _), fun y b hy => ?_⟩
  have hagree := hall y
  rw [tableEntry_ofFn x y, hy, getD_beq_self_eq_true_iff] at hagree
  exact hagree b rfl

/-- **Completeness of the verifier.** Every instance in `PartialMCSP` has a certificate of length
`certLength x.arity (MCSP.budget x.arity x.threshold)` that is accepted whatever bits follow it. -/
theorem exists_verifier_append {x : Instance} (hx : x ∈ PartialMCSP) :
    ∃ u : List Bool, u.length = certLength x.arity (MCSP.budget x.arity x.threshold) ∧
      ∀ extra, verifier (x, u ++ extra) = true := by
  set S := MCSP.budget x.arity x.threshold
  have hcomp_bound :
      complexityOn interpretation x.definedInputs (single x.completion) ≤
        2 ^ x.arity * (2 * x.arity + 3) + 1 :=
    complexityOn_le_complexity.trans (complexity_le_two_pow_mul_add_one _)
  have hS : complexityOn interpretation x.definedInputs (single x.completion) ≤ S :=
    le_min hx hcomp_bound
  obtain ⟨c, hc, hsize⟩ := complexityOn_le_iff.mp hS
  have hagree : x.AgreesWith fun y => c.eval interpretation y 0 :=
    (Instance.computesOn_definedInputs_iff.mp hc)
  obtain ⟨u, hu, hV⟩ := MCSP.exists_checkCertificate_append
    (accept := fun y out => (tableEntry (List.ofFn x.table) y).getD out == out)
    hsize fun y => by
    rw [tableEntry_ofFn, getD_beq_self_eq_true_iff]
    intro b hb
    exact hagree y b hb
  exact ⟨u, hu, hV⟩

/-- `PartialMCSP.verifier` verifies `PartialMCSP` under `enc` (unary threshold). -/
theorem isVerifier : IsVerifier enc MCSP.certPolynomial verifier PartialMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_enc x, fun k => hV _⟩

/-- `PartialMCSP.verifier` verifies `PartialMCSP` under `encBinary` (binary threshold). -/
theorem isVerifier_encBinary : IsVerifier encBinary MCSP.certPolynomial verifier PartialMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_encBinary x, fun k => hV _⟩

/-! ### Polynomial time -/

open ComputableTidilyInPolyTime

/-- The verifier on a raw partial truth-table list, a threshold, and a certificate, with the number
of inputs read from the length of the table. -/
def tableVerifier (r : (List (Option Bool) × ℕ) × List Bool) : Bool :=
  let n := Nat.log 2 r.1.1.length
  MCSP.checkCertificate
    (fun y out => (tableEntry r.1.1 y).getD out == out)
    n (min r.1.2 (r.1.1.length * (2 * n + 3) + 1)) r.2

theorem verifier_eq_tableVerifier (p : Instance × List Bool) :
    verifier p = tableVerifier ((List.ofFn p.1.table, p.1.threshold), p.2) := by
  simp only [tableVerifier, verifier, List.length_ofFn, Nat.log_pow Nat.one_lt_two]
  rfl

/-- Looking up an entry in a partial truth table is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_tableEntry :
    ComputableInPolyTime
      (fun p : List (Option Bool) × List Bool => tableEntry p.1 p.2)
      (encPair (encList (encOption encBool)) encBits) (encOption encBool) := by
  unfold tableEntry
  exact .of_tidy
    ((listGetD (encA := encOption encBool) (encL := encList (encOption encBool)) none).comp
      ((fst _ _).prod (bitsBoundedBinaryValueWithInput
        ((length_list (encOption encBool)).comp (fst _ _))
        (bitsReverse.comp (snd _ _)))))

/-- The verifier on raw data is computable in polynomial time. -/
theorem computableInPolyTime_tableVerifier :
    ComputableInPolyTime tableVerifier
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) encBool := by
  let encT := encList (encOption encBool)
  let encIn := encPair (encPair encT encNat) encBits
  have hT : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool => r.1.1)
      encIn encT := (fst encT encNat).comp (fst _ _)
  have hlen : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool =>
      r.1.1.length) encIn encUnary :=
    (length_list (encOption encBool)).comp hT
  have hm : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool =>
      Nat.log 2 r.1.1.length) encIn encUnary :=
    unary_log_two.comp hlen
  have hcap : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool =>
      r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1) encIn encUnary := by
    fun_prop
  have hs : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool => r.1.2)
      encIn encNat := (snd encT encNat).comp (fst _ _)
  have hS := MCSP.computableInPolyTime_min_cap (.of_tidy hs) (.of_tidy hcap)
  have hw : ComputableTidilyInPolyTime (fun r : (List (Option Bool) × ℕ) × List Bool => r.2)
      encIn encBits := snd _ _
  have hsize : PolynomiallyBounded (fun L => L * (2 * L + 1)) := by fun_prop
  have hbudget (r : (List (Option Bool) × ℕ) × List Bool) :
      2 ^ Nat.log 2 r.1.1.length * (2 * Nat.log 2 r.1.1.length + 1) ≤
        (encIn r).length * (2 * (encIn r).length + 1) := by
    set T := r.1.1.length
    have hpow : 2 ^ Nat.log 2 T ≤ T + 1 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · simp [h]
      · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ T)
    have hlog : 2 * Nat.log 2 T + 1 ≤ 2 * T + 1 := by
      have := Nat.log_le_self 2 T
      omega
    have h1 := SizedListEncoding.length_le (encA := encOption encBool) (encL := encT) r.1.1
    have hT_enc : 2 * T + 1 ≤ (encIn r).length := by
      simp only [encIn, length_encPair]
      omega
    calc 2 ^ Nat.log 2 T * (2 * Nat.log 2 T + 1) ≤ (T + 1) * (2 * T + 1) :=
          Nat.mul_le_mul hpow hlog
      _ ≤ (encIn r).length * (2 * (encIn r).length + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
  have htable : ComputableTidilyInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool => p.1.1.1.1)
      (encPair (encPair encIn encBits) encBool) encT :=
    (fst _ _).fst'.fst'.fst'
  have hy : ComputableTidilyInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool => p.1.2)
      (encPair (encPair encIn encBits) encBool) encBits :=
    (fst _ _).snd'
  have hout : ComputableTidilyInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool => p.2)
      (encPair (encPair encIn encBits) encBool) encBool :=
    snd _ _
  have hentry : ComputableTidilyInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool =>
        tableEntry p.1.1.1.1 p.1.2)
      (encPair (encPair encIn encBits) encBool) (encOption encBool) :=
    computableInPolyTime_tableEntry.tidy.comp (htable.prod hy)
  have hval : ComputableTidilyInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool =>
        (tableEntry p.1.1.1.1 p.1.2).getD p.2)
      (encPair (encPair encIn encBits) encBool) encBool :=
    optionGetDWithInput hentry hout
  have haccept : ComputableInPolyTime
      (fun p : (((List (Option Bool) × ℕ) × List Bool) × List Bool) × Bool =>
        (tableEntry p.1.1.1.1 p.1.2).getD p.2 == p.2)
      (encPair (encPair encIn encBits) encBool) encBool :=
    .of_tidy (ComputableTidilyInPolyTime.beq hval hout)
  exact MCSP.computableInPolyTime_checkCertificate
    (γ := (List (Option Bool) × ℕ) × List Bool) (encIn := encIn)
    (accept := fun r y out => (tableEntry r.1.1 y).getD out == out)
    (m := fun r => Nat.log 2 r.1.1.length)
    (S := fun r => min r.1.2 (r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1))
    (w := fun r => r.2)
    (.of_tidy hm) hS (.of_tidy hw) hsize hbudget haccept

/-- The `PartialMCSP` verifier is computable in polynomial time under `encBinary`. -/
theorem computableInPolyTime_verifier_encBinary :
    ComputableInPolyTime verifier (encPair encBinary encBits) encBool := by
  have hraw : ComputableInPolyTime
      (fun p : Instance × List Bool => ((List.ofFn p.1.table, p.1.threshold), p.2))
      (encPair encBinary encBits)
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) :=
    .of_eq fun _ => rfl
  rw [funext verifier_eq_tableVerifier]
  exact computableInPolyTime_tableVerifier.comp hraw

/-- The `PartialMCSP` verifier is computable in polynomial time under `enc` (unary threshold). -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair enc encBits) encBool := by
  have hraw : ComputableInPolyTime
      (fun p : Instance × List Bool => ((List.ofFn p.1.table, p.1.threshold), p.2))
      (encPair enc encBits)
      (encPair (encPair (encList (encOption encBool)) encUnary) encBits) :=
    .of_eq fun _ => rfl
  have hconv : ComputableInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool => ((r.1.1, r.1.2), r.2))
      (encPair (encPair (encList (encOption encBool)) encUnary) encBits)
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) :=
    .of_tidy (((fst _ _).fst'.prod (unary_to_binary.comp (fst _ _).snd')).prod (snd _ _))
  rw [funext verifier_eq_tableVerifier]
  exact (computableInPolyTime_tableVerifier.comp hconv).comp hraw

/-- **`PartialMCSP` is in `NP`** under `PartialMCSP.enc` (framed `Option Bool` truth table and
unary threshold) [Hirahara2022, ECCC TR22-119, Definition 8.4, p. 30]. -/
theorem mem_NP : PartialMCSP ∈ NP enc :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier, isVerifier⟩

/-- **`PartialMCSP` is in `NP`** under `PartialMCSP.encBinary` (framed `Option Bool` truth table
and binary threshold) [Ilango2020FOCS, Section II.B; ECCC TR20-183, Section 2.2]. -/
theorem mem_NP_encBinary : PartialMCSP ∈ NP encBinary :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier_encBinary, isVerifier_encBinary⟩

/-! ### Polynomial-time reduction from `MCSP` to `PartialMCSP` -/

private theorem foldl_cons_some (l : List Bool) (acc : List (Option Bool)) :
    l.foldl (fun acc b => some b :: acc) acc = l.reverse.map some ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    simp [ih, List.map_append]

private theorem computableTidilyInPolyTime_bitsMapSome :
    ComputableTidilyInPolyTime (List.map some) encBits (encList (encOption encBool)) := by
  have hfold := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (encB := encList (encOption encBool))
    (step := fun acc b => some b :: acc) (init := fun _ => [])
    bitsReverse (const [])
    (show ComputableTidilyInPolyTime
      (fun p : List (Option Bool) × Bool => some p.2 :: p.1)
      (encPair (encList (encOption encBool)) encBool) (encList (encOption encBool)) by fun_prop)
    (growth := 5) (fun acc b => by
      rw [encList_cons, List.length_append]
      have hb : (frame (encOption encBool (some b))).length = 5 := by cases b <;> rfl
      omega)
  refine hfold.of_enc_eq fun l => ?_
  rw [foldl_cons_some, List.reverse_reverse, List.append_nil]

/-- Embedding a total `MCSP.Instance` as a `PartialMCSP.Instance` with no `*` entries is computable
in polynomial time. -/
theorem computableInPolyTime_ofTotal_encBinary :
    ComputableInPolyTime Instance.ofTotal MCSP.encInstance encBinary := by
  have hraw : ComputableTidilyInPolyTime
      (fun x : MCSP.Instance => (List.ofFn x.table, x.threshold))
      MCSP.encInstance (encPair encBits encNat) :=
    .of_eq fun _ => rfl
  have hmap : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ => (p.1.map some, p.2))
      (encPair encBits encNat) (encPair (encList (encOption encBool)) encNat) :=
    (computableTidilyInPolyTime_bitsMapSome.comp (fst encBits encNat)).prod (snd encBits encNat)
  have hout : ComputableTidilyInPolyTime Instance.ofTotal MCSP.encInstance encBinary := by
    refine (hmap.comp hraw).of_enc_eq fun x => ?_
    have hofFn : (List.ofFn x.table).map some = List.ofFn (Instance.ofTotal x).table := by
      ext i b
      simp [Instance.ofTotal]
    simp [encBinary_apply, hofFn, Instance.ofTotal]
  exact .of_tidy hout

/-- `MCSP` reduces to `PartialMCSP` in polynomial time via `Instance.ofTotal`. -/
theorem polyTimeReducible_MCSP_PartialMCSP_encBinary :
    PolyTimeReducible MCSP.encInstance encBinary MCSP PartialMCSP :=
  ⟨Instance.ofTotal, computableInPolyTime_ofTotal_encBinary, fun x => (ofTotal_mem_iff x).symm⟩

end Cslib.PartialMCSP
