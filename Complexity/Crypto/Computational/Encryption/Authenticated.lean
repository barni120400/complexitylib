/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.MAC
public import Complexity.Crypto.Game.UntilBad
public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Hybrid
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Authenticated Encryption, Chosen-Ciphertext Security, and Encrypt-then-MAC

This module formalizes symmetric authenticated encryption, adaptive chosen-ciphertext security
(`INDCCA`), and the generic **Encrypt-then-MAC** composition following
[Boneh and Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
Chapter 5 (Section 5.3) and Chapter 9 (Sections 9.1, 9.2.2–9.2.3, and 9.4.1):

1. **Symmetric ciphers and adaptive CPA security (`SymmetricCipher`, `cpaGame`, `INDCPA`)**
   ([BonehShoup2023], Section 5.3, Attack Game 5.2 and Definition 5.2, printed pp. 181–182):
   a uniform symmetric cipher on `n`-bit messages at security parameter `n` consists of strict PPT
   key generation `keyGen`, strict PPT encryption `encrypt`, and deterministic polynomial-time
   decryption `decrypt` returning `Option (List Bool)` (encoded via `encOption encBits`). In
   `cpaGame`, an adaptive `OracleDistinguisher` submits left-or-right pairs `(m0, m1)` of `n`-bit
   messages and receives `encrypt n k (if bit then m1 else m0)`.
2. **Ciphertext integrity and authenticated encryption (`ciGame`, `CiphertextIntegrity`,
   `AuthenticatedEncryption`)** ([BonehShoup2023], Section 9.1, Attack Game 9.1 and
   Definitions 9.1–9.2, printed pp. 358–359): in `ciGame`, an adaptive `CIAdversary` queries an
   encryption oracle on `n`-bit messages (logging returned ciphertexts in `queriedCiphertexts`) and
   wins by outputting a candidate ciphertext `ct` such that `!queriedCiphertexts.contains ct` and
   `(decrypt n k ct).isSome`. A cipher provides `AuthenticatedEncryption` when it satisfies both
   `INDCPA` and `CiphertextIntegrity`.
3. **Adaptive chosen-ciphertext security and AE $\Rightarrow$ CCA (`ccaGame`, `INDCCA`,
   `ccaToCPAAdversary`, `ccaToCIAdversary`, `ccaToCIHiddenBitAdversary`,
   `advantage_ccaGame_le`, `advantage_ccaGame_le_two_mul`, `AuthenticatedEncryption.indcca`)**
   ([BonehShoup2023], Sections 9.2.2–9.2.3, Attack Game 9.2, Definition 9.5, and Theorem 9.1,
   printed pp. 362–365): in `ccaGame`, a two-channel `CCAAdversary` (`Operation = Bool`) may
   interleave left-or-right encryption queries (`false`, recording challenge ciphertexts) with
   decryption queries (`true`, rejecting recorded challenge ciphertexts and returning
   `encOption encBits (decrypt n k ct)` on all other ciphertexts). Using the difference lemma
   (`OracleComp.IdenticalUntilBad.advantage_le`, [BonehShoup2023], Theorem 4.7) between `ccaGame`
   and `ccaRejectGame` (where all decryption queries are rejected), we prove that every
   `AuthenticatedEncryption` cipher is `INDCCA`-secure.
4. **Encrypt-then-MAC (`encryptThenMAC`, `etmToMACForger`, `etmToCPAAdversary`,
   `succProbability_ciGame_encryptThenMAC_le`, `succProbability_ciGame_encryptThenMAC_eq`,
   `advantage_cpaGame_encryptThenMAC_eq`, `ciphertextIntegrity_encryptThenMAC`,
   `indcpa_encryptThenMAC`, `authenticatedEncryption_encryptThenMAC`, `indcca_encryptThenMAC`)**
   ([BonehShoup2023], Section 9.4.1, Theorem 9.2, printed pp. 367–368): combining an `INDCPA`
   symmetric cipher `E` with a strongly unforgeable `MACScheme` `M` (`MACScheme.SUFCMA`, #723) over
   independent keys yields an `AuthenticatedEncryption` (and hence `INDCCA`-secure) cipher, with
   certified `IsOraclePPT` reductions and exact quantitative bounds. Combining with
   `PseudorandomFunction.sufCma_prfMAC` (`prfMAC`) yields authenticated and CCA-secure encryption
   from any CPA-secure cipher and uniform PRF.

## Specializations relative to Boneh–Shoup Chapter 9

* **Fixed `n`-bit plaintext domain at security parameter `n`**: encryption queries take `n`-bit
  messages (`msg.length = n` in `ciGame`, `m0.length = n ∧ m1.length = n` in `cpaGame` and
  `ccaGame`). Malformed encryption queries return `[]` without invoking `encrypt` or recording a
  challenge ciphertext.
* **Inner ciphertext length in `encryptThenMAC`**: because `MACScheme` in
  `Complexity/Crypto/Computational/MAC.lean` authenticates `n`-bit messages at security parameter
  `n`, `encryptThenMAC E M` takes an inner cipher `E` whose supported ciphertexts on `n`-bit
  plaintexts at parameter `n` have length `n` (`hctLen`), frames `(c, tag)` via
  `encPair encBits encBits`, and checks canonical framing
  `encPair encBits encBits (unframe ct, dropFrame ct) == ct && (unframe ct).length == n &&
  M.verify km (unframe ct) (dropFrame ct)` before invoking `E.decrypt n ke (unframe ct)`.
* **Total-query budget in Theorem 9.1**: `ccaToCIAdversary` samples a query index uniformly from
  `{0, ..., dyadicSize (Q n) - 1}` via `ProbComp.sampleDyadicIndex (Q n)` (where
  `Q n < dyadicSize (Q n) ≤ 2 * Q n + 2`) and decrements the countdown on every external oracle
  call `Sum.inr` of `(adversary n []).IsQueryBounded (Q n)`, yielding factor `dyadicSize (Q n)`
  (and `2 * dyadicSize (Q n)` for `ccaToCIHiddenBitAdversary`).

## Main definitions

* `Cslib.Crypto.CIAdversary`, `Cslib.Crypto.CCAAdversary`: adaptive ciphertext-integrity and
  chosen-ciphertext adversaries.
* `Cslib.Crypto.SymmetricCipher`: uniform symmetric cipher on `n`-bit messages.
* `Cslib.Crypto.SymmetricCipher.cpaGame`, `INDCPA`: adaptive symmetric CPA game and security
  predicate ([BonehShoup2023], Attack Game 5.2 / Definition 5.2).
* `Cslib.Crypto.SymmetricCipher.ciGame`, `CiphertextIntegrity`, `AuthenticatedEncryption`:
  ciphertext-integrity game, CI predicate, and AE predicate ([BonehShoup2023], Attack Game 9.1 /
  Definitions 9.1–9.2).
* `Cslib.Crypto.SymmetricCipher.ccaGame`, `ccaRejectGame`, `INDCCA`: adaptive CCA game,
  all-reject hybrid game, and CCA security predicate ([BonehShoup2023], Attack Game 9.2 /
  Definition 9.5).
* `Cslib.Crypto.SymmetricCipher.ccaToCPAAdversary`, `ccaToCIAdversary`,
  `ccaToCIHiddenBitAdversary`: Theorem 9.1 reductions from CCA to CPA and CI.
* `Cslib.Crypto.encryptThenMAC`, `etmToMACForger`, `etmToCPAAdversary`: Encrypt-then-MAC
  construction and Theorem 9.2 reductions to `MACScheme.sufCmaGame` and `SymmetricCipher.cpaGame`.

## Main results

* `Cslib.Crypto.SymmetricCipher.isPPTOn_cpaGame`, `isPPT_cpaGame`, `isPPTOn_ciGame`,
  `isPPT_ciGame`, `isPPTOn_ccaGame`, `isPPT_ccaGame`: strict PPT certificates for the CPA, CI, and
  CCA experiments.
* `Cslib.Crypto.SymmetricCipher.isOraclePPT_ccaToCPAAdversary`,
  `isOraclePPT_ccaToCIAdversary`, `isOraclePPT_ccaToCIHiddenBitAdversary`: `IsOraclePPT`
  certificates for the Theorem 9.1 reductions.
* `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le`,
  `Cslib.Crypto.SymmetricCipher.advantage_ccaGame_le_two_mul`,
  `Cslib.Crypto.SymmetricCipher.AuthenticatedEncryption.indcca`: quantitative and asymptotic
  AE $\Rightarrow$ CCA security ([BonehShoup2023], Theorem 9.1).
* `Cslib.Crypto.isOraclePPT_etmToMACForger`, `Cslib.Crypto.isOraclePPT_etmToCPAAdversary`,
  `Cslib.Crypto.succProbability_ciGame_encryptThenMAC_le`,
  `Cslib.Crypto.succProbability_ciGame_encryptThenMAC_eq`,
  `Cslib.Crypto.advantage_cpaGame_encryptThenMAC_eq`,
  `Cslib.Crypto.ciphertextIntegrity_encryptThenMAC`,
  `Cslib.Crypto.indcpa_encryptThenMAC`,
  `Cslib.Crypto.authenticatedEncryption_encryptThenMAC`,
  `Cslib.Crypto.indcca_encryptThenMAC`,
  `Cslib.Crypto.authenticatedEncryption_encryptThenMAC_prfMAC`,
  `Cslib.Crypto.indcca_encryptThenMAC_prfMAC`: Encrypt-then-MAC security ([BonehShoup2023],
  Theorem 9.2).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.3 (pp. 181–182) and Chapter 9, Sections 9.1, 9.2, 9.4.1
  (pp. 357–368).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- An adaptive ciphertext-integrity adversary receives the unary security parameter and an
auxiliary word, queries an encryption oracle on chosen messages, and outputs a candidate
ciphertext. -/
abbrev CIAdversary := ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- An adaptive chosen-ciphertext distinguisher receives the unary security parameter and an
auxiliary word, queries a left-or-right encryption oracle (`false`) and a decryption oracle
(`true`), and outputs a distinguishing bit. -/
abbrev CCAAdversary := ℕ → List Bool → WordOracleComp Bool Bool

/-- A uniform symmetric cipher on `n`-bit messages at security parameter `n`, with strict
probabilistic polynomial-time key generation and encryption, deterministic polynomial-time
decryption (returning `Option (List Bool)`), and perfect decryption completeness on supported keys,
`n`-bit messages, and ciphertexts ([BonehShoup2023], Sections 5.3 and 9.1). -/
structure SymmetricCipher where
  /-- Sample a symmetric secret key `k` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Probabilistically encrypt a message `msg` under secret key `k` at security parameter `n`. -/
  encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically decrypt a candidate ciphertext `ct` under secret key `k` at parameter `n`,
  returning `none` on rejection and `some msg` on acceptance. -/
  decrypt : ℕ → List Bool → List Bool → Option (List Bool)
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Encryption is uniformly strict PPT in `(n, k, msg)`. -/
  encrypt_ppt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
    (fun p => encrypt p.1 p.2.1 p.2.2)
  /-- Decryption is computable in plain polynomial time on `(n, k, ct)`. -/
  decrypt_polyTime : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) (encOption encBits)
  /-- Every ciphertext produced by `encrypt` on an `n`-bit message under a supported secret key at
  security parameter `n` decrypts to `some msg`. -/
  decrypt_encrypt : ∀ n k, k ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ ct, ct ∈ (ProbComp.eval (encrypt n k msg)).support →
    decrypt n k ct = some msg

namespace SymmetricCipher

attribute [program_certificate] keyGen_ppt encrypt_ppt decrypt_polyTime

/-! ### Adaptive Chosen-Plaintext Security (`cpaGame`, `INDCPA`) -/

/-- Stateful left-or-right CPA encryption oracle ([BonehShoup2023], Section 5.3, Attack Game 5.2):
decode the request into `m0 = unframe request.2` and `m1 = dropFrame request.2`; if both have
length `n`, encrypt `if bit then m1 else m0` under `k`, and otherwise return `[]`. -/
noncomputable def cpaEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Unit × List Bool) : StateT Unit ProbComp (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let ct ← E.encrypt n k (if bit then m1 else m0)
      return (ct, ())
    else
      return ([], ())

/-- The adaptive symmetric IND-CPA experiment ([BonehShoup2023], Section 5.3, Attack Game 5.2):
sample `k ← E.keyGen n` and run `adversary n []` against `E.cpaEncryptionOracle n k bit`. -/
noncomputable def cpaGame (E : SymmetricCipher) (adversary : OracleDistinguisher)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.cpaEncryptionOracle n k bit)) (adversary n [])).run ()
  return out.1

/-- Running an oracle-PPT distinguisher against `cpaEncryptionOracle` is uniformly strict PPT in
`(n, k)` for each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_cpaEncryptionOracle (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encFinite Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.cpaEncryptionOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run ()) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinite Unit) encBits) (encFinite Unit))
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hyes : IsPPTOn EIn (encPair encBits (encFinite Unit))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × Unit) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, ())) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.const ())).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encFinite Unit))
      (fun _ => pure ([], ())) :=
    (ComputableTidilyInPolyTime.const ([], ())).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encFinite Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        E.cpaEncryptionOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold cpaEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ())
    (resources := fun caller _ =>
      c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d + 1)
    (by fun_prop) hhandler (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request _ _ result hresult
  unfold cpaEncryptionOracle at hresult
  by_cases hlenEq : ((unframe request.2).length == caller.1 &&
      (dropFrame request.2).length == caller.1) = true
  · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
    have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
      cases bit <;> simp [hlenEq]
    have hctLen := hlen (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2)
      ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmbLen] at hctLen
    have hbound : ct.length ≤ c * (3 * caller.1 + 2 * caller.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    exact ⟨trivial, by lia, by lia⟩
  · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- The symmetric CPA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.cpaGame adversary bit) := by
  have hrun := E.isPPTOn_run_cpaEncryptionOracle hadversary bit
  unfold cpaGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The symmetric CPA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_cpaGame (E : SymmetricCipher) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.cpaGame adversary bit n) :=
  ((E.isPPTOn_cpaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-plaintext security (`INDCPA`) for a symmetric cipher ([BonehShoup2023],
Section 5.3, Attack Game 5.2 and Definition 5.2): every uniform strict `IsOraclePPT encBool`
distinguisher has negligible advantage between `E.cpaGame adversary false` and
`E.cpaGame adversary true`. -/
def INDCPA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.cpaGame adversary false n))
    (fun adversary n => ProbComp.eval (E.cpaGame adversary true n))
    (IsOraclePPT encBool)

/-! ### Ciphertext Integrity and Authenticated Encryption (`ciGame`, `CiphertextIntegrity`,
`AuthenticatedEncryption`) -/

/-- Stateful encryption oracle for the ciphertext-integrity game ([BonehShoup2023], Section 9.1,
Attack Game 9.1): if `request.2.length == n`, encrypt `request.2` under `k`, prepend the resulting
ciphertext to `queriedCiphertexts`, and return it; otherwise return `[]` without modifying the
ciphertext log. -/
noncomputable def ciEncryptionOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.2.length == n then do
      let ct ← E.encrypt n k request.2
      return (ct, ct :: queriedCiphertexts)
    else
      return ([], queriedCiphertexts)

/-- The ciphertext-integrity experiment ([BonehShoup2023], Section 9.1, Attack Game 9.1):
sample `k ← E.keyGen n`, run `adversary n []` with oracle access to `E.ciEncryptionOracle n k`, and
accept when the adversary outputs a candidate ciphertext `ct` that was never returned by the
encryption oracle (`!out.2.contains out.1`) and decrypts without rejection
(`(E.decrypt n k out.1).isSome`). -/
noncomputable def ciGame (E : SymmetricCipher) (adversary : CIAdversary) (n : ℕ) :
    ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ciEncryptionOracle n k)) (adversary n [])).run []
  return !out.2.contains out.1 && (E.decrypt n k out.1).isSome

/-- Running an oracle-PPT CI adversary against `ciEncryptionOracle` is uniformly strict PPT in
`(n, k)`. -/
@[program_certificate]
theorem isPPTOn_run_ciEncryptionOracle (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn (encPair encUnary encBits) (encPair encBits (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ciEncryptionOracle caller.1 caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := E.encrypt_ppt.length_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinite Unit) encBits) (encList encBits))
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        p.2.1.2.length == p.1.1)
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hyes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 p.2.1.2
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Unit × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hno : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        E.ciEncryptionOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold ciEncryptionOracle
    exact IsPPTOn.cond hcond hyes hno
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ d) + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold ciEncryptionOracle at hresult
  split_ifs at hresult with hlenEq
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨ct, hct, rfl⟩ := hresult
    have hctLen := hlen (caller.1, caller.2, request.2) ct hct
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hctLen
    have hbound : ct.length ≤ c * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ d :=
      hctLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d))
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- The ciphertext-integrity experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPTOn encUnary encBool (E.ciGame adversary) := by
  have hrun := E.isPPTOn_run_ciEncryptionOracle hadversary
  let EOut := encPair (encPair encUnary encBits) (encPair encBits (encList encBits))
  have hcontains : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        pair.2.2.contains pair.2.1)
      EOut encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.2)
        EOut (encList encBits) := by dsimp only [EOut]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) => pair.2.1)
        EOut encBits := by dsimp only [EOut]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (pair.1.1, pair.1.2, pair.2.1))
      EOut (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EOut]; fun_prop
  have hdec : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool :=
    (E.decrypt_polyTime.tidy.comp hdecArg).optionIsSome
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × (List Bool × List (List Bool)) =>
        !pair.2.2.contains pair.2.1 && (E.decrypt pair.1.1 pair.1.2 pair.2.1).isSome)
      EOut encBool := by
    dsimp only [EOut]; polytime
  unfold ciGame
  exact E.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The ciphertext-integrity experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_ciGame (E : SymmetricCipher) {adversary : CIAdversary}
    (hadversary : IsOraclePPT encBits adversary) :
    IsPPT encBool (fun n _ => E.ciGame adversary n) :=
  ((E.isPPTOn_ciGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Ciphertext integrity (`CiphertextIntegrity`, or CI) for a symmetric cipher
([BonehShoup2023], Section 9.1, Attack Game 9.1 and Definition 9.1): every uniform strict
`IsOraclePPT encBits` adversary has negligible probability of outputting a fresh valid
ciphertext. -/
def CiphertextIntegrity (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ciGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- Ciphertext integrity gives negligible winning probability in `ciGame` for every oracle-PPT CI
adversary. -/
theorem CiphertextIntegrity.negligible {E : SymmetricCipher} (h : E.CiphertextIntegrity)
    (adversary : CIAdversary) (hadversary : IsOraclePPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish `CiphertextIntegrity` by bounding every oracle-PPT CI adversary's winning
probability. -/
theorem CiphertextIntegrity.of_negligible {E : SymmetricCipher}
    (h : ∀ adversary, IsOraclePPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (E.ciGame adversary n)))) :
    E.CiphertextIntegrity := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Authenticated encryption (`AuthenticatedEncryption`, or AE-security) for a symmetric cipher
([BonehShoup2023], Section 9.1, Definition 9.2): the cipher satisfies both `INDCPA` and
`CiphertextIntegrity`. -/
def AuthenticatedEncryption (E : SymmetricCipher) : Prop :=
  E.INDCPA ∧ E.CiphertextIntegrity

/-! ### Adaptive Chosen-Ciphertext Security (`ccaGame`, `ccaRejectGame`, `INDCCA`) -/

/-- Stateful two-channel oracle for the adaptive chosen-ciphertext experiment
([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
* On an encryption query `(false, req)`: decode `m0 = unframe req` and `m1 = dropFrame req`; if
  both have length `n`, encrypt `if bit then m1 else m0` under `k`, prepend the resulting
  ciphertext `ct` to `queriedCiphertexts`, and return `ct`; otherwise return `[]`.
* On a decryption query `(true, ct)`: if `queriedCiphertexts.contains ct` is `true`, return `[]`
  (prohibited challenge ciphertext); otherwise return `encOption encBits (E.decrypt n k ct)`. -/
noncomputable def ccaOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      if queriedCiphertexts.contains request.2 then
        return ([], queriedCiphertexts)
      else
        return (encOption encBits (E.decrypt n k request.2), queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The adaptive chosen-ciphertext experiment ([BonehShoup2023], Section 9.2.2, Attack Game 9.2):
sample `k ← E.keyGen n` and run `adversary n []` against `E.ccaOracle n k bit`. -/
noncomputable def ccaGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaOracle n k bit)) (adversary n [])).run []
  return out.1

/-- Running an oracle-PPT CCA adversary against `ccaOracle` is uniformly strict PPT in `(n, k)` for
each challenge bit `bit`. -/
@[program_certificate]
theorem isPPTOn_run_ccaOracle (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary encBits) (encPair encBool (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (E.ccaOracle caller.1 caller.2 bit)) (adversary caller.1 [])).run []) := by
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cd, dd, hlenDec⟩ := E.decrypt_polyTime.tidy.polyBounded_length.exists_le
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encFinite Bool) encBits) (encList encBits))
  have hop : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.1)
      EIn encBool :=
    (ComputableTidilyInPolyTime.of_finite id).comp (by dsimp only [EIn]; fun_prop)
  have hcontains : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        p.2.2.contains p.2.1.2)
      EIn encBool := by
    have hlist : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.2)
        EIn (encList encBits) := by dsimp only [EIn]; fun_prop
    have helem : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => p.2.1.2)
        EIn encBits := by dsimp only [EIn]; fun_prop
    classical
    convert ComputableTidilyInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn]; fun_prop
  have hdecWord : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2))
      EIn encBits :=
    (ComputableTidilyInPolyTime.encode (encOption encBits)).comp
      (E.decrypt_polyTime.tidy.comp hdecArg)
  have hnoReply : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by dsimp only [EIn]; fun_prop)).isPPTOn
  have hdecBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if p.2.2.contains p.2.1.2 then
          pure ([], p.2.2)
        else
          pure (encOption encBits (E.decrypt p.1.1 p.1.2 p.2.1.2), p.2.2)) :=
    IsPPTOn.cond hcontains hnoReply
      ((ComputableTidilyInPolyTime.prod hdecWord (by dsimp only [EIn]; fun_prop)).isPPTOn)
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn]; fun_prop)
  have hencCond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hencArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        (p.1.1, p.1.2, if bit then dropFrame p.2.1.2 else unframe p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) :=
    ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop)
      (ComputableTidilyInPolyTime.prod (by dsimp only [EIn]; fun_prop) hmsg)
  have hencYes : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) => do
        let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
        return (ct, ct :: p.2.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).bind_with
      ((by dsimp only [EIn]; polytime : ComputableTidilyInPolyTime
        (fun q : ((ℕ × List Bool) × ((Bool × List Bool) × List (List Bool))) × List Bool =>
          (q.2, q.2 :: q.1.2.2))
        (encPair EIn encBits) (encPair encBits (encList encBits))).isPPTOn)
  have hencBranch : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        if ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1) then do
          let ct ← E.encrypt p.1.1 p.1.2 (if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
          return (ct, ct :: p.2.2)
        else
          pure ([], p.2.2)) :=
    IsPPTOn.cond hencCond hencYes hnoReply
  have hhandler : IsPPTOn EIn (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × List (List Bool)) =>
        E.ccaOracle pair.1.1 pair.1.2 bit pair.2.1 pair.2.2) := by
    unfold ccaOracle
    exact IsPPTOn.cond hop hdecBranch hencBranch
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      2 * (ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de) +
      cd * (2 * caller.1 + 2 * caller.2.length + query.length + 4) ^ dd + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by polytime)
  intro caller request queried _ result hresult
  unfold ccaOracle at hresult
  cases hreq : request.1
  · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
    by_cases hlenEq : ((unframe request.2).length == caller.1 &&
        (dropFrame request.2).length == caller.1) = true
    · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
      obtain ⟨ct, hct, rfl⟩ := hresult
      simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
      have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = caller.1 := by
        cases bit <;> simp [hlenEq]
      have hctLen := hlenEnc
        (caller.1, caller.2, if bit then dropFrame request.2 else unframe request.2) ct hct
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
        hmbLen] at hctLen
      have hbound : ct.length ≤ ce * (3 * caller.1 + 2 * caller.2.length + 4) ^ de :=
        hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      refine ⟨trivial, by lia, ?_⟩
      simp only [encList_cons, List.length_append, length_frame, encBits_apply]
      lia
    · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
  · simp only [hreq, ↓reduceIte] at hresult
    split_ifs at hresult with hmem
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨trivial, by simp, by lia⟩
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      have hdecLen := hlenDec (caller.1, caller.2, request.2)
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hdecLen
      have hbound : (encOption encBits (E.decrypt caller.1 caller.2 request.2)).length ≤
          cd * (2 * caller.1 + 2 * caller.2.length + request.2.length + 4) ^ dd :=
        hdecLen.trans (Nat.mul_le_mul_left cd (Nat.pow_le_pow_left (by lia) dd))
      exact ⟨trivial, by lia, by lia⟩

/-- The adaptive CCA experiment is uniformly strict PPT in the unary security parameter. -/
@[program_certificate, fun_prop]
theorem isPPTOn_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPTOn encUnary encBool (E.ccaGame adversary bit) := by
  have hrun := E.isPPTOn_run_ccaOracle hadversary bit
  unfold ccaGame
  exact E.keyGen_ppt.bind_with (hrun.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn)

/-- The adaptive CCA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_ccaGame (E : SymmetricCipher) {adversary : CCAAdversary}
    (hadversary : IsOraclePPT encBool adversary) (bit : Bool) :
    IsPPT encBool (fun n _ => E.ccaGame adversary bit n) :=
  ((E.isPPTOn_ccaGame hadversary bit).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Adaptive chosen-ciphertext security (`INDCCA`, or CCA-security) for a symmetric cipher
([BonehShoup2023], Section 9.2.2, Attack Game 9.2 and Definition 9.5): every uniform strict
`IsOraclePPT encBool` CCA adversary has negligible advantage between `E.ccaGame adversary false`
and `E.ccaGame adversary true`. -/
def INDCCA (E : SymmetricCipher) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (E.ccaGame adversary false n))
    (fun adversary n => ProbComp.eval (E.ccaGame adversary true n))
    (IsOraclePPT encBool)

/-! ### Authenticated Encryption Implies Adaptive CCA Security (Boneh–Shoup Theorem 9.1) -/

/-- Hybrid two-channel oracle for Game 1 in the proof of [BonehShoup2023], Theorem 9.1
(Section 9.2.3, printed pp. 363–364): encryption queries `(false, req)` behave identically to
`ccaOracle`, whereas every decryption query `(true, _)` immediately returns `[]` (rejection) without
invoking `decrypt`. -/
noncomputable def ccaRejectOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool) (bit : Bool)
    (request : Bool × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queriedCiphertexts =>
    if request.1 then
      return ([], queriedCiphertexts)
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, ct :: queriedCiphertexts)
      else
        return ([], queriedCiphertexts)

/-- The all-reject hybrid CCA experiment (Game 1 in [BonehShoup2023], Section 9.2.3,
Theorem 9.1): sample `k ← E.keyGen n` and run `adversary n []` against
`E.ccaRejectOracle n k bit`. -/
noncomputable def ccaRejectGame (E : SymmetricCipher) (adversary : CCAAdversary)
    (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← E.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (E.ccaRejectOracle n k bit)) (adversary n [])).run []
  return out.1

/-- Stateful handler for `ccaToCPAAdversary` ([BonehShoup2023], Section 9.2.3, Theorem 9.1):
reject all decryption queries `(true, _)` with `[]`, and forward valid left-or-right encryption
queries `(false, req)` to the external CPA encryption oracle (truncating replies to `ctBound`). -/
noncomputable def ccaToCPAHandler (n ctBound : ℕ) (request : Bool × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.1 then
      pure ([], ())
    else
      if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
        (fun ct => (ct, ())) <$> (List.take ctBound <$> ProbOracleComp.query ((), request.2))
      else
        pure ([], ())

/-- Reduction from the all-reject hybrid `ccaRejectGame` to the adaptive CPA experiment `cpaGame`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{cpa}}$ in Theorem 9.1): run `adversary n []`
against `ccaToCPAHandler n (ctBound n)`. -/
noncomputable def ccaToCPAAdversary (ctBound : ℕ → ℕ) (adversary : CCAAdversary) :
    OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCPAHandler n (ctBound n)))
      (adversary n [])).run ()
    return out.1

/-- `ccaToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCPAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (ccaToCPAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair encBool encBits) (encFinite Unit))
  have hop : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) => p.2.1.1)
      EIn encBool := by
    dsimp only [EIn]; fun_prop
  have hencCond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1) && ((dropFrame p.2.1.2).length == p.1.1))
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hlimit : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) => ctBound p.1.1)
      EIn encUnary :=
    hctBound.tidy.comp (by dsimp only [EIn]; fun_prop)
  have hquery : IsOraclePPTOn EIn (encPair encBits (encFinite Unit))
      (fun p : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        (fun ct => (ct, ())) <$>
          (List.take (ctBound p.1.1) <$> ProbOracleComp.query ((), p.2.1.2))) :=
    (IsOraclePPTOn.query_take () (by dsimp only [EIn]; fun_prop) hlimit).map
      (ComputableTidilyInPolyTime.prod (by fun_prop) (ComputableTidilyInPolyTime.const ()))
  have hnoReply : IsOraclePPTOn EIn (encPair encBits (encFinite Unit))
      (fun _ => pure ([], ())) :=
    (ComputableTidilyInPolyTime.const ([], ())).isPPTOn.isOraclePPTOn (Operation := Unit)
  have hhandler : IsOraclePPTOn EIn (encPair encBits (encFinite Unit))
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × Unit) =>
        ccaToCPAHandler pair.1.1 (ctBound pair.1.1) pair.2.1 pair.2.2) := by
    unfold ccaToCPAHandler
    exact IsOraclePPTOn.cond hop hnoReply (IsOraclePPTOn.cond hencCond hquery hnoReply)
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1 + 1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp
      (ComputableTidilyInPolyTime.prod (hctBound.tidy.comp (by fun_prop))
        (ComputableTidilyInPolyTime.const 1))
  have hrun : IsOraclePPTOn (encPair encUnary encBits) (encPair encBool (encFinite Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCPAHandler caller.1 (ctBound caller.1)))
          (adversary caller.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ => ctBound caller.1 + 1)
      (by fun_prop) hhandler (ComputableTidilyInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request _ _ result hresult
    unfold ccaToCPAHandler at hresult
    cases hreq : request.1
    · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
      split_ifs at hresult with hlenEq
      · obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
        obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
        exact ⟨trivial, (List.length_take_le _ _).trans (by lia), by lia⟩
      · cases ProbOracleComp.eq_of_mem_support_pure hresult
        exact ⟨trivial, by simp, by lia⟩
    · simp only [hreq, ↓reduceIte] at hresult
      cases ProbOracleComp.eq_of_mem_support_pure hresult
      exact ⟨trivial, by simp, by lia⟩
  unfold ccaToCPAAdversary
  simpa only [bind_pure_comp] using (hrun.map (ComputableTidilyInPolyTime.fst _ _)).isOraclePPT

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCPAAdversary ctBound adversary` in `cpaGame` has the exact same output distribution as
`ccaRejectGame adversary` ([BonehShoup2023], Section 9.2.3, equation (9.7) in the proof of
Theorem 9.1, printed p. 365). -/
theorem eval_cpaGame_ccaToCPAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.ccaRejectGame adversary bit n) := by
  simp only [cpaGame, ccaRejectGame, ccaToCPAAdversary, ProbComp.eval_bind, ProbComp.eval_pure]
  apply PMF.bind_congr_on_support
  intro k hk
  simp only [ProbOracleComp.eval_run_interpret]
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [StateT.run_pure, OracleComp.interpret_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (fun request queried => ProbComp.eval (E.ccaRejectOracle n k bit request queried))
    (fun request state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
        ((ccaToCPAHandler n (ctBound n) request).run state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (fun _ : List (List Bool) => ((), ()))
    (fun request queried => by
      change (ProbComp.eval (E.ccaRejectOracle n k bit request queried)).map
          (fun x => (x.1, (), ())) =
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s)))
          (ccaToCPAHandler n (ctBound n) request ())).run ()).map
          (fun result => (result.1.1, result.1.2, result.2))
      cases hreq : request.1
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            Functor.map_map, OracleComp.interpret_map, StateT.run_map,
            ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
            cpaEncryptionOracle]
          dsimp only [StateT.run]
          simp only [PMF.map_bind, PMF.pure_map]
          simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
          have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
            cases bit <;> simp [hlenEq]
          apply PMF.bind_congr_on_support
          intro ct hct
          rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
            PMF.pure_map]
      · simp only [ccaRejectOracle, ccaToCPAHandler, hreq, ↓reduceIte, ProbComp.eval_pure,
          OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.pure_map])
    (adversary n []) []
  rw [← hsim]
  simp only [PMF.bind_map, Function.comp_def]

/-- Stateful handler for `ccaToCIAtIndexAdversary` and `ccaToCIAdversary`
([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$ in Theorem 9.1):
maintains `(rem, (hasCaptured, capturedCt)) : ℕ × (Bool × List Bool)`.
* Once `hasCaptured = true`, all subsequent queries return `[]` without calling the external CI
  encryption oracle.
* While `hasCaptured = false`:
  - if `rem == 0`, a decryption query `(true, ct)` captures `(0, (true, ct))` and an encryption
    query `(false, _)` captures `(0, (true, []))`, both returning `[]` without calling the external
    CI oracle;
  - if `rem != 0`, a decryption query `(true, _)` returns `([], (rem - 1, (false, [])))`, and an
    encryption query `(false, req)` with `(unframe req).length == n && (dropFrame req).length == n`
    queries the external CI encryption oracle on `if bit then dropFrame req else unframe req`
    (truncating the reply to `ctBound`) and transitions to `(rem - 1, (false, []))`. -/
noncomputable def ccaToCIHandler (n ctBound : ℕ) (bit : Bool) (request : Bool × List Bool) :
    StateT (ℕ × (Bool × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun state =>
    if state.2.1 then
      pure ([], (state.1, (true, state.2.2)))
    else
      if state.1 == 0 then
        if request.1 then
          pure ([], (0, (true, request.2)))
        else
          pure ([], (0, (true, [])))
      else
        if request.1 then
          pure ([], (state.1 - 1, (false, [])))
        else
          if ((unframe request.2).length == n) && ((dropFrame request.2).length == n) then
            (fun ct => (ct, (state.1 - 1, (false, [])))) <$>
              (List.take ctBound <$>
                ProbOracleComp.query ((), if bit then dropFrame request.2 else unframe request.2))
          else
            pure ([], (state.1 - 1, (false, [])))

/-- Deterministic-index ciphertext-integrity reduction at query countdown `j`
([BonehShoup2023], Section 9.2.3, Theorem 9.1): run `adversary n []` against
`ccaToCIHandler n (ctBound n) bit` starting from `(j, (false, []))` and output the captured
ciphertext candidate `out.2.2.2`. -/
noncomputable def ccaToCIAtIndexAdversary (ctBound : ℕ → ℕ) (j : ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (ccaToCIHandler n (ctBound n) bit))
      (adversary n [])).run (j, (false, []))
    return out.2.2.2

/-- Reduction from decryption-oracle forgery in `ccaRejectGame` to the ciphertext-integrity game
`ciGame` for fixed challenge bit `bit` ([BonehShoup2023], Section 9.2.3, adversary $B_{\mathrm{ci}}$
in Theorem 9.1): sample a uniform dyadic query countdown
`j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))` and run
`ccaToCIAtIndexAdversary ctBound j bit adversary`. -/
noncomputable def ccaToCIAdversary (ctBound Q : ℕ → ℕ) (bit : Bool)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
    ccaToCIAtIndexAdversary ctBound j bit adversary n aux

/-- Single-adversary ciphertext-integrity reduction that samples a hidden challenge bit uniformly
via `BitString.sampleList 1` and invokes `ccaToCIAdversary` ([BonehShoup2023], Section 9.2.3,
proof of Theorem 9.1, printed p. 364). -/
noncomputable def ccaToCIHiddenBitAdversary (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) : CIAdversary :=
  fun n aux => do
    let bits ← ProbOracleComp.sample (BitString.sampleList 1)
    if bits == [true] then
      ccaToCIAdversary ctBound Q true adversary n aux
    else
      ccaToCIAdversary ctBound Q false adversary n aux

/-- `ccaToCIAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary) (bit : Bool)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIAdversary ctBound Q bit adversary) := by
  let ECaller := encPair (encPair encUnary encBits) encUnary
  let EState := encPair encUnary (encPair encBool encBits)
  let EIn := encPair ECaller (encPair (encPair encBool encBits) EState)
  have hcaptured : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.2.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hremZero : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.2.1 == 0)
      EIn encBool :=
    ComputableTidilyInPolyTime.unary_beq (by dsimp only [EIn, ECaller, EState]; fun_prop)
      (ComputableTidilyInPolyTime.const 0)
  have hop : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        p.2.1.1)
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; fun_prop
  have hencCond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ((unframe p.2.1.2).length == p.1.1.1) && ((dropFrame p.2.1.2).length == p.1.1.1))
      EIn encBool := by
    dsimp only [EIn, ECaller, EState]; polytime
  have hm0 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        unframe p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.unframe.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hm1 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        dropFrame p.2.1.2)
      EIn encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hmsg : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        if bit then dropFrame p.2.1.2 else unframe p.2.1.2)
      EIn encBits := by
    cases bit <;> simpa using (by first | exact hm1 | exact hm0)
  have hlimit : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ctBound p.1.1.1)
      EIn encUnary :=
    hctBound.tidy.comp (by dsimp only [EIn, ECaller, EState]; fun_prop)
  have hdecRem : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (p.2.2.1 - 1, (false, ([] : List Bool))))
      EIn EState := by
    dsimp only [EIn, ECaller, EState]
    exact ComputableTidilyInPolyTime.prod
      (ComputableTidilyInPolyTime.unary_sub.comp
        (ComputableTidilyInPolyTime.prod (by fun_prop) (ComputableTidilyInPolyTime.const 1)))
      (ComputableTidilyInPolyTime.const (false, []))
  have hbranchCaptured : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], (p.2.2.1, (true, p.2.2.2.2)))) := by
    dsimp only [EIn, ECaller, EState]
    exact (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const true)
          (by fun_prop)))).isPPTOn.isOraclePPTOn
  have hbranchZeroDec : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        pure ([], (0, (true, p.2.1.2)))) := by
    dsimp only [EIn, ECaller, EState]
    exact (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const 0)
        (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const true)
          (by fun_prop)))).isPPTOn.isOraclePPTOn
  have hbranchZeroEnc : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun _ => pure ([], (0, (true, ([] : List Bool))))) :=
    (ComputableTidilyInPolyTime.const ([], (0, (true, [])))).isPPTOn.isOraclePPTOn
  have hbranchStepNo : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits EState)
      (fun p => pure ([], (p.2.2.1 - 1, (false, ([] : List Bool))))) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      hdecRem).isPPTOn.isOraclePPTOn
  have hbranchStepQuery : IsOraclePPTOn EIn (encPair encBits EState)
      (fun p : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        (fun ct => (ct, (p.2.2.1 - 1, (false, ([] : List Bool))))) <$>
          (List.take (ctBound p.1.1.1) <$>
            ProbOracleComp.query ((), if bit then dropFrame p.2.1.2 else unframe p.2.1.2))) :=
    (IsOraclePPTOn.query_take (Operation := Unit) () hmsg hlimit).map_with
      (ComputableTidilyInPolyTime.prod (by fun_prop)
        (hdecRem.comp (ComputableTidilyInPolyTime.fst EIn encBits)))
  have hhandler : IsOraclePPTOn EIn (encPair encBits EState)
      (fun pair : ((ℕ × List Bool) × ℕ) × ((Bool × List Bool) × (ℕ × (Bool × List Bool))) =>
        ccaToCIHandler pair.1.1.1 (ctBound pair.1.1.1) bit pair.2.1 pair.2.2) := by
    unfold ccaToCIHandler
    exact IsOraclePPTOn.cond hcaptured hbranchCaptured
      (IsOraclePPTOn.cond hremZero
        (IsOraclePPTOn.cond hop hbranchZeroDec hbranchZeroEnc)
        (IsOraclePPTOn.cond hop hbranchStepNo
          (IsOraclePPTOn.cond hencCond hbranchStepQuery hbranchStepNo)))
  have hres : ComputableTidilyInPolyTime
      (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1 + pair.2.length + 4)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]
    have hct : ComputableTidilyInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => ctBound pair.1.1.1)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary :=
      hctBound.tidy.comp (by fun_prop)
    have hqlen : ComputableTidilyInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) × List Bool => pair.2.length + 4)
        (encPair (encPair (encPair encUnary encBits) encUnary) encBits) encUnary := by
      polytime
    exact ComputableTidilyInPolyTime.unary_add.comp (ComputableTidilyInPolyTime.prod hct hqlen)
  have hinit : ComputableTidilyInPolyTime
      (fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      ECaller EState := by
    dsimp only [ECaller, EState]
    exact ComputableTidilyInPolyTime.prod (by fun_prop)
      (ComputableTidilyInPolyTime.const (false, []))
  have hrun : IsOraclePPTOn ECaller (encPair encBool EState)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (ccaToCIHandler caller.1.1 (ctBound caller.1.1) bit))
          (adversary caller.1.1 [])).run (caller.2, (false, []))) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : (ℕ × List Bool) × ℕ => (caller.1.1, ([] : List Bool)))
      (initial := fun caller : (ℕ × List Bool) × ℕ => (caller.2, (false, ([] : List Bool))))
      (resources := fun caller query => ctBound caller.1.1 + query.length + 4)
      (by dsimp only [ECaller]; fun_prop) hhandler hinit
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold ccaToCIHandler at hresult
    by_cases hcap : state.2.1 = true
    · simp only [hcap, ↓reduceIte] at hresult
      cases ProbOracleComp.eq_of_mem_support_pure hresult
      refine ⟨trivial, by simp, ?_⟩
      simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton, encBits_apply]
      lia
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte] at hresult
      by_cases hzero : (state.1 == 0) = true
      · simp only [hzero, ↓reduceIte] at hresult
        cases hreq : request.1 <;>
          simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult <;>
          cases ProbOracleComp.eq_of_mem_support_pure hresult <;>
          refine ⟨trivial, by simp, ?_⟩ <;>
          simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
            encBool_apply, List.length_singleton, encBits_apply, List.length_nil] <;>
          lia
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte] at hresult
        cases hreq : request.1
        · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hresult
          by_cases hlenEq : ((unframe request.2).length == caller.1.1 &&
              (dropFrame request.2).length == caller.1.1) = true
          · simp only [hlenEq, ↓reduceIte] at hresult
            obtain ⟨ct, hct, rfl⟩ := ProbOracleComp.mem_support_map hresult
            obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hct
            refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
            simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
              encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
            lia
          · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte] at hresult
            cases ProbOracleComp.eq_of_mem_support_pure hresult
            refine ⟨trivial, by simp, ?_⟩
            simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
              encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
            lia
        · simp only [hreq, ↓reduceIte] at hresult
          cases ProbOracleComp.eq_of_mem_support_pure hresult
          refine ⟨trivial, by simp, ?_⟩
          simp only [EState, length_encPair, encUnary_apply, List.length_replicate,
            encBool_apply, List.length_singleton, encBits_apply, List.length_nil]
          lia
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encUnary
      (fun caller : ℕ × List Bool =>
        ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q caller.1))) :=
    (isPPTOn_sampleDyadicIndex (hQ.tidy.comp (by fun_prop))).isOraclePPTOn (Operation := Unit)
  have hpost : ComputableTidilyInPolyTime
      (fun out : Bool × (ℕ × (Bool × List Bool)) => out.2.2.2)
      (encPair encBool EState) encBits := by
    dsimp only [EState]; fun_prop
  unfold ccaToCIAdversary ccaToCIAtIndexAdversary
  simpa only [bind_pure_comp] using (hsample.bind_with (hrun.map hpost)).isOraclePPT

/-- `ccaToCIHiddenBitAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_ccaToCIHiddenBitAdversary {ctBound Q : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : CCAAdversary} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBits (ccaToCIHiddenBitAdversary ctBound Q adversary) := by
  have hsample : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun _ : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList 1)) :=
    (ComputableTidilyInPolyTime.sampleList
      (ComputableTidilyInPolyTime.const 1)).isOraclePPTOn (Operation := Unit)
  have hcond : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => pair.2 == [true])
      (encPair (encPair encUnary encBits) encBits) encBool :=
    ComputableTidilyInPolyTime.beq (by fun_prop) (ComputableTidilyInPolyTime.const [true])
  have htrue : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Q true adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQ true hadversary).on.preprocess (by fun_prop)
  have hfalse : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) encBits
      (fun pair : (ℕ × List Bool) × List Bool =>
        ccaToCIAdversary ctBound Q false adversary pair.1.1 pair.1.2) :=
    (isOraclePPT_ccaToCIAdversary hctBound hQ false hadversary).on.preprocess (by fun_prop)
  unfold ccaToCIHiddenBitAdversary
  exact (hsample.bind_with (IsOraclePPTOn.cond hcond htrue hfalse)).isOraclePPT

/-! #### Difference-Lemma Hop and Query-Budget Induction for Theorem 9.1 -/

/-- `ccaOracle` instrumented with a sticky Boolean flag `bad` that becomes `true` whenever the
adversary submits a fresh ciphertext `ct` (`!queried.contains ct`) that decrypts to `some _`
([BonehShoup2023], Section 9.2.3, event $Z$ in Theorem 9.1). -/
private noncomputable def ccaWithBadOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return (encOption encBits dec, (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, (ct :: state.1, state.2))
      else
        return ([], state)

/-- `ccaRejectOracle` instrumented with the same sticky Boolean flag `bad`
([BonehShoup2023], Section 9.2.3, Game 1 with event $Z$ in Theorem 9.1). -/
private noncomputable def ccaRejectWithBadOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT (List (List Bool) × Bool) ProbComp (List Bool) :=
  fun state =>
    if request.1 then
      if state.1.contains request.2 then
        return ([], state)
      else
        let dec := E.decrypt n k request.2
        return ([], (state.1, state.2 || dec.isSome))
    else
      let m0 := unframe request.2
      let m1 := dropFrame request.2
      if (m0.length == n) && (m1.length == n) then do
        let ct ← E.encrypt n k (if bit then m1 else m0)
        return (ct, (ct :: state.1, state.2))
      else
        return ([], state)

private theorem run_ccaWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaWithBadOracle, ccaOracle, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : ((unframe request.2).length == n &&
        (dropFrame request.2).length == n) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaWithBadOracle, ccaOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem run_ccaRejectWithBadOracle_map_fst (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (program : WordOracleComp Bool Bool) (queried : List (List Bool)) (bad : Bool) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      program).run (queried, bad)).map (fun (a, s) => (a, s.1)) =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s)))
        program).run queried := by
  refine ProbOracleComp.run_interpret_map_state
    (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s))
    (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s))
    Prod.fst ?_ program (queried, bad)
  intro request state
  cases hreq : request.1
  · simp only [ccaRejectWithBadOracle, ccaRejectOracle, hreq, Bool.false_eq_true, ↓reduceIte]
    by_cases hlenEq : ((unframe request.2).length == n &&
        (dropFrame request.2).length == n) = true
    · simp [hlenEq, PMF.map_comp, Function.comp_def]
    · simp [hlenEq, PMF.pure_map]
  · simp only [ccaRejectWithBadOracle, ccaRejectOracle, hreq, ↓reduceIte]
    split_ifs <;> simp [PMF.pure_map]

private theorem identicalUntilBad_ccaRejectWithBad_ccaWithBad (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) :
    OracleComp.IdenticalUntilBad
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
      (fun s => s.2 = true) where
  agree q s hs a s' hs' := by
    cases q with
    | inl m => rfl
    | inr request =>
      simp only [ProbOracleComp.handler]
      cases hreq : request.1
      · simp only [ccaRejectWithBadOracle, ccaWithBadOracle, hreq, Bool.false_eq_true, ↓reduceIte]
      · simp only [ccaRejectWithBadOracle, ccaWithBadOracle, hreq, ↓reduceIte]
        split_ifs with hmem
        · rfl
        · cases hdec : E.decrypt n k request.2 with
          | none =>
            simp [Option.isSome, encOption]
          | some msg =>
            have hne : s' ≠ (s.1, true) := fun h => hs' (congrArg Prod.snd h)
            simp [Option.isSome, ProbComp.eval_pure, PMF.pure_apply, hne]
  absorb_first q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, ccaRejectWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]
  absorb_second q s hs x hx := by
    cases q with
    | inl m =>
      change x ∈ ((ProbComp.unifOracle m).map (·, s)).support at hx
      obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
      exact hs
    | inr request =>
      simp only [ProbOracleComp.handler, ccaWithBadOracle] at hx
      cases hreq : request.1
      · simp only [hreq, Bool.false_eq_true, ↓reduceIte] at hx
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
            PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hx
          obtain ⟨_, _, rfl⟩ := hx
          exact hs
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hx
          subst x
          exact hs
      · simp only [hreq, ↓reduceIte] at hx
        split_ifs at hx <;>
          simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx <;>
          subst x <;>
          simp [hs]

/-- Combined single-step stateful oracle representing `ccaToCIHandler` composed with
`ciEncryptionOracle` on joint state `(rem, (hasCaptured, capturedCt)) × queriedCiphertexts`. -/
private noncomputable def ccaToCICombinedOracle (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) :
    StateT ((ℕ × (Bool × List Bool)) × List (List Bool)) ProbComp (List Bool) :=
  fun state =>
    if state.1.2.1 then
      return ([], ((state.1.1, (true, state.1.2.2)), state.2))
    else
      if state.1.1 == 0 then
        if request.1 then
          return ([], ((0, (true, request.2)), state.2))
        else
          return ([], ((0, (true, [])), state.2))
      else
        if request.1 then
          return ([], ((state.1.1 - 1, (false, [])), state.2))
        else
          let m0 := unframe request.2
          let m1 := dropFrame request.2
          if (m0.length == n) && (m1.length == n) then do
            let ct ← E.encrypt n k (if bit then m1 else m0)
            return (ct, ((state.1.1 - 1, (false, [])), ct :: state.2))
          else
            return ([], ((state.1.1 - 1, (false, [])), state.2))

/-- Once `hasCaptured = true` holds in `ccaToCICombinedOracle`, both `capturedCt` and `queried`
remain frozen across any subsequent computation `program`. -/
private theorem ciCombined_captured_bind_eq_one {α : Type} (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) (program : WordOracleComp Bool α) (rem : ℕ)
    (ct : List Bool) (queried : List (List Bool))
    (hwin : (!queried.contains ct && (E.decrypt n k ct).isSome) = true) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
      program).run ((rem, (true, ct)), queried)).bind
      (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) true =
      1 := by
  refine le_antisymm (PMF.coe_le_one _ _) (PMF.le_bind_apply_on_support _ fun x hx => ?_)
  have hinv := ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s))
    (fun s => s.1.2 = (true, ct) ∧ s.2 = queried)
    (fun q s ⟨hcap, hq⟩ a s' hs' => by
      have hcap1 : s.1.2.1 = true := by rw [hcap]
      have hcap2 : s.1.2.2 = ct := by rw [hcap]
      simp only [ccaToCICombinedOracle, hcap1, ↓reduceIte, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hs'
      cases hs'
      exact ⟨by simp [hcap2], hq⟩)
    program ((rem, (true, ct)), queried) ⟨rfl, rfl⟩ x.1 x.2 hx
  have hct : x.2.1.2.2 = ct := by rw [hinv.1]
  rw [hct, hinv.2, hwin, PMF.pure_apply_self]

private theorem ennreal_tsum_finsetSum {α β : Type*}
    (s : Finset β) (f : α → β → ℝ≥0∞) :
    (∑' a, ∑ b ∈ s, f a b) = ∑ b ∈ s, ∑' a, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.sum_insert hb, ENNReal.tsum_add, ih]

private theorem eval_ccaRejectWithBadOracle_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaRejectWithBadOracle n k bit request (queried, false)) =
      if request.1 then
        if queried.contains request.2 then
          PMF.pure ([], (queried, false))
        else
          PMF.pure ([], (queried, (E.decrypt n k request.2).isSome))
      else
        if ((unframe request.2).length == n && (dropFrame request.2).length == n) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, (ct :: queried, false)))
        else
          PMF.pure ([], (queried, false)) := by
  unfold ccaRejectWithBadOracle
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, Bool.false_or]
    split_ifs <;> simp only [ProbComp.eval_pure]

private theorem eval_ccaToCICombinedOracle_succ_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (j : ℕ) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaToCICombinedOracle n k bit request ((j + 1, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((j, (false, [])), queried))
      else
        if ((unframe request.2).length == n && (dropFrame request.2).length == n) = true then
          (ProbComp.eval (E.encrypt n k
            (if bit then dropFrame request.2 else unframe request.2))).bind
            (fun ct => PMF.pure (ct, ((j, (false, [])), ct :: queried)))
        else
          PMF.pure ([], ((j, (false, [])), queried)) := by
  have hne : ((j + 1 == 0) = true) ↔ False := by simp
  unfold ccaToCICombinedOracle
  simp only [Bool.false_eq_true, ↓reduceIte, hne, Nat.add_sub_cancel]
  cases hreq : request.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  · simp only [↓reduceIte, ProbComp.eval_pure]

private theorem eval_ccaToCICombinedOracle_zero_false (E : SymmetricCipher) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Bool × List Bool) (queried : List (List Bool)) :
    ProbComp.eval (E.ccaToCICombinedOracle n k bit request ((0, (false, [])), queried)) =
      if request.1 then
        PMF.pure ([], ((0, (true, request.2)), queried))
      else
        PMF.pure ([], ((0, (true, [])), queried)) := by
  unfold ccaToCICombinedOracle
  cases hreq : request.1 <;>
    simp [ProbComp.eval_pure]

/-- Query-budget induction for [BonehShoup2023], Theorem 9.1: for any program `program` making at
most `Q` external oracle queries, the probability of reaching `bad = true` under
`ccaRejectWithBadOracle` from `(queried, false)` is bounded by the sum over countdown indices
`j ∈ Finset.range (Q + 1)` of the CI winning probability under `ccaToCICombinedOracle` from
`((j, (false, [])), queried)`. -/
private theorem bad_ccaRejectWithBad_le_sum_ciCombined {α : Type} (E : SymmetricCipher) (n : ℕ)
    (k : List Bool) (bit : Bool) {program : WordOracleComp Bool α} {Q : ℕ}
    (hq : program.IsQueryBounded Q) (queried : List (List Bool)) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
      program).run (queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ j ∈ Finset.range (Q + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
          program).run ((j, (false, [])), queried)).bind
          (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
          true := by
  induction hq generalizing queried with
  | pure a Q =>
    simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte, zero_le]
  | liftBind q cont Q hcont ih =>
    cases q with
    | inl m =>
      simp only [Sum.elim_inl, Nat.add_zero, OracleComp.run_interpret_bind,
        OracleComp.run_interpret_query, ProbOracleComp.handler, StateT.lift,
        Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
        PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.bind_apply]
      calc ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
            ((OracleComp.interpret
              (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
              (cont a)).run (queried, false)).toOuterMeasure {x | x.2.2 = true}
          ≤ ∑' a : Fin (m + 1), ProbComp.unifOracle m a *
              ∑ j ∈ Finset.range (Q + 1),
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                  (cont a)).run ((j, (false, [])), queried)).bind
                  (fun x =>
                    PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome))
                  true :=
            ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (ih a queried) zero_le
        _ = _ := by
          simp only [Finset.mul_sum]
          rw [ennreal_tsum_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [← PMF.bind_apply]
    | inr request =>
      simp only [Sum.elim_inr, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
        ProbOracleComp.handler]
      rw [Finset.sum_range_succ']
      simp only [eval_ccaRejectWithBadOracle_false, eval_ccaToCICombinedOracle_succ_false,
        eval_ccaToCICombinedOracle_zero_false]
      cases hreq : request.1
      · -- Encryption query: `request.1 = false`
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hlenEq : ((unframe request.2).length == n &&
            (dropFrame request.2).length == n) = true
        · simp only [hlenEq, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind,
            PMF.bind_bind, PMF.pure_bind, PMF.toOuterMeasure_bind_apply]
          have hle : ∑' ct : List Bool,
              ProbComp.eval
                (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                ((OracleComp.interpret
                  (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                    (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
                  (cont ct)).run (ct :: queried, false)).toOuterMeasure {x | x.2.2 = true} ≤
              ∑ j ∈ Finset.range (Q + 1),
                (ProbComp.eval (E.encrypt n k
                  (if bit then dropFrame request.2 else unframe request.2))).bind (fun ct =>
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                      (cont ct)).run ((j, (false, [])), ct :: queried)).bind
                      (fun x =>
                        PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                          (E.decrypt n k x.2.1.2.2).isSome)))
                  true := by
            calc ∑' ct : List Bool,
                  ProbComp.eval
                    (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                    ((OracleComp.interpret
                      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                        (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
                      (cont ct)).run (ct :: queried, false)).toOuterMeasure {x | x.2.2 = true}
                ≤ ∑' ct : List Bool,
                    ProbComp.eval
                      (E.encrypt n k (if bit then dropFrame request.2 else unframe request.2)) ct *
                      ∑ j ∈ Finset.range (Q + 1),
                        ((OracleComp.interpret
                          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
                            (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
                          (cont ct)).run ((j, (false, [])), ct :: queried)).bind
                          (fun x =>
                            PMF.pure (!x.2.2.contains x.2.1.2.2 &&
                              (E.decrypt n k x.2.1.2.2).isSome))
                          true :=
                  ENNReal.tsum_le_tsum fun ct =>
                    mul_le_mul_of_nonneg_left (ih ct (ct :: queried)) zero_le
              _ = _ := by
                simp only [Finset.mul_sum]
                rw [ennreal_tsum_finsetSum]
                refine Finset.sum_congr rfl fun j _ => ?_
                simp only [PMF.bind_apply]
          exact hle.trans le_self_add
        · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte,
            Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
      · -- Decryption query: `request.1 = true`
        simp only [↓reduceIte,
          Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
        by_cases hmem : queried.contains request.2 = true
        · simp only [hmem, ↓reduceIte, PMF.pure_bind]
          exact (ih [] queried).trans le_self_add
        · simp only [hmem, Bool.false_eq_true, ↓reduceIte, PMF.pure_bind]
          by_cases hsome : (E.decrypt n k request.2).isSome = true
          · simp only [hsome]
            have hwin :
                (!queried.contains request.2 && (E.decrypt n k request.2).isSome) = true := by
              rw [Bool.eq_false_iff.mpr hmem, hsome]
              rfl
            rw [ciCombined_captured_bind_eq_one E n k bit (cont []) 0 request.2 queried hwin]
            exact (Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans le_add_self
          · have hnotSome : (E.decrypt n k request.2).isSome = false :=
              Bool.eq_false_iff.mpr hsome
            simp only [hnotSome]
            exact (ih [] queried).trans le_self_add

/-- When `ctBound n` bounds all ciphertext lengths produced by `E.encrypt n k` on `n`-bit messages,
running `ccaToCIAtIndexAdversary ctBound j bit adversary` in `ciGame` under key `k` has the same
winning distribution as `ccaToCICombinedOracle` from `((j, (false, [])), [])`. -/
private theorem eval_ciGame_ccaToCIAtIndexAdversary_key (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (j : ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) (k : List Bool)
    (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
      (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
      (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaToCICombinedOracle n k bit q s)))
        (adversary n [])).run ((j, (false, [])), [])).bind
        (fun x => PMF.pure (!x.2.2.contains x.2.1.2.2 && (E.decrypt n k x.2.1.2.2).isSome)) := by
  unfold ccaToCIAtIndexAdversary
  rw [OracleComp.interpret_bind, StateT.run_bind]
  simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  congr 2
  funext q state
  cases q with
  | inl m => rfl
  | inr request =>
    simp only [ProbOracleComp.handler]
    change ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
        (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
      (ccaToCIHandler n (ctBound n) bit request state.1)).run state.2).map
      (fun result => (result.1.1, result.1.2, result.2)) =
      ProbComp.eval (E.ccaToCICombinedOracle n k bit request state)
    unfold ccaToCIHandler ccaToCICombinedOracle
    by_cases hcap : state.1.2.1 = true
    · simp only [hcap, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
    · simp only [hcap, Bool.false_eq_true, ↓reduceIte]
      by_cases hzero : (state.1.1 == 0) = true
      · simp only [hzero, ↓reduceIte]
        cases hreq : request.1 <;>
          simp only [Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
            StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
      · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
        cases hreq : request.1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hlenEq : ((unframe request.2).length == n &&
              (dropFrame request.2).length == n) = true
          · simp only [hlenEq, ↓reduceIte, Functor.map_map, OracleComp.interpret_map,
              StateT.run_map, ProbOracleComp.interpret_query, _root_.PMF.monad_map_eq_map,
              ProbComp.eval_bind, ProbComp.eval_pure, ciEncryptionOracle]
            simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
            have hmbLen : (if bit then dropFrame request.2 else unframe request.2).length = n := by
              cases bit <;> simp [hlenEq]
            have hmbEq : ((if bit then dropFrame request.2 else unframe request.2).length == n) =
                true := beq_iff_eq.mpr hmbLen
            dsimp only [StateT.run]
            simp only [hmbEq, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.map_bind, PMF.pure_map]
            apply PMF.bind_congr_on_support
            intro ct hct
            rw [List.take_of_length_le (hctBound k hk _ hmbLen ct hct)]
          · simp only [hlenEq, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
              StateT.run_pure, Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]
        · simp only [↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
            Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure, PMF.pure_map]

/-- Advantage between `ccaGame` and `ccaRejectGame` at challenge bit `bit` is bounded by the sum
over `j ∈ Finset.range (Q n + 1)` of the CI winning probabilities of
`ccaToCIAtIndexAdversary ctBound j bit adversary`. -/
private theorem advantage_ccaGame_ccaRejectGame_le_sum (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (bit : Bool) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary bit n))
        (ProbComp.eval (E.ccaRejectGame adversary bit n)) : ℝ) ≤
      ∑ j ∈ Finset.range (Q n + 1),
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ) := by
  have hccaEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  have hrejEq (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectOracle n k bit q s)))
        (adversary n [])).run []).bind (fun out => PMF.pure out.1) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) := by
    rw [← run_ccaRejectWithBadOracle_map_fst E n k bit (adversary n []) [] false,
      PMF.bind_map, Function.comp_def]
  set pCCA := ProbComp.eval (E.ccaGame adversary bit n) true
  set pRej := ProbComp.eval (E.ccaRejectGame adversary bit n) true
  set pSum : ℝ≥0∞ := ∑ j ∈ Finset.range (Q n + 1),
    ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n) true
  have hsum_eq : pSum = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ∑ j ∈ Finset.range (Q n + 1),
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) true := by
    simp only [pSum, ciGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret]
    conv_lhs =>
      arg 2; ext j
      rw [PMF.bind_apply]
    rw [← ennreal_tsum_finsetSum]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
  have hCCA_eq : pCCA = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pCCA, ccaGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hccaEq]
    exact PMF.bind_apply _ _ _
  have hRej_eq : pRej = ∑' k : List Bool, ProbComp.eval (E.keyGen n) k *
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ccaRejectWithBadOracle n k bit q s)))
        (adversary n [])).run ([], false)).bind (fun out => PMF.pure out.1) true := by
    simp only [pRej, ccaRejectGame, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbOracleComp.eval_run_interpret, hrejEq]
    exact PMF.bind_apply _ _ _
  have hle1 : pCCA ≤ pRej + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := (identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit).symm
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      rw [← (identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit).bad_eq] at hstep
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_ccaRejectWithBad_le_sum_ciCombined E n k bit hq []).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hle2 : pRej ≤ pCCA + pSum := by
    rw [hCCA_eq, hRej_eq, hsum_eq, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [← mul_add]
    by_cases hk : k ∈ (ProbComp.eval (E.keyGen n)).support
    · refine mul_le_mul_of_nonneg_left ?_ zero_le
      have hiub := identicalUntilBad_ccaRejectWithBad_ccaWithBad E n k bit
      have hstep := hiub.bind_apply_le (adversary n []) ([], false) (fun out => PMF.pure out.1) true
      refine hstep.trans (add_le_add le_rfl ?_)
      refine (bad_ccaRejectWithBad_le_sum_ciCombined E n k bit hq []).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eval_ciGame_ccaToCIAtIndexAdversary_key E ctBound j bit adversary n k hk hctBound]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hk, zero_mul, zero_mul]
  have hpSum_ne_top : pSum ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => PMF.apply_ne_top _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle1
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hpSum_ne_top⟩) hle2
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) hpSum_ne_top] at h1 h2
  have habs : |pCCA.toReal - pRej.toReal| ≤ pSum.toReal :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, pCCA, pRej, pSum,
    ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top _ _)] using habs

/-- Running `ccaToCIAdversary` in `ciGame` averages `ccaToCIAtIndexAdversary` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_ciGame_ccaToCIAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound i.val bit adversary) n)) := by
  simp only [ciGame, ccaToCIAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
        (do
          let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
          ccaToCIAtIndexAdversary ctBound j bit adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind (fun i =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAtIndexAdversary ctBound i.val bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      ProbComp.eval_sampleDyadicIndex]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- The sum of CI winning probabilities over `j ∈ Finset.range (Q n + 1)` is at most
`dyadicSize (Q n)` times the CI winning probability of `ccaToCIAdversary`. -/
private theorem sum_succProbability_ccaToCIAtIndexAdversary_le (E : SymmetricCipher)
    (ctBound Q : ℕ → ℕ) (bit : Bool) (adversary : CCAAdversary) (n : ℕ) :
    (∑ j ∈ Finset.range (Q n + 1),
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ)) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n)) : ℝ) := by
  have hcap : (dyadicSize (Q n) : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos (Q n)).ne'
  rw [eval_ciGame_ccaToCIAdversary, Game.succProbability_uniform, NNReal.coe_div,
    NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_fin, mul_div_cancel₀ _ hcap,
    Fin.sum_univ_eq_sum_range
      (fun j => (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAtIndexAdversary ctBound j bit adversary) n)) : ℝ))]
  have hsub : Finset.range (Q n + 1) ⊆ Finset.range (dyadicSize (Q n)) := by
    intro x hx
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le (lt_dyadicSize (Q n)))
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => NNReal.coe_nonneg _

/-- **Quantitative AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3, Theorem 9.1,
printed pp. 363–365): for any `CCAAdversary` making at most `Q n` oracle queries at security
parameter `n`, the adaptive CCA distinguishing advantage is bounded by the CPA advantage of
`ccaToCPAAdversary` plus `dyadicSize (Q n)` times the ciphertext-integrity winning probabilities of
`ccaToCIAdversary` for `bit = false` and `bit = true`. -/
theorem advantage_ccaGame_le (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) +
      (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
  have h1 : (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaRejectGame adversary false n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n))
  have h2 : (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
        (ProbComp.eval (E.ccaRejectGame adversary true n)) : ℝ) +
      (Game.advantage (ProbComp.eval (E.ccaRejectGame adversary true n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) := by
    exact_mod_cast Game.advantage_triangle
      (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary true n))
      (ProbComp.eval (E.ccaGame adversary true n))
  have hcomm : Game.advantage (ProbComp.eval (E.ccaRejectGame adversary true n))
      (ProbComp.eval (E.ccaGame adversary true n)) =
      Game.advantage (ProbComp.eval (E.ccaGame adversary true n))
      (ProbComp.eval (E.ccaRejectGame adversary true n)) := Game.advantage_comm _ _
  have hcpaEq : Game.advantage (ProbComp.eval (E.ccaRejectGame adversary false n))
      (ProbComp.eval (E.ccaRejectGame adversary true n)) =
      Game.advantage (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
      (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) := by
    rw [eval_cpaGame_ccaToCPAAdversary E ctBound adversary false n hctBound,
      eval_cpaGame_ccaToCPAAdversary E ctBound adversary true n hctBound]
  rw [hcomm, hcpaEq] at h2
  have hfalse := (advantage_ccaGame_ccaRejectGame_le_sum E ctBound Q adversary false n hq
    hctBound).trans (sum_succProbability_ccaToCIAtIndexAdversary_le E ctBound Q false adversary n)
  have htrue := (advantage_ccaGame_ccaRejectGame_le_sum E ctBound Q adversary true n hq
    hctBound).trans (sum_succProbability_ccaToCIAtIndexAdversary_le E ctBound Q true adversary n)
  linarith

/-- Running `ccaToCIHiddenBitAdversary` in `ciGame` averages `ccaToCIAdversary` uniformly over
`bit : Bool`. -/
theorem eval_ciGame_ccaToCIHiddenBitAdversary (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ) :
    ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n) =
      (PMF.uniformOfFintype Bool).bind
        (fun bit => ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q bit adversary) n)) := by
  simp only [ciGame, ccaToCIHiddenBitAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hsample (k : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
        (do
          let bits ← ProbOracleComp.sample (BitString.sampleList 1)
          if bits == [true] then
            ccaToCIAdversary ctBound Q true adversary n []
          else
            ccaToCIAdversary ctBound Q false adversary n [])).run []).bind
        (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome)) =
      (PMF.uniformOfFintype Bool).bind (fun bit =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (E.ciEncryptionOracle n k q s)))
          (ccaToCIAdversary ctBound Q bit adversary n [])).run []).bind
          (fun out => PMF.pure (!out.2.contains out.1 && (E.decrypt n k out.1).isSome))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample,
      BitString.eval_sampleList, BitString.uniformList_succ 0, BitString.uniformList_zero]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map,
      PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext bit
    cases bit <;> rfl
  simp only [hsample]
  exact PMF.bind_comm _ _ _

/-- **Single-adversary quantitative AE $\Rightarrow$ CCA bound** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, equation (9.3) and proof on printed pp. 363–364): using `ccaToCIHiddenBitAdversary` to
sample the hidden challenge bit uniformly yields factor `2 * dyadicSize (Q n)` on the single CI
adversary. -/
theorem advantage_ccaGame_le_two_mul (E : SymmetricCipher) (ctBound Q : ℕ → ℕ)
    (adversary : CCAAdversary) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n))
    (hctBound : ∀ k ∈ (ProbComp.eval (E.keyGen n)).support,
      ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n) :
    (Game.advantage (ProbComp.eval (E.ccaGame adversary false n))
        (ProbComp.eval (E.ccaGame adversary true n)) : ℝ) ≤
      2 * (dyadicSize (Q n) : ℝ) *
        (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) +
      (Game.advantage
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) false n))
        (ProbComp.eval (E.cpaGame (ccaToCPAAdversary ctBound adversary) true n)) : ℝ) := by
  have hmain := advantage_ccaGame_le E ctBound Q adversary n hq hctBound
  have havg : 2 * (Game.succProbability
      (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q false adversary) n)) : ℝ) +
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIAdversary ctBound Q true adversary) n)) : ℝ) := by
    rw [eval_ciGame_ccaToCIHiddenBitAdversary, Game.succProbability_uniform,
      NNReal.coe_div, NNReal.coe_sum, NNReal.coe_natCast, Fintype.card_bool,
      Fintype.sum_bool]
    ring
  have hd : 2 * (dyadicSize (Q n) : ℝ) *
      (Game.succProbability
        (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ) =
      (dyadicSize (Q n) : ℝ) *
        (2 * (Game.succProbability
          (ProbComp.eval (E.ciGame (ccaToCIHiddenBitAdversary ctBound Q adversary) n)) : ℝ)) := by
    ring
  rw [hd, havg]
  linarith

/-- **Authenticated encryption implies adaptive CCA security** ([BonehShoup2023], Section 9.2.3,
Theorem 9.1, printed pp. 363–365): every symmetric cipher satisfying `AuthenticatedEncryption`
(`INDCPA ∧ CiphertextIntegrity`) also satisfies `INDCCA`. -/
theorem AuthenticatedEncryption.indcca {E : SymmetricCipher} (hAE : E.AuthenticatedEncryption) :
    E.INDCCA := by
  rcases hAE with ⟨hcpa, hci⟩
  intro adversary hadversary
  obtain ⟨ck, dk, hlenKey⟩ := E.keyGen_ppt.length_le
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let ctBound : ℕ → ℕ := fun n => ce * (3 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ de
  let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hctBoundPoly : ComputableInPolyTime ctBound encUnary encUnary := by
    dsimp only [ctBound]; polytime
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]; polytime
  have hctBound (n : ℕ) (k : List Bool) (hk : k ∈ (ProbComp.eval (E.keyGen n)).support)
      (msg : List Bool) (hmsg : msg.length = n) (ct : List Bool)
      (hct : ct ∈ (ProbComp.eval (E.encrypt n k msg)).support) : ct.length ≤ ctBound n := by
    have hkLen := hlenKey n k hk
    have hctLen := hlenEnc (n, k, msg) ct hct
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkLen
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      hmsg] at hctLen
    exact hctLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
  have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
    simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
  have hcpaNeg := hcpa (ccaToCPAAdversary ctBound adversary)
    (isOraclePPT_ccaToCPAAdversary hctBoundPoly hadversary)
  have hciNeg := hci.negligible (ccaToCIHiddenBitAdversary ctBound Q adversary)
    (isOraclePPT_ccaToCIHiddenBitAdversary hctBoundPoly hQPoly hadversary)
  have hpolyDyadic : PolynomiallyBounded (fun n => 2 * dyadicSize (Q n)) := by
    dsimp only [Q]; fun_prop
  have hsumNeg := (hciNeg.polynomiallyBounded_mul hpolyDyadic).add hcpaNeg
  refine negligible_of_le hsumNeg fun n => ?_
  rw [← NNReal.coe_le_coe]
  simpa only [Pi.add_apply, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    advantage_ccaGame_le_two_mul E ctBound Q adversary n (hq n) (hctBound n)

end SymmetricCipher

/-! ### Encrypt-then-MAC Construction and Security (Boneh–Shoup Section 9.4.1 & Theorem 9.2) -/

@[local fun_prop]
private theorem isPPTOn_mac_keyGen_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess (ComputableInPolyTime.of_tidy hn)

@[local fun_prop]
private theorem isPPTOn_mac_sign_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a)) :=
  M.sign_ppt.preprocess (ComputableInPolyTime.of_tidy (hsk.prod hmsg))

@[local fun_prop]
private theorem computableTidilyInPolyTime_mac_verify_comp (M : MACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg tag : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits)
    (htag : ComputableTidilyInPolyTime tag encIn encBits) :
    ComputableTidilyInPolyTime (fun a => M.verify (sk a) (msg a) (tag a)) encIn encBool :=
  M.verify_polyTime.tidy.comp (hsk.prod (hmsg.prod htag))

/-- **Encrypt-then-MAC symmetric cipher** ([BonehShoup2023], Section 9.4.1, printed p. 367):
given a symmetric cipher `E : SymmetricCipher` whose ciphertexts on `n`-bit messages under supported
keys at security parameter `n` have length `n`, and a message authentication code `M : MACScheme` on
`n`-bit messages:
* `keyGen n` samples independent keys `ke ← E.keyGen n` and `km ← M.keyGen n` and returns
  `encPair encBits encBits (ke, km)`.
* `encrypt n k msg` encrypts `c ← E.encrypt n (unframe k) msg`, computes a tag
  `tag ← M.sign (dropFrame k) c`, and returns `encPair encBits encBits (c, tag)`.
* `decrypt n k ct` checks canonical pair framing
  `encPair encBits encBits (unframe ct, dropFrame ct) == ct`, checks `(unframe ct).length == n`, and
  verifies `M.verify (dropFrame k) (unframe ct) (dropFrame ct)`; if all three hold, it returns
  `E.decrypt n (unframe k) (unframe ct)`, and otherwise `none`.

Canonical pair framing `encPair encBits encBits (c, tag)` establishes a bijection between valid
encoded ciphertexts `ct` and pairs `(c, tag)` with `c.length = n`, so ciphertext freshness in
`ciGame` coincides with pair freshness in `M.sufCmaGame`. -/
noncomputable def encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n) :
    SymmetricCipher where
  keyGen n := do
    let ke ← E.keyGen n
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let c ← E.encrypt n (unframe k) msg
    let tag ← M.sign (dropFrame k) c
    return encPair encBits encBits (c, tag)
  decrypt n k ct :=
    if (encPair encBits encBits (unframe ct, dropFrame ct) == ct) &&
        ((unframe ct).length == n) &&
        M.verify (dropFrame k) (unframe ct) (dropFrame ct) then
      E.decrypt n (unframe k) (unframe ct)
    else
      none
  keyGen_ppt := by
    simp only [encPair_apply, encBits_apply]
    ppt
  encrypt_ppt := by
    simp only [encPair_apply, encBits_apply]
    ppt
  decrypt_polyTime := by
    have hcond : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (frame (unframe p.2.2) ++ dropFrame p.2.2 == p.2.2) &&
            ((unframe p.2.2).length == p.1) &&
            M.verify (dropFrame p.2.1) (unframe p.2.2) (dropFrame p.2.2))
        (encPair encUnary (encPair encBits encBits)) encBool := by polytime
    have hdecArg : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool => (p.1, unframe p.2.1, unframe p.2.2))
        (encPair encUnary (encPair encBits encBits))
        (encPair encUnary (encPair encBits encBits)) := by polytime
    have hyes : ComputableTidilyInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          E.decrypt p.1 (unframe p.2.1) (unframe p.2.2))
        (encPair encUnary (encPair encBits encBits)) (encOption encBits) :=
      E.decrypt_polyTime.tidy.comp hdecArg
    have hno : ComputableTidilyInPolyTime
        (fun _ : ℕ × List Bool × List Bool => (none : Option (List Bool)))
        (encPair encUnary (encPair encBits encBits)) (encOption encBits) :=
      ComputableTidilyInPolyTime.const none
    simp only [encPair_apply, encBits_apply]
    exact .of_tidy (ComputableTidilyInPolyTime.cond hcond hyes hno)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hk hct
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
      simp [encPair_apply, dropFrame_frame_append]
    rw [hunframe_k, hdrop_k] at hct
    obtain ⟨c, hc, tag, htag, rfl⟩ := hct
    have hunframe_ct : unframe (encPair encBits encBits (c, tag)) = c := by
      simp [encPair_apply, unframe_frame_append]
    have hdrop_ct : dropFrame (encPair encBits encBits (c, tag)) = tag := by
      simp [encPair_apply, dropFrame_frame_append]
    have hcLen : c.length = n := hctLen n ke hke msg hmsg c hc
    have hver : M.verify km c tag = true := M.verify_sign n km hkm c hcLen tag htag
    have hdec : E.decrypt n ke c = some msg := E.decrypt_encrypt n ke hke msg hmsg c hc
    rw [hunframe_k, hdrop_k, hunframe_ct, hdrop_ct]
    simp [hcLen, hver, hdec]

/-! #### Ciphertext-Integrity to SUF-CMA Reduction for Theorem 9.2 -/

/-- Open stateful handler that simulates the `ciEncryptionOracle` of `encryptThenMAC E M` inside
`M.sufCmaGame` ([BonehShoup2023], Section 9.4.1, Theorem 9.2, Part 1): on an `n`-bit message query
`request.2`, it encrypts `c ← E.encrypt n ke request.2`, queries the external MAC signing oracle on
`((), c)` (truncating the returned tag to `tagBound` bits), and returns
`encPair encBits encBits (c, tag)`. -/
noncomputable def etmToMACHandler (E : SymmetricCipher) (n tagBound : ℕ) (ke : List Bool)
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    if request.2.length == n then do
      let c ← ProbOracleComp.sample (E.encrypt n ke request.2)
      (fun tag => (encPair encBits encBits (c, tag), ())) <$>
        (List.take tagBound <$> ProbOracleComp.query ((), c))
    else
      pure ([], ())

/-- Ciphertext-integrity to SUF-CMA reduction `etmToMACForger` ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 1, printed pp. 367–368): samples `ke ← E.keyGen n`, runs `adversary n []`
against `etmToMACHandler E n (tagBound n) ke`, and when the candidate ciphertext `out.1` has
canonical pair framing and `E.decrypt n ke (unframe out.1)` succeeds, outputs the candidate forgery
pair `(unframe out.1, dropFrame out.1)`; otherwise outputs a dummy pair of length `≠ n` that is
rejected by `M.sufCmaGame`. -/
noncomputable def etmToMACForger (E : SymmetricCipher) (tagBound : ℕ → ℕ)
    (adversary : CIAdversary) : Forger :=
  fun n _ => do
    let ke ← ProbOracleComp.sample (E.keyGen n)
    (fun out : List Bool × Unit =>
      if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
          (E.decrypt n ke (unframe out.1)).isSome then
        (unframe out.1, dropFrame out.1)
      else
        (if n == 0 then [false] else [], [])) <$>
      (OracleComp.interpret
        (ProbOracleComp.handler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (etmToMACHandler E n (tagBound n) ke))
        (adversary n [])).run ()

private theorem isOraclePPTOn_etmToMACHandler (E : SymmetricCipher) {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinite Unit) encBits) (encFinite Unit)))
      (encPair encBits (encFinite Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        etmToMACHandler E pair.1.1.1 (tagBound pair.1.1.1) pair.1.2 pair.2.1 pair.2.2) := by
  have htagTidy := htagBound.tidy
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EIn := encPair ECaller (encPair (encPair (encFinite Unit) encBits) (encFinite Unit))
  unfold etmToMACHandler
  have hcond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        p.2.1.2.length == p.1.1.1)
      EIn encBool := by
    dsimp only [EIn, ECaller]; polytime
  have hencArg : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1.1, p.1.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [EIn, ECaller]; fun_prop
  have henc : IsOraclePPTOn (Operation := Unit) EIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        ProbOracleComp.sample (E.encrypt p.1.1.1 p.1.2 p.2.1.2)) :=
    (E.encrypt_ppt.preprocess hencArg.computableInPolyTime).isOraclePPTOn (Operation := Unit)
  have hqReq : ComputableTidilyInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool => q.2)
      (encPair EIn encBits) encBits := by
    fun_prop
  have hqN : ComputableTidilyInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        q.1.1.1.1)
      (encPair EIn encBits) encUnary := by
    dsimp only [EIn, ECaller]; fun_prop
  have hqLim : ComputableTidilyInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        tagBound q.1.1.1.1)
      (encPair EIn encBits) encUnary :=
    htagTidy.comp hqN
  have hq : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        List.take (tagBound q.1.1.1.1) <$> ProbOracleComp.query ((), q.2)) :=
    IsOraclePPTOn.query_take (Operation := Unit) () hqReq hqLim
  have hpairArg : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (r.1.2, r.2))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits encBits) := by
    fun_prop
  have hmap : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (encPair encBits encBits (r.1.2, r.2), ()))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits (encFinite Unit)) :=
    ComputableTidilyInPolyTime.prod hpairArg.encoded (ComputableTidilyInPolyTime.const ())
  have hqMap : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits)
      (encPair encBits (encFinite Unit))
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (fun tag => (encPair encBits encBits (q.2, tag), ())) <$>
          (List.take (tagBound q.1.1.1.1) <$> ProbOracleComp.query ((), q.2))) :=
    hq.map_with hmap
  have hyes : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinite Unit))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => do
        let c ← ProbOracleComp.sample (E.encrypt p.1.1.1 p.1.2 p.2.1.2)
        (fun tag => (encPair encBits encBits (c, tag), ())) <$>
          (List.take (tagBound p.1.1.1) <$> ProbOracleComp.query ((), c))) :=
    henc.bind_with hqMap
  have hno : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinite Unit))
      (fun _ : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        pure ([], ())) :=
    (ComputableTidilyInPolyTime.const ([], ())).isPPTOn.isOraclePPTOn (Operation := Unit)
  exact IsOraclePPTOn.cond hcond hyes hno

/-- `etmToMACForger` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_etmToMACForger (E : SymmetricCipher) {tagBound : ℕ → ℕ}
    {adversary : CIAdversary}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    (hadversary : IsOraclePPT encBits adversary) :
    IsOraclePPT (encPair encBits encBits) (etmToMACForger E tagBound adversary) := by
  have htagTidy := htagBound.tidy
  obtain ⟨ce, de, hlenEnc⟩ := E.encrypt_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hke : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (E.keyGen caller.1)) :=
    (E.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn (Operation := Unit)
  have hhandler := isOraclePPTOn_etmToMACHandler E htagBound
  have hprepare : ComputableTidilyInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableTidilyInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        2 * (ce * (2 * pair.1.1.1 + 2 * pair.1.2.length + pair.2.length + 3) ^ de) +
          tagBound pair.1.1.1 + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; polytime
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits (encFinite Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller query =>
        2 * (ce * (2 * caller.1.1 + 2 * caller.2.length + query.length + 3) ^ de) +
          tagBound caller.1.1 + 2)
      hprepare hhandler (ComputableTidilyInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold etmToMACHandler at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨c, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      change c ∈ OracleComp.support
        (ProbOracleComp.sample (E.encrypt caller.1.1 caller.2 request.2)) at hc
      rw [ProbOracleComp.support_sample] at hc
      have hcLen := hlenEnc (caller.1.1, caller.2, request.2) c hc
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hcLen
      have hcBound : c.length ≤
          ce * (2 * caller.1.1 + 2 * caller.2.length + request.2.length + 3) ^ de :=
        hcLen.trans (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (by lia) de))
      obtain ⟨tag, htag, rfl⟩ := ProbOracleComp.mem_support_map hresult
      obtain ⟨rawTag, _, rfl⟩ := ProbOracleComp.mem_support_map htag
      have htagTake : (List.take (tagBound caller.1.1) rawTag).length ≤ tagBound caller.1.1 :=
        List.length_take_le _ _
      refine ⟨trivial, ?_, by lia⟩
      simp only [length_encPair, encBits_apply]
      lia
    · have hresEq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by lia⟩
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (p.1.1.1, p.1.2, unframe p.2.1))
      (encPair ECaller (encPair encBits (encFinite Unit)))
      (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [ECaller]; fun_prop
  have hdecSome : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome)
      (encPair ECaller (encPair encBits (encFinite Unit))) encBool :=
    (E.decrypt_polyTime.tidy.comp hdecArg).optionIsSome
  have hpostYes : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (unframe p.2.1, dropFrame p.2.1))
      (encPair ECaller (encPair encBits (encFinite Unit))) (encPair encBits encBits) := by
    dsimp only [ECaller]; fun_prop
  have hframeEq : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1 == p.2)
      (encPair encBits encBits) encBool := by
    polytime
  have houtProj : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) => p.2.1)
      (encPair ECaller (encPair encBits (encFinite Unit))) encBits := by
    fun_prop
  have hframeCond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1)
      (encPair ECaller (encPair encBits (encFinite Unit))) encBool :=
    hframeEq.comp (hpostYes.encoded.prod houtProj)
  have hand : ComputableTidilyInPolyTime
      (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := by
    polytime
  have hpostCond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1) &&
          (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome)
      (encPair ECaller (encPair encBits (encFinite Unit))) encBool :=
    hand.comp (hframeCond.prod hdecSome)
  have hnProj : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) => p.1.1.1)
      (encPair ECaller (encPair encBits (encFinite Unit))) encUnary := by
    dsimp only [ECaller]; fun_prop
  have hpostNo : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        (if p.1.1.1 == 0 then [false] else [], ([] : List Bool)))
      (encPair ECaller (encPair encBits (encFinite Unit))) (encPair encBits encBits) :=
    ComputableTidilyInPolyTime.prod
      (ComputableTidilyInPolyTime.cond
        (ComputableTidilyInPolyTime.unary_beq hnProj (ComputableTidilyInPolyTime.const 0))
        (ComputableTidilyInPolyTime.const [false])
        (ComputableTidilyInPolyTime.const []))
      (ComputableTidilyInPolyTime.const [])
  have hpost : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × (List Bool × Unit) =>
        if (encPair encBits encBits (unframe p.2.1, dropFrame p.2.1) == p.2.1) &&
            (E.decrypt p.1.1.1 p.1.2 (unframe p.2.1)).isSome then
          (unframe p.2.1, dropFrame p.2.1)
        else
          (if p.1.1.1 == 0 then [false] else [], []))
      (encPair ECaller (encPair encBits (encFinite Unit)))
      (encPair encBits encBits) :=
    ComputableTidilyInPolyTime.cond hpostCond hpostYes hpostNo
  have hrunMap : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBits encBits)
      (fun caller : (ℕ × List Bool) × List Bool =>
        (fun out : List Bool × Unit =>
          if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
              (E.decrypt caller.1.1 caller.2 (unframe out.1)).isSome then
            (unframe out.1, dropFrame out.1)
          else
            (if caller.1.1 == 0 then [false] else [], [])) <$>
          (OracleComp.interpret
            (ProbOracleComp.handler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (etmToMACHandler E caller.1.1 (tagBound caller.1.1) caller.2))
            (adversary caller.1.1 [])).run ()) :=
    hrun.map_with hpost
  unfold etmToMACForger
  exact (hke.bind_with hrunMap).isOraclePPT

private theorem list_contains_map_encPair (pairs : List (List Bool × List Bool))
    (p : List Bool × List Bool) :
    (pairs.map (encPair encBits encBits)).contains (encPair encBits encBits p) =
      pairs.contains p := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact List.mem_map_of_injective (encPair encBits encBits).injective

private theorem etm_sufCma_win_eq_ci_win (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (n : ℕ) (ke km out : List Bool) (queriedPairs : List (List Bool × List Bool)) :
    (let pair :=
      if (encPair encBits encBits (unframe out, dropFrame out) == out) &&
          (E.decrypt n ke (unframe out)).isSome then
        (unframe out, dropFrame out)
      else
        (if n == 0 then [false] else [], [])
     (pair.1.length == n) && !queriedPairs.contains pair && M.verify km pair.1 pair.2) =
      (!(queriedPairs.map (encPair encBits encBits)).contains out &&
        ((encryptThenMAC E M hctLen).decrypt n (encPair encBits encBits (ke, km)) out).isSome) := by
  have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
    simp [encPair_apply, unframe_frame_append]
  have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
    simp [encPair_apply, dropFrame_frame_append]
  dsimp only [encryptThenMAC]
  rw [hunframe_k, hdrop_k]
  by_cases hframe : (encPair encBits encBits (unframe out, dropFrame out) == out) = true
  · by_cases hdec : (E.decrypt n ke (unframe out)).isSome = true
    · simp only [hframe, hdec, Bool.true_and, ↓reduceIte]
      have houtEq : encPair encBits encBits (unframe out, dropFrame out) = out :=
        beq_iff_eq.mp hframe
      rw [← list_contains_map_encPair queriedPairs (unframe out, dropFrame out), houtEq]
      cases hlen : ((unframe out).length == n) <;>
        cases hmem : (queriedPairs.map (encPair encBits encBits)).contains out <;>
        cases hver : M.verify km (unframe out) (dropFrame out) <;>
        simp [hdec]
    · have hdecF : (E.decrypt n ke (unframe out)).isSome = false := Bool.eq_false_iff.mpr hdec
      have hlenDummy : ((if n == 0 then [false] else []).length == n) = false := by
        cases n <;> rfl
      simp only [hframe, hdecF, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hlenDummy,
        Bool.false_and]
      split_ifs <;> simp [hdecF]
  · have hframeF : (encPair encBits encBits (unframe out, dropFrame out) == out) = false :=
      Bool.eq_false_iff.mpr hframe
    have hlenDummy : ((if n == 0 then [false] else []).length == n) = false := by
      cases n <;> rfl
    simp only [hframeF, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hlenDummy,
      Option.isSome_none, Bool.and_false]

/-- Running `etmToMACForger E tagBound adversary` in `M.sufCmaGame` produces the exact same
winning distribution as running `adversary` in `(encryptThenMAC E M hctLen).ciGame` whenever
`tagBound n` bounds all MAC tag lengths on `n`-bit ciphertexts under supported keys at security
parameter `n`. -/
theorem eval_sufCmaGame_etmToMACForger (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    ProbComp.eval (M.sufCmaGame (etmToMACForger E tagBound adversary) n) =
      ProbComp.eval ((encryptThenMAC E M hctLen).ciGame adversary n) := by
  simp only [MACScheme.sufCmaGame, SymmetricCipher.ciGame, etmToMACForger,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbOracleComp.eval_run_interpret]
  have hinner (km : List Bool) :
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
        (do
          let ke ← ProbOracleComp.sample (E.keyGen n)
          (fun out : List Bool × Unit =>
            if (encPair encBits encBits (unframe out.1, dropFrame out.1) == out.1) &&
                (E.decrypt n ke (unframe out.1)).isSome then
              (unframe out.1, dropFrame out.1)
            else
              (if n == 0 then [false] else [], [])) <$>
            (OracleComp.interpret
              (ProbOracleComp.handler
                (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
                (etmToMACHandler E n (tagBound n) ke))
              (adversary n [])).run ())).run []).bind
        (fun out => PMF.pure
          ((out.1.1.length == n) && !out.2.contains out.1 && M.verify km out.1.1 out.1.2)) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
            (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
          ((OracleComp.interpret
            (ProbOracleComp.handler
              (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
              (etmToMACHandler E n (tagBound n) ke))
            (adversary n [])).run ())).run []).bind
          (fun out => PMF.pure
            (let pair :=
              if (encPair encBits encBits (unframe out.1.1, dropFrame out.1.1) == out.1.1) &&
                  (E.decrypt n ke (unframe out.1.1)).isSome then
                (unframe out.1.1, dropFrame out.1.1)
              else
                (if n == 0 then [false] else [], [])
             (pair.1.length == n) && !out.2.contains pair && M.verify km pair.1 pair.2))) := by
    rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
    congr 1; funext ke
    rw [OracleComp.interpret_map, StateT.run_map]
    simp only [_root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  simp only [hinner]
  rw [PMF.bind_comm]
  have hkeyGen : ProbComp.eval ((encryptThenMAC E M hctLen).keyGen n) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  refine PMF.bind_congr_on_support _ _ _ fun km hkm => ?_
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  conv_lhs =>
    rhs; ext x
    rw [etm_sufCma_win_eq_ci_win E M hctLen n ke km x.1 x.2.2]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × List (List Bool × List Bool)) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (M.signingPairOracle km q s)))
        (etmToMACHandler E n (tagBound n) ke q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((encryptThenMAC E M hctLen).ciEncryptionOracle n
        (encPair encBits encBits (ke, km)) q s))
    (represent := fun s : Unit × List (List Bool × List Bool) =>
      s.2.map (encPair encBits encBits))
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨⟨⟩, queriedPairs⟩
      have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      unfold etmToMACHandler SymmetricCipher.ciEncryptionOracle
      dsimp only [encryptThenMAC]
      rw [hunframe_k, hdrop_k]
      by_cases hlenEq : (msg.length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          ProbOracleComp.run_interpret_sample, Probability.PMF.monad_bind_eq_bind,
          PMF.bind_map, Function.comp_def, PMF.map_bind, ProbComp.eval_bind,
          ProbComp.eval_pure, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro c hc
        have hcLen : c.length = n := hctLen n ke hke msg (beq_iff_eq.mp hlenEq) c hc
        simp only [OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          _root_.PMF.monad_map_eq_map, MACScheme.signingPairOracle, ProbComp.eval_bind,
          ProbComp.eval_pure]
        dsimp only [StateT.run]
        simp only [PMF.map_bind, PMF.pure_map, PMF.pure_bind]
        apply PMF.bind_congr_on_support
        intro tag htag
        rw [List.take_of_length_le (htagBound km hkm c hcLen tag htag)]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    (adversary n []) ((), [])
  dsimp only [List.map] at hsim
  rw [← hsim, PMF.bind_map, Function.comp_def]
  rfl

/-- **Quantitative Ciphertext-Integrity to SUF-CMA equality** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 1, printed pp. 367–368): when `tagBound n` bounds all MAC tag lengths on `n`-bit
ciphertexts under supported keys at security parameter `n`, the ciphertext-integrity winning
probability of `adversary` against `encryptThenMAC E M hctLen` equals the SUF-CMA winning
probability of `etmToMACForger E tagBound adversary` against `M`. -/
theorem succProbability_ciGame_encryptThenMAC_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval ((encryptThenMAC E M hctLen).ciGame adversary n)) =
      Game.succProbability
        (ProbComp.eval (M.sufCmaGame (etmToMACForger E tagBound adversary) n)) := by
  rw [eval_sufCmaGame_etmToMACForger E M hctLen tagBound adversary n htagBound]

/-- **Quantitative Ciphertext-Integrity to SUF-CMA bound** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 1, printed pp. 367–368). -/
theorem succProbability_ciGame_encryptThenMAC_le (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (tagBound : ℕ → ℕ) (adversary : CIAdversary) (n : ℕ)
    (htagBound : ∀ km ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ c, c.length = n →
      ∀ tag ∈ (ProbComp.eval (M.sign km c)).support, tag.length ≤ tagBound n) :
    Game.succProbability (ProbComp.eval ((encryptThenMAC E M hctLen).ciGame adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (M.sufCmaGame (etmToMACForger E tagBound adversary) n)) :=
  le_of_eq (succProbability_ciGame_encryptThenMAC_eq E M hctLen tagBound adversary n htagBound)

/-! #### IND-CPA Reduction for Theorem 9.2 -/

/-- Open stateful handler that simulates the `cpaEncryptionOracle` of `encryptThenMAC E M` inside
`E.cpaGame` ([BonehShoup2023], Section 9.4.1, Theorem 9.2, Part 2): on a valid pair of `n`-bit
messages `request.2`, it forwards `request` to the external CPA encryption oracle of `E`
(truncating the returned ciphertext `c` to `n` bits), computes `tag ← M.sign km c`, and returns
`encPair encBits encBits (c, tag)`. -/
noncomputable def etmToCPAHandler (M : MACScheme) (n : ℕ) (km : List Bool)
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let c ← List.take n <$> ProbOracleComp.query ((), request.2)
      (fun tag => (encPair encBits encBits (c, tag), ())) <$>
        ProbOracleComp.sample (M.sign km c)
    else
      pure ([], ())

/-- IND-CPA reduction `etmToCPAAdversary` for `encryptThenMAC E M` ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): samples a secret MAC key `km ← M.keyGen n` privately and
runs `adversary n []` against `etmToCPAHandler M n km`. -/
noncomputable def etmToCPAAdversary (M : MACScheme) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => do
    let km ← ProbOracleComp.sample (M.keyGen n)
    Prod.fst <$> (OracleComp.interpret
      (ProbOracleComp.handler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (etmToCPAHandler M n km))
      (adversary n [])).run ()

private theorem isOraclePPTOn_etmToCPAHandler (M : MACScheme) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinite Unit) encBits) (encFinite Unit)))
      (encPair encBits (encFinite Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        etmToCPAHandler M pair.1.1.1 pair.1.2 pair.2.1 pair.2.2) := by
  let ECaller := encPair (encPair encUnary encBits) encBits
  let EIn := encPair ECaller (encPair (encPair (encFinite Unit) encBits) (encFinite Unit))
  unfold etmToCPAHandler
  have hcond : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        ((unframe p.2.1.2).length == p.1.1.1) && ((dropFrame p.2.1.2).length == p.1.1.1))
      EIn encBool := by
    dsimp only [EIn, ECaller]; polytime
  have hqReq : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => p.2.1.2)
      EIn encBits := by
    dsimp only [EIn, ECaller]; fun_prop
  have hqLim : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => p.1.1.1)
      EIn encUnary := by
    dsimp only [EIn, ECaller]; fun_prop
  have hq : IsOraclePPTOn (Operation := Unit) EIn encBits
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        List.take p.1.1.1 <$> ProbOracleComp.query ((), p.2.1.2)) :=
    IsOraclePPTOn.query_take (Operation := Unit) () hqReq hqLim
  have hsignArg : ComputableTidilyInPolyTime
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (q.1.1.2, q.2))
      (encPair EIn encBits) (encPair encBits encBits) := by
    dsimp only [EIn, ECaller]; fun_prop
  have hsign : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        ProbOracleComp.sample (M.sign q.1.1.2 q.2)) :=
    (M.sign_ppt.preprocess hsignArg.computableInPolyTime).isOraclePPTOn (Operation := Unit)
  have hpairArg : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (r.1.2, r.2))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits encBits) := by
    fun_prop
  have hmap : ComputableTidilyInPolyTime
      (fun r : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) ×
          List Bool =>
        (encPair encBits encBits (r.1.2, r.2), ()))
      (encPair (encPair EIn encBits) encBits)
      (encPair encBits (encFinite Unit)) :=
    ComputableTidilyInPolyTime.prod hpairArg.encoded (ComputableTidilyInPolyTime.const ())
  have hsignMap : IsOraclePPTOn (Operation := Unit) (encPair EIn encBits)
      (encPair encBits (encFinite Unit))
      (fun q : (((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool =>
        (fun tag => (encPair encBits encBits (q.2, tag), ())) <$>
          ProbOracleComp.sample (M.sign q.1.1.2 q.2)) :=
    hsign.map_with hmap
  have hyes : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinite Unit))
      (fun p : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) => do
        let c ← List.take p.1.1.1 <$> ProbOracleComp.query ((), p.2.1.2)
        (fun tag => (encPair encBits encBits (c, tag), ())) <$>
          ProbOracleComp.sample (M.sign p.1.2 c)) :=
    hq.bind_with hsignMap
  have hno : IsOraclePPTOn (Operation := Unit) EIn (encPair encBits (encFinite Unit))
      (fun _ : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        pure ([], ())) :=
    (ComputableTidilyInPolyTime.const ([], ())).isPPTOn.isOraclePPTOn (Operation := Unit)
  exact IsOraclePPTOn.cond hcond hyes hno

/-- `etmToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_etmToCPAAdversary (M : MACScheme) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (etmToCPAAdversary M adversary) := by
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hkm : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (M.keyGen caller.1)) :=
    (M.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn (Operation := Unit)
  have hhandler := isOraclePPTOn_etmToCPAHandler M
  have hprepare : ComputableTidilyInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableTidilyInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        2 * pair.1.1.1 + cs * (2 * pair.1.2.length + pair.1.1.1 + 2) ^ ds + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; polytime
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBool (encFinite Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        etmToCPAHandler M caller.1.1 caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ =>
        2 * caller.1.1 + cs * (2 * caller.2.length + caller.1.1 + 2) ^ ds + 2)
      hprepare hhandler (ComputableTidilyInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold etmToCPAHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨c, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := ProbOracleComp.mem_support_map hc
      have hcTake : (List.take caller.1.1 rawCt).length ≤ caller.1.1 :=
        List.length_take_le _ _
      obtain ⟨tag, htag, rfl⟩ := ProbOracleComp.mem_support_map hresult
      rw [ProbOracleComp.support_sample] at htag
      have htagLen := hlenSign (caller.2, List.take caller.1.1 rawCt) tag htag
      simp only [length_encPair, encBits_apply] at htagLen
      have htagBound : tag.length ≤ cs * (2 * caller.2.length + caller.1.1 + 2) ^ ds :=
        htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))
      refine ⟨trivial, ?_, by lia⟩
      simp only [length_encPair, encBits_apply]
      lia
    · have hresEq := ProbOracleComp.eq_of_mem_support_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by lia⟩
  have hrunMap : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun caller : (ℕ × List Bool) × List Bool =>
        Prod.fst <$> (OracleComp.interpret
          (ProbOracleComp.handler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (etmToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) :=
    hrun.map (ComputableTidilyInPolyTime.fst encBool (encFinite Unit))
  unfold etmToCPAAdversary
  exact (hkm.bind_with hrunMap).isOraclePPT

/-- Running `etmToCPAAdversary M adversary` in `E.cpaGame` at challenge bit `bit` produces the
exact same output distribution as running `adversary` in
`(encryptThenMAC E M hctLen).cpaGame` at challenge bit `bit`. -/
theorem eval_cpaGame_etmToCPAAdversary (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) bit n) =
      ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary bit n) := by
  simp only [SymmetricCipher.cpaGame, etmToCPAAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret]
  have hkeyGen : ProbComp.eval ((encryptThenMAC E M hctLen).keyGen n) =
      (ProbComp.eval (E.keyGen n)).bind (fun ke =>
        (ProbComp.eval (M.keyGen n)).bind (fun km =>
          PMF.pure (encPair encBits encBits (ke, km)))) := by
    simp only [encryptThenMAC, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [hkeyGen]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  rw [OracleComp.interpret_bind, StateT.run_bind, ProbOracleComp.run_interpret_sample]
  simp only [Probability.PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun km _ => ?_
  rw [OracleComp.interpret_map, StateT.run_map]
  simp only [_root_.PMF.monad_map_eq_map, PMF.bind_map, Function.comp_def]
  rw [ProbOracleComp.run_interpret_run_interpret]
  simp only [PMF.bind_map, Function.comp_def]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : Unit × Unit) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m))
          (fun q s => ProbComp.eval (E.cpaEncryptionOracle n ke bit q s)))
        (etmToCPAHandler M n km q state.1)).run state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((encryptThenMAC E M hctLen).cpaEncryptionOracle n
        (encPair encBits encBits (ke, km)) bit q s))
    (represent := fun _ : Unit × Unit => ())
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨⟨⟩, ⟨⟩⟩
      have hunframe_k : unframe (encPair encBits encBits (ke, km)) = ke := by
        simp [encPair_apply, unframe_frame_append]
      have hdrop_k : dropFrame (encPair encBits encBits (ke, km)) = km := by
        simp [encPair_apply, dropFrame_frame_append]
      unfold etmToCPAHandler SymmetricCipher.cpaEncryptionOracle
      dsimp only [encryptThenMAC]
      rw [hunframe_k, hdrop_k]
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, OracleComp.interpret_bind, StateT.run_bind,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          ProbOracleComp.run_interpret_sample,
          _root_.PMF.monad_map_eq_map, Probability.PMF.monad_bind_eq_bind,
          ProbComp.eval_bind, ProbComp.eval_pure]
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmbLen : (if bit then dropFrame payload else unframe payload).length = n := by
          cases bit <;> simp [hlenEq]
        dsimp only [StateT.run]
        simp only [PMF.map_comp, PMF.map_bind, Function.comp_def,
          PMF.pure_map, PMF.pure_bind, PMF.bind_bind]
        apply PMF.bind_congr_on_support
        intro c hc
        rw [List.take_of_length_le (le_of_eq (hctLen n ke hke _ hmbLen c hc))]
        rfl
      · simp [hlenEq, OracleComp.interpret_pure, StateT.run_pure,
          Probability.PMF.monad_pure_eq_pure, ProbComp.eval_pure])
    (adversary n []) ((), ())
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'

/-- **Quantitative IND-CPA equality for Encrypt-then-MAC** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): the CPA distinguishing advantage of `adversary` against
`encryptThenMAC E M hctLen` equals the CPA distinguishing advantage of
`etmToCPAAdversary M adversary` against `E`. -/
theorem advantage_cpaGame_encryptThenMAC_eq (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (adversary : OracleDistinguisher) (n : ℕ) :
    Game.advantage
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary false n))
      (ProbComp.eval ((encryptThenMAC E M hctLen).cpaGame adversary true n)) =
    Game.advantage
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) false n))
      (ProbComp.eval (E.cpaGame (etmToCPAAdversary M adversary) true n)) := by
  rw [eval_cpaGame_etmToCPAAdversary E M hctLen adversary false n,
    eval_cpaGame_etmToCPAAdversary E M hctLen adversary true n]

/-! #### Asymptotic Security of Encrypt-then-MAC (Boneh–Shoup Theorem 9.2) -/

/-- **SUF-CMA security implies Ciphertext Integrity for Encrypt-then-MAC** ([BonehShoup2023],
Section 9.4.1, Theorem 9.2, Part 1, printed pp. 367–368): if `M` is strongly unforgeable
(`M.SUFCMA`), then `encryptThenMAC E M hctLen` satisfies `CiphertextIntegrity`. -/
theorem ciphertextIntegrity_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).CiphertextIntegrity := by
  obtain ⟨ck, dk, hlenKey⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  let tagBound : ℕ → ℕ := fun n => cs * (2 * (ck * (n + 1) ^ dk) + n + 2) ^ ds
  have htagBoundPoly : ComputableInPolyTime tagBound encUnary encUnary := by
    dsimp only [tagBound]; polytime
  have htagBound (n : ℕ) (km : List Bool) (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
       (c : List Bool) (hc : c.length = n) (tag : List Bool)
      (htag : tag ∈ (ProbComp.eval (M.sign km c)).support) : tag.length ≤ tagBound n := by
    have hkmLen := hlenKey n km hkm
    have htagLen := hlenSign (km, c) tag htag
    simp only [encUnary_apply, List.length_replicate, encBits_apply] at hkmLen
    simp only [length_encPair, encBits_apply, hc] at htagLen
    exact htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))
  apply SymmetricCipher.CiphertextIntegrity.of_negligible
  intro adversary hadversary
  have hmacNeg := hmac.negligible (etmToMACForger E tagBound adversary)
    (isOraclePPT_etmToMACForger E htagBoundPoly hadversary)
  refine hmacNeg.congr fun n => ?_
  exact (succProbability_ciGame_encryptThenMAC_eq E M hctLen tagBound adversary n
    (htagBound n)).symm

/-- **IND-CPA security transfers to Encrypt-then-MAC** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, Part 2, printed pp. 367–368): if `E` satisfies `INDCPA`, then
`encryptThenMAC E M hctLen` also satisfies `INDCPA`. -/
theorem indcpa_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E M hctLen).INDCPA := by
  intro adversary hadversary
  have hred := hcpa (etmToCPAAdversary M adversary) (isOraclePPT_etmToCPAAdversary M hadversary)
  refine hred.congr fun n => ?_
  exact (advantage_cpaGame_encryptThenMAC_eq E M hctLen adversary n).symm

/-- **Encrypt-then-MAC Authenticated Encryption Theorem** ([BonehShoup2023], Section 9.4.1,
Theorem 9.2, printed pp. 367–368): if `E` is `INDCPA`-secure and `M` is `SUFCMA`-secure, then
`encryptThenMAC E M hctLen` is an `AuthenticatedEncryption` cipher
(`INDCPA ∧ CiphertextIntegrity`). -/
theorem authenticatedEncryption_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).AuthenticatedEncryption :=
  ⟨indcpa_encryptThenMAC E M hctLen hcpa, ciphertextIntegrity_encryptThenMAC E M hctLen hmac⟩

/-- **Encrypt-then-MAC Adaptive Chosen-Ciphertext Security** ([BonehShoup2023], combining
Theorem 9.2 and Theorem 9.1): if `E` is `INDCPA`-secure and `M` is `SUFCMA`-secure, then
`encryptThenMAC E M hctLen` is `INDCCA`-secure. -/
theorem indcca_encryptThenMAC (E : SymmetricCipher) (M : MACScheme)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hcpa : E.INDCPA) (hmac : M.SUFCMA) :
    (encryptThenMAC E M hctLen).INDCCA :=
  (authenticatedEncryption_encryptThenMAC E M hctLen hcpa hmac).indcca

/-- **Encrypt-then-MAC with a PRF-based MAC is Authenticated Encryption** ([BonehShoup2023],
combining Theorem 6.2 and Theorem 9.2): if `E` is `INDCPA`-secure and `family` is a uniform
`PseudorandomFunction`, then `encryptThenMAC E (prfMAC family hprf.polyTime) hctLen` satisfies
`AuthenticatedEncryption`. -/
theorem authenticatedEncryption_encryptThenMAC_prfMAC (E : SymmetricCipher)
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E (prfMAC family hprf.polyTime) hctLen).AuthenticatedEncryption :=
  authenticatedEncryption_encryptThenMAC E (prfMAC family hprf.polyTime) hctLen hcpa
    hprf.sufCma_prfMAC

/-- **Encrypt-then-MAC with a PRF-based MAC is IND-CCA secure** ([BonehShoup2023], combining
Theorem 6.2, Theorem 9.2, and Theorem 9.1): if `E` is `INDCPA`-secure and `family` is a uniform
`PseudorandomFunction`, then `encryptThenMAC E (prfMAC family hprf.polyTime) hctLen` satisfies
`INDCCA`. -/
theorem indcca_encryptThenMAC_prfMAC (E : SymmetricCipher)
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hctLen : ∀ n ke, ke ∈ (ProbComp.eval (E.keyGen n)).support →
      ∀ msg, msg.length = n →
      ∀ c ∈ (ProbComp.eval (E.encrypt n ke msg)).support, c.length = n)
    (hcpa : E.INDCPA) :
    (encryptThenMAC E (prfMAC family hprf.polyTime) hctLen).INDCCA :=
  (authenticatedEncryption_encryptThenMAC_prfMAC E hprf hctLen hcpa).indcca

end Cslib.Crypto
