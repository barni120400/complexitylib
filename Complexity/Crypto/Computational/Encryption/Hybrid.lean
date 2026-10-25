/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Basic
public import Complexity.Crypto.Computational.Encryption.PolyTime
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# KEM–DEM hybrid public-key encryption

A Key Encapsulation Mechanism (KEM) samples a public/secret key pair `(pk, sk) ← keyGen n` and
encapsulates a symmetric key `(k, ctKem) ← encaps n pk` ([BonehShoup2023], Section 11.3.1,
Definition 11.3). Its IND-CPA security (`KEMINDCPA`, Attack Game 11.4 and Definition 11.4) asks
that replacing the encapsulated key `k` with an independent uniform `n`-bit key
`BitString.sampleList n` is computationally indistinguishable to every uniform strict PPT
distinguisher receiving `(pk, (k, ctKem))`.

A Data Encapsulation Mechanism (DEM) for bit messages encrypts a single challenge bit under a
fresh uniform `n`-bit key (`demGame`, Attack Game 2.1 / 11.3; `DEMOneTimeINDCPA`).

Combining `encaps` with `encryptSym` produces the hybrid public-key encryption scheme
`hybridEncrypt encaps encryptSym` (`hybridDecrypt decaps decryptSym`, Definition 11.5). By
Boneh and Shoup's Theorem 11.2, if the KEM is IND-CPA secure and the DEM is one-time IND-CPA
secure, then `hybridEncrypt encaps encryptSym` is IND-CPA secure (`KEMINDCPA.hybrid_indcpa`).
We formalize both the two-distinguisher triangle bound (`advantage_hybridGame_le`) and the
single hidden-bit KEM distinguisher bound (`advantage_hybridGame_le_two_mul`), together with a
non-vacuous one-time pad DEM instantiation (`otpEncrypt`, `otpDecrypt`,
`demOneTimeINDCPA_otpEncrypt`, `KEMINDCPA.hybrid_otpEncrypt_indcpa`).

## Main definitions

* `Cslib.Crypto.Encryption.kemRealGame`, `Cslib.Crypto.Encryption.kemIdealGame`,
  `Cslib.Crypto.Encryption.KEMINDCPA`: real and ideal KEM IND-CPA experiments and security.
* `Cslib.Crypto.Encryption.demGame`, `Cslib.Crypto.Encryption.DEMOneTimeINDCPA`: one-time
  symmetric bit-encryption experiment and security.
* `Cslib.Crypto.Encryption.hybridEncrypt`, `Cslib.Crypto.Encryption.hybridDecrypt`: KEM–DEM
  hybrid encryption and deterministic decryption.
* `Cslib.Crypto.Encryption.hybridIdealGame`: intermediate game replacing the encapsulated key
  with an independent uniform `n`-bit key.
* `Cslib.Crypto.Encryption.hybridToKEMDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToKEMHiddenBitDistinguisher`,
  `Cslib.Crypto.Encryption.hybridToDEMAdversary`: the certified uniform reductions.
* `Cslib.Crypto.Encryption.otpEncrypt`, `Cslib.Crypto.Encryption.otpDecrypt`: one-time pad
  single-bit DEM.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_kemRealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_kemIdealGame`,
  `Cslib.Crypto.Encryption.isPPTOn_demGame`,
  `Cslib.Crypto.Encryption.isPPTOn_hybridEncrypt`,
  `Cslib.Crypto.Encryption.computableInPolyTime_hybridDecrypt`: polynomial-time certificates.
* `Cslib.Crypto.Encryption.hybridDecrypt_encPair`,
  `Cslib.Crypto.Encryption.hybridDecrypt_hybridEncrypt`: exact decryption correctness.
* `Cslib.Crypto.Encryption.advantage_hybridGame_le`,
  `Cslib.Crypto.Encryption.advantage_hybridGame_le_two_mul`: quantitative Boneh–Shoup
  Theorem 11.2 reductions.
* `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_indcpa`: asymptotic Boneh–Shoup Theorem 11.2.
* `Cslib.Crypto.Encryption.demOneTimeINDCPA_otpEncrypt`,
  `Cslib.Crypto.Encryption.KEMINDCPA.hybrid_otpEncrypt_indcpa`: unconditional one-time pad DEM
  security and the KEM-to-PKE corollary.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 2.2 (Attack Game 2.1) and Section 11.3
  (Definitions 11.3–11.5, Attack Games 11.3–11.4, Theorem 11.2).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal

@[local fun_prop]
private theorem computableTidilyInPolyTime_encPair_bits {α : Type} {input : α ↪ List Bool}
    {f g : α → List Bool}
    (hf : ComputableTidilyInPolyTime f input encBits)
    (hg : ComputableTidilyInPolyTime g input encBits) :
    ComputableTidilyInPolyTime (fun a => encPair encBits encBits (f a, g a)) input encBits :=
  (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp (hf.prod hg)

@[local fun_prop]
private theorem computableTidilyInPolyTime_encPair_bits_pair {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool} {g : α → List Bool × List Bool}
    (hf : ComputableTidilyInPolyTime f input encBits)
    (hg : ComputableTidilyInPolyTime g input (encPair encBits encBits)) :
    ComputableTidilyInPolyTime
      (fun a => encPair encBits (encPair encBits encBits) (f a, g a)) input encBits :=
  (ComputableTidilyInPolyTime.encode (encPair encBits (encPair encBits encBits))).comp
    (hf.prod hg)

@[local fun_prop]
private theorem computableTidilyInPolyTime_nil_bits {α : Type} {input : α ↪ List Bool} :
    ComputableTidilyInPolyTime (fun _ : α => ([] : List Bool)) input encBits :=
  ComputableTidilyInPolyTime.const []

@[local fun_prop]
private theorem computableTidilyInPolyTime_unframe {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool} (hf : ComputableTidilyInPolyTime f input encBits) :
    ComputableTidilyInPolyTime (fun a => unframe (f a)) input encBits :=
  ComputableTidilyInPolyTime.unframe.comp hf

@[local fun_prop]
private theorem computableTidilyInPolyTime_dropFrame {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool} (hf : ComputableTidilyInPolyTime f input encBits) :
    ComputableTidilyInPolyTime (fun a => dropFrame (f a)) input encBits :=
  ComputableTidilyInPolyTime.dropFrame.comp hf

@[local fun_prop]
private theorem computableInPolyTime_encPair_bits {α : Type} {input : α ↪ List Bool}
    {f g : α → List Bool}
    (hf : ComputableInPolyTime f input encBits)
    (hg : ComputableInPolyTime g input encBits) :
    ComputableInPolyTime (fun a => encPair encBits encBits (f a, g a)) input encBits :=
  ComputableInPolyTime.encoding_comp (hf.prod hg)

@[local fun_prop]
private theorem computableInPolyTime_unframe {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool} (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => unframe (f a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.unframe.comp hf.tidy)

@[local fun_prop]
private theorem computableInPolyTime_dropFrame {α : Type} {input : α ↪ List Bool}
    {f : α → List Bool} (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a => dropFrame (f a)) input encBits :=
  .of_tidy (ComputableTidilyInPolyTime.dropFrame.comp hf.tidy)

/-! ### Key Encapsulation Mechanisms -/

/-- The real KEM IND-CPA experiment ([BonehShoup2023], Section 11.3.1, Attack Game 11.4, `b = 0`):
sample `(pk, sk) ← keyGen n` and `(k, ctKem) ← encaps n pk`, and pass the encoded triple
`(pk, (k, ctKem))` to `distinguisher n`. -/
def kemRealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  distinguisher n (encPair encBits (encPair encBits encBits) (keys.1, encapsulated))

/-- The ideal KEM IND-CPA experiment ([BonehShoup2023], Section 11.3.1, Attack Game 11.4, `b = 1`):
sample `(pk, sk) ← keyGen n`, `(k, ctKem) ← encaps n pk`, and an independent uniform `n`-bit key
`kIdeal ← BitString.sampleList n`, and pass `(pk, (kIdeal, ctKem))` to `distinguisher n`. -/
noncomputable def kemIdealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (distinguisher : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let encapsulated ← encaps n keys.1
  let kIdeal ← BitString.sampleList n
  distinguisher n
    (encPair encBits (encPair encBits encBits) (keys.1, (kIdeal, encapsulated.2)))

/-- The real KEM IND-CPA experiment is uniform strict PPT when key generation, encapsulation, and
the distinguisher have native certificates. -/
@[fun_prop]
theorem isPPTOn_kemRealGame {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    {distinguisher : Distinguisher} (hdist : IsPPT encBool distinguisher)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input encBool (fun a => kemRealGame keyGen encaps distinguisher (n a)) := by
  have hn' := hn.tidy
  unfold kemRealGame
  ppt

/-- The ideal KEM IND-CPA experiment is uniform strict PPT when key generation, encapsulation, and
the distinguisher have native certificates. -/
@[fun_prop]
theorem isPPTOn_kemIdealGame {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    {distinguisher : Distinguisher} (hdist : IsPPT encBool distinguisher)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) :
    IsPPTOn input encBool (fun a => kemIdealGame keyGen encaps distinguisher (n a)) := by
  have hn' := hn.tidy
  unfold kemIdealGame
  ppt

/-- IND-CPA security for a Key Encapsulation Mechanism ([BonehShoup2023], Section 11.3.1,
Definition 11.4 / Attack Game 11.4): every uniform strict PPT distinguisher has negligible
advantage between `kemRealGame` and `kemIdealGame`. -/
def KEMINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)) : Prop :=
  Game.Indistinguishable
    (fun D n => ProbComp.eval (kemRealGame keyGen encaps D n))
    (fun D n => ProbComp.eval (kemIdealGame keyGen encaps D n))
    (IsPPT encBool)

/-! ### One-Time Symmetric Bit Encryption (DEM) -/

/-- The one-time symmetric chosen-plaintext experiment for bit encryption ([BonehShoup2023],
Section 2.2, Attack Game 2.1 / Section 11.3.1, Attack Game 11.3): sample a uniform `n`-bit key
`k ← BitString.sampleList n`, invoke `adversary.choose n []` (no public key), encrypt the selected
challenge bit under `encryptSym n k`, and pass the saved state and challenge ciphertext to
`adversary.guess n`. -/
noncomputable def demGame (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← BitString.sampleList n
  let choice ← adversary.choose n []
  let ciphertext ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 ciphertext

/-- The one-time symmetric experiment has a strict polynomial clock when symmetric encryption and
both adversary stages have native certificates. -/
@[fun_prop]
theorem isPPTOn_demGame {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    {adversary : Adversary} (hadversary : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hbit : ComputableInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => demGame encryptSym adversary (bit a) (n a)) := by
  have hn' := hn.tidy
  have hbit' := hbit.tidy
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold demGame
  ppt

/-- One-time symmetric IND-CPA security for bit encryption ([BonehShoup2023], Section 2.2 /
Section 11.3.1, Attack Game 11.3): every uniform strict PPT `Encryption.Adversary` has negligible
distinguishing advantage between `demGame encryptSym adversary false` and
`demGame encryptSym adversary true`. -/
def DEMOneTimeINDCPA (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (demGame encryptSym adversary false n))
    (fun adversary n => ProbComp.eval (demGame encryptSym adversary true n))
    Adversary.IsPPT

/-! ### Hybrid Encryption Construction and Correctness -/

/-- KEM–DEM hybrid encryption ([BonehShoup2023], Section 11.3.1, Definition 11.5): encapsulate a
symmetric key `(k, ctKem) ← encaps n pk`, encrypt the plaintext bit under `k` via
`ctDem ← encryptSym n k bit`, and encode `(ctKem, ctDem)` using `encPair encBits encBits`. -/
def hybridEncrypt (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (n : ℕ) (pk : List Bool) (bit : Bool) : ProbComp (List Bool) := do
  let encapsulated ← encaps n pk
  let ctDem ← encryptSym n encapsulated.1 bit
  return encPair encBits encBits (encapsulated.2, ctDem)

/-- Deterministic KEM–DEM hybrid decryption ([BonehShoup2023], Section 11.3.1, Definition 11.5):
decode the hybrid ciphertext `ct` into `ctKem = unframe ct` and `ctDem = dropFrame ct`,
decapsulate `k = decaps n sk ctKem`, and return `decryptSym n k ctDem`. -/
def hybridDecrypt (decaps : ℕ → List Bool → List Bool → List Bool)
    (decryptSym : ℕ → List Bool → List Bool → Bool)
    (n : ℕ) (sk ct : List Bool) : Bool :=
  decryptSym n (decaps n sk (unframe ct)) (dropFrame ct)

/-- Hybrid encryption is uniform strict PPT when encapsulation and symmetric encryption are. -/
@[fun_prop]
theorem isPPTOn_hybridEncrypt {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => hybridEncrypt encaps encryptSym p.1 p.2.1 p.2.2) := by
  unfold hybridEncrypt
  ppt

/-- Hybrid decryption is computable in polynomial time when decapsulation and symmetric decryption
are computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_hybridDecrypt {decaps : ℕ → List Bool → List Bool → List Bool}
    {decryptSym : ℕ → List Bool → List Bool → Bool}
    (hdecaps : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decaps p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hdecryptSym : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decryptSym p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hybridDecrypt decaps decryptSym p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  have hdecaps' := hdecaps.tidy
  have hdecryptSym' := hdecryptSym.tidy
  unfold hybridDecrypt
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- Hybrid decryption on an encoded ciphertext pair `(ctKem, ctDem)` decapsulates `ctKem` and
decrypts `ctDem` under the resulting key. -/
theorem hybridDecrypt_encPair (decaps : ℕ → List Bool → List Bool → List Bool)
    (decryptSym : ℕ → List Bool → List Bool → Bool)
    (n : ℕ) (sk ctKem ctDem : List Bool) :
    hybridDecrypt decaps decryptSym n sk (encPair encBits encBits (ctKem, ctDem)) =
      decryptSym n (decaps n sk ctKem) ctDem := by
  simp [hybridDecrypt, encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append]

/-- **Hybrid decryption correctness**: if `decaps n sk` recovers the encapsulated key `k` on every
supported output `(k, ctKem)` of `encaps n pk`, and `decryptSym n k` recovers `bit` on every
supported output of `encryptSym n k bit`, then `hybridDecrypt` recovers `bit` on every supported
ciphertext of `hybridEncrypt`. -/
theorem hybridDecrypt_hybridEncrypt
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {decaps : ℕ → List Bool → List Bool → List Bool}
    {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decryptSym : ℕ → List Bool → List Bool → Bool}
    {n : ℕ} {pk sk ct : List Bool} {bit : Bool}
    (hkem : ∀ k ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support →
      decaps n sk ctKem = k)
    (hdem : ∀ k ctDem, (∃ ctKem, (k, ctKem) ∈ (ProbComp.eval (encaps n pk)).support) →
      ctDem ∈ (ProbComp.eval (encryptSym n k bit)).support →
      decryptSym n k ctDem = bit)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt encaps encryptSym n pk bit)).support) :
    hybridDecrypt decaps decryptSym n sk ct = bit := by
  simp only [hybridEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  rcases hct with ⟨⟨k, ctKem⟩, hkc, ctDem, hdemSupp, rfl⟩
  rw [hybridDecrypt_encPair, hkem k ctKem hkc]
  exact hdem k ctDem ⟨ctKem, hkc⟩ hdemSupp

/-! ### Boneh–Shoup Theorem 11.2 Reductions and Asymptotic Security -/

/-- The intermediate hybrid game $G_1$ ([BonehShoup2023], Section 11.3.2, proof of Theorem 11.2):
identical to `Encryption.game keyGen (hybridEncrypt encaps encryptSym)` except that the symmetric
key passed to `encryptSym` is an independent uniform `n`-bit key `kIdeal ← BitString.sampleList n`
rather than `encapsulated.1`. -/
noncomputable def hybridIdealGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let encapsulated ← encaps n keys.1
  let kIdeal ← BitString.sampleList n
  let ctDem ← encryptSym n kIdeal (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (encPair encBits encBits (encapsulated.2, ctDem))

/-- Direct per-bit KEM distinguisher $D_{\mathrm{kem}, b}$ constructed from an
`Encryption.Adversary` and DEM encryption `encryptSym` ([BonehShoup2023], proof of Theorem 11.2):
given an encoded KEM challenge `(pk, (k, ctKem))`, run `adversary.choose n pk`, encrypt the
`bit`-selected message under `k`, and run `adversary.guess` on `(ctKem, ctDem)`. -/
def hybridToKEMDistinguisher
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) : Distinguisher := fun n challenge => do
  let pk := unframe challenge
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  let choice ← adversary.choose n pk
  let ctDem ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (encPair encBits encBits (ctKem, ctDem))

/-- Single hidden-bit KEM distinguisher $D_{\mathrm{kem}}$ ([BonehShoup2023], Section 11.3.2,
proof of Theorem 11.2): given an encoded KEM challenge `(pk, (k, ctKem))`, run
`adversary.choose n pk`, sample a fair challenge bit `bit ← ProbComp.uniform Bool`, encrypt the
selected message under `k`, run `adversary.guess`, and return `guess ^^ bit`. -/
noncomputable def hybridToKEMHiddenBitDistinguisher
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) : Distinguisher := fun n challenge => do
  let pk := unframe challenge
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  let choice ← adversary.choose n pk
  let bit ← ProbComp.uniform Bool
  let ctDem ← encryptSym n k (if bit then choice.1.2 else choice.1.1)
  let guess ← adversary.guess n choice.2 (encPair encBits encBits (ctKem, ctDem))
  return guess ^^ bit

/-- Two-stage DEM adversary $B_{\mathrm{dem}}$ constructed from `keyGen`, `encaps`, and a hybrid
`Encryption.Adversary` ([BonehShoup2023], Section 11.3.2, proof of Theorem 11.2): stage 1 samples
`(pk, sk) ← keyGen n` and `(k, ctKem) ← encaps n pk`, runs `adversary.choose n pk`, and saves
`encPair encBits encBits (ctKem, choice.2)`; stage 2 combines `ctKem` with the DEM challenge
ciphertext `ctDem` and runs `adversary.guess`. -/
def hybridToDEMAdversary (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (adversary : Adversary) : Adversary where
  choose n _ := do
    let keys ← keyGen n
    let choice ← adversary.choose n keys.1
    let encapsulated ← encaps n keys.1
    return (choice.1, encPair encBits encBits (encapsulated.2, choice.2))
  guess n state ctDem :=
    adversary.guess n (dropFrame state) (encPair encBits encBits (unframe state, ctDem))

/-- `hybridToKEMDistinguisher` is uniform strict PPT whenever symmetric encryption and the hybrid
adversary are. -/
theorem isPPT_hybridToKEMDistinguisher
    {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {adversary : Adversary}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hadversary : adversary.IsPPT) (bit : Bool) :
    IsPPT encBool (hybridToKEMDistinguisher encryptSym adversary bit) := by
  have h1 : IsPPTOn (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits)
      (fun p => adversary.choose p.1 (unframe p.2)) :=
    hadversary.choose.preprocess (by fun_prop) (by fun_prop)
  have h2 : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × (Bool × Bool) × List Bool =>
        (p.1.1, unframe (dropFrame p.1.2), if bit then p.2.1.2 else p.2.1.1))
      (encPair (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits))
      (encPair encUnary (encPair encBits encBool)) := by
    cases bit <;> fun_prop
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Bool × Bool) × List Bool) × List Bool =>
        (p.1.1.1, p.1.2.2, encPair encBits encBits (dropFrame (dropFrame p.1.1.2), p.2)))
      (encPair
        (encPair (encPair encUnary encBits) (encPair (encPair encBool encBool) encBits))
        encBits)
      (encPair encUnary (encPair encBits encBits)) := by
    fun_prop
  unfold IsPPT hybridToKEMDistinguisher
  exact h1.bind_with
    ((hencryptSym.preprocess h2.computableInPolyTime).bind_with
      (hadversary.guess.preprocess h3.computableInPolyTime))

/-- `hybridToKEMHiddenBitDistinguisher` is uniform strict PPT whenever symmetric encryption and the
hybrid adversary are. -/
theorem isPPT_hybridToKEMHiddenBitDistinguisher
    {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {adversary : Adversary}
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2))
    (hadversary : adversary.IsPPT) :
    IsPPT encBool (hybridToKEMHiddenBitDistinguisher encryptSym adversary) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair (encPair encBool encBool) encBits)
  let E2 := encPair E1 encBool
  let E3 := encPair E2 encBits
  let E4 := encPair E3 encBool
  have h1 : IsPPTOn E0 (encPair (encPair encBool encBool) encBits)
      (fun p => adversary.choose p.1 (unframe p.2)) := by
    dsimp only [E0]; exact hadversary.choose.preprocess (by fun_prop) (by fun_prop)
  have h2 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × (Bool × Bool) × List Bool) × Bool =>
        (p.1.1.1, unframe (dropFrame p.1.1.2), if p.2 then p.1.2.1.2 else p.1.2.1.1))
      E2 (encPair encUnary (encPair encBits encBool)) := by
    dsimp only [E2, E1, E0]; fun_prop
  have h3 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × (Bool × Bool) × List Bool) × Bool) × List Bool =>
        (p.1.1.1.1, p.1.1.2.2, encPair encBits encBits (dropFrame (dropFrame p.1.1.1.2), p.2)))
      E3 (encPair encUnary (encPair encBits encBits)) := by
    dsimp only [E3, E2, E1, E0]; fun_prop
  have h4 : ComputableTidilyInPolyTime
      (fun p : ((((ℕ × List Bool) × (Bool × Bool) × List Bool) × Bool) × List Bool) × Bool =>
        p.2 ^^ p.1.1.2)
      E4 encBool := by
    dsimp only [E4, E3, E2, E1, E0]; fun_prop
  unfold IsPPT hybridToKEMHiddenBitDistinguisher
  exact h1.bind_with
    ((isPPTOn_uniform_bool E1).bind_with
      ((hencryptSym.preprocess h2.computableInPolyTime).bind_with
        ((hadversary.guess.preprocess h3.computableInPolyTime).bind_with h4.isPPTOn)))

/-- `hybridToDEMAdversary` is an admissible uniform strict PPT `Encryption.Adversary` whenever key
generation, encapsulation, and the hybrid adversary are. -/
theorem isPPT_hybridToDEMAdversary
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {adversary : Adversary}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hadversary : adversary.IsPPT) :
    (hybridToDEMAdversary keyGen encaps adversary).IsPPT := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 (encPair encBits encBits)
  let E2 := encPair E1 (encPair (encPair encBool encBool) encBits)
  let E3 := encPair E2 (encPair encBits encBits)
  have h1 : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.1) E0 encUnary := by
    dsimp only [E0]; fun_prop
  have h2 : IsPPTOn E1 (encPair (encPair encBool encBool) encBits)
      (fun p => adversary.choose p.1.1 p.2.1) := by
    dsimp only [E1, E0]; exact hadversary.choose.preprocess (by fun_prop) (by fun_prop)
  have h3 : ComputableTidilyInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool × List Bool) × (Bool × Bool) × List Bool =>
        (p.1.1.1, p.1.2.1))
      E2 (encPair encUnary encBits) := by
    dsimp only [E2, E1, E0]; fun_prop
  have h4 : ComputableTidilyInPolyTime
      (fun p : (((ℕ × List Bool) × List Bool × List Bool) × (Bool × Bool) × List Bool) ×
          List Bool × List Bool =>
        (p.1.2.1, encPair encBits encBits (p.2.2, p.1.2.2)))
      E3 (encPair (encPair encBool encBool) encBits) := by
    dsimp only [E3, E2, E1, E0]; fun_prop
  have h5 : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool × List Bool =>
        (p.1, dropFrame p.2.1, encPair encBits encBits (unframe p.2.1, p.2.2)))
      (encPair encUnary (encPair encBits encBits))
      (encPair encUnary (encPair encBits encBits)) := by
    fun_prop
  refine ⟨?_, hadversary.guess.preprocess h5.computableInPolyTime⟩
  unfold Probability.IsPPT hybridToDEMAdversary
  exact (hkeyGen.preprocess h1.computableInPolyTime).bind_with
    (h2.bind_with
      ((hencaps.preprocess h3.computableInPolyTime).bind_with h4.isPPTOn))

/-- In the real KEM experiment, `hybridToKEMDistinguisher` reproduces the actual hybrid encryption
experiment `Encryption.game keyGen (hybridEncrypt encaps encryptSym)`. -/
@[simp] theorem eval_kemRealGame_hybridToKEMDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary bit) n) =
      ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary bit n) := by
  simp only [kemRealGame, hybridToKEMDistinguisher, game, hybridEncrypt, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext keys
  rw [PMF.bind_comm]

/-- In the ideal KEM experiment, `hybridToKEMDistinguisher` reproduces the intermediate game
`hybridIdealGame`. -/
@[simp] theorem eval_kemIdealGame_hybridToKEMDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary bit) n) =
      ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n) := by
  simp only [kemIdealGame, hybridToKEMDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind]
  congr 1; funext keys
  conv_lhs =>
    rhs; ext encapsulated
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the one-time symmetric DEM experiment, `hybridToDEMAdversary` reproduces the intermediate
game `hybridIdealGame`. -/
@[simp] theorem eval_demGame_hybridToDEMAdversary
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) bit n) =
      ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n) := by
  simp only [demGame, hybridToDEMAdversary, hybridIdealGame, encPair_apply, encBits_apply,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
    unframe_frame_append, dropFrame_frame_append]
  rw [PMF.bind_comm]
  congr 1; funext keys
  rw [PMF.bind_comm]
  congr 1; funext choice
  rw [PMF.bind_comm]

/-- In the real KEM experiment, `hybridToKEMHiddenBitDistinguisher` averages the two hybrid
chosen-message games, complementing the second. -/
theorem eval_kemRealGame_hybridToKEMHiddenBitDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    ProbComp.eval
      (kemRealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n) =
      (do
        let bit ← PMF.uniformOfFintype Bool
        (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary bit n)).map
          (fun guess => guess ^^ bit)) := by
  simp only [kemRealGame, hybridToKEMHiddenBitDistinguisher, game, hybridEncrypt, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.bind_bind,
    PMF.pure_bind, PMF.map_bind]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext keys
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  rw [PMF.bind_comm]
  rfl

/-- In the ideal KEM experiment, `hybridToKEMHiddenBitDistinguisher` averages the two intermediate
games `hybridIdealGame`, complementing the second. -/
theorem eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    ProbComp.eval
      (kemIdealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n) =
      (do
        let bit ← PMF.uniformOfFintype Bool
        (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary bit n)).map
          (fun guess => guess ^^ bit)) := by
  simp only [kemIdealGame, hybridToKEMHiddenBitDistinguisher, hybridIdealGame, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.map_bind]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext keys
  conv_lhs =>
    rhs; ext encapsulated
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext encapsulated
  rw [PMF.bind_comm]
  rfl

/-- Success probability of `hybridToKEMHiddenBitDistinguisher` in `kemRealGame` is one half plus
half the signed hybrid chosen-message gap. -/
theorem probability_kemRealGame_hybridToKEMHiddenBitDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (kemRealGame keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval
        (game keyGen (hybridEncrypt encaps encryptSym) adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))) / 2 := by
  rw [eval_kemRealGame_hybridToKEMHiddenBitDistinguisher]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, PMF.monad_bind_eq_bind,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- Success probability of `hybridToKEMHiddenBitDistinguisher` in `kemIdealGame` is one half plus
half the signed `hybridIdealGame` gap. -/
theorem probability_kemIdealGame_hybridToKEMHiddenBitDistinguisher
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (kemIdealGame keyGen encaps
        (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) : ℝ) =
      (1 + (Game.succProbability (ProbComp.eval
        (hybridIdealGame keyGen encaps encryptSym adversary false n)) : ℝ) -
        Game.succProbability (ProbComp.eval
          (hybridIdealGame keyGen encaps encryptSym adversary true n))) / 2 := by
  rw [eval_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  simp only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, PMF.monad_bind_eq_bind,
    PMF.bind_apply_toReal, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  norm_num [PMF.toReal_false_eq_one_sub]
  ring

/-- **Quantitative KEM–DEM reduction via two per-bit KEM distinguishers** ([BonehShoup2023],
Section 11.3.2, Theorem 11.2): the hybrid IND-CPA advantage is bounded by the sum of the KEM
advantages of `hybridToKEMDistinguisher encryptSym adversary false` and
`hybridToKEMDistinguisher encryptSym adversary true`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)) ≤
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary false) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary false) n)) +
      Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary true) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMDistinguisher encryptSym adversary true) n)) +
      Game.advantage
        (ProbComp.eval (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  simp only [eval_kemRealGame_hybridToKEMDistinguisher, eval_kemIdealGame_hybridToKEMDistinguisher,
    eval_demGame_hybridToDEMAdversary]
  have h1 := Game.advantage_triangle
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  have h2 := Game.advantage_triangle
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary false n))
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))
  rw [Game.advantage_comm
    (ProbComp.eval (hybridIdealGame keyGen encaps encryptSym adversary true n))
    (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n))] at h2
  exact (h1.trans (add_le_add le_rfl h2)).trans_eq (by ac_rfl)

/-- **Quantitative KEM–DEM reduction via a single hidden-bit KEM distinguisher** ([BonehShoup2023],
Section 11.3.2, Theorem 11.2): the hybrid IND-CPA advantage is at most twice the KEM advantage of
`hybridToKEMHiddenBitDistinguisher encryptSym adversary`, plus the DEM advantage of
`hybridToDEMAdversary keyGen encaps adversary`. -/
theorem advantage_hybridGame_le_two_mul
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encaps : ℕ → List Bool → ProbComp (List Bool × List Bool))
    (encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : Adversary) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary false n))
      (ProbComp.eval (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)) ≤
      2 * Game.advantage
        (ProbComp.eval
          (kemRealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n))
        (ProbComp.eval
          (kemIdealGame keyGen encaps (hybridToKEMHiddenBitDistinguisher encryptSym adversary) n)) +
      Game.advantage
        (ProbComp.eval (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) false n))
        (ProbComp.eval
          (demGame encryptSym (hybridToDEMAdversary keyGen encaps adversary) true n)) := by
  rw [eval_demGame_hybridToDEMAdversary, eval_demGame_hybridToDEMAdversary]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Game.coe_advantage,
    probability_kemRealGame_hybridToKEMHiddenBitDistinguisher,
    probability_kemIdealGame_hybridToKEMHiddenBitDistinguisher]
  have h := abs_sub_le
    ((Game.succProbability (ProbComp.eval
      (game keyGen (hybridEncrypt encaps encryptSym) adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (game keyGen (hybridEncrypt encaps encryptSym) adversary true n)))
    ((Game.succProbability (ProbComp.eval
      (hybridIdealGame keyGen encaps encryptSym adversary false n)) : ℝ) -
      Game.succProbability (ProbComp.eval
        (hybridIdealGame keyGen encaps encryptSym adversary true n))) 0
  have hscale (a b c d : ℝ) :
      2 * |(1 + a - b) / 2 - (1 + c - d) / 2| = |(a - b) - (c - d)| := by
    calc
      _ = |2 * ((1 + a - b) / 2 - (1 + c - d) / 2)| := by rw [abs_mul]; norm_num
      _ = _ := by congr 1; ring
  simpa only [hscale, sub_zero] using h

/-- **Boneh–Shoup Theorem 11.2 (IND-CPA security of KEM–DEM hybrid encryption)**
([BonehShoup2023], Section 11.3.2, Theorem 11.2): if `(keyGen, encaps)` is an IND-CPA secure KEM
and `encryptSym` is a one-time IND-CPA secure DEM (with uniform strict PPT honest algorithms),
then `hybridEncrypt encaps encryptSym` is IND-CPA secure. -/
theorem KEMINDCPA.hybrid_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    {encryptSym : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hdem : DEMOneTimeINDCPA encryptSym)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2))
    (hencryptSym : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => encryptSym p.1 p.2.1 p.2.2)) :
    INDCPA keyGen (hybridEncrypt encaps encryptSym) := by
  intro adversary hadversary
  have hkemFalse := hkem (hybridToKEMDistinguisher encryptSym adversary false)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary false)
  have hkemTrue := hkem (hybridToKEMDistinguisher encryptSym adversary true)
    (isPPT_hybridToKEMDistinguisher hencryptSym hadversary true)
  have hdemAdv := hdem (hybridToDEMAdversary keyGen encaps adversary)
    (isPPT_hybridToDEMAdversary hkeyGen hencaps hadversary)
  exact negligible_of_le ((hkemFalse.add hkemTrue).add hdemAdv)
    (advantage_hybridGame_le keyGen encaps encryptSym adversary)

/-! ### Non-vacuous One-Time Pad DEM -/

/-- One-time pad single-bit symmetric encryption: XOR the first key bit `k.headD false` with the
plaintext bit `bit`. -/
def otpEncrypt (_ : ℕ) (k : List Bool) (bit : Bool) : ProbComp (List Bool) :=
  pure [k.headD false ^^ bit]

/-- One-time pad single-bit symmetric decryption: XOR the first key bit `k.headD false` with the
first ciphertext bit `ct.headD false`. -/
def otpDecrypt (_ : ℕ) (k ct : List Bool) : Bool :=
  k.headD false ^^ ct.headD false

/-- One-time pad decryption inverts one-time pad encryption on every supported ciphertext. -/
theorem otpDecrypt_otpEncrypt (n : ℕ) (k : List Bool) (bit : Bool) :
    otpDecrypt n k [k.headD false ^^ bit] = bit := by
  unfold otpDecrypt
  cases k.headD false <;> cases bit <;> rfl

/-- One-time pad encryption is uniform strict PPT. -/
@[fun_prop]
theorem isPPTOn_otpEncrypt :
    IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => otpEncrypt p.1 p.2.1 p.2.2) := by
  unfold otpEncrypt
  ppt

/-- One-time pad decryption is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_otpDecrypt :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => otpDecrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool := by
  unfold otpDecrypt
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- For `1 ≤ n`, a uniform `n`-bit key masks the challenge bit perfectly in `demGame otpEncrypt`,
so the `false` and `true` experiment distributions are identical. -/
theorem eval_demGame_otpEncrypt_false_eq_true {n : ℕ} (hn : 1 ≤ n) (adversary : Adversary) :
    ProbComp.eval (demGame otpEncrypt adversary false n) =
      ProbComp.eval (demGame otpEncrypt adversary true n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp only [demGame, otpEncrypt, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
    BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    PMF.pure_bind, List.headD_cons, Bool.false_eq_true, ↓reduceIte]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext tail
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  ext out
  simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_bool]
  cases choice.1.1 <;> cases choice.1.2 <;> simp [add_comm]

/-- For `1 ≤ n`, every adversary has exact advantage `0` in `demGame otpEncrypt`. -/
theorem advantage_demGame_otpEncrypt_eq_zero {n : ℕ} (hn : 1 ≤ n) (adversary : Adversary) :
    Game.advantage (ProbComp.eval (demGame otpEncrypt adversary false n))
      (ProbComp.eval (demGame otpEncrypt adversary true n)) = 0 := by
  rw [eval_demGame_otpEncrypt_false_eq_true hn adversary, Game.advantage_self]

/-- **The one-time pad is unconditionally one-time IND-CPA secure**
(`DEMOneTimeINDCPA otpEncrypt`). -/
theorem demOneTimeINDCPA_otpEncrypt : DEMOneTimeINDCPA otpEncrypt := by
  intro adversary _ c
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp [advantage_demGame_otpEncrypt_eq_zero hn adversary]

/-- **KEM-to-PKE corollary**: combining any IND-CPA secure KEM with the one-time pad DEM yields an
IND-CPA secure public-key bit-encryption scheme. -/
theorem KEMINDCPA.hybrid_otpEncrypt_indcpa
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    INDCPA keyGen (hybridEncrypt encaps otpEncrypt) :=
  hkem.hybrid_indcpa demOneTimeINDCPA_otpEncrypt hkeyGen hencaps isPPTOn_otpEncrypt

end Cslib.Crypto.Encryption
