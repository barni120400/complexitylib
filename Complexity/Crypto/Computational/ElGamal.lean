/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiffieHellman
public import Complexity.Crypto.Computational.Encryption.Basic
public import Complexity.Probability.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# ElGamal and Hashed ElGamal encryption and IND-CPA security under DDH

Over a `PrimeOrderGroupFamily`, multiplicative ElGamal encryption ([BonehShoup2023],
Exercise 11.5, p. 459) uses a group description `d`, a secret exponent `α : ZMod (F.order d)`,
and the public key `u = α • g`.
To encrypt a group element `m : F.Carrier d` with randomness `β : ZMod (F.order d)`, the sender
forms the ciphertext `(v, e) = (β • g, β • u + m) = (β • g, (α * β) • g + m)`. Decryption recovers
`e - α • v = m`, and the word-level operations `encodeElGamalPublicKey`, `encodeElGamalEncrypt`,
and `decodeElGamal` compute public-key generation, encryption, and decryption in polynomial time
from natural-number exponents and encoded group elements using `F.generator`, `F.order`, `F.smul`,
and `F.add`.

We prove IND-CPA security under DDH in three settings:
1. **Shared typed-message ElGamal reduction** (`elGamalMsgCPAGame`,
   `elGamalMsgToDDHDistinguisher`, `advantage_elGamalMsgCPAGame_le`,
   `isPPTOn_elGamalMsgToDDHDistinguisher`, `DDH.negligible_elGamalMsgCPAGame`), instantiated for:
   - **Bit ElGamal** (`elGamalCPAGame`, `elGamalINDCPA`, `DDH.elGamalINDCPA`): `false` and `true`
     are embedded as `0` and `g` (`bitElement`, `encodeBit`), and `Encryption.Adversary` chooses
     two challenge bits.
   - **Group-element ElGamal** (`Encryption.WordAdversary`, `elGamalGroupCPAGame`,
     `DDH.negligible_elGamalGroupCPAGame`, [BonehShoup2023], Exercise 11.5(a), p. 459): a
     two-stage word-message adversary chooses any two valid encoded group elements `(m₀, m₁)` in
     `Set.range (F.encode d)`. Replacing the Diffie–Hellman mask `(α * β) • g` with an independent
     uniform `γ • g` masks any chosen group element perfectly (`uniform_smul_generator_add`).
2. **Hashed ElGamal** (`hashedElGamalEncrypt`, `hashedElGamalDecrypt`, `hashedElGamalCPAGame`,
   `DDH.negligible_hashedElGamalCPAGame`, [BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1,
   and Section 11.5.2, Attack Game 11.3, Definition 11.5, and Theorem 11.5, pp. 448–450): given a
   deterministic polynomial-time key-derivation hash function `H : F.Desc × List Bool → List Bool`,
   the sender masks a message word `m` with `pad = H (d, encode (β • u))` via
   `Cslib.BitString.listXor pad.length [pad, m]` (the one-time pad specialization of the `E'_EG`
   variant of Remark 11.1). Security reduces to `DDH` together with key-derivation security
   (`SecureKDF`, Attack Game 11.3 / Definition 11.5, p. 448: indistinguishability of
   `H (d, encode (γ • g))` from a uniform `msgLen n`-bit key).

## Limitations

Key generation and challenge encryption in the security games sample exact uniform exponents in
`ZMod (F.order d)` at the `PMF` level (`PMF.uniformOfFintype (ZMod (F.order d))`), because an odd
prime order `F.order d` cannot be sampled with exact uniformity by a bounded-time fair-coin
`ProbComp` machine; deterministic public-key computation (`encodeElGamalPublicKey`), encryption
given randomness (`encodeElGamalEncrypt`, `encodeHashedElGamalEncrypt`), and decryption
(`decodeElGamal`, `decodeHashedElGamal`) are certified polynomial time on words. The
Diffie–Hellman and key-derivation security assumptions are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt`: algebraic ElGamal encryption and decryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalPublicKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal`: polynomial-time public-key generation,
  encryption, and decryption on encoded group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMsgCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMsgToDDHDistinguisher`: shared typed-message ElGamal
  IND-CPA experiment and DDH reduction ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.bitElement`, `Cslib.Crypto.PrimeOrderGroupFamily.encodeBit`:
  embedding and polynomial-time encoding of message bits as group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalINDCPA`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalToDDHDistinguisher`: bit ElGamal IND-CPA experiment,
  security property, and DDH distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.ValidGroupMessages`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupToDDHDistinguisher`: group-element ElGamal
  IND-CPA experiment and DDH reduction ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamal`: algebraic and word-level Hashed ElGamal
  encryption and decryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalIdealDDHGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalUniformPadGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.SecureKDF`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToKDFDistinguisher`: Hashed ElGamal IND-CPA
  experiments, hybrids, and reductions ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
  Definition 11.5, and Theorem 11.5, pp. 448–450).

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt_elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalPublicKey_eq_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalEncrypt_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_encodeElGamalEncrypt`: ElGamal correctness.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeElGamalPublicKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeElGamal`: polynomial-time
  certificates for honest ElGamal operations.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalMsgCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalMsgToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalMsgCPAGame`: shared typed-message
  ElGamal IND-CPA reduction to DDH.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.elGamalINDCPA`: ElGamal IND-CPA security for bit
  messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalGroupCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalGroupToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalGroupCPAGame`: ElGamal IND-CPA
  security for group-element messages under DDH ([BonehShoup2023], Exercise 11.5(a), p. 459).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt_hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeHashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCPAGame`: Hashed ElGamal
  correctness, polynomial-time certificates, and IND-CPA security under DDH and `SecureKDF`
  ([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 448–450).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5 (pp. 445–446, Remark 11.1), Section 11.5.2
  (pp. 448–450, Attack Game 11.3, Definition 11.5, Theorem 11.5), and Exercise 11.5(a) (p. 459).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-! ### Group-element ElGamal encryption and decryption -/

/-- Algebraic ElGamal encryption of a group element `m : F.Carrier d` under public key
`u : F.Carrier d` with randomness `β : ZMod (F.order d)`. -/
def elGamalEncrypt (d : F.Desc) (u m : F.Carrier d) (β : ZMod (F.order d)) :
    F.Carrier d × F.Carrier d :=
  (β • F.generator d, β • u + m)

/-- Under a genuine public key `u = α • g`, the second ciphertext component is
`(α * β) • g + m`. -/
theorem elGamalEncrypt_smul_generator (d : F.Desc) (α β : ZMod (F.order d)) (m : F.Carrier d) :
    F.elGamalEncrypt d (α • F.generator d) m β =
      (β • F.generator d, (α * β) • F.generator d + m) := by
  simp only [elGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic ElGamal decryption of a ciphertext pair `(v, e)` using secret key
`α : ZMod (F.order d)`. -/
def elGamalDecrypt (d : F.Desc) (α : ZMod (F.order d)) (ct : F.Carrier d × F.Carrier d) :
    F.Carrier d :=
  ct.2 - α • ct.1

/-- **ElGamal decryption correctness**: decrypting an encryption under `u = α • g` with secret key
`α` recovers the message `m`. -/
@[simp] theorem elGamalDecrypt_elGamalEncrypt (d : F.Desc) (α β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.elGamalDecrypt d α (F.elGamalEncrypt d (α • F.generator d) m β) = m := by
  simp only [elGamalDecrypt, elGamalEncrypt, smul_smul, mul_comm β α, add_sub_cancel_left]

/-- Word-level ElGamal public-key computation: given `(d, a)`, compute `encode ((a : ZMod q) • g)`
as `F.smul (d, a, F.encode d (F.generator d))`. -/
def encodeElGamalPublicKey (input : F.Desc × ℕ) : List Bool :=
  F.smul (input.1, input.2, F.encode input.1 (F.generator input.1))

/-- `encodeElGamalPublicKey` computes the group encoding of `(a : ZMod (F.order d)) • g`. -/
@[simp] theorem encodeElGamalPublicKey_eq_encode (d : F.Desc) (a : ℕ) :
    F.encodeElGamalPublicKey (d, a) =
      F.encode d ((a : ZMod (F.order d)) • F.generator d) := by
  simp only [encodeElGamalPublicKey, F.smul_encode]

/-- Word-level ElGamal public-key computation is computable in polynomial time. -/
theorem computableInPolyTime_encodeElGamalPublicKey :
    ComputableInPolyTime F.encodeElGamalPublicKey (encPair F.encDesc encNat) encBits := by
  have hd : ComputableInPolyTime (fun input : F.Desc × ℕ => input.1)
      (encPair F.encDesc encNat) F.encDesc := by fun_prop
  have ha : ComputableInPolyTime (fun input : F.Desc × ℕ => input.2)
      (encPair F.encDesc encNat) encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  exact F.computableInPolyTime_smul.comp (hd.prod (ha.prod hg))

/-- Word-level ElGamal encryption: given `(d, encode u, encode m, b)`, compute
`(encode (b • g), encode (b • u + m))`. -/
def encodeElGamalEncrypt (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  (F.smul (d, b, F.encode d (F.generator d)),
    F.add (d, F.smul (d, b, u), m))

/-- `encodeElGamalEncrypt` evaluates `elGamalEncrypt` on encoded group elements. -/
@[simp] theorem encodeElGamalEncrypt_encode (d : F.Desc) (u m : F.Carrier d) (b : ℕ) :
    F.encodeElGamalEncrypt (d, F.encode d u, F.encode d m, b) =
      (F.encode d (F.elGamalEncrypt d u m (b : ZMod (F.order d))).1,
        F.encode d (F.elGamalEncrypt d u m (b : ZMod (F.order d))).2) := by
  simp only [encodeElGamalEncrypt, elGamalEncrypt, F.smul_encode, F.add_encode]

/-- Word-level ElGamal encryption is computable in polynomial time. -/
theorem computableInPolyTime_encodeElGamalEncrypt :
    ComputableInPolyTime F.encodeElGamalEncrypt
      (encPair F.encDesc (encPair encBits (encPair encBits encNat)))
      (encPair encBits encBits) := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encNat))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.1) encIn F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.1) encIn encBits := by fun_prop
  have hm : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.1) encIn encBits := by fun_prop
  have hb : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.2) encIn encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  have he := F.computableInPolyTime_add.comp (hd.prod (hbu.prod hm))
  exact hv.prod he

/-- Decryption on encoded group elements: given `(d, a, encode v, encode e)`, compute
`encode (e - a • v)` as `F.add (d, encode e, F.smul (d, F.order d - a % F.order d, encode v))`. -/
def decodeElGamal (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  F.add (input.1, input.2.2.2,
    F.smul (input.1, F.order input.1 - input.2.1 % F.order input.1, input.2.2.1))

/-- `decodeElGamal` computes `encode (elGamalDecrypt d a (v, e))` on encoded group elements. -/
theorem decodeElGamal_encode (d : F.Desc) (a : ℕ) (v e : F.Carrier d) :
    F.decodeElGamal (d, a, F.encode d v, F.encode d e) =
      F.encode d (F.elGamalDecrypt d (a : ZMod (F.order d)) (v, e)) := by
  have hneg : ((F.order d - a % F.order d : ℕ) : ZMod (F.order d)) = -(a : ZMod (F.order d)) := by
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order d).pos)), ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  simp only [decodeElGamal, F.smul_encode, hneg, neg_smul, F.add_encode, elGamalDecrypt,
    sub_eq_add_neg]

/-- Encoded ElGamal decryption of an honest encryption recovers the encoded message. -/
@[simp] theorem decodeElGamal_elGamalEncrypt (d : F.Desc) (a : ℕ) (β : ZMod (F.order d))
    (m : F.Carrier d) :
    F.decodeElGamal (d, a,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).1,
      F.encode d (F.elGamalEncrypt d ((a : ZMod (F.order d)) • F.generator d) m β).2) =
      F.encode d m := by
  rw [F.decodeElGamal_encode, F.elGamalDecrypt_elGamalEncrypt]

/-- Word-level ElGamal decryption of `encodeElGamalEncrypt` under `encodeElGamalPublicKey` recovers
the encoded message. -/
theorem decodeElGamal_encodeElGamalEncrypt (d : F.Desc) (a b : ℕ) (m : F.Carrier d) :
    F.decodeElGamal (d, a,
      (F.encodeElGamalEncrypt (d, F.encodeElGamalPublicKey (d, a), F.encode d m, b)).1,
      (F.encodeElGamalEncrypt (d, F.encodeElGamalPublicKey (d, a), F.encode d m, b)).2) =
      F.encode d m := by
  simp only [encodeElGamalPublicKey_eq_encode, encodeElGamalEncrypt_encode,
    decodeElGamal_elGamalEncrypt]

/-- Encoded ElGamal decryption is computable in polynomial time. -/
theorem computableInPolyTime_decodeElGamal :
    ComputableInPolyTime F.decodeElGamal
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) F.encDesc := by fun_prop
  have ha : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat := by fun_prop
  have hv : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have he : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by fun_prop
  have horder : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    F.computableInPolyTime_order.tidy.comp hd
  have hexp : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool =>
        F.order input.1 - input.2.1 % F.order input.1)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encNat :=
    .binary_sub' horder (.binary_mod' ha horder)
  have hsmul := F.computableInPolyTime_smul.tidy.comp (hd.prod (hexp.prod hv))
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_add.tidy.comp (hd.prod (he.prod hsmul)))

/-! ### Shared typed-message ElGamal IND-CPA reduction ([BonehShoup2023], Exercise 11.5(a)) -/

/-- The IND-CPA experiment for multiplicative ElGamal encryption over message type `Msg` via a
word-level message encoder `encodeMsg : F.Desc → Msg → List Bool` ([BonehShoup2023],
Exercise 11.5(a), p. 459): draw `d ← setup n` and a uniform secret key `α : ZMod (F.order d)`,
pass the encoded public key `(d, encode (α • g))` to `adversary.choose`, encrypt the selected
message `m` under a fresh uniform exponent `β : ZMod (F.order d)` via
`F.add (d, encode ((α * β) • g), encodeMsg d m)`, and pass the saved state and encoded ciphertext
to `adversary.guess`. -/
noncomputable def elGamalMsgCPAGame {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (setup : ℕ → PMF F.Desc) (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      F.add (d, F.encode d ((α * β) • F.generator d), encodeMsg d m))
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- The DDH distinguisher constructed from a typed-message ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a), p. 459): given `(d, u, v, w)`, pass `(d, u)` as the public
key, mask the selected encoded message `encodeMsg d m` with `w` using `F.add`, and return the
adversary's guess. -/
def elGamalMsgToDDHDistinguisher {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits
    (input.2.2.1, F.add (input.1, input.2.2.2, encodeMsg input.1 m))
  adversary.guess n choice.2 ct

/-- In the real DDH game, `elGamalMsgToDDHDistinguisher` simulates `elGamalMsgCPAGame`
exactly. -/
theorem ddhRealGame_elGamalMsgToDDHDistinguisher {Msg : Type}
    (encodeMsg : F.Desc → Msg → List Bool) (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary bit) n =
      F.elGamalMsgCPAGame encodeMsg setup adversary bit n := by
  simp only [ddhRealGame, elGamalMsgToDDHDistinguisher, elGamalMsgCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, whenever `adversary.choose` outputs messages whose encodings under
`encodeMsg d` lie in `Set.range (F.encode d)`, the uniform element `γ • g` perfectly masks both
candidate messages, so the experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true {Msg : Type}
    (encodeMsg : F.Desc → Msg → List Bool) (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hvalid : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      (∃ x₀ : F.Carrier d, encodeMsg d choice.1.1 = F.encode d x₀) ∧
        (∃ x₁ : F.Carrier d, encodeMsg d choice.1.2 = F.encode d x₁)) :
    F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary false) n =
      F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary true) n := by
  simp only [ddhIdealGame, elGamalMsgToDDHDistinguisher, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, Bool.false_eq_true, ↓reduceIte]
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ (setup n).support
  · congr 1
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun α => ?_
    congr 1
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun β => ?_
    congr 1
    rw [PMF.bind_comm,
      PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))
        (ProbComp.eval (adversary.choose n _))]
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun choice => ?_
    by_cases hchoice :
        choice ∈
          (ProbComp.eval
            (adversary.choose n
              (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support
    · congr 1
      obtain ⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩ := hvalid d hd α choice hchoice
      simp only [hx₀, hx₁, F.add_encode]
      exact congrArg (fun p : PMF Bool => p b)
        ((F.uniform_smul_generator_add d x₀
          (fun x => ProbComp.eval (adversary.guess n choice.2
            (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).trans
          (F.uniform_smul_generator_add d x₁
            (fun x => ProbComp.eval (adversary.guess n choice.2
              (encPair encBits encBits
                (F.encode d (β • F.generator d), F.encode d x))))).symm)
    · have h0 :
          ProbComp.eval
            (adversary.choose n
              (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))) choice = 0 := by
        rwa [PMF.mem_support_iff, not_not] at hchoice
      simp only [h0, zero_mul]
  · have hd0 : setup n d = 0 := by rwa [PMF.mem_support_iff, not_not] at hd
    simp only [hd0, zero_mul]

/-- **Quantitative reduction of typed-message ElGamal IND-CPA to DDH** ([BonehShoup2023],
Exercise 11.5(a), p. 459): when `adversary.choose` outputs messages whose encodings under
`encodeMsg d` lie in `Set.range (F.encode d)` at parameter `n`, the IND-CPA distinguishing
advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalMsgToDDHDistinguisher encodeMsg adversary false` and
`elGamalMsgToDDHDistinguisher encodeMsg adversary true`. -/
theorem advantage_elGamalMsgCPAGame_le {Msg : Type}
    (encodeMsg : F.Desc → Msg → List Bool) (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.AdversaryOf Msg) (n : ℕ)
    (hvalid : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      (∃ x₀ : F.Carrier d, encodeMsg d choice.1.1 = F.encode d x₀) ∧
        (∃ x₁ : F.Carrier d, encodeMsg d choice.1.2 = F.encode d x₁)) :
    Game.advantage (F.elGamalMsgCPAGame encodeMsg setup adversary false n)
      (F.elGamalMsgCPAGame encodeMsg setup adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary false) n)
        (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary true) n)
        (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary true) n) := by
  rw [← F.ddhRealGame_elGamalMsgToDDHDistinguisher encodeMsg setup adversary false n,
    ← F.ddhRealGame_elGamalMsgToDDHDistinguisher encodeMsg setup adversary true n]
  refine (Game.advantage_triangle _
    (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary false) n) _).trans ?_
  rw [F.ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true encodeMsg setup adversary n hvalid,
    Game.advantage_comm
      (F.ddhIdealGame setup (F.elGamalMsgToDDHDistinguisher encodeMsg adversary true) n)]

/-- `elGamalMsgToDDHDistinguisher` is uniform strict PPT whenever `encodeMsg` is computable in
polynomial time and `adversary` is uniform strict PPT. -/
theorem isPPTOn_elGamalMsgToDDHDistinguisher {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc → Msg → List Bool}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool
      (fun input => F.elGamalMsgToDDHDistinguisher encodeMsg adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hadd := F.computableInPolyTime_add
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encMsg encMsg) encBits))
      encMsg := by
    cases bit <;> fun_prop
  have hencM : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (Msg × Msg) × List Bool =>
        encodeMsg p.1.2.1 (if bit then p.2.1.2 else p.2.1.1))
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encMsg encMsg) encBits))
      encBits :=
    hencMsg.comp ((by fun_prop : ComputableInPolyTime _ _ F.encDesc).prod hm)
  unfold elGamalMsgToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (Msg × Msg) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          F.add (p.1.2.1, p.1.2.2.2.2, encodeMsg p.1.2.1 (if bit then p.2.1.2 else p.2.1.1)))))
    (by fun_prop)

/-- **Typed-message ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459). -/
theorem DDH.negligible_elGamalMsgCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {Msg : Type} {encMsg : Msg ↪ List Bool} {encodeMsg : F.Desc → Msg → List Bool}
    (hDDH : F.DDH setup)
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    {adversary : Encryption.AdversaryOf Msg}
    (hA : Encryption.AdversaryOf.IsPPT encMsg adversary)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      (∃ x₀ : F.Carrier d, encodeMsg d choice.1.1 = F.encode d x₀) ∧
        (∃ x₁ : F.Carrier d, encodeMsg d choice.1.2 = F.encode d x₁)) :
    Negligible fun n =>
      Game.advantage (F.elGamalMsgCPAGame encodeMsg setup adversary false n)
        (F.elGamalMsgCPAGame encodeMsg setup adversary true n) :=
  negligible_of_eventually_le
    ((hDDH _ (F.isPPTOn_elGamalMsgToDDHDistinguisher hencMsg hA false)).add
      (hDDH _ (F.isPPTOn_elGamalMsgToDDHDistinguisher hencMsg hA true)))
    (hvalid.mono fun n hn => F.advantage_elGamalMsgCPAGame_le encodeMsg setup adversary n hn)

/-! ### Bit encryption and IND-CPA security under DDH -/

/-- Embed a message bit `b : Bool` into `F.Carrier d` as `0` (for `false`) or `g` (for `true`). -/
def bitElement (d : F.Desc) (b : Bool) : F.Carrier d :=
  if b then F.generator d else 0

/-- Distinct message bits map to distinct group elements. -/
theorem bitElement_injective (d : F.Desc) : Function.Injective (F.bitElement d) := by
  intro b₁ b₂ h
  cases b₁ <;> cases b₂
  · rfl
  · exact absurd h.symm (F.generator_ne_zero d)
  · exact absurd h (F.generator_ne_zero d)
  · rfl

/-- Encode a message bit `b : Bool` as an encoded element of `F.Carrier d` using `F.smul`. -/
def encodeBit (d : F.Desc) (b : Bool) : List Bool :=
  F.smul (d, if b then 1 else 0, F.encode d (F.generator d))

/-- `encodeBit` computes the group encoding of `bitElement`. -/
@[simp] theorem encodeBit_eq_encode_bitElement (d : F.Desc) (b : Bool) :
    F.encodeBit d b = F.encode d (F.bitElement d b) := by
  cases b <;> simp [encodeBit, bitElement, F.smul_encode]

/-- `encodeBit` is computable in polynomial time from the group description and the bit. -/
theorem computableInPolyTime_encodeBit :
    ComputableInPolyTime (fun p : F.Desc × Bool => F.encodeBit p.1 p.2)
      (encPair F.encDesc encBool) encBits := by
  have hd : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => p.1)
      (encPair F.encDesc encBool) F.encDesc := by fun_prop
  have hgen : ComputableTidilyInPolyTime
      (fun p : F.Desc × Bool => F.encode p.1 (F.generator p.1))
      (encPair F.encDesc encBool) encBits :=
    F.computableInPolyTime_generator.tidy.comp hd
  have hbit : ComputableTidilyInPolyTime (fun p : F.Desc × Bool => if p.2 then 1 else 0)
      (encPair F.encDesc encBool) encNat :=
    (ComputableTidilyInPolyTime.snd _ _).cond
      (ComputableTidilyInPolyTime.const 1) (ComputableTidilyInPolyTime.const 0)
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_smul.tidy.comp (hd.prod (hbit.prod hgen)))

/-- The IND-CPA experiment for ElGamal bit encryption ([BonehShoup2023], Exercise 11.5, p. 459):
draw `d` from `setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the encoded public
key `(d, encode (α • g))` to `adversary.choose`, encrypt the selected challenge bit under a fresh
uniform exponent `β : ZMod (F.order d)`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def elGamalCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      F.encode d ((α * β) • F.generator d + F.bitElement d m))
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- `elGamalCPAGame` is the `encodeBit` specialization of `elGamalMsgCPAGame`. -/
theorem elGamalCPAGame_eq_elGamalMsgCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.elGamalCPAGame setup adversary bit n =
      F.elGamalMsgCPAGame F.encodeBit setup adversary bit n := by
  simp only [elGamalCPAGame, elGamalMsgCPAGame, F.encodeBit_eq_encode_bitElement, F.add_encode]

/-- IND-CPA security of ElGamal bit encryption over `F` for a setup law `setup`: every uniform
strict PPT `Encryption.Adversary` has negligible distinguishing advantage between challenge bit
`false` and challenge bit `true`. -/
def elGamalINDCPA (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.elGamalCPAGame setup adversary false n)
    (fun adversary n => F.elGamalCPAGame setup adversary true n)
    Encryption.Adversary.IsPPT

/-- The DDH distinguisher constructed from an IND-CPA adversary ([BonehShoup2023], proof of
Exercise 11.5(a), p. 459): given `(d, u, v, w)`, pass `(d, u)` as the public key, encrypt the
selected challenge bit by masking with `w`, and return the adversary's guess. -/
abbrev elGamalToDDHDistinguisher (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.elGamalMsgToDDHDistinguisher F.encodeBit adversary bit n input

/-- In the real DDH game, `elGamalToDDHDistinguisher` simulates `elGamalCPAGame` exactly. -/
@[simp] theorem ddhRealGame_elGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary bit) n =
      F.elGamalCPAGame setup adversary bit n := by
  rw [F.ddhRealGame_elGamalMsgToDDHDistinguisher, F.elGamalCPAGame_eq_elGamalMsgCPAGame]

/-- In the ideal DDH game, the uniform element `γ • g` perfectly masks the challenge bit, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n :=
  F.ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true F.encodeBit setup adversary n
    fun d _ _ choice _ =>
      ⟨⟨F.bitElement d choice.1.1, F.encodeBit_eq_encode_bitElement d choice.1.1⟩,
       ⟨F.bitElement d choice.1.2, F.encodeBit_eq_encode_bitElement d choice.1.2⟩⟩

/-- **Quantitative reduction of ElGamal IND-CPA to DDH** ([BonehShoup2023], Exercise 11.5(a),
p. 459): the IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH
advantages of `elGamalToDDHDistinguisher adversary false` and
`elGamalToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    Game.advantage (F.elGamalCPAGame setup adversary false n)
      (F.elGamalCPAGame setup adversary true n) ≤
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary false) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary true) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n) := by
  rw [F.elGamalCPAGame_eq_elGamalMsgCPAGame, F.elGamalCPAGame_eq_elGamalMsgCPAGame]
  exact F.advantage_elGamalMsgCPAGame_le F.encodeBit setup adversary n
    fun d _ _ choice _ =>
      ⟨⟨F.bitElement d choice.1.1, F.encodeBit_eq_encode_bitElement d choice.1.1⟩,
       ⟨F.bitElement d choice.1.2, F.encodeBit_eq_encode_bitElement d choice.1.2⟩⟩

/-- `elGamalToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalToDDHDistinguisher {adversary : Encryption.Adversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalToDDHDistinguisher adversary bit input.1 input.2) :=
  F.isPPTOn_elGamalMsgToDDHDistinguisher F.computableInPolyTime_encodeBit hA bit

/-- **ElGamal bit encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459). -/
theorem DDH.elGamalINDCPA {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.elGamalINDCPA setup := by
  intro adversary hA
  exact negligible_of_le
    ((hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA false)).add
      (hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA true)))
    (F.advantage_elGamalCPAGame_le setup adversary)

/-! ### Group-element ElGamal IND-CPA security under DDH -/

/-- A challenge choice `((m₀, m₁), state)` consists of valid encoded group elements in
`F.Carrier d` when both `m₀` and `m₁` lie in `Set.range (F.encode d)`. -/
def ValidGroupMessages (d : F.Desc) (choice : (List Bool × List Bool) × List Bool) : Prop :=
  (∃ x₀ : F.Carrier d, choice.1.1 = F.encode d x₀) ∧
    (∃ x₁ : F.Carrier d, choice.1.2 = F.encode d x₁)

/-- The IND-CPA experiment for group-element ElGamal encryption ([BonehShoup2023],
Exercise 11.5(a), p. 459): specialization of `elGamalMsgCPAGame` to identity message encoding on
encoded group elements (`Encryption.WordAdversary`). -/
noncomputable abbrev elGamalGroupCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game :=
  F.elGamalMsgCPAGame (fun _ m => m) setup adversary bit n

/-- The DDH distinguisher constructed from a group-element ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a), p. 459): specialization of `elGamalMsgToDDHDistinguisher` to
identity message encoding. -/
abbrev elGamalGroupToDDHDistinguisher (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool :=
  F.elGamalMsgToDDHDistinguisher (fun _ m => m) adversary bit n input

/-- In the real DDH game, `elGamalGroupToDDHDistinguisher` simulates `elGamalGroupCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_elGamalGroupToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary bit) n =
      F.elGamalGroupCPAGame setup adversary bit n :=
  F.ddhRealGame_elGamalMsgToDDHDistinguisher (fun _ m => m) setup adversary bit n

/-- In the ideal DDH game, whenever `adversary.choose` outputs valid encoded group elements in
`F.Carrier d`, the uniform element `γ • g` perfectly masks both candidate group elements, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalGroupToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n : ℕ)
    (hvalid : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      F.ValidGroupMessages d choice) :
    F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n :=
  F.ddhIdealGame_elGamalMsgToDDHDistinguisher_false_eq_true (fun _ m => m) setup adversary n hvalid

/-- **Quantitative reduction of group-element ElGamal IND-CPA to DDH** ([BonehShoup2023],
Exercise 11.5(a), p. 459): when `adversary.choose` outputs valid encoded group elements at
parameter `n`, the IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH
advantages of `elGamalGroupToDDHDistinguisher adversary false` and
`elGamalGroupToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalGroupCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.WordAdversary) (n : ℕ)
    (hvalid : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      F.ValidGroupMessages d choice) :
    Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
      (F.elGamalGroupCPAGame setup adversary true n) ≤
      Game.advantage (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n)
        (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n)
        (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n) :=
  F.advantage_elGamalMsgCPAGame_le (fun _ m => m) setup adversary n hvalid

/-- `elGamalGroupToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalGroupToDDHDistinguisher {adversary : Encryption.WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalGroupToDDHDistinguisher adversary bit input.1 input.2) :=
  F.isPPTOn_elGamalMsgToDDHDistinguisher (by fun_prop) hA bit

/-- **Group-element ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a), p. 459): every uniform strict PPT `Encryption.WordAdversary`
that eventually outputs valid encoded group elements has negligible IND-CPA distinguishing
advantage. -/
theorem DDH.negligible_elGamalGroupCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      F.ValidGroupMessages d choice) :
    Negligible fun n =>
      Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
        (F.elGamalGroupCPAGame setup adversary true n) :=
  hDDH.negligible_elGamalMsgCPAGame (by fun_prop) hA hvalid

/-! ### Hashed ElGamal encryption and IND-CPA security ([BonehShoup2023], Section 11.5) -/

/-- Applying `Cslib.BitString.listXor pad.length [pad, m]` to a uniform `k`-bit pad preserves
`Cslib.BitString.uniformList k` for every message word `m`. -/
theorem uniformList_map_listXor_length (k : ℕ) (m : List Bool) :
    (Cslib.BitString.uniformList k).map
      (fun pad => Cslib.BitString.listXor pad.length [pad, m]) =
      Cslib.BitString.uniformList k := by
  have hcomp :
      (fun pad : List Bool => Cslib.BitString.listXor pad.length [pad, m]) ∘ List.ofFn =
        (fun pad : List Bool => Cslib.BitString.listXor k [pad, m]) ∘
          (List.ofFn : Cslib.BitString k → List Bool) := by
    funext x
    simp
  calc
    (Cslib.BitString.uniformList k).map
        (fun pad => Cslib.BitString.listXor pad.length [pad, m])
      = (PMF.uniformOfFintype (Cslib.BitString k)).map
          ((fun pad : List Bool => Cslib.BitString.listXor pad.length [pad, m]) ∘ List.ofFn) := by
        rw [Cslib.BitString.uniformList, PMF.map_comp]
    _ = (PMF.uniformOfFintype (Cslib.BitString k)).map
          ((fun pad : List Bool => Cslib.BitString.listXor k [pad, m]) ∘ List.ofFn) := by
        rw [hcomp]
    _ = (Cslib.BitString.uniformList k).map (fun pad => Cslib.BitString.listXor k [pad, m]) := by
        rw [Cslib.BitString.uniformList, PMF.map_comp]
    _ = Cslib.BitString.uniformList k :=
        Cslib.BitString.uniformList_map_listXor k m

/-- Algebraic Hashed ElGamal encryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1):
given key-derivation hash function `H : F.Desc × List Bool → List Bool`, public key
`u : F.Carrier d`, message word `m : List Bool`, and randomness `β : ZMod (F.order d)`, derive
`pad = H (d, encode (β • u))` and output
`(β • g, Cslib.BitString.listXor pad.length [pad, m])`. -/
def hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc) (u : F.Carrier d)
    (m : List Bool) (β : ZMod (F.order d)) : F.Carrier d × List Bool :=
  let pad := H (d, F.encode d (β • u))
  (β • F.generator d, Cslib.BitString.listXor pad.length [pad, m])

/-- Under a genuine public key `u = α • g`, Hashed ElGamal masks `m` with
`pad = H (d, encode ((α * β) • g))` via `Cslib.BitString.listXor pad.length [pad, m]`. -/
theorem hashedElGamalEncrypt_smul_generator (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β : ZMod (F.order d)) (m : List Bool) :
    F.hashedElGamalEncrypt H d (α • F.generator d) m β =
      let pad := H (d, F.encode d ((α * β) • F.generator d))
      (β • F.generator d, Cslib.BitString.listXor pad.length [pad, m]) := by
  simp only [hashedElGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic Hashed ElGamal decryption ([BonehShoup2023], Section 11.5, pp. 445–446, Remark 11.1):
given secret key `α : ZMod (F.order d)` and ciphertext `(v, c)`, derive
`pad = H (d, encode (α • v))` and recover `Cslib.BitString.listXor pad.length [pad, c]`. -/
def hashedElGamalDecrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α : ZMod (F.order d)) (ct : F.Carrier d × List Bool) : List Bool :=
  let pad := H (d, F.encode d (α • ct.1))
  Cslib.BitString.listXor pad.length [pad, ct.2]

/-- **Hashed ElGamal decryption correctness**: when the message word `m` has the same length as the
derived pad `H (d, encode ((α * β) • g))`, decrypting an encryption under `u = α • g` with secret
key `α` recovers `m`. -/
@[simp] theorem hashedElGamalDecrypt_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (α β : ZMod (F.order d)) {m : List Bool}
    (hlen : m.length = (H (d, F.encode d ((α * β) • F.generator d))).length) :
    F.hashedElGamalDecrypt H d α (F.hashedElGamalEncrypt H d (α • F.generator d) m β) = m := by
  simp only [hashedElGamalDecrypt, hashedElGamalEncrypt_smul_generator, smul_smul]
  rw [Cslib.BitString.listXor_pair, Cslib.BitString.ofList_listXor_pair, ← add_assoc,
    Cslib.BitString.add_self, zero_add, Cslib.BitString.ofFn_ofList hlen]

/-- Word-level Hashed ElGamal encryption: given `(d, encode u, m, b)`, derive
`pad = H (d, encode (b • u))` and compute
`(encode (b • g), Cslib.BitString.listXor pad.length [pad, m])`. -/
def encodeHashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  let pad := H (d, F.smul (d, b, u))
  (F.smul (d, b, F.encode d (F.generator d)),
    Cslib.BitString.listXor pad.length [pad, m])

/-- `encodeHashedElGamalEncrypt` evaluates `hashedElGamalEncrypt` on encoded group elements. -/
@[simp] theorem encodeHashedElGamalEncrypt_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (u : F.Carrier d) (m : List Bool) (b : ℕ) :
    F.encodeHashedElGamalEncrypt H (d, F.encode d u, m, b) =
      (F.encode d (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).1,
        (F.hashedElGamalEncrypt H d u m (b : ZMod (F.order d))).2) := by
  simp only [encodeHashedElGamalEncrypt, hashedElGamalEncrypt, F.smul_encode]

/-- Word-level Hashed ElGamal encryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_encodeHashedElGamalEncrypt {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime (F.encodeHashedElGamalEncrypt H)
      (encPair F.encDesc (encPair encBits (encPair encBits encNat)))
      (encPair encBits encBits) := by
  let encIn := encPair F.encDesc (encPair encBits (encPair encBits encNat))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.1) encIn F.encDesc := by fun_prop
  have hu : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.1) encIn encBits := by fun_prop
  have hm : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.1) encIn encBits := by fun_prop
  have hb : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ => input.2.2.2) encIn encNat := by fun_prop
  have hg := F.computableInPolyTime_generator.comp hd
  have hv := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hg))
  have hbu := F.computableInPolyTime_smul.comp (hd.prod (hb.prod hu))
  have hpad := hH.comp (hd.prod hbu)
  have hxor : ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × ℕ =>
        let pad := H (input.1, F.smul (input.1, input.2.2.2, input.2.1))
        Cslib.BitString.listXor pad.length [pad, input.2.2.1])
      encIn encBits := by fun_prop
  exact hv.prod hxor

/-- Word-level Hashed ElGamal decryption: given `(d, a, encode v, c)`, derive
`pad = H (d, encode (a • v))` and compute `Cslib.BitString.listXor pad.length [pad, c]`. -/
def decodeHashedElGamal (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  let pad := H (input.1, F.smul (input.1, input.2.1, input.2.2.1))
  Cslib.BitString.listXor pad.length [pad, input.2.2.2]

/-- `decodeHashedElGamal` computes `hashedElGamalDecrypt` on encoded group elements. -/
@[simp] theorem decodeHashedElGamal_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (v : F.Carrier d) (c : List Bool) :
    F.decodeHashedElGamal H (d, a, F.encode d v, c) =
      F.hashedElGamalDecrypt H d (a : ZMod (F.order d)) (v, c) := by
  simp only [decodeHashedElGamal, hashedElGamalDecrypt, F.smul_encode]

/-- Word-level Hashed ElGamal decryption of an honest encryption recovers `m` whenever `m` has the
same length as the derived pad. -/
theorem decodeHashedElGamal_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (β : ZMod (F.order d)) {m : List Bool}
    (hlen :
      m.length =
        (H (d, F.encode d (((a : ZMod (F.order d)) * β) • F.generator d))).length) :
    F.decodeHashedElGamal H (d, a,
      F.encode d (F.hashedElGamalEncrypt H d ((a : ZMod (F.order d)) • F.generator d) m β).1,
      (F.hashedElGamalEncrypt H d ((a : ZMod (F.order d)) • F.generator d) m β).2) = m := by
  rw [F.decodeHashedElGamal_encode, F.hashedElGamalDecrypt_hashedElGamalEncrypt H d _ β hlen]

/-- Word-level Hashed ElGamal decryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_decodeHashedElGamal {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime (F.decodeHashedElGamal H)
      (encPair F.encDesc (encPair encNat (encPair encBits encBits))) encBits := by
  let encIn := encPair F.encDesc (encPair encNat (encPair encBits encBits))
  have hd : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.1) encIn F.encDesc := by fun_prop
  have ha : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.1) encIn encNat := by fun_prop
  have hv : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.1) encIn encBits := by fun_prop
  have hc : ComputableInPolyTime
      (fun input : F.Desc × ℕ × List Bool × List Bool => input.2.2.2) encIn encBits := by fun_prop
  have hav := F.computableInPolyTime_smul.comp (hd.prod (ha.prod hv))
  have hpad := hH.comp (hd.prod hav)
  unfold decodeHashedElGamal
  fun_prop

/-- The IND-CPA experiment for Hashed ElGamal encryption ([BonehShoup2023], Section 11.5,
pp. 445–446, Remark 11.1, and Section 11.5.2, Theorem 11.5, pp. 448–450): draw `d ← setup n` and a
uniform secret key `α : ZMod (F.order d)`, pass the encoded public key `(d, encode (α • g))` to
`adversary.choose`, encrypt the selected message word `m` under a fresh uniform exponent
`β : ZMod (F.order d)` by masking with `pad = H (d, encode ((α * β) • g))` via
`Cslib.BitString.listXor pad.length [pad, m]`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def hashedElGamalCPAGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad := H (d, F.encode d ((α * β) • F.generator d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 1 for Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5,
pp. 449–450): replace the Diffie–Hellman shared element `(α * β) • g` with an independent uniform
group element `γ • g`. -/
noncomputable def hashedElGamalIdealDDHGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad := H (d, F.encode d (γ • F.generator d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 2 for Hashed ElGamal ([BonehShoup2023], Section 11.5.2, proof of Theorem 11.5,
pp. 449–450): replace the derived key `H (d, encode (γ • g))` with an independent uniform
`msgLen n`-bit key `pad ← Cslib.BitString.uniformList (msgLen n)`. -/
noncomputable def hashedElGamalUniformPadGame (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), Cslib.BitString.listXor pad.length [pad, m])
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- The real key-derivation security experiment ([BonehShoup2023], Section 11.5.2, Attack Game 11.3,
Experiment `0`, p. 448): draw `d ← setup n` and independent uniform `α, β, γ : ZMod (F.order d)`,
and give the distinguisher `(d, encode (α • g), encode (β • g), H (d, encode (γ • g)))`. -/
noncomputable def kdfRealGame (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      H (d, F.encode d (γ • F.generator d))))

/-- The ideal key-derivation security experiment ([BonehShoup2023], Section 11.5.2,
Attack Game 11.3, Experiment `1`, p. 448): draw `d ← setup n`, independent uniform
`α, β : ZMod (F.order d)`, and an independent uniform `msgLen n`-bit key
`pad ← Cslib.BitString.uniformList (msgLen n)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), pad)`. -/
noncomputable def kdfIdealGame (setup : ℕ → PMF F.Desc) (msgLen : ℕ → ℕ)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d), pad))

/-- Secure key derivation for `H` over `F` ([BonehShoup2023], Section 11.5.2, Attack Game 11.3 and
Definition 11.5, p. 448): every uniform strict PPT distinguisher has negligible advantage between
`kdfRealGame` and `kdfIdealGame`. -/
def SecureKDF (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.kdfRealGame setup H) (F.kdfIdealGame setup msgLen)
    fun distinguisher =>
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun input => distinguisher input.1 input.2)

/-- The DDH distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–450): given `(d, u, v, w)`, pass `(d, u)` as the
public key, mask the selected message word with `pad = H (d, w)` via
`Cslib.BitString.listXor pad.length [pad, m]`, and return the adversary's guess. -/
def hashedElGamalToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let pad := H (input.1, input.2.2.2)
  let ct := encPair encBits encBits
    (input.2.2.1, Cslib.BitString.listXor pad.length [pad, m])
  adversary.guess n choice.2 ct

/-- In the real DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary bit) n =
      F.hashedElGamalCPAGame setup H adversary bit n := by
  simp only [ddhRealGame, hashedElGamalToDDHDistinguisher, hashedElGamalCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalIdealDDHGame`
exactly. -/
@[simp] theorem ddhIdealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary bit) n =
      F.hashedElGamalIdealDDHGame setup H adversary bit n := by
  simp only [ddhIdealGame, hashedElGamalToDDHDistinguisher, hashedElGamalIdealDDHGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalToDDHDistinguisher` is uniform strict PPT whenever `H` is polynomial time and
`adversary` is uniform strict PPT. -/
theorem isPPTOn_hashedElGamalToDDHDistinguisher {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToDDHDistinguisher H adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  let E :=
    encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      (encPair (encPair encBits encBits) encBits)
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1) E encBits := by
    cases bit <;> fun_prop
  have hpad : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        H (p.1.2.1, p.1.2.2.2.2)) E encBits :=
    hH.comp (by fun_prop)
  unfold hashedElGamalToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      let pad := H (p.1.2.1, p.1.2.2.2.2)
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          Cslib.BitString.listXor pad.length [pad, if bit then p.2.1.2 else p.2.1.1])))
    (by fun_prop)

/-- The KDF distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
Section 11.5.2, proof of Theorem 11.5, pp. 449–450): given `(d, u, v, pad)`, pass `(d, u)` as the
public key, mask the selected message word with `pad` via
`Cslib.BitString.listXor pad.length [pad, m]`, and return the adversary's guess. -/
def hashedElGamalToKDFDistinguisher (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let pad := input.2.2.2
  let ct := encPair encBits encBits
    (input.2.2.1, Cslib.BitString.listXor pad.length [pad, m])
  adversary.guess n choice.2 ct

/-- In the real KDF game, `hashedElGamalToKDFDistinguisher` simulates `hashedElGamalIdealDDHGame`
exactly. -/
@[simp] theorem kdfRealGame_hashedElGamalToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : Encryption.WordAdversary) (bit : Bool)
    (n : ℕ) :
    F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary bit) n =
      F.hashedElGamalIdealDDHGame setup H adversary bit n := by
  simp only [kdfRealGame, hashedElGamalToKDFDistinguisher, hashedElGamalIdealDDHGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the ideal KDF game, `hashedElGamalToKDFDistinguisher` simulates
`hashedElGamalUniformPadGame` exactly. -/
@[simp] theorem kdfIdealGame_hashedElGamalToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) :
    F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary bit) n =
      F.hashedElGamalUniformPadGame setup msgLen adversary bit n := by
  simp only [kdfIdealGame, hashedElGamalToKDFDistinguisher, hashedElGamalUniformPadGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalToKDFDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_hashedElGamalToKDFDistinguisher {adversary : Encryption.WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToKDFDistinguisher adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBits encBits) encBits))
      encBits := by
    cases bit <;> fun_prop
  unfold hashedElGamalToKDFDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          Cslib.BitString.listXor p.1.2.2.2.2.length
            [p.1.2.2.2.2, if bit then p.2.1.2 else p.2.1.1])))
    (by fun_prop)

/-- In `hashedElGamalUniformPadGame`, the uniform `msgLen n`-bit pad masks any challenge message
word perfectly via `Cslib.BitString.listXor pad.length [pad, m]`, so the experiments for
`bit = false` and `bit = true` are identical. -/
theorem hashedElGamalUniformPadGame_false_eq_true (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : Encryption.WordAdversary) (n : ℕ) :
    F.hashedElGamalUniformPadGame setup msgLen adversary false n =
      F.hashedElGamalUniformPadGame setup msgLen adversary true n := by
  simp only [hashedElGamalUniformPadGame, PMF.monad_bind_eq_bind,
    Bool.false_eq_true, ↓reduceIte]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext choice
  congr 1; funext β
  have hpad (m : List Bool) :
      ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
        ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits
            (F.encode d (β • F.generator d),
              Cslib.BitString.listXor pad.length [pad, m])))) =
      ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
        ProbComp.eval (adversary.guess n choice.2
          (encPair encBits encBits (F.encode d (β • F.generator d), pad)))) := by
    have hmap := congrArg
      (fun p : PMF (List Bool) =>
        p.bind fun pad =>
          ProbComp.eval (adversary.guess n choice.2
            (encPair encBits encBits (F.encode d (β • F.generator d), pad))))
      (uniformList_map_listXor_length (msgLen n) m)
    simpa only [PMF.bind_map, Function.comp_def] using hmap
  exact (hpad choice.1.1).trans (hpad choice.1.2).symm

/-- **Quantitative reduction of Hashed ElGamal IND-CPA to DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 448–450): the IND-CPA distinguishing
advantage of `adversary` is bounded by the sum of the two DDH advantages of
`hashedElGamalToDDHDistinguisher` and the two KDF advantages of
`hashedElGamalToKDFDistinguisher`. -/
theorem advantage_hashedElGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
      (F.hashedElGamalCPAGame setup H adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n)
        (F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary false) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary false) n) +
      Game.advantage
        (F.kdfRealGame setup H (F.hashedElGamalToKDFDistinguisher adversary true) n)
        (F.kdfIdealGame setup msgLen (F.hashedElGamalToKDFDistinguisher adversary true) n) +
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n)
        (F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary true) n) := by
  have h1 := Game.advantage_triangle
    (F.hashedElGamalCPAGame setup H adversary false n)
    (F.hashedElGamalIdealDDHGame setup H adversary false n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  have h2 := Game.advantage_triangle
    (F.hashedElGamalIdealDDHGame setup H adversary false n)
    (F.hashedElGamalUniformPadGame setup msgLen adversary false n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  have h3 := Game.advantage_triangle
    (F.hashedElGamalUniformPadGame setup msgLen adversary true n)
    (F.hashedElGamalIdealDDHGame setup H adversary true n)
    (F.hashedElGamalCPAGame setup H adversary true n)
  rw [F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n] at h2
  calc Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
        (F.hashedElGamalCPAGame setup H adversary true n)
      ≤ Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
          (F.hashedElGamalIdealDDHGame setup H adversary false n) +
        (Game.advantage (F.hashedElGamalIdealDDHGame setup H adversary false n)
          (F.hashedElGamalUniformPadGame setup msgLen adversary true n) +
        (Game.advantage
          (F.hashedElGamalUniformPadGame setup msgLen adversary true n)
          (F.hashedElGamalIdealDDHGame setup H adversary true n) +
        Game.advantage
          (F.hashedElGamalIdealDDHGame setup H adversary true n)
          (F.hashedElGamalCPAGame setup H adversary true n))) :=
        h1.trans (add_le_add le_rfl (h2.trans (add_le_add le_rfl h3)))
    _ = _ := by
        simp only [ddhRealGame_hashedElGamalToDDHDistinguisher,
          ddhIdealGame_hashedElGamalToDDHDistinguisher,
          kdfRealGame_hashedElGamalToKDFDistinguisher,
          kdfIdealGame_hashedElGamalToKDFDistinguisher,
          F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n,
          Game.advantage_comm (F.hashedElGamalIdealDDHGame setup H adversary true n)
            (F.hashedElGamalUniformPadGame setup msgLen adversary true n),
          Game.advantage_comm (F.hashedElGamalCPAGame setup H adversary true n)
            (F.hashedElGamalIdealDDHGame setup H adversary true n),
          add_assoc]

/-- **Hashed ElGamal encryption is IND-CPA secure under DDH and `SecureKDF`**
([BonehShoup2023], Section 11.5.2, Theorem 11.5, pp. 448–450): when `H` is computable in
polynomial time, every uniform strict PPT `Encryption.WordAdversary` has negligible IND-CPA
distinguishing advantage. -/
theorem DDH.negligible_hashedElGamalCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool} {msgLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hKDF : F.SecureKDF setup H msgLen)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
        (F.hashedElGamalCPAGame setup H adversary true n) :=
  negligible_of_le
    ((((hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA false)).add
      (hKDF _ (F.isPPTOn_hashedElGamalToKDFDistinguisher hA false))).add
      (hKDF _ (F.isPPTOn_hashedElGamalToKDFDistinguisher hA true))).add
      (hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA true)))
    (F.advantage_hashedElGamalCPAGame_le setup H msgLen adversary)

end Cslib.Crypto.PrimeOrderGroupFamily
