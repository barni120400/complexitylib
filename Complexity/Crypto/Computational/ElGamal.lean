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

Over a `PrimeOrderGroupFamily`, multiplicative ElGamal encryption ([BonehShoup2023], Exercise 11.5)
uses a group description `d`, a secret exponent `α : ZMod (F.order d)`, and the public key
`u = α • g`.
To encrypt a group element `m : F.Carrier d` with randomness `β : ZMod (F.order d)`, the sender
forms the ciphertext `(v, e) = (β • g, β • u + m) = (β • g, (α * β) • g + m)`. Decryption recovers
`e - α • v = m`, and the word-level operations `encodeElGamalPublicKey`, `encodeElGamalEncrypt`,
and `decodeElGamal` compute public-key generation, encryption, and decryption in polynomial time
from natural-number exponents and encoded group elements using `F.generator`, `F.order`, `F.smul`,
and `F.add`.

We prove IND-CPA security under DDH in three settings:
1. **Bit ElGamal** (`elGamalCPAGame`, `elGamalINDCPA`, `DDH.elGamalINDCPA`): `false` and `true`
   are embedded as `0` and `g` (`bitElement`, `encodeBit`), and `Encryption.Adversary` chooses two
   challenge bits.
2. **Group-element ElGamal** (`WordAdversary`, `elGamalGroupCPAGame`,
   `DDH.negligible_elGamalGroupCPAGame`, [BonehShoup2023], Exercise 11.5(a)): a two-stage
   word-message adversary chooses any two valid encoded group elements `(m₀, m₁)` in
   `Set.range (F.encode d)`. Replacing the Diffie–Hellman mask `(α * β) • g` with an independent
   uniform `γ • g` masks any chosen group element perfectly (`uniform_smul_generator_add`).
3. **Hashed ElGamal** (`hashedElGamalEncrypt`, `hashedElGamalDecrypt`, `hashedElGamalCPAGame`,
   `DDH.negligible_hashedElGamalCPAGame`, [BonehShoup2023], Section 11.4, Theorem 11.1): given a
   deterministic polynomial-time hash function `H : F.Desc × List Bool → List Bool`, the sender
   masks an `ℓ`-bit message word `m` as `(β • g, H (d, encode (β • u)) ⊕ m)`. Security reduces to
   `DDH` together with entropy smoothing (`HashSmoothing`: indistinguishability of
   `H (d, encode (γ • g))` from a uniform `msgLen n`-bit pad).

## Limitations

Key generation and challenge encryption in the security games sample exact uniform exponents in
`ZMod (F.order d)` at the `PMF` level (`PMF.uniformOfFintype (ZMod (F.order d))`), because an odd
prime order `F.order d` cannot be sampled with exact uniformity by a bounded-time fair-coin
`ProbComp` machine; deterministic public-key computation (`encodeElGamalPublicKey`), encryption
given randomness (`encodeElGamalEncrypt`, `encodeHashedElGamalEncrypt`), and decryption
(`decodeElGamal`, `decodeHashedElGamal`) are certified polynomial time on words. The
Diffie–Hellman and entropy-smoothing assumptions are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecrypt`: algebraic ElGamal encryption and decryption.
* `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalPublicKey`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal`: polynomial-time public-key generation,
  encryption, and decryption on encoded group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.bitElement`, `Cslib.Crypto.PrimeOrderGroupFamily.encodeBit`:
  embedding and polynomial-time encoding of message bits as group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalINDCPA`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalToDDHDistinguisher`: bit ElGamal IND-CPA experiment,
  security property, and DDH distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.WordAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ValidGroupMessages`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalGroupToDDHDistinguisher`: group-element ElGamal
  IND-CPA experiment and DDH reduction ([BonehShoup2023], Exercise 11.5(a)).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeHashedElGamal`: algebraic and word-level Hashed ElGamal
  encryption and decryption ([BonehShoup2023], Section 11.4).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalCPAGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalIdealDDHGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalUniformPadGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.HashSmoothing`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalToHashDistinguisher`: Hashed ElGamal IND-CPA
  experiments, hybrids, and reductions ([BonehShoup2023], Section 11.4, Theorem 11.1).

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
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.elGamalINDCPA`: ElGamal IND-CPA security for bit
  messages under DDH ([BonehShoup2023], Exercise 11.5(a)).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_elGamalGroupCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_elGamalGroupToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_elGamalGroupCPAGame`: ElGamal IND-CPA
  security for group-element messages under DDH ([BonehShoup2023], Exercise 11.5(a)).
* `Cslib.Crypto.PrimeOrderGroupFamily.hashedElGamalDecrypt_hashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_encodeHashedElGamalEncrypt`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_decodeHashedElGamal`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_hashedElGamalCPAGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToDDHDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_hashedElGamalToHashDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCPAGame`: Hashed ElGamal
  correctness, polynomial-time certificates, and IND-CPA security under DDH and entropy smoothing
  ([BonehShoup2023], Section 11.4, Theorem 11.1).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.4 (Theorem 11.1, Hashed ElGamal) and Exercise 11.5(a)
  (multiplicative ElGamal).
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

/-- The IND-CPA experiment for ElGamal bit encryption ([BonehShoup2023], Exercise 11.5): draw `d`
from `setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the encoded public key
`(d, encode (α • g))` to `adversary.choose`, encrypt the selected challenge bit under a fresh
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

/-- IND-CPA security of ElGamal bit encryption over `F` for a setup law `setup`: every uniform
strict PPT `Encryption.Adversary` has negligible distinguishing advantage between challenge bit
`false` and challenge bit `true`. -/
def elGamalINDCPA (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.elGamalCPAGame setup adversary false n)
    (fun adversary n => F.elGamalCPAGame setup adversary true n)
    Encryption.Adversary.IsPPT

/-- The DDH distinguisher constructed from an IND-CPA adversary ([BonehShoup2023], proof of
Exercise 11.5(a)): given `(d, u, v, w)`, pass `(d, u)` as the public key, encrypt the selected
challenge bit by masking with `w`, and return the adversary's guess. -/
def elGamalToDDHDistinguisher (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits
    (input.2.2.1, F.add (input.1, input.2.2.2, F.encodeBit input.1 m))
  adversary.guess n choice.2 ct

/-- In the real DDH game, `elGamalToDDHDistinguisher` simulates `elGamalCPAGame` exactly. -/
@[simp] theorem ddhRealGame_elGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary bit) n =
      F.elGamalCPAGame setup adversary bit n := by
  simp only [ddhRealGame, elGamalToDDHDistinguisher, elGamalCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind, F.encodeBit_eq_encode_bitElement, F.add_encode]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, the uniform element `γ • g` perfectly masks the challenge bit, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n := by
  simp only [ddhIdealGame, elGamalToDDHDistinguisher, ProbComp.eval_bind, PMF.monad_bind_eq_bind,
    F.encodeBit_eq_encode_bitElement, F.add_encode, Bool.false_eq_true, ↓reduceIte]
  congr 1; funext d
  congr 1; funext α
  congr 1; funext β
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1; funext choice
  exact (F.uniform_smul_generator_add d (F.bitElement d choice.1.1)
    (fun x => ProbComp.eval (adversary.guess n choice.2
      (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).trans
    (F.uniform_smul_generator_add d (F.bitElement d choice.1.2)
      (fun x => ProbComp.eval (adversary.guess n choice.2
        (encPair encBits encBits (F.encode d (β • F.generator d), F.encode d x))))).symm

/-- **Quantitative reduction of ElGamal IND-CPA to DDH** ([BonehShoup2023], Exercise 11.5(a)): the
IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalToDDHDistinguisher adversary false` and `elGamalToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : Encryption.Adversary) (n : ℕ) :
    Game.advantage (F.elGamalCPAGame setup adversary false n)
      (F.elGamalCPAGame setup adversary true n) ≤
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary false) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) +
      Game.advantage (F.ddhRealGame setup (F.elGamalToDDHDistinguisher adversary true) n)
        (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n) := by
  rw [← F.ddhRealGame_elGamalToDDHDistinguisher setup adversary false n,
    ← F.ddhRealGame_elGamalToDDHDistinguisher setup adversary true n]
  refine (Game.advantage_triangle _
    (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary false) n) _).trans ?_
  rw [F.ddhIdealGame_elGamalToDDHDistinguisher_false_eq_true setup adversary n,
    Game.advantage_comm (F.ddhIdealGame setup (F.elGamalToDDHDistinguisher adversary true) n)]

/-- `elGamalToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalToDDHDistinguisher {adversary : Encryption.Adversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalToDDHDistinguisher adversary bit input.1 input.2) := by
  have hchoose := hA.choose
  have hguess := hA.guess
  have hadd := F.computableInPolyTime_add.tidy
  have hencBit := F.computableInPolyTime_encodeBit.tidy
  have hpk : ComputableTidilyInPolyTime
      (fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
        encPair F.encDesc encBits (input.2.1, input.2.2.1))
      (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBits :=
    (ComputableTidilyInPolyTime.encode (encPair F.encDesc encBits)).comp (by fun_prop)
  have hm : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Bool × Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBool encBool) encBits))
      encBool := by
    cases bit <;> fun_prop
  have hct : ComputableTidilyInPolyTime
      (fun p : (ℕ × F.Desc × List Bool × List Bool × List Bool) × (Bool × Bool) × List Bool =>
        (p.1.1, p.2.2, encPair encBits encBits
          (p.1.2.2.2.1,
            F.add (p.1.2.1, p.1.2.2.2.2,
              F.encodeBit p.1.2.1 (if bit then p.2.1.2 else p.2.1.1)))))
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBool encBool) encBits))
      (encPair encUnary (encPair encBits encBits)) := by
    refine ComputableTidilyInPolyTime.prod (by fun_prop) ?_
    refine ComputableTidilyInPolyTime.prod (by fun_prop) ?_
    exact (ComputableTidilyInPolyTime.encode (encPair encBits encBits)).comp (by fun_prop)
  unfold elGamalToDDHDistinguisher
  exact (hchoose.preprocess (by fun_prop) hpk).bind_with
    (hguess.preprocess hct.computableInPolyTime)

/-- **ElGamal bit encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a)). -/
theorem DDH.elGamalINDCPA {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) : F.elGamalINDCPA setup := by
  intro adversary hA
  exact negligible_of_le
    ((hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA false)).add
      (hDDH _ (F.isPPTOn_elGamalToDDHDistinguisher hA true)))
    (F.advantage_elGamalCPAGame_le setup adversary)

/-! ### Group-element ElGamal IND-CPA security under DDH -/

/-- A two-stage chosen-plaintext adversary for word-message public-key encryption: `choose`
receives the security parameter and the encoded public key and outputs a pair of challenge message
words `(m₀, m₁)` together with a saved state word; `guess` receives the security parameter, saved
state word, and encoded challenge ciphertext and outputs a distinguishing bit. -/
structure WordAdversary where
  /-- Choose two challenge message words `(m₀, m₁)` and a saved state word. -/
  choose : ℕ → List Bool → ProbComp ((List Bool × List Bool) × List Bool)
  /-- Guess the challenge bit from the saved state word and encoded challenge ciphertext. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- Uniform strict PPT admissibility for a `WordAdversary`. -/
structure WordAdversary.IsPPT (adversary : WordAdversary) : Prop where
  /-- Stage 1 (`choose`) is uniform strict PPT. -/
  choose : Probability.IsPPT (encPair (encPair encBits encBits) encBits) adversary.choose
  /-- Stage 2 (`guess`) is uniform strict PPT. -/
  guess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- A challenge choice `((m₀, m₁), state)` consists of valid encoded group elements in
`F.Carrier d` when both `m₀` and `m₁` lie in `Set.range (F.encode d)`. -/
def ValidGroupMessages (d : F.Desc) (choice : (List Bool × List Bool) × List Bool) : Prop :=
  (∃ x₀ : F.Carrier d, choice.1.1 = F.encode d x₀) ∧
    (∃ x₁ : F.Carrier d, choice.1.2 = F.encode d x₁)

/-- The IND-CPA experiment for group-element ElGamal encryption ([BonehShoup2023],
Exercise 11.5(a)): draw `d ← setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the
encoded public key `(d, encode (α • g))` to `adversary.choose`, encrypt the selected encoded group
element `m` under a fresh uniform exponent `β : ZMod (F.order d)` via `F.add`, and pass the saved
state and encoded ciphertext to `adversary.guess`. -/
noncomputable def elGamalGroupCPAGame (setup : ℕ → PMF F.Desc)
    (adversary : WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      F.add (d, F.encode d ((α * β) • F.generator d), m))
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- The DDH distinguisher constructed from a group-element ElGamal IND-CPA adversary
([BonehShoup2023], Exercise 11.5(a)): given `(d, u, v, w)`, pass `(d, u)` as the public key, mask
the selected encoded group element with `w` using `F.add`, and return the adversary's guess. -/
def elGamalGroupToDDHDistinguisher (adversary : WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits (input.2.2.1, F.add (input.1, input.2.2.2, m))
  adversary.guess n choice.2 ct

/-- In the real DDH game, `elGamalGroupToDDHDistinguisher` simulates `elGamalGroupCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_elGamalGroupToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    F.ddhRealGame setup (F.elGamalGroupToDDHDistinguisher adversary bit) n =
      F.elGamalGroupCPAGame setup adversary bit n := by
  simp only [ddhRealGame, elGamalGroupToDDHDistinguisher, elGamalGroupCPAGame, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  rw [PMF.bind_comm]

/-- In the ideal DDH game, whenever `adversary.choose` outputs valid encoded group elements in
`F.Carrier d`, the uniform element `γ • g` perfectly masks both candidate group elements, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem ddhIdealGame_elGamalGroupToDDHDistinguisher_false_eq_true (setup : ℕ → PMF F.Desc)
    (adversary : WordAdversary) (n : ℕ)
    (hvalid : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      F.ValidGroupMessages d choice) :
    F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n =
      F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n := by
  simp only [ddhIdealGame, elGamalGroupToDDHDistinguisher, ProbComp.eval_bind,
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

/-- **Quantitative reduction of group-element ElGamal IND-CPA to DDH** ([BonehShoup2023],
Exercise 11.5(a)): when `adversary.choose` outputs valid encoded group elements at parameter `n`,
the IND-CPA distinguishing advantage of `adversary` is bounded by the sum of the DDH advantages of
`elGamalGroupToDDHDistinguisher adversary false` and
`elGamalGroupToDDHDistinguisher adversary true`. -/
theorem advantage_elGamalGroupCPAGame_le (setup : ℕ → PMF F.Desc)
    (adversary : WordAdversary) (n : ℕ)
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
        (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n) := by
  rw [← F.ddhRealGame_elGamalGroupToDDHDistinguisher setup adversary false n,
    ← F.ddhRealGame_elGamalGroupToDDHDistinguisher setup adversary true n]
  refine (Game.advantage_triangle _
    (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary false) n) _).trans ?_
  rw [F.ddhIdealGame_elGamalGroupToDDHDistinguisher_false_eq_true setup adversary n hvalid,
    Game.advantage_comm (F.ddhIdealGame setup (F.elGamalGroupToDDHDistinguisher adversary true) n)]

/-- `elGamalGroupToDDHDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_elGamalGroupToDDHDistinguisher {adversary : WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.elGamalGroupToDDHDistinguisher adversary bit input.1 input.2) := by
  have hchoose := hA.choose.on
  have hguess := hA.guess
  have hadd := F.computableInPolyTime_add
  have hm : ComputableInPolyTime
      (fun p :
          (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
            (List Bool × List Bool) × List Bool =>
        if bit then p.2.1.2 else p.2.1.1)
      (encPair (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        (encPair (encPair encBits encBits) encBits))
      encBits := by
    cases bit <;> fun_prop
  unfold elGamalGroupToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1, F.add (p.1.2.1, p.1.2.2.2.2, if bit then p.2.1.2 else p.2.1.1))))
    (by fun_prop)

/-- **Group-element ElGamal encryption is IND-CPA secure under the DDH assumption**
([BonehShoup2023], Exercise 11.5(a)): every uniform strict PPT `WordAdversary` that eventually
outputs valid encoded group elements has negligible IND-CPA distinguishing advantage. -/
theorem DDH.negligible_elGamalGroupCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) {adversary : WordAdversary} (hA : adversary.IsPPT)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      F.ValidGroupMessages d choice) :
    Negligible fun n =>
      Game.advantage (F.elGamalGroupCPAGame setup adversary false n)
        (F.elGamalGroupCPAGame setup adversary true n) :=
  negligible_of_eventually_le
    ((hDDH _ (F.isPPTOn_elGamalGroupToDDHDistinguisher hA false)).add
      (hDDH _ (F.isPPTOn_elGamalGroupToDDHDistinguisher hA true)))
    (hvalid.mono fun n hn => F.advantage_elGamalGroupCPAGame_le setup adversary n hn)

/-! ### Hashed ElGamal encryption and IND-CPA security ([BonehShoup2023], Section 11.4) -/

/-- Pointwise XOR with a pad at least as long as `m` is an involution. -/
theorem zipWith_xor_self_left {pad m : List Bool} (hlen : m.length ≤ pad.length) :
    pad.zipWith Bool.xor (pad.zipWith Bool.xor m) = m := by
  apply List.ext_getElem (by simp [Nat.min_eq_right hlen])
  intro i h₁ h₂
  simp only [List.getElem_zipWith]
  cases pad[i] <;> cases m[i] <;> rfl

/-- Pointwise XOR of a uniform `k`-bit pad with a fixed `k`-bit message word `m` preserves the
uniform distribution `uniformList k`. -/
theorem uniformList_map_zipWith_xor {k : ℕ} {m : List Bool} (hm : m.length = k) :
    (Cslib.BitString.uniformList k).map (fun pad => pad.zipWith Bool.xor m) =
      Cslib.BitString.uniformList k := by
  unfold Cslib.BitString.uniformList
  rw [PMF.map_comp]
  have hfun : (fun pad : List Bool => pad.zipWith Bool.xor m) ∘ List.ofFn =
      List.ofFn ∘ Equiv.addRight (Cslib.BitString.ofList k m) := by
    funext pad
    change (List.ofFn pad).zipWith Bool.xor m = List.ofFn (pad + Cslib.BitString.ofList k m)
    rw [Cslib.BitString.ofFn_add, Cslib.BitString.ofFn_ofList hm]
  rw [hfun, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]

/-- Algebraic Hashed ElGamal encryption ([BonehShoup2023], Section 11.4): given hash function
`H : F.Desc × List Bool → List Bool`, public key `u : F.Carrier d`, message word `m : List Bool`,
and randomness `β : ZMod (F.order d)`, output `(β • g, H (d, encode (β • u)) ⊕ m)`. -/
def hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc) (u : F.Carrier d)
    (m : List Bool) (β : ZMod (F.order d)) : F.Carrier d × List Bool :=
  (β • F.generator d, (H (d, F.encode d (β • u))).zipWith Bool.xor m)

/-- Under a genuine public key `u = α • g`, Hashed ElGamal masks `m` with
`H (d, encode ((α * β) • g))`. -/
theorem hashedElGamalEncrypt_smul_generator (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β : ZMod (F.order d)) (m : List Bool) :
    F.hashedElGamalEncrypt H d (α • F.generator d) m β =
      (β • F.generator d, (H (d, F.encode d ((α * β) • F.generator d))).zipWith Bool.xor m) := by
  simp only [hashedElGamalEncrypt, smul_smul, mul_comm β α]

/-- Algebraic Hashed ElGamal decryption ([BonehShoup2023], Section 11.4): given secret key
`α : ZMod (F.order d)` and ciphertext `(v, c)`, recover `H (d, encode (α • v)) ⊕ c`. -/
def hashedElGamalDecrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α : ZMod (F.order d)) (ct : F.Carrier d × List Bool) : List Bool :=
  (H (d, F.encode d (α • ct.1))).zipWith Bool.xor ct.2

/-- **Hashed ElGamal decryption correctness**: when the hash output is at least as long as `m`,
decrypting an encryption under `u = α • g` with secret key `α` recovers `m`. -/
@[simp] theorem hashedElGamalDecrypt_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (α β : ZMod (F.order d)) {m : List Bool}
    (hlen : m.length ≤ (H (d, F.encode d ((α * β) • F.generator d))).length) :
    F.hashedElGamalDecrypt H d α (F.hashedElGamalEncrypt H d (α • F.generator d) m β) = m := by
  simp only [hashedElGamalDecrypt, hashedElGamalEncrypt_smul_generator, smul_smul,
    zipWith_xor_self_left hlen]

/-- Word-level Hashed ElGamal encryption: given `(d, encode u, m, b)`, compute
`(encode (b • g), H (d, encode (b • u)) ⊕ m)`. -/
def encodeHashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × List Bool × List Bool × ℕ) : List Bool × List Bool :=
  let d := input.1
  let u := input.2.1
  let m := input.2.2.1
  let b := input.2.2.2
  (F.smul (d, b, F.encode d (F.generator d)),
    (H (d, F.smul (d, b, u))).zipWith Bool.xor m)

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
  have hxor := (ComputableTidilyInPolyTime.bitsZipWith Bool.xor).computableInPolyTime.comp
    (hpad.prod hm)
  exact hv.prod hxor

/-- Word-level Hashed ElGamal decryption: given `(d, a, encode v, c)`, compute
`H (d, encode (a • v)) ⊕ c`. -/
def decodeHashedElGamal (H : F.Desc × List Bool → List Bool)
    (input : F.Desc × ℕ × List Bool × List Bool) : List Bool :=
  (H (input.1, F.smul (input.1, input.2.1, input.2.2.1))).zipWith Bool.xor input.2.2.2

/-- `decodeHashedElGamal` computes `hashedElGamalDecrypt` on encoded group elements. -/
@[simp] theorem decodeHashedElGamal_encode (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (v : F.Carrier d) (c : List Bool) :
    F.decodeHashedElGamal H (d, a, F.encode d v, c) =
      F.hashedElGamalDecrypt H d (a : ZMod (F.order d)) (v, c) := by
  simp only [decodeHashedElGamal, hashedElGamalDecrypt, F.smul_encode]

/-- Word-level Hashed ElGamal decryption of an honest encryption recovers `m` whenever the hash
output is at least as long as `m`. -/
theorem decodeHashedElGamal_hashedElGamalEncrypt (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (a : ℕ) (β : ZMod (F.order d)) {m : List Bool}
    (hlen :
      m.length ≤
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
  exact (ComputableTidilyInPolyTime.bitsZipWith Bool.xor).computableInPolyTime.comp
    (hpad.prod hc)

/-- The IND-CPA experiment for Hashed ElGamal encryption ([BonehShoup2023], Section 11.4,
Theorem 11.1): draw `d ← setup n` and a uniform secret key `α : ZMod (F.order d)`, pass the
encoded public key `(d, encode (α • g))` to `adversary.choose`, encrypt the selected message word
`m` under a fresh uniform exponent `β : ZMod (F.order d)` by masking with
`H (d, encode ((α * β) • g))`, and pass the saved state and encoded ciphertext to
`adversary.guess`. -/
noncomputable def hashedElGamalCPAGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      (H (d, F.encode d ((α * β) • F.generator d))).zipWith Bool.xor m)
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 1 for Hashed ElGamal ([BonehShoup2023], proof of Theorem 11.1): replace the
Diffie–Hellman shared element `(α * β) • g` with an independent uniform group element `γ • g`. -/
noncomputable def hashedElGamalIdealDDHGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d),
      (H (d, F.encode d (γ • F.generator d))).zipWith Bool.xor m)
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- Hybrid 2 for Hashed ElGamal ([BonehShoup2023], proof of Theorem 11.1): replace the hashed
group element `H (d, encode (γ • g))` with an independent uniform `msgLen n`-bit pad
`pad ← Cslib.BitString.uniformList (msgLen n)`. -/
noncomputable def hashedElGamalUniformPadGame (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let pk := encPair F.encDesc encBits (d, F.encode d (α • F.generator d))
  let choice ← ProbComp.eval (adversary.choose n pk)
  let m := if bit then choice.1.2 else choice.1.1
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  let ct := encPair encBits encBits
    (F.encode d (β • F.generator d), pad.zipWith Bool.xor m)
  ProbComp.eval (adversary.guess n choice.2 ct)

/-- The real entropy-smoothing / hash-pseudorandomness experiment ([BonehShoup2023], Section 11.4):
draw `d ← setup n` and independent uniform `α, β, γ : ZMod (F.order d)`, and give the
distinguisher `(d, encode (α • g), encode (β • g), H (d, encode (γ • g)))`. -/
noncomputable def hashRealGame (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d),
      H (d, F.encode d (γ • F.generator d))))

/-- The ideal entropy-smoothing / hash-pseudorandomness experiment ([BonehShoup2023], Section 11.4):
draw `d ← setup n`, independent uniform `α, β : ZMod (F.order d)`, and an independent uniform
`msgLen n`-bit pad `pad ← Cslib.BitString.uniformList (msgLen n)`, and give the distinguisher
`(d, encode (α • g), encode (β • g), pad)`. -/
noncomputable def hashIdealGame (setup : ℕ → PMF F.Desc) (msgLen : ℕ → ℕ)
    (distinguisher : ℕ → F.Desc × List Bool × List Bool × List Bool → ProbComp Bool)
    (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let pad ← Cslib.BitString.uniformList (msgLen n)
  ProbComp.eval (distinguisher n
    (d, F.encode d (α • F.generator d), F.encode d (β • F.generator d), pad))

/-- Computational entropy smoothing of `H` over `F` ([BonehShoup2023], Section 11.4): every uniform
strict PPT distinguisher has negligible advantage between `hashRealGame` and `hashIdealGame`. -/
def HashSmoothing (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ) : Prop :=
  Game.Indistinguishable (F.hashRealGame setup H) (F.hashIdealGame setup msgLen)
    fun distinguisher =>
      IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
        encBool (fun input => distinguisher input.1 input.2)

/-- The DDH distinguisher constructed from a Hashed ElGamal IND-CPA adversary ([BonehShoup2023],
proof of Theorem 11.1): given `(d, u, v, w)`, pass `(d, u)` as the public key, mask the selected
message word with `H (d, w)`, and return the adversary's guess. -/
def hashedElGamalToDDHDistinguisher (H : F.Desc × List Bool → List Bool)
    (adversary : WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits
    (input.2.2.1, (H (input.1, input.2.2.2)).zipWith Bool.xor m)
  adversary.guess n choice.2 ct

/-- In the real DDH game, `hashedElGamalToDDHDistinguisher` simulates `hashedElGamalCPAGame`
exactly. -/
@[simp] theorem ddhRealGame_hashedElGamalToDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
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
    (H : F.Desc × List Bool → List Bool) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
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
    {adversary : WordAdversary} (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToDDHDistinguisher H adversary bit input.1 input.2) := by
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
  unfold hashedElGamalToDDHDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1,
          (H (p.1.2.1, p.1.2.2.2.2)).zipWith Bool.xor (if bit then p.2.1.2 else p.2.1.1))))
    (by fun_prop)

/-- The entropy-smoothing distinguisher constructed from a Hashed ElGamal IND-CPA adversary
([BonehShoup2023], proof of Theorem 11.1): given `(d, u, v, pad)`, pass `(d, u)` as the public key,
mask the selected message word directly with `pad`, and return the adversary's guess. -/
def hashedElGamalToHashDistinguisher (adversary : WordAdversary) (bit : Bool) (n : ℕ)
    (input : F.Desc × List Bool × List Bool × List Bool) : ProbComp Bool := do
  let pk := encPair F.encDesc encBits (input.1, input.2.1)
  let choice ← adversary.choose n pk
  let m := if bit then choice.1.2 else choice.1.1
  let ct := encPair encBits encBits (input.2.2.1, input.2.2.2.zipWith Bool.xor m)
  adversary.guess n choice.2 ct

/-- In the real hash game, `hashedElGamalToHashDistinguisher` simulates `hashedElGamalIdealDDHGame`
exactly. -/
@[simp] theorem hashRealGame_hashedElGamalToHashDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    F.hashRealGame setup H (F.hashedElGamalToHashDistinguisher adversary bit) n =
      F.hashedElGamalIdealDDHGame setup H adversary bit n := by
  simp only [hashRealGame, hashedElGamalToHashDistinguisher, hashedElGamalIdealDDHGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- In the ideal hash game, `hashedElGamalToHashDistinguisher` simulates
`hashedElGamalUniformPadGame` exactly. -/
@[simp] theorem hashIdealGame_hashedElGamalToHashDistinguisher (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    F.hashIdealGame setup msgLen (F.hashedElGamalToHashDistinguisher adversary bit) n =
      F.hashedElGamalUniformPadGame setup msgLen adversary bit n := by
  simp only [hashIdealGame, hashedElGamalToHashDistinguisher, hashedElGamalUniformPadGame,
    ProbComp.eval_bind, PMF.monad_bind_eq_bind]
  congr 1; funext d
  congr 1; funext α
  conv_lhs =>
    enter [2, β]
    rw [PMF.bind_comm]
  rw [PMF.bind_comm]

/-- `hashedElGamalToHashDistinguisher` is uniform strict PPT whenever `adversary` is. -/
theorem isPPTOn_hashedElGamalToHashDistinguisher {adversary : WordAdversary}
    (hA : adversary.IsPPT) (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits))))
      encBool (fun input => F.hashedElGamalToHashDistinguisher adversary bit input.1 input.2) := by
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
  unfold hashedElGamalToHashDistinguisher
  refine (hchoose.preprocess
    (prepare := fun input : ℕ × F.Desc × List Bool × List Bool × List Bool =>
      (input.1, encPair F.encDesc encBits (input.2.1, input.2.2.1))) (by fun_prop)).bind_with ?_
  exact hguess.preprocess
    (prepare := fun p :
        (ℕ × F.Desc × List Bool × List Bool × List Bool) ×
          (List Bool × List Bool) × List Bool =>
      (p.1.1, p.2.2, encPair encBits encBits
        (p.1.2.2.2.1, p.1.2.2.2.2.zipWith Bool.xor (if bit then p.2.1.2 else p.2.1.1))))
    (by fun_prop)

/-- In `hashedElGamalUniformPadGame`, whenever `adversary.choose` outputs message words of length
`msgLen n`, the uniform `msgLen n`-bit pad perfectly masks the challenge message word, so the
experiments for `bit = false` and `bit = true` are identical. -/
theorem hashedElGamalUniformPadGame_false_eq_true (setup : ℕ → PMF F.Desc)
    (msgLen : ℕ → ℕ) (adversary : WordAdversary) (n : ℕ)
    (hlen : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      choice.1.1.length = msgLen n ∧ choice.1.2.length = msgLen n) :
    F.hashedElGamalUniformPadGame setup msgLen adversary false n =
      F.hashedElGamalUniformPadGame setup msgLen adversary true n := by
  simp only [hashedElGamalUniformPadGame, PMF.monad_bind_eq_bind,
    Bool.false_eq_true, ↓reduceIte]
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ (setup n).support
  · congr 1
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun α => ?_
    congr 1
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun choice => ?_
    by_cases hchoice :
        choice ∈
          (ProbComp.eval
            (adversary.choose n
              (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support
    · congr 1
      obtain ⟨hlen₀, hlen₁⟩ := hlen d hd α choice hchoice
      rw [PMF.bind_apply, PMF.bind_apply]
      refine tsum_congr fun β => ?_
      congr 1
      have hpad (m : List Bool) (hm : m.length = msgLen n) :
          ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
            ProbComp.eval (adversary.guess n choice.2
              (encPair encBits encBits
                (F.encode d (β • F.generator d), pad.zipWith Bool.xor m)))) =
          ((Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
            ProbComp.eval (adversary.guess n choice.2
              (encPair encBits encBits (F.encode d (β • F.generator d), pad)))) := by
        have hmap := congrArg
          (fun p : PMF (List Bool) =>
            p.bind fun pad =>
              ProbComp.eval (adversary.guess n choice.2
                (encPair encBits encBits (F.encode d (β • F.generator d), pad))))
          (uniformList_map_zipWith_xor hm)
        simpa only [PMF.bind_map, Function.comp_def] using hmap
      exact congrArg (fun p : PMF Bool => p b)
        ((hpad choice.1.1 hlen₀).trans (hpad choice.1.2 hlen₁).symm)
    · have h0 :
          ProbComp.eval
            (adversary.choose n
              (encPair F.encDesc encBits (d, F.encode d (α • F.generator d)))) choice = 0 := by
        rwa [PMF.mem_support_iff, not_not] at hchoice
      simp only [h0, zero_mul]
  · have hd0 : setup n d = 0 := by rwa [PMF.mem_support_iff, not_not] at hd
    simp only [hd0, zero_mul]

/-- **Quantitative reduction of Hashed ElGamal IND-CPA to DDH and entropy smoothing**
([BonehShoup2023], Section 11.4, Theorem 11.1): when `adversary.choose` outputs `msgLen n`-bit
message pairs at parameter `n`, the IND-CPA distinguishing advantage of `adversary` is bounded by
the sum of the two DDH advantages of `hashedElGamalToDDHDistinguisher` and the two
entropy-smoothing advantages of `hashedElGamalToHashDistinguisher`. -/
theorem advantage_hashedElGamalCPAGame_le (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (adversary : WordAdversary) (n : ℕ)
    (hlen : ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      choice.1.1.length = msgLen n ∧ choice.1.2.length = msgLen n) :
    Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
      (F.hashedElGamalCPAGame setup H adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n)
        (F.ddhIdealGame setup (F.hashedElGamalToDDHDistinguisher H adversary false) n) +
      Game.advantage
        (F.hashRealGame setup H (F.hashedElGamalToHashDistinguisher adversary false) n)
        (F.hashIdealGame setup msgLen (F.hashedElGamalToHashDistinguisher adversary false) n) +
      Game.advantage
        (F.hashRealGame setup H (F.hashedElGamalToHashDistinguisher adversary true) n)
        (F.hashIdealGame setup msgLen (F.hashedElGamalToHashDistinguisher adversary true) n) +
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
  rw [F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n hlen] at h2
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
          hashRealGame_hashedElGamalToHashDistinguisher,
          hashIdealGame_hashedElGamalToHashDistinguisher,
          F.hashedElGamalUniformPadGame_false_eq_true setup msgLen adversary n hlen,
          Game.advantage_comm (F.hashedElGamalIdealDDHGame setup H adversary true n)
            (F.hashedElGamalUniformPadGame setup msgLen adversary true n),
          Game.advantage_comm (F.hashedElGamalCPAGame setup H adversary true n)
            (F.hashedElGamalIdealDDHGame setup H adversary true n),
          add_assoc]

/-- **Hashed ElGamal encryption is IND-CPA secure under DDH and entropy smoothing**
([BonehShoup2023], Section 11.4, Theorem 11.1): when `H` is computable in polynomial time, every
uniform strict PPT `WordAdversary` that eventually outputs `msgLen n`-bit message pairs has
negligible IND-CPA distinguishing advantage. -/
theorem DDH.negligible_hashedElGamalCPAGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool} {msgLen : ℕ → ℕ}
    (hDDH : F.DDH setup) (hSmooth : F.HashSmoothing setup H msgLen)
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    {adversary : WordAdversary} (hA : adversary.IsPPT)
    (hlen : ∀ᶠ n in Filter.atTop, ∀ d ∈ (setup n).support, ∀ α : ZMod (F.order d),
      ∀ choice ∈
        (ProbComp.eval
          (adversary.choose n
            (encPair F.encDesc encBits (d, F.encode d (α • F.generator d))))).support,
      choice.1.1.length = msgLen n ∧ choice.1.2.length = msgLen n) :
    Negligible fun n =>
      Game.advantage (F.hashedElGamalCPAGame setup H adversary false n)
        (F.hashedElGamalCPAGame setup H adversary true n) :=
  negligible_of_eventually_le
    ((((hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA false)).add
      (hSmooth _ (F.isPPTOn_hashedElGamalToHashDistinguisher hA false))).add
      (hSmooth _ (F.isPPTOn_hashedElGamalToHashDistinguisher hA true))).add
      (hDDH _ (F.isPPTOn_hashedElGamalToDDHDistinguisher hH hA true)))
    (hlen.mono fun n hn => F.advantage_hashedElGamalCPAGame_le setup H msgLen adversary n hn)

end Cslib.Crypto.PrimeOrderGroupFamily
