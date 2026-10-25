/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Native runtime of the chosen-message experiment

The actual experiment composes key generation, message selection, encryption and guessing.
Native certificates charge the complete sampled public key, saved adversary state and challenge
ciphertext; no independent bound on those intermediate values is assumed.

## Main results

* `Cslib.Crypto.Encryption.computableTidilyInPolyTime_sameLength`,
  `Cslib.Crypto.Encryption.computableInPolyTime_sameLength`: the equal-length word predicate
  `sameLength` is computable in polynomial time.
* `Cslib.Crypto.Encryption.AdversaryOf.IsPPT.clamp`,
  `Cslib.Crypto.Encryption.INDCPAOf.indcpaWith`,
  `Cslib.Crypto.Encryption.INDCPAOf.wordINDCPA`: clamping a uniform strict PPT adversary by a
  polynomial-time validity predicate `valid` preserves `AdversaryOf.IsPPT`, so unrestricted
  `INDCPAOf` implies `INDCPAWith` (and in particular `INDCPAOf encBits` implies `WordINDCPA`).
* `Cslib.Crypto.Encryption.isPPTOn_gameWith`, `Cslib.Crypto.Encryption.isPPTOn_wordGame`,
  `Cslib.Crypto.Encryption.isPPTOn_game`: the experiments are uniform strict PPT when their inputs
  are efficiently computed and the honest algorithms and adversary have native certificates.
* `Cslib.Crypto.Encryption.exists_keyLength_bound`: key generation supplies an executable unary
  polynomial bounding all supported public and secret keys.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2, Attack Game 11.1.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- The equal-length challenge-pair predicate `sameLength` on bit words is tidily computable in
polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_sameLength :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => sameLength p.1 p.2)
      (encPair encBits encBits) encBool := by
  unfold sameLength
  polytime

/-- The equal-length challenge-pair predicate `sameLength` on bit words is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_sameLength :
    ComputableInPolyTime (fun p : List Bool × List Bool => sameLength p.1 p.2)
      (encPair encBits encBits) encBool :=
  computableTidilyInPolyTime_sameLength.computableInPolyTime

/-- Clamping a uniform strict PPT adversary by a polynomial-time challenge-pair validity predicate
`valid` preserves `AdversaryOf.IsPPT`. -/
theorem AdversaryOf.IsPPT.clamp {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime (fun p : Msg × Msg => valid p.1 p.2)
      (encPair encMsg encMsg) encBool)
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary) :
    AdversaryOf.IsPPT encMsg (adversary.clamp valid) where
  choose := by
    have hchoose := hadversary.choose
    have hvalid' := hvalid.tidy
    let EOut := encPair (encPair encMsg encMsg) encBits
    let E := encPair (encPair encUnary encBits) EOut
    have hcond : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × (Msg × Msg) × List Bool =>
          true && valid p.2.1.1 p.2.1.2) E encBool := by
      dsimp only [E, EOut]; fun_prop
    have hsel : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × (Msg × Msg) × List Bool =>
          selectChallenge valid true p.2.1) E encMsg := by
      unfold selectChallenge
      exact hcond.cond (by dsimp only [E, EOut]; fun_prop) (by dsimp only [E, EOut]; fun_prop)
    have hpost : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × (Msg × Msg) × List Bool =>
          ((p.2.1.1, selectChallenge valid true p.2.1), p.2.2)) E EOut :=
      (ComputableTidilyInPolyTime.prod (by dsimp only [E, EOut]; fun_prop) hsel).prod
        (by dsimp only [E, EOut]; fun_prop)
    unfold Probability.IsPPT AdversaryOf.clamp
    exact hchoose.on.bind_with hpost.isPPTOn
  guess := hadversary.guess

/-- Unrestricted `INDCPAOf encMsg` implies `INDCPAWith encMsg valid` for any polynomial-time
challenge-pair validity predicate `valid`. -/
theorem INDCPAOf.indcpaWith {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAOf encMsg keyGen encrypt)
    (hvalid : ComputableInPolyTime (fun p : Msg × Msg => valid p.1 p.2)
      (encPair encMsg encMsg) encBool) :
    INDCPAWith encMsg valid keyGen encrypt := by
  intro adversary hadversary
  simpa only [eval_game_clamp] using h (adversary.clamp valid) (hadversary.clamp hvalid)

/-- Unrestricted `INDCPAOf encBits` implies `WordINDCPA` (equal-length word IND-CPA). -/
theorem INDCPAOf.wordINDCPA
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (h : INDCPAOf encBits keyGen encrypt) :
    WordINDCPA keyGen encrypt :=
  h.indcpaWith computableInPolyTime_sameLength

/-- The chosen-message experiment `gameWith valid` has a strict clock in the full encoded caller
input when `valid` is tidily computable in polynomial time. -/
@[fun_prop]
theorem isPPTOn_gameWith {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : Msg → Msg → Bool}
    (hvalid : ComputableTidilyInPolyTime (fun p : Msg × Msg => valid p.1 p.2)
      (encPair encMsg encMsg) encBool)
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hbit : ComputableTidilyInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => gameWith valid keyGen encrypt adversary (bit a) (n a)) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold gameWith selectChallenge
  ppt

/-- The equal-length bit-word chosen-message experiment `wordGame` has a strict clock in the full
encoded caller input. -/
@[fun_prop]
theorem isPPTOn_wordGame
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : WordAdversary} (hadversary : adversary.IsPPT)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hbit : ComputableTidilyInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => wordGame keyGen encrypt adversary (bit a) (n a)) :=
  isPPTOn_gameWith computableTidilyInPolyTime_sameLength hkeyGen hencrypt hadversary hn hbit

/-- The actual chosen-message experiment has a strict clock in the full encoded caller input. -/
@[fun_prop]
theorem isPPTOn_game {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    {adversary : AdversaryOf Msg} (hadversary : AdversaryOf.IsPPT encMsg adversary)
    {α : Type} {input : α ↪ List Bool} {n : α → ℕ} {bit : α → Bool}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hbit : ComputableTidilyInPolyTime bit input encBool) :
    IsPPTOn input encBool (fun a => game keyGen encrypt adversary (bit a) (n a)) := by
  have hchoose := hadversary.choose
  have hguess := hadversary.guess
  unfold game
  ppt

/-- Strict PPT key generation supplies an executable unary polynomial bounding the total public
and secret key material on every supported execution. No width function is assumed computable. -/
theorem exists_keyLength_bound {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen) :
    ∃ c d : ℕ,
      ComputableTidilyInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary ∧
      ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
        keys.1.length + keys.2.length ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hlength⟩ := hkeyGen.length_le
  refine ⟨c, d, by fun_prop, fun n keys hkeys => ?_⟩
  have hbound := hlength n keys hkeys
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at hbound
  omega

end Cslib.Crypto.Encryption
