/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Crypto.Game

/-!
# Chosen-message security for public-key encryption

The adversary receives the public key, chooses two messages of type `Msg` and saves a finite
state, then receives an encryption of the selected message. Both stages are single uniform strict
PPT algorithms. Their clocks charge the unary security parameter and the complete encoded input,
including the saved state. The adversary may retain the public key in that state.

This is the single-challenge public-key experiment of
[Boneh and Shoup, Section 11.2, Attack Game 11.1][BonehShoup2023]. Specializations to single-bit
messages (`Adversary`, `INDCPA`) and bit-word messages (`WordAdversary`, `wordGame`, `WordINDCPA`,
enforcing the textbook equal-length challenge requirement `m₀.length = m₁.length` via `sameLength`)
are provided as abbreviations. For public-key encryption, further encryptions can be computed from
the public key. The separate multi-challenge equivalence of their Theorem 11.1 is not formalized
here. Encryption correctness and efficiency of the honest algorithms remain separate properties.

## Main definitions

* `Cslib.Crypto.Encryption.AdversaryOf`, `Cslib.Crypto.Encryption.Adversary`,
  `Cslib.Crypto.Encryption.WordAdversary`: message selection and guessing with explicit saved
  state, for typed, bit, and bit-word messages.
* `Cslib.Crypto.Encryption.AdversaryOf.IsPPT`, `Cslib.Crypto.Encryption.Adversary.IsPPT`,
  `Cslib.Crypto.Encryption.WordAdversary.IsPPT`: native uniform admissibility of both stages.
* `Cslib.Crypto.Encryption.selectChallenge`, `Cslib.Crypto.Encryption.sameLength`,
  `Cslib.Crypto.Encryption.AdversaryOf.clamp`: challenge-pair validity selection, equal-length
  word predicate, and adversary clamping.
* `Cslib.Crypto.Encryption.gameWith`, `Cslib.Crypto.Encryption.game`,
  `Cslib.Crypto.Encryption.wordGame`: the key-generation and challenge-encryption experiments.
* `Cslib.Crypto.Encryption.INDCPAWith`, `Cslib.Crypto.Encryption.INDCPAOf`,
  `Cslib.Crypto.Encryption.INDCPA`, `Cslib.Crypto.Encryption.WordINDCPA`: negligible distinguishing
  advantage for every admissible adversary, fixed before the security parameter.

## Main results

* `Cslib.Crypto.Encryption.eval_game_clamp`: running `game` on `adversary.clamp valid` agrees
  distributionally with `gameWith valid`.
* `Cslib.Crypto.Encryption.eval_gameWith`, `Cslib.Crypto.Encryption.eval_game`: the experiments
  depend only on the public-key marginal.
* `Cslib.Crypto.Encryption.INDCPAWith.congr`, `Cslib.Crypto.Encryption.INDCPAOf.congr`,
  `Cslib.Crypto.Encryption.INDCPA.congr`, `Cslib.Crypto.Encryption.WordINDCPA.congr`:
  distributionally equal honest algorithms have the same security guarantee.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.2 and Section 11.3.2.
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- A chosen-message adversary over message space `Msg`. The saved word contains all data retained
between stages. -/
structure AdversaryOf (Msg : Type) where
  /-- Receive the public key, choose the two challenge messages, and save a state. -/
  choose : ℕ → List Bool → ProbComp ((Msg × Msg) × List Bool)
  /-- Receive the saved state and challenge ciphertext, then return a distinguishing bit. -/
  guess : ℕ → List Bool → List Bool → ProbComp Bool

/-- One finite-machine certificate for each whole stage over message encoding `encMsg`, including
the full saved-state cost. There is no parameter-dependent advice or separate algorithm for each
security parameter. -/
structure AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : AdversaryOf Msg) : Prop where
  /-- Message selection is uniform strict PPT on the parameter and public key. -/
  choose : Probability.IsPPT (encPair (encPair encMsg encMsg) encBits) adversary.choose
  /-- Guessing is uniform strict PPT on the parameter, saved state, and challenge ciphertext. -/
  guess : IsPPTOn (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- A chosen-message adversary for single-bit messages (`Bool`). -/
abbrev Adversary : Type := AdversaryOf Bool

/-- Native uniform strict PPT admissibility for a bit chosen-message adversary. -/
abbrev Adversary.IsPPT (adversary : Adversary) : Prop := AdversaryOf.IsPPT encBool adversary

/-- A chosen-message adversary for bit-word messages (`List Bool`). -/
abbrev WordAdversary : Type := AdversaryOf (List Bool)

/-- Native uniform strict PPT admissibility for a bit-word chosen-message adversary. -/
abbrev WordAdversary.IsPPT (adversary : WordAdversary) : Prop := AdversaryOf.IsPPT encBits adversary

/-- Select the challenge message from `choice : Msg × Msg` according to `bit` and a challenge-pair
validity predicate `valid : Msg → Msg → Bool`: when `bit = true` and
`valid choice.1 choice.2 = true`, select `choice.2`; otherwise select `choice.1`. When
`valid choice.1 choice.2 = false`, both experiments `bit = false` and `bit = true` encrypt
`choice.1`, so an inadmissible challenge pair yields zero distinguishing advantage
([BonehShoup2023], Attack Game 2.1, p. 34, and Attack Game 11.1, p. 433). -/
def selectChallenge {Msg : Type} (valid : Msg → Msg → Bool) (bit : Bool) (choice : Msg × Msg) :
    Msg :=
  if bit && valid choice.1 choice.2 then choice.2 else choice.1

/-- On challenge bit `false`, `selectChallenge` always selects `choice.1`. -/
@[simp] theorem selectChallenge_false {Msg : Type} (valid : Msg → Msg → Bool)
    (choice : Msg × Msg) :
    selectChallenge valid false choice = choice.1 :=
  rfl

/-- On challenge bit `true` and a valid challenge pair, `selectChallenge` selects `choice.2`. -/
@[simp] theorem selectChallenge_true_of_valid {Msg : Type} {valid : Msg → Msg → Bool}
    {choice : Msg × Msg} (h : valid choice.1 choice.2 = true) :
    selectChallenge valid true choice = choice.2 := by
  simp [selectChallenge, h]

/-- On an invalid challenge pair, `selectChallenge` selects `choice.1` for both `bit = false` and
`bit = true`. -/
@[simp] theorem selectChallenge_of_invalid {Msg : Type} {valid : Msg → Msg → Bool}
    (bit : Bool) {choice : Msg × Msg} (h : valid choice.1 choice.2 = false) :
    selectChallenge valid bit choice = choice.1 := by
  simp [selectChallenge, h]

/-- With the constant-`true` validity predicate, `selectChallenge` reduces to `if bit`. -/
@[simp] theorem selectChallenge_const_true {Msg : Type} (bit : Bool) (choice : Msg × Msg) :
    selectChallenge (fun _ _ => true) bit choice = if bit then choice.2 else choice.1 := by
  simp [selectChallenge]

/-- Selecting between `choice.1` and `selectChallenge valid true choice` according to `bit` agrees
with `selectChallenge valid bit choice`. -/
@[simp] theorem selectChallenge_clamp {Msg : Type} (valid : Msg → Msg → Bool) (bit : Bool)
    (choice : Msg × Msg) :
    (if bit then selectChallenge valid true choice else choice.1) =
      selectChallenge valid bit choice := by
  cases bit <;> simp [selectChallenge]

/-- Equal-length challenge-pair validity predicate for bit-word encryption
([BonehShoup2023], Attack Game 2.1, p. 34, and Attack Game 11.1, p. 433): the two chosen challenge
words `m₀, m₁ : List Bool` must have the same length (`m₀.length == m₁.length`). -/
def sameLength (m₀ m₁ : List Bool) : Bool :=
  m₀.length == m₁.length

/-- `sameLength m₀ m₁ = true` if and only if `m₀.length = m₁.length`. -/
@[simp] theorem sameLength_eq_true_iff (m₀ m₁ : List Bool) :
    sameLength m₀ m₁ = true ↔ m₀.length = m₁.length :=
  beq_iff_eq

/-- `sameLength m₀ m₁ = false` if and only if `m₀.length ≠ m₁.length`. -/
@[simp] theorem sameLength_eq_false_iff (m₀ m₁ : List Bool) :
    sameLength m₀ m₁ = false ↔ m₀.length ≠ m₁.length :=
  beq_eq_false_iff_ne

/-- Clamp a chosen-message adversary's challenge pair by `valid : Msg → Msg → Bool`, replacing
`choice.1.2` with `selectChallenge valid true choice.1` so that an invalid pair `(m₀, m₁)` becomes
`(m₀, m₀)`. -/
def AdversaryOf.clamp {Msg : Type} (valid : Msg → Msg → Bool) (adversary : AdversaryOf Msg) :
    AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    return ((choice.1.1, selectChallenge valid true choice.1), choice.2)
  guess := adversary.guess

/-- Sample the key pair and the chosen challenge encryption under challenge-pair validity predicate
`valid : Msg → Msg → Bool` using the honest algorithms. When `valid choice.1.1 choice.1.2 = false`,
both `bit = false` and `bit = true` encrypt `choice.1.1`. The secret key is never passed to the
adversary. -/
def gameWith {Msg : Type} (valid : Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let ciphertext ← encrypt n keys.1 (selectChallenge valid bit choice.1)
  adversary.guess n choice.2 ciphertext

/-- Sample the key pair and the chosen challenge encryption using the honest algorithms (where every
challenge pair is admissible, `valid = fun _ _ => true`). The secret key is never passed to the
adversary. -/
def game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let ciphertext ← encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 ciphertext

/-- With the constant-`true` validity predicate, `gameWith` reduces to `game`. -/
@[simp] theorem gameWith_const_true {Msg : Type}
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    gameWith (fun _ _ => true) keyGen encrypt adversary bit n =
      game keyGen encrypt adversary bit n := by
  simp only [gameWith, game, selectChallenge_const_true]

/-- Single-challenge chosen-message experiment for bit-word messages (`List Bool`), enforcing the
textbook equal-length requirement `m₀.length = m₁.length` ([BonehShoup2023], Attack Game 11.1,
p. 433) via `sameLength`. -/
abbrev wordGame (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : WordAdversary) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  gameWith sameLength keyGen encrypt adversary bit n

/-- Running `game` on `adversary.clamp valid` has the exact same output distribution as running
`gameWith valid` on `adversary`. -/
@[simp] theorem eval_game_clamp {Msg : Type} (valid : Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt (adversary.clamp valid) bit n) =
      ProbComp.eval (gameWith valid keyGen encrypt adversary bit n) := by
  simp only [game, gameWith, AdversaryOf.clamp, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind, selectChallenge_clamp]

/-- Single-challenge IND-CPA for encryption over message encoding `encMsg` and challenge-pair
validity predicate `valid : Msg → Msg → Bool` against every uniform strict PPT adversary. -/
def INDCPAWith {Msg : Type} (encMsg : Msg ↪ List Bool) (valid : Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (gameWith valid keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (gameWith valid keyGen encrypt adversary true n))
    (AdversaryOf.IsPPT encMsg)

/-- Single-challenge IND-CPA for encryption over message encoding `encMsg` against every uniform
strict PPT adversary (with unrestricted challenge pairs). The negligible bound may depend on the
adversary, which is fixed before the parameter. -/
def INDCPAOf {Msg : Type} (encMsg : Msg ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (game keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (game keyGen encrypt adversary true n))
    (AdversaryOf.IsPPT encMsg)

/-- Single-challenge IND-CPA for bit encryption against every uniform strict PPT adversary. -/
abbrev INDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)) : Prop :=
  INDCPAOf encBool keyGen encrypt

/-- Single-challenge IND-CPA for bit-word encryption against every uniform strict PPT adversary,
enforcing the textbook equal-length challenge condition `m₀.length = m₁.length`
([BonehShoup2023], Attack Game 11.1, p. 433) via `sameLength`. -/
abbrev WordINDCPA (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  INDCPAWith encBits sameLength keyGen encrypt

/-- Only the public-key marginal of key generation is observed by `gameWith`. -/
theorem eval_gameWith {Msg : Type} (valid : Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (gameWith valid keyGen encrypt adversary bit n) =
      (do
        let pk ← (ProbComp.eval (keyGen n)).map Prod.fst
        let choice ← ProbComp.eval (adversary.choose n pk)
        let ciphertext ← ProbComp.eval (encrypt n pk (selectChallenge valid bit choice.1))
        ProbComp.eval (adversary.guess n choice.2 ciphertext)) := by
  simp only [gameWith, ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]

/-- Only the public-key marginal of key generation is observed by the experiment. -/
theorem eval_game {Msg : Type} (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt adversary bit n) =
      (do
        let pk ← (ProbComp.eval (keyGen n)).map Prod.fst
        let choice ← ProbComp.eval (adversary.choose n pk)
        let ciphertext ← ProbComp.eval (encrypt n pk (if bit then choice.1.2 else choice.1.1))
        ProbComp.eval (adversary.guess n choice.2 ciphertext)) := by
  simp only [game, ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]

/-- Equal public-key marginals and equal encryption laws preserve `INDCPAWith`. -/
theorem INDCPAWith.congr {Msg : Type} {encMsg : Msg ↪ List Bool} {valid : Msg → Msg → Bool}
    {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAWith encMsg valid keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk msg, ProbComp.eval (encrypt n pk msg) =
      ProbComp.eval (encrypt' n pk msg)) : INDCPAWith encMsg valid keyGen' encrypt' := by
  intro adversary hadversary
  simpa only [eval_gameWith, hkeyGen, hencrypt] using h adversary hadversary

/-- Equal public-key marginals and equal encryption laws preserve security. -/
theorem INDCPAOf.congr {Msg : Type} {encMsg : Msg ↪ List Bool}
    {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (h : INDCPAOf encMsg keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk msg, ProbComp.eval (encrypt n pk msg) =
      ProbComp.eval (encrypt' n pk msg)) : INDCPAOf encMsg keyGen' encrypt' := by
  intro adversary hadversary
  simpa only [eval_game, hkeyGen, hencrypt] using h adversary hadversary

/-- Equal public-key marginals and equal bit-encryption laws preserve security. -/
theorem INDCPA.congr {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (h : INDCPA keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk bit, ProbComp.eval (encrypt n pk bit) =
      ProbComp.eval (encrypt' n pk bit)) : INDCPA keyGen' encrypt' :=
  INDCPAOf.congr h hkeyGen hencrypt

/-- Equal public-key marginals and equal word-encryption laws preserve `WordINDCPA`. -/
theorem WordINDCPA.congr {keyGen keyGen' : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt encrypt' : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (h : WordINDCPA keyGen encrypt)
    (hkeyGen : ∀ n, (ProbComp.eval (keyGen n)).map Prod.fst =
      (ProbComp.eval (keyGen' n)).map Prod.fst)
    (hencrypt : ∀ n pk msg, ProbComp.eval (encrypt n pk msg) =
      ProbComp.eval (encrypt' n pk msg)) : WordINDCPA keyGen' encrypt' :=
  INDCPAWith.congr h hkeyGen hencrypt

end Cslib.Crypto.Encryption
