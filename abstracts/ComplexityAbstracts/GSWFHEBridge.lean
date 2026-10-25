/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CryptographyBridge
import ComplexityAbstracts.Randomized
import Complexity.Crypto.Computational.Homomorphic.GSW.FullyHomomorphic

/-! # Bridge for fully homomorphic encryption from GSW

The public abstract states the GSW laws, both assumptions and every claimed property in
elementary terms. This bridge identifies them with the library's serialized programs, its
decision-LWE and circular-security experiments, `Scheme.Correct`, `Scheme.FixedWidth`, native
certificates and `Encryption.INDCPA`, and assembles the leveled endpoint for every efficiently
computable budget from the generic bootstrapping lemmas. The bridge introduces no notation or
elaboration rules.
-/

namespace ComplexityTests.Abstracts.GSWFHEBridge

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM
open Cslib.Crypto Cslib.Crypto.Homomorphic

def logSize (security : ℕ) : ℕ := 1 + Nat.clog 2 (security + 2)

def width (security : ℕ) : ℕ := 16384 * logSize security ^ 2

def dimension (security : ℕ) : ℕ := security + 1

def rows (security : ℕ) : ℕ := (dimension security + 1) * width security

def samples (security : ℕ) : ℕ := rows security + 2 * security

def secretWidth (security : ℕ) : ℕ := dimension security * width security

def ciphertextWidth (security : ℕ) : ℕ := rows security * rows security

def lowBits (w value : ℕ) : List Bool := (List.range w).map value.testBit

def rowHead (n w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) (i : ℕ) : ℕ :=
  (((((List.range n).map fun j =>
    (inputs.2.1.getD i []).getD j 0 * inputs.1.getD j 0).sum : ℕ) +
      inputs.2.2.getD i 0 : ℤ) % (2 ^ w : ℤ)).toNat

def publicWord (n m w : ℕ) (inputs : List ℕ × (List (List ℕ) × List ℤ)) : List Bool :=
  (List.range m).flatMap fun i =>
    lowBits w (rowHead n w inputs i) ++
      (List.range n).flatMap fun j => lowBits w ((inputs.2.1.getD i []).getD j 0 % 2 ^ w)

def secretWord (n w : ℕ) (secret : List ℕ) : List Bool :=
  (List.range n).flatMap fun j => lowBits w (secret.getD j 0 % 2 ^ w)

def matrixEntry (cols w : ℕ) (word : List Bool) (i j : ℕ) : ℕ :=
  ((word.drop ((i * cols + j) * w) ++ List.replicate w false).take w).foldr Nat.bit 0

def ciphertextEntry (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) (i k j : ℕ) : ℕ :=
  ((if i = j then message.toNat * 2 ^ k else 0) +
    ((List.range m).map fun r =>
      if ((coins.getD i []).getD k []).getD r false then
        matrixEntry (n + 1) w publicKey r j else 0).sum) % 2 ^ w

def ciphertextWord (n m w : ℕ) (publicKey : List Bool) (message : Bool)
    (coins : List (List (List Bool))) : List Bool :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range w).flatMap fun k =>
      (List.range (n + 1)).flatMap fun j =>
        lowBits w (ciphertextEntry n m w publicKey message coins i k j)

noncomputable def independentList {α : Type} (count : ℕ) (law : PMF α) : PMF (List α) :=
  (List.replicate count ()).mapM (fun _ => law)

noncomputable def residueLaw (w : ℕ) : PMF ℕ :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (2 ^ w))).map Fin.val

noncomputable def errorLaw (noiseWidth : ℕ) : PMF ℤ := do
  let positive ← Randomized.uniformBits noiseWidth
  let negative ← Randomized.uniformBits noiseWidth
  return (positive.count true : ℤ) - negative.count true

noncomputable def keyGeneration (security : ℕ) : PMF (List Bool × List Bool) := do
  let secret ← independentList (dimension security) (residueLaw (width security))
  let matrix ← independentList (samples security)
    (independentList (dimension security) (residueLaw (width security)))
  let errors ← independentList (samples security) (errorLaw (dimension security))
  return (publicWord (dimension security) (samples security) (width security)
    (secret, (matrix, errors)), secretWord (dimension security) (width security) secret)

noncomputable def encryption (security : ℕ) (publicKey : List Bool) (message : Bool) :
    PMF (List Bool) := do
  let coins ← independentList (dimension security + 1)
    (independentList (width security) (independentList (samples security)
      (Cslib.Probability.PMF.uniformOfFintype Bool)))
  return ciphertextWord (dimension security) (samples security) (width security)
    publicKey message coins

noncomputable def uniformMatrixWord (m k w : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin m → Fin k → ZMod (2 ^ w))).map
    (fun A => (List.ofFn fun i => (List.ofFn fun j => lowBits w (A i j).val).flatten).flatten)

noncomputable def uniformPublic (security : ℕ) : PMF (List Bool) :=
  uniformMatrixWord (samples security) (dimension security + 1) (width security)

def DecisionLWE : Prop :=
  Randomized.Indistinguishable (fun security => (keyGeneration security).map Prod.fst)
    uniformPublic

noncomputable def selfEncryption (real : Bool) (security : ℕ) : PMF (List Bool) := do
  let keys ← keyGeneration security
  let encrypted ← (if real then keys.2 else List.replicate keys.2.length false).mapM
    (encryption security keys.1)
  return Encoding.encPair Encoding.encBits (Encoding.encList Encoding.encBits) (keys.1, encrypted)

def CircularSecure : Prop :=
  Randomized.Indistinguishable (selfEncryption true) (selfEncryption false)

def Homomorphic (S : Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop) : Prop :=
  ∀ security keys, keys ∈ (ProbComp.eval (S.keyGen security)).support →
    (∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support →
        S.decrypt security keys.2 ciphertext = bit) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        S.decrypt security keys.2 ciphertext =
          C.2.eval Circuits.Boolean.interpretation (fun i => bits.getD i false) 0

def FixedWidths (S : Homomorphic.Scheme)
    (allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop)
    (keyBits cipherBits : ℕ → ℕ) : Prop :=
  ∀ security keys, keys ∈ (ProbComp.eval (S.keyGen security)).support →
    keys.2.length = keyBits security ∧
    (∀ bit ciphertext,
      ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support →
        ciphertext.length = cipherBits security) ∧
    ∀ C bits inputs, allowed security C → bits.length = C.1 →
      List.Forall₂ (fun bit ciphertext =>
        ciphertext ∈ (ProbComp.eval (S.encrypt security keys.1 bit)).support) bits inputs →
      ∀ ciphertext ∈ (ProbComp.eval (S.evaluate security keys.1 C inputs)).support,
        ciphertext.length = cipherBits security

def DecryptsWith (S : Homomorphic.Scheme) (keyBits cipherBits : ℕ → ℕ)
    (circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
      (keyBits security + cipherBits security) 1) : Prop :=
  ∀ security (secret ciphertext : List Bool), secret.length = keyBits security →
    ciphertext.length = cipherBits security →
    (circuit security).eval Circuits.Boolean.interpretation
      (fun i => (secret ++ ciphertext).getD i false) 0 = S.decrypt security secret ciphertext

def Native (S : Homomorphic.Scheme) : Prop :=
  Randomized.StrictPPT Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits)
      (fun security => ProbComp.eval (S.keyGen security)) ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBool))
      Encoding.encBits (fun p => ProbComp.eval (S.encrypt p.1 p.2.1 p.2.2)) ∧
    Computation.PolyTime (fun p : ℕ × List Bool × List Bool => S.decrypt p.1 p.2.1 p.2.2)
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool ∧
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits
        (Encoding.encPair (Circuits.Boolean.encCircuit 1)
          (Encoding.encList Encoding.encBits))))
      Encoding.encBits (fun p => ProbComp.eval (S.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2))

noncomputable def chosenMessageGame (S : Homomorphic.Scheme)
    (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool) (bit : Bool) (security : ℕ) :
    PMF Bool := do
  let keys ← ProbComp.eval (S.keyGen security)
  let choice ← choose security keys.1
  let ciphertext ← ProbComp.eval
    (S.encrypt security keys.1 (if bit then choice.1.2 else choice.1.1))
  guess security choice.2 ciphertext

def ChosenMessageSecure (S : Homomorphic.Scheme) : Prop :=
  ∀ (choose : ℕ → List Bool → PMF ((Bool × Bool) × List Bool))
    (guess : ℕ → List Bool → List Bool → PMF Bool),
    Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits)
      (Encoding.encPair (Encoding.encPair Encoding.encBool Encoding.encBool) Encoding.encBits)
      (fun p => choose p.1 p.2) →
    Randomized.StrictPPT
      (Encoding.encPair Encoding.encUnary (Encoding.encPair Encoding.encBits Encoding.encBits))
      Encoding.encBool (fun p => guess p.1 p.2.1 p.2.2) →
    Randomized.Negligible (fun security =>
      nndist (Randomized.probability (chosenMessageGame S choose guess false security))
        (Randomized.probability (chosenMessageGame S choose guess true security)))

/-! ### The GSW laws are the library's serialized programs -/

private theorem independentList_eval {α : Type} (count : ℕ) (program : ProbComp α) :
    independentList count (ProbComp.eval program) =
      ProbComp.eval (OracleComp.replicate count program) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [independentList] at ih
    simp only [independentList, List.replicate_succ, List.mapM_cons,
      OracleComp.replicate_succ, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map,
      Function.comp_def, ih]

private theorem keyGeneration_eq (security : ℕ) :
    keyGeneration security = ProbComp.eval
      (GSW.keyGenSerialized (dimension security) (samples security) (width security)
        (dimension security)) := by
  simp only [keyGeneration, GSW.keyGenSerialized, GSW.sampleKeyInputsSerialized,
    ProbComp.eval_bind, ProbComp.eval_pure, ← independentList_eval, eval_sampleBinaryNat,
    eval_sampleCenteredBinomial, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, errorLaw, Randomized.uniformBits]
  rfl

private theorem encryption_eq (security : ℕ) (publicKey : List Bool) (message : Bool) :
    encryption security publicKey message = ProbComp.eval
      (GSW.encryptSerialized (dimension security) (samples security) (width security)
        publicKey message) := by
  simp only [encryption, GSW.encryptSerialized, GSW.sampleCoinsSerialized, ProbComp.eval_bind,
    ProbComp.eval_pure, ← independentList_eval, ProbComp.eval_uniform, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rfl

/-- The named GSW key generation and encryption have exactly the explicit laws. -/
theorem base_scheme (security : ℕ) :
    ProbComp.eval (GSW.DepthParameters.scheme.keyGen security) = keyGeneration security ∧
      ∀ publicKey message,
        ProbComp.eval (GSW.DepthParameters.scheme.encrypt security publicKey message) =
          encryption security publicKey message :=
  ⟨(keyGeneration_eq security).symm, fun publicKey message =>
    (encryption_eq security publicKey message).symm⟩

/-! ### The two assumptions -/

private theorem uniformMatrixWord_eq (m k w : ℕ) :
    uniformMatrixWord m (k + 1) w =
      LWE.uniformEnsemble (fun _ => k) (fun _ => m) (fun _ => w) 0 := by
  unfold uniformMatrixWord LWE.uniformEnsemble
  congr 1
  funext A
  simpa only [← BitString.lowBits_eq_ofFn, BitString.lowBits, lowBits] using
    (Matrix.toBinary_eq A).symm

private theorem uniformPublic_eq (security : ℕ) :
    uniformPublic security = LWE.uniformEnsemble dimension samples width security :=
  uniformMatrixWord_eq _ _ _

theorem decisionLWE_iff : DecisionLWE ↔
    Crypto.DecisionLWE GSW.Parameters.dimension GSW.DepthParameters.samples
      GSW.DepthParameters.width
      (fun security => GSW.noiseLaw (GSW.DepthParameters.width security)
        (GSW.Parameters.noise security)) := by
  change Randomized.Indistinguishable _ _ ↔ _
  rw [CryptographyBridge.indistinguishable_iff]
  change ComputationallyIndistinguishable _ _ ↔ ComputationallyIndistinguishable _ _
  have hreal : (fun security => (keyGeneration security).map Prod.fst) =
      LWE.realEnsemble dimension samples width
        (fun security => GSW.noiseLaw (width security) (dimension security)) := by
    funext security
    rw [keyGeneration_eq, GSW.eval_keyGenSerialized_publicWord]
  rw [hreal, show uniformPublic = LWE.uniformEnsemble dimension samples width
    from funext uniformPublic_eq]
  rfl

private theorem mapM_eval {α β : Type} (program : α → ProbComp β) (inputs : List α) :
    inputs.mapM (fun a => ProbComp.eval (program a)) = ProbComp.eval (inputs.mapM program) := by
  induction inputs with
  | nil => simp only [List.mapM_nil, ProbComp.eval_pure, PMF.monad_pure_eq_pure]
  | cons a inputs ih =>
    simp only [List.mapM_cons, ProbComp.eval_bind, ProbComp.eval_pure, ih,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]

private theorem selfEncryption_eq (real : Bool) (security : ℕ) :
    selfEncryption real security =
      (ProbComp.eval (Encryption.circularPublicKey GSW.DepthParameters.scheme.keyGen
        GSW.DepthParameters.scheme.encrypt real security)).map
        Encryption.encCircularPublicKey := by
  have hencrypt : encryption security = fun publicKey message =>
      ProbComp.eval (GSW.DepthParameters.scheme.encrypt security publicKey message) := by
    funext publicKey message
    exact encryption_eq security publicKey message
  simp only [selfEncryption, Encryption.circularPublicKey, hencrypt, mapM_eval,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, (base_scheme security).1]
  rfl

theorem circularSecure_iff : CircularSecure ↔
    Encryption.CircularSecure GSW.DepthParameters.scheme.keyGen
      GSW.DepthParameters.scheme.encrypt := by
  change Randomized.Indistinguishable _ _ ↔ _
  rw [CryptographyBridge.indistinguishable_iff]
  have h (real : Bool) : selfEncryption real = fun security =>
      (ProbComp.eval (Encryption.circularPublicKey GSW.DepthParameters.scheme.keyGen
        GSW.DepthParameters.scheme.encrypt real security)).map
        Encryption.encCircularPublicKey :=
    funext (selfEncryption_eq real)
  rw [h true, h false]
  rfl

/-! ### The claimed properties from the library's notions -/

theorem homomorphic_of_correct {S : Homomorphic.Scheme} (hS : S.Correct)
    {allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop}
    (hallowed : ∀ security C, allowed security C → S.permitted security C) :
    Homomorphic S allowed := fun security keys hkeys =>
  ⟨hS.decrypt_encrypt security keys hkeys, fun C bits inputs hC hbits hinputs =>
    hS.decrypt_evaluate security keys hkeys C (hallowed security C hC) bits inputs hbits
      hinputs⟩

theorem fixedWidths_of_fixedWidth {S : Homomorphic.Scheme} {keyBits cipherBits : ℕ → ℕ}
    (hS : S.FixedWidth keyBits cipherBits)
    {allowed : ℕ → (Σ k, Circuits.Circuit Circuits.Boolean.signature k 1) → Prop}
    (hallowed : ∀ security C, allowed security C → S.permitted security C) :
    FixedWidths S allowed keyBits cipherBits := fun security keys hkeys =>
  ⟨hS.secret_length security keys hkeys, hS.encrypt_length security keys hkeys,
    fun C bits inputs hC hbits hinputs =>
      hS.evaluate_length security keys hkeys C (hallowed security C hC) bits inputs hbits
        hinputs⟩

theorem native_of {S : Homomorphic.Scheme}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) S.keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
      (fun p => S.encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => S.decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBool)
    (hevaluate : IsPPTOn
      (encPair encUnary (encPair encBits (encPair (Circuits.Boolean.encCircuit 1)
        (encList encBits))))
      encBits (fun p => S.evaluate p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Native S :=
  ⟨CryptographyBridge.strictPPT_iff.mpr ⟨S.keyGen, hkeyGen, fun _ => rfl⟩,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hencrypt, fun _ => rfl⟩, hdecrypt,
    CryptographyBridge.strictPPT_iff.mpr ⟨_, hevaluate, fun _ => rfl⟩⟩

theorem chosenMessageSecure_of_indCPA {S : Homomorphic.Scheme}
    (hS : Encryption.INDCPA S.keyGen S.encrypt) : ChosenMessageSecure S := by
  intro choose guess hchoose hguess
  obtain ⟨chooseProgram, hchooseProgram, hchooseLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hchoose
  obtain ⟨guessProgram, hguessProgram, hguessLaw⟩ :=
    CryptographyBridge.strictPPT_iff.mp hguess
  let adversary : Encryption.Adversary :=
    ⟨fun security pk => chooseProgram (security, pk),
      fun security state ciphertext => guessProgram (security, state, ciphertext)⟩
  have h := hS adversary ⟨hchooseProgram, hguessProgram⟩
  simpa only [Encryption.game, adversary, ProbComp.eval_bind, hchooseLaw, hguessLaw,
    chosenMessageGame, PMF.monad_bind_eq_bind, Randomized.Negligible, Crypto.Negligible,
    Asymptotics.SuperpolynomialDecay, Crypto.Game.advantage, Crypto.Game.succProbability,
    Randomized.probability] using h

/-! ### The headline theorems -/

theorem leveled (hLWE : DecisionLWE) :
    ∃ circuit : ∀ security, Circuits.Circuit Circuits.Boolean.signature
        ((3 * secretWidth security + 1) + (ciphertextWidth security + 1)) 1,
      PolynomiallyBounded (fun security => (circuit security).size) ∧
      PolynomiallyBounded (fun security => 3 * secretWidth security + 1) ∧
      PolynomiallyBounded (fun security => ciphertextWidth security + 1) ∧
      ∀ budget : ℕ → ℕ, Computation.PolyTime budget Encoding.encUnary Encoding.encUnary →
        DecryptsWith (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) circuit ∧
        Homomorphic (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security C => C.2.depth ≤ budget security) ∧
        FixedWidths (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget)
          (fun security C => C.2.depth ≤ budget security)
          (fun security => 3 * secretWidth security + 1)
          (fun security => ciphertextWidth security + 1) ∧
        Native (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget) ∧
        ChosenMessageSecure (Leveled.scheme GSW.DepthParameters.decryptionCircuits budget) := by
  let D := GSW.DepthParameters.decryptionCircuits
  have hD := GSW.DepthParameters.computableInPolyTime_decryptionCircuits.tidy
  have hkeyGen := GSW.DepthParameters.isPPTOn_keyGen
  have hencrypt := GSW.DepthParameters.isPPTOn_encrypt
  have hevaluate := GSW.DepthParameters.isPPTOn_evaluate
  obtain ⟨circuits, hsize, hcircuits⟩ := Leveled.exists_decrypt_circuits D hD
  obtain ⟨hsecret, hciphertext⟩ := Leveled.polynomiallyBounded_widths D hD
  refine ⟨circuits, hsize, hsecret, hciphertext, fun budget hbudget => ?_⟩
  have hb : ComputableTidilyInPolyTime budget encUnary encUnary :=
    CryptographyBridge.polyTime_iff.mp hbudget
  obtain ⟨hcorrect, hwidth, -, -, hsecure⟩ :=
    Leveled.correct_fixedWidth_indCPA D GSW.DepthParameters.correct
      GSW.DepthParameters.fixedWidth GSW.DepthParameters.bootstrappable
      (GSW.DepthParameters.indCPA_scheme (decisionLWE_iff.mp hLWE)) hkeyGen hencrypt hD hb
  exact ⟨fun security => hcircuits budget security,
    homomorphic_of_correct hcorrect fun _ _ h => h,
    fixedWidths_of_fixedWidth hwidth fun _ _ h => h,
    native_of (Leveled.isPPTOn_scheme_keyGen hkeyGen hencrypt D budget hb)
      (Leveled.isPPTOn_scheme_encrypt hencrypt D budget)
      (Leveled.computableTidilyInPolyTime_scheme_decrypt D hD budget).computableInPolyTime
      (Leveled.isPPTOn_scheme_evaluate hencrypt D hD hevaluate budget hb),
    chosenMessageSecure_of_indCPA hsecure⟩

theorem fullyHomomorphic (hLWE : DecisionLWE) (hcircular : CircularSecure) :
    DecryptsWith (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) secretWidth
        ciphertextWidth GSW.DepthParameters.decryptionCircuits.circuit ∧
      PolynomiallyBounded
        (fun security => (GSW.DepthParameters.decryptionCircuits.circuit security).size) ∧
      PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth ∧
      Homomorphic (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) (fun _ _ => True) ∧
      FixedWidths (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) (fun _ _ => True)
        secretWidth ciphertextWidth ∧
      Native (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) ∧
      ChosenMessageSecure (FixedKey.scheme GSW.DepthParameters.decryptionCircuits) := by
  obtain ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
      hdecrypt, hevaluate, hsecure⟩ :=
    GSW.DepthParameters.fullyHomomorphic_of_decisionLWE_of_circularSecure
      (decisionLWE_iff.mp hLWE) (circularSecure_iff.mp hcircular)
  exact ⟨(FixedKey.decryptionCircuits GSW.DepthParameters.decryptionCircuits).correct, hsize,
    hsecret, hciphertext,
    homomorphic_of_correct hcorrect fun security C _ => hpermitted security C,
    fixedWidths_of_fixedWidth hwidth fun security C _ => hpermitted security C,
    native_of hkeyGen hencrypt hdecrypt hevaluate, chosenMessageSecure_of_indCPA hsecure⟩

end ComplexityTests.Abstracts.GSWFHEBridge
