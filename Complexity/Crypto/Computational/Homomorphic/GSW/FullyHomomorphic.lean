/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.GSW.DepthParameters.Scheme
public import Complexity.Crypto.Computational.Homomorphic.Leveled.Bootstrapping
public import Complexity.Crypto.Computational.Homomorphic.FixedKey.Bootstrapping
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Fully homomorphic encryption from GSW and decision LWE

Gentry's generic bootstrapping constructions are instantiated with GSW at the logarithmic-depth
parameter family. The base scheme is `DepthParameters.scheme`, its decryption circuits are the
actual raw-input decryptors, and its bootstrappability, correctness, widths and native runtime
are proved without computational assumptions.

* **Leveled FHE.** For every polynomially bounded depth family, the acyclic key-chain
  construction evaluates all circuits of that depth, with polynomial widths independent of the
  depth, native algorithms, and IND-CPA security assuming only decision LWE for this exact
  family [Gentry2009, Theorems 3 and 4].
* **Fully homomorphic encryption.** The one-key self-loop construction evaluates every circuit,
  assuming decision LWE for this family *and* the separate one-key circular-security assumption
  `Encryption.CircularSecure` for the base scheme [Gentry2009, Section 2, the self-loop
  construction]. This is a one-key specialization of the KDM security Gentry assumes there.
  Circular security is not derived from LWE.

Neither theorem asserts lattice hardness, a worst-case reduction, circuit privacy, or an exact
concrete-security loss.

## Main results

* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.exists_leveled_of_decisionLWE`: leveled FHE.
* `Cslib.Crypto.Homomorphic.GSW.DepthParameters.fullyHomomorphic_of_decisionLWE`: FHE under the
  additional circular-security assumption.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorems 3 and 4
  and the self-loop construction][Gentry2009]
* [C. Gentry, A. Sahai and B. Waters, Sections 3.2–3.4][GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW.DepthParameters

open Circuits Probability Turing.MultiTapeTM
open Parameters (dimension noise)

/-- Leveled FHE from GSW: under decision LWE for this family, every polynomially bounded depth
family is covered by one actual scheme with an efficiently computable budget. Its secret and
ciphertext widths are polynomial and do not depend on the requested depth, its four algorithms
are native, and it is IND-CPA. No circular-security assumption is used. -/
theorem exists_leveled_of_decisionLWE
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k)))
    {depth : ℕ → ℕ} (hdepth : PolynomiallyBounded depth) :
    ∃ budget : ℕ → ℕ,
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ k, depth k ≤ budget k) ∧
      (Leveled.scheme decryptionCircuits budget).Correct ∧
      (∀ k c, c.2.depth ≤ depth k → (Leveled.scheme decryptionCircuits budget).permitted k c) ∧
      (Leveled.scheme decryptionCircuits budget).FixedWidth (fun k => 3 * secretWidth k + 1)
        (fun k => ciphertextWidth k + 1) ∧
      PolynomiallyBounded (fun k => 3 * secretWidth k + 1) ∧
      PolynomiallyBounded (fun k => ciphertextWidth k + 1) ∧
      IsPPTOn encUnary (encPair encBits encBits) (Leveled.scheme decryptionCircuits budget).keyGen ∧
      IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
        (fun p => (Leveled.scheme decryptionCircuits budget).encrypt p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (Leveled.scheme decryptionCircuits budget).decrypt p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encBits
          (encPair (Boolean.encCircuit 1) (encList encBits))))
        encBits
        (fun p => (Leveled.scheme decryptionCircuits budget).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Encryption.INDCPA (Leveled.scheme decryptionCircuits budget).keyGen
        (Leveled.scheme decryptionCircuits budget).encrypt := by
  obtain ⟨budget, hbudget, hle, hcorrect, hpermitted, hwidth, hsecret, hciphertext, hkeyGen,
      hencrypt, hdecrypt, hevaluate, hsecure⟩ :=
    Leveled.exists_scheme_of_polynomiallyBounded decryptionCircuits correct fixedWidth
      bootstrappable (indCPA_scheme hLWE) isPPTOn_keyGen isPPTOn_encrypt isPPTOn_evaluate
      computableInPolyTime_decryptionCircuits.tidy hdepth
  exact ⟨budget, hbudget.computableInPolyTime, hle, hcorrect, hpermitted, hwidth, hsecret,
    hciphertext, hkeyGen, hencrypt, hdecrypt.computableInPolyTime, hevaluate, hsecure⟩

/-- Fully homomorphic encryption from GSW: under decision LWE for this family and the explicit
one-key circular-security assumption for the base scheme, the self-loop construction correctly
evaluates every finite circuit. Its widths are those of GSW, its decryption circuits have
polynomial size, its four algorithms are native, and it is IND-CPA. -/
theorem fullyHomomorphic_of_decisionLWE
    (hLWE : DecisionLWE dimension samples width (fun k => noiseLaw (width k) (noise k)))
    (hcircular : Encryption.CircularSecure scheme.keyGen scheme.encrypt) :
    (FixedKey.scheme decryptionCircuits).Correct ∧
      (∀ k c, (FixedKey.scheme decryptionCircuits).permitted k c) ∧
      (FixedKey.scheme decryptionCircuits).FixedWidth secretWidth ciphertextWidth ∧
      PolynomiallyBounded secretWidth ∧ PolynomiallyBounded ciphertextWidth ∧
      PolynomiallyBounded
        (fun k => ((FixedKey.decryptionCircuits decryptionCircuits).circuit k).size) ∧
      IsPPTOn encUnary (encPair encBits encBits) (FixedKey.scheme decryptionCircuits).keyGen ∧
      IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
        (fun p => (FixedKey.scheme decryptionCircuits).encrypt p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (FixedKey.scheme decryptionCircuits).decrypt p.1 p.2.1 p.2.2)
        (encPair encUnary (encPair encBits encBits)) encBool ∧
      IsPPTOn
        (encPair encUnary (encPair encBits
          (encPair (Boolean.encCircuit 1) (encList encBits))))
        encBits
        (fun p => (FixedKey.scheme decryptionCircuits).evaluate p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Encryption.INDCPA (FixedKey.scheme decryptionCircuits).keyGen
        (FixedKey.scheme decryptionCircuits).encrypt := by
  obtain ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
      hdecrypt, hevaluate, hsecure⟩ :=
    FixedKey.fullyHomomorphic decryptionCircuits correct fixedWidth bootstrappable
      (indCPA_scheme hLWE) hcircular isPPTOn_keyGen isPPTOn_encrypt isPPTOn_evaluate
      computableInPolyTime_decryptionCircuits.tidy
  exact ⟨hcorrect, hpermitted, hwidth, hsecret, hciphertext, hsize, hkeyGen, hencrypt,
    hdecrypt.computableInPolyTime, hevaluate, hsecure⟩

end Cslib.Crypto.Homomorphic.GSW.DepthParameters
