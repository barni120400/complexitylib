/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.Encryption.Hybrid
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF.Bind
import Complexity.Tactic.PPT

/-!
# Tests for KEM–DEM hybrid public-key encryption

Exercises the KEM, DEM, and KEM–DEM hybrid encryption API in
`Complexity.Crypto.Computational.Encryption.Hybrid`:
* native runtime certificates for `kemRealGame`, `kemIdealGame`, `demGame`, `hybridEncrypt`,
  `hybridDecrypt`, `otpEncrypt`, and `otpDecrypt`;
* non-vacuous rejection of an insecure KEM (`not_kemINDCPA_leaking`) by an explicit uniform
  distinguisher;
* exact decryption correctness of `hybridEncrypt` / `hybridDecrypt` instantiated with a concrete
  KEM and the one-time pad DEM (`otpEncrypt` / `otpDecrypt`);
* quantitative advantage bounds (`advantage_hybridGame_le`, `advantage_hybridGame_le_two_mul`) and
  the KEM-to-PKE specialization (`KEMINDCPA.hybrid_otpEncrypt_indcpa`).
-/

@[expose] public section

namespace ComplexityTests.Crypto.HybridEncryption

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- A simple key generator sampling a uniform `n`-bit key as both public and secret key. -/
noncomputable def toyKeyGen (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList n
  return (k, k)

/-- Deliberately insecure encapsulation that copies the public key as both encapsulated key and
ciphertext, and prefixes `true` so the encapsulated key is non-empty even at `n = 0`. -/
def leakingEncaps (_ : ℕ) (pk : List Bool) : ProbComp (List Bool × List Bool) :=
  pure (true :: pk, true :: pk)

/-- Deterministic decapsulation returning the encapsulation ciphertext directly. -/
def leakingDecaps (_ : ℕ) (_ ctKem : List Bool) : List Bool := ctKem

theorem toyKeyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) toyKeyGen := by
  unfold toyKeyGen
  ppt

theorem leakingEncaps_ppt :
    IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => leakingEncaps p.1 p.2) := by
  unfold leakingEncaps
  ppt

theorem leakingDecaps_polyTime :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => leakingDecaps p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold leakingDecaps
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- A uniform KEM distinguisher testing whether the encapsulated key equals the encapsulation
ciphertext `ctKem`. -/
def eqKemDistinguisher : Distinguisher := fun _ challenge =>
  let rest := dropFrame challenge
  let k := unframe rest
  let ctKem := dropFrame rest
  pure (decide (k = ctKem))

theorem eqKemDistinguisher_ppt : IsPPT encBool eqKemDistinguisher := by
  have hk : ComputableTidilyInPolyTime
      (fun challenge : List Bool => unframe (dropFrame challenge)) encBits encBits :=
    ComputableTidilyInPolyTime.unframe.comp ComputableTidilyInPolyTime.dropFrame
  have hct : ComputableTidilyInPolyTime
      (fun challenge : List Bool => dropFrame (dropFrame challenge)) encBits encBits :=
    ComputableTidilyInPolyTime.dropFrame.comp ComputableTidilyInPolyTime.dropFrame
  unfold eqKemDistinguisher
  exact ComputableTidilyInPolyTime.isPPT (hk.decide_eq' hct)

-- Native runtime checks for `kemRealGame`, `kemIdealGame`, `demGame`, `hybridEncrypt`,
-- and `hybridDecrypt`.
example : IsPPTOn encUnary encBool
    (kemRealGame toyKeyGen leakingEncaps eqKemDistinguisher) :=
  isPPTOn_kemRealGame toyKeyGen_ppt leakingEncaps_ppt eqKemDistinguisher_ppt
    (ComputableInPolyTime.of_tidy (by fun_prop))

example : IsPPTOn encUnary encBool
    (kemIdealGame toyKeyGen leakingEncaps eqKemDistinguisher) :=
  isPPTOn_kemIdealGame toyKeyGen_ppt leakingEncaps_ppt eqKemDistinguisher_ppt
    (ComputableInPolyTime.of_tidy (by fun_prop))

example : IsPPTOn (encPair encUnary (encPair encBits encBool)) encBits
    (fun p => hybridEncrypt leakingEncaps otpEncrypt p.1 p.2.1 p.2.2) :=
  isPPTOn_hybridEncrypt leakingEncaps_ppt isPPTOn_otpEncrypt

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool =>
      hybridDecrypt leakingDecaps otpDecrypt p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair encBits encBits)) encBool :=
  computableInPolyTime_hybridDecrypt leakingDecaps_polyTime computableInPolyTime_otpDecrypt

/-- Every ciphertext produced by `hybridEncrypt leakingEncaps otpEncrypt` decrypts to the original
plaintext bit under `hybridDecrypt leakingDecaps otpDecrypt`. -/
example (n : ℕ) (pk sk ct : List Bool) (bit : Bool)
    (hct : ct ∈ (ProbComp.eval (hybridEncrypt leakingEncaps otpEncrypt n pk bit)).support) :
    hybridDecrypt leakingDecaps otpDecrypt n sk ct = bit := by
  refine hybridDecrypt_hybridEncrypt ?_ ?_ hct
  · intro k ctKem hsupp
    simp only [leakingEncaps, ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hsupp
    rcases hsupp with ⟨rfl, rfl⟩
    rfl
  · intro k ctDem _ hdemSupp
    simp only [otpEncrypt, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hdemSupp
    subst hdemSupp
    exact otpDecrypt_otpEncrypt n k bit

/-- Concrete round-trip evaluation of `hybridDecrypt` on an encoded `(ctKem, ctDem)` pair. -/
example (bit : Bool) :
    hybridDecrypt leakingDecaps otpDecrypt 4 []
      (encPair encBits encBits ([true, false], [true ^^ bit])) = bit := by
  rw [hybridDecrypt_encPair]
  simp [leakingDecaps, otpDecrypt]

/-- In `kemRealGame`, `eqKemDistinguisher` always outputs `true` on `leakingEncaps`. -/
theorem eval_kemRealGame_leaking (n : ℕ) :
    ProbComp.eval (kemRealGame toyKeyGen leakingEncaps eqKemDistinguisher n) =
      PMF.pure true := by
  simp only [kemRealGame, toyKeyGen, leakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind,
    decide_true, PMF.bind_const]

/-- In `kemIdealGame`, `eqKemDistinguisher` always outputs `false` on `leakingEncaps` because the
ideal key `kIdeal` has length `n` while `ctKem = true :: pk` has length `n + 1`. -/
theorem eval_kemIdealGame_leaking (n : ℕ) :
    ProbComp.eval (kemIdealGame toyKeyGen leakingEncaps eqKemDistinguisher n) =
      PMF.pure false := by
  simp only [kemIdealGame, toyKeyGen, leakingEncaps, eqKemDistinguisher, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, ProbComp.eval_bind,
    ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
  trans (BitString.uniformList n).bind (fun _ => PMF.pure false)
  · refine PMF.bind_congr_on_support _ _ _ fun pk hpk => ?_
    trans (BitString.uniformList n).bind (fun _ => PMF.pure false)
    · refine PMF.bind_congr_on_support _ _ _ fun kIdeal hkIdeal => ?_
      have hlenPk := BitString.length_of_mem_support_uniformList hpk
      have hlenIdeal := BitString.length_of_mem_support_uniformList hkIdeal
      have hne : kIdeal ≠ true :: pk := by
        intro heq
        have := congrArg List.length heq
        simp [hlenPk, hlenIdeal] at this
      simp [hne]
    · exact PMF.bind_const _ _
  · exact PMF.bind_const _ _

/-- The leaking KEM is not IND-CPA secure: `eqKemDistinguisher` achieves advantage `1` at every
security parameter. -/
theorem not_kemINDCPA_leaking : ¬ KEMINDCPA toyKeyGen leakingEncaps := by
  intro hsecure
  have hneg := hsecure eqKemDistinguisher eqKemDistinguisher_ppt
  simp only [eval_kemRealGame_leaking, eval_kemIdealGame_leaking] at hneg
  have hone : Game.advantage (PMF.pure true) (PMF.pure false) = 1 := by
    simp [Game.advantage, Game.succProbability]
  rw [hone] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- Specialization of the KEM-to-PKE corollary `KEMINDCPA.hybrid_otpEncrypt_indcpa`. -/
example {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encaps : ℕ → List Bool → ProbComp (List Bool × List Bool)}
    (hkem : KEMINDCPA keyGen encaps)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencaps : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p => encaps p.1 p.2)) :
    INDCPA keyGen (hybridEncrypt encaps otpEncrypt) :=
  hkem.hybrid_otpEncrypt_indcpa hkeyGen hencaps

end ComplexityTests.Crypto.HybridEncryption
