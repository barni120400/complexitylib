/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Basic
public import Complexity.Crypto.Computational.Homomorphic.Evaluation
import Mathlib.Data.List.GetD

/-!
# Correctness of depth-budgeted homomorphic encryption

The actual acyclic sampler and padded evaluator satisfy the existing encryption interface for
every Boolean circuit within the chosen depth budget. Fresh ciphertexts decrypt at the initial
endpoint; evaluated ciphertexts decrypt at the final endpoint, independent of actual depth.

The private key has length `3 * secretWidth n + 1` and ciphertexts have length
`ciphertextWidth n + 1`. These exact lengths are independent of the depth budget. Uniform
polynomial bounds and security remain separate obligations. Correctness takes fresh input
ciphertexts, as in `Scheme.Correct`; it does not identify evaluated ciphertexts with fresh ones.

## Main results

* `Cslib.Crypto.Homomorphic.Leveled.encryptedWires_evaluateCircuit`: a common final key for
  every permitted circuit, including depth-zero wiring and input-free constants.
* `Cslib.Crypto.Homomorphic.Leveled.encryptedWires_evaluateCircuit_drop`: evaluating a padded
  circuit at an arbitrary offset along a generated key chain.
* `Cslib.Crypto.Homomorphic.Leveled.evaluateHop_spec`: correctness of a single depth-bounded
  evaluation hop from level `offset` to `offset + step`.
* `Cslib.Crypto.Homomorphic.Leveled.evaluate_twoHop_spec`: two-hop leveled evaluation across
  `step₁ + step₂ = budget n` decrypts under the endpoint secret key to the composed circuit value.
* `Cslib.Crypto.Homomorphic.Leveled.correct`: perfect correctness of the constructed scheme.
* `Cslib.Crypto.Homomorphic.Leveled.fixedWidth`: budget-independent secret and ciphertext widths.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open Circuits Circuits.Boolean

variable {E : Scheme} {secretWidth ciphertextWidth : ℕ → ℕ}
  (D : DecryptionCircuits E secretWidth ciphertextWidth)

/-- The serialized keys come from an actual supported acyclic chain. -/
theorem mem_support_keyGen_iff (n budget : ℕ) (output : List Bool × List Bool) :
    output ∈ (ProbComp.eval (keyGen E n budget)).support ↔
      ∃ keys links, (keys, links) ∈
        (ProbComp.eval (E.generateKeyChain n (2 * budget))).support ∧
        keyPair (2 * budget) keys links = output := by
  simp only [keyGen, ProbComp.eval_map, PMF.mem_support_map_iff, Prod.exists]

/-- A false tag selects the initial endpoint on valid payloads. -/
theorem decrypt_false (n : ℕ) (first last payload : List Bool)
    (hfirst : first.length = secretWidth n) (hpayload : payload.length = ciphertextWidth n) :
    decrypt D n (encSecretKey (first, last)) (false :: payload) =
      E.decrypt n first payload := by
  simpa only [decrypt, secretKeyDecoder_decode_enc, List.headD_cons, Bool.false_eq_true,
    ↓reduceIte, List.tail_cons] using D.correct n first payload hfirst hpayload

/-- A true tag selects the final endpoint on valid payloads. -/
theorem decrypt_true (n : ℕ) (first last payload : List Bool)
    (hlast : last.length = secretWidth n) (hpayload : payload.length = ciphertextWidth n) :
    decrypt D n (encSecretKey (first, last)) (true :: payload) =
      E.decrypt n last payload := by
  simpa only [decrypt, secretKeyDecoder_decode_enc, List.headD_cons, ↓reduceIte,
    List.tail_cons] using D.correct n last payload hlast hpayload

/-- Padding reaches the budget's final key and preserves the original ordered output vector. -/
theorem encryptedWires_evaluateCircuit (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (n budget : ℕ) (keys : List (List Bool × List Bool)) (links : List (List (List Bool)))
    {inputCount outputCount : ℕ} (c : Circuit signature inputCount outputCount)
    (hbudget : c.depth ≤ budget)
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * budget))).support)
    (x : Fin inputCount → Bool) (inputs : List (List Bool))
    (hinputs : E.FreshInputs n (keys.getD 0 ([], [])).1 (List.ofFn x) inputs)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateCircuit D n budget (keys.tail.map Prod.fst) links inputs
        inputCount c.code)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (2 * budget) ([], [])).2
      (List.ofFn (c.eval interpretation x)) outputs := by
  have hlength :
      (Layered.padTo inputCount (2 * budget) (Layered.compile inputCount c.code).1).length =
        2 * budget :=
    Layered.length_padTo_of_le _ _ _ (by rw [Layered.length_compile]; omega)
  rw [evaluateCircuit, ProbComp.eval_map, PMF.mem_support_map_iff] at houtputs
  obtain ⟨row, hrow, rfl⟩ := houtputs
  have h := Scheme.encryptedWires_evaluateLayers_of_generatedChain D hE hwidth hD n keys
    links (Layered.padTo inputCount (2 * budget) (Layered.compile inputCount c.code).1)
    (by simpa only [hlength] using hchain) (List.ofFn x) inputs hinputs
    (by simpa only [List.length_ofFn] using (Layered.wellFormed_compile c).padTo (2 * budget))
    row hrow
  have heval : Layered.eval (List.ofFn x)
      (Layered.padTo inputCount (2 * budget) (Layered.compile inputCount c.code).1) =
        Layered.eval (List.ofFn x) (Layered.compile inputCount c.code).1 := by
    simpa only [List.length_ofFn] using
      Layered.eval_padTo (List.ofFn x) (2 * budget) (Layered.compile inputCount c.code).1
  rw [heval, hlength] at h
  have hselected := h.select (outputs := (Layered.compile inputCount c.code).2) (by
    simpa only [Layered.length_eval, List.length_ofFn] using Layered.outputs_valid_compile c)
  simpa only [Layered.select_eval_compile] using hselected

/-- Evaluate a layer schedule starting at index `start` in a generated key chain of total depth
`total`, advancing the wire invariant from key `start` to key `start + layers.length`. -/
theorem encryptedWires_evaluateLayers_drop (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (n total start : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) (layers : List (List Layered.Node))
    (htotal : start + layers.length ≤ total)
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n total)).support)
    (bits : List Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n (keys.getD start ([], [])).2 bits inputs)
    (hvalid : Layered.WellFormed bits.length layers) (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (Scheme.evaluateLayers D n ((keys.map Prod.fst).tail.drop start)
        (links.drop start) inputs layers)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (start + layers.length) ([], [])).2
      (Layered.eval bits layers) outputs := by
  obtain ⟨hcount, hkeys, hlinks⟩ :=
    (E.mem_support_generateKeyChain_iff n total keys links).1 hchain
  have hkey (i : ℕ) (hi : i ≤ total) :
      keys.getD i ([], []) ∈ (ProbComp.eval (E.keyGen n)).support :=
    E.key_mem_support_of_generatedChain hchain hi
  have hlinkCount : links.length = total := by
    simpa only [hcount, Nat.add_sub_cancel] using hlinks.length_eq
  have hpk (i : ℕ) :
      ((keys.map Prod.fst).tail.drop start).getD i [] =
        (keys.getD (start + i + 1) ([], [])).1 := by
    rw [← List.map_tail, List.getD_eq_getElem?_getD, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
    change (keys.tail.map Prod.fst).getD (start + i)
      (Prod.fst (([], []) : List Bool × List Bool)) = _
    rw [List.getD_map]
    cases keys <;> rfl
  have hlink (i : ℕ) :
      (links.drop start).getD i [] = links.getD (start + i) [] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [Scheme.evaluateLayers, ProbComp.eval_map, PMF.mem_support_map_iff] at houtputs
  obtain ⟨state, hstate, rfl⟩ := houtputs
  have hrun := ProbComp.iterate_invariant layers.length
    (Scheme.evaluateLayerStep D n ((keys.map Prod.fst).tail.drop start)
      (links.drop start) layers) (0, inputs)
    (fun i state => state.1 = i ∧
      E.EncryptedWires ciphertextWidth n (keys.getD (start + i) ([], [])).2
        (Layered.eval bits (layers.take i)) state.2)
    ⟨rfl, by rw [Nat.add_zero]; exact hinputs⟩
    (by
      intro i hi state hinvariant next hnext
      rw [Scheme.evaluateLayerStep, ProbComp.eval_map, PMF.mem_support_map_iff] at hnext
      obtain ⟨newWires, hnewWires, rfl⟩ := hnext
      rw [hinvariant.1, hpk, hlink] at hnewWires
      refine ⟨congrArg (· + 1) hinvariant.1, ?_⟩
      rw [Layered.eval_take_succ bits layers hi, ← Nat.add_assoc]
      exact Scheme.encryptedWires_evaluateLayer D hE hwidth hD n
        (keys.getD (start + i + 1) ([], [])) (hkey _ (by omega))
        (keys.getD (start + i) ([], [])).2 (hwidth.secret_length n _ (hkey _ (by omega)))
        (links.getD (start + i) []) (hlinks.getD (by omega))
        (Layered.eval bits (layers.take i)) state.2 hinvariant.2
        (layers.getD i []) (hvalid.valid_getD hi) newWires hnewWires)
    state hstate
  simpa only [List.take_length] using hrun.2

/-- Evaluating a circuit of depth at most `step` starting at depth offset `offset` (`2 * offset`
into a generated chain of depth `2 * total`) advances the wire invariant to key
`2 * (offset + step)` and preserves the ordered output vector. -/
theorem encryptedWires_evaluateCircuit_drop (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (n total offset step : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool)))
    {inputCount outputCount : ℕ} (c : Circuit signature inputCount outputCount)
    (hstep : c.depth ≤ step) (htotal : offset + step ≤ total)
    (hchain : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * total))).support)
    (x : Fin inputCount → Bool) (inputs : List (List Bool))
    (hinputs : E.EncryptedWires ciphertextWidth n (keys.getD (2 * offset) ([], [])).2
      (List.ofFn x) inputs)
    (outputs : List (List Bool))
    (houtputs : outputs ∈ (ProbComp.eval
      (evaluateCircuit D n step ((keys.map Prod.fst).tail.drop (2 * offset))
        (links.drop (2 * offset)) inputs inputCount c.code)).support) :
    E.EncryptedWires ciphertextWidth n (keys.getD (2 * (offset + step)) ([], [])).2
      (List.ofFn (c.eval interpretation x)) outputs := by
  have hlength :
      (Layered.padTo inputCount (2 * step) (Layered.compile inputCount c.code).1).length =
        2 * step :=
    Layered.length_padTo_of_le _ _ _ (by rw [Layered.length_compile]; omega)
  rw [evaluateCircuit, ProbComp.eval_map, PMF.mem_support_map_iff] at houtputs
  obtain ⟨row, hrow, rfl⟩ := houtputs
  have h := encryptedWires_evaluateLayers_drop D hE hwidth hD n (2 * total) (2 * offset) keys
    links (Layered.padTo inputCount (2 * step) (Layered.compile inputCount c.code).1)
    (by omega) hchain (List.ofFn x) inputs hinputs
    (by simpa only [List.length_ofFn] using (Layered.wellFormed_compile c).padTo (2 * step))
    row hrow
  have heval : Layered.eval (List.ofFn x)
      (Layered.padTo inputCount (2 * step) (Layered.compile inputCount c.code).1) =
        Layered.eval (List.ofFn x) (Layered.compile inputCount c.code).1 := by
    simpa only [List.length_ofFn] using
      Layered.eval_padTo (List.ofFn x) (2 * step) (Layered.compile inputCount c.code).1
  rw [heval, hlength, ← Nat.mul_add] at h
  have hselected := h.select (outputs := (Layered.compile inputCount c.code).2) (by
    simpa only [Layered.length_eval, List.length_ofFn] using Layered.outputs_valid_compile c)
  simpa only [Layered.select_eval_compile] using hselected

/-- Tagged ciphertexts at depth offset `level` along a generated key chain: each ciphertext has
width `ciphertextWidth n + 1` and its payload decrypts under the secret key at index `2 * level`. -/
def EncryptedAtLevel (n level : ℕ) (chain : List (List Bool × List Bool))
    (bits : List Bool) (inputs : List (List Bool)) : Prop :=
  List.Forall₂
    (fun bit ciphertext =>
      ciphertext.length = ciphertextWidth n + 1 ∧
        E.decrypt n (chain.getD (2 * level) ([], [])).2 ciphertext.tail = bit)
    bits inputs

/-- Stripping the leading endpoint tag from `EncryptedAtLevel` ciphertexts yields base
`EncryptedWires` at key index `2 * level`. -/
theorem EncryptedAtLevel.tail_encryptedWires {n level : ℕ}
    {chain : List (List Bool × List Bool)} {bits : List Bool} {inputs : List (List Bool)}
    (h : EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n level chain bits inputs) :
    E.EncryptedWires ciphertextWidth n (chain.getD (2 * level) ([], [])).2
      bits (inputs.map List.tail) := by
  rw [Scheme.EncryptedWires, List.forall₂_map_right_iff]
  apply h.imp
  intro bit ciphertext hc
  refine ⟨?_, hc.2⟩
  rw [List.length_tail, hc.1, Nat.add_sub_cancel]

/-- Fresh leveled ciphertexts satisfy `EncryptedAtLevel` at depth offset `0`. -/
theorem freshInputs_encryptedAtLevel (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) {budget : ℕ → ℕ} {n : ℕ}
    {chain : List (List Bool × List Bool)} {links : List (List (List Bool))}
    (hchain : (chain, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * budget n))).support)
    {bits : List Bool} {inputs : List (List Bool)}
    (hinputs : (scheme D budget).FreshInputs n (keyPair (2 * budget n) chain links).1 bits inputs) :
    EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n 0 chain bits inputs := by
  have hfirst := E.key_mem_support_of_generatedChain hchain (Nat.zero_le _)
  have hpk : (chain.map Prod.fst).getD 0 [] = (chain.getD 0 ([], [])).1 :=
    List.getD_map chain ([], []) Prod.fst
  apply hinputs.imp
  intro bit ciphertext hc
  change ciphertext ∈ (ProbComp.eval (encrypt E n _ bit)).support at hc
  rw [encrypt, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨payload, hpayload, rfl⟩ := hc
  simp only [keyPair, publicKeyDecoder_decode_enc, hpk] at hpayload
  refine ⟨?_, ?_⟩
  · simp [hwidth.encrypt_length n _ hfirst bit payload hpayload]
  · simpa only [Nat.mul_zero, List.tail_cons] using
      hE.decrypt_encrypt n _ hfirst bit payload hpayload

/-- Evaluating one hop of depth at most `step` starting at offset `offset` produces a `true`-tagged
ciphertext of width `ciphertextWidth n + 1` whose payload decrypts under key `2 * (offset + step)`
to the evaluated circuit output. -/
theorem evaluateHop_spec (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) (n total offset step : ℕ)
    (chain : List (List Bool × List Bool)) (links : List (List (List Bool)))
    (hchain : (chain, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * total))).support)
    (c : Σ m, Circuit signature m 1) (hstep : c.2.depth ≤ step) (htotal : offset + step ≤ total)
    (bits : List Bool) (inputs : List (List Bool)) (hbits : bits.length = c.1)
    (hinputs :
      EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n offset chain bits inputs)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval
      (evaluateHop D n offset step (keyPair (2 * total) chain links).1 c inputs)).support) :
    ciphertext.length = ciphertextWidth n + 1 ∧
      ciphertext.headD false = true ∧
      E.decrypt n (chain.getD (2 * (offset + step)) ([], [])).2 ciphertext.tail =
        c.2.eval interpretation (BitString.ofList c.1 bits) 0 := by
  have hin := hinputs.tail_encryptedWires
  rw [evaluateHop, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨row, hrow, rfl⟩ := hc
  simp only [keyPair, publicKeyDecoder_decode_enc] at hrow
  have h := encryptedWires_evaluateCircuit_drop D hE hwidth hD n total offset step chain links c.2
    hstep htotal hchain (BitString.ofList c.1 bits) (inputs.map List.tail)
    (by simpa only [BitString.ofFn_ofList hbits] using hin) row hrow
  have hout := h.getD (i := 0) (by simp)
  have hlength : (row.headD []).length = ciphertextWidth n := by
    simpa only [List.headD_eq_getD] using hout.1
  refine ⟨by rw [List.length_cons, hlength], rfl, ?_⟩
  rw [List.tail_cons, List.headD_eq_getD]
  simpa using hout.2

/-- Pointwise hop evaluations at offset `offset` with step budget `step` advance `EncryptedAtLevel`
to `offset + step`. -/
theorem encryptedAtLevel_of_evaluateHop (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    {n total offset step : ℕ} {chain : List (List Bool × List Bool)}
    {links : List (List (List Bool))}
    (hchain : (chain, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * total))).support)
    (htotal : offset + step ≤ total) {midBits : List Bool} {mids : List (List Bool)}
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          c.2.depth ≤ step ∧
            bits.length = c.1 ∧
            EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n offset chain
              bits inputs ∧
            mid ∈ (ProbComp.eval
              (evaluateHop D n offset step (keyPair (2 * total) chain links).1 c inputs)).support ∧
            c.2.eval interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids) :
    EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n (offset + step) chain
      midBits mids :=
  hmids.imp fun _ _ ⟨c, bits, inputs, hstep, hbits, hinputs, hmid, heval⟩ => by
    have hspec := evaluateHop_spec D hE hwidth hD n total offset step chain links hchain c
      hstep htotal bits inputs hbits hinputs _ hmid
    exact ⟨hspec.1, hspec.2.2.trans heval⟩

/-- Final hop reaching the total budget `offset + step = budget n`: the output ciphertext has
width `ciphertextWidth n + 1` and decrypts under `(scheme D budget).decrypt` to the circuit
value. -/
theorem evaluateHop_final_spec (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (budget : ℕ → ℕ) (n offset step : ℕ)
    (chain : List (List Bool × List Bool)) (links : List (List (List Bool)))
    (hchain : (chain, links) ∈ (ProbComp.eval (E.generateKeyChain n (2 * budget n))).support)
    (hfinal : offset + step = budget n)
    (c : Σ m, Circuit signature m 1) (hstep : c.2.depth ≤ step)
    (bits : List Bool) (inputs : List (List Bool)) (hbits : bits.length = c.1)
    (hinputs :
      EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n offset chain bits inputs)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval
      (evaluateHop D n offset step (keyPair (2 * budget n) chain links).1 c inputs)).support) :
    ciphertext.length = ciphertextWidth n + 1 ∧
      (scheme D budget).decrypt n (keyPair (2 * budget n) chain links).2 ciphertext =
        c.2.eval interpretation (BitString.ofList c.1 bits) 0 := by
  have hlast := E.key_mem_support_of_generatedChain hchain (Nat.le_refl _)
  have hspec := evaluateHop_spec D hE hwidth hD n (budget n) offset step chain links hchain c
    hstep (by omega) bits inputs hbits hinputs ciphertext hc
  refine ⟨hspec.1, ?_⟩
  cases ciphertext with
  | nil => simp at hspec
  | cons tag payload =>
    have htag : tag = true := by simpa using hspec.2.1
    subst htag
    have hpayload : payload.length = ciphertextWidth n := by simpa using hspec.1
    change decrypt D n (encSecretKey _) (true :: payload) = _
    rw [decrypt_true D n _ _ _ (hwidth.secret_length n _ hlast) hpayload]
    simpa [hfinal] using hspec.2.2

/-- Two-hop leveled evaluation: first-hop circuits of depth at most `step₁` evaluated on fresh
inputs via `evaluateHop D n 0 step₁ keys.1`, followed by a second-hop circuit `outer` of depth at
most `step₂` evaluated on the intermediate ciphertexts via `evaluateHop D n step₁ step₂ keys.1`
with `step₁ + step₂ = budget n`, produces a ciphertext of width `ciphertextWidth n + 1` that
decrypts under `(scheme D budget).decrypt n keys.2` to the composed circuit value. -/
theorem evaluate_twoHop_spec (hE : E.Correct)
    (hwidth : E.FixedWidth secretWidth ciphertextWidth) (hD : Scheme.Bootstrappable D)
    (budget : ℕ → ℕ) (n step₁ step₂ : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D budget).keyGen n)).support)
    (hbudget : step₁ + step₂ = budget n)
    (outer : Σ m, Circuit signature m 1) (houter : outer.2.depth ≤ step₂)
    (midBits : List Bool) (mids : List (List Bool)) (hmidBits : midBits.length = outer.1)
    (hmids : List.Forall₂
      (fun bit mid =>
        ∃ (c : Σ m, Circuit signature m 1) (bits : List Bool) (inputs : List (List Bool)),
          c.2.depth ≤ step₁ ∧
            bits.length = c.1 ∧
            (scheme D budget).FreshInputs n keys.1 bits inputs ∧
            mid ∈ (ProbComp.eval (evaluateHop D n 0 step₁ keys.1 c inputs)).support ∧
            c.2.eval interpretation (BitString.ofList c.1 bits) 0 = bit)
      midBits mids)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval (evaluateHop D n step₁ step₂ keys.1 outer mids)).support) :
    ciphertext.length = ciphertextWidth n + 1 ∧
      (scheme D budget).decrypt n keys.2 ciphertext =
        outer.2.eval interpretation (BitString.ofList outer.1 midBits) 0 := by
  obtain ⟨chain, links, hchain, rfl⟩ := (mem_support_keyGen_iff n (budget n) keys).1 hkeys
  have hmidsLevel :
      EncryptedAtLevel (E := E) (ciphertextWidth := ciphertextWidth) n step₁ chain
        midBits mids := by
    simpa only [Nat.zero_add] using
      encryptedAtLevel_of_evaluateHop D hE hwidth hD hchain (offset := 0) (step := step₁)
        (by omega)
        (hmids.imp fun _ _ ⟨c, bits, inputs, hstep, hbits, hinputs, hmid, heval⟩ =>
          ⟨c, bits, inputs, hstep, hbits,
            freshInputs_encryptedAtLevel D hE hwidth hchain hinputs, hmid, heval⟩)
  exact evaluateHop_final_spec D hE hwidth hD budget n step₁ step₂ chain links hchain hbudget
    outer houter midBits mids hmidBits hmidsLevel ciphertext hc

/-- Removing fresh tags gives fresh base ciphertexts under the initial public key. -/
theorem freshInputs_tail {budget : ℕ → ℕ} {n : ℕ} {pk bits : List Bool}
    {inputs : List (List Bool)} (h : (scheme D budget).FreshInputs n pk bits inputs) :
    E.FreshInputs n ((publicKeyDecoder.decode pk).1.getD 0 []) bits
      (inputs.map List.tail) := by
  rw [Scheme.FreshInputs, List.forall₂_map_right_iff]
  apply h.imp
  intro bit ciphertext hc
  change ciphertext ∈ (ProbComp.eval (encrypt E n pk bit)).support at hc
  rw [encrypt, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨payload, hpayload, rfl⟩ := hc
  exact hpayload

/-- Fresh ciphertexts have the tagged base width and decrypt under the initial endpoint. -/
theorem encrypt_spec (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (budget : ℕ → ℕ) (n : ℕ) (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D budget).keyGen n)).support)
    (bit : Bool) (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval ((scheme D budget).encrypt n keys.1 bit)).support) :
    ciphertext.length = ciphertextWidth n + 1 ∧
      (scheme D budget).decrypt n keys.2 ciphertext = bit := by
  obtain ⟨chain, links, hchain, rfl⟩ := (mem_support_keyGen_iff n (budget n) keys).1 hkeys
  have hfirst := E.key_mem_support_of_generatedChain hchain (Nat.zero_le _)
  change ciphertext ∈ (ProbComp.eval (encrypt E n _ bit)).support at hc
  rw [encrypt, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨payload, hpayload, rfl⟩ := hc
  have hpk : (chain.map Prod.fst).getD 0 [] = (chain.getD 0 ([], [])).1 :=
    List.getD_map chain ([], []) Prod.fst
  simp only [keyPair, publicKeyDecoder_decode_enc, hpk] at hpayload
  have hlength := hwidth.encrypt_length n _ hfirst bit payload hpayload
  refine ⟨by simp [hlength], ?_⟩
  change decrypt D n (encSecretKey _) (false :: payload) = bit
  rw [decrypt_false D n _ _ _ (hwidth.secret_length n _ hfirst) hlength]
  exact hE.decrypt_encrypt n _ hfirst bit payload hpayload

/-- Every supported permitted evaluation has the tagged base width and decrypts at the common
final endpoint. This includes circuits whose actual depth is smaller than the chosen budget. -/
theorem evaluate_spec (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) (budget : ℕ → ℕ) (n : ℕ)
    (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval ((scheme D budget).keyGen n)).support)
    (c : Σ m, Circuit signature m 1) (hbudget : (scheme D budget).permitted n c)
    (bits : List Bool) (inputs : List (List Bool)) (hbits : bits.length = c.1)
    (hinputs : (scheme D budget).FreshInputs n keys.1 bits inputs)
    (ciphertext : List Bool)
    (hc : ciphertext ∈ (ProbComp.eval ((scheme D budget).evaluate n keys.1 c inputs)).support) :
    ciphertext.length = ciphertextWidth n + 1 ∧
      (scheme D budget).decrypt n keys.2 ciphertext =
        c.2.eval interpretation (BitString.ofList c.1 bits) 0 := by
  obtain ⟨chain, links, hchain, rfl⟩ := (mem_support_keyGen_iff n (budget n) keys).1 hkeys
  have hlast := E.key_mem_support_of_generatedChain hchain (Nat.le_refl _)
  have hin := freshInputs_tail D hinputs
  have hpk : (chain.map Prod.fst).getD 0 [] = (chain.getD 0 ([], [])).1 :=
    List.getD_map chain ([], []) Prod.fst
  simp only [keyPair, publicKeyDecoder_decode_enc, hpk] at hin
  change ciphertext ∈ (ProbComp.eval (evaluate D n (budget n) _ c inputs)).support at hc
  rw [evaluate, ProbComp.eval_map, PMF.mem_support_map_iff] at hc
  obtain ⟨row, hrow, rfl⟩ := hc
  simp only [keyPair, publicKeyDecoder_decode_enc] at hrow
  rw [← List.map_tail] at hrow
  have h := encryptedWires_evaluateCircuit D hE hwidth hD n (budget n) chain links c.2
    hbudget hchain (BitString.ofList c.1 bits) (inputs.map List.tail)
    (by simpa only [BitString.ofFn_ofList hbits] using hin) row hrow
  have hout := h.getD (i := 0) (by simp)
  have hlength : (row.headD []).length = ciphertextWidth n := by
    simpa only [List.headD_eq_getD] using hout.1
  refine ⟨by rw [List.length_cons, hlength], ?_⟩
  change decrypt D n (encSecretKey _) (true :: row.headD []) = _
  rw [decrypt_true D n _ _ _ (hwidth.secret_length n _ hlast) hlength]
  rw [List.headD_eq_getD]
  simpa using hout.2

/-- Bootstrappability constructs a correct scheme for every circuit within the depth budget.
No assumption of leveled correctness is used; the keys, padding, and evaluation are explicit. -/
theorem correct (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) (budget : ℕ → ℕ) : (scheme D budget).Correct where
  decrypt_encrypt n keys hkeys bit ciphertext hc :=
    (encrypt_spec D hE hwidth budget n keys hkeys bit ciphertext hc).2
  decrypt_evaluate n keys hkeys c hbudget bits inputs hbits hinputs ciphertext hc :=
    (evaluate_spec D hE hwidth hD budget n keys hkeys c hbudget bits inputs hbits hinputs
      ciphertext hc).2

/-- Private key and ciphertext lengths are independent of both circuit size and depth budget.
Public key size and key-generation work may grow with the budget. -/
theorem fixedWidth (hE : E.Correct) (hwidth : E.FixedWidth secretWidth ciphertextWidth)
    (hD : Scheme.Bootstrappable D) (budget : ℕ → ℕ) :
    (scheme D budget).FixedWidth (fun n => 3 * secretWidth n + 1)
      (fun n => ciphertextWidth n + 1) where
  secret_length n keys hkeys := by
    obtain ⟨chain, links, hchain, rfl⟩ := (mem_support_keyGen_iff n (budget n) keys).1 hkeys
    have hfirst := E.key_mem_support_of_generatedChain hchain (Nat.zero_le _)
    have hlast := E.key_mem_support_of_generatedChain hchain (Nat.le_refl _)
    simp only [keyPair, length_encSecretKey, hwidth.secret_length n _ hfirst,
      hwidth.secret_length n _ hlast]
    omega
  encrypt_length n keys hkeys bit ciphertext hc :=
    (encrypt_spec D hE hwidth budget n keys hkeys bit ciphertext hc).1
  evaluate_length n keys hkeys c hbudget bits inputs hbits hinputs ciphertext hc :=
    (evaluate_spec D hE hwidth hD budget n keys hkeys c hbudget bits inputs hbits hinputs
      ciphertext hc).1

end Cslib.Crypto.Homomorphic.Leveled
