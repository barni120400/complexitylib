/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.DiffieHellman
public import Complexity.Crypto.Game.Hybrid
public import Complexity.Foundations.Data.BitString.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Probability.PMF.Uniform
import Complexity.Tactic.PolyTime

/-!
# The Naor–Reingold pseudorandom function from Decisional Diffie–Hellman

Over a `PrimeOrderGroupFamily` `F`, the Naor–Reingold pseudorandom function
([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424; [NaorReingold2004], Section 4.1,
Construction 4.1 & Theorem 4.1) with key `(α₀, α₁, …, αₙ) ∈ (ZMod q)ⁿ⁺¹` maps an `n`-bit input
`x ∈ {0, 1}ⁿ` to the group element
$$F_{\mathrm{NR}}((\alpha_0, \alpha_1, \dots, \alpha_n), (x_1, \dots, x_n))
  := \left(\alpha_0 \cdot \prod_{i=1}^n \alpha_i^{x_i}\right) \bullet g.$$

Following Boneh–Shoup Exercises 10.4, 10.8, 10.11, and 4.18, we formalize:

1. **Algebraic and augmented-tree characterization (`naorReingoldEval`, `naorReingoldTreeEval`)**:
   - The closed-form exponent product `naorReingoldExp` and group evaluation `naorReingoldEval`.
   - The single-step generator `naorReingoldPRG`
     ($G_{\mathrm{NR}}(\alpha, u) = (u, \alpha \bullet u)$)
     and augmented-tree fold `naorReingoldTreeEval`, together with
     `naorReingoldTreeEval_eq_naorReingoldEval` ([BonehShoup2023], Exercise 10.4(a), p. 424, and
     Exercise 4.18, p. 172).
   - The word-level evaluator `naorReingoldWordEval`, its correctness theorem
     `naorReingoldWordEval_eq_encode`, and its plain polynomial-time certificate
     `computableInPolyTime_naorReingoldWordEval`.
2. **Fixed-$u$ DDH random self-reduction and Multi-DDH (I) (`ddhFixedURerandomize`,
   `multiDDHRerandomizeLaw`)**:
   - Fixed-$u$ rerandomization $(u, v, w) \mapsto (u, \sigma \bullet g + \tau \bullet v,
     \sigma \bullet u + \tau \bullet w)$ ([BonehShoup2023], Exercise 10.8, p. 425), its word-level
     counterpart `ddhFixedUWordRerandomize`, and the exact distributional laws
     `ddhFixedURerandomizeLaw_real` (Exercise 10.8(a)) and `ddhFixedURerandomizeLaw_ideal`
     (Exercise 10.8(b)).
   - The $n = 1$ (single shared secret $\alpha$, $|\iota|$ pairs) Multi-DDH (I) reduction
     `multiDDHRerandomizeLaw` ([BonehShoup2023], Exercise 10.11, p. 426), whose wrapper samples
     $|\iota|$ rerandomized pairs, proving `multiDDHRerandomizeLaw_real`,
     `multiDDHRerandomizeLaw_ideal`, and the quantitative bound `advantage_multiDDH_le`
     ($\le \mathrm{DDHadv}[B] + 1 / q$).
3. **Naor–Reingold PRF prefix hybrids and distributional security bound (`naorReingoldRealGame`,
   `naorReingoldIdealGame`, `naorReingoldHybridGame`)**:
   - The adaptive oracle experiments `naorReingoldRealGame`, `naorReingoldIdealGame`, and the
     depth-$k$ prefix hybrids `naorReingoldHybridGame` ($0 \le k \le n$), with exact endpoint
     identities `naorReingoldHybridGame_zero` and `naorReingoldHybridGame_self`.
   - The distributional single-level DDH distinguisher `naorReingoldLevelDDHDistinguisher`
     (which samples the $2^k$-entry prefix table `BitString k`) and adjacent-hop bound
     `advantage_naorReingoldHybridGame_succ_le`, the $n$-hybrid sum bound
     `advantage_naorReingold_le_sum`, and the common-bound corollary `advantage_naorReingold_le_mul`
     ($\le n \cdot (\varepsilon + 1 / q)$). The efficient lazy-sampling reduction (`IsOraclePPT` /
     `PseudorandomFunction` bridge) remains open in #1093.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldEval`:
  the Naor–Reingold exponent product and PRF evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldPRG`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldStep`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldTreeEval`:
  the single-step generator $G_{\mathrm{NR}}$ and augmented-tree evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldWordEval`:
  polynomial-time evaluation on encoded group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomize`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw`:
  fixed-$u$ DDH rerandomization (Boneh–Shoup Exercise 10.8).
* `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRealTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHIdealTupleLaw`,
  `Cslib.Crypto.PrimeOrderGroupFamily.multiDDHRerandomizeLaw`:
  $n = 1$ Multi-DDH (I) distributions and rerandomization (Boneh–Shoup Exercise 10.11).
* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldRealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldHybridGame`:
  real, ideal, and prefix-hybrid adaptive PRF experiments.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.naorReingoldTreeEval_eq_naorReingoldEval`:
  augmented-tree characterization of the Naor–Reingold PRF (Boneh–Shoup Exercise 10.4(a)).
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_naorReingoldWordEval`:
  plain polynomial-time certificate for word-level Naor–Reingold evaluation.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_real`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhFixedURerandomizeLaw_ideal`:
  fixed-$u$ DDH random self-reduction (Boneh–Shoup Exercise 10.8).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_multiDDH_le`:
  $n = 1$ Multi-DDH (I) reduction to DDH, sampling $|\iota|$ rerandomized pairs
  (Boneh–Shoup Exercise 10.11).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingoldHybridGame_succ_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingold_le_sum`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_naorReingold_le_mul`:
  distributional prefix-hybrid security bounds for the Naor–Reingold PRF against the explicit
  $2^k$-pair PMF distinguisher `naorReingoldLevelDDHDistinguisher` (Boneh–Shoup Exercise 10.4(b);
  Naor–Reingold Theorem 4.1). The efficient lazy-sampling reduction (`IsOraclePPT` /
  `PseudorandomFunction` bridge) remains open in #1093.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.11 (Exercise 4.18, p. 172) and Section 10.11
  (Exercises 10.4, 10.8, 10.11, pp. 424–426).
* [M. Naor, O. Reingold, *Number-Theoretic Constructions of Efficient Pseudo-Random
  Functions*][NaorReingold2004], Section 4.1 (Construction 4.1 & Theorem 4.1).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Naor–Reingold PRF and augmented-tree characterization (Exercise 10.4(a) & Exercise 4.18) -/

/-- The Naor–Reingold exponent product `α₀ * ∏ i : Fin n, if x i then α i else 1` in
`ZMod (F.order d)` ([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424;
[NaorReingold2004], Section 4.1, Construction 4.1). -/
def naorReingoldExp (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    ZMod (F.order d) :=
  α₀ * ∏ i : Fin n, if x i then α i else 1

/-- The Naor–Reingold pseudorandom function
`F_NR((α₀, α₁, …, αₙ), (x₁, …, xₙ)) = (α₀ * ∏ i, αᵢ^{xᵢ}) • g`
([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424;
[NaorReingold2004], Section 4.1, Construction 4.1). -/
def naorReingoldEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  F.naorReingoldExp d α₀ α x • F.generator d

@[simp]
theorem naorReingoldExp_zero (d : F.Desc)
    (α₀ : ZMod (F.order d)) (α : Fin 0 → ZMod (F.order d)) (x : BitString 0) :
    F.naorReingoldExp d α₀ α x = α₀ := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_zero (d : F.Desc)
    (α₀ : ZMod (F.order d)) (α : Fin 0 → ZMod (F.order d)) (x : BitString 0) :
    F.naorReingoldEval d α₀ α x = α₀ • F.generator d := by
  simp [naorReingoldEval]

@[simp]
theorem naorReingoldExp_false (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldExp d α₀ α (fun _ => false) = α₀ := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_false (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldEval d α₀ α (fun _ => false) = α₀ • F.generator d := by
  simp [naorReingoldEval]

@[simp]
theorem naorReingoldExp_true (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldExp d α₀ α (fun _ => true) = α₀ * ∏ i : Fin n, α i := by
  simp [naorReingoldExp]

@[simp]
theorem naorReingoldEval_true (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
    F.naorReingoldEval d α₀ α (fun _ => true) = (α₀ * ∏ i : Fin n, α i) • F.generator d := by
  simp [naorReingoldEval]

/-- The Naor–Reingold single-step generator `G_NR(α, u) := (u, α • u)` ([BonehShoup2023],
Section 10.11, Exercise 10.4(a), p. 424). -/
def naorReingoldPRG (d : F.Desc) (α : ZMod (F.order d)) (u : F.Carrier d) :
    F.Carrier d × F.Carrier d :=
  (u, α • u)

/-- One step of the augmented tree construction ([BonehShoup2023], Section 4.11, Exercise 4.18,
p. 172, and Section 10.11, Exercise 10.4(a), p. 424): select the `false` (`u`) or `true` (`α • u`)
child of `naorReingoldPRG d α u`. -/
def naorReingoldStep (d : F.Desc) (u : F.Carrier d) (p : ZMod (F.order d) × Bool) :
    F.Carrier d :=
  if p.2 then p.1 • u else u

@[simp]
theorem naorReingoldStep_eq_prg (d : F.Desc) (u : F.Carrier d) (α : ZMod (F.order d)) (b : Bool) :
    F.naorReingoldStep d u (α, b) =
      if b then (F.naorReingoldPRG d α u).2 else (F.naorReingoldPRG d α u).1 :=
  rfl

/-- Augmented-tree evaluation of `naorReingoldStep` along a list of `(key, bit)` pairs starting
from an initial group element `u`. -/
def naorReingoldTreeFold (d : F.Desc) (u : F.Carrier d)
    (steps : List (ZMod (F.order d) × Bool)) : F.Carrier d :=
  steps.foldl (F.naorReingoldStep d) u

/-- Augmented-tree evaluation of the Naor–Reingold PRF from root `α₀ • g` along `(α i, x i)` for
`i : Fin n` ([BonehShoup2023], Exercise 10.4(a), p. 424, and Exercise 4.18, p. 172). -/
def naorReingoldTreeEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  F.naorReingoldTreeFold d (α₀ • F.generator d) (List.ofFn fun i : Fin n => (α i, x i))

/-- Folding `naorReingoldStep` starting from `β • u` multiplies the scalar `β` by the product of
selected step exponents. -/
theorem naorReingoldTreeFold_smul (d : F.Desc) (β : ZMod (F.order d)) (u : F.Carrier d)
    (steps : List (ZMod (F.order d) × Bool)) :
    F.naorReingoldTreeFold d (β • u) steps =
      (β * (steps.map fun p => if p.2 then p.1 else 1).prod) • u := by
  induction steps generalizing β with
  | nil => simp [naorReingoldTreeFold]
  | cons p rest ih =>
    have hstep : F.naorReingoldStep d (β • u) p = (β * if p.2 then p.1 else 1) • u := by
      rcases p with ⟨a, _ | _⟩ <;> simp [naorReingoldStep, smul_smul, mul_comm]
    rw [naorReingoldTreeFold, List.foldl_cons, ← naorReingoldTreeFold, hstep,
      ih (β * if p.2 then p.1 else 1), List.map_cons, List.prod_cons, mul_assoc]

/-- **Boneh–Shoup Exercise 10.4(a)**: the augmented-tree construction `naorReingoldTreeEval` built
from `naorReingoldPRG` ($G_{\mathrm{NR}}(\alpha, u) = (u, \alpha \bullet u)$) coincides with
`naorReingoldEval`. -/
theorem naorReingoldTreeEval_eq_naorReingoldEval (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldTreeEval d α₀ α x = F.naorReingoldEval d α₀ α x := by
  rw [naorReingoldTreeEval, naorReingoldTreeFold_smul, naorReingoldEval, naorReingoldExp]
  congr 2
  rw [List.map_ofFn, Fin.prod_univ_def, List.prod_ofFn]
  rfl

/-! ### Word-level polynomial-time evaluation -/

/-- Multiply the selected natural-number exponents in `steps` starting from `acc`. -/
def naorReingoldProdNat (acc : ℕ) (steps : List (ℕ × Bool)) : ℕ :=
  steps.foldl (fun e p => if p.2 then e * p.1 else e) acc

/-- Casting `naorReingoldProdNat` to `ZMod q` equals `acc` times the product of selected step
exponents in `ZMod q`. -/
theorem naorReingoldProdNat_cast (q acc : ℕ) (steps : List (ℕ × Bool)) :
    (naorReingoldProdNat acc steps : ZMod q) =
      (acc : ZMod q) * (steps.map fun p => if p.2 then (p.1 : ZMod q) else 1).prod := by
  induction steps generalizing acc with
  | nil => simp [naorReingoldProdNat]
  | cons p rest ih =>
    rw [naorReingoldProdNat, List.foldl_cons, ← naorReingoldProdNat,
      ih (if p.2 then acc * p.1 else acc), List.map_cons, List.prod_cons]
    rcases p with ⟨a, _ | _⟩ <;> simp [Nat.cast_mul, mul_assoc]

/-- Word-level suffix evaluation of the Naor–Reingold tree from an encoded group element `u` along
`αs` and `xs`. -/
def naorReingoldWordSuffix (d : F.Desc) (u : List Bool) (αs : List ℕ) (xs : List Bool) :
    List Bool :=
  F.smul (d, naorReingoldProdNat 1 (αs.zip xs), u)

/-- Word-level evaluation of the Naor–Reingold PRF on `(d, α₀, αs, xs)`. -/
def naorReingoldWordEval (d : F.Desc) (α₀ : ℕ) (αs : List ℕ) (xs : List Bool) : List Bool :=
  F.smul (d, naorReingoldProdNat α₀ (αs.zip xs), F.encode d (F.generator d))

/-- On an encoded group element `F.encode d u`, `naorReingoldWordSuffix` computes the encoding of
`naorReingoldTreeFold`. -/
theorem naorReingoldWordSuffix_encode (d : F.Desc) (u : F.Carrier d) (αs : List ℕ)
    (xs : List Bool) :
    F.naorReingoldWordSuffix d (F.encode d u) αs xs =
      F.encode d (F.naorReingoldTreeFold d u
        ((αs.zip xs).map fun p => ((p.1 : ZMod (F.order d)), p.2))) := by
  obtain ⟨β, rfl⟩ := F.smul_generator_surjective d u
  rw [naorReingoldWordSuffix, F.smul_encode, naorReingoldProdNat_cast, Nat.cast_one, one_mul,
    naorReingoldTreeFold_smul, List.map_map, smul_smul, mul_comm]
  rfl

/-- Correctness of `naorReingoldWordEval` on an `n`-element exponent list `αs` and `n`-bit query
`xs`. -/
theorem naorReingoldWordEval_eq_encode (d : F.Desc) {n : ℕ} (α₀ : ℕ)
    (α : Fin n → ℕ) (x : BitString n) :
    F.naorReingoldWordEval d α₀ (List.ofFn α) (List.ofFn x) =
      F.encode d (F.naorReingoldEval d (α₀ : ZMod (F.order d))
        (fun i => (α i : ZMod (F.order d))) x) := by
  rw [naorReingoldWordEval, F.smul_encode, naorReingoldProdNat_cast, naorReingoldEval,
    naorReingoldExp]
  congr 2
  have hzip : (List.ofFn α).zip (List.ofFn x) = List.ofFn (fun i : Fin n => (α i, x i)) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp
  rw [hzip, List.map_ofFn, Fin.prod_univ_def, List.prod_ofFn]
  rfl

/-- `naorReingoldProdNat` is computable in polynomial time. -/
@[fun_prop]
theorem computableTidilyInPolyTime_naorReingoldProdNat :
    ComputableTidilyInPolyTime
      (fun input : ℕ × List (ℕ × Bool) => naorReingoldProdNat input.1 input.2)
      (encPair encNat (encList (encPair encNat encBool))) encNat := by
  unfold naorReingoldProdNat
  refine ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encPair encNat encBool) (encL := encList (encPair encNat encBool))
    (encB := encNat) (encP := encBool)
    (par := fun _ => false) (list := Prod.snd) (init := Prod.fst)
    (step := fun _ e p => if p.2 then e * p.1 else e)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun input => (encList (encPair encNat encBool) input.2).length)
    (ComputableTidilyInPolyTime.snd _ _).polyBounded_length ?_
  intro input state value hmem
  have hval : value.1.size ≤ (encList (encPair encNat encBool) input.2).length := by
    rw [← Nat.size_eq_bits_len, ← encNat_apply]
    have h1 : (encNat value.1).length ≤ (encPair encNat encBool value).length := by
      simp only [length_encPair]
      omega
    exact h1.trans (length_le_encList_of_mem (encPair encNat encBool) hmem)
  rcases value with ⟨v, _ | _⟩
  · simp
  · simp only [↓reduceIte, encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_mul_le state v).trans (Nat.add_le_add_left hval _)

/-- `naorReingoldWordSuffix` is computable in polynomial time. -/
theorem computableInPolyTime_naorReingoldWordSuffix :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool =>
        F.naorReingoldWordSuffix input.1 input.2.1 input.2.2.1 input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encBits := by
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) F.encDesc := by
    fun_prop
  have hu : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encBits := by
    fun_prop
  have hαs : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList encNat) := by
    fun_prop
  have hxs : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList encBool) :=
    ComputableTidilyInPolyTime.bitsToList.comp (by fun_prop)
  have hzip : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool => input.2.2.1.zip input.2.2.2)
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits)))
      (encList (encPair encNat encBool)) :=
    (ComputableTidilyInPolyTime.zip encNat encBool).comp (hαs.prod hxs)
  have hprod : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List ℕ × List Bool =>
        naorReingoldProdNat 1 (input.2.2.1.zip input.2.2.2))
      (encPair F.encDesc (encPair encBits (encPair (encList encNat) encBits))) encNat :=
    computableTidilyInPolyTime_naorReingoldProdNat.comp
      ((ComputableTidilyInPolyTime.const 1).prod hzip)
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_smul.tidy.comp (hd.prod (hprod.prod hu)))

/-- `naorReingoldWordEval` is computable in polynomial time. -/
theorem computableInPolyTime_naorReingoldWordEval :
    ComputableInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool =>
        F.naorReingoldWordEval input.1 input.2.1 input.2.2.1 input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encBits := by
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) F.encDesc := by
    fun_prop
  have hα₀ : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encNat := by
    fun_prop
  have hαs : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.1)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) (encList encNat) := by
    fun_prop
  have hxs : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits)))
      (encList encBool) :=
    ComputableTidilyInPolyTime.bitsToList.comp (by fun_prop)
  have hzip : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => input.2.2.1.zip input.2.2.2)
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits)))
      (encList (encPair encNat encBool)) :=
    (ComputableTidilyInPolyTime.zip encNat encBool).comp (hαs.prod hxs)
  have hprod : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool =>
        naorReingoldProdNat input.2.1 (input.2.2.1.zip input.2.2.2))
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encNat :=
    computableTidilyInPolyTime_naorReingoldProdNat.comp (hα₀.prod hzip)
  have hgen : ComputableTidilyInPolyTime
      (fun input : F.Desc × ℕ × List ℕ × List Bool => F.encode input.1 (F.generator input.1))
      (encPair F.encDesc (encPair encNat (encPair (encList encNat) encBits))) encBits :=
    F.computableInPolyTime_generator.tidy.comp hd
  exact ComputableInPolyTime.of_tidy
    (F.computableInPolyTime_smul.tidy.comp (hd.prod (hprod.prod hgen)))

/-! ### Fixed-$u$ DDH random self-reduction and Multi-DDH (I) (Exercises 10.8 & 10.11) -/

/-- Fixed-$u$ DDH rerandomization ([BonehShoup2023], Section 10.11, Exercise 10.8, p. 425):
given `(u, v, w)` and exponents `σ, τ : ZMod (F.order d)`, output
`(v*, w*) = (σ • g + τ • v, σ • u + τ • w)`. -/
def ddhFixedURerandomize (d : F.Desc) (u v w : F.Carrier d)
    (σ τ : ZMod (F.order d)) : F.Carrier d × F.Carrier d :=
  (σ • F.generator d + τ • v, σ • u + τ • w)

/-- Algebraic action of `ddhFixedURerandomize` on multiples of the generator:
`v* = (σ + τ * β) • g` and `w* = (α * (σ + τ * β) + τ * (γ - α * β)) • g`. -/
theorem ddhFixedURerandomize_smul_generator (d : F.Desc) (α β γ σ τ : ZMod (F.order d)) :
    F.ddhFixedURerandomize d (α • F.generator d) (β • F.generator d) (γ • F.generator d) σ τ =
      ((σ + τ * β) • F.generator d,
        (α * (σ + τ * β) + τ * (γ - α * β)) • F.generator d) := by
  simp only [ddhFixedURerandomize, smul_smul, ← add_smul]
  refine Prod.ext rfl (congrArg (· • F.generator d) (by ring))

/-- Word-level fixed-$u$ DDH rerandomization on encoded group elements. -/
def ddhFixedUWordRerandomize (d : F.Desc) (u v w : List Bool) (σ τ : ℕ) :
    List Bool × List Bool :=
  (F.add (d, F.smul (d, σ, F.encode d (F.generator d)), F.smul (d, τ, v)),
   F.add (d, F.smul (d, σ, u), F.smul (d, τ, w)))

/-- `ddhFixedUWordRerandomize` computes the encoded output of `ddhFixedURerandomize`. -/
theorem ddhFixedUWordRerandomize_encode (d : F.Desc) (u v w : F.Carrier d) (σ τ : ℕ) :
    F.ddhFixedUWordRerandomize d (F.encode d u) (F.encode d v) (F.encode d w) σ τ =
      ((F.encode d (F.ddhFixedURerandomize d u v w σ τ).1,
        F.encode d (F.ddhFixedURerandomize d u v w σ τ).2)) := by
  simp [ddhFixedUWordRerandomize, ddhFixedURerandomize, F.smul_encode, F.add_encode]

/-- `ddhFixedUWordRerandomize` is computable in polynomial time. -/
theorem computableInPolyTime_ddhFixedUWordRerandomize :
    ComputableInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ =>
        F.ddhFixedUWordRerandomize input.1 input.2.1 input.2.2.1 input.2.2.2.1
          input.2.2.2.2.1 input.2.2.2.2.2)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      (encPair encBits encBits) := by
  have hd : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      F.encDesc := by fun_prop
  have hu : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hv : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hw : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encBits := by fun_prop
  have hσ : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.2.1)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encNat := by fun_prop
  have hτ : ComputableTidilyInPolyTime
      (fun input : F.Desc × List Bool × List Bool × List Bool × ℕ × ℕ => input.2.2.2.2.2)
      (encPair F.encDesc
        (encPair encBits (encPair encBits (encPair encBits (encPair encNat encNat)))))
      encNat := by fun_prop
  have hgen := F.computableInPolyTime_generator.tidy.comp hd
  have hσg := F.computableInPolyTime_smul.tidy.comp (hd.prod (hσ.prod hgen))
  have hτv := F.computableInPolyTime_smul.tidy.comp (hd.prod (hτ.prod hv))
  have hσu := F.computableInPolyTime_smul.tidy.comp (hd.prod (hσ.prod hu))
  have hτw := F.computableInPolyTime_smul.tidy.comp (hd.prod (hτ.prod hw))
  have hv' := F.computableInPolyTime_add.tidy.comp (hd.prod (hσg.prod hτv))
  have hw' := F.computableInPolyTime_add.tidy.comp (hd.prod (hσu.prod hτw))
  exact ComputableInPolyTime.of_tidy (hv'.prod hw')

/-- The distribution of `(v*, w*)` obtained by drawing `σ, τ : ZMod (F.order d)` independently and
uniformly in `ddhFixedURerandomize` ([BonehShoup2023], Exercise 10.8, p. 425). -/
noncomputable def ddhFixedURerandomizeLaw (d : F.Desc) (u v w : F.Carrier d) :
    PMF (F.Carrier d × F.Carrier d) := do
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  return F.ddhFixedURerandomize d u v w σ τ

/-- The real DDH pair distribution `(β • g, (α * β) • g)` for a fixed first exponent `α`. -/
noncomputable def ddhFixedURealLaw (d : F.Desc) (α : ZMod (F.order d)) :
    PMF (F.Carrier d × F.Carrier d) := do
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  return (β • F.generator d, (α * β) • F.generator d)

/-- The ideal pair distribution `(β • g, γ • g)` on `F.Carrier d × F.Carrier d`. -/
noncomputable def ddhFixedUIdealLaw (d : F.Desc) :
    PMF (F.Carrier d × F.Carrier d) := do
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  return (β • F.generator d, γ • F.generator d)

private theorem uniformOfFintype_bind_equiv {α β : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (f : α → PMF β) :
    (PMF.uniformOfFintype α).bind (fun a => f (e a)) = (PMF.uniformOfFintype α).bind f := by
  change (PMF.uniformOfFintype α).bind (f ∘ e) = (PMF.uniformOfFintype α).bind f
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- **Boneh–Shoup Exercise 10.8(a)**: if `(u, v, w) = (α • g, β • g, (α * β) • g)` is a DDH triple,
then `ddhFixedURerandomizeLaw` produces `ddhFixedURealLaw d α` for every `α, β`. -/
theorem ddhFixedURerandomizeLaw_real (d : F.Desc) (α β : ZMod (F.order d)) :
    F.ddhFixedURerandomizeLaw d (α • F.generator d) (β • F.generator d)
      ((α * β) • F.generator d) = F.ddhFixedURealLaw d α := by
  simp only [ddhFixedURerandomizeLaw, ddhFixedURealLaw, ddhFixedURerandomize_smul_generator,
    sub_self, mul_zero, add_zero, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  have hσ (τ : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        PMF.pure ((σ + τ * β) • F.generator d, (α * (σ + τ * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (β' • F.generator d, (α * β') • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addRight (τ * β))
      (fun β' => PMF.pure (β' • F.generator d, (α * β') • F.generator d))
  simp_rw [hσ, PMF.bind_const]

/-- **Boneh–Shoup Exercise 10.8(b)**: if `(u, v, w) = (α • g, β • g, γ • g)` is a non-DDH triple
(`γ ≠ α * β`), then `ddhFixedURerandomizeLaw` produces `ddhFixedUIdealLaw d`. -/
theorem ddhFixedURerandomizeLaw_ideal (d : F.Desc) {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.ddhFixedURerandomizeLaw d (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.ddhFixedUIdealLaw d := by
  simp only [ddhFixedURerandomizeLaw, ddhFixedUIdealLaw, ddhFixedURerandomize_smul_generator,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  have hσ (τ : ZMod (F.order d)) :
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        PMF.pure ((σ + τ * β) • F.generator d,
          (α * (σ + τ * β) + τ * (γ - α * β)) • F.generator d)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β' =>
        PMF.pure (β' • F.generator d,
          (α * β' + τ * (γ - α * β)) • F.generator d)) :=
    uniformOfFintype_bind_equiv (Equiv.addRight (τ * β))
      (fun β' => PMF.pure (β' • F.generator d,
        (α * β' + τ * (γ - α * β)) • F.generator d))
  simp_rw [hσ]
  rw [PMF.bind_comm]
  congr 1; funext β'
  exact uniformOfFintype_bind_equiv
    ((Equiv.mulRight₀ (γ - α * β) (sub_ne_zero.mpr hγ)).trans (Equiv.addLeft (α * β')))
    (fun γ' => PMF.pure (β' • F.generator d, γ' • F.generator d))

/-- The Multi-DDH (I) real tuple family `i ↦ (B i • g, (α * B i) • g)` for a fixed `α` and an
index type `ι` ([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
noncomputable def multiDDHRealTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α : ZMod (F.order d)) : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d))).map fun B i =>
    (B i • F.generator d, (α * B i) • F.generator d)

/-- The Multi-DDH (I) ideal tuple family `i ↦ (B₀ i • g, B₁ i • g)` for an index type `ι`
([BonehShoup2023], Section 10.11, Exercise 10.11, p. 426). -/
noncomputable def multiDDHIdealTupleLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d) × ZMod (F.order d))).map fun B i =>
    ((B i).1 • F.generator d, (B i).2 • F.generator d)

/-- Multi-DDH (I) rerandomization ([BonehShoup2023], Exercise 10.11, p. 426): given a single
candidate DDH triple `(u, v, w)`, draw independent `(σ i, τ i) ← ZMod q × ZMod q` for each `i : ι`
and output `i ↦ ddhFixedURerandomize d u v w (σ i) (τ i)`. -/
noncomputable def multiDDHRerandomizeLaw (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u v w : F.Carrier d) : PMF (ι → F.Carrier d × F.Carrier d) :=
  (PMF.uniformOfFintype (ι → ZMod (F.order d) × ZMod (F.order d))).map fun r i =>
    F.ddhFixedURerandomize d u v w (r i).1 (r i).2

private def ddhRerandomizeRealTupleEquiv {q : ℕ} (ι : Type*) (β : ZMod q) :
    (ι → ZMod q × ZMod q) ≃ ((ι → ZMod q) × (ι → ZMod q)) where
  toFun r := (fun i => (r i).1 + (r i).2 * β, fun i => (r i).2)
  invFun p i := (p.1 i - p.2 i * β, p.2 i)
  left_inv r := by ext i <;> simp
  right_inv p := by ext i <;> simp

private def ddhRerandomizeRealCoordEquiv {q : ℕ} (β : ZMod q) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun p := (p.1 + p.2 * β, p.2)
  invFun p := (p.1 - p.2 * β, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private def ddhRerandomizeSecondCoordEquiv {q : ℕ} [Fact (Nat.Prime q)]
    {α β γ : ZMod q} (hγ : γ ≠ α * β) :
    (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun p := (p.1, α * p.1 + p.2 * (γ - α * β))
  invFun p := (p.1, (p.2 - α * p.1) * (γ - α * β)⁻¹)
  left_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · rfl
    · dsimp; rw [add_sub_cancel_left, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  right_inv p := by
    have hne : γ - α * β ≠ 0 := sub_ne_zero.mpr hγ
    ext
    · rfl
    · dsimp; rw [mul_assoc, inv_mul_cancel₀ hne, mul_one, add_sub_cancel]

/-- On any real DDH triple `(α • g, β • g, (α * β) • g)`, `multiDDHRerandomizeLaw` produces
`multiDDHRealTupleLaw d ι α` ([BonehShoup2023], Exercise 10.11). -/
theorem multiDDHRerandomizeLaw_real (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α β : ZMod (F.order d)) :
    F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
      ((α * β) • F.generator d) = F.multiDDHRealTupleLaw d ι α := by
  let e : (ι → ZMod (F.order d) × ZMod (F.order d)) ≃
      ((ι → ZMod (F.order d)) × (ι → ZMod (F.order d))) :=
    ddhRerandomizeRealTupleEquiv ι β
  rw [multiDDHRealTupleLaw,
    ← PMF.uniformOfFintype_prod_map_fst (α := ι → ZMod (F.order d)) (β := ι → ZMod (F.order d)),
    ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp, PMF.map_comp,
    multiDDHRerandomizeLaw]
  congr 1; funext r; funext i
  simp [e, ddhRerandomizeRealTupleEquiv, ddhFixedURerandomize_smul_generator]

/-- On any non-DDH triple `(α • g, β • g, γ • g)` with `γ ≠ α * β`, `multiDDHRerandomizeLaw`
produces `multiDDHIdealTupleLaw d ι` ([BonehShoup2023], Exercise 10.11). -/
theorem multiDDHRerandomizeLaw_ideal (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    {α β γ : ZMod (F.order d)} (hγ : γ ≠ α * β) :
    F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d) (γ • F.generator d) =
      F.multiDDHIdealTupleLaw d ι := by
  let e : (ι → ZMod (F.order d) × ZMod (F.order d)) ≃
      (ι → ZMod (F.order d) × ZMod (F.order d)) :=
    Equiv.piCongrRight fun _ =>
      (ddhRerandomizeRealCoordEquiv β).trans (ddhRerandomizeSecondCoordEquiv hγ)
  rw [multiDDHIdealTupleLaw, ← PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
    multiDDHRerandomizeLaw]
  congr 1; funext r; funext i
  simp [e, ddhRerandomizeRealCoordEquiv, ddhRerandomizeSecondCoordEquiv,
    ddhFixedURerandomize_smul_generator]

/-- If a family of games `g : α → Game` agrees with `p : Game` on every `a ≠ a₀`, then averaging
`g` over `PMF.uniformOfFintype α` is within `(Fintype.card α)⁻¹` of `p`. -/
private theorem advantage_bind_uniformOfFintype_of_ne_le {α : Type*} [Fintype α] [Nonempty α]
    (a₀ : α) (g : α → Game) (p : Game) (hne : ∀ a, a ≠ a₀ → g a = p) :
    Game.advantage ((PMF.uniformOfFintype α).bind g) p ≤ (Fintype.card α : ℝ≥0)⁻¹ := by
  classical
  have hsingle :
      ((PMF.uniformOfFintype α).bind fun a => PMF.pure (decide (a = a₀))) true =
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply, tsum_fintype]
    simp [PMF.uniformOfFintype_apply, PMF.pure_apply, eq_comm (a := true)]
  have hle₁ :
      ((PMF.uniformOfFintype α).bind g) true ≤ p true + (Fintype.card α : ℝ≥0∞)⁻¹ := by
    rw [← PMF.bind_const (PMF.uniformOfFintype α) p, ← hsingle, PMF.bind_apply, PMF.bind_apply,
      PMF.bind_apply, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases ha : a = a₀
    · simp only [ha, decide_true, PMF.pure_apply, ↓reduceIte]
      exact (PMF.coe_le_one _ _).trans le_add_self
    · simp [hne a ha, ha]
  have hle₂ :
      p true ≤ ((PMF.uniformOfFintype α).bind g) true + (Fintype.card α : ℝ≥0∞)⁻¹ := by
    nth_rw 1 [← PMF.bind_const (PMF.uniformOfFintype α) p]
    rw [← hsingle, PMF.bind_apply, PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    by_cases ha : a = a₀
    · simp only [ha, decide_true, PMF.pure_apply, ↓reduceIte]
      exact (PMF.coe_le_one _ _).trans le_add_self
    · simp [hne a ha, ha]
  have hinv_ne_top : (Fintype.card α : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hadv := Game.advantage_le_of_apply_le hinv_ne_top hle₁ hle₂
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, ← NNReal.coe_natCast, ← NNReal.coe_inv] at hadv
  exact NNReal.coe_le_coe.mp hadv

/-- **Boneh–Shoup Exercise 10.11 ($n = 1$ Multi-DDH (I), p. 426)**: for a single shared secret `α`,
any finite index type `ι` (`|ι|` pairs), and any test
`test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool`, the advantage between
`(α • g, multiDDHRealTupleLaw d ι α)` and `(α • g, multiDDHIdealTupleLaw d ι)` is at most the DDH
advantage of the rerandomizing wrapper `multiDDHRerandomizeLaw` (which samples `|ι|` pairs) plus
`(F.order d)⁻¹`. -/
theorem advantage_multiDDH_le (d : F.Desc) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (test : F.Carrier d → (ι → F.Carrier d × F.Carrier d) → PMF Bool) :
    Game.advantage
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) ≤
    Game.advantage
      ((F.ddhRealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1))
      ((F.ddhIdealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) +
      (F.order d : ℝ≥0)⁻¹ := by
  have hreal :
      ((F.ddhRealTupleLaw d).bind fun t =>
        (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) =
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (F.multiDDHRealTupleLaw d ι α).bind (test (α • F.generator d))) := by
    simp only [ddhRealTupleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind, multiDDHRerandomizeLaw_real, PMF.bind_const]
  rw [← hreal]
  refine (Game.advantage_triangle _
    ((F.ddhIdealTupleLaw d).bind fun t =>
      (F.multiDDHRerandomizeLaw d ι t.1 t.2.1 t.2.2).bind (test t.1)) _).trans ?_
  refine add_le_add le_rfl ?_
  simp only [ddhIdealTupleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind]
  -- Bound the advantage inside the outer `α, β` averages using `Game.advantage_bind_le`.
  have hpoint (α β : ZMod (F.order d)) :
      (Game.advantage
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
          (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
            (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) : ℝ) ≤
      (((F.order d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) := by
    refine NNReal.coe_le_coe.mpr ?_
    simpa only [ZMod.card] using
      advantage_bind_uniformOfFintype_of_ne_le (α * β)
        (fun γ => (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
          (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d)))
        (fun γ hγ => by rw [F.multiDDHRerandomizeLaw_ideal d ι hγ])
  have hβ (α : ZMod (F.order d)) :
      (Game.advantage
        ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            (F.multiDDHRerandomizeLaw d ι (α • F.generator d) (β • F.generator d)
              (γ • F.generator d)).bind (test (α • F.generator d)))
        ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d))) : ℝ) ≤
      (((F.order d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) := by
    rw [← PMF.bind_const (PMF.uniformOfFintype (ZMod (F.order d)))
      ((F.multiDDHIdealTupleLaw d ι).bind (test (α • F.generator d)))]
    exact Game.advantage_bind_le _ _ _ (hpoint α)
  exact NNReal.coe_le_coe.mp (Game.advantage_bind_le _ _ _ hβ)

/-! ### Naor–Reingold PRF prefix hybrids and security reduction (Exercise 10.4(b)) -/

/-- The `k`-bit prefix of an `n`-bit string `x : BitString n`, padded with `false` if `j ≥ n`. -/
def naorReingoldTakePrefix {n : ℕ} (k : ℕ) (x : BitString n) : BitString k :=
  fun j => if h : j.1 < n then x ⟨j.1, h⟩ else false

@[simp]
theorem naorReingoldTakePrefix_self {n : ℕ} (x : BitString n) :
    naorReingoldTakePrefix n x = x := by
  funext j
  simp [naorReingoldTakePrefix, j.isLt]

@[simp]
theorem init_naorReingoldTakePrefix_succ {n k : ℕ} (x : BitString n) :
    Fin.init (naorReingoldTakePrefix (k + 1) x) = naorReingoldTakePrefix k x := by
  funext j
  simp [Fin.init, naorReingoldTakePrefix]

@[simp]
theorem last_naorReingoldTakePrefix_succ {n k : ℕ} (hk : k < n) (x : BitString n) :
    naorReingoldTakePrefix (k + 1) x (Fin.last k) = x ⟨k, hk⟩ := by
  simp [Fin.last, naorReingoldTakePrefix, hk]

/-- Suffix exponent product `∏ i : Fin n, if k ≤ i.1 ∧ x i then α i else 1` from depth `k` to `n`.
-/
def naorReingoldSuffixExp (d : F.Desc) {n : ℕ} (k : ℕ)
    (α : Fin n → ZMod (F.order d)) (x : BitString n) : ZMod (F.order d) :=
  ∏ i : Fin n, if k ≤ i.1 ∧ x i then α i else 1

@[simp]
theorem naorReingoldSuffixExp_zero (d : F.Desc) {n : ℕ}
    (α₀ : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    α₀ * F.naorReingoldSuffixExp d 0 α x = F.naorReingoldExp d α₀ α x := by
  simp [naorReingoldSuffixExp, naorReingoldExp]

@[simp]
theorem naorReingoldSuffixExp_self (d : F.Desc) {n : ℕ}
    (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d n α x = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  simp [Nat.not_le.mpr i.isLt]

/-- Splitting `naorReingoldSuffixExp` at depth `k < n` into the `k`-th bit factor and the depth
`k + 1` suffix. -/
theorem naorReingoldSuffixExp_eq_mul_succ (d : F.Desc) {n k : ℕ} (hk : k < n)
    (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d k α x =
      (if x ⟨k, hk⟩ then α ⟨k, hk⟩ else 1) * F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
  congr 1
  · simp
  · symm
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
    simp only [Nat.add_one_le_iff, lt_self_iff_false, false_and, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i.1 ≠ k := by
      intro heq
      exact (Finset.mem_erase.mp hi).1 (Fin.ext heq)
    by_cases hlt : k < i.1
    · simp [hlt, Nat.le_of_lt hlt]
    · have hnotle : ¬k ≤ i.1 := fun hle => hlt (Nat.lt_of_le_of_ne hle hne.symm)
      simp [hlt, hnotle]

/-- Updating `α` at `⟨k, hk⟩` does not affect `naorReingoldSuffixExp` at depth `k + 1`. -/
theorem naorReingoldSuffixExp_succ_update (d : F.Desc) {n k : ℕ} (hk : k < n)
    (α : Fin n → ZMod (F.order d)) (a : ZMod (F.order d)) (x : BitString n) :
    F.naorReingoldSuffixExp d (k + 1) (Function.update α ⟨k, hk⟩ a) x =
      F.naorReingoldSuffixExp d (k + 1) α x := by
  unfold naorReingoldSuffixExp
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : k + 1 ≤ i.1
  · have hne : i ≠ ⟨k, hk⟩ := by
      intro heq
      have hval : i.1 = k := congrArg Fin.val heq
      omega
    simp [hne]
  · simp [h]

/-- Hybrid function at depth `k`: look up the `k`-bit prefix in `B : BitString k → ZMod (F.order d)`
and multiply by the remaining suffix exponent product from `k` to `n`. -/
def naorReingoldHybridEval (d : F.Desc) {n : ℕ} (k : ℕ)
    (B : BitString k → ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) (x : BitString n) :
    F.Carrier d :=
  (B (naorReingoldTakePrefix k x) * F.naorReingoldSuffixExp d k α x) • F.generator d

/-- Run an adaptive oracle distinguisher `adv` against a deterministic function
`fn : BitString n → F.Carrier d`. -/
noncomputable def naorReingoldEvalWithFn (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool)
    (fn : BitString n → F.Carrier d) : PMF Bool :=
  OracleComp.interpret (fun x => PMF.pure (fn x)) adv

/-- The real Naor–Reingold PRF experiment at group `d` and input length `n`
([BonehShoup2023], Section 10.11, Exercise 10.4, p. 424). -/
noncomputable def naorReingoldRealGame (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) : Game := do
  let α₀ ← PMF.uniformOfFintype (ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin n → ZMod (F.order d))
  F.naorReingoldEvalWithFn d n adv (F.naorReingoldEval d α₀ α)

/-- The ideal random-function experiment at group `d` and input length `n`: a uniformly random
function `BitString n → F.Carrier d` represented via
`B ← PMF.uniformOfFintype (BitString n → ZMod (F.order d))` and the bijection `β ↦ β • g`. -/
noncomputable def naorReingoldIdealGame (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) : Game := do
  let B ← PMF.uniformOfFintype (BitString n → ZMod (F.order d))
  F.naorReingoldEvalWithFn d n adv (fun x => B x • F.generator d)

/-- The depth-`k` Naor–Reingold prefix-hybrid experiment ($0 \le k \le n$): queries share a
uniform random function `B : BitString k → ZMod (F.order d)` on `k`-bit prefixes and evaluate the
remaining suffix bits with `α : Fin n → ZMod (F.order d)`
([BonehShoup2023], Exercise 10.4 & Exercise 4.18). -/
noncomputable def naorReingoldHybridGame (d : F.Desc) (n k : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) : Game := do
  let B ← PMF.uniformOfFintype (BitString k → ZMod (F.order d))
  let α ← PMF.uniformOfFintype (Fin n → ZMod (F.order d))
  F.naorReingoldEvalWithFn d n adv (F.naorReingoldHybridEval d k B α)

/-- At depth `0`, `naorReingoldHybridGame` is the real Naor–Reingold PRF experiment. -/
@[simp]
theorem naorReingoldHybridGame_zero (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    F.naorReingoldHybridGame d n 0 adv = F.naorReingoldRealGame d n adv := by
  let e : ZMod (F.order d) ≃ (BitString 0 → ZMod (F.order d)) :=
    (Equiv.funUnique (BitString 0) (ZMod (F.order d))).symm
  simp only [naorReingoldHybridGame, naorReingoldRealGame, PMF.monad_bind_eq_bind]
  rw [← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  congr 1; funext α₀
  dsimp only [Function.comp_apply]
  congr 1; funext α
  congr 1; funext x
  simp [naorReingoldHybridEval, naorReingoldEval, e]

/-- At depth `n`, `naorReingoldHybridGame` is the ideal random-function experiment. -/
@[simp]
theorem naorReingoldHybridGame_self (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    F.naorReingoldHybridGame d n n adv = F.naorReingoldIdealGame d n adv := by
  simp only [naorReingoldHybridGame, naorReingoldIdealGame, PMF.monad_bind_eq_bind]
  congr 1; funext B
  have hfn (α : Fin n → ZMod (F.order d)) :
      F.naorReingoldHybridEval d n B α = fun x => B x • F.generator d := by
    funext x
    simp [naorReingoldHybridEval]
  simp_rw [hfn, PMF.bind_const]

private def boolProdEquiv (α : Type*) : (α × α) ≃ (Bool → α) where
  toFun p b := if b then p.2 else p.1
  invFun f := (f false, f true)
  left_inv p := by simp
  right_inv f := by funext b; cases b <;> rfl

private def prefixTableEquiv (α : Type*) (k : ℕ) :
    (BitString k → α × α) ≃ (BitString (k + 1) → α) :=
  ((Equiv.piCongrRight fun _ : BitString k => boolProdEquiv α).trans
    (Equiv.curry (BitString k) Bool α).symm).trans
    (Equiv.arrowCongr
      ((Fin.snocEquiv fun _ : Fin (k + 1) => Bool).symm.trans (Equiv.prodComm _ _)).symm
      (Equiv.refl α))

private theorem prefixTableEquiv_apply {α : Type*} (k : ℕ) (T : BitString k → α × α)
    (p : BitString (k + 1)) :
    prefixTableEquiv α k T p = if p (Fin.last k) then (T (Fin.init p)).2 else (T (Fin.init p)).1 :=
  rfl

private def shiftAtEquiv {n : ℕ} {α : Type*} [AddGroup α] (i : Fin n) (δ : α) :
    (Fin n → α) ≃ (Fin n → α) where
  toFun f := Function.update f i (f i + δ)
  invFun f := Function.update f i (f i - δ)
  left_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  right_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

private theorem uniformOfFintype_bind_update {n : ℕ} {α β : Type*}
    [AddGroup α] [Fintype α] [Nonempty α] (i : Fin n) (g : (Fin n → α) → PMF β) :
    ((PMF.uniformOfFintype α).bind fun a =>
      (PMF.uniformOfFintype (Fin n → α)).bind fun f =>
        g (Function.update f i a)) =
    (PMF.uniformOfFintype (Fin n → α)).bind g := by
  rw [PMF.bind_comm]
  have h1 (f : Fin n → α) :
      ((PMF.uniformOfFintype α).bind fun a => g (Function.update f i a)) =
      ((PMF.uniformOfFintype α).bind fun δ => g (shiftAtEquiv i δ f)) :=
    (uniformOfFintype_bind_equiv (Equiv.addLeft (f i))
      (fun a => g (Function.update f i a))).symm
  simp_rw [h1]
  rw [PMF.bind_comm]
  have h2 (δ : α) :
      ((PMF.uniformOfFintype (Fin n → α)).bind fun f => g (shiftAtEquiv i δ f)) =
      (PMF.uniformOfFintype (Fin n → α)).bind g :=
    uniformOfFintype_bind_equiv (shiftAtEquiv i δ) g
  simp_rw [h2, PMF.bind_const]

/-- Evaluating the level-`k` child table `T : BitString k → F.Carrier d × F.Carrier d` followed by
the depth-`(k + 1)` suffix exponent product. -/
def naorReingoldTableEval (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (T : BitString k → F.Carrier d × F.Carrier d) (α : Fin n → ZMod (F.order d))
    (x : BitString n) : F.Carrier d :=
  F.naorReingoldSuffixExp d (k + 1) α x •
    if x ⟨k, hk⟩ then (T (naorReingoldTakePrefix k x)).2 else (T (naorReingoldTakePrefix k x)).1

/-- Level-`k` Multi-DDH test induced by a Naor–Reingold PRF adversary `adv`: draw suffix exponents
`α ← PMF.uniformOfFintype (Fin n → ZMod (F.order d))` and run `adv` against
`naorReingoldTableEval`. -/
noncomputable def naorReingoldLevelTest (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool)
    (_u : F.Carrier d) (T : BitString k → F.Carrier d × F.Carrier d) : PMF Bool := do
  let α ← PMF.uniformOfFintype (Fin n → ZMod (F.order d))
  F.naorReingoldEvalWithFn d n adv (F.naorReingoldTableEval d k hk T α)

/-- Single-level DDH distinguisher at depth `k < n`: given a candidate DDH triple `(u, v, w)`,
rerandomize it into a `BitString k`-indexed family via `multiDDHRerandomizeLaw` and run
`naorReingoldLevelTest`. -/
noncomputable def naorReingoldLevelDDHDistinguisher (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool)
    (t : F.Carrier d × F.Carrier d × F.Carrier d) : PMF Bool :=
  (F.multiDDHRerandomizeLaw d (BitString k) t.1 t.2.1 t.2.2).bind
    (F.naorReingoldLevelTest d k hk adv t.1)

/-- Under `multiDDHRealTupleLaw`, `naorReingoldLevelTest` reproduces `naorReingoldHybridGame` at
depth `k`. -/
theorem multiDDHRealTupleLaw_naorReingoldLevelTest (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHRealTupleLaw d (BitString k) α_k).bind
        (F.naorReingoldLevelTest d k hk adv (α_k • F.generator d))) =
      F.naorReingoldHybridGame d n k adv := by
  unfold naorReingoldLevelTest
  simp only [multiDDHRealTupleLaw, naorReingoldHybridGame, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))
    (PMF.uniformOfFintype (BitString k → ZMod (F.order d)))]
  congr 1; funext B
  have hfn (α_k : ZMod (F.order d)) (α : Fin n → ZMod (F.order d)) :
      F.naorReingoldTableEval d k hk
        (fun i => (B i • F.generator d, (α_k * B i) • F.generator d)) α =
      F.naorReingoldHybridEval d k B (Function.update α ⟨k, hk⟩ α_k) := by
    funext x
    rw [naorReingoldTableEval, naorReingoldHybridEval,
      F.naorReingoldSuffixExp_eq_mul_succ d hk (Function.update α ⟨k, hk⟩ α_k) x,
      F.naorReingoldSuffixExp_succ_update d hk α α_k x]
    simp only [Function.update_self]
    rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk
    · simp only [hxk, ↓reduceIte, smul_smul]
      exact congrArg (· • F.generator d) (by ring)
    · simp [hxk, smul_smul, mul_comm]
  simp_rw [hfn]
  exact uniformOfFintype_bind_update ⟨k, hk⟩
    (fun α => F.naorReingoldEvalWithFn d n adv (F.naorReingoldHybridEval d k B α))

/-- Under `multiDDHIdealTupleLaw`, `naorReingoldLevelTest` reproduces `naorReingoldHybridGame` at
depth `k + 1`. -/
theorem multiDDHIdealTupleLaw_naorReingoldLevelTest (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α_k =>
      (F.multiDDHIdealTupleLaw d (BitString k)).bind
        (F.naorReingoldLevelTest d k hk adv (α_k • F.generator d))) =
      F.naorReingoldHybridGame d n (k + 1) adv := by
  unfold naorReingoldLevelTest
  rw [PMF.bind_const]
  simp only [multiDDHIdealTupleLaw, naorReingoldHybridGame, PMF.monad_bind_eq_bind, PMF.bind_map,
    Function.comp_def]
  rw [← PMF.uniformOfFintype_map_equiv (prefixTableEquiv (ZMod (F.order d)) k), PMF.bind_map]
  congr 1; funext B
  dsimp only [Function.comp_apply]
  congr 1; funext α
  congr 1; funext x
  rw [naorReingoldTableEval, naorReingoldHybridEval]
  have hpref : prefixTableEquiv (ZMod (F.order d)) k B (naorReingoldTakePrefix (k + 1) x) =
      if x ⟨k, hk⟩ then (B (naorReingoldTakePrefix k x)).2
      else (B (naorReingoldTakePrefix k x)).1 := by
    rw [prefixTableEquiv_apply, init_naorReingoldTakePrefix_succ,
      last_naorReingoldTakePrefix_succ hk]
  rw [hpref]
  rcases Bool.eq_false_or_eq_true (x ⟨k, hk⟩) with hxk | hxk <;>
    simp [hxk, smul_smul, mul_comm]

/-- **Single-level Naor–Reingold prefix-hybrid bound**: for every `k < n`, the advantage between
`naorReingoldHybridGame` at depth `k` and depth `k + 1` is at most the DDH distinguishing advantage
of `naorReingoldLevelDDHDistinguisher d k hk adv` plus `(F.order d)⁻¹`. -/
theorem advantage_naorReingoldHybridGame_succ_le (d : F.Desc) {n : ℕ} (k : ℕ) (hk : k < n)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    Game.advantage (F.naorReingoldHybridGame d n k adv)
      (F.naorReingoldHybridGame d n (k + 1) adv) ≤
    Game.advantage
      ((F.ddhRealTupleLaw d).bind (F.naorReingoldLevelDDHDistinguisher d k hk adv))
      ((F.ddhIdealTupleLaw d).bind (F.naorReingoldLevelDDHDistinguisher d k hk adv)) +
      (F.order d : ℝ≥0)⁻¹ := by
  rw [← F.multiDDHRealTupleLaw_naorReingoldLevelTest d k hk adv,
    ← F.multiDDHIdealTupleLaw_naorReingoldLevelTest d k hk adv]
  exact F.advantage_multiDDH_le d (BitString k) (F.naorReingoldLevelTest d k hk adv)

/-- Total- parameterized level DDH distinguisher (returning `PMF.pure false` when `k ≥ n`). -/
noncomputable def naorReingoldHopDDHDistinguisher (d : F.Desc) (n k : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool)
    (t : F.Carrier d × F.Carrier d × F.Carrier d) : PMF Bool :=
  if hk : k < n then F.naorReingoldLevelDDHDistinguisher d k hk adv t else PMF.pure false

/-- **Naor–Reingold PRF distributional prefix-hybrid bound (`∑ k < n` bound,
[BonehShoup2023], Exercise 10.4; [NaorReingold2004], Theorem 4.1)**: the distinguishing advantage
between `naorReingoldRealGame` and `naorReingoldIdealGame` is bounded by the sum over
`k ∈ Finset.range n` of the DDH distinguishing advantages of the explicit `2^k`-pair PMF
distinguisher `naorReingoldLevelDDHDistinguisher` (`naorReingoldHopDDHDistinguisher`) plus
`n * (F.order d)⁻¹`. The efficient lazy-sampling reduction (`IsOraclePPT` /
`PseudorandomFunction` bridge) remains open in #1093. -/
theorem advantage_naorReingold_le_sum (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) :
    Game.advantage (F.naorReingoldRealGame d n adv) (F.naorReingoldIdealGame d n adv) ≤
      (∑ k ∈ Finset.range n,
        Game.advantage
          ((F.ddhRealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))
          ((F.ddhIdealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))) +
        n * (F.order d : ℝ≥0)⁻¹ := by
  rw [← F.naorReingoldHybridGame_zero d n adv, ← F.naorReingoldHybridGame_self d n adv]
  refine (Game.advantage_hybrid_le_sum (F.naorReingoldHybridGame d n · adv) n).trans ?_
  have hsum :
      (∑ k ∈ Finset.range n,
        (Game.advantage
          ((F.ddhRealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))
          ((F.ddhIdealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv)) +
          (F.order d : ℝ≥0)⁻¹)) =
      (∑ k ∈ Finset.range n,
        Game.advantage
          ((F.ddhRealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))
          ((F.ddhIdealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))) +
        n * (F.order d : ℝ≥0)⁻¹ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hsum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hlt : k < n := Finset.mem_range.mp hk
  have heq : F.naorReingoldHopDDHDistinguisher d n k adv =
      F.naorReingoldLevelDDHDistinguisher d k hlt adv := by
    funext t
    simp [naorReingoldHopDDHDistinguisher, hlt]
  rw [heq]
  exact F.advantage_naorReingoldHybridGame_succ_le d k hlt adv

/-- **Common-bound Naor–Reingold PRF distributional prefix-hybrid bound**
([BonehShoup2023], Exercise 10.4; [NaorReingold2004], Theorem 4.1): if for every `k < n` the
explicit `2^k`-pair PMF distinguisher `naorReingoldHopDDHDistinguisher d n k adv` has DDH advantage
at most `ε`, then the Naor–Reingold PRF advantage is at most `n * (ε + (F.order d)⁻¹)`. The
efficient lazy-sampling reduction (`IsOraclePPT` / `PseudorandomFunction` bridge) remains open in
#1093. -/
theorem advantage_naorReingold_le_mul (d : F.Desc) (n : ℕ)
    (adv : OracleComp (fun _ : BitString n => F.Carrier d) Bool) (ε : ℝ≥0)
    (hε : ∀ k < n,
      Game.advantage
        ((F.ddhRealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv))
        ((F.ddhIdealTupleLaw d).bind (F.naorReingoldHopDDHDistinguisher d n k adv)) ≤ ε) :
    Game.advantage (F.naorReingoldRealGame d n adv) (F.naorReingoldIdealGame d n adv) ≤
      n * (ε + (F.order d : ℝ≥0)⁻¹) := by
  rw [← F.naorReingoldHybridGame_zero d n adv, ← F.naorReingoldHybridGame_self d n adv]
  refine Game.advantage_hybrid_le (F.naorReingoldHybridGame d n · adv) n
    (ε + (F.order d : ℝ≥0)⁻¹) fun k hk => ?_
  have heq : F.naorReingoldHopDDHDistinguisher d n k adv =
      F.naorReingoldLevelDDHDistinguisher d k hk adv := by
    funext t
    simp [naorReingoldHopDDHDistinguisher, hk]
  refine (F.advantage_naorReingoldHybridGame_succ_le d k hk adv).trans ?_
  rw [← heq]
  exact add_le_add (hε k hk) le_rfl

end Cslib.Crypto.PrimeOrderGroupFamily
