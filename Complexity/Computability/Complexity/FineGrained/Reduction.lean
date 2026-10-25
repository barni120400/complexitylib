/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Sparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-!
# Reductions of linear size

Exponential time bounds in a parameter of the instance transfer along polynomial-time reductions
that increase the parameter at most linearly. If `f` reduces `A` to `B` in polynomial time and
`μB (f a) ≤ c μA a + c`, then a decider for `B` within time `2 ^ (δ μB b)` times a polynomial in
the length of the encoded instance gives a decider for `A` within time `2 ^ (c δ μA a)` times a
polynomial (`Cslib.Complexity.DecidableInExpTime.of_reduction`): run the reduction, then the
decider. The polynomial absorbs the running time of the reduction and the length of its output.
Hence subexponential time in `μB` gives subexponential time in `μA`
(`Cslib.Complexity.DecidableInSubexpTime.of_reduction`).

More generally, subexponential time transfers along:
* **$2^{O(m(a))}$-time reductions** (`Cslib.Complexity.DecidableInSubexpTime.of_expReduction`),
  where the target measure is bounded linearly in $m(a) \log_2 m(a)$ and the $2^{O(m(a))}$ runtime
  is absorbed into $2^{(\varepsilon / 2) m(a) \log_2 m(a)}$ via
  `Cslib.Complexity.mul_le_pow_add_mul_log`;
* **exhaustive-search reductions** (`Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`,
  `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`), where an instance $a \in A$ reduces
  to a disjunction over $2^{\nu(a)}$ polynomial-time branches $f(a, r) \in B$ with sublinear branch
  exponent $\nu(a) = o(\mu_A(a))$.

Under the exponential time hypothesis, 3SAT is not decidable in subexponential time in the number
of clauses (`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`, by the sparsification
lemma). So a polynomial-time reduction from 3SAT whose output measure is linear in the number of
clauses shows that the target problem is not decidable in subexponential time in that measure
(`Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`)
[ImpagliazzoPaturiZane2001] [CyganEtAl2015, Chapter 14]. Lower bounds for larger measures are
stronger: a lower bound for a measure gives one for every measure at most linear in it
(`Cslib.Complexity.DecidableInSubexpTime.mono_measure`).

## Main results

* `Cslib.Complexity.DecidableInExpTime.mono_measure`,
  `Cslib.Complexity.DecidableInSubexpTime.mono_measure`: changing the measure.
* `Cslib.Complexity.DecidableInExpTime.of_reduction`,
  `Cslib.Complexity.DecidableInSubexpTime.of_reduction`: transfer along reductions of linear
  size.
* `Cslib.Complexity.mul_le_pow_add_mul_log`: absorbing $C \cdot n$ into
  $(\varepsilon / 2) \cdot n \log_2 n$ plus a constant.
* `Cslib.Complexity.DecidableInSubexpTime.of_expReduction`: subexponential-time transfer along
  $2^{O(m)}$-time reductions into parameter $m \log_2 m$.
* `Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`,
  `Cslib.Complexity.DecidableInSubexpTime.of_exhaustiveSearch`: exponential and subexponential
  time transfer along exhaustive-search reductions.
* `Cslib.Complexity.ETH.not_decidableInSubexpTime_of_reduction`: lower bounds from the exponential
  time hypothesis through reductions of linear size from 3SAT.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Changing the measure -/

section Measure

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α} {μ μ' : α → ℕ}

/-- A decider within time `2 ^ (δ μ a)` times a polynomial, for a measure `μ ≤ c μ' + c`, decides
within time `2 ^ (c δ μ' a)` times a polynomial. -/
theorem DecidableInExpTime.mono_measure {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : DecidableInExpTime A enc μ δ) : DecidableInExpTime A enc μ' (c * δ) := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, h.mono ⌈(2 : ℝ) ^ (δ * c)⌉₊ (fun a => ?_) fun a => by positivity⟩
  have hK : (2 : ℝ) ^ (δ * c) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ := Nat.le_ceil _
  have h₁ : (2 : ℝ) ^ (δ * μ a) ≤ 2 ^ (δ * c) * 2 ^ (c * δ * μ' a) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (μ a : ℝ) ≤ c * μ' a + c := by exact_mod_cast hμ a
    nlinarith
  have h₂ : (2 : ℝ) ^ (δ * μ a) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ * 2 ^ (c * δ * μ' a) :=
    h₁.trans (mul_le_mul_of_nonneg_right hK (by positivity))
  have h₃ := mul_le_mul_of_nonneg_right h₂ (by positivity :
    (0 : ℝ) ≤ ((enc a).length + 1) ^ e)
  have h₄ : (0 : ℝ) ≤ ⌈(2 : ℝ) ^ (δ * c)⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- Subexponential time in a measure `μ ≤ c μ' + c` gives subexponential time in `μ'`. So a lower
bound for `μ'` gives the lower bound for `μ`. -/
theorem DecidableInSubexpTime.mono_measure {c : ℕ} (hμ : ∀ a, μ a ≤ c * μ' a + c)
    (h : DecidableInSubexpTime A enc μ) : DecidableInSubexpTime A enc μ' := by
  intro δ hδ
  refine ((h (δ / (c + 1)) (by positivity)).mono_measure hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end Measure

/-! ### Reductions -/

section Reduction

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}
  {μA : α → ℕ} {μB : β → ℕ}

/-- **Transfer along reductions of linear size.** If `f` reduces `A` to `B` in polynomial time
with `μB (f a) ≤ c μA a + c`, then a decider for `B` within time `2 ^ (δ μB b)` times a polynomial
in the length of the encoded instance gives a decider for `A` within time `2 ^ (c δ μA a)` times a
polynomial. -/
theorem DecidableInExpTime.of_reduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * μA a + c) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime B encB μB δ) : DecidableInExpTime A encA μA (c * δ) := by
  have hf := hf.tidy
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k, hg, hgB, ht⟩ := h.exists_computableInO
  have hg := hg.tidy
  obtain ⟨d, _, hf⟩ := hf.exists_degree
  have hfO := hf.inO
  obtain ⟨l, hl⟩ := hfO.length_le_time
  set K : ℝ := 1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k
  refine Complexity.DecidableInExpTime.of_computableInO (.of_tidy (hg.comp hfO))
    (fun a => (hfA a).trans (hgB (f a)))
    ⌈K⌉₊ (d * e + d) fun a => ?_
  show _ ≤ _
  set P : ℝ := ((encA a).length + 1) ^ d
  set X : ℝ := 2 ^ (c * δ * μA a)
  have hP : 1 ≤ P := one_le_pow₀ (by linarith [(Nat.cast_nonneg (encA a).length : (0 : ℝ) ≤ _)])
  have hX : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  -- the output of the reduction has length at most `2 l P`
  have hlen : ((encB (f a)).length : ℝ) + 1 ≤ (2 * l + 1) * P := by
    have : ((encB (f a)).length : ℝ) ≤ l * (P + 1) := by
      have := hl a
      simp only [P]
      exact_mod_cast this
    nlinarith
  -- the exponential factor
  have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤ 2 ^ (δ * c) * X := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (μB (f a) : ℝ) ≤ c * μA a + c := by exact_mod_cast hμ a
    nlinarith
  -- the decider on the reduced instance
  have hpow : (((encB (f a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlen e
  have ht' : (t (f a) : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e) * (X * P ^ e) + k := by
    refine (ht (f a)).trans ?_
    have := mul_le_mul hexp hpow (by positivity) (by positivity)
    nlinarith
  have hPe : P ^ e ≤ P ^ (e + 1) := pow_le_pow_right₀ hP (Nat.le_succ e)
  have hP1 : P ≤ P ^ (e + 1) := le_self_pow₀ hP (Nat.succ_ne_zero e)
  have hXP : 1 ≤ X * P ^ (e + 1) := one_le_mul_of_one_le_of_one_le hX (one_le_pow₀ hP)
  have hgoal : P + (t (f a) : ℝ) ≤ K * (X * P ^ (e + 1)) := by
    have h₁ : P ≤ X * P ^ (e + 1) := hP1.trans (le_mul_of_one_le_left (by positivity) hX)
    have h₂ : X * P ^ e ≤ X * P ^ (e + 1) := mul_le_mul_of_nonneg_left hPe (by positivity)
    have h₃ := mul_le_mul_of_nonneg_left h₂
      (by positivity : (0 : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e))
    have h₄ := mul_le_mul_of_nonneg_left hXP hk
    simp only [K]
    nlinarith
  have hPow : X * P ^ (e + 1) = X * (((encA a).length : ℝ) + 1) ^ (d * e + d) := by
    simp only [P, ← pow_mul]
    ring_nf
  have hK : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  push_cast
  calc P + (t (f a) : ℝ) ≤ K * (X * P ^ (e + 1)) := hgoal
    _ ≤ ⌈K⌉₊ * (X * P ^ (e + 1)) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = ⌈K⌉₊ * (X * (((encA a).length : ℝ) + 1) ^ (d * e + d)) := by rw [hPow]

/-- **Transfer along reductions of linear size.** If `f` reduces `A` to `B` in polynomial time
with `μB (f a) ≤ c μA a + c`, and `B` is decidable in subexponential time in `μB`, then `A` is
decidable in subexponential time in `μA`. -/
theorem DecidableInSubexpTime.of_reduction {f : α → β}
    (hf : ComputableInPolyTime f encA encB) (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * μA a + c) (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro δ hδ
  refine ((h (δ / (c + 1)) (by positivity)).of_reduction hf hfA hμ (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- **Lower bounds from the exponential time hypothesis** [ImpagliazzoPaturiZane2001]
[CyganEtAl2015, Chapter 14]. Under `ETH`, if `f` is computable in polynomial time and, on formulas
`φ` in conjunctive normal form with `m` clauses of at most three literals, maps `φ` to an instance
of `B` exactly when `φ` is satisfiable, with `μB (f φ) ≤ k m + k`, then `B` is not decidable in
subexponential time in `μB`: for some `δ > 0`, no decider runs within time `2 ^ (δ μB b)` times a
polynomial in the length of the encoded instance. -/
theorem ETH.not_decidableInSubexpTime_of_reduction (hETH : ETH) {f : CNF ℕ → β}
    (hf : ComputableInPolyTime f encCNF encB)
    (hfB : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → (f φ ∈ B ↔ φ ∈ SAT)) {k : ℕ}
    (hμ : ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) → μB (f φ) ≤ k * φ.length + k) :
    ¬DecidableInSubexpTime B encB μB := by
  intro h
  -- formulas with a clause of more than three literals go to the image of the empty clause
  refine ETH_iff_not_decidableInSubexpTime_length.mp hETH
    (h.of_reduction (f := fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then f φ
      else f [[]]) (ComputableInPolyTime.ite' (computableInPolyTime_all_length_le 3)
        hf (ComputableInPolyTime.const _)) (fun φ => ?_) (c := 2 * k) fun φ => ?_)
  · by_cases hφ : ∀ c ∈ φ, c.length ≤ 3
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
      simp only [hw, ite_true, hfB φ hφ]
      exact ⟨fun h => h.2, fun h => ⟨hφ, h⟩⟩
    · have hw : (φ.all fun c => decide (c.length ≤ 3)) = false := by simpa using hφ
      simp only [hw, Bool.false_eq_true, ite_false, hfB [[]] (by simp)]
      exact ⟨fun h => (hφ h.1).elim, fun ⟨σ, hσ⟩ => by simp at hσ⟩
  · split_ifs with hw
    · have := hμ φ (by simpa using hw)
      nlinarith
    · have := hμ [[]] (by simp)
      simp only [List.length_singleton, mul_one] at this
      nlinarith

/-! ### Exponential-time and exhaustive-search reductions -/

/-- For any constant $C \ge 0$ and $\varepsilon > 0$, $(C : \mathbb{R}) \cdot n$ is bounded by an
$\varepsilon$-dependent constant plus $(\varepsilon / 2) \cdot n \log_2 n$. -/
theorem mul_le_pow_add_mul_log (C : ℕ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (C : ℝ) * n ≤ C * ((2 ^ (⌈(2 * C : ℝ) / ε⌉₊ + 1) : ℕ) : ℝ) +
      (ε / 2) * (n * Nat.log 2 n : ℝ) := by
  set M : ℕ := ⌈(2 * C : ℝ) / ε⌉₊ + 1
  have hnonneg : 0 ≤ (ε / 2) * (n * Nat.log 2 n : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (C : ℝ) * ((2 ^ M : ℕ) : ℝ) := by positivity
  by_cases hn : n < 2 ^ M
  · have hn_le : (n : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast hn.le
    have h1 : (C : ℝ) * n ≤ C * ((2 ^ M : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hn_le (Nat.cast_nonneg C)
    linarith
  · have hn' : 2 ^ M ≤ n := not_lt.mp hn
    have hlog : M ≤ Nat.log 2 n := Nat.le_log_of_pow_le Nat.one_lt_two hn'
    have hM_ge : (2 * C : ℝ) / ε ≤ M :=
      (Nat.le_ceil ((2 * C : ℝ) / ε)).trans (by simp [M])
    have hlog_ge : (2 * C : ℝ) / ε ≤ (Nat.log 2 n : ℝ) :=
      hM_ge.trans (by exact_mod_cast hlog)
    have hC_le : (C : ℝ) ≤ (ε / 2) * (Nat.log 2 n : ℝ) := by
      rw [div_le_iff₀ hε] at hlog_ge
      linarith
    have hmul := mul_le_mul_of_nonneg_right hC_le (Nat.cast_nonneg n)
    linarith [show (ε / 2) * (Nat.log 2 n : ℝ) * n = (ε / 2) * (n * Nat.log 2 n : ℝ) by ring]

/-- **Subexponential-time transfer along $2^{O(m(a))}$-time reductions.** If $f : \alpha \to \beta$
is computable in time $O(2^{C m(a)} \cdot (|a| + 1)^D)$, reduces $A$ to $B$, and maps every
instance $a$ to one with parameter $\mu_B(f(a)) \le c \cdot m(a) \log_2 m(a) + c$, then a
$2^{o(\mu_B)}$-time decider for $B$ yields a $2^{o(m \log m)}$-time decider for $A$. -/
theorem DecidableInSubexpTime.of_expReduction {f : α → β} {m : α → ℕ}
    (hf : ∃ C D : ℕ, ComputableInO f encA encB
      (fun a => 2 ^ (C * m a) * ((encA a).length + 1) ^ D)
      (fun a => 2 ^ (C * m a) * ((encA a).length + 1) ^ D))
    (hfA : ∀ a, a ∈ A ↔ f a ∈ B) {c : ℕ}
    (hμ : ∀ a, μB (f a) ≤ c * (m a * Nat.log 2 (m a)) + c)
    (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA (fun a => m a * Nat.log 2 (m a)) := by
  intro ε hε
  obtain ⟨C, D, hfO⟩ := hf
  have hfO := hfO.tidy
  obtain ⟨l, hl⟩ := hfO.length_le_time
  set δ : ℝ := ε / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨e, hdec⟩ := h δ hδ
  obtain ⟨g, t, k, hg, hgB, ht⟩ := hdec.exists_computableInO
  have hg := hg.tidy
  set C' : ℕ := C * (e + 1)
  set E : ℕ := D * (e + 1)
  set M : ℕ := ⌈(2 * C' : ℝ) / ε⌉₊ + 1
  set K₀ : ℝ := 2 ^ ((C' : ℝ) * ((2 ^ M : ℕ) : ℝ))
  set K₁ : ℝ := 1 + k * 2 ^ (δ * c) * (2 * l + 1) ^ e + k
  set K : ℝ := K₁ * K₀
  refine DecidableInExpTime.of_computableInO (.of_tidy (hg.comp hfO))
    (fun a => (hfA a).trans (hgB (f a)))
    ⌈K⌉₊ E fun a => ?_
  show _ ≤ _
  set L : ℕ := (encA a).length
  set P_exp : ℝ := 2 ^ ((C : ℝ) * m a)
  set P_poly : ℝ := ((L : ℝ) + 1) ^ D
  set P : ℝ := P_exp * P_poly
  set X₁ : ℝ := 2 ^ ((ε / 2) * (m a * Nat.log 2 (m a) : ℕ))
  set X : ℝ := 2 ^ (ε * (m a * Nat.log 2 (m a) : ℕ))
  have hP_exp1 : 1 ≤ P_exp := Real.one_le_rpow (by norm_num) (by positivity)
  have hP_poly1 : 1 ≤ P_poly :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)])
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hP_exp1 hP_poly1
  have hX₁ : 1 ≤ X₁ := Real.one_le_rpow (by norm_num) (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hP_nat : ((2 ^ (C * m a) * (L + 1) ^ D : ℕ) : ℝ) = P := by
    simp only [P, P_exp, P_poly]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    push_cast
    rfl
  have hlen : ((encB (f a)).length : ℝ) + 1 ≤ (2 * l + 1) * P := by
    have h1 : ((encB (f a)).length : ℝ) ≤ l * (P + 1) := by
      have := hl a
      rw [← hP_nat]
      exact_mod_cast this
    nlinarith
  have hcδ : (c : ℝ) * δ ≤ ε / 2 := by
    simp only [δ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hexp : (2 : ℝ) ^ (δ * μB (f a)) ≤ 2 ^ (δ * c) * X₁ := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hμ' : (μB (f a) : ℝ) ≤ c * (m a * Nat.log 2 (m a) : ℕ) + c := by
      exact_mod_cast hμ a
    have hmul := mul_le_mul_of_nonneg_right hcδ (Nat.cast_nonneg (m a * Nat.log 2 (m a)))
    nlinarith
  have hpow : (((encB (f a)).length : ℝ) + 1) ^ e ≤ (2 * l + 1) ^ e * P ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlen e
  have ht' : (t (f a) : ℝ) ≤
      k * (2 ^ (δ * c) * (2 * l + 1) ^ e) * (X₁ * P ^ e) + k := by
    refine (ht (f a)).trans ?_
    have := mul_le_mul hexp hpow (by positivity) (by positivity)
    nlinarith
  have hPe : P ^ e ≤ P ^ (e + 1) := pow_le_pow_right₀ hP (Nat.le_succ e)
  have hP1 : P ≤ P ^ (e + 1) := le_self_pow₀ hP (Nat.succ_ne_zero e)
  have hX₁P : 1 ≤ X₁ * P ^ (e + 1) := one_le_mul_of_one_le_of_one_le hX₁ (one_le_pow₀ hP)
  have hstep1 : P + (t (f a) : ℝ) ≤ K₁ * (X₁ * P ^ (e + 1)) := by
    have h₁ : P ≤ X₁ * P ^ (e + 1) := hP1.trans (le_mul_of_one_le_left (by positivity) hX₁)
    have h₂ : X₁ * P ^ e ≤ X₁ * P ^ (e + 1) := mul_le_mul_of_nonneg_left hPe (by positivity)
    have h₃ := mul_le_mul_of_nonneg_left h₂
      (by positivity : (0 : ℝ) ≤ k * (2 ^ (δ * c) * (2 * l + 1) ^ e))
    have h₄ := mul_le_mul_of_nonneg_left hX₁P hk
    simp only [K₁]
    nlinarith
  have hP_exp_pow : P_exp ^ (e + 1) ≤ K₀ * X₁ := by
    have hrpow : P_exp ^ (e + 1) = 2 ^ ((C' : ℝ) * m a) := by
      simp only [P_exp, C', ← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hrpow]
    have hK₀X₁ : K₀ * X₁ =
        2 ^ ((C' : ℝ) * ((2 ^ M : ℕ) : ℝ) + (ε / 2) * (m a * Nat.log 2 (m a) : ℕ)) := by
      simp only [K₀, X₁]
      rw [← Real.rpow_add (by norm_num)]
    rw [hK₀X₁]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    simpa only [Nat.cast_mul] using mul_le_pow_add_mul_log C' hε (m a)
  have hP_poly_pow : P_poly ^ (e + 1) = ((L : ℝ) + 1) ^ E := by
    simp only [P_poly, E, ← pow_mul]
  have hX₁_sq : X₁ * X₁ = X := by
    simp only [X₁, X]
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hstep2 : X₁ * P ^ (e + 1) ≤ K₀ * (X * ((L : ℝ) + 1) ^ E) := by
    have hsplit : X₁ * P ^ (e + 1) = X₁ * P_exp ^ (e + 1) * P_poly ^ (e + 1) := by
      simp only [P, mul_pow]
      ring
    rw [hsplit, hP_poly_pow]
    have hmul1 := mul_le_mul_of_nonneg_left hP_exp_pow (by positivity : (0 : ℝ) ≤ X₁)
    have hmul2 := mul_le_mul_of_nonneg_right hmul1 (by positivity : (0 : ℝ) ≤ ((L : ℝ) + 1) ^ E)
    calc X₁ * P_exp ^ (e + 1) * ((L : ℝ) + 1) ^ E
        ≤ X₁ * (K₀ * X₁) * ((L : ℝ) + 1) ^ E := hmul2
      _ = K₀ * ((X₁ * X₁) * ((L : ℝ) + 1) ^ E) := by ring
      _ = K₀ * (X * ((L : ℝ) + 1) ^ E) := by rw [hX₁_sq]
  have hK_ceil : K ≤ ⌈K⌉₊ := Nat.le_ceil K
  have hLHS : (((2 ^ (C * m a) * (L + 1) ^ D + t (f a) : ℕ) : ℝ)) =
      P + (t (f a) : ℝ) := by
    rw [Nat.cast_add, hP_nat]
  calc (((2 ^ (C * m a) * (L + 1) ^ D + t (f a) : ℕ) : ℝ))
      = P + (t (f a) : ℝ) := hLHS
    _ ≤ K₁ * (X₁ * P ^ (e + 1)) := hstep1
    _ ≤ K₁ * (K₀ * (X * ((L : ℝ) + 1) ^ E)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = K * (X * ((L : ℝ) + 1) ^ E) := by simp only [K, mul_assoc]
    _ ≤ ⌈K⌉₊ * (X * ((L : ℝ) + 1) ^ E) :=
        mul_le_mul_of_nonneg_right hK_ceil (by positivity)

namespace ExhaustiveSearch

private abbrev State (α : Type) : Type := (α × ℕ) × Bool

private def encState (encA : α ↪ List Bool) : State α ↪ List Bool :=
  encPair (encPair encA encNat) encBool

private def init (a : α) : State α := ((a, 0), false)

private def step (f : α × ℕ → β) (g : β → Bool) (s : State α) : State α :=
  ((s.1.1, s.1.2 + 1), s.2 || g (f s.1))

private def rounds (ν : α → ℕ) (a : α) : ℕ := 2 ^ ν a

private def search (f : α × ℕ → β) (ν : α → ℕ) (g : β → Bool) (a : α) : Bool :=
  ((step f g)^[rounds ν a] (init a)).2

private theorem iterate_step_init (f : α × ℕ → β) (g : β → Bool) (a : α) (k : ℕ) :
    (step f g)^[k] (init a) =
      ((a, k), (List.range k).any fun r => g (f (a, r))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]

private theorem search_eq_true_iff {f : α × ℕ → β} {ν : α → ℕ} {g : β → Bool}
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B)
    (hg : ∀ b, g b = true ↔ b ∈ B) (a : α) :
    search f ν g a = true ↔ a ∈ A := by
  rw [search, iterate_step_init, List.any_eq_true, hfA]
  simp only [List.mem_range, hg, rounds]

open ComputableTidilyInPolyTime in
private theorem computableTidilyInPolyTime_init :
    ComputableTidilyInPolyTime init encA (encState encA) := by
  unfold init encState
  fun_prop

open ComputableTidilyInPolyTime in
private theorem computableTidilyInPolyTime_rounds {ν : α → ℕ}
    (hν : ComputableTidilyInPolyTime ν encA encUnary) :
    ComputableTidilyInPolyTime (rounds ν) encA encNat :=
  binary_two_pow.comp hν

open ComputableTidilyInPolyTime in
private theorem exists_computableTidilyInO_step {f : α × ℕ → β}
    (hf : ComputableTidilyInPolyTime f (encPair encA encNat) encB)
    {g : β → Bool} {t : β → ℕ}
    (hg : ComputableTidilyInO g encB encBool t t) :
    ∃ d, ComputableTidilyInO (step f g) (encState encA) (encState encA)
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1))
      (fun s => ((encState encA s).length + 1) ^ d + t (f s.1)) := by
  obtain ⟨dN, eN, hN⟩ := (show ComputableTidilyInPolyTime (fun s : State α => (s.1.1, s.1.2 + 1))
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop).exists_degree
  obtain ⟨dB, eB, hB⟩ := (show ComputableTidilyInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨dR, eR, hR⟩ := (hf.comp (show ComputableTidilyInPolyTime (fun s : State α => s.1)
    (encState encA) (encPair encA encNat) by unfold encState; fun_prop)).exists_degree
  obtain ⟨dO, eO, hO⟩ := bool_or.exists_degree
  set D := dN + dB + dR
  have hN' := (hN.mono (d' := D) (e' := eN) (by omega) le_rfl).inO
  have hB' := (hB.mono (d' := D) (e' := eB) (by omega) le_rfl).inO
  have hR' := (hR.mono (d' := D) (e' := eR) (by omega) le_rfl).inO
  have h := hN'.prod (hO.inO.comp (hB'.prod (hg.comp hR')))
  have h4 (p : Bool × Bool) : (encPair encBool encBool p).length = 4 := by simp
  refine ⟨D, (h.mono (5 ^ dO + 4) (fun s => ?_) (fun s => ?_)).of_enc_eq fun _ => rfl⟩ <;>
  · simp only [Function.comp_apply, h4]
    generalize ((encState encA s).length + 1) ^ D = P
    generalize t (f s.1) = T
    have hF : 1 ≤ (4 + 1) ^ dO := Nat.one_le_pow _ _ (by norm_num)
    generalize (4 + 1) ^ dO = F at hF ⊢
    nlinarith

private theorem exists_state_and_node_bounds {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableTidilyInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableTidilyInPolyTime ν encA encUnary) :
    ∃ (c_st d_st c_nd d_nd : ℕ),
      (∀ (g : β → Bool) (a : α) (k : ℕ),
        k ≤ rounds ν a →
        (encState encA ((step f g)^[k] (init a))).length ≤ c_st * ((encA a).length + 1) ^ d_st) ∧
      (∀ (a : α),
        (encNat (rounds ν a)).length + 1 ≤ c_st * ((encA a).length + 1) ^ d_st) ∧
      (∀ (a : α) (k : ℕ),
        k ≤ rounds ν a →
        (encB (f (a, k))).length ≤ c_nd * ((encA a).length + 1) ^ d_nd) := by
  obtain ⟨c_ν, d_ν, hν_len⟩ := hν.polyBounded_length.exists_le
  obtain ⟨cb, db, hf_len⟩ := hf.polyBounded_length.exists_le
  set d_st := d_ν + 1
  set c_p := 2 * c_ν + 4
  set c_st := 2 * c_p + 4
  have hpair_le (a : α) {k : ℕ} (hk : k ≤ rounds ν a) :
      (encPair encA encNat (a, k)).length ≤ c_p * ((encA a).length + 1) ^ d_st := by
    set L := (encA a).length
    have hK := ComputableTidilyInO.length_encNat_mono hk
    rw [rounds, encNat_two_pow, List.length_append, List.length_replicate,
      List.length_singleton] at hK
    have hνa : ν a ≤ c_ν * (L + 1) ^ d_ν := by
      simpa only [encUnary_apply, List.length_replicate] using hν_len a
    have hd1 : (L + 1) ^ d_ν ≤ (L + 1) ^ d_st :=
      Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ d_ν)
    have hd2 : L + 1 ≤ (L + 1) ^ d_st := by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.succ_pos d_ν)
    have hνa' : ν a ≤ c_ν * (L + 1) ^ d_st := hνa.trans (Nat.mul_le_mul_left c_ν hd1)
    simp only [length_encPair, L, c_p]
    nlinarith
  refine ⟨c_st, d_st, cb * (c_p + 1) ^ db, d_st * db,
    fun g a k hk => ?_, fun a => ?_, fun a k hk => ?_⟩
  · rw [iterate_step_init, encState, length_encPair]
    have hp := hpair_le a hk
    have h1 : 1 ≤ ((encA a).length + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos _)
    simp only [encBool_apply, List.length_singleton, c_st]
    nlinarith
  · set L := (encA a).length
    rw [rounds, encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hνa : ν a ≤ c_ν * (L + 1) ^ d_ν := by
      simpa only [encUnary_apply, List.length_replicate] using hν_len a
    have hd1 : (L + 1) ^ d_ν ≤ (L + 1) ^ d_st :=
      Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ d_ν)
    have h1 : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
    have hνa' : ν a ≤ c_ν * (L + 1) ^ d_st := hνa.trans (Nat.mul_le_mul_left c_ν hd1)
    simp only [c_st, c_p, L]
    nlinarith
  · have h1 := hf_len (a, k)
    have h2 := hpair_le a hk
    have h3 : (encPair encA encNat (a, k)).length + 1 ≤
        (c_p + 1) * ((encA a).length + 1) ^ d_st := by
      have : 1 ≤ ((encA a).length + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos _)
      nlinarith
    calc (encB (f (a, k))).length
        ≤ cb * ((encPair encA encNat (a, k)).length + 1) ^ db := h1
      _ ≤ cb * ((c_p + 1) * ((encA a).length + 1) ^ d_st) ^ db :=
          Nat.mul_le_mul_left cb (Nat.pow_le_pow_left h3 db)
      _ = cb * (c_p + 1) ^ db * ((encA a).length + 1) ^ (d_st * db) := by
          rw [mul_pow, ← pow_mul, ← mul_assoc]

private noncomputable def leafTime (encA : α ↪ List Bool) (μA : α → ℕ)
    (c_mu c_nd d_nd : ℕ) (δ : ℝ) (c e : ℕ) (a : α) : ℕ :=
  ⌈(c : ℝ) * (2 ^ (δ * ((c_mu * μA a + c_mu : ℕ) : ℝ)) *
    ((c_nd * ((encA a).length + 1) ^ d_nd : ℕ) + 1 : ℝ) ^ e) + c⌉₊

end ExhaustiveSearch

open ExhaustiveSearch in
/-- **Exponential-time transfer along an exhaustive search.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and $\nu(a) \le \mu_A(a) / M + K$, then a decider for $B$
within time $2^{\delta \mu_B(b)} \cdot \mathrm{poly}(|b|)$ yields a decider for $A$ within time
$2^{(1 / M + c \delta) \mu_A(a)} \cdot \mathrm{poly}(|a|)$. -/
theorem DecidableInExpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c) {M K : ℕ}
    (hνM : ∀ a, ν a ≤ μA a / M + K) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (1 / M + c * δ) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact DecidableInExpTime.of_computableInO (.of_tidy (.const false))
      (fun a => hα.elim a) 1 0 (fun a => hα.elim a)
  obtain ⟨a₀⟩ := hα
  have : Inhabited α := ⟨a₀⟩
  have hf_tidy := hf.tidy
  have hν_tidy := hν.tidy
  obtain ⟨e, h⟩ := h
  obtain ⟨g, t, k_dec, hg, hgB, ht⟩ := h.exists_computableInO
  have hg := hg.tidy
  obtain ⟨d, hstep⟩ := exists_computableTidilyInO_step hf_tidy hg
  obtain ⟨dn, _, hn⟩ := (computableTidilyInPolyTime_rounds hν_tidy).exists_degree
  obtain ⟨di, _, hi⟩ := (computableTidilyInPolyTime_init (encA := encA)).exists_degree
  obtain ⟨da, _, ha⟩ := (show ComputableTidilyInPolyTime (fun s : State α => s.2)
    (encState encA) encBool by unfold encState; fun_prop).exists_degree
  obtain ⟨c_st, d_st, c_nd, d_nd, hst_bound, hrounds_len, hnd_bound⟩ :=
    exists_state_and_node_bounds hf_tidy hν_tidy
  set stBound : α → ℕ := fun a => c_st * ((encA a).length + 1) ^ d_st
  set ndBound : α → ℕ := fun a => c_nd * ((encA a).length + 1) ^ d_nd
  have hround (a : α) (k : ℕ) (hk : k ≤ rounds ν a) :
      ((encState encA ((step f g)^[k] (init a))).length + 1) ^ d +
        t (f ((step f g)^[k] (init a)).1) ≤
        (stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a := by
    have hS : (encState encA ((step f g)^[k] (init a))).length ≤ stBound a :=
      hst_bound g a k hk
    refine Nat.add_le_add (Nat.pow_le_pow_left (by omega) d) ?_
    rw [iterate_step_init]
    dsimp only
    set b := f (a, k)
    have hb_mu : μB b ≤ c * μA a + c := hμ a k
    have hb_enc : (encB b).length ≤ ndBound a := hnd_bound a k hk
    have h₁ : (2 : ℝ) ^ (δ * μB b) ≤ 2 ^ (δ * ((c * μA a + c : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hb_mu) hδ)
    have h₂ : (((encB b).length : ℝ) + 1) ^ e ≤ ((ndBound a : ℝ) + 1) ^ e :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hb_enc 1) e
    have h₃ := mul_le_mul h₁ h₂ (by positivity) (by positivity)
    have h₄ := mul_le_mul_of_nonneg_left h₃ (Nat.cast_nonneg k_dec : (0 : ℝ) ≤ k_dec)
    have h₅ := (ht b).trans (add_le_add h₄ le_rfl)
    exact Nat.cast_le.mp (h₅.trans (Nat.le_ceil _))
  have hstate (a : α) (k : ℕ) (hk : k ≤ rounds ν a) :
      (encState encA ((step f g)^[k] (init a))).length ≤ stBound a :=
    hst_bound g a k hk
  have hiter := ComputableTidilyInO.iterate hn.inO hi.inO hstep hround hround hstate
  have hsearch := ha.inO.comp hiter
  set C₁ := (c_st + 1) ^ d + c_st + c_st ^ 2
  set C₃ := (c_st + 1) ^ da
  set E := dn + di + d_st * d + d_st * da + d_nd * e + 2 * d_st
  set C₂ : ℝ := k_dec * 2 ^ (c * δ) * ((c_nd : ℝ) + 1) ^ e + k_dec + 1
  set C₀ : ℝ := 3 + C₃ + (2 ^ K + 1 : ℝ) * (C₁ + C₂)
  refine DecidableInExpTime.of_computableInO (.of_tidy hsearch)
    (fun a => (search_eq_true_iff hfA (fun b => (hgB b).symm) a).symm) ⌈C₀⌉₊ E fun a => ?_
  set L := (encA a).length
  set N := μA a
  set P := (L + 1) ^ E
  have hP (m : ℕ) (hm : m ≤ E) : (L + 1) ^ m ≤ P := Nat.pow_le_pow_right (Nat.succ_pos L) hm
  have hsb : stBound a = c_st * (L + 1) ^ d_st := rfl
  have hr : rounds ν a + 1 ≤ (2 ^ K + 1) * 2 ^ (N / M) := by
    have h1 := hνM a
    have h2 : rounds ν a ≤ 2 ^ K * 2 ^ (N / M) := by
      calc rounds ν a = 2 ^ ν a := rfl
        _ ≤ 2 ^ (N / M + K) := Nat.pow_le_pow_right two_pos h1
        _ = 2 ^ K * 2 ^ (N / M) := by rw [pow_add, Nat.mul_comm]
    have h3 : 1 ≤ 2 ^ (N / M) := Nat.one_le_two_pow
    nlinarith
  have hpoly : (L + 1) ^ dn + (L + 1) ^ di ≤ 2 * P := by
    have := hP dn (by omega)
    have := hP di (by omega)
    omega
  have hans_le :
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da ≤ C₃ * P := by
    have h1 := hstate a (rounds ν a) le_rfl
    have h2 : stBound a + 1 ≤ (c_st + 1) * (L + 1) ^ d_st := by
      have : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
      rw [hsb]
      nlinarith
    calc ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da
        ≤ (stBound a + 1) ^ da := Nat.pow_le_pow_left (by omega) da
      _ ≤ ((c_st + 1) * (L + 1) ^ d_st) ^ da := Nat.pow_le_pow_left h2 da
      _ = C₃ * (L + 1) ^ (d_st * da) := by simp only [C₃, mul_pow, ← pow_mul]
      _ ≤ C₃ * P := Nat.mul_le_mul_left C₃ (hP (d_st * da) (by omega))
  have hrnd : (stBound a + 1) ^ d + stBound a +
      ((encNat (rounds ν a)).length + 1) ^ 2 ≤ C₁ * P := by
    have h1 : (stBound a + 1) ^ d ≤ (c_st + 1) ^ d * (L + 1) ^ (d_st * d) := by
      have hst1 : stBound a + 1 ≤ (c_st + 1) * (L + 1) ^ d_st := by
        have : 1 ≤ (L + 1) ^ d_st := Nat.one_le_pow _ _ (Nat.succ_pos L)
        rw [hsb]
        nlinarith
      calc (stBound a + 1) ^ d ≤ ((c_st + 1) * (L + 1) ^ d_st) ^ d := Nat.pow_le_pow_left hst1 d
        _ = (c_st + 1) ^ d * (L + 1) ^ (d_st * d) := by rw [mul_pow, ← pow_mul]
    have h2 : ((encNat (rounds ν a)).length + 1) ^ 2 ≤ c_st ^ 2 * (L + 1) ^ (d_st * 2) := by
      have hr_len := hrounds_len a
      calc ((encNat (rounds ν a)).length + 1) ^ 2
          ≤ (c_st * (L + 1) ^ d_st) ^ 2 := Nat.pow_le_pow_left hr_len 2
        _ = c_st ^ 2 * (L + 1) ^ (d_st * 2) := by rw [mul_pow, ← pow_mul]
    have h3 := hP (d_st * d) (by omega)
    have h4 := hP d_st (by omega)
    have h5 := hP (d_st * 2) (by omega)
    calc (stBound a + 1) ^ d + stBound a + ((encNat (rounds ν a)).length + 1) ^ 2
        ≤ (c_st + 1) ^ d * P + c_st * P + c_st ^ 2 * P := by
          have := h1.trans (Nat.mul_le_mul_left ((c_st + 1) ^ d) h3)
          have := (le_of_eq hsb).trans (Nat.mul_le_mul_left c_st h4)
          have := h2.trans (Nat.mul_le_mul_left (c_st ^ 2) h5)
          omega
      _ = C₁ * P := by simp only [C₁]; ring
  set Y : ℝ := 2 ^ ((c * δ) * N)
  have hY : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos L)
  have hleaf : (leafTime encA μA c c_nd d_nd δ k_dec e a : ℝ) ≤ C₂ * Y * P := by
    have h₁ : (2 : ℝ) ^ (δ * ((c * N + c : ℕ) : ℝ)) = 2 ^ (c * δ) * Y := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    have h₂ : ((ndBound a : ℝ) + 1) ^ e ≤ ((c_nd : ℝ) + 1) ^ e * P := by
      have hnb_le : (ndBound a : ℝ) + 1 ≤ ((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd := by
        have hnb_eq : (ndBound a : ℝ) = c_nd * ((L : ℝ) + 1) ^ d_nd := by
          simp only [ndBound]
          push_cast
          ring
        have hpow1 : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ d_nd :=
          one_le_pow₀ (by linarith [(L.cast_nonneg : (0 : ℝ) ≤ L)])
        nlinarith
      calc ((ndBound a : ℝ) + 1) ^ e ≤ (((c_nd : ℝ) + 1) * ((L : ℝ) + 1) ^ d_nd) ^ e :=
            pow_le_pow_left₀ (by positivity) hnb_le e
        _ = ((c_nd : ℝ) + 1) ^ e * ((L : ℝ) + 1) ^ (d_nd * e) := by rw [mul_pow, ← pow_mul]
        _ ≤ ((c_nd : ℝ) + 1) ^ e * P := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hP (d_nd * e) (by omega)
    have h₃ := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (k_dec : ℝ) * (2 ^ (δ * ((c * N + c : ℕ) : ℝ)) *
      ((ndBound a : ℝ) + 1) ^ e) + k_dec by positivity)
    unfold leafTime
    change (⌈(k_dec : ℝ) * (2 ^ (δ * ((c * N + c : ℕ) : ℝ)) *
      ((ndBound a : ℝ) + 1) ^ e) + k_dec⌉₊ : ℝ) ≤ _
    rw [h₁] at h₃ ⊢
    have h₄ : (k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) ≤
        k_dec * 2 ^ (c * δ) * ((c_nd : ℝ) + 1) ^ e * Y * P := by
      have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ k_dec * 2 ^ (c * δ) * Y)
      nlinarith
    have h₅ : (k_dec : ℝ) + 1 ≤ ((k_dec : ℝ) + 1) * Y * P := by
      have : (1 : ℝ) ≤ Y * P := one_le_mul_of_one_le_of_one_le hY hP1
      nlinarith
    calc (⌈(k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) + k_dec⌉₊ : ℝ)
        ≤ (k_dec : ℝ) * (2 ^ (c * δ) * Y * ((ndBound a : ℝ) + 1) ^ e) + k_dec + 1 := h₃.le
      _ ≤ C₂ * Y * P := by simp only [C₂]; nlinarith
  set X : ℝ := 2 ^ ((1 / M : ℝ) * N)
  have hX : ((2 ^ (N / M) : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [one_div_mul_eq_div]
    exact Nat.cast_div_le
  have hX1 : 1 ≤ X := Real.one_le_rpow (by norm_num) (by positivity)
  have hXY : X * Y = 2 ^ ((1 / M + c * δ) * N) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hT : ((L + 1) ^ dn + (L + 1) ^ di +
      (rounds ν a + 1) * ((stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a +
        stBound a + ((encNat (rounds ν a)).length + 1) ^ 2) +
      ((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da : ℝ) ≤
      (2 + C₃ : ℝ) * P + (2 ^ K + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
    have h₁ : ((L + 1) ^ dn + (L + 1) ^ di : ℝ) ≤ 2 * P := by exact_mod_cast hpoly
    have h₁' :
        (((encState encA ((step f g)^[rounds ν a] (init a))).length + 1) ^ da : ℝ) ≤ C₃ * P := by
      exact_mod_cast hans_le
    have h₂ : ((rounds ν a + 1 : ℕ) : ℝ) ≤ (2 ^ K + 1 : ℝ) * X := by
      have : ((rounds ν a + 1 : ℕ) : ℝ) ≤ (((2 ^ K + 1) * 2 ^ (N / M) : ℕ) : ℝ) := by
        exact_mod_cast hr
      rw [Nat.cast_mul] at this
      have hKM : (0 : ℝ) ≤ (2 ^ K + 1 : ℕ) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hX hKM
      push_cast at this hmul ⊢
      linarith
    have h₃ : (((stBound a + 1) ^ d + stBound a +
        ((encNat (rounds ν a)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P := by exact_mod_cast hrnd
    have h₄ : (((stBound a + 1) ^ d + leafTime encA μA c c_nd d_nd δ k_dec e a + stBound a +
        ((encNat (rounds ν a)).length + 1) ^ 2 : ℕ) : ℝ) ≤ C₁ * P + C₂ * Y * P := by
      push_cast at h₃ ⊢
      linarith
    have h₅ := mul_le_mul h₂ h₄ (by positivity) (by positivity)
    push_cast at h₁ h₁' h₅ ⊢
    linarith
  calc _ ≤ (2 + C₃ : ℝ) * P + (2 ^ K + 1 : ℝ) * X * (C₁ * P + C₂ * Y * P) := by
          exact_mod_cast hT
    _ ≤ C₀ * (X * Y * P) := by
        have hXY1 : 1 ≤ X * Y := one_le_mul_of_one_le_of_one_le hX1 hY
        have hC₂ : 0 ≤ C₂ := by positivity
        have hC₁ : (0 : ℝ) ≤ C₁ := by positivity
        have hC₃ : (0 : ℝ) ≤ C₃ := by positivity
        have hKM : (0 : ℝ) ≤ 2 ^ K + 1 := by positivity
        have hP0 : (0 : ℝ) ≤ P := by positivity
        have a₁ : (P : ℝ) ≤ X * Y * P := le_mul_of_one_le_left hP0 hXY1
        have a₂ : X * P ≤ X * Y * P := by
          have := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ X * P)
          linarith [show X * P * Y = X * Y * P by ring]
        have a₃ := mul_le_mul_of_nonneg_left a₂ (mul_nonneg hKM hC₁)
        have a₄ := mul_le_mul_of_nonneg_left a₁ hC₃
        simp only [C₀]
        nlinarith
    _ ≤ ⌈C₀⌉₊ * (2 ^ ((1 / M + c * δ) * N) * ((L : ℝ) + 1) ^ E) := by
        rw [← hXY]
        push_cast [P]
        exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₀) (by positivity)

/-- **Subexponential-time transfer along an exhaustive search with sublinear branch exponent.** If
$f : \alpha \times \mathbb{N} \to \beta$ and $\nu : \alpha \to \mathbb{N}$ are computable in
polynomial time (with $\nu$ in unary), $a \in A \iff \exists r < 2^{\nu(a)},\, f(a, r) \in B$,
$\mu_B(f(a, r)) \le c \cdot \mu_A(a) + c$, and for every $M \ge 1$ there is a constant $K$ with
$\nu(a) \le \mu_A(a) / M + K$, then subexponential time for $B$ in $\mu_B$ gives subexponential time
for $A$ in $\mu_A$. -/
theorem DecidableInSubexpTime.of_exhaustiveSearch {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encA encNat) encB)
    (hν : ComputableInPolyTime ν encA encUnary)
    (hfA : ∀ a, a ∈ A ↔ ∃ r < 2 ^ ν a, f (a, r) ∈ B) {c : ℕ}
    (hμ : ∀ a r, μB (f (a, r)) ≤ c * μA a + c)
    (hνM : ∀ M > 0, ∃ K, ∀ a, ν a ≤ μA a / M + K)
    (h : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM_nat : 0 < M := Nat.cast_pos.mp hMpos
  obtain ⟨K, hK⟩ := hνM M hM_nat
  have hMε : 1 / (M : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM
    linarith
  set δ : ℝ := ε / (2 * (c + 1))
  have hδ : 0 < δ := by positivity
  refine ((h δ hδ).of_exhaustiveSearch hf hν hfA hμ hK hδ.le).mono ?_
  have hcδ : (c : ℝ) * δ ≤ ε / 2 := by
    simp only [δ]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Reduction

end Cslib.Complexity
