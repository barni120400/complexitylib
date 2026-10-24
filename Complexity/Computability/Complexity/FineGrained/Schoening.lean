/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
public import Mathlib.InformationTheory.Hamming
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Schöning's random walk for 3-SAT

Schöning's algorithm searches for a satisfying assignment of a CNF formula by local search with
restarts. One *trial* draws a uniformly random assignment and then performs `3 n` steps, where `n`
is the number of variables. Each step stops if the formula is satisfied. Otherwise it takes the
first unsatisfied clause, chooses one of its literal occurrences uniformly, and flips that
variable (`Cslib.Complexity.Schoening.walk`, `Cslib.Complexity.Schoening.trial`)
[Schöning][Schoening1999].

For a satisfiable formula whose clauses have at most three literals, a trial succeeds with
probability at least `(3 / 4) ^ n / (3 n + 1)` (`Cslib.Complexity.Schoening.trial_success`). So
about `(4 / 3) ^ n` independent trials find a satisfying assignment with high probability,
exponentially faster than the `2 ^ n` assignments of brute force. Schöning states the bound up to a
polynomial factor; the factor `1 / (3 n + 1)` here is this file's explicit constant.

The proof compares the walk with a biased random walk on distances. Fix a satisfying assignment
`σ⋆`. A step changes the Hamming distance to `σ⋆` by one. Since `σ⋆` satisfies the chosen clause
and the current assignment does not, at least one of its at most three literals moves toward `σ⋆`.
Let `hit t d` be the probability that a walk on `ℕ`, stepping down with probability `1 / 3` and up
with probability `2 / 3`, reaches `0` from `d` within `t` steps (`Cslib.Complexity.Schoening.hit`).
It is antitone in `d` (`hit_succ_le`), so by induction on `t` the trial walk succeeds with
probability at least `hit t (dist σ σ⋆)` (`hit_le_succeedProb`). No coupling is needed.

A path of `2 j` down-steps and `j` up-steps reaches `0` from `j`, so
`hit (3 j) j ≥ C(3j, j) (1/3)^{2j} (2/3)^j` (`choose_mul_le_hit`). The middle binomial weight is the
largest of the `3 j + 1` terms of `(1 + 2) ^ {3j}`, so `C(3j, j) 4^j (3j + 1) ≥ 27^j`
(`pow_le_choose_mul`), and `hit (3 j) j ≥ 2^{-j} / (3 j + 1)`. Averaging `2^{-dist}` over a
uniform start gives `(3/4)^n`, a product over the coordinates.

## Main definitions

* `Cslib.Complexity.Schoening.walk`: `t` steps of the local search from an assignment.
* `Cslib.Complexity.Schoening.trial`: a uniform start followed by `3 n` steps.
* `Cslib.Complexity.Schoening.hit`: hitting probabilities of the biased walk.

## Main results

* `Cslib.Complexity.Schoening.hit_le_succeedProb`: the local search dominates the biased walk.
* `Cslib.Complexity.Schoening.choose_mul_le_hit`: path counting for the biased walk.
* `Cslib.Complexity.Schoening.pow_le_choose_mul`: `27^j ≤ C(3j, j) 4^j (3j + 1)`.
* `Cslib.Complexity.Schoening.trial_success`: a trial succeeds with probability at least
  `(3 / 4) ^ n / (3 n + 1)`.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Complexity.Schoening

open Cslib.Logic.PL Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The algorithm -/

/-- Flip the value of the variable `v`. -/
def flip (σ : V → Bool) (v : V) : V → Bool := Function.update σ v (!σ v)

/-- The first clause of `φ` that `σ` falsifies, if any. -/
def firstUnsat (φ : CNF V) (σ : V → Bool) : Option (Clause V) :=
  φ.find? fun c => !c.eval σ

/-- Flip the variable of a uniformly chosen literal occurrence of `c`. The empty clause, which no
assignment satisfies, leaves the assignment unchanged. -/
noncomputable def flipStep (c : Clause V) (σ : V → Bool) : PMF (V → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    haveI : NeZero c.length := ⟨h⟩
    (Probability.PMF.uniformOfFintype (Fin c.length)).map fun i => flip σ (c.get i).1

/-- **Schöning's local search**: `t` steps from `σ`. Each step stops if `φ` is satisfied, and
otherwise flips a uniformly chosen variable of the first unsatisfied clause. -/
noncomputable def walk (φ : CNF V) : ℕ → (V → Bool) → PMF (V → Bool)
  | 0, σ => PMF.pure σ
  | t + 1, σ =>
    match firstUnsat φ σ with
    | none => PMF.pure σ
    | some c => (flipStep c σ).bind (walk φ t)

/-- **One trial of Schöning's algorithm**: a uniformly random assignment followed by `3 n` steps of
local search, where `n` is the number of variables. -/
noncomputable def trial (φ : CNF V) : PMF (V → Bool) :=
  (Probability.PMF.uniformOfFintype (V → Bool)).bind (walk φ (3 * Fintype.card V))

/-- The probability that `μ` produces an assignment satisfying `φ`. -/
noncomputable def succeedProb (φ : CNF V) (μ : PMF (V → Bool)) : ℝ :=
  (μ.toOuterMeasure {σ | φ.eval σ = true}).toReal

/-! ### The biased walk -/

/-- The probability that a walk on `ℕ` that steps down with probability `1 / 3` and up with
probability `2 / 3` reaches `0` from `d` within `t` steps. -/
noncomputable def hit : ℕ → ℕ → ℝ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | t + 1, d + 1 => hit t d / 3 + 2 * hit t (d + 2) / 3

@[simp] theorem hit_zero_right (t : ℕ) : hit t 0 = 1 := by cases t <;> rfl

@[simp] theorem hit_zero_succ (d : ℕ) : hit 0 (d + 1) = 0 := rfl

theorem hit_succ_succ (t d : ℕ) : hit (t + 1) (d + 1) = hit t d / 3 + 2 * hit t (d + 2) / 3 :=
  rfl

theorem hit_nonneg (t d : ℕ) : 0 ≤ hit t d := by
  induction t generalizing d with
  | zero => cases d <;> simp
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ]
      have := ih d
      have := ih (d + 2)
      positivity

theorem hit_le_one (t d : ℕ) : hit t d ≤ 1 := by
  induction t generalizing d with
  | zero => cases d <;> simp
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ]
      linarith [ih d, ih (d + 2)]

/-- Hitting `0` is less likely from farther away. -/
theorem hit_succ_le (t d : ℕ) : hit t (d + 1) ≤ hit t d := by
  induction t generalizing d with
  | zero => simpa using hit_nonneg 0 d
  | succ t ih =>
    cases d with
    | zero => simpa using hit_le_one (t + 1) 1
    | succ d =>
      rw [hit_succ_succ, hit_succ_succ]
      linarith [ih d, ih (d + 2)]

theorem hit_antitone (t : ℕ) : Antitone (hit t) :=
  antitone_nat_of_succ_le (hit_succ_le t)

/-- Hitting `0` is more likely with more time. -/
theorem hit_le_hit_succ (t d : ℕ) : hit t d ≤ hit (t + 1) d := by
  induction t generalizing d with
  | zero => cases d <;> simp [hit_nonneg]
  | succ t ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [hit_succ_succ, hit_succ_succ (t + 1)]
      linarith [ih d, ih (d + 2)]

theorem hit_monotone (d : ℕ) : Monotone fun t => hit t d :=
  monotone_nat_of_le_succ fun t => hit_le_hit_succ t d

/-- A single binomial weight is at most one. -/
private theorem choose_mul_pow_le_one (m a b : ℕ) (h : a + b = m) :
    (m.choose a : ℝ) * (1 / 3) ^ b * (2 / 3) ^ a ≤ 1 := by
  have hsum := add_pow (2 / 3 : ℝ) (1 / 3) m
  rw [show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, one_pow] at hsum
  have ha : a ∈ range (m + 1) := mem_range.mpr (by omega)
  have hle := single_le_sum (f := fun i => (2 / 3 : ℝ) ^ i * (1 / 3) ^ (m - i) * (m.choose i))
    (fun i _ => by positivity) ha
  rw [← hsum, show m - a = b by omega] at hle
  linarith

/-- **Path counting.** Any sequence of `b` down-steps and `a` up-steps with `d + a ≤ b` reaches `0`
from `d`, so the biased walk reaches `0` from `d` within `a + b` steps with probability at least
`C(a + b, a) (1/3)^b (2/3)^a`. -/
theorem choose_mul_le_hit (a b d : ℕ) (h : d + a ≤ b) :
    ((a + b).choose a : ℝ) * (1 / 3) ^ b * (2 / 3) ^ a ≤ hit (a + b) d := by
  induction hm : a + b generalizing a b d with
  | zero =>
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain rfl : d = 0 := by omega
    simp
  | succ m ih =>
    cases d with
    | zero => simpa using choose_mul_pow_le_one (m + 1) a b hm
    | succ d =>
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [hit_succ_succ]
      have h₁ := ih a b d (by omega) (by omega)
      cases a with
      | zero =>
        have := hit_nonneg m (d + 2)
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one] at h₁ ⊢
        rw [pow_succ]
        linarith
      | succ a =>
        have h₂ := ih a (b + 1) (d + 2) (by omega) (by omega)
        rw [Nat.choose_succ_succ, Nat.cast_add]
        calc
          ((m.choose a : ℝ) + m.choose (a + 1)) * (1 / 3) ^ (b + 1) * (2 / 3) ^ (a + 1) =
              (m.choose (a + 1) : ℝ) * (1 / 3) ^ b * (2 / 3) ^ (a + 1) / 3 +
                2 * ((m.choose a : ℝ) * (1 / 3) ^ (b + 1) * (2 / 3) ^ a) / 3 := by ring
          _ ≤ hit m d / 3 + 2 * hit m (d + 2) / 3 := by gcongr

/-! ### The middle binomial weight -/

/-- The weights `C(3j, i) 2^{3j - i}` of `(1 + 2) ^ {3j}` increase up to `i = j`. -/
private theorem weight_le_succ {j i : ℕ} (hi : i < j) :
    (3 * j).choose i * 2 ^ (3 * j - i) ≤ (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) := by
  have hrec := Nat.choose_succ_right_eq (3 * j) i
  have hpow : 2 ^ (3 * j - i) = 2 * 2 ^ (3 * j - (i + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  have key : (3 * j).choose i * (2 * 2 ^ (3 * j - (i + 1))) * (i + 1) ≤
      (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) * (i + 1) := by
    calc
      (3 * j).choose i * (2 * 2 ^ (3 * j - (i + 1))) * (i + 1) =
          (3 * j).choose i * (2 * (i + 1)) * 2 ^ (3 * j - (i + 1)) := by ring
      _ ≤ (3 * j).choose i * (3 * j - i) * 2 ^ (3 * j - (i + 1)) := by
        gcongr
        omega
      _ = (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) * (i + 1) := by
        rw [← hrec]
        ring
  exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos i)

/-- The weights `C(3j, i) 2^{3j - i}` of `(1 + 2) ^ {3j}` decrease from `i = j`. -/
private theorem weight_succ_le {j i : ℕ} (hi : j ≤ i) :
    (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) ≤ (3 * j).choose i * 2 ^ (3 * j - i) := by
  rcases lt_or_ge i (3 * j) with hlt | hge
  · have hrec := Nat.choose_succ_right_eq (3 * j) i
    have hpow : 2 ^ (3 * j - i) = 2 * 2 ^ (3 * j - (i + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    have key : (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) * (i + 1) ≤
        (3 * j).choose i * (2 * 2 ^ (3 * j - (i + 1))) * (i + 1) := by
      calc
        (3 * j).choose (i + 1) * 2 ^ (3 * j - (i + 1)) * (i + 1) =
            (3 * j).choose i * (3 * j - i) * 2 ^ (3 * j - (i + 1)) := by
          rw [← hrec]
          ring
        _ ≤ (3 * j).choose i * (2 * (i + 1)) * 2 ^ (3 * j - (i + 1)) := by
          gcongr
          omega
        _ = (3 * j).choose i * (2 * 2 ^ (3 * j - (i + 1))) * (i + 1) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos i)
  · rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
    exact Nat.zero_le _

/-- The middle weight `C(3j, j) 2^{2j}` is the largest weight of `(1 + 2) ^ {3j}`. -/
private theorem weight_le_middle (j i : ℕ) :
    (3 * j).choose i * 2 ^ (3 * j - i) ≤ (3 * j).choose j * 2 ^ (3 * j - j) := by
  rcases le_total i j with hij | hij
  · have key : ∀ k i, i + k = j →
        (3 * j).choose i * 2 ^ (3 * j - i) ≤ (3 * j).choose j * 2 ^ (3 * j - j) := by
      intro k
      induction k with
      | zero => intro i hi; subst hi; rfl
      | succ k ih =>
        intro i hi
        exact (weight_le_succ (by omega)).trans (ih (i + 1) (by omega))
    exact key (j - i) i (by omega)
  · have key : ∀ k, (3 * j).choose (j + k) * 2 ^ (3 * j - (j + k)) ≤
        (3 * j).choose j * 2 ^ (3 * j - j) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => exact (weight_succ_le (i := j + k) (by omega)).trans ih
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact key k

/-- **The middle binomial coefficient of `(1 + 2) ^ {3j}`**: `27^j ≤ C(3j, j) 4^j (3j + 1)`, since
the middle weight is the largest of the `3 j + 1` weights summing to `27^j`. -/
theorem pow_le_choose_mul (j : ℕ) : 27 ^ j ≤ (3 * j).choose j * 4 ^ j * (3 * j + 1) := by
  have hsum : 27 ^ j = ∑ i ∈ range (3 * j + 1), (3 * j).choose i * 2 ^ (3 * j - i) := by
    have h := add_pow (1 : ℕ) 2 (3 * j)
    rw [show (1 : ℕ) + 2 = 3 by rfl, show (3 : ℕ) ^ (3 * j) = 27 ^ j by
      rw [pow_mul]; norm_num] at h
    rw [h]
    exact sum_congr rfl fun i _ => by rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [hsum]
  calc
    ∑ i ∈ range (3 * j + 1), (3 * j).choose i * 2 ^ (3 * j - i) ≤
        ∑ _i ∈ range (3 * j + 1), (3 * j).choose j * 2 ^ (3 * j - j) :=
      sum_le_sum fun i _ => weight_le_middle j i
    _ = (3 * j).choose j * 4 ^ j * (3 * j + 1) := by
      rw [sum_const, card_range, smul_eq_mul, show 3 * j - j = 2 * j by omega, pow_mul]
      norm_num
      ring

/-- From distance `j`, the biased walk reaches `0` within `3 j` steps with probability at least
`2^{-j} / (3 j + 1)`. -/
theorem inv_le_hit (j : ℕ) : (1 / 2 : ℝ) ^ j / (3 * j + 1) ≤ hit (3 * j) j := by
  have hpath := choose_mul_le_hit j (2 * j) j (by omega)
  rw [show j + 2 * j = 3 * j by omega] at hpath
  refine le_trans ?_ hpath
  have hbin : (27 : ℝ) ^ j ≤ (3 * j).choose j * 4 ^ j * (3 * j + 1) := by
    exact_mod_cast pow_le_choose_mul j
  have hpos : (0 : ℝ) < 3 * j + 1 := by positivity
  have hx : (0 : ℝ) < 2 ^ j := by positivity
  have hy : (0 : ℝ) < 27 ^ j := by positivity
  rw [show (4 : ℝ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num] at hbin
  have hweight : ((3 * j).choose j : ℝ) * (1 / 3) ^ (2 * j) * (2 / 3) ^ j =
      (3 * j).choose j * (2 ^ j / 27 ^ j) := by
    rw [mul_assoc, pow_mul, ← mul_pow]
    norm_num [div_pow]
  rw [hweight, div_le_iff₀ hpos, one_div_pow, div_le_iff₀ hx]
  have hrhs : ((3 * j).choose j : ℝ) * (2 ^ j / 27 ^ j) * (3 * j + 1) * 2 ^ j =
      ((3 * j).choose j * (2 ^ j * 2 ^ j) * (3 * j + 1)) / 27 ^ j := by
    field_simp
  rw [hrhs, le_div_iff₀ hy, one_mul]
  exact hbin

/-! ### The local search dominates the biased walk -/

/-- Flipping one variable changes the Hamming distance to `τ` by one: it grows if the variable
agreed with `τ` and shrinks otherwise. -/
theorem hammingDist_flip (σ τ : V → Bool) (v : V) :
    hammingDist (flip σ v) τ =
      if σ v = τ v then hammingDist σ τ + 1 else hammingDist σ τ - 1 := by
  unfold hammingDist
  split_ifs with h
  · have hset : (univ.filter fun i => flip σ v i ≠ τ i) =
        insert v (univ.filter fun i => σ i ≠ τ i) := by
      ext i
      by_cases hi : i = v
      · subst hi
        cases hσ : σ i <;> cases hτ : τ i <;> simp_all [flip]
      · simp [flip, Function.update_apply, hi]
    rw [hset, card_insert_of_notMem (by simp [h])]
  · have hset : (univ.filter fun i => flip σ v i ≠ τ i) =
        (univ.filter fun i => σ i ≠ τ i).erase v := by
      ext i
      by_cases hi : i = v
      · subst hi
        cases hσ : σ i <;> cases hτ : τ i <;> simp_all [flip]
      · simp [flip, Function.update_apply, hi]
    rw [hset, card_erase_of_mem (by simp [h])]

omit [Fintype V] [DecidableEq V] in
theorem succeedProb_pure (φ : CNF V) (σ : V → Bool) :
    succeedProb φ (PMF.pure σ) = if φ.eval σ = true then 1 else 0 := by
  rw [succeedProb, PMF.toOuterMeasure_pure_apply]
  split_ifs <;> simp_all

omit [Fintype V] [DecidableEq V] in
theorem succeedProb_nonneg (φ : CNF V) (μ : PMF (V → Bool)) : 0 ≤ succeedProb φ μ :=
  ENNReal.toReal_nonneg

omit [Fintype V] in
/-- The success probability of one step followed by `t` more is the average over the literal
occurrences of the chosen clause. -/
private theorem succeedProb_flipStep_bind (φ : CNF V) {c : Clause V} (hc : c.length ≠ 0)
    (σ : V → Bool) (μ : (V → Bool) → PMF (V → Bool)) :
    haveI : NeZero c.length := ⟨hc⟩
    succeedProb φ ((flipStep c σ).bind μ) =
      ∑ i : Fin c.length, (c.length : ℝ)⁻¹ * succeedProb φ (μ (flip σ (c.get i).1)) := by
  have : NeZero c.length := ⟨hc⟩
  simp only [flipStep, hc, ↓reduceDIte]
  rw [PMF.bind_map, succeedProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Function.comp_apply, succeedProb]

/-- **The local search dominates the biased walk.** If `σ⋆` satisfies `φ` and every clause of `φ`
has at most three literals, then `t` steps from `σ` reach a satisfying assignment with probability
at least `hit t (dist σ σ⋆)`. -/
theorem hit_le_succeedProb {φ : CNF V} {σs : V → Bool} (hs : φ.eval σs = true)
    (h3 : ∀ c ∈ φ, c.length ≤ 3) (t : ℕ) (σ : V → Bool) :
    hit t (hammingDist σ σs) ≤ succeedProb φ (walk φ t σ) := by
  induction t generalizing σ with
  | zero =>
    rw [walk, succeedProb_pure]
    rcases Nat.eq_zero_or_pos (hammingDist σ σs) with h0 | hpos
    · rw [hammingDist_eq_zero.mp h0]
      simp [hs]
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hd, hit_zero_succ]
      split_ifs <;> norm_num
  | succ t ih =>
    rw [walk]
    cases hfu : firstUnsat φ σ with
    | none =>
      have hsat : φ.eval σ = true := by
        rw [CNF.eval_eq_true_iff]
        intro c hc
        have := List.find?_eq_none.mp hfu c hc
        simpa using this
      simp only [succeedProb_pure, hsat, ite_true]
      exact hit_le_one _ _
    | some c =>
      have hc : c ∈ φ := List.mem_of_find?_eq_some hfu
      have hcσ : ∀ l ∈ c, σ l.1 ≠ l.2 := by
        have := List.find?_some hfu
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
        intro l hl hl'
        have hsat : c.eval σ = true := (Clause.eval_eq_true_iff σ c).mpr ⟨l, hl, hl'⟩
        rw [hsat] at this
        exact absurd this (by decide)
      obtain ⟨l, hl, hls⟩ :=
        (Clause.eval_eq_true_iff σs c).mp ((CNF.eval_eq_true_iff σs φ).mp hs c hc)
      have hne : σ l.1 ≠ σs l.1 := by rw [hls]; exact hcσ l hl
      have hdpos : hammingDist σ σs ≠ 0 := fun h => hne (congrFun (hammingDist_eq_zero.mp h) _)
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hdpos
      have hlen : c.length ≠ 0 := (List.length_pos_of_mem hl).ne'
      have : NeZero c.length := ⟨hlen⟩
      rw [hd, hit_succ_succ, succeedProb_flipStep_bind φ hlen]
      set f : Fin c.length → ℝ := fun i => succeedProb φ (walk φ t (flip σ (c.get i).1))
      obtain ⟨i₀, hi₀⟩ := List.get_of_mem hl
      have hterm : ∀ i, hit t (d + 2) ≤ f i := by
        intro i
        refine le_trans (hit_antitone t ?_) (ih _)
        rw [hammingDist_flip, hd]
        split_ifs <;> omega
      have hterm₀ : hit t d ≤ f i₀ := by
        refine le_trans (le_of_eq ?_) (ih _)
        rw [hi₀, hammingDist_flip, hd]
        simp [hne]
      have hsum : hit t d + ((c.length : ℝ) - 1) * hit t (d + 2) ≤ ∑ i, f i := by
        rw [← add_sum_erase _ _ (mem_univ i₀)]
        have hcard : ((c.length : ℝ) - 1) * hit t (d + 2) =
            ∑ _i ∈ univ.erase i₀, hit t (d + 2) := by
          rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hlen), Nat.cast_one]
        rw [hcard]
        exact add_le_add hterm₀ (sum_le_sum fun i _ => hterm i)
      rw [← mul_sum]
      have hm3 : (c.length : ℝ) ≤ 3 := by exact_mod_cast h3 c hc
      have hm1 : (1 : ℝ) ≤ c.length := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hlen
      have hAB : hit t (d + 2) ≤ hit t d := hit_antitone t (by omega)
      have hB := hit_nonneg t (d + 2)
      calc
        hit t d / 3 + 2 * hit t (d + 2) / 3 ≤
            (c.length : ℝ)⁻¹ * (hit t d + ((c.length : ℝ) - 1) * hit t (d + 2)) := by
          rw [inv_mul_eq_div, le_div_iff₀ (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hm3)]
        _ ≤ (c.length : ℝ)⁻¹ * ∑ i, f i := by gcongr

/-! ### Schöning's bound -/

omit [DecidableEq V] in
/-- Averaging `2^{-dist(σ, τ)}` over all assignments `σ` gives `(3/2)^n`, a product over the
coordinates. -/
theorem sum_half_pow_hammingDist [DecidableEq V] (τ : V → Bool) :
    ∑ σ : V → Bool, (1 / 2 : ℝ) ^ hammingDist σ τ = (3 / 2) ^ Fintype.card V := by
  have hprod (σ : V → Bool) :
      (1 / 2 : ℝ) ^ hammingDist σ τ = ∏ i, if σ i = τ i then 1 else 1 / 2 := by
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    rfl
  simp only [hprod]
  rw [← Fintype.prod_sum (fun i b => if b = τ i then (1 : ℝ) else 1 / 2)]
  have hb (i : V) : ∑ b : Bool, (if b = τ i then (1 : ℝ) else 1 / 2) = 3 / 2 := by
    rw [Fintype.sum_bool]
    cases τ i <;> norm_num
  simp only [hb, prod_const, card_univ]

/-- **Schöning's theorem for 3-SAT, one trial.** For a satisfiable CNF formula on `n` variables
whose clauses have at most three literals, one trial of Schöning's algorithm finds a satisfying
assignment with probability at least `(3 / 4) ^ n / (3 n + 1)`. -/
theorem trial_success {φ : CNF V} (hφ : φ.Satisfiable) (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    (3 / 4 : ℝ) ^ Fintype.card V / (3 * Fintype.card V + 1) ≤ succeedProb φ (trial φ) := by
  obtain ⟨σs, hs⟩ := hφ
  set n := Fintype.card V
  have hlow (σ : V → Bool) :
      (1 / 2 : ℝ) ^ hammingDist σ σs / (3 * n + 1) ≤ succeedProb φ (walk φ (3 * n) σ) := by
    have hd : hammingDist σ σs ≤ n := hammingDist_le_card_fintype
    calc
      (1 / 2 : ℝ) ^ hammingDist σ σs / (3 * n + 1) ≤
          (1 / 2 : ℝ) ^ hammingDist σ σs / (3 * hammingDist σ σs + 1) := by
        gcongr
      _ ≤ hit (3 * hammingDist σ σs) (hammingDist σ σs) := inv_le_hit _
      _ ≤ hit (3 * n) (hammingDist σ σs) := hit_monotone _ (by omega)
      _ ≤ _ := hit_le_succeedProb hs h3 _ σ
  rw [trial, succeedProb, Cslib.Probability.PMF.toOuterMeasure_bind_toReal]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (3 / 4 : ℝ) ^ n / (3 * n + 1) =
        ∑ σ : V → Bool, ((2 : ℝ) ^ n)⁻¹ * ((1 / 2 : ℝ) ^ hammingDist σ σs / (3 * n + 1)) := by
      rw [← mul_sum, ← sum_div, sum_half_pow_hammingDist, ← mul_div_assoc, ← inv_pow, ← mul_pow]
      norm_num
    _ ≤ ∑ σ : V → Bool, ((2 : ℝ) ^ n)⁻¹ * succeedProb φ (walk φ (3 * n) σ) := by
      gcongr with σ
      exact hlow σ

end Cslib.Complexity.Schoening
