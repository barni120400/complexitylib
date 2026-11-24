/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Tactic.Ring

/-!
# Binary numbers in most-significant-bit-first order

Complements `Cslib.BitString.binaryValue` and `Cslib.BitString.binaryWord` with concatenation,
fixed-width padding `Uni.bin` (of unconditional length `L`), carry-cut increment identity
`Uni.binaryValue_succ`, existence (`Uni.exists_cut`), and uniqueness (`Uni.cut_unique`) of the
carry position used by the universal pointer-machine counter tape.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.Bin`.

## Main definitions

* `Uni.bin`: the `L`-bit big-endian binary word of a natural number (always of length `L`).

## Main results

* `Uni.length_bin`: `(bin L n).length = L`.
* `Uni.binaryValue_append`, `Uni.binaryValue_cons`: splitting `binaryValue` at `++` and `::`.
* `Uni.binaryValue_bin`, `Uni.bin_binaryValue`, `Uni.bin_eq_binaryWord`: inversion lemmas linking
  `Uni.bin` to `Cslib.BitString.binaryValue` and `Cslib.BitString.binaryWord`.
* `Uni.binaryValue_succ`: flipping trailing `false, true, …, true` to `true, false, …, false`
  adds `1`.
* `Uni.exists_cut`, `Uni.cut_unique`: unique decomposition of a non-maximal binary word before
  its rightmost `false`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Cslib.BitString (binaryValue binaryValue_binaryWord binaryValue_injective_of_length_eq
  binaryValue_lt_two_pow binaryValue_replicate_false_append binaryValue_replicate_true
  binaryValue_snoc binaryWord length_binaryWord)

theorem binaryValue_append (u v : List Bool) :
    binaryValue (u ++ v) = binaryValue u * 2 ^ v.length + binaryValue v := by
  induction v using List.reverseRecOn with
  | nil => simp [binaryValue]
  | append_singleton v b ih =>
    rw [← List.append_assoc, binaryValue_snoc, binaryValue_snoc, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem binaryValue_cons (b : Bool) (w : List Bool) :
    binaryValue (b :: w) = (if b then 2 ^ w.length else 0) + binaryValue w := by
  have h := binaryValue_append [b] w
  simp only [List.singleton_append] at h
  rw [h]
  cases b <;> simp [binaryValue]

theorem binaryValue_replicate_false (k : ℕ) :
    binaryValue (List.replicate k false) = 0 := by
  have h := binaryValue_replicate_false_append k []
  simpa [binaryValue] using h

/-- The fixed-width `L`-bit big-endian binary word of `n` (most significant bit first).
Unlike `Cslib.BitString.binaryWord`, this always has length `L` (matching `binaryWord L n`
whenever `n < 2 ^ L`, see `bin_eq_binaryWord`). -/
@[expose] def bin : ℕ → ℕ → List Bool
  | 0, _ => []
  | L + 1, n => decide (2 ^ L ≤ n) :: bin L (if 2 ^ L ≤ n then n - 2 ^ L else n)

theorem length_bin (L n : ℕ) : (bin L n).length = L := by
  induction L generalizing n with
  | zero => rfl
  | succ L ih => rw [bin, List.length_cons, ih]

theorem binaryValue_bin {L n : ℕ} (h : n < 2 ^ L) : binaryValue (bin L n) = n := by
  induction L generalizing n with
  | zero =>
    simp only [pow_zero] at h
    have : n = 0 := by omega
    subst this
    rfl
  | succ L ih =>
    rw [bin, binaryValue_cons, length_bin]
    rw [pow_succ] at h
    by_cases hn : 2 ^ L ≤ n
    · simp only [hn, decide_true, ↓reduceIte]
      rw [ih (by omega)]
      omega
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih (by omega)]
      omega

theorem bin_binaryValue (w : List Bool) : bin w.length (binaryValue w) = w :=
  binaryValue_injective_of_length_eq (length_bin _ _)
    (binaryValue_bin (binaryValue_lt_two_pow w))

theorem bin_eq_binaryWord {L n : ℕ} (h : n < 2 ^ L) : bin L n = binaryWord L n :=
  binaryValue_injective_of_length_eq
    (by rw [length_bin, length_binaryWord h])
    (by rw [binaryValue_bin h, binaryValue_binaryWord])

/-- Adding `1` to a big-endian word replaces `false :: true^k` by `true :: false^k`. -/
theorem binaryValue_succ (u : List Bool) (k : ℕ) :
    binaryValue (u ++ true :: List.replicate k false) =
      binaryValue (u ++ false :: List.replicate k true) + 1 := by
  have h := binaryValue_replicate_true k
  rw [binaryValue_append, binaryValue_append, binaryValue_cons, binaryValue_cons,
    binaryValue_replicate_false]
  simp only [↓reduceIte, Bool.false_eq_true, List.length_cons, List.length_replicate]
  omega

/-- Every non-maximal big-endian word ends with `false` followed by `true`s. -/
theorem exists_cut {w : List Bool} (h : binaryValue w + 1 < 2 ^ w.length) :
    ∃ u k, w = u ++ false :: List.replicate k true := by
  induction w using List.reverseRecOn with
  | nil => simp [binaryValue] at h
  | append_singleton w b ih =>
    cases b
    · exact ⟨w, 0, rfl⟩
    · rw [binaryValue_snoc, List.length_append, List.length_singleton, pow_succ] at h
      simp only [Bool.toNat_true] at h
      obtain ⟨u, k, rfl⟩ := ih (by omega)
      refine ⟨u, k + 1, ?_⟩
      rw [List.replicate_succ', List.append_assoc]
      rfl

theorem cut_unique {u u' : List Bool} {k k' : ℕ}
    (h : u ++ false :: List.replicate k true = u' ++ false :: List.replicate k' true) :
    u = u' ∧ k = k' := by
  have h1 := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h1
  have key : ∀ (k k' : ℕ) (a b : List Bool),
      List.replicate k true ++ false :: a = List.replicate k' true ++ false :: b →
        k = k' ∧ a = b := by
    intro k
    induction k with
    | zero =>
      intro k' a b e
      cases k' with
      | zero => simpa using e
      | succ k' => simp [List.replicate_succ] at e
    | succ k ih =>
      intro k' a b e
      cases k' with
      | zero => simp [List.replicate_succ] at e
      | succ k' =>
        simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at e
        obtain ⟨h2, h3⟩ := ih k' a b e
        exact ⟨by rw [h2], h3⟩
  obtain ⟨h2, h3⟩ := key k k' _ _ h1
  exact ⟨List.reverse_injective h3, h2⟩

end Cslib.Circuits.Arithmetic.Separation.Uni
