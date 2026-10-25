/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Count

/-!
# Occurrence ranks in finite lists

The rank of an occurrence at index `i` is the number of equal entries strictly before it. These
ranks assign distinct ports to repeated occurrences of one graph vertex without using choice.

## Main results

* `List.count_take_getElem_lt_count`: an occurrence rank is smaller than the total count.
* `List.eq_of_getElem_eq_of_count_take_eq`: an entry and its occurrence rank identify its index.
-/

@[expose] public section

namespace List

/-- The number of preceding equal entries is strictly smaller than the total number. -/
theorem count_take_getElem_lt_count {α : Type*} [DecidableEq α] {l : List α} {i : ℕ}
    (hi : i < l.length) : (l.take i).count l[i] < l.count l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih (i := i) (by simpa using hi)
      simp only [take_succ_cons, getElem_cons_succ, count_cons]
      omega

/-- An entry together with its occurrence rank determines its index. -/
theorem eq_of_getElem_eq_of_count_take_eq {α : Type*} [DecidableEq α] {l : List α}
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (heq : l[i] = l[j])
    (hrank : (l.take i).count l[i] = (l.take j).count l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [getElem_cons_zero, getElem_cons_succ] at heq
        simp only [take_zero, count_nil, take_succ_cons, getElem_cons_zero,
          getElem_cons_succ, ← heq, count_cons_self] at hrank
        omega
    | succ i =>
      cases j with
      | zero =>
        simp only [getElem_cons_zero, getElem_cons_succ] at heq
        simp only [take_zero, count_nil, take_succ_cons, getElem_cons_zero,
          getElem_cons_succ, heq, count_cons_self] at hrank
        omega
      | succ j =>
        simp only [getElem_cons_succ] at heq
        simp only [take_succ_cons, getElem_cons_succ, count_cons, heq] at hrank
        exact congrArg Nat.succ
          (ih (by simpa using hi) (by simpa using hj) heq (by rw [heq]; omega))

end List
