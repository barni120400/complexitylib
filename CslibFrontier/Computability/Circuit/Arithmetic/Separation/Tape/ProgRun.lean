/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.ReduceOption

/-!
# From programs to runs

A program (a rational series on the channels) is turned into a finite automaton whose matched runs
emit the letters of the program and then pad with idle (`none`) steps.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.ProgRun`.

## Main definitions

* `Tape.Series.idle`: pad a series with trailing `none` letters.

## Main results

* `Tape.RatLe.idle`: dimension increases by at most `1` under trailing idle padding.
* `Tape.exists_run`: a rational series gives an automaton whose `runVal` sums `hat P (tup W u)`.
* `Tape.exists_run_val`: a bounded program is realized by an automaton of dimension `≤ n + 3`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset

section Idle

variable {F : Type*} [CommRing F] {Ω : Type*}

/-- The words of a series, followed by arbitrarily many idle (`none`) letters. -/
@[expose] def Series.idle (P : Series F Ω) : Series F (Option Ω) :=
  Series.mul
    (fun o => if o.all Option.isSome then P o.reduceOption else 0)
    (fun o => if o.all Option.isNone then 1 else 0)

theorem RatLe.idle {n : ℕ} {P : Series F Ω} (hP : RatLe n P) :
    RatLe (n + 1) (Series.idle P) := by
  refine RatLe.mul ?_ ?_
  · obtain ⟨Q, _, r, hn, rfl⟩ := hP
    refine ⟨Q, inferInstance, ⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩, hn, ?_⟩
    have key : ∀ o : List (Option Ω),
        (⟨r.lam, fun a => a.elim 0 r.mu, r.gam⟩ : Rep F (Option Ω) Q).tail o =
          if o.all Option.isSome then r.tail o.reduceOption else 0 := by
      intro o
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a with
        | none => simp
        | some a =>
          by_cases h : o.all Option.isSome
          · simp only [h, ite_true, List.all_cons, Option.isSome_some, Bool.true_and,
              List.reduceOption_cons_of_some, Option.elim]
            rfl
          · simp [h]
    funext o
    rw [Rep.series, key]
    by_cases h : o.all Option.isSome
    · simp only [h, ite_true]; rfl
    · simp [h]
  · refine ⟨Unit, inferInstance, ⟨1, fun a => a.elim 1 fun _ => 0, 1⟩, by simp, ?_⟩
    have key : ∀ o : List (Option Ω),
        (⟨1, fun a => a.elim 1 fun _ => 0, 1⟩ : Rep F (Option Ω) Unit).tail o =
          if o.all Option.isNone then 1 else 0 := by
      intro o
      induction o with
      | nil => rfl
      | cons a o ih =>
        rw [Rep.tail, ih]
        cases a <;> simp
    funext o
    rw [Rep.series, key]
    by_cases h : o.all Option.isNone <;> simp [h]

theorem idle_apply (P : Series F Ω) (w : List Ω) (j : ℕ) :
    Series.idle P (w.map some ++ List.replicate j none) = P w := by
  rw [Series.idle, Series.mul, Finset.sum_eq_single w.length]
  · rw [List.take_left' (by simp), List.drop_left' (by simp)]
    simp [List.reduceOption]
  · intro k hk hne
    rw [mem_range, List.length_append, List.length_map, List.length_replicate] at hk
    rcases lt_or_gt_of_ne hne with h | h
    · have hmem : some w[k] ∈ (w.map some ++ List.replicate j none).drop k := by
        rw [List.drop_append_of_le_length (by simp; omega), List.mem_append, ← List.map_drop]
        left
        rw [List.mem_map]
        refine ⟨w[k], ?_, rfl⟩
        rw [List.drop_eq_getElem_cons h]
        exact List.mem_cons_self
      have hn : ¬ ((w.map some ++ List.replicate j none).drop k).all Option.isNone = true := by
        intro hall
        have := List.all_eq_true.1 hall _ hmem
        simp at this
      rw [ite_eq_right hn, mul_zero]
    · have hmem : none ∈ (w.map some ++ List.replicate j none).take k := by
        rw [List.take_append, List.mem_append]
        right
        rw [List.length_map, List.take_replicate, List.mem_replicate]
        exact ⟨by omega, rfl⟩
      have hn : ¬ ((w.map some ++ List.replicate j none).take k).all Option.isSome = true := by
        intro hall
        have := List.all_eq_true.1 hall _ hmem
        simp at this
      rw [ite_eq_right hn, zero_mul]
  · intro h
    exfalso
    apply h
    rw [mem_range, List.length_append, List.length_map]
    omega

theorem idle_ne_zero (P : Series F Ω) (o : List (Option Ω)) (h : Series.idle P o ≠ 0) :
    ∃ (w : List Ω) (j : ℕ), o = w.map some ++ List.replicate j none := by
  unfold Series.idle Series.mul at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  beta_reduce at hk
  have h1 : (o.take k).all Option.isSome = true := by
    by_contra hn
    rw [ite_eq_right hn, zero_mul] at hk
    exact hk rfl
  have h2 : (o.drop k).all Option.isNone = true := by
    by_contra hn
    rw [ite_eq_right hn, mul_zero] at hk
    exact hk rfl
  refine ⟨(o.take k).reduceOption, (o.drop k).length, ?_⟩
  have e1 : ∀ l : List (Option Ω), l.all Option.isSome = true → l.reduceOption.map some = l := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      cases a with
      | none => simp at hl
      | some a =>
        simp only [List.all_cons, Option.isSome_some, Bool.true_and] at hl
        rw [List.reduceOption_cons_of_some, List.map_cons, ih hl]
  have e2 : ∀ l : List (Option Ω), l.all Option.isNone = true →
      List.replicate l.length none = l := by
    intro l hl
    symm
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun a ha => ?_⟩
    have := List.all_eq_true.1 hl a ha
    simpa using this
  rw [e1 _ h1, e2 _ h2, List.take_append_drop]

end Idle

theorem sum_length_tup {Γ S J : Type*} [Fintype S] [Fintype J]
    (W : S → List Γ) (u : J → List Γ) :
    ∑ z, (tup W u z).length = 2 * ∑ s, (W s).length + ∑ j, (u j).length := by
  rw [Fintype.sum_equiv (chSumEquiv S J) _
    (Sum.elim (fun x : S × Bool => (W x.1).length) fun j => (u j).length)]
  · rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.mul_sum]
    simp [two_mul]
  · intro z
    cases z <;> rfl

theorem ofFn_getElem? {Ω : Type*} (w : List Ω) (t : ℕ) (h : w.length ≤ t) :
    List.ofFn (fun k : Fin t => w[(k : ℕ)]?) =
      w.map some ++ List.replicate (t - w.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    rw [List.getElem_ofFn]
    by_cases hk : k < w.length
    · rw [List.getElem_append_left (by simpa using hk)]
      simp [hk]
    · rw [List.getElem_append_right (by simpa using hk)]
      simp; omega

theorem emit_idle {Γ S J : Type*} [DecidableEq S] [DecidableEq J]
    (w : List (Ch S J × Γ)) (j : ℕ) :
    emit (w.map some ++ List.replicate j none) = proj w := by
  have hred : (w.map some ++ List.replicate j none).reduceOption = w := by
    rw [List.reduceOption_append]
    simp [List.reduceOption]
  rw [emit, hred]

section Runs

variable {F Γ S J : Type*} [CommRing F] [Fintype Γ] [DecidableEq Γ]
  [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]

/-- **From programs to runs.** A rational series of dimension at most `n` gives an automaton of
dimension at most `n + 3` whose value on runs of length `t ≥ 1` matches `hat P` summed over
tape contents fitting inside `t` steps. -/
theorem exists_run {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F)
      (i e : Q), Fintype.card Q ≤ n + 3 ∧ ∀ t, 1 ≤ t → ∀ u : J → List Γ,
        runVal mu i e t u =
          ∑ W ∈ (contents S Γ t).filter
              (fun W => 2 * ∑ s, (W s).length + ∑ j, (u j).length ≤ t),
            hat P (tup W u) := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, hmu⟩ := hP.idle.normal
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t ht u => ?_⟩
  have hne : ∀ o : Fin t → Letter S J Γ, List.ofFn o ≠ [] := by
    intro o h
    have hlen := congrArg List.length h
    simp at hlen
    omega
  rw [runVal, Finset.sum_congr rfl fun o _ => by rw [hmu _ (hne o)]]
  simp only [hat]
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_of_injOn (fun x k => x.2[(k : ℕ)]?) ?_ (by simp) ?_ ?_
  · rintro ⟨W, w⟩ hx ⟨W', w'⟩ hx' h
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib] at hx hx'
    have l1 : w.length ≤ t := by
      rw [← sum_length_proj w, hx.2, sum_length_tup]; exact hx.1.2
    have l2 : w'.length ≤ t := by
      rw [← sum_length_proj w', hx'.2, sum_length_tup]; exact hx'.1.2
    have hw : w = w' := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < t
      · exact congrFun h ⟨k, hk⟩
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    subst hw
    have hW : W = W' := by
      funext s
      exact congrFun (hx.2.symm.trans hx'.2) (.tp s false)
    rw [hW]
  · intro o _ ho
    by_contra hcon
    have hm : Matched (List.ofFn o) u := by
      by_contra hm
      exact hcon (ite_eq_right hm)
    rw [ite_eq_left hm] at hcon
    obtain ⟨w, j, hw⟩ := idle_ne_zero P _ hcon
    have hlen : w.length + j = t := by
      have := congrArg List.length hw
      simpa using this.symm
    apply ho
    have hproj : proj w = tup (fun s => proj w (.tp s false)) u := by
      rw [Matched, hw, emit_idle] at hm
      funext z
      cases z with
      | tp s b =>
        cases b with
        | false => rfl
        | true => exact (hm.1 s).symm
      | inp j => exact hm.2 j
    have hlen2 := sum_length_proj w
    rw [hproj, sum_length_tup] at hlen2
    refine ⟨⟨fun s => proj w (.tp s false), w⟩, ?_, ?_⟩
    · simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_fib, mem_contents]
      exact ⟨⟨by omega, by omega⟩, hproj⟩
    · apply List.ofFn_injective
      rw [hw, ofFn_getElem? w t (by omega)]
      congr 2
      omega
  · rintro ⟨W, w⟩ hx
    simp only [mem_sigma, mem_filter, mem_fib] at hx
    have l1 : w.length ≤ t := by
      rw [← sum_length_proj w, hx.2, sum_length_tup]; exact hx.1.2
    rw [ofFn_getElem? w t l1, ite_eq_left _, idle_apply]
    rw [Matched, emit_idle, hx.2]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- A bounded rational program is realized by a weighted automaton of dimension at most `n + 3`. -/
theorem exists_run_val {n : ℕ} {P : Series F (Ch S J × Γ)} (hP : RatLe n P) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S J Γ → Matrix Q Q F)
      (i e : Q), Fintype.card Q ≤ n + 3 ∧ ∀ (t₀ t : ℕ) (u : J → List Γ), Bdd t₀ P u →
        2 * t₀ + ∑ j, (u j).length + 1 ≤ t → runVal mu i e t u = val t₀ P u := by
  obtain ⟨Q, i1, i2, mu, i, e, hcard, H⟩ := exists_run hP
  refine ⟨Q, i1, i2, mu, i, e, hcard, fun t₀ t u hb ht => ?_⟩
  rw [H t (by omega) u, val]
  symm
  apply Finset.sum_subset
  · intro W hW
    rw [mem_contents] at hW
    rw [mem_filter, mem_contents]
    omega
  · intro W _ hW
    by_contra hne
    exact hW (mem_contents.2 (hb W hne))

end Runs

end Cslib.Circuits.Arithmetic.Separation.Tape
