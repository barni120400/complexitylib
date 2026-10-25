/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.List.OfFn
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Mathlib.Data.Vector.Basic

/-!
# Uniform binary strings

Uniform sampling from `Fin n → Bool`, represented as a list. The recursive equations connect
this finite uniform distribution to a program drawing one independent fair bit at a time.

## Main definitions

* `Cslib.BitString.uniformList`: uniform fixed-length words represented as lists.

## Main results

* `Cslib.BitString.uniformList_succ`, `Cslib.BitString.uniformList_add`: independent decomposition.
* `Cslib.BitString.mem_support_uniformList_iff`: support is exactly the requested length.
* `Cslib.BitString.uniformList_map_of_bijective`: length-preserving permutations preserve
  uniformity.
* `Cslib.BitString.uniformList_map_apply`,
  `Cslib.BitString.toOuterMeasure_map_uniformList_toReal`: the probability of a value or event
  under a map of a uniform word is the fraction of words of that length mapping into it.
* `Cslib.BitString.zipWith_xor_self_left`, `Cslib.BitString.uniformOfFintype_bool_map_xor`,
  `Cslib.BitString.uniformList_map_zipWith_xor`,
  `Cslib.BitString.uniformList_map_take_zipWith_xor`: pointwise `List.zipWith xor` left-cancellation
  and `uniformList` invariance under one-time-pad masking.
* `Cslib.BitString.uniformList_apply_le`,
  `Cslib.BitString.toOuterMeasure_lookup_uniformList_le`: point-mass bound `1 / 2 ^ n` and
  finite-cache lookup union bound `cache.length * (1 / 2 ^ n)` for `uniformList n`.

## References

Adapted from Cslib/Probability/BitString.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, placed in the shared bit-string namespace.
-/

@[expose] public section

namespace Cslib.BitString

open Probability

/-- The uniform distribution on binary words of exactly `n` bits. -/
noncomputable def uniformList (n : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

/-- The uniform distribution on words of `0` bits is the point mass at the empty word. -/
@[simp] theorem uniformList_zero : uniformList 0 = PMF.pure [] := by
  simp [uniformList, PMF.map, Function.comp_def]

/-- A uniform nonempty string consists of a fair first bit and an independent uniform tail. -/
theorem uniformList_succ (n : ℕ) :
    uniformList (n + 1) = (PMF.uniformOfFintype Bool).bind
      (fun bit => (uniformList n).map (List.cons bit)) := by
  unfold uniformList
  rw [← PMF.uniformOfFintype_map_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)),
    PMF.map_comp, ← PMF.uniformOfFintype_prod]
  simp [PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.consEquiv]

/-- Concatenating independent uniform words gives a uniform word of the combined length. -/
theorem uniformList_add (m n : ℕ) :
    uniformList (m + n) = (uniformList m).bind
      (fun left => (uniformList n).map (left ++ ·)) := by
  induction m with
  | zero => simp [PMF.map, Function.comp_def]
  | succ m ih =>
    rw [Nat.succ_add, uniformList_succ, ih, uniformList_succ]
    simp [PMF.map_bind, PMF.bind_map, PMF.map_comp, PMF.bind_bind, Function.comp_def]

/-- Appending one independent fair bit gives a uniform word one bit longer. -/
theorem uniformList_snoc (n : ℕ) :
    uniformList (n + 1) = (uniformList n).bind
      (fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) := by
  rw [uniformList_add n 1, uniformList_succ 0]
  simp [PMF.map, Function.comp_def]

/-- Every sampled word has exactly the requested length. -/
theorem length_of_mem_support_uniformList {n : ℕ} {word : List Bool}
    (h : word ∈ (uniformList n).support) : word.length = n := by
  obtain ⟨bits, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp

/-- Every word of the requested length has positive uniform probability, and no other word does. -/
theorem mem_support_uniformList_iff {n : ℕ} {word : List Bool} :
    word ∈ (uniformList n).support ↔ word.length = n := by
  refine ⟨length_of_mem_support_uniformList, fun h => ?_⟩
  subst n
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨word.get, by simp, List.ofFn_get _⟩

/-- Splitting a uniform tape gives two independent tapes, also when either length is zero. -/
theorem uniformList_bind_split {α : Type*} (first second : ℕ)
    (next : List Bool → List Bool → PMF α) :
    (uniformList (first + second)).bind (fun tape => next (tape.take first) (tape.drop first)) =
      (uniformList first).bind (fun front => (uniformList second).bind (next front)) := by
  rw [uniformList_add, PMF.bind_bind]
  apply PMF.bind_congr_on_support
  intro front hfront
  rw [PMF.bind_map]
  simp only [Function.comp_def, ← length_of_mem_support_uniformList hfront,
    List.take_left, List.drop_left]

/-- A prefix of a uniform word is uniform, with no condition on the discarded suffix. -/
theorem uniformList_take {n k : ℕ} (hkn : k ≤ n) :
    (uniformList n).map (List.take k) = uniformList k := by
  rw [show n = k + (n - k) by lia, uniformList_add, PMF.map_bind]
  calc
    (uniformList k).bind (fun seed =>
        ((uniformList (n - k)).map (seed ++ ·)).map (List.take k)) =
        (uniformList k).bind PMF.pure := by
      apply PMF.bind_congr_on_support
      intro seed hseed
      have hlen := length_of_mem_support_uniformList hseed
      simp [Function.comp_def, ← hlen, PMF.map, PMF.bind_const]
    _ = _ := PMF.bind_pure _

/-- A length-preserving permutation sends a uniform word to a uniform word of the same length.
This is a distributional fact and makes no assumption about computing the inverse. -/
theorem uniformList_map_of_bijective (f : List Bool → List Bool) (hf : Function.Bijective f)
    (hlen : ∀ word, (f word).length = word.length) (n : ℕ) :
    (uniformList n).map f = uniformList n := by
  let e : List.Vector Bool n ≃ List.Vector Bool n :=
    (Equiv.ofBijective f hf).subtypeEquiv (fun word => by simp [hlen])
  let bits : (Fin n → Bool) ≃ (Fin n → Bool) :=
    (Equiv.vectorEquivFin Bool n).symm.trans (e.trans (Equiv.vectorEquivFin Bool n))
  have hbits (word : Fin n → Bool) : List.ofFn (bits word) = f (List.ofFn word) := by
    change List.ofFn (List.Vector.get (e (List.Vector.ofFn word))) = _
    rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
    change f (List.Vector.ofFn word).toList = _
    rw [List.Vector.toList_ofFn]
  calc
    (uniformList n).map f = ((PMF.uniformOfFintype (Fin n → Bool)).map bits).map List.ofFn := by
      simp only [uniformList, PMF.map_comp]
      congr 1
      funext word
      exact (hbits word).symm
    _ = uniformList n := by rw [PMF.uniformOfFintype_map_equiv]; rfl

/-- The probability of a value of a function of a uniform word is the fraction of the words of
that length giving it. -/
theorem uniformList_map_apply {β : Type*} [DecidableEq β] (f : List Bool → β) (n : ℕ)
    (b : β) : ((uniformList n).map f) b =
      ((Finset.univ.filter fun r : Fin n → Bool => f (List.ofFn r) = b).card : ENNReal) /
        2 ^ n := by
  rw [uniformList, PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Function.comp_apply, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]
  simp [eq_comm]

open Classical in
/-- The real probability that a function of a uniform word of length `n` lands in `S` is the
fraction of words of that length mapping into `S`. -/
theorem toOuterMeasure_map_uniformList_toReal {β : Type*} (f : List Bool → β) (n : ℕ)
    (S : Set β) :
    (((uniformList n).map f).toOuterMeasure S).toReal =
      ((Finset.univ.filter fun r : Fin n → Bool => f (List.ofFn r) ∈ S).card : ℝ) / 2 ^ n := by
  rw [uniformList, PMF.map_comp, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_toReal]
  simp [Function.comp_def, Set.mem_preimage]

/-- Pointwise XOR of equal-length bit lists is left-involutive:
`List.zipWith xor pad (List.zipWith xor pad msg) = msg`. -/
theorem zipWith_xor_self_left :
    ∀ pad msg : List Bool, pad.length = msg.length →
      List.zipWith xor pad (List.zipWith xor pad msg) = msg
  | [], [], _ => rfl
  | b :: pad, m :: msg, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, zipWith_xor_self_left pad msg h]
    cases b <;> cases m <;> rfl

/-- XORing a uniformly random bit with a fixed bit `b` preserves `PMF.uniformOfFintype Bool`. -/
theorem uniformOfFintype_bool_map_xor (b : Bool) :
    (PMF.uniformOfFintype Bool).map (fun bit => xor bit b) = PMF.uniformOfFintype Bool := by
  ext x
  cases b <;> cases x <;>
    simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]

/-- Pointwise XOR of a uniform `msg.length`-bit word with a fixed word `msg` preserves
`uniformList msg.length`. -/
theorem uniformList_map_zipWith_xor :
    ∀ msg : List Bool,
      (uniformList msg.length).map (fun pad => List.zipWith xor pad msg) =
        uniformList msg.length
  | [] => by simp [PMF.map]
  | b :: tail => by
    rw [List.length_cons, uniformList_succ, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, List.zipWith_cons_cons]
    have htail (bit : Bool) :
        (uniformList tail.length).map
          (fun pad => xor bit b :: List.zipWith xor pad tail) =
        ((uniformList tail.length).map
          (fun pad => List.zipWith xor pad tail)).map (List.cons (xor bit b)) := by
      simp [PMF.map_comp, Function.comp_def]
    simp_rw [htail, uniformList_map_zipWith_xor tail]
    have hcomp :
        (fun a => PMF.map (List.cons (xor a b)) (uniformList tail.length)) =
          (fun bit' => (uniformList tail.length).map (List.cons bit')) ∘
            (fun bit => xor bit b) := rfl
    rw [hcomp, ← PMF.bind_map, uniformOfFintype_bool_map_xor b]

/-- Pointwise XOR of `pad.take n` for a uniform `n`-bit word `pad` with an `n`-bit word `msg`
preserves `uniformList n`. -/
theorem uniformList_map_take_zipWith_xor {n : ℕ} {msg : List Bool} (hmsg : msg.length = n) :
    (uniformList n).map (fun pad => List.zipWith xor (pad.take n) msg) =
      uniformList n := by
  have hcongr :
      (uniformList n).map (fun pad => List.zipWith xor (pad.take n) msg) =
        (uniformList n).map (fun pad => List.zipWith xor pad msg) := by
    rw [PMF.map, PMF.map]
    refine PMF.bind_congr_on_support _ _ _ fun pad hpad => ?_
    dsimp only [Function.comp_def]
    rw [List.take_of_length_le (length_of_mem_support_uniformList hpad).le]
  rw [hcongr, ← hmsg, uniformList_map_zipWith_xor]

/-- Every candidate word `r` has probability at most `1 / 2 ^ n` under `uniformList n`. -/
theorem uniformList_apply_le (n : ℕ) (r : List Bool) :
    uniformList n r ≤ (1 : ENNReal) / 2 ^ n := by
  have h := uniformList_map_apply id n r
  simp only [PMF.map_id, id_eq] at h
  rw [h]
  gcongr
  norm_cast
  exact Finset.card_le_one.mpr fun a ha b hb =>
    List.ofFn_injective ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)

/-- Union bound on finite-cache lookups: a uniform `n`-bit word hits the domain of a finite
association list `cache` with outer measure at most `cache.length * (1 / 2 ^ n)`. -/
theorem toOuterMeasure_lookup_uniformList_le {V : Type*} (n : ℕ)
    (cache : List (List Bool × V)) :
    (uniformList n).toOuterMeasure {r | (cache.lookup r).isSome} ≤
      (cache.length : ENNReal) * ((1 : ENNReal) / 2 ^ n) := by
  induction cache with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨r₀, pad₀⟩
    calc (uniformList n).toOuterMeasure
          {r | (((r₀, pad₀) :: rest).lookup r).isSome}
        ≤ (uniformList n).toOuterMeasure
          ({r | r = r₀} ∪ {r | (rest.lookup r).isSome}) := by
          refine (uniformList n).toOuterMeasure.mono fun r hr => ?_
          have hr' : (((r₀, pad₀) :: rest).lookup r).isSome = true := hr
          rw [List.lookup_cons] at hr'
          by_cases h : r = r₀
          · exact Or.inl h
          · rw [beq_false_of_ne h] at hr'
            exact Or.inr hr'
      _ ≤ (uniformList n).toOuterMeasure {r | r = r₀} +
          (uniformList n).toOuterMeasure {r | (rest.lookup r).isSome} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ (1 : ENNReal) / 2 ^ n + (rest.length : ENNReal) * ((1 : ENNReal) / 2 ^ n) := by
          refine add_le_add ?_ ih
          rw [show {r : List Bool | r = r₀} = {r₀} from Set.ext fun _ => Set.mem_singleton_iff.symm,
            PMF.toOuterMeasure_apply_singleton]
          exact uniformList_apply_le n r₀
      _ = (((r₀, pad₀) :: rest).length : ENNReal) * ((1 : ENNReal) / 2 ^ n) := by
          rw [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

end Cslib.BitString
