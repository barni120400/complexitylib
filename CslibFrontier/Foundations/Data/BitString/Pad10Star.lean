/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.PadBlocks
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
# Padding with a one and zeros, and the blocks of a bit list

`BitString.pad10star r msg` appends to a bit list a `1` and then the fewest zeros that make its
length a multiple of `r`: the padding `m ↦ m ‖ 1 ‖ 0^*` of the sponge construction
([KatzLindell2020], Construction 7.6), called `pad10*` in the Keccak literature.
`BitString.toBlocks r l` cuts a bit list into its consecutive blocks of `r` bits, dropping an
incomplete last block; it is `BitString.padBlocks r l.length l`. Padding and then cutting is
injective (`BitString.toBlocks_pad10star_injective`), so a bit list of any length can be
recovered from its blocks.

These were part of `CslibFrontier.Crypto.Primitives.Hash.Sponge`; they are here because the
cutting argument of [AnthropicVPVNP2026] uses the same padding for its units.

## Main definitions

* `Cslib.BitString.pad10star`: the padding `m ‖ 1 ‖ 0^*` to a multiple of `r` bits.
* `Cslib.BitString.toBlocks`: the blocks of `r` bits of a bit list.

## Main results

* `Cslib.BitString.pad10star_injective`, `Cslib.BitString.toBlocks_pad10star_injective`:
  distinct bit lists have distinct paddings and distinct padded block sequences.
* `Cslib.BitString.dvd_length_pad10star`, `Cslib.BitString.length_pad10star_div`: the padded
  length is a multiple of `r`, namely `(msg.length / r + 1) * r`.
* `Cslib.BitString.getD_pad10star`: the padded list read with default `false` is `msg ++ [true]`
  read with default `false`.
* `Cslib.BitString.toBlocks_injOn`, `Cslib.BitString.toBlocks_append`,
  `Cslib.BitString.toBlocks_ofFn`: cutting is injective on lists of whole blocks and commutes
  with appending after whole blocks.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Construction 7.6
-/

public section

namespace Cslib.BitString

/-- Padding of Construction 7.6: append a `1` and then the fewest zeros making the length a
multiple of `r`. -/
@[expose]
def pad10star (r : ℕ) (msg : List Bool) : List Bool :=
  msg ++ true :: List.replicate ((r - (msg.length + 1) % r) % r) false

/-- Parse a bit string into its consecutive `r`-bit blocks, dropping any incomplete final
block: `padBlocks` with the length of the list itself as the bound. -/
@[expose]
def toBlocks (r : ℕ) (l : List Bool) : List (BitString r) := padBlocks r l.length l

private theorem replicate_false_append_true_inj :
    ∀ (k k' : ℕ) (a b : List Bool),
      List.replicate k false ++ true :: a = List.replicate k' false ++ true :: b → a = b
  | 0, 0, a, b, h => by simpa using h
  | k + 1, 0, a, b, h => by simp [List.replicate_succ] at h
  | 0, k' + 1, a, b, h => by simp [List.replicate_succ] at h
  | k + 1, k' + 1, a, b, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    exact replicate_false_append_true_inj k k' a b h

/-- Padding is injective: distinct messages have distinct padded strings. -/
theorem pad10star_injective (r : ℕ) : Function.Injective (pad10star r) := by
  intro a b h
  have h' := congrArg List.reverse h
  simp only [pad10star, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h'
  simpa using congrArg List.reverse (replicate_false_append_true_inj _ _ _ _ h')

theorem dvd_length_pad10star {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    r ∣ (pad10star r msg).length := by
  have h1 := Nat.mod_lt (msg.length + 1) hr
  have hlen : (pad10star r msg).length = (msg.length + 1) + (r - (msg.length + 1) % r) % r := by
    simp only [pad10star, List.length_append, List.length_cons, List.length_replicate]
    omega
  rw [hlen, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.eq_zero_or_pos ((msg.length + 1) % r) with h | h
  · rw [h, Nat.sub_zero, Nat.mod_self, Nat.add_zero, h]
  · rw [Nat.mod_eq_of_lt (by omega : r - (msg.length + 1) % r < r), Nat.add_mod,
      Nat.mod_eq_of_lt (by omega : r - (msg.length + 1) % r < r), Nat.add_sub_cancel' h1.le,
      Nat.mod_self]

/-- Padding adds at most one block: a `1` and fewer than `r` zeros. -/
theorem length_pad10star_le {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    (pad10star r msg).length ≤ msg.length + r := by
  have := Nat.mod_lt (r - (msg.length + 1) % r) hr
  simp only [pad10star, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- On a message whose length is a multiple of `r`, padding appends one full block
`1 ‖ 0^(r - 1)`. -/
theorem pad10star_of_dvd {r : ℕ} (hr : 0 < r) {msg : List Bool} (h : r ∣ msg.length) :
    pad10star r msg = msg ++ true :: List.replicate (r - 1) false := by
  obtain ⟨k, hk⟩ := h
  have : (r - (msg.length + 1) % r) % r = r - 1 := by
    rw [hk, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]
    · obtain rfl : r = 1 := by omega
      rfl
  simp only [pad10star, this]

@[simp]
theorem length_toBlocks (r : ℕ) (l : List Bool) : (toBlocks r l).length = l.length / r :=
  length_padBlocks r l.length l

theorem getElem?_toBlocks (r : ℕ) (l : List Bool) (b : ℕ) :
    (toBlocks r l)[b]? =
      if b < l.length / r then some (fun i : Fin r => l.getD (b * r + i) false) else none := by
  split_ifs with hb
  · rw [List.getElem?_eq_getElem (by simpa using hb)]
    exact congrArg some (funext fun i => padBlocks_getElem_apply r l.length l b hb i)
  · exact List.getElem?_eq_none (by simpa using hb)

/-- The blocks of a list, read position by position. -/
theorem toBlocks_eq_map_range (r : ℕ) (l : List Bool) :
    toBlocks r l =
      (List.range (l.length / r)).map fun b => (fun i : Fin r => l.getD (b * r + i) false) := by
  refine List.ext_getElem? fun b => ?_
  rw [getElem?_toBlocks]
  by_cases hb : b < l.length / r <;> simp [hb]

private theorem getD_eq_of_toBlocks_eq {r : ℕ} (hr : 0 < r) {l l' : List Bool}
    (h : toBlocks r l = toBlocks r l') {n : ℕ} (hn : n / r < l.length / r) :
    l.getD n false = l'.getD n false := by
  have hn' : n / r < l'.length / r := by
    have := congrArg List.length h
    simp only [length_toBlocks] at this
    rwa [← this]
  have e := congrArg (fun L => (L[n / r]?).map (· ⟨n % r, Nat.mod_lt n hr⟩)) h
  simp only [getElem?_toBlocks, hn, hn', ↓reduceIte, Option.map_some, Option.some.injEq] at e
  rwa [Nat.div_add_mod'] at e

/-- Parsing is injective on strings whose lengths are multiples of `r`. -/
theorem toBlocks_injOn {r : ℕ} (hr : 0 < r) {l l' : List Bool} (hl : r ∣ l.length)
    (hl' : r ∣ l'.length) (h : toBlocks r l = toBlocks r l') : l = l' := by
  have hlen : l.length = l'.length := by
    have := congrArg List.length h
    simp only [length_toBlocks] at this
    rw [← Nat.div_mul_cancel hl, ← Nat.div_mul_cancel hl', this]
  refine List.ext_getElem hlen fun n hn hn' => ?_
  have hd : n / r < l.length / r := by
    rw [Nat.div_lt_iff_lt_mul hr, Nat.div_mul_cancel hl]
    exact hn
  have := getD_eq_of_toBlocks_eq hr h hd
  rwa [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hn'] at this

/-- Distinct messages have distinct padded block sequences. -/
theorem toBlocks_pad10star_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective fun msg => toBlocks r (pad10star r msg) := fun _ _ h =>
  pad10star_injective r
    (toBlocks_injOn hr (dvd_length_pad10star hr _) (dvd_length_pad10star hr _) h)

theorem toBlocks_pad10star_ne_nil {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    toBlocks r (pad10star r msg) ≠ [] := by
  have hpos : 0 < (pad10star r msg).length := by simp [pad10star]
  refine List.ne_nil_of_length_pos ?_
  rw [length_toBlocks]
  exact Nat.div_pos (Nat.le_of_dvd hpos (dvd_length_pad10star hr msg)) hr

theorem toBlocks_append {r : ℕ} (hr : 0 < r) {a : List Bool} (ha : r ∣ a.length)
    (b : List Bool) : toBlocks r (a ++ b) = toBlocks r a ++ toBlocks r b := by
  obtain ⟨k, hk⟩ := ha
  have hka : (toBlocks r a).length = k := by
    rw [length_toBlocks, hk, Nat.mul_div_cancel_left _ hr]
  refine List.ext_getElem? fun j => ?_
  rcases Nat.lt_or_ge j k with hj | hj
  · rw [List.getElem?_append_left (by rw [hka]; exact hj), getElem?_toBlocks, getElem?_toBlocks,
      List.length_append, hk, Nat.mul_add_div hr, Nat.mul_div_cancel_left _ hr]
    simp only [Nat.lt_add_right _ hj, hj, ↓reduceIte, Option.some.injEq]
    funext i
    exact List.getD_append _ _ _ _ (by
      rw [hk]; nlinarith [i.isLt, Nat.mul_le_mul_right r (show j + 1 ≤ k from hj)])
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [List.getElem?_append_right (by rw [hka]; exact hj), hka, Nat.add_sub_cancel_left,
      getElem?_toBlocks, getElem?_toBlocks, List.length_append, hk, Nat.mul_add_div hr]
    simp only [Nat.add_lt_add_iff_left]
    split_ifs
    · congr 1 with i : 1
      rw [List.getD_append_right a b false ((k + d) * r + i) (by rw [hk]; nlinarith), hk,
        show (k + d) * r + i - r * k = d * r + i by
          rw [add_mul, mul_comm k r, Nat.add_assoc, Nat.add_sub_cancel_left]]
    · rfl

@[simp]
theorem toBlocks_ofFn {r : ℕ} (hr : 0 < r) (m : BitString r) :
    toBlocks r (List.ofFn m) = [m] := by
  refine List.ext_getElem? fun j => ?_
  rw [getElem?_toBlocks, List.length_ofFn, Nat.div_self hr]
  rcases j with _ | j
  · simp only [Nat.zero_lt_one, ↓reduceIte, zero_mul, zero_add, List.getElem?_cons_zero,
      Option.some.injEq]
    funext i
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  · simp

/-- The padded blocks of a full-block list `u` followed by one more block `m` are the blocks of
`u`, then `m`, then the padding block. -/
theorem toBlocks_pad10star_append_ofFn {r : ℕ} (hr : 0 < r) {u : List Bool} (hu : r ∣ u.length)
    (m : BitString r) :
    toBlocks r (pad10star r (u ++ List.ofFn m)) =
      toBlocks r u ++ m :: toBlocks r (true :: List.replicate (r - 1) false) := by
  have hum : r ∣ (u ++ List.ofFn m).length := by
    simpa using Nat.dvd_add hu (dvd_refl r)
  rw [pad10star_of_dvd hr hum, List.append_assoc, toBlocks_append hr hu,
    toBlocks_append hr (a := List.ofFn m) (by simp), toBlocks_ofFn hr]
  rfl

/-- The padded length in blocks: one more than the whole blocks of the message. -/
theorem length_pad10star_div {r : ℕ} (hr : 0 < r) (msg : List Bool) :
    (pad10star r msg).length / r = msg.length / r + 1 := by
  obtain ⟨c, hc⟩ := dvd_length_pad10star hr msg
  have h1 : msg.length + 1 ≤ (pad10star r msg).length := by simp [pad10star]
  have h2 := length_pad10star_le hr msg
  have h3 := Nat.div_add_mod msg.length r
  have h4 := Nat.mod_lt msg.length hr
  rw [hc] at h1 h2 ⊢
  rw [Nat.mul_div_cancel_left _ hr]
  have hlt : msg.length / r < c := by
    by_contra hcon
    have := Nat.mul_le_mul_left r (not_lt.1 hcon)
    omega
  have hle : c ≤ msg.length / r + 1 := by
    by_contra hcon
    have := Nat.mul_le_mul_left r (show msg.length / r + 2 ≤ c by omega)
    rw [Nat.mul_add] at this
    omega
  omega

/-- Reading the padded list with default `false` is reading `msg ++ [true]` with default
`false`: the zeros of the padding are the default. -/
theorem getD_pad10star (r : ℕ) (msg : List Bool) (i : ℕ) :
    (pad10star r msg).getD i false = (msg ++ [true]).getD i false := by
  simp only [pad10star, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_cons]
  split_ifs <;> simp_all [List.getElem?_replicate]
  split_ifs <;> rfl

end Cslib.BitString
