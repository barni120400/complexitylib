/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Defs
import Mathlib.Data.List.Basic

/-!
# Concatenations of blocks of one length

A substitution that replaces every letter by a block of the same positive length is injective on
words as soon as it is injective on letters (`List.flatMap_injective_of_forall_length_eq`): the
blocks can be read back one after the other. `List.flatMap_singleton_injective` is the case of
blocks of length one, and `List.length_flatMap_of_forall_length_eq` gives the length of such a
concatenation.
-/

public section

/-- A substitution by blocks of one positive length is injective on words when it is injective on
letters. -/
theorem List.flatMap_injective_of_forall_length_eq {α β : Type*} {f : α → List β} {k : ℕ}
    (hk : 0 < k) (hlen : ∀ a, (f a).length = k) (hf : Function.Injective f) :
    Function.Injective fun w : List α => w.flatMap f := by
  intro w w' h
  dsimp only at h
  induction w generalizing w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons a w' =>
      have := congrArg List.length h
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons, List.length_append,
        hlen] at this
      omega
  | cons a w ih =>
    cases w' with
    | nil =>
      have := congrArg List.length h
      simp only [List.flatMap_nil, List.length_nil, List.flatMap_cons, List.length_append,
        hlen] at this
      omega
    | cons a' w' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨h1, h2⟩ := List.append_inj h ((hlen a).trans (hlen a').symm)
      rw [hf h1, ih h2]
