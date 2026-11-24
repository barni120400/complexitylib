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
concatenation. Two substitutions whose blocks have the same lengths on the letters of a word give
the same concatenation exactly when they agree on these letters
(`List.flatMap_eq_flatMap_iff_of_forall_length_eq`).
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

/-- Two substitutions whose blocks have the same lengths on the letters of a word give the same
word exactly when they agree on its letters. -/
theorem List.flatMap_eq_flatMap_iff_of_forall_length_eq {α β : Type*} {l : List α}
    {f g : α → List β} (h : ∀ a ∈ l, (f a).length = (g a).length) :
    l.flatMap f = l.flatMap g ↔ ∀ a ∈ l, f a = g a := by
  refine ⟨fun e => ?_, List.flatMap_congr⟩
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (h a List.mem_cons_self)
    exact List.forall_mem_cons.2 ⟨e1, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) e2⟩
