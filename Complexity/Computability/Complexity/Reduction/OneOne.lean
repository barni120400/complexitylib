/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction

/-!
# Polynomial-time one-one reductions

A one-one reduction is a many-one reduction by an injective map. In polynomial time it underlies
p-isomorphism and the Berman–Hartmanis conjecture [Berman and Hartmanis][BermanHartmanis1977].
It is `ManyOneReducibleBy` for the injective polynomial-time maps
(`Cslib.Complexity.polyTimeOneOneReducible_iff_manyOneReducibleBy`), so the generic
many-one kernel applies.

## Main definitions

* `Cslib.Complexity.PolyTimeOneOneReducible`: reduction by an injective polynomial-time map.

## Main results

* `Cslib.Complexity.polyTimeOneOneReducible_iff_manyOneReducibleBy`: the bridge to the generic
  many-one kernel.
* `Cslib.Complexity.PolyTimeOneOneReducible.polyTimeReducible`: one-one reductions are many-one.
* `Cslib.Complexity.PolyTimeOneOneReducible.refl`, `Cslib.Complexity.PolyTimeOneOneReducible.trans`:
  a preorder.
* `Cslib.Complexity.PolyTimeOneOneReducible.compl`,
  `Cslib.Complexity.PolyTimeOneOneReducible.mem_P`.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

/-- `A` reduces to `B` by an injective polynomial-time map `f` with `a ∈ A ↔ f a ∈ B`. -/
def PolyTimeOneOneReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α)
    (B : Set β) : Prop :=
  ∃ f : α → β, (ComputableInPolyTime f encA encB ∧ Function.Injective f) ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- One-one reducibility is many-one reducibility by the injective polynomial-time maps. -/
theorem polyTimeOneOneReducible_iff_manyOneReducibleBy :
    PolyTimeOneOneReducible encA encB A B ↔
      ManyOneReducibleBy (fun f => ComputableInPolyTime f encA encB ∧ Function.Injective f) A B :=
  Iff.rfl

/-- A one-one reduction is a many-one reduction. -/
theorem PolyTimeOneOneReducible.polyTimeReducible (h : PolyTimeOneOneReducible encA encB A B) :
    PolyTimeReducible encA encB A B :=
  let ⟨f, ⟨hf, _⟩, hA⟩ := h
  ⟨f, hf, hA⟩

/-- The identity is a one-one reduction. -/
@[refl]
theorem PolyTimeOneOneReducible.refl (encA : α ↪ List Bool) (A : Set α) :
    PolyTimeOneOneReducible encA encA A A :=
  ⟨id, ⟨ComputableInPolyTime.id', Function.injective_id⟩, fun _ => Iff.rfl⟩

/-- One-one reductions compose. -/
@[trans]
theorem PolyTimeOneOneReducible.trans (hAB : PolyTimeOneOneReducible encA encB A B)
    (hBC : PolyTimeOneOneReducible encB encC B C) : PolyTimeOneOneReducible encA encC A C :=
  let ⟨f, ⟨hf, hfi⟩, hA⟩ := hAB
  let ⟨g, ⟨hg, hgi⟩, hB⟩ := hBC
  ⟨g ∘ f, ⟨hg.comp hf, hgi.comp hfi⟩, fun a => (hA a).trans (hB (f a))⟩

/-- A one-one reduction from `A` to `B` is one from `Aᶜ` to `Bᶜ`. -/
theorem PolyTimeOneOneReducible.compl (h : PolyTimeOneOneReducible encA encB A B) :
    PolyTimeOneOneReducible encA encB Aᶜ Bᶜ :=
  let ⟨f, hf, hA⟩ := h
  ⟨f, hf, fun a => not_congr (hA a)⟩

/-- `P` is closed under one-one reductions. -/
theorem PolyTimeOneOneReducible.mem_P (h : PolyTimeOneOneReducible encA encB A B)
    (hB : B ∈ P encB) : A ∈ P encA :=
  h.polyTimeReducible.mem_P hB

end Cslib.Complexity
