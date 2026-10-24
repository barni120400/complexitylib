/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial

/-!
# Direct consequences of charged asymptotic bounds

Time, workspace and encoded output are separate obligations. These rules package or forget the
actual realizing machine; they do not normalize it or import a higher construction calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {T S : α → ℕ}

/-- Exact plain machine bounds and an explicit output charge supply asymptotic bounds. -/
theorem of_bounds {t s : α → ℕ}
    (hf : ComputableInTimeAndSpace f encIn encOut t s) (k : ℕ)
    (ht : ∀ a, t a ≤ k * (T a + 1)) (hs : ∀ a, s a ≤ k * (S a + 1))
    (hl : ∀ a, (encOut (f a)).length ≤ k * (S a + 1)) :
    ComputableInO f encIn encOut T S :=
  ⟨k, hf.mono ht hs, hl⟩

/-- Polynomial bounds on both resource functions give a plain polynomial-time certificate. -/
theorem computableInPolyTime (h : ComputableInO f encIn encOut T S)
    (hT : PolyBounded (fun a => (encIn a).length) T)
    (hS : PolyBounded (fun a => (encIn a).length) S) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨c, h, _⟩ := h
  obtain ⟨ct, dt, ht⟩ := hT.exists_le
  obtain ⟨cs, ds, hs⟩ := hS.exists_le
  refine ⟨fun n => c * (ct * (n + 1) ^ dt + 1),
    fun n => c * (cs * (n + 1) ^ ds + 1), by fun_prop, by fun_prop, h.mono ?_ ?_⟩
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (ht a) 1)
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (hs a) 1)

end Turing.MultiTapeTM.ComputableInO
