/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PPT

/-! # Conditional and iteration dispatch through reducible program wrappers -/

public section
open Cslib Cslib.Probability Turing.MultiTapeTM

namespace ComplexityTests.PPTProgramShapes

noncomputable abbrev branch (word : List Bool) : ProbComp Bool :=
  if word.isEmpty then ProbComp.uniform Bool else pure false

example : IsPPTOn encBits encBool branch := by ppt

abbrev loop (count : List Bool → ℕ) (initial : List Bool → List Bool)
    (step : List Bool → ProbComp (List Bool)) (word : List Bool) :=
  OracleComp.iterate (count word) step (initial word)

example (count : List Bool → ℕ) (initial : List Bool → List Bool)
    (step : List Bool → ProbComp (List Bool))
    (hc : ComputableTidilyInPolyTime count encBits encUnary)
    (hi : ComputableTidilyInPolyTime initial encBits encBits)
    (hs : IsPPTOn encBits encBits step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (encBits next).length ≤ (encBits state).length) :
    IsPPTOn encBits encBits (loop count initial step) := by ppt

example (count : List Bool → ℕ) (initial : List Bool → List Bool)
    (step : List Bool → ProbComp (List Bool)) (growth : ℕ)
    (hc : ComputableTidilyInPolyTime count encBits encUnary)
    (hi : ComputableTidilyInPolyTime initial encBits encBits)
    (hs : IsPPTOn encBits encBits step)
    (hg : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      (encBits next).length ≤ (encBits state).length + growth) :
    IsPPTOn encBits encBits (loop count initial step) := by ppt

abbrev capturedLoop (count : List Bool → ℕ) (initial : List Bool → List Bool)
    (step : List Bool → List Bool → ProbComp (List Bool)) (word : List Bool) :=
  OracleComp.iterate (count word) (step word) (initial word)

example (count : List Bool → ℕ) (initial : List Bool → List Bool)
    (step : List Bool → List Bool → ProbComp (List Bool)) (growth : List Bool → ℕ)
    (hc : ComputableTidilyInPolyTime count encBits encUnary)
    (hi : ComputableTidilyInPolyTime initial encBits encBits)
    (hs : IsPPTOn (encPair encBits encBits) encBits (fun p => step p.1 p.2))
    (hp : PolyBounded (fun word => (encBits word).length) growth)
    (hg : ∀ word state next, next ∈ (ProbComp.eval (step word state)).support →
      (encBits next).length ≤ (encBits state).length + growth word) :
    IsPPTOn encBits encBits (capturedLoop count initial step) := by ppt

-- Retain the original bounded shared-encoding regression in both local fact orders.
set_option maxHeartbeats 12000 in
-- Keep the original regression budget rather than the default proof-search allowance.
example (sample : List Bool → ProbComp ℕ)
    (hUnary : IsPPTOn encBits encUnary sample) (_hBinary : IsPPTOn encBits encNat sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

-- Retain the original bounded shared-encoding regression in both local fact orders.
set_option maxHeartbeats 12000 in
-- Keep the original regression budget rather than the default proof-search allowance.
example (sample : List Bool → ProbComp ℕ)
    (_hBinary : IsPPTOn encBits encNat sample) (hUnary : IsPPTOn encBits encUnary sample) :
    IsPPTOn encBits encBool (fun word => do
      let n ← sample word
      pure ((List.range n).foldl (fun parity _ => !parity) true)) := by
  ppt

-- A generic nonzero bound must remain available through the production named handler.
private meta def namedOnly : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``ComputableInPolyTime

example {γ α β : Type} (encIn : γ ↪ List Bool) (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (encL : List α ↪ List Bool)
    (list : γ → List α) (init : γ → β) (step : γ → β → α → β)
    (hi : ComputableInPolyTime init encIn encB)
    (hc : ComputableInPolyTime list encIn encL ∧
      ComputableInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
        (encPair (encPair encIn encB) encA) encB ∧
      ListEncoding encA encL ∧ SizedListEncoding encA encL)
    (growth : γ → ℕ)
    (hb : PolyBounded (fun x => (encIn x).length) growth ∧
      ∀ x state value, value ∈ list x →
      (encB (step x state value)).length ≤ (encB state).length + growth x) :
    ComputableInPolyTime (fun x => (list x).foldl (step x) (init x)) encIn encB := by
  aesop (rule_sets := [-default]) (add unsafe 100% tactic namedOnly)

-- Both checked-zero and unconstrained alternatives survive a successful local bound proof.
private meta def twoNamedAlternatives : Aesop.RuleTac := fun input => do
  let result ← Cslib.Tactic.applyCertificates ``ComputableInPolyTime input
  unless result.applications.size ≥ 2 do
    throwError "the checked-zero and generic alternatives must both survive"
  return result

example {γ α β : Type} (encIn : γ ↪ List Bool) (encA : α ↪ List Bool)
    (encB : β ↪ List Bool) (encL : List α ↪ List Bool)
    (list : γ → List α) (init : γ → β) (step : γ → β → α → β)
    (hi : ComputableInPolyTime init encIn encB)
    (hc : ComputableInPolyTime list encIn encL ∧
      ComputableInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
        (encPair (encPair encIn encB) encA) encB ∧
      ListEncoding encA encL ∧ SizedListEncoding encA encL)
    (hb : PolyBounded (fun x => (encIn x).length) (fun _ => 0) ∧
      ∀ x state value, value ∈ list x →
      (encB (step x state value)).length ≤ (encB state).length + 0) :
    ComputableInPolyTime (fun x => (list x).foldl (step x) (init x)) encIn encB := by
  aesop (rule_sets := [-default]) (add unsafe 100% tactic twoNamedAlternatives)

end ComplexityTests.PPTProgramShapes
