/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-! # Direct word and List clients -/

open Turing.MultiTapeTM

run_elab do
  let env ← Lean.getEnv
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains name then throwError "unexpected high-level tidy predicate: {name}"

example {γ : Type} {input : γ ↪ List Bool} {word : γ → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun x => (word x).reverse) input encBits := by
  fun_prop

-- This is the all-word reverse/trim/reverse shape used by the natural-number decoder.
example (htrim : ComputableInPolyTime (fun word : List Bool => word.dropWhile (!·))
    encBits encBits) :
    ComputableInPolyTime (fun word : List Bool => (word.reverse.dropWhile (!·)).reverse)
      encBits encBits := by
  fun_prop

example (_unknown : List Bool → List Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun word => (_unknown word).reverse) encBits encBits := by
      fun_prop
  trivial

example : ComputableInPolyTime List.range encUnary (encList encUnary) :=
  ComputableInPolyTime.range

example {α γ : Type} {element : α ↪ List Bool} {input : γ ↪ List Bool}
    {list : γ → List α} {test : γ → α → Bool}
    (hlist : ComputableInPolyTime list input (encList element))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair input element) encBool) :
    ComputableInPolyTime (fun x => (list x).all (test x)) input encBool := by
  fun_prop

example (test : ℕ → ℕ → Bool)
    (htest : ComputableInPolyTime (fun p : ℕ × ℕ => test p.1 p.2)
      (encPair encUnary encUnary) encBool) :
    ComputableInPolyTime (fun n => (List.range n).all (test n)) encUnary encBool := by
  fun_prop

example {γ : Type} {input : γ ↪ List Bool} {ι : Type*} (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableInPolyTime (fun x => test x i) input encBool) :
    ComputableInPolyTime (fun x => l.all (test x)) input encBool := by
  exact ComputableInPolyTime.allConst l htest

-- No callback or encoding is needed for a type with no selected members.
example {ι : Type*} (test : List Bool → ι → Bool) :
    ComputableInPolyTime (fun word => ([] : List ι).all (test word)) encBits encBool := by
  apply ComputableInPolyTime.allConst
  simp

example (_test : List Bool → ℕ → Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun word => [0].all (_test word)) encBits encBool := by
      fun_prop
  trivial

example : List.range 0 = [] := by decide
example : (encList encUnary (List.range 4)).length = 16 := by decide

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.bitsReverse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.bitsReverse
