/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Lean.Elab.Command

/-! Shared Option automation, including empty value types and encoded runtime defaults. -/
open Turing.MultiTapeTM

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (some (α := α)) enc (encOption enc) := by fun_prop

example {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool} {value : α → Option β}
    (hvalue : ComputableInPolyTime value a (encOption b)) :
    ComputableInPolyTime (fun x => (value x).isSome) a encBool := by fun_prop

example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : Option α × α => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by fun_prop

example (enc : Empty ↪ List Bool) :
    ComputableInPolyTime (fun p : Option Empty × Empty => p.1.getD p.2)
      (encPair (encOption enc) enc) enc := by fun_prop

example : (none : Option Bool).getD false = false := rfl
example : (some true : Option Bool).getD false = true := rfl
example : (some false : Option Bool).getD true = false := rfl

example {α : Type} (a : α ↪ List Bool) (e : Empty ↪ List Bool)
    {value : α → Option Empty} (hvalue : ComputableInPolyTime value a (encOption e)) :
    ComputableInPolyTime (fun x => (value x).isSome) a encBool := by fun_prop

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
