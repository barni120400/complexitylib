/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Tactic.PolyTime
import Mathlib.Util.CountHeartbeats

open Turing.MultiTapeTM

set_option maxHeartbeats 200000 in
-- Pin the original guide/default budget as a regression limit; do not raise it.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool := by
  polytime
