/- Evidence-only instrumentation for #1155; never a production tactic dependency. -/
module
public meta import Lean.Elab.Tactic.Basic
public import Lean.Util.Heartbeats
public import Lean.Data.Json

open Lean Elab Tactic

namespace Diag1155

private meta def emit (fields : List (String × Json)) : IO Unit := do
  let some path ← IO.getEnv "DIAG1155_OUTPUT"
    | throw (IO.userError "DIAG1155_OUTPUT is required")
  IO.FS.withFile path .append fun h => h.putStrLn (Json.mkObj fields).compress

/-- Forward precisely one unchanged child tactic. No original handler/registry is overridden. -/
elab "diag1155_call " label:str " => " child:tactic : tactic => do
  let id := label.getString
  let tid ← IO.getTID
  let before ← getGoals
  let opts ← getOptions
  let eventStart ← IO.monoNanosNow
  let event := s!"{id}:{tid}:{eventStart}"
  emit [("phase", toJson "begin"), ("call_id", toJson id), ("event_id", toJson event),
    ("thread_id", toJson tid.toNat), ("goals_before", toJson before.length),
    ("maxHeartbeats_user", toJson (maxHeartbeats.get opts)),
    ("async_option", toJson (Lean.Elab.async.get opts)),
    ("child_kind", toJson child.raw.getKind.toString)]
  let hb0 ← IO.getNumHeartbeats
  let ns0 ← IO.monoNanosNow
  let result ← observing (evalTactic child)
  let ns1 ← IO.monoNanosNow
  let hb1 ← IO.getNumHeartbeats
  let status := match result with
    | .ok _ => "returned"
    | .error ex => if ex.isMaxHeartbeat then "heartbeat_exception"
      else if ex.isMaxRecDepth then "recursion_exception"
      else if ex.isInterrupt then "interrupt_exception" else "exception"
  let remaining : Option Nat ← match result with
    | .ok _ => do
      let after ← getGoals
      pure (some after.length)
    | .error _ => pure none
  emit [("phase", toJson "end"), ("call_id", toJson id), ("event_id", toJson event),
    ("thread_id", toJson tid.toNat), ("status", toJson status),
    ("raw_thread_heartbeats", toJson (hb1 - hb0)),
    ("wall_nanoseconds", toJson (ns1 - ns0)),
    ("goals_after", toJson remaining)]
  match result with
  | .ok _ => pure ()
  | .error ex => throw ex

end Diag1155
