# Artifact-only partial/censored parser controls

Scope: the fixed three-call pilot at **b83da912f9c0230bd9047e5f473ad9a27cff28b3**, not a runtime collector, general profiler framework or source expansion. No Lean/build/cache operations, package changes or production PR. Existing accepted/rejected raw files, source snapshots, parsers and hashes remain unchanged.

`pilot_parser.py` separates two data-only operations:

- `parse_partial`: retain observed runtime attempts without conferring whole-command acceptance. A begin without an end becomes **censored_unknown**, with all cost/goal fields null. A call with no observed begin is **not_observed**, with no invented attempt/cost. An end without a begin is malformed and fails closed. Repeated distinct event IDs stay separate attempts under ONE original call ID; no final-proof retention is inferred.
- `require_complete_pilot`: strict acceptance for ONLY the original three-call/six-command pilot. All six distinct command rows must match provenance and pass; every mapped call must have exactly one complete attempt with its expected outcome. Partial, unobserved, repeated or unexpectedly returned negative calls cannot pass. Expected ordinary failure remains an **exception invocation** even though its enclosing original negative-control command passes.

The previously reviewed strict acceptance script in `wrapper-compact-3a6d/parse.py` was not altered or weakened. This new small parser is an artifact-only candidate for independent review, explicitly bounded to the three existing calls. No new real parsed measurement rows are written.

## Executed controls

**22 checks PASS**: one read-only real-pilot reconciliation plus21 synthetic checks derived from cloned existing events. The deterministic transformations and all assertions live in `control_checks.py`; the report records exact original JSONL/sidecar/parsed hashes and marks synthetic cases explicitly. Synthetic counts/events are never combined with real measurement rows.

| Control | Required result |
|---|---|
| Complete real pilot | Same IDs, outcomes, costs and strict acceptance; no output rewrite |
| Begin only | censored_unknown, null costs/goals, strict rejection |
| No events | not_observed/no attempts, strict rejection |
| Existing ordinary caught-failure pair | Still exception; partial dataset rejected |
| Cloned retry/backtrack-shaped pair with distinct attempt ID | Two attempts under one authored call, not two calls; strict fixed-pilot rejection |
| Duplicate begin/end, unmatched end, cross-call event reuse | Parser error, fail closed |
| Sidecar/event digest, run, implementation digest, token or thread mismatch | Parser error, fail closed |
| Unknown phase or invalid negative cost | Parser error, fail closed |
| Real command success plus a censored call | Strict rejection; success metadata cannot bless partial data |
| Synthetic negative changed to returned | Preserve observed status but reject expected-outcome acceptance |
| Missing/duplicate/failed command metadata | Strict rejection |

These are **synthetic parser behaviors**, not empirical kill/crash/timeout/backtracking guarantees. The actual pilot still only observes two returned positives and one ordinary caught exception. No rule/final-proof inference or full-census completeness claim.

## Reproduce

From the evidence checkout (Python standard library only):

```sh
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/parser-controls-b83da912/control_checks.py
```

This reads archived inputs, tests in-memory clones, and writes ONLY the synthetic control-results.json here. It does not invoke Lean, edit old parser/data files or create Python bytecode caches. All prior artifacts are separately verified against the b83 manifest before publication. All jobs terminal; audit's sole-builder slot unchanged. Independent method review remains required before any one-file expansion.
