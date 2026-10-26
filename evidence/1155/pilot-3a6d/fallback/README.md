# Qualified successful-call heartbeat fallback

The coordinator authorized this fallback after the frozen `d13e77e1` JSON mapping limitation. It uses **existing Mathlib tactic-form** `#count_heartbeats polytime`, not command-form `#count_heartbeats in ...`, repeated runs, a custom elaborator or a new profiler. Source pin remains actual merged `3a6d7706`.

| Positive | Raw counter delta | User-facing heartbeats (raw/1000) | Original limit |
|---|---:|---:|---:|
| Exact captured guide filter | 10,067,483 | 10,067.483 | 200,000 |
| Exact supplied-operand comparison | 4,019,008 | 4,019.008 | 200,000 |

These are single successful, inclusive **instrumented tactic-sequence** deltas. The counter starts before saveState/options handling and stops after evalTactic; it forces `Elab.async=false` internally and includes that wrapper overhead. It does not reset maxHeartbeats. No proof/failure/matching/encoding cache was introduced. Counts are not minimum budgets, wall times, async-on predictions or a stability distribution. The ordinary uninstrumented acceptance run remains separate.

Both diagnostic files add `Mathlib.Util.CountHeartbeats`. An import-only uninstrumented positive was checked first for each and passed. The guide diagnostic retains its exact original goal, script body, full imports/options and default limit, but places the expression at ordinary top level rather than in Verso's message-capturing document wrapper. This is deliberately **not an uninstrumented whole-guide timing claim**. The supplied positive retains its original normal-module context and explicit 200,000 limit. One authored counter/positive per file permits manual external source anchoring (`parsed.json`); this does not repair or validate automatic profiler span export.

The original missing-operand negative is unchanged and passed separately in the baseline file. It was **not** sent through a success-only heartbeat counter. Failure/censored-node deltas remain unknown/null; no count was fabricated for the negative.

Separate one-positive-per-file traces use the existing `trace.Meta.Tactic.fun_prop` and `trace.aesop`, at the same limits, without the heartbeat wrapper or async override. Both pass. Raw trace logs retain all details. Parsed JSON lists 35/12 **application-attempt lines**, including their local success markers; these are neither distinct final-proof rules nor a final dependency list. A locally successful application can still backtrack; final-proof contributions remain null. Nested/generated search nodes are not additional authored calls. Verbose trace process elapsed time includes tracing and imports and is not baseline per-call time.

`results.json` records exact commands, return codes and process durations; each is one observation. The observed heartbeat-run process durations (2.739s/1.615s) versus import-only durations (2.754s/1.635s) cannot establish negative overhead or comparative performance. No repeated/cold-cache benchmark was attempted.

Reproduction, after the parent pilot's accepted isolated bootstrap/import freshness:

```sh
python3 evidence/1155/pilot-3a6d/fallback/run.py /absolute/isolated/source/checkout
python3 evidence/1155/pilot-3a6d/fallback/parse.py
```

The runner executes only the two positives, sequentially, in three separate processes each: added-import baseline, tactic counter, rule trace. It stops on an unexpected failure and preserves logs. It never changes package/production source or maxHeartbeats. Preserve archived outputs before rerunning. The exact missing-operand negative stays in the parent acceptance evidence; reproducing the fallback alone does not rerun that negative.

This two-positive pilot does not populate or complete the static census. All other calls remain unmeasured. Per-call wall time, exact preparation/matching phase costs, failing/censored HB and final-proof rule attribution are still missing. Methodology review/representative CI additions are future work. All local jobs are terminal.
