# ONE original Cloud file — executed diagnostic, review pending

Source pin **3a6d770645c1217689da774f519cd785c253d8a2**. Only the prepared whole Cloud.lean baseline/import-only/wrapped variants were elaborated. All3 complete commands PASS at the original project options/default200000. No source reconstruction, smaller proof, model/encoder/budget change, new registry policy, production PR, full-library build or output-cache publication.

## Guard correction before execution

Source review identified two consistency holes. Frozen prefix **d4e496c3** requires a present true integer UInt64-range thread ID on EVERY begin/end (None==None and bools reject) and global per-run event-ID ownership (reuse across different calls rejects; its own begin/end remains valid). Four added SYNTHETIC regressions exercise absent/null/bool threads and cross-call reuse; total14 synthetic rejection checks plus complete-contract smoke PASS before execution. This is metadata consistency, **not forged-sidecar authentication**. Source/mapping/old b83 and9f contracts remain unchanged.

## Actual context and acceptance

Each command uses the ORIGINAL relative path below a variant root and Lean's `--root`, retaining **Complexity.Computability.PCP.Encoded.Cloud**. Newly generated private-local .ilean metadata confirms that actual module name and the same17 source declaration names in ALL modes. Baseline original direct-import metadata matches exactly; other modes add only Diag1155.Wrapper. Extracted metadata/digests are in actual-contexts.json; raw compiler outputs stay private and are not published. Generated auxiliary-name/selected-data identity is not inferred.

All original package leanOptions were passed identically in every mode and crosschecked against existing setup.options. The copied setup's foreign absolute importArts paths were **not used**; no --setup or foreign-output mutation. Warning-as-error retained, maxHeartbeats not overridden, async not forced. Only the six Cloud direct-import targets were refreshed (5336 mostly cached jobs); no bootstrap rerun/full-library check.

Strict Cloud-only validation requires all3 whole-file exits0, exact mapping/source/module/run/sidecar provenance and exactly one complete matching returned/zero-goal pair per authored call. All3 pairs pass, both thread fields are valid/match, event IDs are owned uniquely, and baseline/import-only emit no events. Unknown/partial/censored/duplicate data or a failed later whole-file proof cannot be blessed by returned wrappers. No rejection or partial-status override was needed.

| Authored original call | Line | Raw current-thread HB | User HB | Forwarded wall ns | Actual async |
|---|---:|---:|---:|---:|---|
| isPolyTime_halfEdges |75|5,634,699|5,634.699|457,284,031|true|
| isPolyTime_endpoint |86|5,468,112|5,468.112|577,294,818|true|
| isPolyTime_cloud |96|5,360,395|5,360.395|714,910,123|true|

Each returns with0 local goals. These are instrumented forwarded-call intervals, **not minima, final-proof rule attribution, async-total work or a causal overhead estimate**. The3 calls execute on distinct threads; intervals may overlap, so do not sum wall times or call it total module time. Thread-local raw units/1000 yield user HB. Sampling/observing has overhead; outer wrapper/telemetry still consumes original command budget. No proof/failure/encoding/matching cache or reset was introduced.

Whole-process observations baseline2.688s/import-only2.236s/wrapped2.234s include imports/startup/concurrent elaboration/output. Their single ordered differences are NOT negative overhead evidence or a stable performance comparison. All other tactics/proofs run as part of full-file validation but their individual metrics remain unmeasured. No inference to all4003 census entries or other files.

Concurrent JSONL was valid for these observed3 pairs. No general concurrent-write atomicity, kill/crash/timeout/recursion/censor guarantee is established; malformed/partial future records must fail closed. No rule traces/final dependency lists were collected. Methodology_approved remains false pending independent postrun source/data assessment. Earlier caught-failure evidence is unchanged; this Cloud file itself contains only the3 positives.

## Reproduction / provenance

Use the source-preparation instructions and a private pinned checkout with independent mutable outputs. Compile the **unchanged** b83 wrapper locally if needed. Accepted bootstrap already ran once for this owned checkout; no package source/toolchain edit. Freshen only the exact Cloud imports. To avoid overwriting archived provenance, copy run.py/parse.py to a NEW EMPTY sibling evidence directory (the prepared source directory remains locatable). Then:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/NEW-EMPTY-DIR/run.py /absolute/private/3a6/checkout
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/NEW-EMPTY-DIR/parse.py
```

The driver enforces pin/clean tracked source/unchanged wrapper, source hashes, original options, context metadata and stop-on-error. It generates only private .ilean output and publishes extracted context, not compiled caches. Full commands, raw logs/events, runtime sidecar, parsed JSON/CSV, guard digest and import-freshness log are preserved. Do not run additional files without a new builder handoff.

All owned jobs terminal. All prior accepted/rejected real raw bytes are preserved; only the explicitly authorized checker/synthetic guard artifacts changed. Broader survey and LiuPass remain OPEN. Stop for independent postrun method review, not a full-survey claim.
