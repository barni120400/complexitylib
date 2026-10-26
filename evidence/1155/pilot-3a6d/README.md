# Existing-profiler pilot: source-mapping limitation

Actual source: **3a6d770645c1217689da774f519cd785c253d8a2**, merged #1168. Evidence only; no production changes/PR. Original census is unchanged; all other census timings remain unmeasured.

The unchanged guide filter/script passed at default **200000** heartbeats. `guide-baseline.lean` retains every chapter import and header option and the original hidden namespace-open block. Its Verso document is reduced to this example: exact example/context acceptance, **not whole-chapter execution**. `source-map.json` records correspondence. The exact landed generic supplied-operand example and first missing-right-operand control also passed, with their original explicit200000 setters and normal module import. Success of `fail_if_success` means the missing-premise attempt failed as required, not that a missing certificate was proved.

Fresh isolated worktree bootstrap ran once. Initial cached-object/import-graph failures are retained separately. Only the chapter's listed import closure was built for freshness; no whole-library/test target. MCP discovery found no Lean tool; the existing CLI was used. No source/package/proof/encoder/budget changes or async override.

Separate wall-profiler runs also passed. **Existing JSON export cannot provide the requested authored-source mapping:** all414 guide and247 operand function-table entries have null file/line/column. The pinned exporter explicitly leaves these TODO placeholders. The guide export has no `polytime` tag despite successful elaboration. The operand export has one reused `Elab.step: Cslib.Tactic.PolyTime.tacticPolytime` tag, not separate authored source spans. Generated/nested frames are not independent authored calls.

Markers are empty; exporter omits TraceData.result?, so rejected inner attempts and hard-interrupted/censored nodes cannot be classified from it. Per the initial stop-if-unsuitable instruction, heartbeat-mode JSON and rule traces were not run in this checkpoint; no replacement profiler/mapping heuristic was built. Authored-call metrics and final-proof rules are null in parsed JSON/CSV.

Process observations: baseline3.084s/1.933s (guide/two operand controls), wall-diagnostic3.158s/2.127s. These include startup/imports/elaboration and export. Single-run differences+0.074s/+0.194s are **not causal trace-overhead estimates**, per-call times or cold-cache claims. No repeated benchmark was made.

Pinned exporter wall seconds become JSON milliseconds; trace costs are inclusive/overlap, so do not sum parents and children. Heartbeat mode reads raw IO.getNumHeartbeats: **1000raw =1user heartbeat**. It reuses millisecond conversion types plus wall runFrontend wrapping; a future heartbeat export cannot be read as wall milliseconds or blindly aggregated. No empirical HB-unit validation is claimed here. No rule trace was run; attempted applications are not final proof. No command-form #count_heartbeats (which resets budget) was used.

Reproduce in a fresh isolated pinned source checkout after accepted cache bootstrap and exact-import freshness:

```sh
python3 evidence/1155/pilot-3a6d/run.py /absolute/source/checkout baseline
python3 evidence/1155/pilot-3a6d/run.py /absolute/source/checkout wall
python3 evidence/1155/pilot-3a6d/parse.py
```

Runner writes diagnostic source under pilot1155 in source checkout and artifacts beside itself; preserve outputs before reruns. Parser validates missingness/process observations only. environment.json, pinned-tool-excerpts.txt and raw logs/exports retain provenance. All jobs terminal at this checkpoint. A separately authorized tactic-form heartbeat fallback will be recorded separately, not silently substituted for this export.
