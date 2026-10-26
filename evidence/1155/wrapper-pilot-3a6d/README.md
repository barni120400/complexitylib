# Three-call forwarding-wrapper experiment: stopped on context mismatch

Actual source pin **3a6d770645c1217689da774f519cd785c253d8a2**, same as archived pilot. Scope authorized in #1155 comment6415261502: guide positive, supplied-operand positive, and existing missing-operand attempt/following proof only. No production/package source edits or standard registry changes; no compiled outputs/cache published.

## Result and stop

| Guide mode | Command result |
|---|---|
| Unchanged baseline (same archived reduced Verso document/full imports/options) | PASS |
| Added diagnostic-import only | PASS |
| Wrapped call | **FAIL: unchanged Verso 80-column check** |

The wrapped child actually returned, with one goal before and zero after. Its nonrollback begin/end records survive. However, embedding the full stable hash/path/span label made the displayed code line **155 columns**, violating the original `verso.code.warnLineLength=80`. The command fails, so this is **not accepted measurement or proof completion**. No goal, budget, style limit or original tactic option was weakened. Per stop-on-mismatch instructions, **supplied and missing-operand runs were NOT started**; caught-failure/restoration agreement therefore remains untested in this experiment. They remain explicit unknown/not-run rows, not successes or censored executed calls.

The incidental child record is 10,067,776 raw current-thread HB (10,067.776 user HB), 715,028,485 monotonic ns, actual async option=false and maxHeartbeats=200000. Parsed output marks `accepted_measurement=false`. Do not use it as a regression baseline, compare it causally to prior counts, or infer a successful document proof. Whole-process observations include fresh guide configuration/startup and cannot estimate wrapper overhead.

A possible future *metadata-format-only* disposition is a compact digest token mapping to the full original identifier in the sidecar, with validation against the original source hash/span. **That change was not implemented or tried**; any resumption needs coordinator disposition. No alternate formatting/options campaign or broader source sweep was started.

## Implementation/source mapping

`Wrapper.lean` introduces one uniquely named diagnostic elaborator, not a replacement for polytime/fun_prop/ppt. Its body contains exactly **one** `evalTactic child` call. The parsed child is forwarded, not re-quoted/reconstructed; runtime kind is `Cslib.Tactic.PolyTime.tacticPolytime`. The helper reads environment output-path metadata and appends begin/end JSONL through IO, outside rollback-prone tactic messages/state. It samples IO.getNumHeartbeats and monotonic time around `observing`, then returns/rethrows the same Except. It does not save/restore proof state, alter options or call a registry/environment mutator. Lean's original evaluator/caller retains responsibility for state restoration.

The diagnostic compiles warning-strict and is consumed by normal import. Compiler setup required public/meta visibility for Lean tactic APIs and a meta IO helper, and corrected Nat sampling/type annotations; initial compiler logs are preserved separately from runtime acceptance. These are not changes to production imports or algorithms.

`sidecar.json` records the manually selected original pin, whole-file SHA256, repository path and **UTF-8 byte spans** for each original `polytime`. The runner verifies the bytes equal the expected original token before inserting any label. Diagnostic shifted spans are not claimed to be original positions. No quoted/generated child nodes are selected; labels identify authored occurrences, while an event ID also distinguishes the runtime attempt. No full-census parser/rewriter was built.

## Method limitations

- Current-thread raw HB divide by1000 for user units; not a sum of spawned task work. No async override was made. Future async claims require separate validation.
- Wall interval includes scheduling and forwarded dispatch, with sampling overhead; outer wrapper/telemetry also consumes the same shared command budget. No reset/increase/subtraction trick or proof/matching cache.
- The wrapper adds dispatch, recursion/macro scope and an imported diagnostic module. Import-only passed here, but complete acceptance did not; no semantic-equivalence generalization.
- `returned` and zero local goals do not establish retained final proof or accepted command. Backtracked invocations are attempts, not separate authored calls/final proof dependencies.
- An unmatched begin must be censored/unknown, never ordinary success. Parser encodes that policy, but no kill/crash/censor control was executed. IO failure invalidates the measurement; no success is inferred from absent telemetry.
- Expected caught failure and original `fail_if_success`/following `trivial` were planned unchanged but not executed after the guide mismatch. Do not claim preservation from source inspection alone.

## Reproduction/provenance

Fresh owned checkout `automation-wrapper-1155`, branch diagnostic/forwarding-wrapper-1155-codex, accepted seed/bootstrap once; only exact guide-import freshness targets and the standalone diagnostic module were compiled. No whole library/test build. Source/registry implementation and package files are otherwise unchanged. Compile command is recorded in environment.json; create the local output directory and compile Wrapper.lean at Diag1155/Wrapper.lean before the runner, with private independent mutable outputs.

```sh
python3 evidence/1155/wrapper-pilot-3a6d/run.py /absolute/pinned/source/checkout
python3 evidence/1155/wrapper-pilot-3a6d/parse.py
```

Runner enforces exact source HEAD, separate baseline/import-only/wrapped subprocesses, unchanged default/explicit200000 and refuses existing telemetry files. It stops at the first failed command. Logs, raw JSONL, source variants, sidecar and parsed JSON/CSV are retained. No new profiler framework or production PR. All jobs terminal; stopping for methodology review/disposition. Existing #1155 survey and LiuPass gaps remain open.
