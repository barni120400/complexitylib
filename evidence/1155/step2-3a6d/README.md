# Original automatic-proof replay, bounded step 2

Actual-main source pin: **3a6d770645c1217689da774f519cd785c253d8a2**. Same isolated worktree/bootstrap as pilot step 1, sole builder. No production/library/tactic/package edits, budget changes, new helper or full-library/test target.

| Restored original positive | Result at original default 200,000 | Whole-module process wall observation |
|---|---|---:|
| AddTrivial: `unfold addTrivial; polytime` | PASS | 1.73s |
| LiuPass threshold: `unfold thresholdValue; fun_prop` | FAIL: deterministic `whnf` timeout | 14.95s |
| #1063: original `hs_bound` and `hg` unfolded `fun_prop` blocks | PASS | 5.28s |

These are **whole current module diagnostic copies**, with only the historical explicit-composition replacement reverted to the original automatic proof body. Full original theorem context, preceding local facts, imports, encodings, programs, assertions, assumptions and following source remain. No imported named version of the theorem under test substitutes for its original body. This approach also keeps the private LiuPass threshold accessible in its real scope without importprivate/new API or a smaller arithmetic substitute. No module maxHeartbeats/maxRecDepth setter was found; original default 200,000 is retained, with no tactic-option override. Process wall includes imports, all other commands, startup and output; it is **not per-call timing** or a minimum-budget claim.

Historical before/after proof hunks are retained as raw `.diff` files: AddTrivial `e35a5b36`, LiuPass `19743e82`, #1063 `ba2a95aa`. `source-provenance.json` records paths, commits, complete current imports and comparison to historical imports. AddTrivial/#1063 import lists match their historical originals. LiuPass retains every historical import plus the two pure Nat foundation imports now present on actual main (`Asymptotics` and `Log`); those current-main additions and surrounding current proofs are preserved, so this is not a bit-identical historical environment replay. No historical import is removed. The exact source copies and commands/logs/results are archived. Only their listed import closure was refreshed (7,400 jobs, mostly cached artifacts); no whole Complexity or test target.

## Real remaining gap, not a newly blessed negative

The uninstrumented original LiuPass positive fails at its `fun_prop` call (line 217 in the diagnostic source), reaching its **actual 200,000** limit. Its original explicit production proof still exists unchanged; passing that proof would not establish automation parity.

One additional run enables `trace.Meta.Tactic.fun_prop` only around the threshold theorem. The same original automatic body fails at the same limit (14.15s whole-module observation). The trace begins with the ordinary `trans` route and a captured unary pair. Later candidate attempts carry unresolved second encoding metavariables through projection branches, including binary multiplication and legacy transition alternatives. The last observed application is `unary_mul` when `whnf` exhausts the budget. This is **attempted-search evidence**, not proof that this final rule alone causes the cost or that an ordering/global-policy change would fix it. Trace overhead is not an uninstrumented cost estimate; no phase split or failed-call heartbeat delta is claimed.

No engine redesign, encoder preference, budget increase, manual replacement of the regression or new mathematical supplier was attempted. No failing production test/PR was opened. The requested representative regression suite remains incomplete because this original positive is still a real gap; passing source copies are not proposed wholesale as production tests. Compact test-only additions/missing-certificate controls can be reviewed in a later bounded batch once disposition of this gap is decided.

The exact historical multi-depth Boolean probe source was not recovered by the prior preparation, so no generated substitute was introduced here. Existing current depth-one Boolean CI coverage is reused. Extraction12k, Cloud and landed #1168 positives were likewise not rerun merely to duplicate correctness coverage.

## Reproduction / source guard

```sh
python3 evidence/1155/step2-3a6d/run.py /absolute/isolated/source/checkout
python3 evidence/1155/step2-3a6d/run.py /absolute/isolated/source/checkout --trace-failures
```

Runner now refuses a mismatched source HEAD before Lean starts. The same reversible expected-HEAD guard was added to the two prior pilot runners, as independently suggested; **no prior measurement was rerun** for that addition. Wrong-HEAD refusal controls execute git only and are recorded separately. Existing raw pilot sources/logs/exports/results are unchanged. `--trace-failures` is intentionally bounded to the actually mapped failed LiuPass theorem; it refuses unknown failed cases instead of starting a broad tracing campaign.

All local jobs terminal. This is a source replay/status artifact, not a whole-survey or readiness claim. Dynamic per-call metrics for these originals remain null; existing static census is unchanged.
