# ONE-file Cloud source/mapping preparation — NOT EXECUTED

Pin **3a6d770645c1217689da774f519cd785c253d8a2**, original path `Complexity/Computability/PCP/Encoded/Cloud.lean`,174 lines. Source-only artifacts; **zero Lean/elaboration/bootstrap/cache/build operations**. Audit retains the sole-builder slot. Explicit later handoff is required before execution.

## Eligibility and exact scope

Manual source inspection finds **3 authored polytime calls,0 fun_prop calls,0 ppt calls**, below the20-call bound. Each is a standalone `polytime` line without arguments, quotations, generated source, nested tactic syntax, semicolon sequencing or macro/elab declarations:

| Original declaration | Original line | Child retained |
|---|---:|---|
| isPolyTime_halfEdges |75|polytime|
| isPolyTime_endpoint |86|polytime|
| isPolyTime_cloud |96|polytime|

The3 `@[fun_prop]` occurrences are attributes, **not instrumented calls**. Every other Lean tactic/proof/data definition remains unchanged and unmeasured. This is not a full-census rewriter. No lost-history or baseline success claim is made by preparation.

`baseline/` contains the complete original source byte-for-byte, not rebuilt proof snippets. `import-only/` adds ONLY `import Diag1155.Wrapper` after the existing import block. `wrapped/` additionally prefixes only the3 exact parsed-child source tokens with compact diagnostic syntax. Original programs, declarations, full captured Input/input/encoding scopes, truth/default/empty behavior, expressions, imports/order, attributes and proof sequence are retained. No tactic argument, proof goal or arithmetic expression is reconstructed. Full-text reversal is checked: remove wrapper prefixes → exact import-only; remove extra import → exact original bytes.

`mapping.json` records original whole-file SHA256, pin/path, verified UTF-8 byte spans/lines, full IDs and collision-checked short tokens. Every span is verified to slice exactly `polytime`. It references the **unchanged** b83 diagnostic implementation source hash; no new wrapper/helper/registry implementation is introduced.

## Module/private-name context

The source uses `module`, namespace Cslib.PCP.Encoded.Graph, and `@[expose] public section`, with **no explicit private declarations**. Each variant retains the ORIGINAL relative path below its variant root. A later diagnostic CLI should use Lean's existing `--root=<variant-directory>` with that complete path, so the computed main module remains **Complexity.Computability.PCP.Encoded.Cloud**, rather than renaming it Cloud-baseline. This flag's meaning was inspected in pinned Lean Shell.lean145/532; it has **not** been executed here.

Keep the pinned project's original leanOptions in ALL modes (`acceptance-config.json` records them), warning-strict behavior and default200000. There is no file heartbeat/recursion override. Do not disable linters or force async to make the trial pass. The exact execution driver/setup remains subject to builder/method handoff. Import closure must come from a private pinned checkout, never a foreign builder's outputs.

Stable main-module and public names do **not** promise identical generated private auxiliary names or opaque selected data: wrapper dispatch/fresh macro scopes can affect generated names. Pure source/data blocks are byte-preserved, but no compiled-data identity is inferred. Report any real context/import mismatch instead of patching algorithms or inserting compatibility aliases.

## Separate fail-closed acceptance contract

`acceptance-config.json` and `cloud_acceptance.py` are a small **Cloud-only** future contract, not a collector or extension of the old3-call checker. Future runtime provenance must bind this mapping digest, pin, unchanged implementation, exact calls, run ID, variant source hashes and main-module name. ALL3 whole-file command modes must return0. Wrapped data must have exactly one matching begin/end for EACH original call, returned/zero goals, original200000 and nonnegative counters. Partial/censored/unobserved/duplicate/repeated/unmatched/provenance-invalid data or a failed later whole-file proof cannot pass merely because some wrappers returned.

Preparation itself is `prepared_not_executed` and is explicitly rejected as execution evidence. `preflight.py` verifies source hashes/spans and runs ONE in-memory **SYNTHETIC** complete-contract smoke check plus10 rejection checks. These mock counters are not measured data; only control outcomes are saved. No actual Cloud runtime-sidecar/command results/event telemetry were created. Old b83/9f strict/partial checkers and all real accepted/rejected data remain untouched.

## Reproduce preparation ONLY

```sh
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/cloud-source-prep-3a6d/prepare.py
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/cloud-source-prep-3a6d/preflight.py
```

Both use git/file/Python data APIs only, no Lean, package or cache command. Source construction is deliberately specific to the three manually inspected Cloud lines, with cardinality/reversibility guards; it is not an automatic framework. `preflight-results.json` says actual_Cloud_result=NOT_RUN. Do not execute variants from this task or mistake synthetic acceptance for original source acceptance.

All jobs terminal. Full1155 survey, LiuPass gap and caller expansion remain OPEN. Stop for source/mapping/config review and explicit sole-builder handoff before any elaboration.
