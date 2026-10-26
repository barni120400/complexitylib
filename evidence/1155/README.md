# Initial static automation census (#1155)

Pinned source: **67c6ea4d7d59bf8089f7b305394649b0cf033c1c** (actual main at collection).
Worker `review_560`, read-only survey role, under [the coordinator claim](https://github.com/cslib-community/complexitylib/issues/1155#issuecomment-6411747610).
No Lean/Lake execution, elaboration, build-output access, cache bootstrap, production edit or tactic design was performed.

## Static scope

Every `.lean` file under the four requested roots is scanned from `git archive` at the pin. Counts are lexical candidates, **not AST-verified invocations or executed proof goals**. Multiple fallback tactics in one proof count separately; generated/quoted tactics are separated. All candidate locations have pinned GitHub source links.

| Root | Lean files | polytime ordinary candidates | fun_prop ordinary candidates | ppt ordinary candidates | Total ordinary |
|---|---:|---:|---:|---:|---:|
| Complexity | 2216 | 215 | 2161 | 89 | 2465 |
| ComplexityTests | 615 | 344 | 945 | 231 | 1520 |
| abstracts | 51 | 0 | 6 | 2 | 8 |
| guide | 5 | 4 | 6 | 0 | 10 |
| **Total** | **2887** | **563** | **3118** | **322** | **4003** |

There are another **9 quoted/generated candidates** (6 polytime, 3 fun_prop), for **4012 candidates** including quotes. Of **5827** exact unmasked code tokens, **1815** attribute/registration, quoted-name, rule-set or metadata references are excluded and listed separately. Markdown files in the same roots have zero matching tokens; other non-Lean formats are not interpreted as Lean call sites.

Files:
- [census.py](census.py): standalone reproducible script, using only Python's standard library and read-only Git archive.
- [static/callsites.csv](static/callsites.csv), [static/callsites.json](static/callsites.json): all candidates, locations, declaration/nearby text signals and prior option directives.
- [static/excluded-code-tokens.csv](static/excluded-code-tokens.csv): auditable exclusions.
- [static/summary.json](static/summary.json): counts by root/tactic/classification and method limits.
- [published-evidence.json](published-evidence.json): 13 curated historical case/control/request records, exact URLs and source-body hashes; these are not current-pin timings.
- [published-source-index.csv](published-source-index.csv): broader keyword-discovered comment index, not a validated regression count.

Reproduce without Lean or caches:

```sh
python3 evidence/1155/census.py --revision 67c6ea4d7d59bf8089f7b305394649b0cf033c1c --output /tmp/automation-static-census
```

The scanner masks nested Lean comments, ordinary strings and raw strings while retaining line/column coordinates. Columns count Unicode code points. It classifies obvious attributes, rule-set references and quoted identifiers lexically; unusual quotation/antiquotation/name forms still need spot checks. Nine generated candidates are not ordinary authored proof calls.

**Budget and manual-work signals are deliberately qualified.** `prior_option_directives` lists the last three textual setters with location/value/`in`, not the effective option scope. Section, command-local and nested scopes are not elaborated. No setter is automatically labelled a raised budget. Declaration signals appear at 1210 candidates for explicit composition, 99 for fallback syntax, 345 for negative controls and 24 for search controls; these are repeated per-candidate observations in enclosing textual declarations, not counts of distinct workarounds or proof failures. The presence of `.comp` can be routine mathematics, not evidence automation failed.

## Already-published measurements

The JSON retains historical revisions, units, limits and coverage qualifications. Short guide:

| Case | Published result | Qualification |
|---|---|---|
| AddTrivial | minimum fun_prop maxSteps 25–32 (main9e) →401–512 (8654) →171–180 (96cf) →21–24 (a06) | Search-step intervals, not wall time. Original automated probe was retained independently of explicit production proof. |
| Cloud endpoint | 177–192 →513–768 →257–320 maxSteps | Import/revision-specific; not fresh current main. |
| Cloud halfEdges/range controls | halfEdges97–128 at main/96cf; cloud/addLoops range≤16 | Useful unaffected controls; intermediate revision not measured. |
| Extraction:50 | reviewer reports25757→3384 HB; controlled order probe ~0.621 HB table projection vs3307.591 HB matching | Original12000 retained. Duplicate-entry hypothesis rejected. Failed frontend/removal probes were not shipped. |
| LiuPass threshold | original unfolded fun_prop passes at96cf, times out200000 at a06 | Demonstrated composition-order tradeoff; explicit composition repaired same program/header. |
| #1063 unary nest | hosted whnf timeout471;369 shares declaration budget; author reports module~2s after explicit composition | 200k unchanged. Not two independently timed calls or a controlled per-call wall-time speedup. #733 qualifies causal evidence. |
| Nested Boolean ite_decide | kernel-only positive depths2/4/8/12:60/91/162/247→291/554/1093/1654 HB | Whole-command/import-sensitive reviewer profile; linear growth. Library-import positives unchanged; some new unary conditional goals improve. |
| PPT114 preparation | first attempt10273.059 HB setup vs228.614 matching;2359 function/lambda entries | Historical494 profile only; not the cost of every later branch or a current benchmark. |
| PPT114 failed applies | five unrelated rules4219.255 HB of a4297-HB interval | Historical00d6; continuation not yet expanded in that interval. |
| PPT59 shared budget | negative returns108233.470 HB (~6.47s traced), following positive exhausts shared200000 | Must not call this a negative-alone200k timeout. |
| Boolean facade | module client lost bool_and/bool_not; restored public import fixed it | Functional/import regression; no time metric. Some composite goal failures were pre-existing. |
| #1148 filter | published API-docs failure at8d845488; pre-restack guide passed | Different contexts, causal hypotheses unconfirmed in the collected record; sole builder's current diagnosis/fix is pending. |

Sources: [AddTrivial/Cloud](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6400324902), [core order/Extraction/LiuPass](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6400732408), [phase-separated Extraction](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6400425510), [nested conditionals](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6403982121), [114 setup](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6392036946), [114 failed applies](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6392560858), [59 shared budget](https://github.com/cslib-community/complexitylib/issues/608#issuecomment-6393958663), [1063 failure](https://github.com/cslib-community/complexitylib/pull/1063#issuecomment-6403509003), [1063 repair](https://github.com/cslib-community/complexitylib/pull/1063#issuecomment-6404882875), [733 qualification](https://github.com/cslib-community/complexitylib/issues/733#issuecomment-6403782631), [1148](https://github.com/cslib-community/complexitylib/issues/1148).

## Coverage gaps / next coordinator batch

- **Zero calls were dynamically measured by this census.** Every current entry has null time, heartbeats, rules fired and effective budget. Historical values are never pasted onto current call sites.
- Need actual per-call execution/success, fired rules, preparation/matching split and effective option scopes at a controlled revision/import context. Static counts do not determine what fraction syntax-directed automation could solve.
- Historical results use multiple staging/main revisions and different measurement methods; they cannot be pooled into a speed ranking. Some old automatic proof blocks have since become explicit composition, so historical-to-current mapping is not one-to-one.
- The 13 curated records are an **initial consolidation**, not proof that every regression in the last two weeks was recovered. The keyword index provides a review backlog; no missing timing is invented.
- Preserve positive/negative pairing and shared-command budgets in future representative tests, especially literal PPT59, both encoding orders of114, and actual guide imports. The auxiliary Binary-only12k performance follow-up is not an original repository acceptance limit.
- #1148 diagnosis belongs to the sole builder. Initial issue hypotheses do not establish rule-order/registration causality; incorporate its durable measured result when available rather than duplicate it.
- The representative CI suite and dynamic phase remain coordinator-owned subsequent work. No production PR, new framework or redesign is included in this evidence branch.
