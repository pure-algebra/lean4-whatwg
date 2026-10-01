# Receipts log of `URL-PG-CENSUS`

This log holds the history of `docs/URL-CENSUS-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/URL-CENSUS-DAG.md`.

## URL census assurance graph (`URL-PG-CENSUS`)

Moved verbatim from the edge table under the title of `docs/URL-CENSUS-DAG.md` at `325d5d5`; its "Current state" section supersedes it.

| Edge | State | Evidence and remaining obligation |
| --- | --- | --- |
| identity | `required-open` | `urlinventory` checks the pin and lexical spans. U2c's `urlcensus` reads the six authored inputs and checks unique in-span anchors, raw source/input/span digests, origin/owner joins and exactly-one disposition resolution. Canonical declaration/assurance identity joins remain open. |
| construction | `required-open` | U2b adapts the canonical `Gates.Census.Row` through `SourceRow`. U2c's `Inputs` is only a raw authored-file view; the two source projections are Lean-generated and checked for byte drift. Generated declaration and assurance joins remain open. |
| semantics | `required-open` | Independent review accounts for every candidate through a containing row, specific explanation or heading; it reviews each authored disposition and dependency list. Modal requirements, law prose and shared bodies are retained. Dependencies name obligations, not implementations. Declaration correspondence and semantic assurance remain open. |
| laws | `required-open` | U2a/U2b/U2c retain frozen finite scanner, join, syntax, priority, anchor and exact-projection probes. U2c rejects unresolved rows and unused dispositions, overrides and dependency inputs. These are finite tooling receipts, not general parser laws; numerator/denominator agreement remains open. |
| representation | `required-open` | Candidate keys are pin-local ordinals. U2b's interval forest retains parser states, shared host/hostname bodies, tables/lists and initial values. Canonical-owner relationships to Infra and other standards still require per-declaration records and checked joins. |
| counterexamples | `required-open` | Inventory, assignment and U2c authored-input packets are frozen; retained regression identities and current closure states are owned by the central register. Coverage/declaration-join attacks still require their own packet. |
| bridges | `not-applicable` | No host, third-party implementation, or cross-language equivalence is claimed by source census tooling. Those bridges belong to their URL semantic families. |
| targets | `not-applicable` | The TSV is an inventory projection, not executable URL target code. No TypeScript lowering is introduced. |
| trust | `required-open` | Scanner, assignment and U2c reader/test declarations enter the common module and standard-base axiom audit; actual receipts are in the URL plan. Future assurance modules must enter it before cutover. Choice minimization does not silently remove tooling dependencies from the receipt. |
| coverage | `required-open` | No admitted URL coverage denominator or report exists. Authored source classifications now have a checked projection; the declaration/numerator join and its gate remain required under `docs/SPEC-COVERAGE.md`. |

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/URL-CENSUS-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/UrlCensus.lean` and its projection `generated/graphs/URL-PG-CENSUS.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30. No edge has moved since
the U2c handoff of 2026-09-05, and no ruling in `COORDINATION.md` changes one.
Ruling R-V4 sets the rule: an edge is `required-closed` only when every ground
this document or a ruling states for keeping it open is discharged by
something named in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The canonical declaration and assurance identity joins; the per-declaration assurance snapshot has no generator (debt D47). `lake exe whatwg_urlinventory` checks the pin and lexical spans, and `lake exe whatwg_urlcensus` checks the six authored inputs, in-span anchors, digests, origin and owner joins and disposition resolution |
| construction | `required-open` | The generated declaration and assurance joins (debt D47). U2b adapts `Gates.Census.Row` through `SourceRow`, and the two source projections are Lean-generated and drift-checked |
| semantics | `required-open` | Declaration correspondence and semantic assurance. Independent review accounted for every candidate and reviewed each authored disposition and dependency list |
| laws | `required-open` | Numerator/denominator agreement. The frozen scanner, join, syntax, priority, anchor and projection probes are finite tooling receipts, not general parser laws |
| representation | `required-open` | Canonical-owner relationships to Infra and other standards, which need per-declaration records and checked joins |
| counterexamples | `required-open` | Coverage and declaration-join attacks need their own packet. The retained tooling regressions `URL-INV-CE-001` to `005`, `URL-CEN-CE-001` and `URL-INP-CE-001` are `CLOSED` in `test/counterexamples/REGISTER.md` |
| bridges | `not-applicable` | Source census tooling claims no host, third-party or cross-language relation; those bridges belong to the URL semantic families |
| targets | `not-applicable` | The TSV is an inventory projection, not executable URL target code; no TypeScript lowering is introduced |
| trust | `required-open` | The assurance modules of the declaration and assurance join do not exist yet and must enter the common module and axiom audit before cutover. The scanner, assignment and U2c reader and test declarations are in that audit today, with receipts in `docs/URL-PACKAGE-PLAN.md` |
| coverage | `required-open` | No admitted URL coverage denominator or report exists; the declaration/numerator join and its gate remain required under `docs/SPEC-COVERAGE.md` |

This graph cannot close from a passing finite input, fixed-pin candidate
count, or reproducible TSV alone. U2b and U2c's exact interfaces are owned by
`docs/URL-CENSUS-INTERFACE.md` and `docs/URL-CENSUS-INPUT-INTERFACE.md`.
The next packet must freeze the canonical-owner/declaration/assurance
inputs and their generated joins. No URL coverage report is admitted here.
