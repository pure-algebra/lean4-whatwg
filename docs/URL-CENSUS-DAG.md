# URL census assurance graph (`URL-PG-CENSUS`)

Status: open, 2026-09-05. This document owns the graph for the URL census
cutover. The URL inventory, census and census-input interface documents own
their respective tooling declaration records; `docs/URL-PACKAGE-PLAN.md`
owns phases. No URL denominator or
coverage state is established by this graph or by source candidate counts.

The authority is the pinned `url.bs` in `SPEC-MANIFEST.md`, with fetch and
independent hash evidence in `docs/PROVENANCE.md`. The U2a inventory is a
derived source view, not a model of URL algorithms. Its `TokenKind`, `Token`,
`Kind`, and `Entry` belong to `Gates.UrlInventory` and do not replace the
classified `Gates.Census.Row` carrier. Constructors and generated declaration
machinery inherit that tooling role. U2 must still generate and join the
per-declaration assurance snapshot described by `docs/AGENT-ROUTING.md`.

U2a evidence consists of the frozen finite battery committed at `afcd91d`,
the Lean input/partition/projection gate, a second source reader, and the
common module/axiom audit. Its observation is the exact ordered source-candidate
array with UTF-8 byte spans, kind, label, and nearest heading identifier.
It has no URL runtime observation mask, no URL execution theorem, and no
host evidence. All semantic/classification edges below remain open until
their separately frozen obligations are fulfilled.

## Current state

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

## Receipts

`docs/receipts/URL-PG-CENSUS.md` holds the edge table of 2026-09-05, moved
there verbatim under ruling R-V4. The U2a, U2b and U2c receipts are in
`docs/URL-PACKAGE-PLAN.md` and the handoff records of `COORDINATION.md`.
