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

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/UrlCensus.lean`, rendered to
`generated/graphs/URL-PG-CENSUS.md` by `lake exe whatwg_ledger --write`, and
checked by `lake exe whatwg_ledger`. The table this section held before the
ledger is in `docs/receipts/URL-PG-CENSUS.md`.

## Claim scope

This graph cannot close from a passing finite input, fixed-pin candidate
count, or reproducible TSV alone. U2b and U2c's exact interfaces are owned by
`docs/URL-CENSUS-INTERFACE.md` and `docs/URL-CENSUS-INPUT-INTERFACE.md`.
The next packet must freeze the canonical-owner/declaration/assurance
inputs and their generated joins. No URL coverage report is admitted here.

## Receipts

`docs/receipts/URL-PG-CENSUS.md` holds the edge table of 2026-09-05, moved
there verbatim under ruling R-V4. The U2a, U2b and U2c receipts are in
`docs/URL-PACKAGE-PLAN.md` and the handoff records of `COORDINATION.md`.
