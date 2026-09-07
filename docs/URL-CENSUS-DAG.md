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

This graph cannot close from a passing finite input, fixed-pin candidate
count, or reproducible TSV alone. U2b and U2c's exact interfaces are owned by
`docs/URL-CENSUS-INTERFACE.md` and `docs/URL-CENSUS-INPUT-INTERFACE.md`.
The next packet must freeze the canonical-owner/declaration/assurance
inputs and their generated joins. No URL coverage report is admitted here.
