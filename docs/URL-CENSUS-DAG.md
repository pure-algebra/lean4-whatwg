# URL census assurance graph (`URL-PG-CENSUS`)

Status: open, 2026-09-05. This document owns the graph for the URL census
cutover. `docs/URL-INVENTORY-INTERFACE.md` owns the U2a tooling declaration
records; `docs/URL-PACKAGE-PLAN.md` owns phases. No URL denominator or
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
| identity | `required-open` | Source pin and lexical spans are checked by `lake exe urlinventory`. U2b has reviewed authored source identities/spans and a strict origin/owner join; the fixed-pin data reader, generated anchors/digests and exactly-one disposition/declaration joins remain open. |
| construction | `required-open` | U2a has executable source inventories. U2b adapts the canonical `Gates.Census.Row` through `Gates.UrlCensus.SourceRow`, with frozen finite assignment probes. Authored dispositions and generated assurance joins remain to be implemented under their own packet. |
| semantics | `required-open` | Independent review accounts for every current source candidate through a containing row, a specific explanation or a heading. Modal requirements, law prose and shared bodies are retained. The authored files are not yet read by a Lean data gate; semantic dispositions, dependencies and declaration correspondence remain unadmitted. |
| laws | `required-open` | U2a checks partition and deterministic regeneration. U2b's frozen finite battery exercises row/explanation/dependency rejection and complete candidate assignment; it is not a theorem for arbitrary input. No unused disposition input and numerator/denominator agreement still require their own checks. |
| representation | `required-open` | Candidate keys are pin-local ordinals. U2b's interval forest retains parser states, shared host/hostname bodies, tables/lists and initial values. Canonical-owner relationships to Infra and other standards still require per-declaration records and checked joins. |
| counterexamples | `required-open` | Original inventory and census acceptance packets are frozen. `URL-INV-CE-*` and the independently retained `URL-CEN-CE-001` are closed finite regressions. Fixed-pin data-reader, disposition and coverage-join attacks remain to be frozen. |
| bridges | `not-applicable` | No host, third-party implementation, or cross-language equivalence is claimed by source census tooling. Those bridges belong to their URL semantic families. |
| targets | `not-applicable` | The TSV is an inventory projection, not executable URL target code. No TypeScript lowering is introduced. |
| trust | `required-open` | U2a and U2b scanner/join/test declarations enter the common module and standard-base axiom audit; actual receipts are in the URL plan. Remaining data-reader and assurance modules must enter it before cutover. Choice minimization is a separate proof-quality objective and does not silently remove tooling dependencies from the receipt. |
| coverage | `required-open` | No URL coverage denominator exists. All intended rows need reviewed dispositions and a checked numerator join before any URL report can be emitted under `docs/SPEC-COVERAGE.md`. |

This graph cannot close from a passing finite input, fixed-pin candidate
count, or reproducible TSV alone. U2b's exact interface is owned by
`docs/URL-CENSUS-INTERFACE.md`. Its next packet must freeze the fixed-pin
data reader, the disposition/dependency/canonical-owner inputs and their
generated joins. No URL coverage report is admitted at this checkpoint.
