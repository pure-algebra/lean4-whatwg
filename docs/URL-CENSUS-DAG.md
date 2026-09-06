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
| identity | `required-open` | Source pin and lexical spans are checked by `lake exe urlinventory`; stable semantic IDs, containing semantic spans, and exactly-one-owner joins remain to be frozen and reviewed. |
| construction | `required-open` | U2a has executable source inventories and finite acceptance probes. The classified census carrier, authored dispositions and generated assurance joins remain to be implemented under their own packet. |
| semantics | `required-open` | Every candidate needs a reviewed role, including non-algorithm prose, parameter definitions, notes/examples, parser states, API exposure and external requirements. Lexical `<dfn>` spans do not establish containing semantic spans. |
| laws | `required-open` | U2a checks byte partition and deterministic regeneration. Census join rejection laws, no unused classification input, no duplicate semantic owner, and numerator/denominator agreement need their own frozen evidence. No arbitrary-source lexical parsing theorem is claimed. |
| representation | `required-open` | Candidate keys are pin-local ordinals with byte spans and digests. The semantic census must retain parent/child links, shared algorithm bodies, source tables/lists, and explicit relationships to canonical Infra and other standard declarations. |
| counterexamples | `required-open` | Frozen `URL-INV-P01` through `URL-INV-P11` are acceptance probes. Review regressions are retained separately under stable `URL-INV-CE-*` IDs in the central register. Further semantic-span and classification attacks remain to be frozen. |
| bridges | `not-applicable` | No host, third-party implementation, or cross-language equivalence is claimed by source census tooling. Those bridges belong to their URL semantic families. |
| targets | `not-applicable` | The TSV is an inventory projection, not executable URL target code. No TypeScript lowering is introduced. |
| trust | `required-open` | U2a scanner/test declarations are checked by the common module and standard-base axiom audit. Future census/assurance modules and their exact public declarations must also enter that audit before cutover. |
| coverage | `required-open` | No URL coverage denominator exists. All intended rows need reviewed dispositions and a checked numerator join before any URL report can be emitted under `docs/SPEC-COVERAGE.md`. |

This graph cannot close from a passing finite input, fixed-pin candidate
count, or reproducible TSV alone. Its next packet must freeze the semantic
classification join and the containing spans described in the URL plan.
