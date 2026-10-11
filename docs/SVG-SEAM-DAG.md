# SVG seam assurance graph (`SVG-PG-SEAM`)

Status: open, 2026-10-11. This document owns the graph for the admission of SVG content in an
HTML tree. `docs/SVG-PACKAGE-PLAN.md` owns the slices, the rulings SV-1 to SV-30 and the list
of anticipated nodes (its section 6).

The graph opened at slice S3b, when `Whatwg.Html.Content.validIn` first accepted a tree that
holds `svg`. An admission needs a proof graph (`docs/AGENT-ROUTING.md`, "Assurance threshold").

**Authority.** The HTML Standard at its pin owns the seam: where `svg` stands, where the
namespace changes, and how a foreign element is written. SVG 2 at `w3c/svgwg` commit `47e645ef`
owns the elements, their content models, their attributes and the grammars of their values.
CSS Transforms 1 at `w3c/csswg-drafts` commit `50337328` owns the value of the three transform
attributes. `SPEC-MANIFEST.md` holds the pins, and `docs/PROVENANCE.md` their digests.

**Fence.** The graph owns eleven modules of `Whatwg/Svg/`: the three of `Data`, the five of
`Schema`, the authored `Schema/Universe`, `Content/Context`, and `Value/Attribute`, which says
which grammar judges which attribute. The value grammars under `Whatwg/Svg/Value/` are the leaf
record `SVG-LF-GRAMMAR`, which contributes to this graph's representation edge. The seam itself
is modules of `Whatwg/Html/`: `Svg`, `Node/Walk`, `Schema/Foreign` and `Content/Values`. They
stay under the unrouted prefix `Whatwg.Html` (debt D57), as every module of the HTML package
does. This graph cites their theorems as grounds and does not own them.

**Observation.** There are two judgments, and neither has an observation mask: each reads the
tree and nothing else. `validIn ctx n = true` says that the raw tree `n` may stand at the HTML
position `ctx`. `valuesOk n = true` says that each value of an SVG attribute in `n` is of its
grammar, where the package holds one. No host runs in this graph.

## Current state

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/SvgSeam.lean`, rendered to `generated/graphs/SVG-PG-SEAM.md` by
`lake exe whatwg_ledger --write`, and checked by `lake exe whatwg_ledger`. The history of this
document is in `docs/receipts/SVG-PG-SEAM.md`.

## Claim scope

- The graph says what the checker admits. It does not say that a browser parses a printed tree
  back to the same tree: no parser exists in this package (ruling HP-8).
- The SVG content model is the index of the sealed definitions files. A sentence of a chapter
  that narrows a model is not read, apart from the four readings of ruling SV-4.
- The HTML checker's own fidelity to the standard is the HTML package's edge, and it is open
  (debt D57). This graph bounds the change to that checker by two equations and no more.
- `validIn` reads no SVG value (ruling SV-30). `valuesOk` judges the values of six attributes:
  `d`, `points`, `viewBox` and the three transform attributes. Any other SVG attribute takes
  any text, and CSS is never judged (ruling SV-14).
- A grammar's description is the seat's transcription of the sealed productions. No gate
  compares the two languages. Each grammar module names the productions it restructured.
- `html!` runs a literal value through its grammar and proves nothing of it.
