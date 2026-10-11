# SVG seam assurance graph (`SVG-PG-SEAM`)

Status: open, 2026-10-11. This document owns the graph for the admission of SVG content in an
HTML tree. `docs/SVG-PACKAGE-PLAN.md` owns the slices, the rulings SV-1 to SV-27 and the list
of anticipated nodes (its section 6).

The graph opened at slice S3b, when `Whatwg.Html.Content.validIn` first accepted a tree that
holds `svg`. An admission needs a proof graph (`docs/AGENT-ROUTING.md`, "Assurance threshold").

**Authority.** The HTML Standard at its pin owns the seam: where `svg` stands, where the
namespace changes, and how a foreign element is written. SVG 2 at `w3c/svgwg` commit `47e645ef`
owns the elements, their content models and their attributes. `SPEC-MANIFEST.md` holds both
pins, and `docs/PROVENANCE.md` their digests.

**Fence.** The graph owns the ten modules of `Whatwg/Svg/` that declare a constant: the three
of `Data`, the five of `Schema`, the authored `Schema/Universe`, and `Content/Context`. The
seam itself is three modules of `Whatwg/Html/`: `Svg`, `Node/Walk` and `Schema/Foreign`. They
stay under the unrouted prefix `Whatwg.Html` (debt D57), as every module of the HTML package
does. This graph cites their theorems as grounds and does not own them.

**Observation.** The judgment is `validIn ctx n = true`: the raw tree `n` may stand at the
HTML position `ctx`. It has no observation mask: it reads the tree and nothing else. No host
runs in this graph.

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
- An attribute's value is not judged before slice S4 (ruling SV-13), and CSS is never judged
  (ruling SV-14).
