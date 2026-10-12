# SVG seam assurance graph (`SVG-PG-SEAM`)

Status: open, 2026-10-11. This document owns the graph for the admission of SVG content in an
HTML tree. `docs/SVG-PACKAGE-PLAN.md` owns the slices, the rulings SV-1 to SV-35 and the list
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
is modules of `Whatwg/Html/`: `Svg`, `Node/Walk`, `Schema/Foreign`, `Content/Values`, and the
typed node `Node/Svg` with its reader `Node/SvgRead`. They stay under the unrouted prefix
`Whatwg.Html` (debt D57), as every module of the HTML package does. This graph cites their
theorems as grounds and does not own them.

**Observation.** There are two judgments, and neither has an observation mask: each reads the
tree and nothing else. `validIn ctx n = true` says that the raw tree `n` may stand at the HTML
position `ctx`. `valuesOk n = true` says that each value of an SVG attribute in `n` is of its
grammar, where the package holds one. A typed tree (`SvgNode`) has the second judgment by its
type: the raw tree of every typed tree passes it. No host runs in this graph.

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
- `validIn` reads no SVG value (ruling SV-30). `valuesOk` judges the values that the table of
  `Whatwg/Svg/Value/Attribute.lean` gives a kind: `d`, `points`, `viewBox` and the three
  transform attributes on any element, `x1`, `y1`, `x2` and `y2` on `line` (ruling SV-32), and
  the nine geometry properties on the elements the sealed chapter names (ruling SV-35). Any
  other SVG attribute takes any text, and CSS is never judged (ruling SV-14).
- The check of a length refuses some values that SVG admits: a unit the sealed table does not
  name, `calc()`, a CSS comment and a CSS escape (ruling SV-31). The check of a size refuses a
  negative one, which SVG treats as the initial value (ruling SV-35).
- A typed tree has good values and may still be refused: the type gives no structure.
  `SvgNode.okAt` judges the structure by tags and keys, and `SvgNode.validAt_toRaw` says that
  its verdict is the checker's on the raw tree. For a tree that `html!` builds, the structure
  is one kernel evaluation of that test. It is one evaluation, and not a proof composed from
  the nodes.
- A refusal of a value names the offset at which no reading of its grammar continues. When the
  text has a character there, every text that agrees with it through that character is refused
  at the same offset (`Syn.explain_local`). A refusal at the end of a text says nothing of a
  longer text.
- A grammar's description is the seat's transcription of the sealed productions. No gate
  compares the two languages. Each grammar module names the productions it restructured.
- `html!` reads a literal value with its grammar and holds the typed value. It proves nothing of a value whose attribute has no kind: that value is text.
