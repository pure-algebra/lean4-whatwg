# Architecture

## Dependency direction

```text
first-order data (queue-with-sizes, chunks, strategies)
  -> per-class state machines (readable, writable, transform)
  -> piping requirements and realizers
  -> configuration, step relation, runs, observation masks
  -> logic (wlp, totality, EffHOL modality)
  -> combinator alphabet and typed targets
  -> host conformance harnesses
```

Nothing in `Whatwg/` depends on `WhatwgGates/`,
`WhatwgTest/`, or `harness/`. `WhatwgGates/` depends on nothing in `Whatwg/`. The
test tree imports both.

Each standard is its own Lake library (ruling R-V3(d)): `WhatwgInfra`,
`WhatwgEcma262`, `WhatwgWebIdl`, `WhatwgUrl`, `WhatwgHtml`, `WhatwgSvg` and
`WhatwgStreams`, and beside them `WhatwgAuto` for proof search, each owning its root module `Whatwg.<Standard>` and every
module under it, while the library `Whatwg` owns only the umbrella module
`Whatwg`. The library `WhatwgSignatures` owns `Whatwg.Signatures` and every
module under it in the same way (ruling R-W3); it is not a standard but the
`Effects.Signature` faces of the stateful layers, and it is the one production
library that imports the `effects` package, so no standard's library needs
`effects` to build. No module belongs to two libraries, so
`lake build WhatwgEcma262` builds that standard's import closure alone, and
`lake build Whatwg` builds every production module through the umbrella's
imports. Module names and namespaces are unchanged by the split. A module
placed directly under `Whatwg/` outside those seven directories has no owning
library and cannot be imported, so a new standard needs its own library entry
in `lakefile.toml`.

## Planned source tree

| Area | Public responsibility |
| --- | --- |
| `Whatwg/Ecma262` | ECMA-262 (ES2026), not a WHATWG standard: `Promise` (promise objects, reaction and capability records, resolving functions, `PerformPromiseThen`) and `Jobs` (job closures, `HostEnqueuePromiseJob`, the FIFO queue DB-03 makes state); beneath every Stratum S library, imports only `Whatwg/Infra` (ruling DB-11); bootstrapped 2026-09-06, declarations landed by the promise slices Q3 and Q3b (graph `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`) |
| `Whatwg/WebIdl` | Web IDL Standard: `Promise` (the spec-level verbs over `Ecma262.Promise`) and `Exceptions` (simple exceptions and `DOMException` names); imports `Whatwg/Ecma262` and `Whatwg/Infra` only; the binding layer stays `hostOnly`; bootstrapped 2026-09-06, declarations landed by the promise slices Q3 and Q3b (graph `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`) |
| `Whatwg/Signatures` | not a standard: the `Effects.Signature` faces of the stateful layers, each an adapter over its layer's step. `Ecma262` is the ECMAScript agent's (promise slice Q5, graph `PROMISE-PG-AGENT`, ruling R-W3): the signature, its canonical, lens and sum handlers, the step-fold `run` and the handler–step agreement laws. Imports `Whatwg/Ecma262` and, alone among the production trees, the `effects` package, through `Effects.Algebra.Sum` and never `Effects.Experimental`, `Effects.Trace`, `Effects.Flow` or `Effects.Family`; library `WhatwgSignatures` |
| `Whatwg/Url` | URL Standard: `PercentEncoding`, `Host`, `Record`, `Parser`, `Serializer`, `Origin`, `Rendering`, `FormUrlEncoded`, `Api/Url`, `Api/UrlSearchParams`, `Boundary`; U1 scaffold, of which `PercentEncoding` and `Boundary` carry the U3 percent-encoding declarations (graph `URL-PG-PERCENT`, `docs/URL-PERCENT-ENCODING-DAG.md`) and the other modules are still declaration-free; packets scheduled by `docs/URL-PACKAGE-PLAN.md` |
| `Whatwg/Infra` | the Infra Standard: the value universe every other standard is indexed by (Stratum V); byte, code-point, UTF-16 string and text helpers imported from its root; `docs/INFRA-PROOF-PLAN.md` tracks the wider census and assurance work |
| `Whatwg/Html` | the HTML content model ported from TyXML's row types under the HTML Standard's authority: `Schema` (authored source since 2026-09-06, first transcribed from TyXML at H2: tag and attribute universes, every named content and attribute set as a constructor-dispatch membership function, element and attribute rows; data and derived instances only), `Content` (admission, transparency, lattice, divergence rows, the checker with its located refusal, and since slice S4c the judgment of an SVG attribute's value by its name), `Node` (raw and typed trees, erasure, combinators, since slice S3b of `docs/SVG-PACKAGE-PLAN.md` the one top-down walk with its two laws, and since slices S5 and S6 the typed SVG node: `Svg`, whose attribute values are right by their types, `SvgRead`, its reader from a raw tree, and `SvgKeys` and `SvgValid`, the structure of a typed tree by its tags and keys with the law that this is the checker's verdict; and since slice S10 `SvgBuild`, `SvgPaint` and `SvgNest`, the constructors, the presentation attributes and the forest of a flat list of drawing calls that a program writes a picture with; and since slice S11 `SvgDraw`, the elements of a picture from exact geometry), `Print` (escaping and rendering: the HTML serialization with its decoder, and since slice S8 `Xml`, the XML serialization of DOM Parsing and Serialization, with `Xml/Productions`, the four productions of XML 1.0 that it cites, and since slice S10 `Picture`, the text of a typed picture in one call) and `Syntax` (the markup term `html!`), which carry declarations; `Svg`, the seam with `Whatwg/Svg` (the namespace automaton, the position as a sum of the HTML and the SVG position, and its transition; the checker `validIn` is one algebra of the walk over that position); and `Audit` (a docstring) |
| `Whatwg/Auto` | proof search, no standard: `RuleSets` declares the named Aesop rule banks that a proof module of any standard asks for (root `AGENTS.md`, "Proof search"; ruling R-S10). The one module of the production tree that imports `Aesop` directly; it states no law and declares no semantic declaration |
| `Whatwg/Svg` | W3C SVG 2, not a WHATWG standard, for inline use in an HTML tree (`docs/SVG-PACKAGE-PLAN.md`): `Data` (a finite universe, a set as a mask over it, and a name table with its two laws; it names no schema), `Schema` (the element, category and attribute universes, each element's attributes and content model, every set a mask; generated from the sealed svgwg definitions by `lake exe whatwg_svgdefinitions`, with the four content models stated as a sentence read in the authored `Schema/Readings`, and the authored `Schema/Universe` proving the name tables exact and each resolved set the join of what is stated) `Content` (the position in an SVG subtree, its transition, and the judgments of one node; slice S3a) and `Value` (slice S4: `Grammar`, a grammar as first-order data with its printer, reader and checker, and `Grammar/Laws`, their retraction laws, which no carrier imports; the reader's rule as a relation, the bridge to the bare expression, and the located refusal; and the carriers `Decimal`, `Magnitude`, `Length`, `Extent`, `PathData`, `Points`, `ViewBox`, `TransformList`, `LengthList` and `NumberList`, with `Attribute`, the one table from an element and an attribute to the kind of its value). It imports no module of `Whatwg/Html`: the seam that admits `svg` in an HTML tree is `Whatwg/Html`'s and imports this library. Since slice S10 `Geometry` computes with those values: `Arith`, `Order` and `Convert` (exact arithmetic, the order of the numbers, a number where a typed value stands), `Cursor` and `Pen` (what a path means for its point, and a builder stated against it), `Shape` (the curves of d3-shape) and `Affine` (a transform on a point, and the view that is moved and scaled). Since slice S11 the geometry is exact and computes in `Rat` of core, with one rounding where a number is written: `Vec` (a point), `Rational` (the number a typed value denotes, and the three roundings that write one), `Cubic` (a cubic Bézier segment: the point at a parameter, the part between two, the velocity), `Box` (a box, and the theorem that the box of a segment's four points holds it), `Affine/Map` (an affine map with its inverse, exact rotations, a `transform` attribute as a map, and the map of a view box onto a viewport), `Outline` (a box with round corners, a frame, an ellipse), `Root` (a square root to a number of places, a distance, a normal) and `Write` (segments into a `Path`, a box into a `ViewBox`); `Shape` is the curves of d3-shape as lists of segments, from end to end, open and closed. Since slice S12: `Smooth` (no corner at a joint of a spline), `Near` (what one rounding does to a curve), `Noise` and `Stroke` (a line as a filled outline of varying width), `Grid` (the seam between whole units and exact numbers), `Easing` (what an easing means exactly) and `Stack` (intervals in a row, each as long as its weight). `Scene` is what a picture is made of with no rational number in it: things that move (`Moves`), the join of two lists by key (`Join`), motion as data (`Motion`) and, since slice S13, where the nodes of a tree stand (`Tree`), what holds at every moment of a step (`Between`), widths that conserve at a fork (`Branch`) and the order of tracks in time (`Score`); a consumer that keeps its own proofs to the strict ceiling can use this layer and not the geometry, since in core the definition `Rat.add` reaches `Classical.choice`. `Data`, `Schema`, `Content`, `Value` and `Scene` are under the strict ceiling, and `Geometry` under the ordinary one, so that it can use the arithmetic of Lean's core library |
| `Whatwg/Streams/Data` | queue-with-sizes, chunk universe, size functions, high-water marks, desired size |
| `Whatwg/Streams/Strategy` | the IDL class surface that reads the strategy slots; the two strategy records, their size functions, and the extraction operations live in `Whatwg/Streams/Data/Strategy.lean` under `DATA-PG-QUEUE` (ownership repaired at the P3 landing, 2026-09-02) |
| `Whatwg/Streams/Readable` | `ReadableStream` state, default controller, default reader, generic reader mixin, tee, async iteration |
| `Whatwg/Streams/Readable/Byte` | byte controller, BYOB reader and request, pull-into descriptors (P9) |
| `Whatwg/Streams/Writable` | `WritableStream` state, default controller, default writer, backpressure |
| `Whatwg/Streams/Transform` | `TransformStream`, its controller, backpressure coupling |
| `Whatwg/Streams/Piping` | the piping requirements as a specification; the reference `pipeTo` algorithm as a realizer; `pipeThrough` |
| `Whatwg/Streams/Boundary` | foreign-boundary profiles: underlying source, sink, and transformer answers; abort signals; ArrayBuffer detachment |
| `Whatwg/Streams/Semantics` | configuration with the promise-job queue, labeled step relation, runs, frontiers, observation masks, equivalence |
| `Whatwg/Streams/Logic` | `wlp`, totality, the `wp` decomposition, the EffHOL modality instance |
| `Whatwg/Streams/Alphabet` | the closed combinator alphabet as first-order data |
| `Whatwg/Streams/Target/TypeScript` | typed target IR, lowering, rendering, decoding, simulation |
| `Whatwg/Streams/Bridge` | Node legacy streams calculus and Effect Channel embedding (P12) |
| `Whatwg/Streams/Meta` | declaration introspection and deterministic emitters |
| `Whatwg/Streams/Audit` | per-packet axiom receipts and closure snapshots |
| (`Hash`, from lean4-hash) | the proved SHA-256 the gates compute digests with; required by exact commit, never re-declared here |

Tests mirror these areas under `WhatwgTest/Streams/`. Durable attacks live
under `WhatwgTest/Streams/Counterexamples/`, while their stable registry and
contracts live under `test/`.

## Public API principles

URL reuses Infra's canonical byte, code-point, and string carriers after
their declaration records and import routes are verified. Pure parsing and
serialization sit below API record mutations. Dependency adapters for
Encoding, UTS #46, Web IDL, HTML origins, and File API entries are explicit;
none is an unrecorded host callback. URL test modules will mirror `Whatwg/Url`
under `WhatwgTest/Url` and be imported before the common axiom gate. The URL
root already reaches that gate through `Whatwg.lean`.

- Internal slots are fields of first-order state records; the XOR invariants
  the specification states in prose become constructors, not checked
  booleans.
- Abstract operations are total functions of state and decision, or
  relations where the specification leaves a choice.
- Every theorem names its observation mask.
- Host objects, promises, and closures never appear in state. A promise is a
  first-order record with a settlement status and the job-queue position of
  its reactions.
- Runtimes eliminate stream programs but never become canonical program
  data.
- Metaprogramming emits first-order declarations and digests, never stores
  raw `Lean.Expr` as semantic content.

## Observation faces

The library keeps four faces distinct:

1. structural syntax for induction and construction;
2. first-order checked state and combinator data for identity, sharing, and
   generation;
3. relational step and big-step meaning over explicit decisions;
4. executable bounded runners and host harnesses for decidable evidence.

Theorems relate these faces explicitly. No bounded runner is promoted into
the denotation merely because it executes, and no WPT pass is promoted into a
theorem.
