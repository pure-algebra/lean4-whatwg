import Whatwg.WebIdl.Promise
import Whatwg.WebIdl.Exceptions

/-!
# Whatwg.WebIdl

The WHATWG Web IDL Standard: the specification-level vocabulary every WHATWG
algorithm uses to speak about promises and exceptions, defined as thin
wrappers over ECMA-262's operations.

Authority: `whatwg/webidl` commit `a652053f1e74e4aaf647528deb174012ed6c909f`
("Review Draft Publication: March 2026"), source `index.bs`, sealed under
`vendor/whatwg-webidl-a652053f/`. `SPEC-MANIFEST.md` owns the pin and
dispositions; `docs/PROVENANCE.md` owns the fetch and digest cross-check.

Layering (ruling DB-11 in `docs/DESIGN-BASIS.md`): this library sits beneath
`Whatwg.Streams` and imports `Whatwg.Ecma262` and `Whatwg.Infra` only. The
binding layer (conversions, brand checks, overload resolution) stays
`hostOnly` at the boundary as the Streams manifest already rules; only the
promise and exception vocabulary is reified here.

Landed surface, frozen by `PROMISE-PG-FIRST`
(`test/contracts/promise-first-packet.contract.md`) and built by the Q3
builder seat:

- `Whatwg/WebIdl/Promise.lean` — "a new promise", "a promise resolved with",
  "a promise rejected with", "resolve", "reject", "mark as handled", "react"
  with "upon fulfillment" and "upon rejection", and "wait for all" as the
  settled predicate in `Prop` and `Bool` form plus the ordered result and
  first-rejection short-circuit (1 type, 12 functions, 17 theorems). Every
  operation is a thin wrapper over `Whatwg.Ecma262.Promise`; this module mints
  no state of its own.
- `Whatwg/WebIdl/Exceptions.lean` — the five simple exception kinds, the 32
  base `DOMException` error names in specification order, and the first-order
  exception carrier `Whatwg.Streams.Boundary.Exception` embeds into
  (3 types, 5 functions, 15 theorems). Part C of the packet, landed last per
  R-P14, so the allocation identity the Streams constructors carry is
  preserved rather than erased. It declares no import.

Still open, with their gap ids from the packet: `G-06` remainder ("get a
promise to wait for all", `op.waiting-for-all-promise` 354881..356058, with
its `[=Queue a microtask=]` step, and the returned promise of "wait for all"),
`G-09` remainder (`create a DOMException`, `create a DOMException derived
interface`, `throw an exception`, the six `rule.domexception-derived-*` rows,
`QuotaExceededError` and its serialization steps, and the 25 legacy
`idl.domexception-*-err` code constants), and the binding layer, which stays
`hostOnly` at the boundary.

Every Web IDL census row this library cites is cited as an anchor for a
declaration, never as a numerator: `generated/webidl-census.tsv` stays
all-`absent`, and no coverage state moves here.
-/
