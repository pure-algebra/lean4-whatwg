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

This root and both imported modules are declaration-free bootstrap stubs.
No census, disposition or semantic work has started; the operator's
semantics hold applies.
-/
