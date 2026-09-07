import Whatwg.Ecma262.Promise
import Whatwg.Ecma262.Jobs

/-!
# Whatwg.Ecma262

ECMA-262, the ECMAScript Language Specification: the promise objects and
the job queue that every WHATWG algorithm written over promises depends on.
ECMA-262 is not a WHATWG standard; this root sits under the package
namespace so that the root audit, census and coverage tooling apply to it
unchanged, and its authority is Ecma International TC39, never WHATWG.

Authority: `tc39/ecma262` commit `0248456c758431e4bb8e5d26333ff1865123c9cd`
(tag `es2026`), source `spec.html`, sealed under `vendor/ecma262-0248456c/`.
`SPEC-MANIFEST.md` owns the pin and dispositions; `docs/PROVENANCE.md` owns
the fetch and digest cross-check.

Layering (ruling DB-11 in `docs/DESIGN-BASIS.md`): this library sits beneath
`Whatwg.Streams` and every other Stratum S library. Those import it; it
imports only `Whatwg.Infra`. `Whatwg.WebIdl` wraps its operations in the
vocabulary WHATWG algorithms use.

This root and both imported modules are declaration-free bootstrap stubs.
No census, disposition or semantic work has started; the operator's
semantics hold applies.
-/
