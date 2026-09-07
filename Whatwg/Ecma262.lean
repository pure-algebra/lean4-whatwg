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

Landed surface, frozen by `PROMISE-PG-FIRST`
(`test/contracts/promise-first-packet.contract.md`) and built by the Q3
builder seat:

- `Whatwg/Ecma262/Jobs.lean` — the payload-polymorphic FIFO job queue, the
  reaction-job record, the activation state and run condition, and the DB-05
  specification/realizer pair for `requirement.hostenqueuepromisejob.3`
  (3 types, 12 functions, 20 theorems). It imports only `Whatwg.Infra`.
- `Whatwg/Ecma262/Promise.lean` — the promise state, settled-outcome and
  callback-return carriers, promise identity, the general promise table with
  its allocation, lookup, settle and mark-handled operations, the reaction
  records and the two reaction lists, `TriggerPromiseReactions`, the
  capability record and the resolving functions, and `PerformPromiseThen`
  (12 types, 22 functions, 44 theorems). It imports `Whatwg.Ecma262.Jobs` and
  `Whatwg.Infra`.

Still open, with their gap ids from the packet: `G-02` remainder (the
handled-bit consumer and `HostPromiseRejectionTracker`), `G-04` (`IsPromise`
and the value universe), `G-05` (thenable adoption and
`NewPromiseResolveThenableJob`), `G-07` remainder (the realm parameter, the
Job Abstract Closure carrier, `HostMakeJobCallback`, `HostCallJobCallback`
and the JobCallback `[[HostDefined]]` field), `G-08` remainder (a global
configuration that observes the run condition), `G-10` (the Completion
carrier beyond `Except`), `G-11` remainder (`Promise.prototype.then` /
`catch` / `finally`, the four combinators, the `Promise` constructor and the
static resolve/reject helpers).

Every ES2026 census row this library cites is cited as an anchor for a
declaration, never as a numerator: `generated/ecma262-census.tsv` stays
all-`absent`, and no coverage state moves here.
-/
