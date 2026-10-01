import Whatwg.Ecma262.Promise
import Whatwg.Ecma262.Jobs
import Whatwg.Ecma262.Agent
import Whatwg.Ecma262.AgentLaws
import Whatwg.Ecma262.AgentInvariant

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
(`test/contracts/promise-first-packet.contract.md` and its Q3b addendum
`test/contracts/promise-first-packet-q3b.contract.md`) and built by the Q3 and
Q3b builder seats:

- `Whatwg/Ecma262/Jobs.lean` — the payload-polymorphic FIFO job queue, the
  reaction-job record, the activation state and run condition, the DB-05
  specification/realizer pair for `requirement.hostenqueuepromisejob.3`, and
  the `Active`-threaded `startJob` and `completeJob` with the run-to-completion
  specification `RunToCompletion` for `requirement.jobs.3`. It imports
  nothing (ruling R-V3(a)).
- `Whatwg/Ecma262/Promise.lean` — the promise state, settled-outcome and
  callback-return carriers, promise identity, the general promise table with
  its allocation, lookup, settle and mark-handled operations, the reaction
  records with their capability field and the two reaction lists,
  `TriggerPromiseReactions`, the capability record and the resolving
  functions, `PerformPromiseThen`, the reaction job's handler step and the
  settlement trace. It imports `Whatwg.Ecma262.Jobs` and nothing else.
- `Whatwg/Ecma262/Agent.lean` — promise slice Q5 (`PROMISE-PG-AGENT`,
  `test/contracts/promise-agent-q5.contract.md`, ruling R-W3): the agent
  record that contains the table, the reaction lists and the job queue above,
  its nine first-order operations with one total step, `Minted` and `WF`, and
  the views onto the store-level operations. It imports
  `Whatwg.Ecma262.Promise` and nothing else.
- `Whatwg/Ecma262/AgentLaws.lean` — promise slice Q5, builder slice B2: every
  lemma about `WF`, the world order `Le`, the operations' laws in the
  handler-adequacy shape (`pre`, `post`, `Implements` and one `*_implements`
  per operation), runs of the step with the lifted FIFO law, and the other
  lifted laws. It imports `Whatwg.Ecma262.Agent` and nothing else.
- `Whatwg/Ecma262/AgentInvariant.lean` — promise slice Q5, addendum Q5b,
  builder slice B5 (rulings R-W16 and R-W20): the stronger invariant
  `Coherent`, which extends `WF`, with its inductiveness and reachability
  laws; the stronger order `Extends`, which extends `Le`; the two-state post
  `postFrom` and the second adequacy judgment `ImplementsFrom` over the
  unchanged `pre`, one theorem per operation; and the reaction job's two
  completions with the named departure `finishJob_abrupt_dropped`. It imports
  `Whatwg.Ecma262.AgentLaws` and nothing else.

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
