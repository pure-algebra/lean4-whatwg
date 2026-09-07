import Whatwg.Ecma262.Jobs
import Whatwg.Infra

/-!
# ECMAScript promise objects

Owner: the Promise Objects clause of the pinned ES2026 source, at the first
packet surface `PROMISE-PG-FIRST` freezes
(`test/contracts/promise-first-packet.contract.md`).

Landed here: the promise state carrier (`E-01`, move), the settled-outcome and
callback-return carriers (`E-02`, `E-03`, move), promise identity (`E-14`,
`E-23`, generalize), the general promise table with its allocation, lookup,
settle and mark-handled operations (`E-13`..`E-15`, `E-18`..`E-23`,
generalize), the reaction records and the two reaction lists (`E-29`..`E-33`,
generalize; gap `G-01`), `TriggerPromiseReactions` with its order and
once-only laws (`G-01`), the capability record and the resolving functions
(`G-03`), and `PerformPromiseThen` with a result capability (`G-11`).

Still open, with their gap ids: the handled-bit consumer and
`HostPromiseRejectionTracker` (`G-02` remainder); `IsPromise` and the value
universe (`G-04`); thenable adoption and `NewPromiseResolveThenableJob`
(`G-05`); the Completion carrier beyond `Except` (`G-10`);
`Promise.prototype.then`/`catch`/`finally`, the four combinators, the
`Promise` constructor and the static resolve/reject helpers (`G-11`
remainder).

Layering (DB-11): this module imports `Whatwg.Ecma262.Jobs` and
`Whatwg.Infra`, and nothing else. The reason parameter stays free
(decision 2); `Whatwg.WebIdl.Exceptions` is the instantiation Streams uses.
-/

namespace Whatwg.Ecma262.Promise

/-! ## Part A — the moved carriers -/

/--
`slot.PromiseState` (2744957..2745252) fused with `slot.PromiseResult`
(2745263..2745619): the first-order promise-outcome view, with the three tags
the clause names. `E-01` (move) relocates
`Whatwg.Streams.Readable.PromiseState` here; two type parameters per R-P13,
because `E-22` (`Readable.State.readPromises`) already needs a non-unit value.
-/
inductive State (value reason : Type) where
  | pending
  | fulfilled (value : value)
  | rejected (reason : reason)
  deriving DecidableEq, Repr

/--
`op.fulfillpromise` (2695419..2696230) and `op.rejectpromise`
(2699323..2700252): the settled outcome a foreign callback's promise delivers,
with the value fixed to unit. `E-02` (move). One parameter, not two
(decision 12): `Readable.PullAnswer.fulfilled` takes no argument, and the
value-carrying settled outcome already exists as `Except reason value`.
-/
inductive Outcome (reason : Type) where
  | fulfilled
  | rejected (reason : reason)
  deriving DecidableEq, Repr

/--
The `[[PromiseState]]` of a returned promise observed at callback-return time,
before any reaction runs. `E-03` (move). Decision 6 keeps `State`, `Outcome`
and `Returned` distinct; their isomorphisms are bridging lemmas, not
identifications.
-/
inductive Returned (reason : Type) where
  | pending
  | settled (answer : Outcome reason)
  deriving DecidableEq, Repr

/--
The owner-qualified promise identity. P8a rename class "rename only":
`PromiseRef` becomes `Ref` and `PromiseRef.local` becomes `Ref.cell`, because
`local` is a Lean 4 keyword and cannot be a field name (§11 of the contract).
`E-14`, `E-23` (generalize) and decision 3 keep identities `Nat` with a
monotone cursor; Streams keeps bare `Nat` under a single-owner view until P8.
-/
structure Ref where
  owner : Nat
  cell : Nat
  deriving DecidableEq

end Whatwg.Ecma262.Promise
