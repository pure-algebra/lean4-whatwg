import Whatwg.Ecma262

/-!
Breaker-owned Q3 exact-signature battery for `Whatwg.Ecma262.Jobs`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, opened in `docs/PROMISE-DAG.md`.

Every ascription cites an extraction row (`E-…`) of
`docs/PROMISE-EXTRACTION-INVENTORY.md` with its reuse mode, or a gap id
(`G-…`) with the ES2026 census row it realizes. The builder must not change a
statement here. The root import is intentional: `Whatwg.Ecma262` is an
importable declaration-free bootstrap today, so the intended red failures are
unknown declarations and their direct consequences only.

Import direction inside this library: `Whatwg/Ecma262/Jobs.lean` imports only
`Whatwg.Infra` and is imported by `Whatwg/Ecma262/Promise.lean`. Nothing here
mentions a promise state, so the queue stays payload-polymorphic (decision 4).
-/

set_option autoImplicit false

/-! ## The payload-polymorphic job queue

`E-45`, `E-48`, `E-52` (generalize): the three Streams job lists
(`Writable.State.jobs : List (SinkJob α ε)`, `Readable.State.jobs :
List (PullAnswer ε)`, `Transform.State.jobs : List (Job α ε)`) become
instances of one queue at three payloads. `G-07`: ES2026 has one
realm-indexed queue where Streams has three per-component lists; the realm
parameter stays out of this packet.
Anchor: `hook.hostenqueuepromisejob`, bytes 633447..635836 of
`vendor/ecma262-0248456c/spec.html`. -/

#check (@Whatwg.Ecma262.Jobs.Queue :
  Type → Type)

#check (@Whatwg.Ecma262.Jobs.Queue.mk :
  ∀ {payload : Type}, List payload → Whatwg.Ecma262.Jobs.Queue payload)

#check (@Whatwg.Ecma262.Jobs.Queue.pending :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload → List payload)

#check (@Whatwg.Ecma262.Jobs.Queue.empty :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload)

#check (@Whatwg.Ecma262.Jobs.Queue.enqueue :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload → payload →
    Whatwg.Ecma262.Jobs.Queue payload)

#check (@Whatwg.Ecma262.Jobs.Queue.enqueueAll :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload → List payload →
    Whatwg.Ecma262.Jobs.Queue payload)

#check (@Whatwg.Ecma262.Jobs.Queue.oldest :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload → Option payload)

#check (@Whatwg.Ecma262.Jobs.Queue.dequeue :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload →
    Option (payload × Whatwg.Ecma262.Jobs.Queue payload))

/-! `E-44` risk: `Writable.SinkJob` derives `DecidableEq` and `Transform.Job`
derives `Repr` only, so both instances are conditional on the payload. -/
#check (inferInstance :
  DecidableEq (Whatwg.Ecma262.Jobs.Queue Nat))

#check (inferInstance :
  Repr (Whatwg.Ecma262.Jobs.Queue Nat))

/-! ## The reaction-job record

`E-44` (generalize) and `G-07`: `NewPromiseReactionJob` reduced to its capture
list, kept payload-polymorphic in the argument so that
`Whatwg/Ecma262/Jobs.lean` never mentions a promise state.
Anchors: `op.newpromisereactionjob`, 2702885..2705591;
`record.jobcallback-records`, 628436..630247. -/

#check (@Whatwg.Ecma262.Jobs.ReactionJob :
  Type → Type)

#check (@Whatwg.Ecma262.Jobs.ReactionJob.mk :
  ∀ {arg : Type}, Nat → arg → Whatwg.Ecma262.Jobs.ReactionJob arg)

#check (@Whatwg.Ecma262.Jobs.ReactionJob.reaction :
  ∀ {arg : Type}, Whatwg.Ecma262.Jobs.ReactionJob arg → Nat)

#check (@Whatwg.Ecma262.Jobs.ReactionJob.argument :
  ∀ {arg : Type}, Whatwg.Ecma262.Jobs.ReactionJob arg → arg)

#check (@Whatwg.Ecma262.Jobs.newReactionJob :
  ∀ {arg : Type}, Nat → arg → Whatwg.Ecma262.Jobs.ReactionJob arg)

/-! ## The activation state and the run condition

P8a rename class "rename only": `Semantics.Ordering.Active` becomes
`Whatwg.Ecma262.Jobs.Active`; its `observer` constructor is renamed `job` and
both job-carrying constructors take the job's serial rather than the whole
record, because `Whatwg.Ecma262.Jobs` has no Streams `Job` type.
`E-47` (keep) fixes that `Writable.Control.react` is *not* re-stated here.
`G-08`: the run condition exists in Streams only as a hypothesis of a branch
equation. Anchors: `requirement.jobs.1`, 625769..626250, digest
`c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2`;
`requirement.jobs.2`, 626257..626350; `requirement.jobs.3`, 626357..626479. -/

#check (@Whatwg.Ecma262.Jobs.Active :
  Type)

#check (@Whatwg.Ecma262.Jobs.Active.script :
  Whatwg.Ecma262.Jobs.Active)

#check (@Whatwg.Ecma262.Jobs.Active.intrinsic :
  Nat → Whatwg.Ecma262.Jobs.Active)

#check (@Whatwg.Ecma262.Jobs.Active.job :
  Nat → Whatwg.Ecma262.Jobs.Active)

#check (@Whatwg.Ecma262.Jobs.Active.checkpoint :
  Whatwg.Ecma262.Jobs.Active)

#check (inferInstance :
  DecidableEq Whatwg.Ecma262.Jobs.Active)

#check (@Whatwg.Ecma262.Jobs.mayRun :
  Whatwg.Ecma262.Jobs.Active → Bool)

#check (@Whatwg.Ecma262.Jobs.RunCondition :
  Whatwg.Ecma262.Jobs.Active → Prop)

/-! ## The specification and its realizer (DB-03, DB-05, R-P5)

`FifoRequirement` is the specification over runs that
`requirement.hostenqueuepromisejob.3` states, at bytes 634739..634841, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`:
"Jobs must run in the same order as the HostEnqueuePromiseJob invocations that
scheduled them." `step` and `run` are the deterministic FIFO realizer
`E-46`, `E-49`, `E-53` extract from three places. -/

#check (@Whatwg.Ecma262.Jobs.FifoRequirement :
  ∀ {payload : Type}, List payload → List payload → Prop)

#check (@Whatwg.Ecma262.Jobs.step :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Active → Whatwg.Ecma262.Jobs.Queue payload →
    Option (payload × Whatwg.Ecma262.Jobs.Queue payload))

#check (@Whatwg.Ecma262.Jobs.run :
  ∀ {payload : Type}, Nat → Whatwg.Ecma262.Jobs.Queue payload →
    List payload × Whatwg.Ecma262.Jobs.Queue payload)

#check (@Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Queue payload → payload →
    Whatwg.Ecma262.Jobs.Queue payload)
