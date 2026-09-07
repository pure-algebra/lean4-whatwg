import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q4 interface battery: the DB-11 restatement of the held P8a
configuration-ordering draft against the landed promise libraries.

Contract: `test/contracts/configuration-ordering.contract.md`.
Graph: `CONFIGURATION-PG-ORDERING`, `docs/CONFIGURATION-DAG.md`.
Declared red: `test/fixtures/trust-gate/known-red.txt`.

This module restates the 104 interface ascriptions the held draft carries on
disk at `C:\Users\kokok\Dev\lean4-WHATWG-streams-configuration-breaker`
(`WhatwgTest/Streams/Semantics/OrderingContract.lean`, read-only), joined to
the P8a reuse table of `docs/PROMISE-EXTRACTION-INVENTORY.md` and re-homed
onto what slice Q3 actually landed. It adds three Q4-owned bridging views,
for 107 ascriptions in total. Section §2 of the contract records the three
classes and every place the reuse table's prediction and the landed surface
disagree.

Three classes, marked per block:

- **[R]** re-homed: the ascription *is* a landed `Whatwg.Ecma262` name. These
  fifteen elaborate today and must keep elaborating; a builder that makes one
  fail has changed a landed library and is refused.
- **[B]** bridged: the declaration stays in `Whatwg.Streams.Semantics.Ordering`
  and is joined to a landed name by a Q4-owned receipt in `OrderingLaws.lean`.
  R-P13 rules exactly this shape ("move for types and generalize for every
  function").
- **[A]** adapter: Streams-specific, carried over from the draft unchanged in
  content as well as in file.

No ascription in class [A] is reinterpreted. Where a field's *type* is one of
the class [R] names, the ascription names the landed type; that substitution
is the re-homing and is listed exhaustively in §2.4 of the contract.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## [R] The owner-qualified promise identity

Draft ascriptions 1–4 (`PromiseRef`, `.mk`, `.owner`, `.local`). R-P18 renames
`PromiseRef.local` to `Ref.cell`, because `local` is a Lean 4 keyword and
cannot be a field name; the draft was never elaborated and never found this.
Anchor: `record.promise-capability-record`'s identity discipline as R-P13 fixed
it (identities stay `Nat`, owner-qualified above them). -/

#check (@Whatwg.Ecma262.Promise.Ref : Type)

#check (@Whatwg.Ecma262.Promise.Ref.mk : Nat → Nat → Whatwg.Ecma262.Promise.Ref)

#check (@Whatwg.Ecma262.Promise.Ref.owner : Whatwg.Ecma262.Promise.Ref → Nat)

#check (@Whatwg.Ecma262.Promise.Ref.cell : Whatwg.Ecma262.Promise.Ref → Nat)

/-! ## [A] The startup envelope

Draft ascriptions 5–7. Streams-specific: it stands for the source's omitted
`[[started]]` guard on `op.writable-stream-default-controller-advance-queue-if-needed`
(271219..272322) and has no ECMA-262 or Web IDL counterpart. -/

#check (@Semantics.Ordering.Startup : Type)
#check (@Semantics.Ordering.Startup.pending : Semantics.Ordering.Startup)
#check (@Semantics.Ordering.Startup.started : Semantics.Ordering.Startup)

/-! ## [R] The reaction phase

Draft ascriptions 8–12 (`ObserverPhase` and its four constructors), landed as
`Whatwg.Ecma262.Promise.ReactionPhase` with the four constructors unchanged.
The `job : Nat` field of `queued` and `running` is read as the *job serial* in
this packet; §2.5 of the contract records that the landed `react` and
`performPromiseThen` instantiate the same field with a *registration* id, and
marks the difference Q3b-sensitive. -/

#check (@Whatwg.Ecma262.Promise.ReactionPhase : Type)
#check (@Whatwg.Ecma262.Promise.ReactionPhase.waiting : Whatwg.Ecma262.Promise.ReactionPhase)
#check (@Whatwg.Ecma262.Promise.ReactionPhase.queued :
  Nat → Whatwg.Ecma262.Promise.ReactionPhase)
#check (@Whatwg.Ecma262.Promise.ReactionPhase.running :
  Nat → Whatwg.Ecma262.Promise.ReactionPhase)
#check (@Whatwg.Ecma262.Promise.ReactionPhase.done : Whatwg.Ecma262.Promise.ReactionPhase)

/-! ## [R] The registration record

Draft ascriptions 13–18 (`Registration`, `.mk`, `.id`, `.promise`, `.callback`,
`.phase`), landed as `Whatwg.Ecma262.Promise.Reaction body` at `body := Nat`.
Three of the six are renames with a stated change, recorded in §2.4:

- `.mk` grows one argument, the `[[Type]]` tag `ReactionType`
  (`field.promisereaction-records.Type`, 2691815..2692138), which is `G-01`
  new content adopted by R-P18 decision 8;
- `.promise` is the bare cell `Nat`, not the owner-qualified `Ref`: P8a has one
  root, `Config.owner` carries the owner, and `CellsWellFormed` already
  requires every registration owner to equal `c.owner`;
- `.callback` becomes `.handler : Option body`, because
  `field.promisereaction-records.Handler` (2692151..2692611) admits an empty
  handler and Web IDL "upon fulfillment" (352410..352816) registers exactly
  one side.

All six are Q3b-sensitive: fidelity finding F4 adds a `[[Capability]]` field. -/

#check (@Whatwg.Ecma262.Promise.Reaction : Type → Type)

#check (@Whatwg.Ecma262.Promise.Reaction.mk :
  ∀ {body : Type}, Nat → Nat → Whatwg.Ecma262.Promise.ReactionType → Option body →
    Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.Reaction body)

#check (@Whatwg.Ecma262.Promise.Reaction.id :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Nat)

#check (@Whatwg.Ecma262.Promise.Reaction.promise :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Nat)

#check (@Whatwg.Ecma262.Promise.Reaction.handler :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Option body)

#check (@Whatwg.Ecma262.Promise.Reaction.phase :
  ∀ {body : Type}, Whatwg.Ecma262.Promise.Reaction body → Whatwg.Ecma262.Promise.ReactionPhase)

/-! ## [A] The job payload and its token

Draft ascriptions 19–26. The reuse table calls the four `Job` ascriptions
"direct — only the namespace changes". They are not: `Whatwg.Ecma262.Jobs`
landed no general `Job` record. Its only job carrier is
`Jobs.ReactionJob (reaction : Nat) (argument : arg)`, anchored to
`op.newpromisereactionjob` (2702885..2705591), and a startup token or a sink
token is not a reaction job. `Jobs.Queue` is payload-polymorphic by decision 4
precisely so that its client supplies the payload, so `JobKind` and `Job` are
that payload and stay here. §2.3 of the contract records the finding. -/

#check (@Semantics.Ordering.JobKind : Type)
#check (@Semantics.Ordering.JobKind.startup : Semantics.Ordering.JobKind)
#check (@Semantics.Ordering.JobKind.sink : Writable.SinkKind → Nat → Semantics.Ordering.JobKind)
#check (@Semantics.Ordering.JobKind.observer : Nat → Semantics.Ordering.JobKind)
#check (@Semantics.Ordering.Job : Type)
#check (@Semantics.Ordering.Job.mk : Nat → Semantics.Ordering.JobKind → Semantics.Ordering.Job)
#check (@Semantics.Ordering.Job.serial : Semantics.Ordering.Job → Nat)
#check (@Semantics.Ordering.Job.kind : Semantics.Ordering.Job → Semantics.Ordering.JobKind)

/-! ## [B] The activation state

Draft ascriptions 27–31. The reuse table calls these rename-only onto
`Whatwg.Ecma262.Jobs.Active`, and `Jobs.lean`'s own docstring adopts that
reading — "with `observer` renamed `job` and both job-carrying constructors
taking a serial rather than the whole record". The serial is the difference,
and it is not a rename: five of the 118 adapter ascriptions
(`authorFrontier_eq`, `tick_observer_empty`, `tick_intrinsic_empty`,
`decide_intrinsic_gap`, `takeSinkHead_matching`) consume the whole `Job`
record, and `tick_intrinsic_empty` emits `.jobFinished job` from it, which a
bare serial cannot supply. So `Active` stays here and `activeErase` below is
the Q4-owned erasure onto the landed state, with
`Jobs.RunCondition` (625769..626250, 626257..626350) reached through it. -/

#check (@Semantics.Ordering.Active : Type)
#check (@Semantics.Ordering.Active.script : Semantics.Ordering.Active)
#check (@Semantics.Ordering.Active.intrinsic : Semantics.Ordering.Job → Semantics.Ordering.Active)
#check (@Semantics.Ordering.Active.observer : Semantics.Ordering.Job → Semantics.Ordering.Active)
#check (@Semantics.Ordering.Active.checkpoint : Semantics.Ordering.Active)

/-! ## [A] The configuration event alphabet

Draft ascriptions 32–41, carried over unchanged. The only substitution is the
class [R] one: `Event.registered` and `Event.observerCalled` carry
`Whatwg.Ecma262.Promise.Ref` where the draft wrote `PromiseRef`. -/

#check (@Semantics.Ordering.Event : Type → Type → Type)
#check (@Semantics.Ordering.Event.writable :
  ∀ {α ε : Type}, Writable.Event α ε → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.registered :
  ∀ {α ε : Type}, Nat → Whatwg.Ecma262.Promise.Ref → Nat → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.observerCalled :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Ecma262.Promise.Ref →
    Except (Boundary.Exception ε) Unit → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.observerReturned :
  ∀ {α ε : Type}, Nat → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.jobQueued :
  ∀ {α ε : Type}, Semantics.Ordering.Job → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.jobStarted :
  ∀ {α ε : Type}, Semantics.Ordering.Job → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.jobFinished :
  ∀ {α ε : Type}, Semantics.Ordering.Job → Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.scriptEntered : ∀ {α ε : Type}, Semantics.Ordering.Event α ε)
#check (@Semantics.Ordering.Event.scriptReturned : ∀ {α ε : Type}, Semantics.Ordering.Event α ε)

/-! ## [A] The configuration

Draft ascriptions 42–52, carried over unchanged. Two field types take their
class [R] substitution: `registrations` is a list of
`Whatwg.Ecma262.Promise.Reaction Nat`, and nothing else moves. `jobs` stays a
`List Job`, exactly as Q3 left `Writable.State.jobs` a `List` with `jobQueue`
as the view; the FIFO obligation is stated over `Jobs.Queue` through
`Semantics.Ordering.jobQueue` below. -/

#check (@Semantics.Ordering.Config : Type → Type → Type)
#check (@Semantics.Ordering.Config.mk :
  ∀ {α ε : Type}, Nat → Writable.State α ε → Semantics.Ordering.Startup →
    Semantics.Ordering.Active → List (Whatwg.Ecma262.Promise.Reaction Nat) → Nat →
    List Semantics.Ordering.Job → Nat → List (Semantics.Ordering.Event α ε) →
    Semantics.Ordering.Config α ε)
#check (@Semantics.Ordering.Config.owner : ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat)
#check (@Semantics.Ordering.Config.writable :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Writable.State α ε)
#check (@Semantics.Ordering.Config.startup :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Semantics.Ordering.Startup)
#check (@Semantics.Ordering.Config.active :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Semantics.Ordering.Active)
#check (@Semantics.Ordering.Config.registrations :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → List (Whatwg.Ecma262.Promise.Reaction Nat))
#check (@Semantics.Ordering.Config.nextObserver :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat)
#check (@Semantics.Ordering.Config.jobs :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → List Semantics.Ordering.Job)
#check (@Semantics.Ordering.Config.nextJob : ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat)
#check (@Semantics.Ordering.Config.trace :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → List (Semantics.Ordering.Event α ε))

/-! ## [A] The decision alphabet

Draft ascriptions 53–58, carried over unchanged; `Decision.observe` takes the
class [R] `Ref`. This is the one place the owner qualification is observable:
`lookup` rejects a cross-owner address, and `Reaction.promise`'s bare `Nat` is
the local half of it. -/

#check (@Semantics.Ordering.Decision : Type → Type → Type)
#check (@Semantics.Ordering.Decision.writable :
  ∀ {α ε : Type}, Writable.Decision α ε → Semantics.Ordering.Decision α ε)
#check (@Semantics.Ordering.Decision.observe :
  ∀ {α ε : Type}, Whatwg.Ecma262.Promise.Ref → Nat → Semantics.Ordering.Decision α ε)
#check (@Semantics.Ordering.Decision.observerReturn :
  ∀ {α ε : Type}, Semantics.Ordering.Decision α ε)
#check (@Semantics.Ordering.Decision.scriptReturn :
  ∀ {α ε : Type}, Semantics.Ordering.Decision α ε)
#check (@Semantics.Ordering.Decision.scriptBegin :
  ∀ {α ε : Type}, Semantics.Ordering.Decision α ε)

/-! ## [A] Initialization

Draft ascription 59, unchanged. -/

#check (@Semantics.Ordering.initial :
  ∀ {α ε : Type}, Nat → Writable.Size → Writable.Algorithms → Nat → Nat →
    Semantics.Ordering.Config α ε)

/-! ## [B] The four operations the reuse table calls rename-only

Draft ascriptions 60–61 and 63–65, plus 62. Each stays here and is joined to a
landed operation by a Q4-owned bridge in `OrderingLaws.lean`. R-P13 rules the
shape: move for types, generalize for functions. The exact landed targets:

| here | landed target |
| --- | --- |
| `lookup` | `Whatwg.Ecma262.Promise.Table.get` over `Writable.promiseTable`, under the owner guard |
| `lookupRegistration` | `Whatwg.Ecma262.Promise.Reactions.get` at `ReactionType.fulfill` |
| `enqueueJob` | `Whatwg.Ecma262.Jobs.Queue.enqueue` (633447..635836), plus serial allocation and the `jobQueued` event |
| `setRegistrationPhase` | `Whatwg.Ecma262.Promise.Reactions.setPhase` at `ReactionType.fulfill` |
| `register` | `Whatwg.WebIdl.Promise.react` (350075..352408), reaction half only |
| `notifySettled` | `Whatwg.Ecma262.Promise.triggerReactions` (2700260..2701212), reaction half only |

`register` and `notifySettled` are bridged on their reaction half alone, for
the same reason Q3 bridged `Writable.attachSink` on its job queue alone: the
landed operations write a `Jobs.Queue (Jobs.ReactionJob …)`, while the P8a
configuration has one heterogeneous token queue carrying startup, sink and
observer tokens. §2.6 of the contract records that mismatch. -/

#check (@Semantics.Ordering.lookup :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Whatwg.Ecma262.Promise.Ref →
    Option (Writable.UnitPromise ε))
#check (@Semantics.Ordering.lookupRegistration :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat →
    Option (Whatwg.Ecma262.Promise.Reaction Nat))
#check (@Semantics.Ordering.enqueueJob :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Semantics.Ordering.JobKind →
    Semantics.Ordering.Config α ε × Semantics.Ordering.Job)
#check (@Semantics.Ordering.setRegistrationPhase :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat → Whatwg.Ecma262.Promise.ReactionPhase →
    Semantics.Ordering.Config α ε)
#check (@Semantics.Ordering.register :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Whatwg.Ecma262.Promise.Ref → Nat →
    Option (Semantics.Ordering.Config α ε))
#check (@Semantics.Ordering.notifySettled :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Nat → Semantics.Ordering.Config α ε)

/-! ## [A] The Streams-specific stages

Draft ascriptions 66–71, carried over unchanged in content and in file. -/

#check (@Semantics.Ordering.liftWritable :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Writable.State α ε →
    Semantics.Ordering.Config α ε)
#check (@Semantics.Ordering.preStartAllowed :
  ∀ {α ε : Type}, Writable.Decision α ε → Bool)
#check (@Semantics.Ordering.authorFrontier :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Bool)
#check (@Semantics.Ordering.takeSinkHead :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Semantics.Ordering.Job →
    Option (Semantics.Ordering.Config α ε))
#check (@Semantics.Ordering.tick :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Option (Semantics.Ordering.Config α ε))
#check (@Semantics.Ordering.decide :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Semantics.Ordering.Decision α ε →
    Option (Semantics.Ordering.Config α ε))

/-! ## [A] The relational face

Draft ascriptions 72–78, carried over unchanged. -/

#check (@Semantics.Ordering.Step :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Option (Semantics.Ordering.Decision α ε) →
    Semantics.Ordering.Config α ε → Prop)
#check (@Semantics.Ordering.Reaches :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → List (Option (Semantics.Ordering.Decision α ε)) →
    Semantics.Ordering.Config α ε → Prop)
#check (@Semantics.Ordering.Reaches.nil :
  ∀ {α ε : Type} (s : Semantics.Ordering.Config α ε), Semantics.Ordering.Reaches s [] s)
#check (@Semantics.Ordering.Reaches.cons :
  ∀ {α ε : Type} {s mid t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Step s d mid → Semantics.Ordering.Reaches mid ds t →
      Semantics.Ordering.Reaches s (d :: ds) t)
#check (@Semantics.Ordering.EpisodePrefix :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → List (Option (Semantics.Ordering.Decision α ε)) →
    Semantics.Ordering.Config α ε → Prop)
#check (@Semantics.Ordering.EpisodePrefix.nil :
  ∀ {α ε : Type} (s : Semantics.Ordering.Config α ε), Semantics.Ordering.EpisodePrefix s [] s)
#check (@Semantics.Ordering.EpisodePrefix.cons :
  ∀ {α ε : Type} {s mid t : Semantics.Ordering.Config α ε}
    {d : Option (Semantics.Ordering.Decision α ε)}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    s.active ≠ Semantics.Ordering.Active.checkpoint →
      Semantics.Ordering.Step s d mid → Semantics.Ordering.EpisodePrefix mid ds t →
        Semantics.Ordering.EpisodePrefix s (d :: ds) t)

/-! ## [A] The trace filter

Draft ascription 79. The reuse table calls `queuedJobs` "direct"; it is a
filter over the configuration's own event list and `Whatwg.Ecma262.Jobs` has
no counterpart at all. It stays here. -/

#check (@Semantics.Ordering.queuedJobs :
  ∀ {α ε : Type}, List (Semantics.Ordering.Event α ε) → List Semantics.Ordering.Job)

/-! ## [A] The live M2 view

Draft ascriptions 80–86, carried over unchanged. DB-04 M2 is a repository
ruling about claim scope and belongs in no promise library (inventory group
G); restating one of these rows in `Whatwg.Ecma262` or `Whatwg.WebIdl` would
be a defect under R-P12. -/

#check (@Semantics.Ordering.m2Allowed : ∀ {ε : Type}, Writable.VisibleEvent ε → Bool)
#check (@Semantics.Ordering.M2LivePrefix : Type → Type)
#check (@Semantics.Ordering.M2LivePrefix.mk :
  ∀ {ε : Type}, Nat → (events : List (Writable.VisibleEvent ε)) →
    (∀ event ∈ events, Semantics.Ordering.m2Allowed event = true) →
      Semantics.Ordering.M2LivePrefix ε)
#check (@Semantics.Ordering.M2LivePrefix.owner :
  ∀ {ε : Type}, Semantics.Ordering.M2LivePrefix ε → Nat)
#check (@Semantics.Ordering.M2LivePrefix.events :
  ∀ {ε : Type}, Semantics.Ordering.M2LivePrefix ε → List (Writable.VisibleEvent ε))
#check (@Semantics.Ordering.M2LivePrefix.allowed :
  ∀ {ε : Type} (p : Semantics.Ordering.M2LivePrefix ε),
    ∀ event ∈ p.events, Semantics.Ordering.m2Allowed event = true)
#check (@Semantics.Ordering.observeLive :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Option (Semantics.Ordering.M2LivePrefix ε))

/-! ## [A] The successful-control grammar

Draft ascriptions 87–102, carried over unchanged. These are predicates on the
actual P5 `Writable.Control` list; nothing in them is promise-layer content. -/

#check (@Semantics.Ordering.stagedRequests : ∀ {α ε : Type}, List (Writable.Control α ε) → List Nat)
#check (@Semantics.Ordering.sinkMarkerCount : ∀ {α ε : Type}, List (Writable.Control α ε) → Nat)
#check (@Semantics.Ordering.Suspensions : ∀ {α ε : Type}, List (Writable.Control α ε) → Prop)
#check (@Semantics.Ordering.Suspensions.nil :
  ∀ {α ε : Type}, Semantics.Ordering.Suspensions (α := α) (ε := ε) [])
#check (@Semantics.Ordering.Suspensions.size :
  ∀ {α ε : Type} (call : Nat) (chunk : α) {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest →
      Semantics.Ordering.Suspensions (.awaitSize call chunk :: rest))
#check (@Semantics.Ordering.Suspensions.sinkIntrinsic :
  ∀ {α ε : Type} (request : Nat) (chunk : α),
    Semantics.Ordering.Suspensions (ε := ε) [.awaitSink (.write request chunk)])
#check (@Semantics.Ordering.Suspensions.sinkCall :
  ∀ {α ε : Type} (request : Nat) (chunk : α) (call id : Nat)
    {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest → Semantics.Ordering.sinkMarkerCount rest = 0 →
      Semantics.Ordering.Suspensions
        (.awaitSink (.write request chunk) :: .returnPromise call id :: rest))

#check (@Semantics.Ordering.SuccessfulControl :
  ∀ {α ε : Type}, List (Writable.Control α ε) → Prop)
#check (@Semantics.Ordering.SuccessfulControl.suspended :
  ∀ {α ε : Type} {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest → Semantics.Ordering.SuccessfulControl rest)
#check (@Semantics.Ordering.SuccessfulControl.getSize :
  ∀ {α ε : Type} (call : Nat) (chunk : α) {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest →
      Semantics.Ordering.SuccessfulControl (.getSize call chunk :: rest))
#check (@Semantics.Ordering.SuccessfulControl.afterSize :
  ∀ {α ε : Type} (call : Nat) (chunk : α) (size : Writable.Size)
    {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest →
      Semantics.Ordering.SuccessfulControl (.afterSize call chunk size :: rest))
#check (@Semantics.Ordering.SuccessfulControl.enqueue :
  ∀ {α ε : Type} (chunk : α) (size : Writable.Size) (call id : Nat)
    {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest → Semantics.Ordering.SuccessfulControl
      (.enqueueWrite chunk size :: .returnPromise call id :: rest))
#check (@Semantics.Ordering.SuccessfulControl.advanceCall :
  ∀ {α ε : Type} (call id : Nat) {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest →
      Semantics.Ordering.SuccessfulControl (.advance :: .returnPromise call id :: rest))
#check (@Semantics.Ordering.SuccessfulControl.returnPromise :
  ∀ {α ε : Type} (call id : Nat) {rest : List (Writable.Control α ε)},
    Semantics.Ordering.Suspensions rest →
      Semantics.Ordering.SuccessfulControl (.returnPromise call id :: rest))
#check (@Semantics.Ordering.SuccessfulControl.advanceIntrinsic :
  ∀ {α ε : Type}, Semantics.Ordering.SuccessfulControl (α := α) (ε := ε) [.advance])
#check (@Semantics.Ordering.SuccessfulControl.react :
  ∀ {α ε : Type} (job : Writable.SinkJob α ε),
    Semantics.Ordering.SuccessfulControl [.react job])

/-! ## [A] The replay helpers

Draft ascriptions 103–104, carried over unchanged. -/

#check (@Semantics.Ordering.externalWord :
  ∀ {α ε : Type}, List (Option (Semantics.Ordering.Decision α ε)) →
    List (Semantics.Ordering.Decision α ε))
#check (@Semantics.Ordering.Normalized : ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Prop)

/-! ## Q4-owned bridging views

Three declarations the draft does not have. They are the whole cost of the
re-homing on the interface side: each names a landed carrier and lets the
class [B] receipts in `OrderingLaws.lean` be stated over the landed
operations. They follow Q3's landed pattern exactly — `Writable.jobQueue`,
`Writable.promiseTable`, `Transform.reactions`. -/

#check (@Semantics.Ordering.jobQueue :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε →
    Whatwg.Ecma262.Jobs.Queue Semantics.Ordering.Job)

#check (@Semantics.Ordering.reactions :
  ∀ {α ε : Type}, Semantics.Ordering.Config α ε → Whatwg.Ecma262.Promise.Reactions Nat)

#check (@Semantics.Ordering.activeErase :
  Semantics.Ordering.Active → Whatwg.Ecma262.Jobs.Active)

/-!
Intentionally not ascribed here, and unchanged from the draft: `WellFormed`
and the successful-progress statements, the bounded-driver result, and every
theorem receipt other than the laws frozen in `OrderingLaws.lean`. The
source/certificate judgments the CFG-WPT seam names are frozen separately in
`OrderingSource.lean`.
-/
