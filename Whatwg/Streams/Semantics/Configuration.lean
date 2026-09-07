import Whatwg.Streams.Writable.Laws
import Whatwg.WebIdl.Promise

/-!
# Semantics.Configuration.lean

Owner: the configuration a run steps through: the stream and controller
states, the promise records with their settlement status, and the
deterministic job queue.

Spec anchors: none; the `model` section is a reading aid only.

Opened by slice Q4 of `docs/PROMISE-PACKAGE-PLAN.md`. Packet:
`test/contracts/configuration-ordering.contract.md`; graph
`CONFIGURATION-PG-ORDERING` in `docs/CONFIGURATION-DAG.md`. The DB-11
restatement of the held P8a configuration-ordering draft: one writable root
plus a global heterogeneous token FIFO, with the promise records re-homed onto
`Whatwg.Ecma262.Promise` and the activation state joined to
`Whatwg.Ecma262.Jobs.Active` by an erasure rather than replaced by it (§2.5 of
the contract).

There is no second promise table, no second scheduler and no shadow reaction
list here: `Writable.State.promises` stays the sole outcome table, read through
`Writable.promiseTable`, and `jobQueue` and `reactions` below are views onto the
landed carriers, in the shape slice Q3 established for `Writable`, `Readable`
and `Transform`.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

/-! ## The carriers -/

/-- The omitted `[[started]]` guard of
`op.writable-stream-default-controller-advance-queue-if-needed`
(271219..272322), as a two-state envelope. Streams-specific (class [A]): it has
no ECMA-262 or Web IDL counterpart. -/
inductive Startup where
  | pending
  | started
  deriving DecidableEq, Repr

/-- The token payload of the configuration's one heterogeneous FIFO. Class [A]:
`Whatwg.Ecma262.Jobs` landed no general `Job` record — its only job carrier is
`Jobs.ReactionJob`, and a startup token or a sink token is not a reaction job
(§2.3 of the contract). `Jobs.Queue` is payload-polymorphic by decision 4
precisely so that its client supplies the payload. -/
inductive JobKind where
  | startup
  | sink (kind : Writable.SinkKind) (request : Nat)
  | observer (registration : Nat)
  deriving DecidableEq, Repr

/-- One scheduled token: a serial from `Config.nextJob` and its payload tag. -/
structure Job where
  serial : Nat
  kind : JobKind
  deriving DecidableEq, Repr

/-- The agent's activation, carrying the whole token rather than a serial.
Class [B]: `Whatwg.Ecma262.Jobs.Active` is the landed state, reached from here
by `activeErase` below. §2.5 of the contract records why the record cannot be
dropped for a serial: five class [A] ascriptions consume it, and
`tick_intrinsic_empty` emits `.jobFinished job` from it. -/
inductive Active where
  | script
  | intrinsic (job : Job)
  | observer (job : Job)
  | checkpoint
  deriving DecidableEq, Repr

/-- The configuration's event alphabet. Class [A], with the one class [R]
substitution: `registered` and `observerCalled` carry
`Whatwg.Ecma262.Promise.Ref`, the landed owner-qualified identity. -/
inductive Event (α ε : Type) where
  | writable (event : Writable.Event α ε)
  | registered (registration : Nat) (promise : Whatwg.Ecma262.Promise.Ref) (callback : Nat)
  | observerCalled (registration callback : Nat) (promise : Whatwg.Ecma262.Promise.Ref)
      (result : Except (Boundary.Exception ε) Unit)
  | observerReturned (registration : Nat)
  | jobQueued (job : Job)
  | jobStarted (job : Job)
  | jobFinished (job : Job)
  | scriptEntered
  | scriptReturned

/-- The one-root configuration. Class [A]; `registrations` takes the class [R]
substitution and is a list of `Whatwg.Ecma262.Promise.Reaction Nat`, and `jobs`
stays a `List Job` exactly as slice Q3 left `Writable.State.jobs` a `List` with
`Writable.jobQueue` as the view. -/
structure Config (α ε : Type) where
  owner : Nat
  writable : Writable.State α ε
  startup : Startup
  active : Active
  registrations : List (Whatwg.Ecma262.Promise.Reaction Nat)
  nextObserver : Nat
  jobs : List Job
  nextJob : Nat
  trace : List (Event α ε)

/-- The external decision alphabet. Class [A]; `observe` takes the class [R]
`Ref`, which is the one place the owner qualification is observable. -/
inductive Decision (α ε : Type) where
  | writable (decision : Writable.Decision α ε)
  | observe (promise : Whatwg.Ecma262.Promise.Ref) (callback : Nat)
  | observerReturn
  | scriptReturn
  | scriptBegin

/-! ## Initialization -/

/-- The frozen initial configuration: script entered, the startup token
scheduled and nothing else. Class [A]. -/
def initial {α ε : Type} (owner : Nat) (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat) : Config α ε :=
  { owner := owner, writable := Writable.initial hwm alg promiseSeed errorSeed,
    startup := .pending, active := .script, registrations := [], nextObserver := 0,
    jobs := [⟨0, .startup⟩], nextJob := 1,
    trace := [.scriptEntered, .jobQueued ⟨0, .startup⟩] }

/-! ## The Q4-owned views onto the landed carriers -/

/-- The configuration's token FIFO read as `Whatwg.Ecma262.Jobs.Queue`. This is
the queue R-P12 requires `active_episode_fifo_suffix` stated over. -/
def jobQueue {α ε : Type} (c : Config α ε) : Whatwg.Ecma262.Jobs.Queue Job :=
  Whatwg.Ecma262.Jobs.Queue.mk c.jobs

/-- Decision 8's one-list view, inverted: the draft's single registration list
is the fulfil list, and the reject list is its handler-free image. -/
def reactions {α ε : Type} (c : Config α ε) : Whatwg.Ecma262.Promise.Reactions Nat :=
  Whatwg.Ecma262.Promise.Reactions.mk c.registrations
    (c.registrations.map (fun r => { r with kind := .reject, handler := none }))
    c.nextObserver

/-- The erasure onto `Whatwg.Ecma262.Jobs.Active`: the landed constructors take
a serial where this one takes the whole token, and `observer` is landed as
`job`. §2.5 of the contract. -/
def activeErase : Active → Whatwg.Ecma262.Jobs.Active
  | .script => .script
  | .intrinsic job => .intrinsic job.serial
  | .observer job => .job job.serial
  | .checkpoint => .checkpoint

/-! ## The operations the reuse table calls rename-only -/

/-- Class [B]: the owner-guarded read of the one outcome table.
`lookup_bridge` joins it to `Whatwg.Ecma262.Promise.Table.get` over
`Writable.promiseTable`. -/
def lookup {α ε : Type} (c : Config α ε) (p : Whatwg.Ecma262.Promise.Ref) :
    Option (Writable.UnitPromise ε) :=
  if c.owner = p.owner then Writable.lookupPromise c.writable p.cell else none

/-- Class [B]: registration lookup, joined to
`Whatwg.Ecma262.Promise.Reactions.get` at `ReactionType.fulfill`. -/
def lookupRegistration {α ε : Type} (c : Config α ε) (id : Nat) :
    Option (Whatwg.Ecma262.Promise.Reaction Nat) :=
  c.registrations.find? (fun r => r.id == id)

/-- Class [B]: phase advance, joined to
`Whatwg.Ecma262.Promise.Reactions.setPhase` at `ReactionType.fulfill`. -/
def setRegistrationPhase {α ε : Type} (c : Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase) : Config α ε :=
  { c with
    registrations :=
      c.registrations.map (fun r => if r.id == id then { r with phase := phase } else r) }

/-- Class [B]: schedule one token. The landed
`Whatwg.Ecma262.Jobs.Queue.enqueue` (`hook.hostenqueuepromisejob`,
633447..635836) is the tail append alone; this operation additionally allocates
a serial from `nextJob`, advances that cursor and emits a `jobQueued` event, so
`enqueueJob_queue_bridge` carries the queue half only. -/
def enqueueJob {α ε : Type} (c : Config α ε) (kind : JobKind) : Config α ε × Job :=
  ({ c with
      jobs := c.jobs ++ [⟨c.nextJob, kind⟩], nextJob := c.nextJob + 1,
      trace := c.trace ++ [.jobQueued ⟨c.nextJob, kind⟩] }, ⟨c.nextJob, kind⟩)

/-- Class [B]: Web IDL "react" (`op.dfn-perform-steps-once-promise-is-settled`,
350075..352408) at this configuration. The registered entry carries the
`[[Type]]` tag `fulfill` and the handler `some callback`; the
`[[Capability]]` field the Q3b fidelity addendum added is `none`, because this
registration derives no promise (`G-11`'s remainder, exactly as
`Transform.subscribe` supplies `none`).

Only the reaction half is bridged, by `register_reactions_bridge`: the landed
operation writes a `Jobs.Queue (Jobs.ReactionJob …)` while this configuration
has one heterogeneous token queue (§2.6 of the contract). -/
def register {α ε : Type} (c : Config α ε) (p : Whatwg.Ecma262.Promise.Ref) (callback : Nat) :
    Option (Config α ε) :=
  match lookup c p with
  | none => none
  | some outcome =>
      let id := c.nextObserver
      let b : Config α ε :=
        { c with
          registrations := c.registrations ++ [⟨id, p.cell, .fulfill, some callback, none, .waiting⟩],
          nextObserver := id + 1, trace := c.trace ++ [.registered id p callback] }
      match outcome with
      | .pending => some b
      | .fulfilled _ | .rejected _ =>
          let queued := enqueueJob b (.observer id)
          some (setRegistrationPhase queued.1 id (.queued queued.2.serial))

/-- Class [B]: `op.triggerpromisereactions` (2700260..2701212) at this
configuration. The draft's owner conjunct is discharged by `CellsWellFormed`'s
registration-owner clause rather than restated per entry, which is what makes
this a true instance of the landed operation, whose `Reactions.waitingOn`
filter is `r.promise == promise && r.phase == waiting`. -/
def notifySettled {α ε : Type} (c : Config α ε) (id : Nat) : Config α ε :=
  match Writable.lookupPromise c.writable id with
  | none => c
  | some .pending => c
  | some (.fulfilled _) | some (.rejected _) =>
      c.registrations.foldl
        (fun (acc : Config α ε) (r : Whatwg.Ecma262.Promise.Reaction Nat) =>
          match r.phase with
          | .waiting =>
              if r.promise == id then
                let queued := enqueueJob acc (.observer r.id)
                setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
              else acc
          | _ => acc) c

/-- Class [A]: lift one canonical writable transition. Every new writable event
is logged, every new settlement notifies its registrations, and every new sink
job is scheduled as a token. This is the append-only path; the checkpoint
dequeue of decision 6 is `takeSinkHead`, which does not use it. -/
def liftWritable {α ε : Type} (c : Config α ε) (w : Writable.State α ε) : Config α ε :=
  let b : Config α ε := { c with writable := w }
  let observed := (w.trace.drop c.writable.trace.length).foldl
    (fun (acc : Config α ε) (event : Writable.Event α ε) =>
      let logged : Config α ε := { acc with trace := acc.trace ++ [.writable event] }
      match event with
      | .settled id _ => notifySettled logged id
      | _ => logged) b
  (w.jobs.drop c.writable.jobs.length).foldl
    (fun (acc : Config α ε) (job : Writable.SinkJob α ε) =>
      (enqueueJob acc (.sink job.kind job.request)).1) observed

/-- Class [A]: the scheduled tokens a trace records, in trace order. A filter
over the configuration's own event list; `Whatwg.Ecma262.Jobs` has no
counterpart and none is wanted, because a trace is Streams observation state. -/
def queuedJobs {α ε : Type} (trace : List (Event α ε)) : List Job :=
  trace.filterMap (fun event => match event with
    | .jobQueued job => some job
    | _ => none)

/-! ## Equations — mask M1 unless noted -/

/-- Class [A]. Mask M1. -/
theorem initial_eq {α ε : Type} (owner : Nat) (hwm : Writable.Size) (alg : Writable.Algorithms)
    (promiseSeed errorSeed : Nat) :
    initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed =
      { owner := owner, writable := Writable.initial hwm alg promiseSeed errorSeed,
        startup := .pending, active := .script, registrations := [], nextObserver := 0,
        jobs := [⟨0, .startup⟩], nextJob := 1,
        trace := [.scriptEntered, .jobQueued ⟨0, .startup⟩] } := rfl

/-- Class [B]. Mask M1. -/
theorem lookup_eq {α ε : Type} (c : Config α ε) (p : Whatwg.Ecma262.Promise.Ref) :
    lookup c p = (if c.owner = p.owner then Writable.lookupPromise c.writable p.cell else none) :=
  rfl

/-- Class [B]. Mask M1. -/
theorem lookupRegistration_eq {α ε : Type} (c : Config α ε) (id : Nat) :
    lookupRegistration c id = c.registrations.find? (fun r => r.id == id) := rfl

/-- Class [B]. Mask M1. -/
theorem setRegistrationPhase_eq {α ε : Type} (c : Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase) :
    setRegistrationPhase c id phase =
      { c with
        registrations :=
          c.registrations.map (fun r => if r.id == id then { r with phase := phase } else r) } :=
  rfl

/-- Class [B]. Mask M2: the statement observes the token entering the queue. -/
theorem enqueueJob_eq {α ε : Type} (c : Config α ε) (kind : JobKind) :
    enqueueJob c kind =
      ({ c with
          jobs := c.jobs ++ [⟨c.nextJob, kind⟩], nextJob := c.nextJob + 1,
          trace := c.trace ++ [.jobQueued ⟨c.nextJob, kind⟩] }, ⟨c.nextJob, kind⟩) := rfl

/--
Class [B]. Mask M1.

**Builder note B2 of the Q4 landing** (`test/contracts/configuration-ordering.contract.md`,
"Builder notes"): the frozen ascription of this equation in
`WhatwgTest/Streams/Semantics/OrderingLaws.lean` builds the registered entry as
`⟨id, p.cell, .fulfill, some callback, .waiting⟩`, five fields. Finding F4 of
the Q3b fidelity addendum gave `Whatwg.Ecma262.Promise.Reaction` a sixth,
`capability : Option Capability` (CAPFIELD, 2691475..2691802), between
`handler` and `phase`, so that literal no longer elaborates. This statement is
the frozen one with `none` inserted at that field, which is what `G-11`'s
remainder requires and what `Transform.subscribe` already supplies. The
coordinator rules whether the frozen ascription is re-frozen to match.
-/
theorem register_eq {α ε : Type} (c : Config α ε) (p : Whatwg.Ecma262.Promise.Ref)
    (callback : Nat) :
    register c p callback =
      (match lookup c p with
      | none => none
      | some outcome =>
          let id := c.nextObserver
          let b : Config α ε :=
            { c with
              registrations :=
                c.registrations ++ [⟨id, p.cell, .fulfill, some callback, none, .waiting⟩],
              nextObserver := id + 1, trace := c.trace ++ [.registered id p callback] }
          match outcome with
          | .pending => some b
          | .fulfilled _ | .rejected _ =>
              let queued := enqueueJob b (.observer id)
              some (setRegistrationPhase queued.1 id (.queued queued.2.serial))) := rfl

/-- Class [B]. Mask M2: the statement observes the order in which the
registrations are scheduled. -/
theorem notifySettled_eq {α ε : Type} (c : Config α ε) (id : Nat) :
    notifySettled c id =
      (match Writable.lookupPromise c.writable id with
      | none | some .pending => c
      | some (.fulfilled _) | some (.rejected _) =>
          c.registrations.foldl
            (fun (acc : Config α ε) (r : Whatwg.Ecma262.Promise.Reaction Nat) =>
              match r.phase with
              | .waiting =>
                  if r.promise == id then
                    let queued := enqueueJob acc (.observer r.id)
                    setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
                  else acc
              | _ => acc) c) := rfl

/-- Class [A]. Mask M2. -/
theorem liftWritable_eq {α ε : Type} (c : Config α ε) (w : Writable.State α ε) :
    liftWritable c w =
      (let b : Config α ε := { c with writable := w }
       let observed := (w.trace.drop c.writable.trace.length).foldl
         (fun (acc : Config α ε) (event : Writable.Event α ε) =>
           let logged : Config α ε := { acc with trace := acc.trace ++ [.writable event] }
           match event with
           | .settled id _ => notifySettled logged id
           | _ => logged) b
       (w.jobs.drop c.writable.jobs.length).foldl
         (fun (acc : Config α ε) (job : Writable.SinkJob α ε) =>
           (enqueueJob acc (.sink job.kind job.request)).1) observed) := rfl

/-- Class [A]. Mask M2. -/
theorem queuedJobs_eq {α ε : Type} (trace : List (Event α ε)) :
    queuedJobs trace =
      trace.filterMap (fun event => match event with
        | .jobQueued job => some job
        | _ => none) := rfl

/-! ## The Q4-owned bridging receipts on the configuration's own operations -/

/-- The configuration's token FIFO read as the landed queue. Mask M1. -/
theorem jobQueue_eq {α ε : Type} (c : Config α ε) :
    jobQueue c = Whatwg.Ecma262.Jobs.Queue.mk c.jobs := rfl

/-- Decision 8's one-list view, inverted. Mask M1. -/
theorem reactions_eq {α ε : Type} (c : Config α ε) :
    reactions c =
      Whatwg.Ecma262.Promise.Reactions.mk c.registrations
        (c.registrations.map (fun r => { r with kind := .reject, handler := none }))
        c.nextObserver := rfl

/-- The erasure onto the landed activation state. Mask M1. -/
theorem activeErase_eq (a : Active) :
    activeErase a =
      (match a with
      | .script => .script
      | .intrinsic job => .intrinsic job.serial
      | .observer job => .job job.serial
      | .checkpoint => .checkpoint) := by
  cases a <;> rfl

/-- `requirement.jobs.1` (625769..626250) and `requirement.jobs.2`
(626257..626350) reach this configuration only through the erasure. Mask M1. -/
theorem runCondition_iff {α ε : Type} (c : Config α ε) :
    Whatwg.Ecma262.Jobs.RunCondition (activeErase c.active) ↔ c.active = Active.checkpoint := by
  cases h : c.active <;>
    simp [Whatwg.Ecma262.Jobs.RunCondition, activeErase]

/-- `lookup` is the landed table read under the owner guard, through Q3's
`Writable.promiseTable` and its `lookupPromise_bridge`. Mask M1. -/
theorem lookup_bridge {α ε : Type} (c : Config α ε) (p : Whatwg.Ecma262.Promise.Ref) :
    lookup c p =
      (if c.owner = p.owner then
        Whatwg.Ecma262.Promise.Table.get (Writable.promiseTable c.writable) p.cell
       else none) := by
  rw [lookup_eq, Writable.lookupPromise_bridge]

/-- Registration lookup is `Reactions.get` at the fulfil list. Mask M1. -/
theorem lookupRegistration_bridge {α ε : Type} (c : Config α ε) (id : Nat) :
    lookupRegistration c id =
      Whatwg.Ecma262.Promise.Reactions.get (reactions c) .fulfill id := rfl

/-- Phase advance is `Reactions.setPhase` at the fulfil list. Mask M1. -/
theorem setRegistrationPhase_bridge {α ε : Type} (c : Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase) :
    (setRegistrationPhase c id phase).registrations =
      (Whatwg.Ecma262.Promise.Reactions.setPhase (reactions c) .fulfill id phase).fulfill := rfl

/-- Scheduling one token is the landed tail append. Mask M2. -/
theorem enqueueJob_queue_bridge {α ε : Type} (c : Config α ε) (kind : JobKind) :
    jobQueue (enqueueJob c kind).1 =
      Whatwg.Ecma262.Jobs.Queue.enqueue (jobQueue c) (enqueueJob c kind).2 := rfl

/--
The reaction half of `register` is Web IDL `react`'s pending branch.

**Builder note B4 of the Q4 landing**: the frozen ascription in
`WhatwgTest/Streams/Semantics/OrderingLaws.lean` closes with
`.map Prod.fst`, which projects the **table** out of `react`'s result tuple and
therefore does not typecheck against the `Option (Reactions Nat)` on the left.
The projection this statement uses is the reactions component, which is what
the ascription's own name and docstring say it is. The coordinator rules
whether the frozen ascription is re-frozen to match. Mask M1.
-/
theorem register_reactions_bridge {α ε : Type} (c : Config α ε)
    (p : Whatwg.Ecma262.Promise.Ref) (callback : Nat) :
    c.owner = p.owner →
    Whatwg.Ecma262.Promise.Table.get (Writable.promiseTable c.writable) p.cell =
        some Whatwg.Ecma262.Promise.State.pending →
      (register c p callback).map reactions =
        ((Whatwg.WebIdl.Promise.react (Writable.promiseTable c.writable) (reactions c)
          Whatwg.Ecma262.Jobs.Queue.empty p.cell (some callback) none).map
            (fun x => x.2.1)) := by
  intro howner hpending
  have hlookup : lookup c p = some Whatwg.Ecma262.Promise.State.pending := by
    rw [lookup_bridge, if_pos howner, hpending]
  rw [register_eq, hlookup]
  rw [Whatwg.WebIdl.Promise.react,
    Whatwg.Ecma262.Promise.performPromiseThen_pending _ _ _ _ _ _ _ hpending]
  simp [reactions, Whatwg.Ecma262.Promise.Reactions.add]

end Whatwg.Streams.Semantics.Ordering
