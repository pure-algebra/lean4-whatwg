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

/-! ## Q4 amendment A4: the phase erasure and the reaction half of `notifySettled`

Amendment A4 of `test/contracts/configuration-ordering.contract.md`
(breaker seat, branch `promise/q4-amend`, 2026-09-07), under builder note B3 and
counterexample `WS-PROM-CE-039`. The frozen statement

```text
  Writable.lookupPromise c.writable id = some (.fulfilled ()) →
    (notifySettled c id).registrations =
      (triggerReactions (reactions c) id .fulfill (.ok ()) Queue.empty).1.fulfill
```

is **false**, not merely unproved: decision 2 of §3.3 gives this configuration
two unrelated monotone supplies, so `notifySettled` writes `.queued
queued.2.serial`, a job serial drawn from `Config.nextJob`, where
`op.triggerpromisereactions` writes `.queued r.id`, a registration id. The
amendment restates it modulo the erasure below and recovers the dropped payload
exactly in `notifySettled_queued_serial`.

The erasure lives here rather than in `Whatwg/Ecma262/Promise.lean` because that
file belongs to the Q3 and Q3b packets and is outside the Q4 fence of §9, and
because §2.5's `activeErase` is already the Q4-owned pattern for erasing exactly
this kind of carrier difference. -/

/-- Q4 amendment A4: "up to the payload" on a reaction phase, realized by
normalizing the payload to `0`, so the codomain stays `ReactionPhase` and the
bridge stays a plain list equality. Idempotent, and no law reads the normalized
payload: `notifySettled_queued_serial` recovers it from the token FIFO's own
supply. -/
def phaseErase : Whatwg.Ecma262.Promise.ReactionPhase → Whatwg.Ecma262.Promise.ReactionPhase
  | .waiting => .waiting
  | .queued _ => .queued 0
  | .running _ => .running 0
  | .done => .done

/-- Q4 amendment A4: `phaseErase` lifted to a whole reaction record. Every other
field is retained, so the erased lists still compare identity, promise, tag,
handler and capability. -/
def reactionErase {body : Type} (r : Whatwg.Ecma262.Promise.Reaction body) :
    Whatwg.Ecma262.Promise.Reaction body :=
  { r with phase := phaseErase r.phase }

/-- The erasure, frozen as an equation so it cannot be widened. Mask M1. -/
theorem phaseErase_eq (phase : Whatwg.Ecma262.Promise.ReactionPhase) :
    phaseErase phase =
      (match phase with
      | .waiting => .waiting
      | .queued _ => .queued 0
      | .running _ => .running 0
      | .done => .done) := by
  cases phase <;> rfl

/-- Mask M1. -/
theorem reactionErase_eq {body : Type} (r : Whatwg.Ecma262.Promise.Reaction body) :
    reactionErase r = { r with phase := phaseErase r.phase } := rfl

/-- The one-registration step of `notifySettled`'s fold, named so the two Q4
receipts below can be stated and proved over it. `notifySettled_fold` is the
`rfl` that ties it to the frozen body, which is unchanged. -/
private def notifyStep {α ε : Type} (id : Nat) (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) : Config α ε :=
  match r.phase with
  | .waiting =>
      if r.promise == id then
        let queued := enqueueJob acc (.observer r.id)
        setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
      else acc
  | _ => acc

/-- The settled branch of the frozen `notifySettled` body, as a fold over the
named step. Closes by `rfl`: no definition changes. -/
private theorem notifySettled_fold {α ε : Type} (c : Config α ε) (id : Nat)
    (h : Writable.lookupPromise c.writable id = some (.fulfilled ())) :
    notifySettled c id = c.registrations.foldl (notifyStep id) c := by
  rw [notifySettled_eq, h]
  rfl

/-- The erased image of one fold step: a pointwise map on the erased list whose
only datum is the triggered registration's identity. This is the step at which
the job serial disappears and the two cursors stop mattering. -/
private def eraseStep (id : Nat) (r : Whatwg.Ecma262.Promise.Reaction Nat)
    (y : Whatwg.Ecma262.Promise.Reaction Nat) : Whatwg.Ecma262.Promise.Reaction Nat :=
  if r.phase = .waiting ∧ r.promise = id ∧ y.id = r.id then
    { y with phase := .queued 0 }
  else y

/-- Folding a list of pointwise maps is the pointwise map of the folds. -/
private theorem foldl_map_comm {A B : Type} (h : A → B → B) :
    ∀ (l : List A) (L : List B),
      l.foldl (fun L a => L.map (h a)) L = L.map (fun b => l.foldl (fun b a => h a b) b)
  | [], L => by simp
  | a :: l, L => by
      simp only [List.foldl_cons]
      rw [foldl_map_comm h l (L.map (h a)), List.map_map]
      rfl

/-- One fold step, erased. The job serial `acc.nextJob` is exactly what the
erasure drops, which is why the right-hand side needs no accumulator. -/
private theorem notifyStep_erased {α ε : Type} (id : Nat) (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) :
    (notifyStep id acc r).registrations.map reactionErase =
      (acc.registrations.map reactionErase).map (eraseStep id r) := by
  rw [List.map_map]
  by_cases hw : r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting
  · by_cases hp : r.promise = id
    · have hstep : (notifyStep id acc r).registrations =
          acc.registrations.map
            (fun y => if y.id == r.id then
              { y with phase := .queued acc.nextJob } else y) := by
        simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]
      rw [hstep, List.map_map]
      refine List.map_congr_left ?_
      intro y _
      by_cases hy : y.id = r.id <;>
        simp [Function.comp_apply, hy, eraseStep, hw, hp, reactionErase, phaseErase]
    · have hstep : notifyStep id acc r = acc := by simp [notifyStep, hw, hp]
      rw [hstep]
      refine List.map_congr_left ?_
      intro y _
      simp [Function.comp_apply, eraseStep, hp]
  · have hstep : notifyStep id acc r = acc := by
      cases hcase : r.phase <;> simp_all [notifyStep]
    rw [hstep]
    refine List.map_congr_left ?_
    intro y _
    simp [Function.comp_apply, eraseStep, hw]

/-- The whole fold, erased: the accumulator disappears and only a pointwise map
survives. -/
private theorem notify_fold_erased {α ε : Type} (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      (l.foldl (notifyStep id) acc).registrations.map reactionErase =
        l.foldl (fun L r => L.map (eraseStep id r)) (acc.registrations.map reactionErase)
  | [], _ => rfl
  | r :: l, acc => by
      simp only [List.foldl_cons]
      rw [notify_fold_erased id l (notifyStep id acc r), notifyStep_erased]

/-- No step of the erased fold touches a registration whose identity none of the
folded entries carries. -/
private theorem eraseStep_noop (id : Nat) :
    ∀ (m : List (Whatwg.Ecma262.Promise.Reaction Nat))
      (y : Whatwg.Ecma262.Promise.Reaction Nat),
      (∀ r ∈ m, r.id ≠ y.id) → m.foldl (fun y r => eraseStep id r y) y = y
  | [], _, _ => rfl
  | a :: m, y, h => by
      have ha : a.id ≠ y.id := h a (by simp)
      have hcond : ¬ (a.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting ∧
          a.promise = id ∧ y.id = a.id) := by
        rintro ⟨_, _, hid⟩
        exact ha hid.symm
      have hy : eraseStep id a y = y := by simp only [eraseStep, if_neg hcond]
      simp only [List.foldl_cons, hy]
      exact eraseStep_noop id m y (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- Under distinct registration identities the erased fold fires at most once for
each entry, at that entry's own position. This is the clause the `Nodup`
hypothesis of `notifySettled_reactions_bridge` buys: `setRegistrationPhase`
selects by identity alone, so two registrations sharing an identity but
addressing different promises make even the erased equality false. -/
private theorem eraseStep_single (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat))
      (x y : Whatwg.Ecma262.Promise.Reaction Nat),
      y.id = x.id → (l.map (fun r => r.id)).Nodup → x ∈ l →
        l.foldl (fun y r => eraseStep id r y) y =
          if x.phase = .waiting ∧ x.promise = id then { y with phase := .queued 0 } else y
  | [], _, _, _, _, hx => absurd hx (List.not_mem_nil)
  | a :: l, x, y, hyx, hnd, hx => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndl⟩ := hnd
      by_cases hxa : x = a
      · subst hxa
        have hrest : ∀ r ∈ l, r.id ≠ (eraseStep id x y).id := by
          intro r hr
          have : r.id ∈ l.map (fun r => r.id) := List.mem_map_of_mem hr
          have hne : x.id ≠ r.id := fun heq => hnot (heq ▸ this)
          have : (eraseStep id x y).id = y.id := by
            simp only [eraseStep]; split <;> rfl
          rw [this, hyx]
          exact fun h => hne h.symm
        simp only [List.foldl_cons]
        rw [eraseStep_noop id l _ hrest]
        simp only [eraseStep, hyx, and_true]
      · have hxl : x ∈ l := (List.mem_cons.mp hx).resolve_left hxa
        have hax : a.id ≠ y.id := by
          rw [hyx]
          intro heq
          exact hnot (heq ▸ List.mem_map_of_mem hxl)
        have hcond : ¬ (a.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting ∧
            a.promise = id ∧ y.id = a.id) := by
          rintro ⟨_, _, hid⟩
          exact hax hid.symm
        have ha : eraseStep id a y = y := by simp only [eraseStep, if_neg hcond]
        simp only [List.foldl_cons, ha]
        exact eraseStep_single id l x y hyx hndl hxl

/--
Q4 amendment A4. The reaction half of `notifySettled`, modulo the phase erasure
and under distinct registration identities: the same registrations leave
`waiting`, in the same list order, on the same trigger, as
`op.triggerpromisereactions` (2700260..2701212) leaves them. Only the reaction
half: the landed operation writes a `Jobs.Queue (Jobs.ReactionJob …)` while this
configuration has one heterogeneous token queue (§2.6 of the contract).

The payload the erasure drops is recovered exactly by
`notifySettled_queued_serial` below, so the pair is strictly more informative
than the false equality it replaces (`WS-PROM-CE-039`). Mask M1.
-/
theorem notifySettled_reactions_bridge {α ε : Type} (c : Config α ε) (id : Nat)
    (hnd : (c.registrations.map (fun r => r.id)).Nodup)
    (h : Writable.lookupPromise c.writable id = some (.fulfilled ())) :
    (notifySettled c id).registrations.map reactionErase =
      ((Whatwg.Ecma262.Promise.triggerReactions (reactions c) id .fulfill
        (Except.ok () : Except (Boundary.Exception ε) Unit)
        Whatwg.Ecma262.Jobs.Queue.empty).1.fulfill).map reactionErase := by
  rw [notifySettled_fold c id h, notify_fold_erased, foldl_map_comm, List.map_map]
  simp only [Whatwg.Ecma262.Promise.triggerReactions, reactions, List.map_map]
  refine List.map_congr_left ?_
  intro x hx
  rw [Function.comp_apply, Function.comp_apply,
    eraseStep_single id c.registrations x (reactionErase x) rfl hnd hx]
  by_cases hw : x.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting
  · by_cases hp : x.promise = id
    · simp [hw, hp, reactionErase, phaseErase]
    · simp [hw, hp, reactionErase, phaseErase]
  · cases hcase : x.phase <;> simp_all [reactionErase, phaseErase]

/-! ### The payload the erasure drops -/

/-- Under distinct identities the identity search returns the entry itself. -/
private theorem find?_id_of_nodup :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat))
      (r : Whatwg.Ecma262.Promise.Reaction Nat),
      (l.map (fun x => x.id)).Nodup → r ∈ l → l.find? (fun x => x.id == r.id) = some r
  | [], _, _, hr => absurd hr List.not_mem_nil
  | a :: l, r, hnd, hr => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndl⟩ := hnd
      by_cases hra : r = a
      · subst hra
        simp only [List.find?_cons, beq_self_eq_true]
      · have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left hra
        have hne : (a.id == r.id) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro h
          exact hnot (h ▸ List.mem_map_of_mem hrl)
        simp only [List.find?_cons, hne]
        exact find?_id_of_nodup l r hndl hrl

/-- Under distinct identities, `lookupRegistration` returns the entry itself. -/
private theorem lookupRegistration_mem {α ε : Type} (c : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat)
    (hnd : (c.registrations.map (fun x => x.id)).Nodup) (hr : r ∈ c.registrations) :
    lookupRegistration c r.id = some r :=
  find?_id_of_nodup c.registrations r hnd hr

/-- A phase advance preserves every identity, so the identity search commutes
with it. -/
private theorem find?_setPhaseMap (L : List (Whatwg.Ecma262.Promise.Reaction Nat))
    (rid k : Nat) (ph : Whatwg.Ecma262.Promise.ReactionPhase) :
    (L.map (fun y => if y.id == rid then { y with phase := ph } else y)).find?
        (fun x => x.id == k) =
      (L.find? (fun x => x.id == k)).map
        (fun y => if y.id == rid then { y with phase := ph } else y) := by
  have hcomp : ((fun x : Whatwg.Ecma262.Promise.Reaction Nat => x.id == k) ∘
      (fun y : Whatwg.Ecma262.Promise.Reaction Nat =>
        if y.id == rid then { y with phase := ph } else y)) =
      (fun x : Whatwg.Ecma262.Promise.Reaction Nat => x.id == k) := by
    funext y
    simp only [Function.comp_apply]
    by_cases hy : y.id = rid <;> simp [hy]
  rw [List.find?_map, hcomp]

/-- A phase advance at one identity is invisible at every other identity. -/
private theorem find?_setPhase_other (L : List (Whatwg.Ecma262.Promise.Reaction Nat))
    (rid k : Nat) (ph : Whatwg.Ecma262.Promise.ReactionPhase) (h : rid ≠ k) :
    (L.map (fun y => if y.id == rid then { y with phase := ph } else y)).find?
        (fun x => x.id == k) = L.find? (fun x => x.id == k) := by
  rw [find?_setPhaseMap]
  cases hf : L.find? (fun x => x.id == k) with
  | none => rfl
  | some y =>
      have hy : y.id = k := by simpa using List.find?_some hf
      have hne : ¬ (y.id = rid) := by rw [hy]; exact fun heq => h heq.symm
      simp [hne]

/-- A phase advance is observable exactly at the identity it names. -/
private theorem find?_setPhase_self (L : List (Whatwg.Ecma262.Promise.Reaction Nat))
    (k : Nat) (ph : Whatwg.Ecma262.Promise.ReactionPhase) :
    (L.map (fun y => if y.id == k then { y with phase := ph } else y)).find?
        (fun x => x.id == k) =
      (L.find? (fun x => x.id == k)).map (fun y => { y with phase := ph }) := by
  rw [find?_setPhaseMap]
  cases hf : L.find? (fun x => x.id == k) with
  | none => rfl
  | some y =>
      have hy : y.id = k := by simpa using List.find?_some hf
      simp [hy]

/-- One fold step appends to the token FIFO and removes nothing. -/
private theorem notifyStep_jobs {α ε : Type} (id : Nat) (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) :
    ∃ ext, (notifyStep id acc r).jobs = acc.jobs ++ ext := by
  by_cases hw : r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting
  · by_cases hp : r.promise = id
    · exact ⟨[⟨acc.nextJob, .observer r.id⟩], by
        simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]⟩
    · exact ⟨[], by simp [notifyStep, hw, hp]⟩
  · refine ⟨[], ?_⟩
    have hstep : notifyStep id acc r = acc := by
      cases hcase : r.phase <;> simp_all [notifyStep]
    simp [hstep]

/-- The whole fold appends to the token FIFO and removes nothing. -/
private theorem notify_fold_jobs {α ε : Type} (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      ∃ ext, (l.foldl (notifyStep id) acc).jobs = acc.jobs ++ ext
  | [], _ => ⟨[], by simp⟩
  | r :: l, acc => by
      obtain ⟨e0, h0⟩ := notifyStep_jobs id acc r
      obtain ⟨e1, h1⟩ := notify_fold_jobs id l (notifyStep id acc r)
      exact ⟨e0 ++ e1, by simp only [List.foldl_cons, h1, h0, List.append_assoc]⟩

/-- The job cursor is monotone along one fold step. -/
private theorem notifyStep_nextJob {α ε : Type} (id : Nat) (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) :
    acc.nextJob ≤ (notifyStep id acc r).nextJob := by
  by_cases hw : r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting
  · by_cases hp : r.promise = id
    · simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]
    · simp [notifyStep, hw, hp]
  · have hstep : notifyStep id acc r = acc := by
      cases hcase : r.phase <;> simp_all [notifyStep]
    simp [hstep]

/-- The job cursor is monotone along the whole fold. -/
private theorem notify_fold_nextJob {α ε : Type} (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      acc.nextJob ≤ (l.foldl (notifyStep id) acc).nextJob
  | [], _ => Nat.le_refl _
  | r :: l, acc =>
      Nat.le_trans (notifyStep_nextJob id acc r)
        (notify_fold_nextJob id l (notifyStep id acc r))

/-- A fold step at another registration leaves this one's entry alone. -/
private theorem notifyStep_lookup_other {α ε : Type} (id : Nat) (acc : Config α ε)
    (r : Whatwg.Ecma262.Promise.Reaction Nat) (k : Nat) (h : r.id ≠ k) :
    lookupRegistration (notifyStep id acc r) k = lookupRegistration acc k := by
  by_cases hw : r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting
  · by_cases hp : r.promise = id
    · have hstep : (notifyStep id acc r).registrations =
          acc.registrations.map
            (fun y => if y.id == r.id then
              { y with phase := .queued acc.nextJob } else y) := by
        simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]
      simp only [lookupRegistration, hstep]
      exact find?_setPhase_other acc.registrations r.id k _ h
    · have hstep : notifyStep id acc r = acc := by simp [notifyStep, hw, hp]
      rw [hstep]
  · have hstep : notifyStep id acc r = acc := by
      cases hcase : r.phase <;> simp_all [notifyStep]
    rw [hstep]

/-- A fold over registrations none of which carries this identity leaves this
one's entry alone. -/
private theorem notify_fold_lookup_other {α ε : Type} (id : Nat) (k : Nat) :
    ∀ (m : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      (∀ b ∈ m, b.id ≠ k) →
      lookupRegistration (m.foldl (notifyStep id) acc) k = lookupRegistration acc k
  | [], _, _ => rfl
  | b :: m, acc, h => by
      simp only [List.foldl_cons]
      rw [notify_fold_lookup_other id k m (notifyStep id acc b)
            (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        notifyStep_lookup_other id acc b k (h b (by simp))]

/-- The serial recovery, as a statement about the fold. -/
private theorem notify_fold_serial {α ε : Type} (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε)
      (r : Whatwg.Ecma262.Promise.Reaction Nat),
      (l.map (fun x => x.id)).Nodup → r ∈ l → r.promise = id →
      r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting →
      lookupRegistration acc r.id = some r →
      ∃ serial, acc.nextJob ≤ serial ∧
        lookupRegistration (l.foldl (notifyStep id) acc) r.id =
          some { r with phase := .queued serial } ∧
        Job.mk serial (.observer r.id) ∈ (l.foldl (notifyStep id) acc).jobs
  | [], _, _, _, hr, _, _, _ => absurd hr List.not_mem_nil
  | a :: l, acc, r, hnd, hr, hp, hw, hlook => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hndl⟩ := hnd
      by_cases hra : r = a
      · subst hra
        have hrest : ∀ b ∈ l, b.id ≠ r.id := by
          intro b hb heq
          exact hnot (heq ▸ List.mem_map_of_mem hb)
        have hsteps : (notifyStep id acc r).registrations =
            acc.registrations.map
              (fun y => if y.id == r.id then
                { y with phase := .queued acc.nextJob } else y) := by
          simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]
        have hstepj : (notifyStep id acc r).jobs =
            acc.jobs ++ [⟨acc.nextJob, .observer r.id⟩] := by
          simp [notifyStep, hw, hp, setRegistrationPhase, enqueueJob]
        refine ⟨acc.nextJob, Nat.le_refl _, ?_, ?_⟩
        · simp only [List.foldl_cons]
          rw [notify_fold_lookup_other id r.id l (notifyStep id acc r) hrest]
          simp only [lookupRegistration, hsteps]
          rw [find?_setPhase_self acc.registrations r.id _]
          rw [show acc.registrations.find? (fun x => x.id == r.id) = some r from hlook]
          rfl
        · obtain ⟨ext, hext⟩ := notify_fold_jobs id l (notifyStep id acc r)
          simp only [List.foldl_cons, hext, hstepj]
          simp
      · have hrl : r ∈ l := (List.mem_cons.mp hr).resolve_left hra
        have hane : a.id ≠ r.id := by
          intro heq
          exact hnot (heq ▸ List.mem_map_of_mem hrl)
        have hlook' : lookupRegistration (notifyStep id acc a) r.id = some r := by
          rw [notifyStep_lookup_other id acc a r.id hane, hlook]
        obtain ⟨serial, hle, hfound, hjob⟩ :=
          notify_fold_serial id l (notifyStep id acc a) r hndl hrl hp hw hlook'
        exact ⟨serial, Nat.le_trans (notifyStep_nextJob id acc a) hle, hfound, hjob⟩

/--
Q4 amendment A4. The payload `reactionErase` drops, recovered exactly: every
registration this notification triggers is left `.queued s` for the serial of the
`.observer` token the same notification appended to the configuration's own
token FIFO, and that serial is drawn at or after `c.nextJob`.

This is the "separate lemma" the erasure owes, and together with
`notifySettled_reactions_bridge` it is what the false frozen equality was
reaching for: the first says the same registrations leave `waiting` in the same
order, the second recovers the payload and ties it to the queue, which is the
fact a later CFG-FIFO obligation needs. Mask M2: the statement observes the
token entering the queue.
-/
theorem notifySettled_queued_serial {α ε : Type} (c : Config α ε) (id : Nat)
    (r : Whatwg.Ecma262.Promise.Reaction Nat)
    (hnd : (c.registrations.map (fun x => x.id)).Nodup)
    (h : Writable.lookupPromise c.writable id = some (.fulfilled ()))
    (hmem : r ∈ c.registrations) (hp : r.promise = id)
    (hw : r.phase = Whatwg.Ecma262.Promise.ReactionPhase.waiting) :
    ∃ serial : Nat, c.nextJob ≤ serial ∧
      lookupRegistration (notifySettled c id) r.id =
        some { r with phase := .queued serial } ∧
      Job.mk serial (.observer r.id) ∈ (jobQueue (notifySettled c id)).pending := by
  rw [notifySettled_fold c id h]
  exact notify_fold_serial id c.registrations c r hnd hmem hp hw
    (lookupRegistration_mem c r hnd hmem)

end Whatwg.Streams.Semantics.Ordering
