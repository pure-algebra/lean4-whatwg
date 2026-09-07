import Whatwg.Streams.Readable.DefaultReader
import Whatwg.Streams.Writable.Step

/-!
# Piping.Requirements.lean

Owner: the piping requirements stated as a specification over runs: error
and close propagation, the shutdown conditions, and the locking and
backpressure obligations a pipe must meet.

Spec anchors: `pipe-chains`, `rs-abstract-ops`.

Opens in P7.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
# Independent forward-error shutdown requirements

The P2 note above records this module's origin. The following P7a surface
is frozen by PIPING-PG-FORWARD-SHUTDOWN. The observation stops at a request
to finalize; canonical release, full lifecycle and global masks remain open.
-/

namespace Whatwg.Streams.Piping

/-- Intrinsic write-call/result linkage for an already-delivered read; ACTION and STOP. -/
inductive WriteStage where
  | unwritten
  | invoking (call : Nat)
  | submitted (call request : Nat)
  deriving Repr, DecidableEq

/-- One canonical P4 read ID and chunk, with its separate P5 write progress; STOP. -/
structure ReadWriteLink (α : Type) where
  readId : Nat
  chunk : α
  write : WriteStage
  deriving Repr

/-- First selected forward error, captured destination guard and preventAbort flag; PROPAGATE. -/
structure ShutdownPlan (ε : Type) where
  reason : Boundary.Exception ε
  drainRequired : Bool
  preventAbort : Bool
  deriving Repr

/-- Read-only protocol view, retaining canonical components without candidate control phases. -/
structure Snapshot (α ε : Type) where
  source : Readable.State α ε
  destination : Writable.State α ε
  links : List (ReadWriteLink α)
  preventAbort : Bool
  selection : Option (ShutdownPlan ε)
  abortCall : Option Nat
  abortPromise : Option Nat
  finalization : Option (Boundary.Exception ε)

/-- Intrinsic protocol events and canonical component steps; not a host event log or global mask. -/
inductive ProtocolEvent (α ε : Type) where
  | selected (plan : ShutdownPlan ε)
  | writeInvoked (readId : Nat) (chunk : α) (call : Nat)
  | writeReturned (readId call request : Nat)
  | abortInvoked (call : Nat) (reason : Boundary.Exception ε)
  | abortReturned (call request : Nat)
  | readyToFinalize (reason : Boundary.Exception ε)
  | writable (decision : Option (Writable.Decision α ε))
  | sourceError (reason : Boundary.Exception ε)
  | administrative

/-- Before/after evidence for a single protocol event under the named fragment observation. -/
structure ProtocolRecord (α ε : Type) where
  before : Snapshot α ε
  event : ProtocolEvent α ε
  after : Snapshot α ε

/-- The named shutdown-fragment observation, ending before lock release and pipe settlement. -/
structure ShutdownObservation (α ε : Type) where
  initial : Snapshot α ε
  records : List (ProtocolRecord α ε)
  current : Snapshot α ε

/-- requirement.shutdown-must-stop-activity: the independently frozen local surface. -/
def deliveredReads {α ε : Type} (s : Readable.State α ε) : List (Nat × α) :=
  s.trace.filterMap (fun e => match e with
     | .settled (.read id (.ok (.chunk chunk))) => some (id, chunk)
     | _ => none)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def markWrite {α : Type} (ls : List (ReadWriteLink α)) (id : Nat) (stage : WriteStage) :
    List (ReadWriteLink α) :=
  ls.map (fun l => if l.readId = id then { l with write := stage } else l)

/-- requirement.rs-pipe-to-shutdown-with-action: the independently frozen local surface. -/
def WritesSettled {α ε : Type} (s : Snapshot α ε) : Prop :=
  ∀ l ∈ s.links, ∃ call request,
     l.write = .submitted call request ∧
       (Writable.lookupPromise s.destination request = some (.fulfilled ()) ∨
         ∃ reason, Writable.lookupPromise s.destination request = some (.rejected reason))

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def BodyDecision {α ε : Type} (d : Writable.Decision α ε) : Prop :=
  (match d with
     | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => True
     | _ => False)

/-- requirement.shutdown-must-stop-activity: the independently frozen local surface. -/
def ReadInventory {α ε : Type} (s : Snapshot α ε) : Prop :=
  s.links.map (fun l => (l.readId, l.chunk)) = deliveredReads s.source ∧
  (s.links.map ReadWriteLink.readId).Nodup

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def InitialSnapshot {α ε : Type} (s : Snapshot α ε) : Prop :=
  ReadInventory s ∧ (∀ l ∈ s.links, l.write = .unwritten) ∧
  s.selection = none ∧ s.abortCall = none ∧ s.abortPromise = none ∧ s.finalization = none ∧
  s.source.frames = [] ∧ s.source.jobs = [] ∧ s.source.readRequests = [] ∧
  s.source.pulling = false ∧ s.source.pullAwaiting = false ∧
  (s.source.status = .readable ∨ ∃ e, s.source.status = .errored e) ∧
  ∃ hwm algorithms promiseSeed,
    s.destination = Writable.initial hwm algorithms promiseSeed s.source.nextError

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def RecordAllowed {α ε : Type} (r : ProtocolRecord α ε) : Prop :=
  let b := r.before
  let a := r.after
  b.finalization = none ∧ ReadInventory b ∧ ReadInventory a ∧
  a.preventAbort = b.preventAbort ∧ a.source.nextRead = b.source.nextRead ∧
  (match r.event with
  | .selected p =>
      b.selection = none ∧ b.source.status = .errored p.reason ∧
      p.preventAbort = b.preventAbort ∧
      (p.drainRequired = true ↔
        b.destination.status = .writable ∧ b.destination.closeState = .none) ∧
      a = { b with selection := some p }
  | .writeInvoked id chunk call =>
      b.abortCall = none ∧ b.destination.control = [] ∧ call = b.destination.nextCall ∧
      (∃ pre l post, b.links = pre ++ l :: post ∧
        (∀ earlier ∈ pre, earlier.write ≠ .unwritten) ∧
        l.readId = id ∧ l.chunk = chunk ∧ l.write = .unwritten) ∧
      (match b.selection with
        | none => b.source.status = .readable ∧ b.destination.status = .writable ∧
            b.destination.closeState = .none ∧
            ∃ size, Writable.desiredSize b.destination = some size ∧
              Readable.sizePositive size = true
        | some p => p.drainRequired = true) ∧
      Writable.decide b.destination (.write chunk) = some a.destination ∧
      a = { b with
        destination := a.destination,
        links := markWrite b.links id (.invoking call) }
  | .writeReturned id call request =>
      (∃ l ∈ b.links, l.readId = id ∧ l.write = .invoking call) ∧
      Writable.Event.returned call request ∈ b.destination.trace ∧
      (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
      a = { b with links := markWrite b.links id (.submitted call request) }
  | .abortInvoked call reason =>
      b.destination.control = [] ∧ b.abortCall = none ∧
      call = b.destination.nextCall ∧
      (∃ p, b.selection = some p ∧ p.preventAbort = false ∧ reason = p.reason ∧
        (p.drainRequired = false ∨ WritesSettled b)) ∧
      Writable.decide b.destination (.abort reason) = some a.destination ∧
      a = { b with destination := a.destination, abortCall := some call }
  | .abortReturned call request =>
      b.abortCall = some call ∧ b.abortPromise = none ∧
      Writable.Event.returned call request ∈ b.destination.trace ∧
      (∃ outcome, Writable.lookupPromise b.destination request = some outcome) ∧
      a = { b with abortPromise := some request }
  | .readyToFinalize reason =>
      (∃ p, b.selection = some p ∧
        (p.drainRequired = false ∨ WritesSettled b) ∧
        (if p.preventAbort then
          b.abortCall = none ∧ b.abortPromise = none ∧ reason = p.reason
        else ∃ call request, b.abortCall = some call ∧ b.abortPromise = some request ∧
          ((Writable.lookupPromise b.destination request = some (.fulfilled ()) ∧
              reason = p.reason) ∨
            Writable.lookupPromise b.destination request = some (.rejected reason)))) ∧
      a = { b with finalization := some reason }
  | .writable d =>
      (match d with | none => True | some choice => BodyDecision choice) ∧
      Writable.Step b.destination d a.destination ∧
      a = { b with destination := a.destination }
  | .sourceError reason =>
      a = { b with source := Readable.error b.source reason }
  | .administrative => a = b)

/-- Chained canonical snapshots, independent of candidate phases or reachability. -/
def ObservationChain {α ε : Type} (a : Snapshot α ε) :
    List (ProtocolRecord α ε) → Snapshot α ε → Prop
  | [], b => a = b
  | r :: rs, b => r.before = a ∧ ObservationChain r.after rs b

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def ForwardShutdownSpec {α ε : Type} (o : ShutdownObservation α ε) : Prop :=
  InitialSnapshot o.initial ∧
     ObservationChain o.initial o.records o.current ∧
     ∀ r ∈ o.records, RecordAllowed r

end Whatwg.Streams.Piping
