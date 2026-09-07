import Whatwg.Streams.Piping.Requirements

/-!
# Piping.PipeTo.lean

Owner: the reference `ReadableStreamPipeTo` algorithm as one candidate
realizer of the piping requirements, with its shutdown, abort and
finalization steps.

Spec anchors: `rs-abstract-ops`.

Opens in P7.

The requirements it realizes are owned by
`Whatwg/Streams/Piping/Requirements.lean`; realizability is a claim about the
pair, under a named observation mask.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
# Canonical forward-error shutdown candidate

The P2 note above records this module's origin. The following P7a surface
is frozen by PIPING-PG-FORWARD-SHUTDOWN. The observation stops at a request
to finalize; canonical release, full lifecycle and global masks remain open.
-/

namespace Whatwg.Streams.Piping

/-- Candidate continuations for forward-error shutdown; no completed-pipe constructor. -/
inductive Phase (ε : Type) where
  | running
  | draining
  | returningWrite (readId call : Nat)
  | waitingWrites
  | returningAbort (call : Nat)
  | waitingAbort
  | readyToFinalize (reason : Boundary.Exception ε)
  deriving Repr

/-- Actual canonical components, protocol progress and historical evidence for the fragment. -/
structure State (α ε : Type) where
  source : Readable.State α ε
  destination : Writable.State α ε
  links : List (ReadWriteLink α)
  preventAbort : Bool
  selection : Option (ShutdownPlan ε)
  abortCall : Option Nat
  abortPromise : Option Nat
  phase : Phase ε
  entry : Snapshot α ε
  trace : List (ProtocolRecord α ε)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def snapshot {α ε : Type} (s : State α ε) : Snapshot α ε :=
  ⟨s.source, s.destination, s.links, s.preventAbort, s.selection,
     s.abortCall, s.abortPromise,
     match s.phase with | .readyToFinalize reason => some reason | _ => none⟩

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def initial {α ε : Type} (r : Readable.State α ε) (w : Writable.State α ε) (prevent : Bool) :
    State α ε :=
  let links := (deliveredReads r).map (fun p => ReadWriteLink.mk p.1 p.2 .unwritten)
  {
    source := r, destination := w, links := links, preventAbort := prevent,
    selection := none, abortCall := none, abortPromise := none, phase := .running,
    entry := ⟨r, w, links, prevent, none, none, none, none⟩, trace := [] }

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def observeShutdown {α ε : Type} (s : State α ε) : ShutdownObservation α ε :=
  ⟨s.entry, s.trace, snapshot s⟩

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def emit {α ε : Type} (s : State α ε) (e : ProtocolEvent α ε) (t : State α ε) : State α ε :=
  { t with
    entry := s.entry,
    trace := s.trace ++ [⟨snapshot s, e, snapshot t⟩] }

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def Admitted {α ε : Type} (s : State α ε) : Prop :=
  InitialSnapshot (snapshot s) ∧
     s.phase = .running ∧ s.entry = snapshot s ∧ s.trace = []

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def drainGuard {α ε : Type} (w : Writable.State α ε) : Bool :=
  (match w.status with | .writable => !Writable.closeQueuedOrInFlight w | _ => false)

/-- First still-unwritten read obligation, retaining ID order even when chunks are equal. -/
def nextUnwritten {α : Type} : List (ReadWriteLink α) → Option (ReadWriteLink α)
  | [] => none
  | l :: ls => match l.write with
      | .unwritten => some l
      | _ => nextUnwritten ls

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def allWrittenSettled {α ε : Type} (w : Writable.State α ε) (ls : List (ReadWriteLink α)) : Bool :=
  ls.all (fun l =>
     match l.write with
     | .submitted _ request => match Writable.lookupPromise w request with
         | some (.fulfilled _) | some (.rejected _) => true
         | _ => false
     | _ => false)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def lookupReturn {α ε : Type} (w : Writable.State α ε) (call : Nat) : Option Nat :=
  w.trace.findSome? (fun e => match e with
     | .returned c request => if c = call then some request else none
     | _ => none)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def foreignDecision {α ε : Type} (d : Writable.Decision α ε) : Bool :=
  (match d with
     | .controllerError _ | .answer _ _ _ | .returnSize _ | .returnSink _ | .returnSignal => true
     | _ => false)

/--
requirement.error-and-close-states-must-be-propagated: the independently frozen local surface.
-/
def enterForwardShutdown {α ε : Type} (s : State α ε) : State α ε :=
  (match s.selection, s.source.status with
  | none, .errored reason =>
      let p : ShutdownPlan ε := ⟨reason, drainGuard s.destination, s.preventAbort⟩
      emit s (.selected p) { s with selection := some p, phase := .draining }
  | _, _ => s)

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def invokeWrite {α ε : Type} (s : State α ε) (l : ReadWriteLink α) : Option (State α ε) :=
  (Writable.decide s.destination (.write l.chunk)).map (fun w =>
     emit s (.writeInvoked l.readId l.chunk s.destination.nextCall)
       { s with
         destination := w,
         links := markWrite s.links l.readId (.invoking s.destination.nextCall),
         phase := .returningWrite l.readId s.destination.nextCall })

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def captureWrite {α ε : Type} (s : State α ε) (id call : Nat) : Option (State α ε) :=
  (lookupReturn s.destination call).map (fun request =>
     emit s (.writeReturned id call request)
       { s with
         links := markWrite s.links id (.submitted call request),
         phase := match s.selection with | none => .running | some _ => .draining })

/-- requirement.rs-pipe-to-shutdown-with-action: the independently frozen local surface. -/
def invokeAbort {α ε : Type} (s : State α ε) (p : ShutdownPlan ε) : Option (State α ε) :=
  (Writable.decide s.destination (.abort p.reason)).map (fun w =>
     emit s (.abortInvoked s.destination.nextCall p.reason)
       { s with
         destination := w, abortCall := some s.destination.nextCall,
         phase := .returningAbort s.destination.nextCall })

/-- PIPING-PG-FORWARD-SHUTDOWN: the independently frozen local surface. -/
def captureAbort {α ε : Type} (s : State α ε) (call : Nat) : Option (State α ε) :=
  (lookupReturn s.destination call).map (fun request =>
     emit s (.abortReturned call request)
       { s with abortPromise := some request, phase := .waitingAbort })

/--
requirement.rs-pipe-to-finalize (request frontier only): the independently frozen local surface.
-/
def requestFinalize {α ε : Type} (s : State α ε) (reason : Boundary.Exception ε) : State α ε :=
  emit s (.readyToFinalize reason) { s with phase := .readyToFinalize reason }

end Whatwg.Streams.Piping
