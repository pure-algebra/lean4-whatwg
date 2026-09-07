import Whatwg.Streams.Readable.State

/-!
# Writable.Stream.lean

Owner: the `WritableStream` state as a first-order record: the writable,
erroring, errored and closed cases, the in-flight write and close
bookkeeping, and the stream-level abstract operations.

Spec anchors: `ws-class`, `ws-internal-slots`, `ws-abstract-ops`.

Opens in P5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
The P2 note above records this module's origin. The following post-start,
attached-writer projection is frozen by P5a, `WRITABLE-PG-DEFAULT`. Declaration
roles and source digests are in `docs/WRITABLE-DAG.md`. These are raw first-order
slots and passive views of shared P3/P4 types. Reachability, shared allocation,
global scheduling, and DB-04 observation embeddings remain open.
-/

namespace Whatwg.Streams.Writable

@[instance_reducible] private def exceptDecidableEq {α ε : Type} [DecidableEq α]
    [DecidableEq ε] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

attribute [local instance] exceptDecidableEq

/-- Named view of P3's canonical exact arithmetic carrier; binary64 rounding remains foreign. -/
abbrev Size := Data.DyadicSize

/-- P3's canonical queue-size operations. -/
def sizes : Data.SizeClass Size := Data.DyadicSize.sizes

/-- Shared passive promise outcome, first frozen in P4; not a host promise object. -/
abbrev UnitPromise (ε : Type) := Readable.PromiseState Unit ε

/-- Shared eventual unit callback answer, with the exact exception reason. -/
abbrev SinkAnswer (ε : Type) := Readable.PullAnswer ε

/-- Shared synchronous callback return, distinct from eventual settlement. -/
abbrev SinkReturn (ε : Type) := Readable.PullReturn ε

/-- The unit-outcome view introduces no conversion loss. -/
def unitPromiseToShared {ε : Type} (a : UnitPromise ε) : Readable.PromiseState Unit ε := a

/-- Embed the shared unit-outcome view without changing identity-bearing reasons. -/
def unitPromiseFromShared {ε : Type} (a : Readable.PromiseState Unit ε) : UnitPromise ε := a

/-- Expose the shared answer shape without interpreting a sink body. -/
def sinkAnswerToShared {ε : Type} (a : SinkAnswer ε) : Readable.PullAnswer ε := a

/-- Reuse the shared answer shape without minting a second answer carrier. -/
def sinkAnswerFromShared {ε : Type} (a : Readable.PullAnswer ε) : SinkAnswer ε := a

/-- Expose the shared callback-return shape. -/
def sinkReturnToShared {ε : Type} (a : SinkReturn ε) : Readable.PullReturn ε := a

/-- Reuse the shared callback-return shape. -/
def sinkReturnFromShared {ε : Type} (a : Readable.PullReturn ε) : SinkReturn ε := a

/-- Writable stream state and stored-error slots, with erroring distinct from errored. -/
inductive Status (ε : Type) where
  | writable
  | erroring (reason : Boundary.Exception ε)
  | errored (reason : Boundary.Exception ε)
  | closed
  deriving DecidableEq, Repr

/-- The canonical sized queue carries chunks and the distinct zero-size close sentinel. -/
inductive QueueItem (α : Type) where
  | chunk (value : α)
  | close
  deriving DecidableEq, Repr

/-- A callback is invoking, returned pending, or has its reaction queued. -/
inductive OperationPhase where
  | invoking
  | awaiting
  | queued
  deriving DecidableEq, Repr

/-- Which sink algorithm owns an in-flight operation. -/
inductive SinkKind where
  | write
  | close
  | abort
  deriving DecidableEq, Repr

/-- First-order invocation arguments and the corresponding allocated request identity. -/
inductive SinkOperation (α ε : Type) where
  | write (request : Nat) (chunk : α)
  | close (request : Nat)
  | abort (request : Nat) (reason : Boundary.Exception ε)
  deriving DecidableEq, Repr

/-- The specification's XOR between queued and in-flight close requests is structural. -/
inductive CloseState where
  | none
  | queued (request : Nat)
  | inFlight (request : Nat) (phase : OperationPhase)
  deriving DecidableEq, Repr

/-- An abort requested while already erroring carries no newly stored abort reason. -/
inductive PendingAbort (ε : Type) where
  | requested (request : Nat) (reason : Boundary.Exception ε)
  | alreadyErroring (request : Nat)
  deriving DecidableEq, Repr

/-- Setup installs either the default fulfilled algorithm or a named foreign callback. -/
inductive SinkAlgorithm where
  | fulfilled
  | foreign (name : Nat)
  deriving DecidableEq, Repr

/-- Optional algorithm slots distinguish clearing from an installed default algorithm. -/
structure Algorithms where
  size : Option (Data.SizeAlgorithm Nat)
  write : Option SinkAlgorithm
  close : Option SinkAlgorithm
  abort : Option SinkAlgorithm
  deriving DecidableEq, Repr

/-- A FIFO reaction records its owner, request identity, and admitted eventual answer. -/
structure SinkJob (α ε : Type) where
  kind : SinkKind
  request : Nat
  answer : SinkAnswer ε
  deriving DecidableEq, Repr

/-- Administrative continuations and synchronous callback markers; never stored functions. -/
inductive Control (α ε : Type) where
  | getSize (call : Nat) (chunk : α)
  | awaitSize (call : Nat) (chunk : α)
  | afterSize (call : Nat) (chunk : α) (size : Size)
  | enqueueWrite (chunk : α) (size : Size)
  | advance
  | beginClose (call : Nat)
  | beginAbort (call : Nat) (reason : Boundary.Exception ε)
  | awaitSignal (call : Nat) (reason : Boundary.Exception ε)
  | afterSignal (call : Nat) (reason : Boundary.Exception ε)
  | awaitSink (operation : SinkOperation α ε)
  | startErroring (reason : Boundary.Exception ε)
  | finishErroring
  | errorIfNeeded (reason : Boundary.Exception ε)
  | controllerError (reason : Boundary.Exception ε)
  | dealRejection (reason : Boundary.Exception ε)
  | rejectCloseClosed (reason : Boundary.Exception ε)
  | returnPromise (call request : Nat)
  | returnUnit (call : Nat)
  | react (job : SinkJob α ε)
  deriving DecidableEq, Repr

/-- Local invocation, promise-outcome, and consumer-observation events. -/
inductive Event (α ε : Type) where
  | sizeCalled (algorithm call : Nat) (chunk : α)
  | sinkCalled (algorithm : Nat) (operation : SinkOperation α ε)
  | signalCalled (call : Nat) (reason : Boundary.Exception ε)
  | settled (request : Nat) (result : Except (Boundary.Exception ε) Unit)
  | returned (call request : Nat)
  | readyRead (call request : Nat)
  | closedRead (call request : Nat)
  | desiredSizeRead (call : Nat) (result : Option Size)
  | controllerReturned (call : Nat)
  deriving DecidableEq, Repr

/-- Consumer events of the local ordered candidate view; not the full DB-04 mask. -/
inductive VisibleEvent (ε : Type) where
  | settled (request : Nat) (result : Except (Boundary.Exception ε) Unit)
  | returned (call request : Nat)
  | readyRead (call request : Nat)
  | closedRead (call request : Nat)
  | desiredSizeRead (call : Nat) (result : Option Size)
  | controllerReturned (call : Nat)
  deriving DecidableEq, Repr

/-- Raw post-start slot projection. Global freshness and reachable invariants are separate. -/
structure State (α ε : Type) where
  status : Status ε
  queue : Data.Queue (QueueItem α) Size
  highWaterMark : Size
  backpressure : Bool
  algorithms : Algorithms
  readyPromise : Nat
  closedPromise : Nat
  promises : List (Nat × UnitPromise ε)
  handled : List Nat
  writeRequests : List Nat
  closeState : CloseState
  inFlightWrite : Option (Nat × OperationPhase)
  abortInFlight : Option (Nat × OperationPhase)
  pendingAbort : Option (PendingAbort ε)
  signalArgument : Option (Boundary.Exception ε)
  nextCall : Nat
  nextPromise : Nat
  nextError : Nat
  control : List (Control α ε)
  jobs : List (SinkJob α ε)
  trace : List (Event α ε)

/-- Consumer calls and typed foreign returns/answers; deterministic ticks are not decisions. -/
inductive Decision (α ε : Type) where
  | write (chunk : α)
  | close
  | abort (reason : Boundary.Exception ε)
  | controllerError (reason : Boundary.Exception ε)
  | queryReady
  | queryClosed
  | queryDesiredSize
  | returnSize (answer : Data.SizeAnswer Size (Boundary.Exception ε))
  | returnSink (result : SinkReturn ε)
  | returnSignal
  | answer (kind : SinkKind) (request : Nat) (result : SinkAnswer ε)

/-- Foreign sink-input candidate view; default fulfilled sink algorithms add no invocation. -/
structure SinkObservation (α ε : Type) where
  chunks : List α
  status : Status ε
  deriving DecidableEq, Repr

/-- Local ordered candidate view contains its sink projection and consumer-visible events. -/
structure OrderedObservation (α ε : Type) where
  sink : SinkObservation α ε
  events : List (VisibleEvent ε)
  deriving DecidableEq, Repr

/-- `op.writable-stream-default-controller-get-backpressure`: nonpositive exact size. -/
def sizeNonPositive : Size → Bool
  | .finite units => decide (units ≤ 0)
  | .negInfinity => true
  | _ => false

/-- The admitted post-start projection, with caller-supplied promise and error supply views. -/
def initial {α ε : Type} (hwm : Size) (alg : Algorithms) (promiseSeed errorSeed : Nat) :
    State α ε :=
  { status := .writable, queue := Data.Queue.empty sizes, highWaterMark := hwm,
    backpressure := sizeNonPositive hwm, algorithms := alg,
    readyPromise := promiseSeed, closedPromise := promiseSeed + 1,
    promises := [(promiseSeed, if sizeNonPositive hwm then .pending else .fulfilled ()),
      (promiseSeed + 1, .pending)], handled := [], writeRequests := [], closeState := .none,
    inFlightWrite := none, abortInFlight := none, pendingAbort := none, signalArgument := none,
    nextCall := 0, nextPromise := promiseSeed + 2, nextError := errorSeed,
    control := [], jobs := [], trace := [] }

/-- Look up an allocated promise outcome in the local shared-table view. -/
def lookupPromise {α ε : Type} (s : State α ε) (id : Nat) : Option (UnitPromise ε) :=
  (s.promises.find? (fun p => p.1 == id)).map Prod.snd

/-- Allocate a fresh local cell, retaining every earlier cell and recording immediate outcomes. -/
def freshPromise {α ε : Type} (s : State α ε) (outcome : UnitPromise ε) : State α ε × Nat :=
  let t := { s with
    promises := s.promises ++ [(s.nextPromise, outcome)], nextPromise := s.nextPromise + 1 }
  let result := match outcome with
    | .pending => t
    | .fulfilled _ => { t with trace := s.trace ++ [.settled s.nextPromise (.ok ())] }
    | .rejected reason => { t with trace := s.trace ++ [.settled s.nextPromise (.error reason)] }
  (result, s.nextPromise)

/-- Settle only a pending cell; an absent or already-settled cell is unchanged. -/
def settle {α ε : Type} (s : State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) : State α ε :=
  let pending := match lookupPromise s id with | some .pending => true | _ => false
  { s with
    promises := if pending then s.promises.map (fun p => if p.1 == id then
      (id, match result with | .ok _ => .fulfilled () | .error e => .rejected e) else p)
      else s.promises
    trace := if pending then s.trace ++ [.settled id result] else s.trace }

/-- Retain the local handled marker once without changing its promise identity or outcome. -/
def markHandled {α ε : Type} (s : State α ε) (id : Nat) : State α ε :=
  if id ∈ s.handled then s else { s with handled := s.handled ++ [id] }

/-- `E-45` (generalize, `PROMISE-PG-FIRST`): the sink-job list read as the general
`hook.hostenqueuepromisejob` queue, at payload `SinkJob α ε`. -/
def jobQueue {α ε : Type} (s : State α ε) : Whatwg.Ecma262.Jobs.Queue (SinkJob α ε) :=
  Whatwg.Ecma262.Jobs.Queue.mk s.jobs

/-- `E-13`..`E-15`, `E-18`..`E-23` (generalize, `PROMISE-PG-FIRST`): the promise slots read
as the general promise table. Decision 9 puts `handled` in the cell, so this view folds the
Streams identity list into the per-cell flag; `handled_bridge` is the relation it promises. -/
def promiseTable {α ε : Type} (s : State α ε) :
    Whatwg.Ecma262.Promise.Table Unit (Boundary.Exception ε) :=
  Whatwg.Ecma262.Promise.Table.mk
    (s.promises.map (fun p =>
      (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 (Decidable.decide (p.1 ∈ s.handled)))))
    s.nextPromise

/-- Foreign write callback inputs in invocation order, not all admitted writer writes. -/
def sinkInput {α ε : Type} (s : State α ε) : List α :=
  s.trace.filterMap fun e => match e with
    | .sinkCalled _ (.write _ chunk) => some chunk
    | _ => none

/-- Project the local consumer-visible event alphabet. -/
def visibleEvents {α ε : Type} (s : State α ε) : List (VisibleEvent ε) :=
  s.trace.filterMap fun e => match e with
    | .settled id a => some (.settled id a)
    | .returned call id => some (.returned call id)
    | .readyRead call id => some (.readyRead call id)
    | .closedRead call id => some (.closedRead call id)
    | .desiredSizeRead call size => some (.desiredSizeRead call size)
    | .controllerReturned call => some (.controllerReturned call)
    | _ => none

/-- Promise settlements form one component of the ordered view. -/
def settlementTrace {α ε : Type} (s : State α ε) :
    List (Nat × Except (Boundary.Exception ε) Unit) :=
  s.trace.filterMap fun e => match e with
    | .settled id a => some (id, a)
    | _ => none

/-- The foreign sink-input and terminal-status candidate observation. -/
def observeSink {α ε : Type} (s : State α ε) : SinkObservation α ε :=
  ⟨sinkInput s, s.status⟩

/-- The ordered candidate observation contains its sink projection directly. -/
def observeOrdered {α ε : Type} (s : State α ε) : OrderedObservation α ε :=
  ⟨observeSink s, visibleEvents s⟩

end Whatwg.Streams.Writable
