import Whatwg.Streams.Writable.Stream

/-!
# Writable.Backpressure.lean

Owner: the writable backpressure signal: when the queue is deemed full, and
how the ready promise of the current writer is set and reset as that answer
changes.

Spec anchors: `ws-abstract-ops`, `ws-abstract-ops-used-by-controllers`.

Opens in P5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
The P2 note above is historical. P5a freezes these slot operations under
WRITABLE-PG-DEFAULT. They support the local ordered and sink candidate views;
the full writer, reachability, and DB-04 embeddings remain open.
-/

namespace Whatwg.Streams.Writable

variable {α ε : Type}

/-- `op.writable-stream-default-writer-ensure-ready-promise-rejected`: retain or replace ready. -/
def ensureReadyRejected (s : State α ε) (e : Boundary.Exception ε) : State α ε :=
  match lookupPromise s s.readyPromise with
  | some .pending => markHandled (settle s s.readyPromise (.error e)) s.readyPromise
  | _ =>
      let r := freshPromise s (.rejected e)
      markHandled { r.1 with readyPromise := r.2 } r.2

/-- `op.writable-stream-update-backpressure`: replacement never overwrites old ready cells. -/
def updateBackpressure (s : State α ε) (b : Bool) : State α ε :=
  if s.backpressure = b then s
  else if b then
    let r := freshPromise s .pending
    { r.1 with readyPromise := r.2, backpressure := true }
  else { settle s s.readyPromise (.ok ()) with backpressure := false }

/-- `op.writable-stream-default-writer-get-desired-size`, in P3's exact arithmetic view. -/
def desiredSize (s : State α ε) : Option Size :=
  match s.status with
  | .writable => some (sizes.sub s.highWaterMark s.queue.totalSize)
  | .closed => some sizes.zero
  | .erroring _ | .errored _ => none

/-- `op.writable-stream-default-controller-get-backpressure`: inspect controller desired size. -/
def getBackpressure (s : State α ε) : Bool :=
  sizeNonPositive (sizes.sub s.highWaterMark s.queue.totalSize)

/-- `op.writable-stream-default-controller-clear-algorithms`: remove all four installed slots. -/
def clearAlgorithms (s : State α ε) : State α ε :=
  { s with algorithms := { size := none, write := none, close := none, abort := none } }

/-- `op.writable-stream-close-queued-or-in-flight`: the tagged close-request alternatives. -/
def closeQueuedOrInFlight (s : State α ε) : Bool :=
  match s.closeState with | .none => false | _ => true

/-- `op.writable-stream-has-operation-marked-in-flight`: abort is not a write or close. -/
def hasInFlight (s : State α ε) : Bool :=
  s.inFlightWrite.isSome || (match s.closeState with | .inFlight _ _ => true | _ => false)

end Whatwg.Streams.Writable
