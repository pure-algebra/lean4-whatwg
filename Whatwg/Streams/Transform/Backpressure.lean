import Whatwg.Streams.Transform.Stream

/-!
# Transform.Backpressure.lean

Owner: the coupling that carries backpressure from the readable half back to
the writable half of a transform stream, and the default sink and source
steps that observe it.

Spec anchors: `ts-abstract-ops`, `ts-default-sink-abstract-ops`,
`ts-default-source-abstract-ops`.

TRANSFORM-PG-BACKPRESSURE owns the frozen shared-table adapter and these laws.
No promise table is copied; the component answer/job operations remain canonical.
-/

namespace Whatwg.Streams.Transform

/-- Named view of the P5 cell owner, used by `op.transform-stream-set-backpressure`. -/
def lookupPromise {α β ε : Type} (s : State α β ε) (id : Nat) :
    Option (Readable.PromiseState Unit ε) :=
  (Writable.lookupPromise s.writable id).map Writable.unitPromiseToShared

/-- Allocate a pending internal cell through P5 while retaining every previous cell and ID. -/
def freshInternal {α β ε : Type} (s : State α β ε) : State α β ε × Nat :=
  let (w, id) := Writable.freshPromise s.writable .pending
  let t := withWritable s w
  ({ t with internalPromises := t.internalPromises ++ [id] }, id)

/-- Admit the captured subscriber's answer through its canonical component and queue its tag. -/
def notify {α β ε : Type} (s : State α β ε) (sub : Subscription α)
    (answer : Readable.PullAnswer ε) : Option (State α β ε) :=
  match sub with
  | .readable promise => do
      let r ← Readable.acceptPullAnswer s.readable answer
      pure { withReadable s r with jobs := s.jobs ++ [.readable promise] }
  | .writable _ request => do
      let w ← Writable.acceptAnswer s.writable .write request
        (Writable.sinkAnswerFromShared answer)
      pure { withWritable s w with jobs := s.jobs ++ [.writable request] }
  | .reaction _ reaction => some { s with jobs := s.jobs ++ [.reaction reaction answer] }

/-- Register against the captured identity; already-settled cells queue, rather than run, work. -/
def subscribe {α β ε : Type} (s : State α β ε) (sub : Subscription α) :
    Option (State α β ε) :=
  match lookupPromise s (subscriptionPromise sub) with
  | some .pending => some { s with subscriptions := s.subscriptions ++ [sub] }
  | some (.fulfilled ()) => notify s sub .fulfilled
  | some (.rejected e) => notify s sub (.rejected e)
  | none => none

/-- Resolve through P5 and notify captured subscriptions once, in registration order. -/
def settle {α β ε : Type} (s : State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) : Option (State α β ε) :=
  match lookupPromise s id with
  | some .pending =>
      let outcome : Except (Boundary.Exception ε) Unit :=
        match answer with | .fulfilled => .ok () | .rejected e => .error e
      let t := withWritable s (Writable.settle s.writable id outcome)
      let resting := { t with
        subscriptions := s.subscriptions.filter (fun sub => subscriptionPromise sub != id) }
      (s.subscriptions.filter (fun sub => subscriptionPromise sub == id)).foldlM
        (fun u sub => notify u sub answer) resting
  | _ => some s

/--
`op.transform-stream-set-backpressure`: resolve/queue the OLD cell, then allocate
the NEW pending cell. The equal-flag raw extension is inert, outside the assertion.
-/
def setBackpressure {α β ε : Type} (s : State α β ε) (backpressure : Bool) :
    Option (State α β ε) :=
  if s.backpressure = backpressure then some s
  else do
    let t ← settle s s.backpressurePromise .fulfilled
    let (u, fresh) := freshInternal t
    pure { u with backpressure := backpressure, backpressurePromise := fresh }

/-- `op.transform-stream-unblock-write`, retaining identity when already unblocked. -/
def unblockWrite {α β ε : Type} (s : State α β ε) : Option (State α β ε) :=
  if s.backpressure then setBackpressure s false else some s

end Whatwg.Streams.Transform
