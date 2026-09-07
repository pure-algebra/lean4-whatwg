import Whatwg.Streams.Transform.Backpressure

/-!
# Transform.DefaultController.lean

Owner: the `TransformStreamDefaultController` state and its abstract
operations: enqueue, error and terminate, and the transform and flush
answers it forwards.

Spec anchors: `ts-default-controller-class`,
`ts-default-controller-internal-slots`,
`ts-default-controller-abstract-ops`.

TRANSFORM-PG-BACKPRESSURE owns these frozen count-profile adapters. They use
actual component continuations; global scheduling and full lifecycle remain open.
-/

namespace Whatwg.Streams.Transform

/-- `op.transform-stream-default-source-pull`, realized through the canonical P4 pull frame. -/
def sourcePull {α β ε : Type} (s : State α β ε) : Option (State α β ε × Nat) :=
  match s.readable.frames with
  | .pull _ :: _ =>
      if s.backpressure then do
        let t ← setBackpressure s false
        let r ← Readable.returnPull t.readable .pending
        let u ← subscribe (withReadable t r) (.readable t.backpressurePromise)
        pure (u, t.backpressurePromise)
      else none
  | _ => none

/-- Service one owned native pull synchronously; a size frame is outside the count profile. -/
def servicePull {α β ε : Type} (s : State α β ε) : Option (State α β ε) :=
  match s.readable.frames with
  | [] => some s
  | .pull _ :: _ => (sourcePull s).map Prod.fst
  | .size _ _ :: _ => none

/-- Canonical P4 read followed by its synchronous owned pull port, if called. -/
def read {α β ε : Type} (s : State α β ε) : Option (State α β ε) :=
  servicePull (withReadable s (Readable.read s.readable))

/-- `op.transform-stream-default-controller-perform-transform`: invoke the named foreign body. -/
def performTransform {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
    (completion : Completion) : Option (State α β ε) :=
  match s.algorithms with
  | some a => some { s with
      control := .awaitTransform request completion s.writable.control.length :: s.control,
      trace := s.trace ++ [.transformCalled request a.transform chunk] }
  | none => none

/--
`op.transform-stream-default-sink-write-algorithm`: capture the old wait cell,
or invoke the foreign transformer before returning from the actual P5 sink call.
-/
def sinkWrite {α β ε : Type} (s : State α β ε) : Option (State α β ε) :=
  match s.control, s.readable.frames, s.writable.control, s.writable.status with
  | [], [], .awaitSink (.write request chunk) :: _, .writable =>
      if s.writable.algorithms.write = some (.foreign s.ports.write) ∧
          Writable.operationPhase s.writable .write request = some .invoking then
        if s.backpressure then do
          let (t, result) := freshInternal s
          let w ← Writable.decide t.writable (.returnSink .pending)
          let u ← subscribe (withWritable t w) (.writable result request)
          subscribe u (.reaction s.backpressurePromise (.write request chunk result))
        else performTransform s request chunk .direct
      else none
  | _, _, _, _ => none

/-- Admit one eventual foreign transform answer only after its callback has returned pending. -/
def answerTransform {α β ε : Type} (s : State α β ε) (request : Nat)
    (answer : Readable.PullAnswer ε) : Option (State α β ε) :=
  match s.pendingTransforms.find? (fun p => p.1 == request) with
  | some (_, result) => some { s with
      pendingTransforms := s.pendingTransforms.filter (fun p => p.1 != request),
      jobs := s.jobs ++ [.reaction (.transform result) answer] }
  | none => none

/--
Return from the actual transformer frame after nested writable work. The new
reaction-result identity is allocated after return, with direct/adopt routing.
-/
def returnTransform {α β ε : Type} (s : State α β ε) (ret : Readable.PullReturn ε) :
    Option (State α β ε) :=
  if s.readable.frames.isEmpty then
    match s.control with
    | .awaitTransform request completion depth :: tail =>
        if s.writable.control.length = depth then do
          let (t, result) := freshInternal { s with control := tail }
          let u : State α β ε := match ret with
            | .pending => { t with pendingTransforms := t.pendingTransforms ++ [(request, result)] }
            | .settled a => { t with jobs := t.jobs ++ [.reaction (.transform result) a] }
          let v := { u with trace := u.trace ++ [.transformReturned request result] }
          match completion with
          | .direct =>
              match v.writable.control with
              | .awaitSink (.write request' _) :: _ =>
                  if request' == request then do
                    let w ← Writable.decide v.writable (.returnSink .pending)
                    subscribe (withWritable v w) (.writable result request)
                  else none
              | _ => none
          | .adopt target => subscribe v (.reaction result (.adopt target))
        else none
    | _ => none
  else none

/-- `op.transform-stream-error`: readable error precedes canonical writable erroring/unblock. -/
def error {α β ε : Type} (s : State α β ε) (reason : Boundary.Exception ε) : State α β ε :=
  let t := withReadable s (Readable.error s.readable reason)
  { t with algorithms := none, control := .errorWritable reason :: .unblock :: s.control }

/-- `op.transform-stream-default-controller-terminate`: retain queued readable output for drain. -/
def terminate {α β ε : Type} (s : State α β ε) : State α β ε :=
  let reason : Boundary.Exception ε := .typeError s.writable.nextError
  let t := withReadable s (Readable.close s.readable)
  let u := withWritable t { t.writable with nextError := t.writable.nextError + 1 }
  { u with algorithms := none, control := .errorWritable reason :: .unblock :: s.control }

/--
`op.transform-stream-default-controller-enqueue`, restricted to count output
sizing. The abstract P4 enqueue and any native pull finish before the BP postlude.
-/
def enqueue {α β ε : Type} (s : State α β ε) (chunk : β) : Option (State α β ε) :=
  if Readable.canCloseOrEnqueue s.readable then
    match s.readable.algorithms with
    | some a =>
        if a.size = .one then do
          let u ← servicePull (withReadable s (Readable.beginEnqueue s.readable chunk))
          let pressure := !Readable.shouldCallPull u.readable
          let v ← if pressure = u.backpressure then some u
            else if pressure then setBackpressure u true else none
          pure { v with
            nextCall := s.nextCall + 1,
            trace := v.trace ++ [.enqueueReturned s.nextCall (.ok ())] }
        else none
    | none => none
  else
    let reason : Boundary.Exception ε := .typeError s.writable.nextError
    let t := withWritable s { s.writable with nextError := s.writable.nextError + 1 }
    some { t with
      nextCall := s.nextCall + 1,
      trace := t.trace ++ [.enqueueReturned s.nextCall (.error reason)] }

/--
The sink-write/PerformTransform reactions: recheck current erroring after waiting;
on foreign rejection, stage canonical erroring/unblock before settling its result.
-/
def react {α β ε : Type} (s : State α β ε) (reaction : Reaction α)
    (answer : Readable.PullAnswer ε) : Option (State α β ε) :=
  match reaction, answer with
  | .write request chunk result, .fulfilled =>
      match s.writable.status with
      | .writable => performTransform s request chunk (.adopt result)
      | .erroring e => settle s result (.rejected e)
      | .closed | .errored _ => none
  | .write _ _ result, .rejected e => settle s result (.rejected e)
  | .transform result, .fulfilled => settle s result .fulfilled
  | .transform result, .rejected e =>
      let t := withReadable s (Readable.error s.readable e)
      some { t with
        algorithms := none,
        control := .errorWritable e :: .unblock :: .settle result (.rejected e) :: s.control }
  | .adopt result, a => settle s result a

end Whatwg.Streams.Transform
