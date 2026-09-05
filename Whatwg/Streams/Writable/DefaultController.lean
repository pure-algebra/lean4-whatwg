import Whatwg.Streams.Writable.Backpressure

/-!
# Writable.DefaultController.lean

Owner: the `WritableStreamDefaultController` state and its abstract
operations: the write queue with sizes, the abort reason it carries, and
error and close processing.

Spec anchors: `ws-default-controller-class`,
`ws-default-controller-internal-slots`,
`ws-default-controller-abstract-ops`.

Opens in P5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/

/-!
The P2 note above is historical. WRITABLE-PG-DEFAULT freezes the administrative
stages below. A foreign marker suspends synchronous work; only an empty stack
admits the oldest promise reaction. Raw states violating specification assertions
may have no next transition. Full reachability and global embeddings remain open.
-/

namespace Whatwg.Streams.Writable

variable {α ε : Type}

/-- A consumer may enter only between synchronous calls or inside a foreign callback. -/
def externalFrontier (s : State α ε) : Bool :=
  match s.control with
  | [] | .awaitSize _ _ :: _ | .awaitSink _ :: _ | .awaitSignal _ _ :: _ => true
  | _ => false

/-- Which named sink boundary owns this first-order operation. -/
def operationKind : SinkOperation α ε → SinkKind
  | .write _ _ => .write
  | .close _ => .close
  | .abort _ _ => .abort

/-- The promise request allocated before the sink operation starts. -/
def operationRequest : SinkOperation α ε → Nat
  | .write id _ | .close id | .abort id _ => id

/-- Look up a matching in-flight request without confusing equal IDs in different slots. -/
def operationPhase (s : State α ε) (kind : SinkKind) (id : Nat) : Option OperationPhase :=
  let slot := match kind with
    | .write => s.inFlightWrite
    | .close => match s.closeState with | .inFlight n phase => some (n, phase) | _ => none
    | .abort => s.abortInFlight
  slot.bind fun p => if p.1 == id then some p.2 else none

/-- Update the phase of one named operation, retaining its request identity. -/
def setOperationPhase (s : State α ε) (op : SinkOperation α ε) (phase : OperationPhase) :
    State α ε :=
  match op with
  | .write id _ => { s with inFlightWrite := some (id, phase) }
  | .close id => { s with closeState := .inFlight id phase }
  | .abort id _ => { s with abortInFlight := some (id, phase) }

/--
`op.writable-stream-default-controller-process-close` and `op.ws-default-controller-private-abort`:
clear algorithms after callback return, then attach the eventual reaction.
-/
def attachSink (s : State α ε) (op : SinkOperation α ε) (ret : SinkReturn ε) : State α ε :=
  let b := match op with | .write _ _ => s | .close _ | .abort _ _ => clearAlgorithms s
  match ret with
  | .pending => setOperationPhase b op .awaiting
  | .settled answer =>
      { setOperationPhase b op .queued with
        jobs := b.jobs ++ [⟨operationKind op, operationRequest op, answer⟩] }

/-- Invoke an installed default/foreign sink algorithm, suspending before a foreign return. -/
def invokeSink (s : State α ε) (op : SinkOperation α ε) : Option (State α ε) :=
  let alg := match op with
    | .write _ _ => s.algorithms.write
    | .close _ => s.algorithms.close
    | .abort _ _ => s.algorithms.abort
  match alg with
  | none => none
  | some .fulfilled => some (attachSink s op (.settled .fulfilled))
  | some (.foreign name) =>
      some { setOperationPhase s op .invoking with
        control := .awaitSink op :: s.control, trace := s.trace ++ [.sinkCalled name op] }

/-- Admit an eventual answer only for a matching operation whose pending promise was returned. -/
def acceptAnswer (s : State α ε) (kind : SinkKind) (id : Nat) (a : SinkAnswer ε) :
    Option (State α ε) :=
  if operationPhase s kind id = some .awaiting then
    let b := match kind with
      | .write => { s with inFlightWrite := some (id, .queued) }
      | .close => { s with closeState := .inFlight id .queued }
      | .abort => { s with abortInFlight := some (id, .queued) }
    some { b with jobs := s.jobs ++ [⟨kind, id, a⟩] }
  else none

/--
One deterministic administrative stage of the frozen writable algorithms.
The owning census anchors for each branch are recorded in WRITABLE-PG-DEFAULT.
This supports the local candidate observations; no fuel or external choice selects a job.
-/
def tick (s : State α ε) : Option (State α ε) :=
  match s.control with
  | [] =>
      match s.jobs with
      | [] => none
      | job :: jobs => some { s with control := [.react job], jobs := jobs }
  | .awaitSize _ _ :: _ | .awaitSink _ :: _ | .awaitSignal _ _ :: _ => none
  | .returnPromise call id :: tail =>
      some { s with control := tail, trace := s.trace ++ [.returned call id] }
  | .returnUnit call :: tail =>
      some { s with control := tail, trace := s.trace ++ [.controllerReturned call] }
  | .getSize call chunk :: tail =>
      some (match s.algorithms.size with
        | none | some .one => { s with control := .afterSize call chunk sizes.one :: tail }
        | some (.foreign name) =>
            { s with
              control := .awaitSize call chunk :: tail,
              trace := s.trace ++ [.sizeCalled name call chunk] })
  | .afterSize call chunk size :: tail =>
      let rejectType :=
        let r := freshPromise { s with control := tail, nextError := s.nextError + 1 }
          (.rejected (.typeError s.nextError))
        some { r.1 with control := .returnPromise call r.2 :: tail }
      match s.status with
      | .errored reason =>
          let r := freshPromise { s with control := tail } (.rejected reason)
          some { r.1 with control := .returnPromise call r.2 :: tail }
      | .closed => rejectType
      | .erroring reason =>
          if closeQueuedOrInFlight s then rejectType
          else
            let r := freshPromise { s with control := tail } (.rejected reason)
            some { r.1 with control := .returnPromise call r.2 :: tail }
      | .writable =>
          if closeQueuedOrInFlight s then rejectType
          else
            let r := freshPromise { s with control := tail } .pending
            some { r.1 with
              writeRequests := s.writeRequests ++ [r.2],
              control := .enqueueWrite chunk size :: .returnPromise call r.2 :: tail }
  | .enqueueWrite chunk size :: tail =>
      match Data.enqueueValueWithSize sizes s.queue (.chunk chunk) size with
      | .error .rangeError =>
          some { s with
            nextError := s.nextError + 1,
            control := .errorIfNeeded (.rangeError s.nextError) :: tail }
      | .ok queue =>
          let b := { s with queue := queue, control := .advance :: tail }
          some (match s.status with
            | .writable => if closeQueuedOrInFlight s then b
                else updateBackpressure b (getBackpressure b)
            | _ => b)
  | .advance :: tail =>
      match s.inFlightWrite with
      | some _ => some { s with control := tail }
      | none =>
          match s.status with
          | .erroring _ => some { s with control := .finishErroring :: tail }
          | .writable =>
              match s.queue.entries with
              | [] => some { s with control := tail }
              | ⟨.chunk chunk, _⟩ :: _ =>
                  match s.writeRequests with
                  | [] => none
                  | id :: ids =>
                      invokeSink { s with
                        control := tail, writeRequests := ids,
                        inFlightWrite := some (id, .invoking) } (.write id chunk)
              | ⟨.close, _⟩ :: _ =>
                  match s.closeState, Data.dequeueValue sizes s.queue with
                  | .queued id, some (.close, queue) =>
                      if queue.entries = [] then
                        invokeSink { s with
                          control := tail, queue := queue,
                          closeState := .inFlight id .invoking } (.close id)
                      else none
                  | _, _ => none
          | _ => none
  | .beginClose call :: tail =>
      let rejected :=
        let r := freshPromise { s with control := tail, nextError := s.nextError + 1 }
          (.rejected (.typeError s.nextError))
        some { r.1 with control := .returnPromise call r.2 :: tail }
      if closeQueuedOrInFlight s then rejected
      else match s.status with
        | .closed | .errored _ => rejected
        | .writable | .erroring _ =>
            match Data.enqueueValueWithSize sizes s.queue .close sizes.zero with
            | .error _ => none
            | .ok queue =>
                let r := freshPromise { s with control := tail } .pending
                let b := { r.1 with
                  closeState := .queued r.2, queue := queue,
                  control := .advance :: .returnPromise call r.2 :: tail }
                some (match s.status with
                  | .writable => if s.backpressure then settle b s.readyPromise (.ok ()) else b
                  | _ => b)
  | .beginAbort call reason :: tail =>
      match s.status with
      | .closed | .errored _ =>
          let r := freshPromise { s with control := tail } (.fulfilled ())
          some { r.1 with control := .returnPromise call r.2 :: tail }
      | .writable | .erroring _ =>
          match s.signalArgument with
          | none =>
              some { s with
                signalArgument := some reason, control := .awaitSignal call reason :: tail,
                trace := s.trace ++ [.signalCalled call reason] }
          | some _ => some { s with control := .afterSignal call reason :: tail }
  | .afterSignal call reason :: tail =>
      match s.status with
      | .closed | .errored _ =>
          let r := freshPromise { s with control := tail } (.fulfilled ())
          some { r.1 with control := .returnPromise call r.2 :: tail }
      | .writable | .erroring _ =>
          match s.pendingAbort with
          | some (.requested id _) | some (.alreadyErroring id) =>
              some { s with control := .returnPromise call id :: tail }
          | none =>
              let r := freshPromise { s with control := tail } .pending
              some (match s.status with
                | .writable =>
                    { r.1 with
                      pendingAbort := some (.requested r.2 reason),
                      control := .startErroring reason :: .returnPromise call r.2 :: tail }
                | _ =>
                    { r.1 with
                      pendingAbort := some (.alreadyErroring r.2),
                      control := .returnPromise call r.2 :: tail })
  | .errorIfNeeded reason :: tail =>
      some { s with control := match s.status with
        | .writable => .controllerError reason :: tail | _ => tail }
  | .controllerError reason :: tail =>
      some (match s.status with
        | .writable => clearAlgorithms { s with control := .startErroring reason :: tail }
        | _ => { s with control := tail })
  | .startErroring reason :: tail =>
      match s.status with
      | .writable =>
          some (ensureReadyRejected { s with
            status := .erroring reason,
            control := if hasInFlight s then tail else .finishErroring :: tail } reason)
      | _ => none
  | .dealRejection reason :: tail =>
      match s.status with
      | .writable => some { s with control := .startErroring reason :: tail }
      | .erroring _ => some { s with control := .finishErroring :: tail }
      | _ => none
  | .finishErroring :: tail =>
      if hasInFlight s then none
      else match s.status with
        | .erroring stored =>
            let b := s.writeRequests.foldl (fun st id => settle st id (.error stored))
              { s with
                status := .errored stored, queue := Data.Queue.empty sizes,
                writeRequests := [], pendingAbort := none, control := tail }
            match s.pendingAbort with
            | none => some { b with control := .rejectCloseClosed stored :: tail }
            | some (.alreadyErroring id) =>
                some { settle b id (.error stored) with
                  control := .rejectCloseClosed stored :: tail }
            | some (.requested id reason) => invokeSink b (.abort id reason)
        | _ => none
  | .rejectCloseClosed stored :: tail =>
      match s.status, s.closeState with
      | .errored _, .inFlight _ _ => none
      | .errored _, _ =>
          let b := match s.closeState with
            | .queued id => { settle s id (.error stored) with closeState := .none }
            | _ => s
          some (markHandled (settle { b with control := tail }
            b.closedPromise (.error stored)) b.closedPromise)
      | _, _ => none
  | .react job :: tail =>
      if operationPhase s job.kind job.request = some .queued then
        let id := job.request
        match job.kind with
        | .write =>
            match s.status with
            | .writable | .erroring _ =>
                match job.answer with
                | .fulfilled =>
                    match Data.dequeueValue sizes s.queue with
                    | some (.chunk _, queue) =>
                        let b := { settle s id (.ok ()) with
                          inFlightWrite := none, queue := queue, control := .advance :: tail }
                        some (match s.status with
                          | .writable => if closeQueuedOrInFlight s then b
                              else updateBackpressure b (getBackpressure b)
                          | _ => b)
                    | _ => none
                | .rejected reason =>
                    let b := match s.status with | .writable => clearAlgorithms s | _ => s
                    some { settle b id (.error reason) with
                      inFlightWrite := none, control := .dealRejection reason :: tail }
            | _ => none
        | .close =>
            match s.status with
            | .writable | .erroring _ =>
                match job.answer with
                | .fulfilled =>
                    let b := { settle s id (.ok ()) with closeState := .none, control := tail }
                    let c := match s.status, s.pendingAbort with
                      | .erroring _, some (.requested abortId _) => settle b abortId (.ok ())
                      | .erroring _, some (.alreadyErroring abortId) => settle b abortId (.ok ())
                      | _, _ => b
                    some (settle { c with status := .closed, pendingAbort := none }
                      c.closedPromise (.ok ()))
                | .rejected reason =>
                    let b := { settle s id (.error reason) with closeState := .none }
                    let c := match s.pendingAbort with
                      | some (.requested abortId _) | some (.alreadyErroring abortId) =>
                          settle b abortId (.error reason)
                      | none => b
                    some { c with pendingAbort := none, control := .dealRejection reason :: tail }
            | _ => none
        | .abort =>
            match s.status with
            | .errored stored =>
                let result := match job.answer with | .fulfilled => .ok () | .rejected e => .error e
                some { settle s id result with
                  abortInFlight := none, control := .rejectCloseClosed stored :: tail }
            | _ => none
      else none

end Whatwg.Streams.Writable
