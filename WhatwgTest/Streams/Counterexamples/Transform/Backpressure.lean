import Whatwg.Streams.Readable.State

/-!+# Independent finite transform protocol mutants

These are breaker-authored executions of small, explicitly named projections.
They are not executions of the production transform calculus, P4/P5, WPT, or a host.
`test/counterexamples/transform/ATTACKS.md` records each tape and observation scope.
No snapshot equality is described as a complete stream execution.
-/

namespace WhatwgTest.Streams.Counterexamples.Transform.Breaker

inductive Outcome where
  | pending
  | fulfilled
  | rejected (reason : Nat)
  deriving DecidableEq, Repr

inductive WritableStatus where
  | writable
  | erroring (reason : Nat)
  deriving DecidableEq, Repr

inductive Event where
  | resolved (promise : Nat)
  | allocated (promise : Nat)
  | pullReturned (promise : Nat)
  | writeWaited (promise : Nat)
  | writeReactionQueued
  | transformCalled
  | transformReturned
  | transformReactionQueued
  | sinkFulfilled
  | sinkRejected (reason : Nat)
  | chunk (value : Nat)
  | closed
  deriving DecidableEq, Repr

structure Pressure where
  backpressure : Bool
  current : Nat
  next : Nat
  cells : List (Nat × Outcome)
  waitingWrite : Option Nat
  queuedWrite : Bool
  writable : WritableStatus
  sink : Outcome
  trace : List Event
  deriving DecidableEq, Repr

def initial : Pressure :=
  ⟨true, 4, 5, [(4, .pending)], none, false, .writable, .pending, []⟩

def resolveCurrent (s : Pressure) : Pressure :=
  { s with
    cells := s.cells.map (fun p ↦ if p.1 == s.current then (p.1, .fulfilled) else p)
    trace := s.trace ++ [.resolved s.current] }

def change (s : Pressure) (value : Bool) : Pressure :=
  if s.backpressure == value then s else
    let t := resolveCurrent s
    let wake := s.waitingWrite == some s.current
    { t with
      backpressure := value
      current := s.next
      next := s.next + 1
      cells := t.cells ++ [(s.next, .pending)]
      queuedWrite := s.queuedWrite || wake
      waitingWrite := if wake then none else s.waitingWrite
      trace := t.trace ++ (if wake then [.writeReactionQueued] else []) ++ [.allocated s.next] }

def sourcePull (s : Pressure) : Pressure :=
  let t := change s false
  { t with trace := t.trace ++ [.pullReturned t.current] }

def sourcePullReturnsOld (s : Pressure) : Pressure :=
  let t := change s false
  { t with trace := t.trace ++ [.pullReturned s.current] }

def waitWrite (s : Pressure) : Pressure :=
  { s with waitingWrite := some s.current, trace := s.trace ++ [.writeWaited s.current] }

def retargetWaiter (s : Pressure) : Pressure :=
  let t := change s false
  { t with waitingWrite := some t.current, queuedWrite := false }

def runWriteReaction (s : Pressure) : Pressure :=
  if !s.queuedWrite then s else
    match s.writable with
    | .writable =>
        { s with queuedWrite := false, trace := s.trace ++ [.transformCalled] }
    | .erroring e =>
        { s with
          queuedWrite := false, sink := .rejected e, trace := s.trace ++ [.sinkRejected e] }

def runWithoutRecheck (s : Pressure) : Pressure :=
  if !s.queuedWrite then s else
    { s with queuedWrite := false, trace := s.trace ++ [.transformCalled] }

def unblockFulfillsSink (s : Pressure) : Pressure :=
  let t := sourcePull s
  { t with sink := .fulfilled, trace := t.trace ++ [.sinkFulfilled] }

/-- WS-TRANS-CE-001: one actual change resolves the old cell and retains a new pending cell. -/
theorem ce001_old_resolved_new_pending :
    (change initial false).cells = [(4, .fulfilled), (5, .pending)] ∧
    (change initial false).current = 5 ∧ (change initial false).next = 6 := by
  decide

/-- WS-TRANS-CE-002: the source-pull return records the new identity, unlike the mutant. -/
theorem ce002_source_pull_returns_new :
    (sourcePull initial).trace = [.resolved 4, .allocated 5, .pullReturned 5] ∧
    (sourcePull initial).trace ≠ (sourcePullReturnsOld initial).trace := by
  decide

/-- WS-TRANS-CE-003: wait then change queues the old subscriber; retargeting loses its wakeup. -/
theorem ce003_write_captures_old :
    (sourcePull (waitWrite initial)).queuedWrite = true ∧
    (retargetWaiter (waitWrite initial)).queuedWrite = false ∧
    (sourcePull (waitWrite initial)).waitingWrite = none := by
  decide

/-- WS-TRANS-CE-004: wait then pull leaves sink pending; it only queues the write continuation. -/
theorem ce004_unblock_does_not_fulfill_sink :
    (sourcePull (waitWrite initial)).sink = .pending ∧
    (sourcePull (waitWrite initial)).queuedWrite = true ∧
    (unblockFulfillsSink (waitWrite initial)).sink = .fulfilled := by
  decide

/-- WS-TRANS-CE-012: resolving the old cell queues its subscriber before allocating the new one. -/
theorem ce012_resolution_queues_before_allocation :
    (sourcePull (waitWrite initial)).trace =
      [.writeWaited 4, .resolved 4, .writeReactionQueued, .allocated 5, .pullReturned 5] := by
  decide

/-- WS-TRANS-CE-005: an error between waiting and the queued reaction prevents transformation. -/
theorem ce005_reaction_rechecks_erroring :
    let waited := waitWrite initial
    let errored := { waited with writable := .erroring 17 }
    let unblocked := sourcePull errored
    (runWriteReaction unblocked).sink = .rejected 17 ∧
    Event.transformCalled ∉ (runWriteReaction unblocked).trace ∧
    Event.transformCalled ∈ (runWithoutRecheck unblocked).trace := by
  decide

structure Callback where
  invoking : Bool
  awaiting : Bool
  queued : Bool
  trace : List Event
  deriving DecidableEq, Repr

def enterCallback : Callback := ⟨true, false, false, [.transformCalled]⟩

def returnPending (s : Callback) : Callback :=
  { s with invoking := false, awaiting := true, trace := s.trace ++ [.transformReturned] }

def answerCallback (s : Callback) : Option Callback :=
  if s.awaiting then
    some { s with
      awaiting := false, queued := true, trace := s.trace ++ [.transformReactionQueued] }
  else none

def returnSettled (s : Callback) : Callback :=
  { s with
    invoking := false, queued := true
    trace := s.trace ++ [.transformReturned, .transformReactionQueued] }

def attachBeforeReturn (s : Callback) : Callback :=
  { s with
    invoking := false, queued := true
    trace := s.trace ++ [.transformReactionQueued, .transformReturned] }

structure CallbackOwner where
  algorithms : Bool
  call : Callback
  deriving DecidableEq, Repr

def clearOwner (s : CallbackOwner) : CallbackOwner := { s with algorithms := false }

def returnOwner (s : CallbackOwner) : Option CallbackOwner :=
  if s.call.invoking then some { s with call := returnPending s.call } else none

def returnOwnerChecksAlgorithms (s : CallbackOwner) : Option CallbackOwner :=
  if s.algorithms then returnOwner s else none

/-- WS-TRANS-CE-013: clearing installed algorithms leaves the active callback return live. -/
theorem ce013_return_survives_clear :
    let cleared := clearOwner ⟨true, enterCallback⟩
    returnOwner cleared = some ⟨false, returnPending enterCallback⟩ ∧
    returnOwnerChecksAlgorithms cleared = none := by
  decide

/-- WS-TRANS-CE-006: an eventual answer is not admissible until the pending callback returns. -/
theorem ce006_return_precedes_answer :
    answerCallback enterCallback = none ∧
    answerCallback (returnPending enterCallback) =
      some ⟨false, false, true,
        [.transformCalled, .transformReturned, .transformReactionQueued]⟩ := by
  decide

/-- WS-TRANS-CE-007: already-settled return still attaches after the synchronous return point. -/
theorem ce007_return_precedes_attachment :
    (returnSettled enterCallback).trace =
      [.transformCalled, .transformReturned, .transformReactionQueued] ∧
    (returnSettled enterCallback).trace ≠ (attachBeforeReturn enterCallback).trace := by
  decide

def runCallbackJob (s : Callback) : Option Callback :=
  if s.invoking || !s.queued then none
  else some { s with queued := false, trace := s.trace ++ [.sinkFulfilled] }

/-- WS-TRANS-CE-008: a queued reaction remains blocked by a live synchronous callback frame. -/
theorem ce008_no_job_inside_callback :
    runCallbackJob { enterCallback with queued := true } = none ∧
    runCallbackJob (returnSettled enterCallback) =
      some ⟨false, false, false,
        [.transformCalled, .transformReturned, .transformReactionQueued, .sinkFulfilled]⟩ := by
  decide

structure Output where
  queue : List Nat
  pendingReads : Nat
  highWaterMark : Nat
  closing : Bool
  trace : List Event
  deriving DecidableEq, Repr

def outputInitial : Output := ⟨[], 0, 0, false, []⟩

def outputRead (s : Output) : Output :=
  match s.queue with
  | [] => if s.closing then { s with trace := s.trace ++ [.closed] }
      else { s with pendingReads := s.pendingReads + 1 }
  | x :: xs => { s with
      queue := xs
      trace := s.trace ++ (if s.closing && xs.isEmpty then [.closed] else []) ++ [.chunk x] }

def outputEnqueue (s : Output) (x : Nat) : Output :=
  if s.pendingReads > 0 then
    { s with pendingReads := s.pendingReads - 1, trace := s.trace ++ [.chunk x] }
  else { s with queue := s.queue ++ [x] }

def hasPressure (s : Output) : Bool :=
  !(s.pendingReads > 0 || s.queue.length < s.highWaterMark)

def pressureFromSizeOnly (s : Output) : Bool := !(s.queue.length < s.highWaterMark)

def successfulReadableStart (s : Pressure) (out : Output) : Pressure :=
  if hasPressure out then s else sourcePull s

def beginProjectedWrite (s : Pressure) : Pressure :=
  if s.backpressure then waitWrite s
  else { s with trace := s.trace ++ [.transformCalled] }

/-- WS-TRANS-CE-014: positive readable capacity starts native pull before the next writer call. -/
theorem ce014_start_services_positive_capacity :
    let capacity := { outputInitial with highWaterMark := 1 }
    let started := successfulReadableStart initial capacity
    started.backpressure = false ∧
    Event.transformCalled ∈ (beginProjectedWrite started).trace ∧
    Event.transformCalled ∉ (beginProjectedWrite initial).trace ∧
    (beginProjectedWrite initial).waitingWrite = some 4 := by
  decide

/-- WS-TRANS-CE-009: a read at zero HWM removes pressure until its delivery consumes demand. -/
theorem ce009_zero_hwm_pending_read :
    let demanded := outputRead outputInitial
    hasPressure demanded = false ∧ pressureFromSizeOnly demanded = true ∧
    hasPressure (outputEnqueue demanded 31) = true ∧
    (outputEnqueue demanded 31).trace = [.chunk 31] := by
  decide

def outputTerminate (s : Output) : Output := { s with closing := true }

def terminateDropsQueue (s : Output) : Output := { s with closing := true, queue := [] }

/-- WS-TRANS-CE-010: enqueue, terminate, read drains the chunk, with close before final delivery. -/
theorem ce010_termination_drains :
    let queued := outputEnqueue outputInitial 29
    (outputRead (outputTerminate queued)).trace = [.closed, .chunk 29] ∧
    (outputRead (terminateDropsQueue queued)).trace = [.closed] := by
  decide

/-- WS-TRANS-CE-011: two callback enqueues followed by reads retain two distinct FIFO outputs. -/
theorem ce011_multiple_outputs :
    let transformed := outputEnqueue (outputEnqueue outputInitial 12) 34
    (outputRead (outputRead transformed)).trace = [.chunk 12, .chunk 34] ∧
    outputInitial.queue = [] := by
  decide

#print axioms ce001_old_resolved_new_pending
#print axioms ce002_source_pull_returns_new
#print axioms ce003_write_captures_old
#print axioms ce004_unblock_does_not_fulfill_sink
#print axioms ce005_reaction_rechecks_erroring
#print axioms ce006_return_precedes_answer
#print axioms ce007_return_precedes_attachment
#print axioms ce008_no_job_inside_callback
#print axioms ce009_zero_hwm_pending_read
#print axioms ce010_termination_drains
#print axioms ce011_multiple_outputs
#print axioms ce012_resolution_queues_before_allocation
#print axioms ce013_return_survives_clear
#print axioms ce014_start_services_positive_capacity

end WhatwgTest.Streams.Counterexamples.Transform.Breaker
