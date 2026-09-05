import Std

/-!
# Finite default-readable mutants

Independent breaker models for WS-READ-CE-001 through WS-READ-CE-017.
These finite witnesses distinguish the named mutations. They do not prove production transitions,
host behavior, or coverage. The matching quantified production laws are in DefaultContract.lean.
Only kernel reduction is used. No production imports are required to establish an intended red
  phase.
-/

set_option autoImplicit false

namespace WhatwgTest.Streams.Counterexamples.Readable.Breaker

inductive Event where
  | size
  | pull
  | closed
  | rejected (reason : Nat)
  | desiredSizeRead (value : Nat)
  | chunk (value : Nat)
  deriving DecidableEq, Repr

inductive Status where
  | readable
  | closed
  | errored (reason : Nat)
  deriving DecidableEq, Repr

/-- Correct branch selection bypasses size when a read request is pending. -/
def directDelivery (pending : Bool) : List Event :=
  if pending then [.chunk 7] else [.size]

/-- Mutant evaluates size on every enqueue before choosing delivery. -/
def sizeFirst (pending : Bool) : List Event :=
  .size :: if pending then [.chunk 7] else []

/-- WS-READ-CE-001, M2 plus foreign-call trace. -/
theorem ce001_pending_skips_size : directDelivery true ≠ sizeFirst true := by decide +kernel

/-- A queue uses append for successful sized enqueue. -/
def queueAppend (queue : List Nat) (chunk : Nat) := queue ++ [chunk]

/-- Mutant adds chunks at the head. -/
def queuePrepend (queue : List Nat) (chunk : Nat) := chunk :: queue

/-- WS-READ-CE-002, M1. Equal lengths/totals do not establish FIFO. -/
theorem ce002_queue_is_not_stack :
    (queueAppend [1] 2).head? ≠ (queuePrepend [1] 2).head? := by decide +kernel

/-- A nonempty queue keeps the stream readable after a close request. -/
def requestClose (queue : List Nat) : Status :=
  if queue.isEmpty then .closed else .readable

/-- Mutant closes immediately, making the queued data unreadable. -/
def immediateClose (_queue : List Nat) : Status := .closed

/-- WS-READ-CE-003, terminal component of M1. -/
theorem ce003_close_must_drain : requestClose [1] ≠ immediateClose [1] := by decide +kernel

/-- The final queued read closes the stream before its chunk steps. -/
def lastRead (chunk : Nat) : List Event := [.closed, .chunk chunk]

/-- Mutant places chunk steps before ReadableStreamClose. -/
def lastReadChunkFirst (chunk : Nat) : List Event := [.chunk chunk, .closed]

/-- WS-READ-CE-004, M2. -/
theorem ce004_closed_before_last_chunk : lastRead 1 ≠ lastReadChunkFirst 1 := by decide +kernel

/-- Demand is present from a pending read even when desired size is zero. -/
def demand (pending positiveDesired : Bool) := pending || positiveDesired

/-- Mutant considers only the high-water-mark calculation. -/
def desiredOnly (_pending positiveDesired : Bool) := positiveDesired

/-- WS-READ-CE-005, pull invocation observation under M2's configuration. -/
theorem ce005_zero_hwm_pending_read : demand true false ≠ desiredOnly true false := by
  decide +kernel

/-- The result pair is pullAgain and the new invocation count. -/
def callWhilePulling (pulling : Bool) : Bool × Nat :=
  if pulling then (true, 0) else (false, 1)

/-- Mutant starts a second pull instead of remembering demand. -/
def concurrentPull (_pulling : Bool) : Bool × Nat := (false, 1)

/-- WS-READ-CE-006, pull scheduling state. -/
theorem ce006_pull_again_coalesces :
    callWhilePulling true ≠ concurrentPull true := by decide +kernel

/-- Fulfillment rechecks current demand before re-invocation. -/
def fulfillPull (pullAgain currentDemand : Bool) : Nat :=
  if pullAgain && currentDemand then 1 else 0

/-- Mutant interprets pullAgain as unconditional permission to invoke. -/
def unconditionalRepull (pullAgain _currentDemand : Bool) : Nat :=
  if pullAgain then 1 else 0

/-- WS-READ-CE-007, the stream may have closed while a pull was outstanding. -/
theorem ce007_fulfillment_rechecks_demand :
    fulfillPull true false ≠ unconditionalRepull true false := by decide +kernel

/-- Nested synchronous size calls resume the newest frame first. -/
def nestedSizeReturns (outer inner : Nat) := [inner, outer]

/-- Mutant treats pending size invocations as a FIFO queue. -/
def fifoSizeReturns (outer inner : Nat) := [outer, inner]

/-- WS-READ-CE-008, M1; pinned reentrant-strategies enqueues b during size(a). -/
theorem ce008_nested_size_is_lifo : nestedSizeReturns 1 2 ≠ fifoSizeReturns 1 2 := by decide +kernel

/-- The admitted continuation appends even after reentrant close/error. -/
def resumeAdmitted (queue : List Nat) (chunk : Nat) (_status : Status) := queue ++ [chunk]

/-- Mutant incorrectly repeats CanCloseOrEnqueue after returning from size. -/
def recheckAfterSize (queue : List Nat) (chunk : Nat) (status : Status) :=
  match status with
  | .readable => queue ++ [chunk]
  | _ => queue

/-- WS-READ-CE-009, structural queue observation; M1 alone hides the stranded chunk. -/
theorem ce009_closed_can_retain_chunk :
    resumeAdmitted [] 1 .closed ≠ recheckAfterSize [] 1 .closed := by decide +kernel

/-- A reentrant read leaves a pending request; the admitted outer chunk queues.
The next enqueue delivers b directly, then the following read dequeues a. -/
def readDuringSize (outer next : Nat) : List Nat := [next, outer]

/-- Mutant rechecks for a pending request when the outer size call returns. -/
def recheckReadAfterSize (outer next : Nat) : List Nat := [outer, next]

/-- WS-READ-CE-010, M1, matching the pinned read-inside-size test. -/
theorem ce010_read_during_size : readDuringSize 1 2 ≠ recheckReadAfterSize 1 2 := by decide +kernel

/-- ControllerError is inert after the callback already errored the stream.
The pair is the stored stream error and the enclosing enqueue's thrown reason. -/
def errorThenThrow (stored thrown : Nat) : Status × Nat := (.errored stored, thrown)

/-- Mutant replaces the stored stream error with the later exception. -/
def overwriteStoredError (_stored thrown : Nat) : Status × Nat := (.errored thrown, thrown)

/-- WS-READ-CE-011, M1 terminal reason plus synchronous completion reason. -/
theorem ce011_first_error_survives : errorThenThrow 1 2 ≠ overwriteStoredError 1 2 := by
  decide +kernel

/-- Accepting a foreign fulfillment adds a reaction job; it does not execute it. -/
def acceptAnswer (jobs : List Nat) (answer : Nat) : List Nat × List Nat :=
  (jobs ++ [answer], [])

/-- Mutant executes the answer immediately and bypasses older queued jobs. -/
def executeAnswerImmediately (jobs : List Nat) (answer : Nat) : List Nat × List Nat :=
  (jobs, [answer])

/-- A synchronous size frame prevents a promise reaction from interleaving. -/
def runJob (frames jobs : List Nat) : Option Nat :=
  if frames.isEmpty then jobs.head? else none

/-- Mutant runs a reaction while a size callback is still on the stack. -/
def runJobInsideSize (_frames jobs : List Nat) : Option Nat := jobs.head?

/-- WS-READ-CE-012, M2 reaction ordering and run-to-completion boundary. -/
theorem ce012_answers_are_queued :
    acceptAnswer [1] 2 ≠ executeAnswerImmediately [1] 2 ∧
      runJob [7] [1, 2] ≠ runJobInsideSize [7] [1, 2] := by decide +kernel

/-- Pull synchronously errors the stream before the saved queued-read continuation runs. -/
def readAcrossPullError (chunk reason : Nat) : List Event :=
  [.pull, .rejected reason, .chunk chunk]

/-- Mutant settles the chunk before allowing the pull callback to reenter. -/
def atomicReadAcrossPull (chunk reason : Nat) : List Event :=
  [.pull, .chunk chunk, .rejected reason]

/-- WS-READ-CE-013, settlement-order component of M2. -/
theorem ce013_pull_error_precedes_chunk :
    readAcrossPullError 1 7 ≠ atomicReadAcrossPull 1 7 := by decide +kernel

/-- A source callback can enqueue after the outer read dequeues, before its return. -/
def queueAfterReentrantPull (chunk : Nat) : List Nat := [chunk]

/-- Mutant promotes the intermediate empty queue to an unconditional postcondition. -/
def queueAfterAtomicRead (_chunk : Nat) : List Nat := []

/-- WS-READ-CE-014, queue slot and the following read's M1 result. -/
theorem ce014_pull_can_change_queue :
    queueAfterReentrantPull 2 ≠ queueAfterAtomicRead 2 := by decide +kernel

/-- IDs are allocated before pull: a nested later read can settle before the outer read. -/
def nestedReadOrder (outer inner : Nat) : List (Nat × Nat) := [(1, inner), (0, outer)]

/-- Mutant settles the outer read atomically before source callback reentrancy. -/
def atomicReadOrder (outer inner : Nat) : List (Nat × Nat) := [(0, outer), (1, inner)]

/-- WS-READ-CE-015, both M1 chunk order and M2 promise identity/order. -/
theorem ce015_nested_read_overtakes : nestedReadOrder 1 2 ≠ atomicReadOrder 1 2 := by decide +kernel

/-- Inner/outer invalid sizes allocate distinct IDs; the inner error remains stored.
The triple is stored identity, enclosing thrown identity, and next unused identity. -/
def freshNestedErrors (next : Nat) : Nat × Nat × Nat := (next, next + 1, next + 2)

/-- Mutant identifies every model-generated RangeError with one tag. -/
def collapsedNestedErrors (next : Nat) : Nat × Nat × Nat := (next, next, next)

/-- WS-READ-CE-016, exact error reasons in M1 and synchronous completion observations. -/
theorem ce016_generated_errors_are_distinct :
    freshNestedErrors 0 ≠ collapsedNestedErrors 0 ∧
      (freshNestedErrors 0).1 ≠ (freshNestedErrors 0).2.1 := by decide +kernel

/-- A desiredSize query contributes an observation without changing M1. -/
def observedQuery (trace : List Event) (value : Nat) := trace ++ [.desiredSizeRead value]

/-- Mutant defines M2 as settlements alone, forgetting an observable desiredSize query. -/
def invisibleQuery (trace : List Event) (_value : Nat) := trace

/-- WS-READ-CE-017, DB-04's M2 query observation. -/
theorem ce017_query_is_visible : observedQuery [] 0 ≠ invisibleQuery [] 0 := by decide +kernel

#print axioms ce001_pending_skips_size
#print axioms ce002_queue_is_not_stack
#print axioms ce003_close_must_drain
#print axioms ce004_closed_before_last_chunk
#print axioms ce005_zero_hwm_pending_read
#print axioms ce006_pull_again_coalesces
#print axioms ce007_fulfillment_rechecks_demand
#print axioms ce008_nested_size_is_lifo
#print axioms ce009_closed_can_retain_chunk
#print axioms ce010_read_during_size
#print axioms ce011_first_error_survives
#print axioms ce012_answers_are_queued
#print axioms ce013_pull_error_precedes_chunk
#print axioms ce014_pull_can_change_queue
#print axioms ce015_nested_read_overtakes
#print axioms ce016_generated_errors_are_distinct
#print axioms ce017_query_is_visible

end WhatwgTest.Streams.Counterexamples.Readable.Breaker
