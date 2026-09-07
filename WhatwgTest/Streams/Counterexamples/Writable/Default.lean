import Whatwg.Streams

/-!
P5a retained finite mutants. These are independent test fixtures, not a second stream semantics.
Each theorem refutes a concrete competing stage/identity rule in WRITABLE-PG-DEFAULT.
No theorem here establishes the full writable transition relation or a host correspondence.
-/

set_option autoImplicit false

namespace WhatwgTest.Streams.Counterexamples.Writable.Default

abbrev Reason := Whatwg.Streams.Boundary.Exception Nat
abbrev Outcome := Whatwg.Streams.Readable.PromiseState Unit Nat
abbrev Size := Whatwg.Streams.Data.DyadicSize

private def sizes := Whatwg.Streams.Data.DyadicSize.sizes

inductive Phase
  | writable
  | erroring (reason : Reason)
  | errored (reason : Reason)
  | closed
deriving DecidableEq

inductive WriteChoice
  | enqueue
  | reject (reason : Reason)
deriving DecidableEq

-- The size callback has already returned; these are its reentrant resulting slots.
private def afterSize (phase : Phase) (closing : Bool) (fresh : Nat) : WriteChoice :=
  match phase with
  | .errored e => .reject e
  | .closed => .reject (.typeError fresh)
  | .erroring e => if closing then .reject (.typeError fresh) else .reject e
  | .writable => if closing then .reject (.typeError fresh) else .enqueue

private def checkOnlyBeforeSize (_after : Phase) (_closing : Bool) : WriteChoice :=
  .enqueue

/-- WS-WRITE-CE-001: a size callback closes; admission must use its returned state. -/
theorem ce001_reentrant_size_close :
    afterSize .writable true 9 ≠ checkOnlyBeforeSize .writable true := by
  decide +kernel

-- GetChunkSize swallows the abrupt result after ErrorIfNeeded; WriterWrite checks slots.
private def returnThrownSize (_phase : Phase) (_closing : Bool) (thrown : Reason) : WriteChoice :=
  .reject thrown

/-- WS-WRITE-CE-002: an existing stored error wins over a later thrown size reason. -/
theorem ce002_thrown_size_existing_error :
    afterSize (.errored (.foreign 1)) false 9 ≠
      returnThrownSize (.errored (.foreign 1)) false (.foreign 2) := by
  decide +kernel

/-- WS-WRITE-CE-003: closing is checked before erroring after abrupt size completion. -/
theorem ce003_closing_before_erroring :
    afterSize (.erroring (.foreign 2)) true 9 ≠
      returnThrownSize (.erroring (.foreign 2)) true (.foreign 2) := by
  decide +kernel

private def lookup (cells : List (Nat × Outcome)) (id : Nat) : Option Outcome :=
  (cells.find? (fun p => p.1 == id)).map Prod.snd

private def replaceCell (cells : List (Nat × Outcome)) (id : Nat) (a : Outcome) :=
  cells.map (fun p => if p.1 == id then (id, a) else p)

-- false -> true allocates a new ready promise. The mutant overwrites the old cell.
private def newReady := ([(0, (.fulfilled () : Outcome)), (2, (.pending : Outcome))], 2)
private def overwriteReady := (replaceCell [(0, (.fulfilled () : Outcome))] 0 .pending, 0)

/-- WS-WRITE-CE-004: a retained old ready reference remains fulfilled. -/
theorem ce004_ready_identity :
    (lookup newReady.1 0, newReady.2) ≠
      (lookup overwriteReady.1 0, overwriteReady.2) := by
  decide +kernel

private def closeReady (backpressure : Bool) (ready : Outcome) : Bool × Outcome :=
  (backpressure, if backpressure then .fulfilled () else ready)

private def pendingReady (a : Outcome) : Bool :=
  match a with | .pending => true | _ => false

/-- WS-WRITE-CE-005: ready-pending iff backpressure fails after admitted close. -/
theorem ce005_close_keeps_backpressure :
    (closeReady true .pending).1 = true ∧
      pendingReady (closeReady true .pending).2 = false := by
  decide +kernel

private def oneChunk : Whatwg.Streams.Data.Queue Nat Size :=
  ⟨[⟨7, sizes.one⟩], sizes.one⟩

private def dequeueAtInvocation :=
  (Whatwg.Streams.Data.dequeueValue sizes oneChunk).map Prod.snd

/-- WS-WRITE-CE-006: ProcessWrite cannot dequeue before the sink answer job. -/
theorem ce006_inflight_queue_retained :
    some oneChunk ≠ dequeueAtInvocation := by
  decide +kernel

inductive Settlement
  | fulfilled (id : Nat)
  | rejected (id : Nat) (reason : Reason)
deriving DecidableEq

private def finishWriteOrder (write ready : Nat) :=
  [Settlement.fulfilled write, .fulfilled ready]

private def backpressureFirst (write ready : Nat) :=
  [Settlement.fulfilled ready, .fulfilled write]

/-- WS-WRITE-CE-007: the write promise settles before ready from queue drainage. -/
theorem ce007_write_before_ready :
    finishWriteOrder 2 3 ≠ backpressureFirst 2 3 := by
  decide +kernel

inductive CallbackPoint
  | entering
  | returned
deriving DecidableEq

private def closeAlgorithmsPresent : CallbackPoint → Bool
  | .entering => true
  | .returned => false

private def clearBeforeCallback (_ : CallbackPoint) := false

/-- WS-WRITE-CE-008: close callback reentrancy precedes algorithm clearing. -/
theorem ce008_close_clear_after_return :
    closeAlgorithmsPresent .entering ≠ clearBeforeCallback .entering := by
  decide +kernel

-- Pair = (pendingAbort still stored, algorithms still present) at sink.abort entry.
private def abortEntry := (false, true)
private def keepPendingUntilAbortReturn := (true, true)
private def clearDuringFinishErroring := (false, false)

/-- WS-WRITE-CE-009: pending abort is removed before callback; algorithms survive until return. -/
theorem ce009_abort_entry_slots :
    abortEntry ≠ keepPendingUntilAbortReturn ∧ abortEntry ≠ clearDuringFinishErroring := by
  decide +kernel

private def rejectInflight (stored incoming : Reason) :=
  (stored, [Settlement.rejected 2 incoming])

private def replaceStoredError (_stored incoming : Reason) :=
  (incoming, [Settlement.rejected 2 incoming])

/-- WS-WRITE-CE-010: an in-flight rejection does not replace an earlier stream error. -/
theorem ce010_first_stored_error :
    rejectInflight (.foreign 1) (.foreign 2) ≠
      replaceStoredError (.foreign 1) (.foreign 2) := by
  decide +kernel

private def finishClose :=
  (Phase.closed, (.rejected (.foreign 1) : Outcome),
    [Settlement.fulfilled 3, .fulfilled 4, .fulfilled 1])

private def finishErrorDespiteClose :=
  (Phase.errored (.foreign 1), (.rejected (.foreign 1) : Outcome),
    [Settlement.rejected 4 (.foreign 1), .fulfilled 3, .rejected 1 (.foreign 1)])

/-- WS-WRITE-CE-011: successful in-flight close overrides erroring, settles close/abort/closed. -/
theorem ce011_close_wins_erroring :
    finishClose ≠ finishErrorDespiteClose ∧
      finishClose.2.1 = (.rejected (.foreign 1) : Outcome) := by
  decide +kernel

-- (returned promise identity, resulting outcome); terminal check precedes alias reuse.
private def afterSignal (terminal : Bool) (pending : Option Nat) (fresh : Nat) :=
  if terminal then (fresh, (.fulfilled () : Outcome))
  else match pending with
    | some id => (id, (.pending : Outcome))
    | none => (fresh, (.pending : Outcome))

private def skipTerminalRecheck (_terminal : Bool) (pending : Option Nat) (fresh : Nat) :=
  match pending with
  | some id => (id, (.pending : Outcome))
  | none => (fresh, (.pending : Outcome))

/-- WS-WRITE-CE-012: nested abort can make terminal state, so the outer gets a fresh fulfillment. -/
theorem ce012_signal_terminal_recheck :
    afterSignal true none 5 ≠ skipTerminalRecheck true none 5 := by
  decide +kernel

private def signalOnce (first : Option Reason) (argument : Reason) :=
  match first with
  | none => (some argument, true)
  | some prior => (some prior, false)

private def resignal (_first : Option Reason) (argument : Reason) := (some argument, true)

/-- WS-WRITE-CE-013: nested abort reuses the first signal and the existing pending identity. -/
theorem ce013_nested_abort_identity :
    signalOnce (some (.foreign 1)) (.foreign 2) ≠
      resignal (some (.foreign 1)) (.foreign 2) ∧
    afterSignal false (some 4) 5 = (4, (.pending : Outcome)) := by
  decide +kernel

inductive Item
  | chunk (value : Nat)
  | close
deriving DecidableEq

private def closeSentinel (weight : Size) :=
  match Whatwg.Streams.Data.enqueueValueWithSize sizes
      (Whatwg.Streams.Data.Queue.empty sizes) Item.close weight with
  | .ok queue => some queue.totalSize
  | .error _ => none

/-- WS-WRITE-CE-014: a count-sized close sentinel incorrectly changes queueTotalSize. -/
theorem ce014_zero_size_close :
    closeSentinel sizes.zero ≠ closeSentinel sizes.one := by
  decide +kernel

inductive Flight
  | invoking
  | awaiting
  | queued
deriving DecidableEq

private def admitAnswer (phase : Flight) : Bool :=
  match phase with | .awaiting => true | _ => false

private def admitAnyInflight (_ : Flight) := true

/-- WS-WRITE-CE-015: callback invocation/return and promise settlement cannot be collapsed. -/
theorem ce015_answer_admission :
    admitAnswer .invoking ≠ admitAnyInflight .invoking ∧
    admitAnswer .queued ≠ admitAnyInflight .queued := by
  decide +kernel

private def runJob (liveCallback : Bool) (jobs : List Nat) :=
  if liveCallback then none else jobs.head?

private def runThroughCallback (_liveCallback : Bool) (jobs : List Nat) := jobs.head?

/-- WS-WRITE-CE-016: an attached reaction waits for the synchronous call stack to unwind. -/
theorem ce016_jobs_wait_for_callback :
    runJob true [0, 1] ≠ runThroughCallback true [0, 1] := by
  decide +kernel

#print axioms ce001_reentrant_size_close
#print axioms ce002_thrown_size_existing_error
#print axioms ce003_closing_before_erroring
#print axioms ce004_ready_identity
#print axioms ce005_close_keeps_backpressure
#print axioms ce006_inflight_queue_retained
#print axioms ce007_write_before_ready
#print axioms ce008_close_clear_after_return
#print axioms ce009_abort_entry_slots
#print axioms ce010_first_stored_error
#print axioms ce011_close_wins_erroring
#print axioms ce012_signal_terminal_recheck
#print axioms ce013_nested_abort_identity
#print axioms ce014_zero_size_close
#print axioms ce015_answer_admission
#print axioms ce016_jobs_wait_for_callback

end WhatwgTest.Streams.Counterexamples.Writable.Default
