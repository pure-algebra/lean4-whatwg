import Whatwg.Streams.Readable.Laws

/-!
# Quantified default-readable regressions

Owner: READABLE-PG-DEFAULT, laws and counterexamples edges. These are production
theorems under the local M1/M2 views, with arbitrary chunks and foreign reasons.
The independent finite mutant witnesses remain in WhatwgTest.
-/

namespace Whatwg.Streams.Readable

set_option exponentiation.threshold 2048

attribute [local simp] initial sizes sizePositive beginEnqueue finishEnqueue resumeSize
  returnPull read close streamClose error shouldCallPull canCloseOrEnqueue callPullIfNeeded
  callPullIfNeededWith continuePull observeM1 settlementTrace chunksOfSettlements
  Data.Queue.empty Data.enqueueValueWithSize Data.dequeueValue Data.resetQueue
  Data.SizeClass.isNonNegativeNumber Data.SizeClass.isPositiveInfinity
  Data.SizeClass.clampNonNegative Data.DyadicSize.sizes Data.DyadicSize.oneUnits
  Data.DyadicSize.isNaN Data.DyadicSize.isNegative Data.DyadicSize.isInfinite
  Data.DyadicSize.add Data.DyadicSize.sub Data.DyadicSize.neg
  Boundary.Exception.ofRangeError

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-008.
Nested size continuations resume in LIFO order.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_enqueue_lifo :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : State α ε,
      resumeSize (beginEnqueue
        (beginEnqueue s a) b)
        (.value sizes.one) = some t ∧
      resumeSize t (.value sizes.one) = some u ∧
      u.queue.entries.map Data.QueueEntry.value = [b, a] ∧ u.frames = [] := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-009.
An admitted size continuation can append after close.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_close_keeps_chunk :
  ∀ {α ε : Type} (a : α),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : State α ε, resumeSize
      (close (beginEnqueue s a))
      (.value sizes.one) = some t ∧
      t.status = .closed ∧ t.queue.entries.map Data.QueueEntry.value = [a] ∧
      observeM1 (read t) = ([], .closed) := by
  intros
  simp (config := { zetaDelta := true })
  intro event
  constructor <;> rintro rfl <;> rfl

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-010.
A read during sizing does not change the admitted enqueue branch.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_read_does_not_recheck :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : State α ε,
      returnPull (read
        (beginEnqueue s a)) .pending = some t ∧
      resumeSize t (.value sizes.one) = some u ∧
      u.readRequests = [0] ∧ u.queue.entries.map Data.QueueEntry.value = [a] ∧
      observeM1 (read
        (beginEnqueue u b)) = ([b, a], .readable) := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-009.
An admitted size continuation can append after error.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_error_keeps_chunk :
  ∀ {α ε : Type} (a : α) (e : ε),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : State α ε, resumeSize
      (error (beginEnqueue s a) (.foreign e))
      (.value sizes.one) = some t ∧
      t.status = .errored (.foreign e) ∧ t.queue.entries.map Data.QueueEntry.value =
        [a] ∧
      observeM1 (read t) = ([], .errored (.foreign
        e)) := by
  intros
  simp (config := { zetaDelta := true })
  intro event
  constructor <;> rintro rfl <;> rfl

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-011.
An outer throw retains the earlier stored stream error.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_error_then_throw :
  ∀ {α ε : Type} (a : α) (stored thrown : ε),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : State α ε, resumeSize
      (error (beginEnqueue s a) (.foreign stored))
      (.thrown (.foreign thrown)) = some t ∧
      t.status = .errored (.foreign stored) ∧
      t.trace.getLast? = some (.enqueueReturned 0 (.error (.foreign thrown))) := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-011.
An invalid outer size retains the earlier stored stream error.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem reentrant_error_then_invalid :
  ∀ {α ε : Type} (a : α) (stored : ε),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : State α ε,
      resumeSize (error
        (beginEnqueue s a) (.foreign stored))
        (.value .posInfinity) = some t ∧
      t.status = .errored (.foreign stored) ∧ t.nextError = 1 ∧
      t.trace.getLast? = some (.enqueueReturned 0 (.error (.rangeError 0))) := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-close`; WS-READ-CE-002 through WS-READ-CE-004.
`op.rs-default-controller-private-pull` owns the closed-before-final-chunk order.
FIFO delivery and closed-before-final-chunk settlement in the local masks.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem fifo_close_m1_m2 :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } (.finite 0)
    let t := read (read
      (close
      (beginEnqueue (beginEnqueue s a) b)))
    observeM1 t = ([a, b], .closed) ∧
      settlementTrace t = [.read 0 (.ok (.chunk a)), .closed (.ok ()),
        .read 1 (.ok (.chunk b))] := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-001.
Direct delivery to a pending read bypasses the size callback.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem pending_read_skips_size :
  ∀ {α ε : Type} (a : α),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t : State α ε, returnPull
      (read s) .pending = some t ∧
      let u := beginEnqueue t a
      u.frames = [] ∧ u.queue.entries = [] ∧
        settlementTrace u = [.read 0 (.ok (.chunk a))] ∧
        u.trace = [.pullCalled 11, .settled (.read 0 (.ok (.chunk a))),
          .enqueueReturned 0 (.ok ())] := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-call-pull-if-needed`; WS-READ-CE-013.
A synchronous pull error precedes the captured chunk settlement.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem pull_reentrant_error_before_chunk :
  ∀ {α ε : Type} (a : α) (e : ε),
    let s := initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } sizes.one
    let waiting := read (beginEnqueue s a)
    ∃ t : State α ε,
      returnPull (error waiting (.foreign e))
        .pending = some t ∧
      t.status = .errored (.foreign e) ∧
      settlementTrace t = [.closed (.error (.foreign e)), .read 0 (.ok
        (.chunk a))] := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-call-pull-if-needed`; WS-READ-CE-014.
A synchronous pull enqueue changes the queue before the outer read returns.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem pull_reentrant_enqueue_changes_queue :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } sizes.one
    let waiting := read (beginEnqueue s a)
    ∃ t : State α ε,
      returnPull (beginEnqueue waiting b) .pending
        = some t ∧
      t.queue.entries.map Data.QueueEntry.value = [b] ∧
      observeM1 t = ([a], .readable) := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-call-pull-if-needed`; WS-READ-CE-015.
A nested read can settle before the captured outer read.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem pull_reentrant_read_overtakes :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .one, pull := 11, cancel := 13 } sizes.one
    let waiting := read (beginEnqueue s a)
    ∃ t : State α ε,
      returnPull (beginEnqueue
        (read waiting) b) .pending = some t ∧
      settlementTrace t = [.read 1 (.ok (.chunk b)), .read 0 (.ok (.chunk
        a))] := by
  intros
  simp (config := { zetaDelta := true })

/--
`op.readable-stream-default-controller-enqueue`; WS-READ-CE-016.
Nested invalid sizes allocate distinct errors and retain the first stored reason.
The theorem uses its stated local M1/M2 view, with arbitrary chunks and foreign reasons.
-/
theorem nested_invalid_sizes_fresh_errors :
  ∀ {α ε : Type} (a b : α),
    let s := initial (α := α) (ε := ε)
      { size := .foreign 7, pull := 11, cancel := 13 } (.finite 0)
    ∃ t u : State α ε,
      resumeSize (beginEnqueue
        (beginEnqueue s a) b)
        (.value .posInfinity) = some t ∧
      resumeSize t (.value .posInfinity) = some u ∧
      u.status = .errored (.rangeError 0) ∧ u.nextError = 2 ∧
      u.trace.getLast? = some (.enqueueReturned 0 (.error (.rangeError 1))) := by
  intros
  simp (config := { zetaDelta := true })

end Whatwg.Streams.Readable
