import Whatwg.Streams.Piping.Laws
import Whatwg.Streams.Readable.Step

/-!
# Composed forward-error shutdown runs

PIPING-PG-FORWARD-SHUTDOWN owns the frozen finite tape shapes. The source
prefixes use actual readable enqueue/read operations; the candidate steps use
actual writable operations. Chunks and distinct reasons remain quantified.
The observation ends at the request to finalize; full pipe settlement and
global M1/M2 remain open.
-/

namespace Whatwg.Streams.Piping

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
set_option maxHeartbeats 300000

attribute [local simp] initial snapshot emit drainGuard nextUnwritten allWrittenSettled
  lookupReturn foreignDecision enterForwardShutdown invokeWrite captureWrite invokeAbort
  captureAbort requestFinalize stepWritable externalFrontier decide tick markWrite deliveredReads
  Readable.initial Readable.sizes Readable.sizePositive Readable.beginEnqueue Readable.finishEnqueue
  Readable.read Readable.error Readable.shouldCallPull Readable.canCloseOrEnqueue
  Readable.callPullIfNeeded Readable.callPullIfNeededWith Readable.continuePull
  Readable.chunksOfSettlements
  Writable.initial Writable.tick Writable.decide Writable.externalFrontier Writable.operationPhase
  Writable.operationKind Writable.operationRequest Writable.setOperationPhase Writable.attachSink
  Writable.invokeSink Writable.acceptAnswer Writable.sizes Writable.sizeNonPositive
  Writable.lookupPromise Writable.freshPromise Writable.settle Writable.markHandled
  Writable.ensureReadyRejected Writable.updateBackpressure Writable.desiredSize
  Writable.getBackpressure Writable.clearAlgorithms Writable.closeQueuedOrInFlight
  Writable.hasInFlight Writable.sinkInput Writable.unitPromiseToShared Writable.sinkAnswerFromShared
  Data.Queue.empty Data.enqueueValueWithSize Data.dequeueValue Data.resetQueue
  Data.SizeClass.isNonNegativeNumber Data.SizeClass.isPositiveInfinity
  Data.SizeClass.clampNonNegative Data.DyadicSize.sizes Data.DyadicSize.oneUnits
  Data.DyadicSize.isNaN Data.DyadicSize.isNegative Data.DyadicSize.isInfinite
  Data.DyadicSize.add Data.DyadicSize.sub Data.DyadicSize.neg
  Boundary.Exception.ofRangeError

/-- Frozen canonical prefix/run witness for forward error and rejected abort action. -/
theorem lifecycle_two_writes_abort_rejection :
  ∀ {α ε : Type} (first second : α) (sourceReason actionReason : Boundary.Exception ε),
    actionReason ≠ sourceReason →
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ r : Readable.State α ε,
      Readable.Steps r0 [.enqueue first, .read, .enqueue second, .read] r ∧
      deliveredReads r = [(0, first), (1, second)] ∧
      let start := initial r w0 false
      Admitted start ∧
      ∃ writing blocked secondBlocked done : State α ε,
        Reaches start
          (List.replicate 5 none ++
            [some (.writable (.returnSink .pending)), none, none]) writing ∧
        writing.phase = .running ∧
        Writable.lookupPromise writing.destination 2 = some .pending ∧
        Reaches writing
          (some (.sourceError sourceReason) :: List.replicate 9 none) blocked ∧
        blocked.phase = .waitingWrites ∧
        blocked.selection = some ⟨sourceReason, true, false⟩ ∧
        blocked.links = [⟨0, first, .submitted 0 2⟩, ⟨1, second, .submitted 1 4⟩] ∧
        blocked.destination.inFlightWrite = some (2, .awaiting) ∧
        blocked.destination.writeRequests = [4] ∧
        Writable.lookupPromise blocked.destination 2 = some .pending ∧
        Writable.lookupPromise blocked.destination 4 = some .pending ∧
        blocked.abortCall = none ∧ tick blocked = none ∧
        Reaches blocked
          [some (.writable (.answer .write 2 .fulfilled)), none, none, none,
            some (.writable (.returnSink .pending))] secondBlocked ∧
        Writable.lookupPromise secondBlocked.destination 2 = some (.fulfilled ()) ∧
        Writable.lookupPromise secondBlocked.destination 4 = some .pending ∧
        secondBlocked.abortCall = none ∧ tick secondBlocked = none ∧
        Reaches secondBlocked
          ([some (.writable (.answer .write 4 .fulfilled))] ++ List.replicate 5 none ++
            [some (.writable .returnSignal)] ++ List.replicate 3 none ++
            [some (.writable (.returnSink (.settled (.rejected actionReason))))] ++
            List.replicate 6 none) done ∧
        done.phase = .readyToFinalize actionReason ∧
        done.source.status = .errored sourceReason ∧
        done.destination.status = .errored sourceReason ∧
        done.selection = some ⟨sourceReason, true, false⟩ ∧
        done.abortCall = some 2 ∧ done.abortPromise = some 5 ∧
        Writable.lookupPromise done.destination 2 = some (.fulfilled ()) ∧
        Writable.lookupPromise done.destination 4 = some (.fulfilled ()) ∧
        Writable.lookupPromise done.destination 5 = some (.rejected actionReason) ∧
        Writable.lookupPromise done.destination 1 = some (.rejected sourceReason) ∧
        Writable.sinkInput done.destination = [first, second] ∧
        ForwardShutdownSpec (observeShutdown done) := by
  intro α ε first second sourceReason actionReason distinct
  dsimp only
  let r0 := Readable.initial (α := α) (ε := ε)
    { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
  let r := Readable.read (Readable.beginEnqueue
    (Readable.read (Readable.beginEnqueue r0 first)) second)
  let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
    { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
      abort := some (.foreign 2) } 0 0
  let start := initial r w0 false
  have admitted : Admitted start := by
    refine ⟨?entry, ?_, ?_, ?_⟩
    case entry =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        Writable.sizes.one,
        { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
          abort := some (.foreign 2) }, 0, ?_⟩
      all_goals simp (config := { zetaDelta := true }) [ReadInventory]
    all_goals simp (config := { zetaDelta := true })
  refine ⟨r, .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))), ?reads,
    admitted, ?writing, ?blocked, ?secondBlocked, ?done, ?runs⟩
  case reads => simp (config := { zetaDelta := true })
  case runs => repeat first
  | (guard_target = ForwardShutdownSpec (observeShutdown (α := α) (ε := ε) _)
     apply forwardShutdown_realizes start _
      ((List.replicate 5 none ++ [some (.writable (.returnSink .pending)), none, none]) ++
        (some (.sourceError sourceReason) :: List.replicate 9 none) ++
        [some (.writable (.answer .write 2 .fulfilled)), none, none, none,
          some (.writable (.returnSink .pending))] ++
        ([some (.writable (.answer .write 4 .fulfilled))] ++ List.replicate 5 none ++
          [some (.writable .returnSignal)] ++ List.replicate 3 none ++
          [some (.writable (.returnSink (.settled (.rejected actionReason))))] ++
          List.replicate 6 none)))
  | exact admitted
  | apply And.intro
  | exact Reaches.nil _
  | apply Reaches.cons
  | (unfold Step; simp (config := { zetaDelta := true }))
  | rfl
  | (simp (config := { zetaDelta := true }))

/-- Frozen canonical prefix/run witness for write rejection with either prevention flag. -/
theorem lifecycle_write_rejection_retains_source :
  ∀ {α ε : Type} (chunk : α) (sourceReason writeReason : Boundary.Exception ε) (prevent : Bool),
    writeReason ≠ sourceReason →
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ r : Readable.State α ε,
      Readable.Steps r0 [.enqueue chunk, .read] r ∧
      deliveredReads r = [(0, chunk)] ∧
      let start := initial r w0 prevent
      Admitted start ∧
      ∃ writing blocked done : State α ε,
        Reaches start
          (List.replicate 5 none ++
            [some (.writable (.returnSink .pending)), none, none]) writing ∧
        Reaches writing [some (.sourceError sourceReason), none, none] blocked ∧
        blocked.phase = .waitingWrites ∧
        blocked.selection = some ⟨sourceReason, true, prevent⟩ ∧
        blocked.links = [⟨0, chunk, .submitted 0 2⟩] ∧
        Writable.lookupPromise blocked.destination 2 = some .pending ∧
        blocked.abortCall = none ∧ tick blocked = none ∧
        Reaches blocked
          ([some (.writable (.answer .write 2 (.rejected writeReason)))] ++
            List.replicate 6 none ++ (if prevent then [none] else List.replicate 5 none)) done ∧
        done.phase = .readyToFinalize sourceReason ∧
        done.source.status = .errored sourceReason ∧
        done.destination.status = .errored writeReason ∧
        done.selection = some ⟨sourceReason, true, prevent⟩ ∧
        done.abortCall = (if prevent then none else some 1) ∧
        done.abortPromise = (if prevent then none else some 4) ∧
        Writable.lookupPromise done.destination 2 = some (.rejected writeReason) ∧
        Writable.lookupPromise done.destination 1 = some (.rejected writeReason) ∧
        (if prevent then True else
          Writable.lookupPromise done.destination 4 = some (.fulfilled ())) ∧
        Writable.sinkInput done.destination = [chunk] ∧
        (∀ name request reason,
          Writable.Event.sinkCalled name (.abort request reason) ∉ done.destination.trace) ∧
        ForwardShutdownSpec (observeShutdown done) := by
  intro α ε chunk sourceReason writeReason prevent distinct
  cases prevent with
  | false =>
    dsimp only
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let r := Readable.read (Readable.beginEnqueue r0 chunk)
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    let start := initial r w0 false
    have admitted : Admitted start := by
      refine ⟨?entry, ?_, ?_, ?_⟩
      case entry =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          Writable.sizes.one,
          { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
            abort := some (.foreign 2) }, 0, ?_⟩
        all_goals simp (config := { zetaDelta := true }) [ReadInventory]
      all_goals simp (config := { zetaDelta := true })
    refine ⟨r, .cons rfl (.cons rfl (.nil _)), ?reads,
      admitted, ?writing, ?blocked, ?done, ?runs⟩
    case reads => simp (config := { zetaDelta := true })
    case runs => repeat first
    | (guard_target = ForwardShutdownSpec (observeShutdown (α := α) (ε := ε) _)
       apply forwardShutdown_realizes start _
        ((List.replicate 5 none ++ [some (.writable (.returnSink .pending)), none, none]) ++
          [some (.sourceError sourceReason), none, none] ++
          ([some (.writable (.answer .write 2 (.rejected writeReason)))] ++
            List.replicate 6 none ++ List.replicate 5 none)))
    | exact admitted
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }))
    | rfl
    | (simp (config := { zetaDelta := true }))

  | true =>
    dsimp only
    let r0 := Readable.initial (α := α) (ε := ε)
      { size := .one, pull := 10, cancel := 11 } Readable.sizes.zero
    let r := Readable.read (Readable.beginEnqueue r0 chunk)
    let w0 := Writable.initial (α := α) (ε := ε) Writable.sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    let start := initial r w0 true
    have admitted : Admitted start := by
      refine ⟨?entry, ?_, ?_, ?_⟩
      case entry =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          Writable.sizes.one,
          { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
            abort := some (.foreign 2) }, 0, ?_⟩
        all_goals simp (config := { zetaDelta := true }) [ReadInventory]
      all_goals simp (config := { zetaDelta := true })
    refine ⟨r, .cons rfl (.cons rfl (.nil _)), ?readsTrue,
      admitted, ?writingTrue, ?blockedTrue, ?doneTrue, ?runsTrue⟩
    case readsTrue => simp (config := { zetaDelta := true })
    case runsTrue => repeat first
    | (guard_target = ForwardShutdownSpec (observeShutdown (α := α) (ε := ε) _)
       apply forwardShutdown_realizes start _
        ((List.replicate 5 none ++ [some (.writable (.returnSink .pending)), none, none]) ++
          [some (.sourceError sourceReason), none, none] ++
          ([some (.writable (.answer .write 2 (.rejected writeReason)))] ++
            List.replicate 6 none ++ [none])))
    | exact admitted
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }))
    | rfl
    | (simp (config := { zetaDelta := true }))


end Whatwg.Streams.Piping
