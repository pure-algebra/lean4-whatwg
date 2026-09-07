import Whatwg.Streams.Writable.Laws

/-!
# Composed writable lifecycles

WRITABLE-PG-DEFAULT owns these two frozen statements. They quantify chunks and
reasons but fix initial projections and tape shapes. Observations are the local
ordered candidate view; general reachability and global/DB-04 embeddings stay open.
-/

namespace Whatwg.Streams.Writable

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

attribute [local simp] reaches_cons reaches_nil Step initial tick decide externalFrontier
  operationPhase operationKind operationRequest setOperationPhase attachSink invokeSink acceptAnswer
  sizes sizeNonPositive lookupPromise freshPromise settle markHandled ensureReadyRejected
  updateBackpressure desiredSize getBackpressure clearAlgorithms closeQueuedOrInFlight hasInFlight
  sinkInput visibleEvents observeSink observeOrdered
  Data.Queue.empty Data.enqueueValueWithSize Data.dequeueValue Data.resetQueue
  Data.SizeClass.isNonNegativeNumber Data.SizeClass.isPositiveInfinity
  Data.SizeClass.clampNonNegative Data.DyadicSize.sizes Data.DyadicSize.oneUnits
  Data.DyadicSize.isNaN Data.DyadicSize.isNegative Data.DyadicSize.isInfinite
  Data.DyadicSize.add Data.DyadicSize.sub Data.DyadicSize.neg

/--
`op.writable-stream-default-writer-write`, `op.writable-stream-update-backpressure`,
`op.writable-stream-close`, `op.writable-stream-default-controller-process-write`,
`op.writable-stream-default-controller-process-close`, `op.writable-stream-finish-in-flight-close`.
The frozen initial/tape derivations and exact local ordered observation.
-/
theorem lifecycle_write_close :
  ∀ {α ε : Type} (chunk : α),
    let start := initial (α := α) (ε := ε) sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ blocked done : State α ε,
      Reaches start
        [some .queryReady, some (.write chunk), none, none, none, none,
          some (.returnSink .pending), none, some .queryReady, some .queryDesiredSize] blocked ∧
      blocked.backpressure = true ∧ blocked.readyPromise = 3 ∧
      lookupPromise blocked 0 = some (.fulfilled ()) ∧
      lookupPromise blocked 3 = some .pending ∧
      desiredSize blocked = some sizes.zero ∧
      Reaches blocked
        [some .close, none, none, none, some .queryReady, some .queryDesiredSize,
          some (.answer .write 2 .fulfilled), none, none, none,
          some (.returnSink (.settled .fulfilled)), none, none] done ∧
      done.status = .closed ∧ done.backpressure = true ∧ done.readyPromise = 3 ∧
      lookupPromise done 0 = some (.fulfilled ()) ∧
      lookupPromise done 1 = some (.fulfilled ()) ∧
      lookupPromise done 3 = some (.fulfilled ()) ∧
      lookupPromise done 4 = some (.fulfilled ()) ∧
      observeOrdered done =
        ⟨⟨[chunk], .closed⟩,
          [.readyRead 0 0, .returned 1 2, .readyRead 2 3,
            .desiredSizeRead 3 (some sizes.zero), .settled 3 (.ok ()),
            .returned 4 4, .readyRead 5 3, .desiredSizeRead 6 (some sizes.zero),
            .settled 2 (.ok ()), .settled 4 (.ok ()), .settled 1 (.ok ())]⟩ := by
  intros
  exact ⟨_, _, by
    repeat first
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }))
    | rfl⟩

/--
`op.writable-stream-default-writer-write`, `op.writable-stream-abort`,
`op.writable-stream-start-erroring`, `op.writable-stream-finish-in-flight-write-with-error`,
`op.writable-stream-finish-erroring`, `op.ws-default-controller-private-abort`,
`op.writable-stream-reject-close-and-closed-promise-if-needed`.
The frozen initial/tape derivations and exact local ordered observation.
-/
theorem lifecycle_abort_rejection :
  ∀ {α ε : Type} (first second : α) (abortReason writeReason : Boundary.Exception ε),
    writeReason ≠ abortReason →
    let start := initial (α := α) (ε := ε) sizes.one
      { size := some .one, write := some (.foreign 0), close := some (.foreign 1),
        abort := some (.foreign 2) } 0 0
    ∃ blocked done : State α ε,
      Reaches start
        [some (.write first), none, none, none, none, some (.returnSink .pending), none,
          some (.write second), none, none, none, none, none,
          some (.abort abortReason), none, some .returnSignal, none, none, none] blocked ∧
      blocked.status = .erroring abortReason ∧
      blocked.inFlightWrite = some (2, .awaiting) ∧ blocked.writeRequests = [4] ∧
      blocked.pendingAbort = some (.requested 5 abortReason) ∧
      lookupPromise blocked 0 = some (.fulfilled ()) ∧
      lookupPromise blocked 3 = some (.rejected abortReason) ∧
      Reaches blocked
        [some (.answer .write 2 (.rejected writeReason)), none, none, none, none,
          some (.returnSink (.settled .fulfilled)), none, none, none] done ∧
      done.status = .errored abortReason ∧ done.pendingAbort = none ∧
      done.inFlightWrite = none ∧ done.abortInFlight = none ∧ done.writeRequests = [] ∧
      done.queue = Data.Queue.empty sizes ∧
      lookupPromise done 0 = some (.fulfilled ()) ∧
      lookupPromise done 1 = some (.rejected abortReason) ∧
      lookupPromise done 2 = some (.rejected writeReason) ∧
      lookupPromise done 4 = some (.rejected abortReason) ∧
      lookupPromise done 5 = some (.fulfilled ()) ∧
      observeOrdered done =
        ⟨⟨[first], .errored abortReason⟩,
          [.returned 0 2, .returned 1 4, .settled 3 (.error abortReason),
            .returned 2 5, .settled 2 (.error writeReason), .settled 4 (.error abortReason),
            .settled 5 (.ok ()), .settled 1 (.error abortReason)]⟩ := by
  intros
  exact ⟨_, _, by
    repeat first
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }))
    | rfl⟩

end Whatwg.Streams.Writable
