import Whatwg.Streams.Transform.Laws

/-!
# Composed transform runs

TRANSFORM-PG-BACKPRESSURE owns the three frozen statements. These proofs use
actual P4/P5 transitions for the named count-profile starts and tapes. Chunks,
reasons and the allocation seed remain universally quantified. The observations
are the frozen local candidates; global scheduling and DB-04 remain open.
-/

namespace Whatwg.Streams.Transform

set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

attribute [local simp] initial withReadable withWritable lookupPromise freshInternal
  subscriptionPromise notify subscribe settle setBackpressure unblockWrite sourcePull servicePull
  read performTransform sinkWrite answerTransform returnTransform error terminate enqueue react
  runJob tick externalFrontier decide
  Readable.initial Readable.sizes Readable.sizePositive Readable.beginEnqueue Readable.finishEnqueue
  Readable.returnPull Readable.read Readable.close Readable.streamClose Readable.error
  Readable.shouldCallPull Readable.canCloseOrEnqueue Readable.callPullIfNeeded
  Readable.callPullIfNeededWith Readable.continuePull Readable.observeM1 Readable.settlementTrace
  Readable.chunksOfSettlements Readable.acceptPullAnswer Readable.reactPull Readable.runPullJob
  Writable.initial Writable.tick Writable.decide Writable.externalFrontier Writable.operationPhase
  Writable.operationKind Writable.operationRequest Writable.setOperationPhase Writable.attachSink
  Writable.invokeSink Writable.acceptAnswer Writable.sizes Writable.sizeNonPositive
  Writable.lookupPromise Writable.freshPromise Writable.settle Writable.markHandled
  Writable.ensureReadyRejected Writable.updateBackpressure Writable.desiredSize
  Writable.getBackpressure Writable.clearAlgorithms Writable.closeQueuedOrInFlight
  Writable.hasInFlight Writable.unitPromiseToShared Writable.sinkAnswerFromShared
  Data.Queue.empty Data.enqueueValueWithSize Data.dequeueValue Data.resetQueue
  Data.SizeClass.isNonNegativeNumber Data.SizeClass.isPositiveInfinity
  Data.SizeClass.clampNonNegative Data.DyadicSize.sizes Data.DyadicSize.oneUnits
  Data.DyadicSize.isNaN Data.DyadicSize.isNegative Data.DyadicSize.isInfinite
  Data.DyadicSize.add Data.DyadicSize.sub Data.DyadicSize.neg
  Boundary.Exception.ofRangeError

/--
`op.transform-stream-default-sink-write-algorithm`, `op.transform-stream-default-source-pull`,
`op.transform-stream-default-controller-perform-transform`,
`op.transform-stream-default-controller-enqueue`, `op.initialize-transform-stream`.
The frozen composed local regression, with actual component states.
-/
theorem coupled_write_read_enqueue :
  ∀ {α β ε : Type} (input : α) (output : β) (seed : Nat),
   let start : State α β ε :=
     initial Data.DyadicSize.sizes.zero Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Decision.write input, .read, .enqueue output,
         .returnTransform (.settled .fulfilled)] ∧
     Reaches start tape last ∧
     Readable.observeM1 last.readable = ([output], .readable) ∧
     last.writable.status = .writable ∧
     Writable.lookupPromise last.writable (seed + 3) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.fulfilled ()) ∧
     last.backpressure = true ∧
     last.backpressurePromise = seed + 7 ∧
     lookupPromise last (seed + 2) = some (.fulfilled ()) ∧
     lookupPromise last (seed + 6) = some (.fulfilled ()) ∧
     lookupPromise last (seed + 7) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 3, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [] := by
  intro α β ε input output seed
  dsimp only
  exact ⟨[some (.write input), none, none, none, none, none, none,
      some .read, none, some (.enqueue output), some (.returnTransform (.settled .fulfilled)),
      none, none, none, none, none, none], _, by
    repeat first
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }) [Nat.add_assoc])
    | rfl
    | (simp (config := { zetaDelta := true }))⟩

/--
`op.transform-stream-default-sink-write-algorithm`, `op.transform-stream-default-source-pull`,
`op.transform-stream-default-controller-perform-transform`,
`op.transform-stream-error`, `op.transform-stream-error-writable-and-unblock-write`,
`op.transform-stream-default-controller-clear-algorithms`, `op.initialize-transform-stream`.
The frozen composed local regression, with actual component states.
-/
theorem coupled_error_during_transform :
  ∀ {α β ε : Type} (input : α) (reason : ε) (seed : Nat),
   let start : State α β ε :=
     initial Data.DyadicSize.sizes.zero Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Decision.write input, .read, .error (.foreign reason),
         .returnTransform (.settled .fulfilled)] ∧
     Reaches start tape last ∧
     Readable.observeM1 last.readable = ([], .errored (.foreign reason)) ∧
     last.writable.status = .errored (.foreign reason) ∧
     Writable.lookupPromise last.writable (seed + 3) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.rejected (.foreign reason)) ∧
     Writable.lookupPromise last.writable (seed + 1) = some (.rejected (.foreign reason)) ∧
     last.algorithms = none ∧ last.backpressure = false ∧
     last.backpressurePromise = seed + 6 ∧
     lookupPromise last (seed + 6) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 3, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [] := by
  intro α β ε input reason seed
  dsimp only
  exact ⟨[some (.write input), none, none, none, none, none, none,
      some .read, none, some (.error (.foreign reason)), none, none, none, none, none, none,
      some (.returnTransform (.settled .fulfilled)),
      none, none, none, none, none, none, none], _, by
    repeat first
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }) [Nat.add_assoc])
    | rfl
    | (simp (config := { zetaDelta := true }))⟩

/--
`op.transform-stream-default-sink-write-algorithm`, `op.transform-stream-default-source-pull`,
`op.transform-stream-default-controller-perform-transform`,
`op.transform-stream-default-controller-enqueue`, `op.initialize-transform-stream`,
`op.set-up-readable-stream-default-controller`.
The frozen composed local regression, with actual component states.
-/
theorem coupled_positive_readable_capacity :
  ∀ {α β ε : Type} (input : α) (output : β) (seed : Nat),
   let start : State α β ε :=
     initial Data.DyadicSize.sizes.one Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Decision.write input, .enqueue output, .returnTransform (.settled .fulfilled)]
         ∧
     Reaches start tape last ∧
     last.readable.queue.entries.map Data.QueueEntry.value = [output] ∧
     Readable.observeM1 last.readable = ([], .readable) ∧
     last.writable.status = .writable ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 5) = some (.fulfilled ()) ∧
     last.backpressure = true ∧ last.backpressurePromise = seed + 6 ∧
     lookupPromise last (seed + 2) = some (.fulfilled ()) ∧
     lookupPromise last (seed + 3) = some (.fulfilled ()) ∧
     lookupPromise last (seed + 6) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 4, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [] := by
  intro α β ε input output seed
  dsimp only
  exact ⟨[none, some (.write input), none, none, none, none, none,
      some (.enqueue output), some (.returnTransform (.settled .fulfilled)),
      none, none, none, none, none, none], _, by
    repeat first
    | apply And.intro
    | exact Reaches.nil _
    | apply Reaches.cons
    | (unfold Step; simp (config := { zetaDelta := true }) [Nat.add_assoc])
    | rfl
    | (simp (config := { zetaDelta := true }))⟩

end Whatwg.Streams.Transform
