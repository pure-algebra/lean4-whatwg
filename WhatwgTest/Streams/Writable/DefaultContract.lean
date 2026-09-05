import Whatwg.Streams

/-! Frozen P5a breaker interface, 2026-09-05.
Contract: test/contracts/writable-default.contract.md. Graph: WRITABLE-PG-DEFAULT.
Fixed attached writer; sink-input/ordered candidate views, DB-04 mask embeddings remain open.
Callback markers and deterministic continuation tags are first-order administrative state. -/

set_option autoImplicit false

-- SIZE
#check (@Whatwg.Streams.Writable.Size :
  Type)

-- SIZE
#check (@Whatwg.Streams.Writable.sizes :
  Whatwg.Streams.Data.SizeClass Whatwg.Streams.Writable.Size)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.UnitPromise :
  Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkAnswer :
  Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkReturn :
  Type → Type)

-- STARTERROR
#check (@Whatwg.Streams.Writable.Status :
  Type → Type)

-- ENQUEUE
#check (@Whatwg.Streams.Writable.QueueItem :
  Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.OperationPhase :
  Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkKind :
  Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkOperation :
  Type → Type → Type)

-- CLOSE
#check (@Whatwg.Streams.Writable.CloseState :
  Type)

-- ABORT
#check (@Whatwg.Streams.Writable.PendingAbort :
  Type → Type)

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms :
  Type)

-- ADVANCE
#check (@Whatwg.Streams.Writable.Control :
  Type → Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkJob :
  Type → Type → Type)

-- WRITE
#check (@Whatwg.Streams.Writable.Event :
  Type → Type → Type)

-- DESIRED
#check (@Whatwg.Streams.Writable.VisibleEvent :
  Type → Type)

-- WRITE
#check (@Whatwg.Streams.Writable.State :
  Type → Type → Type)

-- WRITE
#check (@Whatwg.Streams.Writable.Decision :
  Type → Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkObservation :
  Type → Type → Type)

-- DESIRED
#check (@Whatwg.Streams.Writable.OrderedObservation :
  Type → Type → Type)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromiseToShared :
  ∀ {ε : Type}, Whatwg.Streams.Writable.UnitPromise ε → Whatwg.Streams.Readable.PromiseState Unit ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromiseFromShared :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PromiseState Unit ε → Whatwg.Streams.Writable.UnitPromise ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswerToShared :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkAnswer ε → Whatwg.Streams.Readable.PullAnswer ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswerFromShared :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullAnswer ε → Whatwg.Streams.Writable.SinkAnswer ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturnToShared :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkReturn ε → Whatwg.Streams.Readable.PullReturn ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturnFromShared :
  ∀ {ε : Type}, Whatwg.Streams.Readable.PullReturn ε → Whatwg.Streams.Writable.SinkReturn ε)

-- WRITE
#check (@Whatwg.Streams.Writable.Status.writable :
  ∀ {ε : Type}, Whatwg.Streams.Writable.Status ε)

-- STARTERROR
#check (@Whatwg.Streams.Writable.Status.erroring :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Status ε)

-- FINISHERROR
#check (@Whatwg.Streams.Writable.Status.errored :
  ∀ {ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Status ε)

-- CLOSEOK
#check (@Whatwg.Streams.Writable.Status.closed :
  ∀ {ε : Type}, Whatwg.Streams.Writable.Status ε)

-- ENQUEUE
#check (@Whatwg.Streams.Writable.QueueItem.chunk :
  ∀ {α : Type}, α → Whatwg.Streams.Writable.QueueItem α)

-- CLOSEQUEUE
#check (@Whatwg.Streams.Writable.QueueItem.close :
  ∀ {α : Type}, Whatwg.Streams.Writable.QueueItem α)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.OperationPhase.invoking :
  Whatwg.Streams.Writable.OperationPhase)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.OperationPhase.awaiting :
  Whatwg.Streams.Writable.OperationPhase)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.OperationPhase.queued :
  Whatwg.Streams.Writable.OperationPhase)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkKind.write :
  Whatwg.Streams.Writable.SinkKind)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkKind.close :
  Whatwg.Streams.Writable.SinkKind)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkKind.abort :
  Whatwg.Streams.Writable.SinkKind)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkOperation.write :
  ∀ {α ε : Type}, Nat → α → Whatwg.Streams.Writable.SinkOperation α ε)

-- PROCESSCLOSE
#check (@Whatwg.Streams.Writable.SinkOperation.close :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Writable.SinkOperation α ε)

-- ABORTSTEPS
#check (@Whatwg.Streams.Writable.SinkOperation.abort :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.SinkOperation α ε)

-- CLOSE
#check (@Whatwg.Streams.Writable.CloseState.none :
  Whatwg.Streams.Writable.CloseState)

-- CLOSE
#check (@Whatwg.Streams.Writable.CloseState.queued :
  Nat → Whatwg.Streams.Writable.CloseState)

-- PROCESSCLOSE
#check (@Whatwg.Streams.Writable.CloseState.inFlight :
  Nat → Whatwg.Streams.Writable.OperationPhase → Whatwg.Streams.Writable.CloseState)

-- ABORT
#check (@Whatwg.Streams.Writable.PendingAbort.requested :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.PendingAbort ε)

-- ABORT
#check (@Whatwg.Streams.Writable.PendingAbort.alreadyErroring :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Writable.PendingAbort ε)

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms.mk :
  Option (Whatwg.Streams.Data.SizeAlgorithm Nat) → Option Whatwg.Streams.Writable.SinkAlgorithm → Option Whatwg.Streams.Writable.SinkAlgorithm →
    Option Whatwg.Streams.Writable.SinkAlgorithm → Whatwg.Streams.Writable.Algorithms)

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms.size :
  Whatwg.Streams.Writable.Algorithms → Option (Whatwg.Streams.Data.SizeAlgorithm Nat))

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms.write :
  Whatwg.Streams.Writable.Algorithms → Option Whatwg.Streams.Writable.SinkAlgorithm)

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms.close :
  Whatwg.Streams.Writable.Algorithms → Option Whatwg.Streams.Writable.SinkAlgorithm)

-- CLEAR
#check (@Whatwg.Streams.Writable.Algorithms.abort :
  Whatwg.Streams.Writable.Algorithms → Option Whatwg.Streams.Writable.SinkAlgorithm)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkJob.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkKind → Nat → Whatwg.Streams.Writable.SinkAnswer ε → Whatwg.Streams.Writable.SinkJob α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkJob.answer :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkJob α ε → Whatwg.Streams.Writable.SinkAnswer ε)

-- SIZE
#check (@Whatwg.Streams.Writable.Control.getSize :
  ∀ {α ε : Type}, Nat → α → Whatwg.Streams.Writable.Control α ε)

-- SIZE
#check (@Whatwg.Streams.Writable.Control.awaitSize :
  ∀ {α ε : Type}, Nat → α → Whatwg.Streams.Writable.Control α ε)

-- WRITE
#check (@Whatwg.Streams.Writable.Control.afterSize :
  ∀ {α ε : Type}, Nat → α → Whatwg.Streams.Writable.Size → Whatwg.Streams.Writable.Control α ε)

-- ENQUEUE
#check (@Whatwg.Streams.Writable.Control.enqueueWrite :
  ∀ {α ε : Type}, α → Whatwg.Streams.Writable.Size → Whatwg.Streams.Writable.Control α ε)

-- ADVANCE
#check (@Whatwg.Streams.Writable.Control.advance :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Control α ε)

-- CLOSE
#check (@Whatwg.Streams.Writable.Control.beginClose :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Writable.Control α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Control.beginAbort :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Control.awaitSignal :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Control.afterSignal :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.Control.awaitSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.Control α ε)

-- STARTERROR
#check (@Whatwg.Streams.Writable.Control.startErroring :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- FINISHERROR
#check (@Whatwg.Streams.Writable.Control.finishErroring :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Control α ε)

-- ERRORIF
#check (@Whatwg.Streams.Writable.Control.errorIfNeeded :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- PUBLICERROR; ERROR
#check (@Whatwg.Streams.Writable.Control.controllerError :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- DEAL
#check (@Whatwg.Streams.Writable.Control.dealRejection :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- REJECTCLOSED
#check (@Whatwg.Streams.Writable.Control.rejectCloseClosed :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Control α ε)

-- WRITE
#check (@Whatwg.Streams.Writable.Control.returnPromise :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Streams.Writable.Control α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.Control.react :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkJob α ε → Whatwg.Streams.Writable.Control α ε)

-- SIZE
#check (@Whatwg.Streams.Writable.Event.sizeCalled :
  ∀ {α ε : Type}, Nat → Nat → α → Whatwg.Streams.Writable.Event α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.Event.sinkCalled :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.Event α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Event.signalCalled :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Event α ε)

-- WRITEOK
#check (@Whatwg.Streams.Writable.Event.settled :
  ∀ {α ε : Type}, Nat → Except (Whatwg.Streams.Boundary.Exception ε) Unit → Whatwg.Streams.Writable.Event α ε)

-- WRITE
#check (@Whatwg.Streams.Writable.Event.returned :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Streams.Writable.Event α ε)

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.Event.readyRead :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Streams.Writable.Event α ε)

-- REJECTCLOSED
#check (@Whatwg.Streams.Writable.Event.closedRead :
  ∀ {α ε : Type}, Nat → Nat → Whatwg.Streams.Writable.Event α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.Event.desiredSizeRead :
  ∀ {α ε : Type}, Nat → Option Whatwg.Streams.Writable.Size → Whatwg.Streams.Writable.Event α ε)

-- WRITEOK
#check (@Whatwg.Streams.Writable.VisibleEvent.settled :
  ∀ {ε : Type}, Nat → Except (Whatwg.Streams.Boundary.Exception ε) Unit → Whatwg.Streams.Writable.VisibleEvent ε)

-- WRITE
#check (@Whatwg.Streams.Writable.VisibleEvent.returned :
  ∀ {ε : Type}, Nat → Nat → Whatwg.Streams.Writable.VisibleEvent ε)

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.VisibleEvent.readyRead :
  ∀ {ε : Type}, Nat → Nat → Whatwg.Streams.Writable.VisibleEvent ε)

-- REJECTCLOSED
#check (@Whatwg.Streams.Writable.VisibleEvent.closedRead :
  ∀ {ε : Type}, Nat → Nat → Whatwg.Streams.Writable.VisibleEvent ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.VisibleEvent.desiredSizeRead :
  ∀ {ε : Type}, Nat → Option Whatwg.Streams.Writable.Size → Whatwg.Streams.Writable.VisibleEvent ε)

-- WRITE
#check (@Whatwg.Streams.Writable.State.mk :
  ∀ {α ε : Type},
  Whatwg.Streams.Writable.Status ε →
  Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size →
  Whatwg.Streams.Writable.Size →
  Bool →
  Whatwg.Streams.Writable.Algorithms →
  Nat →
  Nat →
  List (Nat × Whatwg.Streams.Writable.UnitPromise ε) →
  List Nat →
  List Nat →
  Whatwg.Streams.Writable.CloseState →
  Option (Nat × Whatwg.Streams.Writable.OperationPhase) →
  Option (Nat × Whatwg.Streams.Writable.OperationPhase) →
  Option (Whatwg.Streams.Writable.PendingAbort ε) →
  Option (Whatwg.Streams.Boundary.Exception ε) →
  Nat →
  Nat →
  Nat →
  List (Whatwg.Streams.Writable.Control α ε) →
  List (Whatwg.Streams.Writable.SinkJob α ε) →
  List (Whatwg.Streams.Writable.Event α ε) → Whatwg.Streams.Writable.State α ε)

-- WRITE
#check (@Whatwg.Streams.Writable.State.status :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.Status ε)

-- WRITE
#check (@Whatwg.Streams.Writable.State.queue :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size)

-- WRITE
#check (@Whatwg.Streams.Writable.State.highWaterMark :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.Size)

-- WRITE
#check (@Whatwg.Streams.Writable.State.backpressure :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

-- WRITE
#check (@Whatwg.Streams.Writable.State.algorithms :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.Algorithms)

-- WRITE
#check (@Whatwg.Streams.Writable.State.readyPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.closedPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.promises :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Nat × Whatwg.Streams.Writable.UnitPromise ε))

-- WRITE
#check (@Whatwg.Streams.Writable.State.handled :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.writeRequests :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.closeState :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.CloseState)

-- WRITE
#check (@Whatwg.Streams.Writable.State.inFlightWrite :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Nat × Whatwg.Streams.Writable.OperationPhase))

-- WRITE
#check (@Whatwg.Streams.Writable.State.abortInFlight :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Nat × Whatwg.Streams.Writable.OperationPhase))

-- WRITE
#check (@Whatwg.Streams.Writable.State.pendingAbort :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Whatwg.Streams.Writable.PendingAbort ε))

-- WRITE
#check (@Whatwg.Streams.Writable.State.signalArgument :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Whatwg.Streams.Boundary.Exception ε))

-- WRITE
#check (@Whatwg.Streams.Writable.State.nextCall :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.nextPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.nextError :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat)

-- WRITE
#check (@Whatwg.Streams.Writable.State.control :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Writable.Control α ε))

-- WRITE
#check (@Whatwg.Streams.Writable.State.jobs :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Writable.SinkJob α ε))

-- WRITE
#check (@Whatwg.Streams.Writable.State.trace :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Writable.Event α ε))

-- WRITE
#check (@Whatwg.Streams.Writable.Decision.write :
  ∀ {α ε : Type}, α → Whatwg.Streams.Writable.Decision α ε)

-- CLOSE
#check (@Whatwg.Streams.Writable.Decision.close :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Decision.abort :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Decision α ε)

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.Decision.controllerError :
  ∀ {α ε : Type}, Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.Decision α ε)

-- READYGET
#check (@Whatwg.Streams.Writable.Decision.queryReady :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε)

-- CLOSEDGET
#check (@Whatwg.Streams.Writable.Decision.queryClosed :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.Decision.queryDesiredSize :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε)

-- SIZE
#check (@Whatwg.Streams.Writable.Decision.returnSize :
  ∀ {α ε : Type}, Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Writable.Size (Whatwg.Streams.Boundary.Exception ε) → Whatwg.Streams.Writable.Decision α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.Decision.returnSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkReturn ε → Whatwg.Streams.Writable.Decision α ε)

-- ABORT
#check (@Whatwg.Streams.Writable.Decision.returnSignal :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Decision α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.Decision.answer :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkKind → Nat → Whatwg.Streams.Writable.SinkAnswer ε → Whatwg.Streams.Writable.Decision α ε)

-- WRITERSETUP
#check (@Whatwg.Streams.Writable.initial :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.Size → Whatwg.Streams.Writable.Algorithms → Nat → Nat → Whatwg.Streams.Writable.State α ε)

-- WRITEOK
#check (@Whatwg.Streams.Writable.lookupPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat → Option (Whatwg.Streams.Writable.UnitPromise ε))

-- WRITE
#check (@Whatwg.Streams.Writable.freshPromise :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.UnitPromise ε → Whatwg.Streams.Writable.State α ε × Nat)

-- WRITEOK
#check (@Whatwg.Streams.Writable.settle :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat → Except (Whatwg.Streams.Boundary.Exception ε) Unit → Whatwg.Streams.Writable.State α ε)

-- READYERROR
#check (@Whatwg.Streams.Writable.markHandled :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Nat → Whatwg.Streams.Writable.State α ε)

-- READYERROR
#check (@Whatwg.Streams.Writable.ensureReadyRejected :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Boundary.Exception ε → Whatwg.Streams.Writable.State α ε)

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.updateBackpressure :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool → Whatwg.Streams.Writable.State α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.desiredSize :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option Whatwg.Streams.Writable.Size)

-- GETBACKPRESSURE; CONTROLLERDESIRED
#check (@Whatwg.Streams.Writable.getBackpressure :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

-- CLEAR
#check (@Whatwg.Streams.Writable.clearAlgorithms :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.State α ε)

-- CLOSEPENDING
#check (@Whatwg.Streams.Writable.closeQueuedOrInFlight :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

-- INFLIGHT
#check (@Whatwg.Streams.Writable.hasInFlight :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.externalFrontier :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Bool)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationPhase :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkKind → Nat → Option Whatwg.Streams.Writable.OperationPhase)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.setOperationPhase :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.OperationPhase → Whatwg.Streams.Writable.State α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.invokeSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkOperation α ε → Option (Whatwg.Streams.Writable.State α ε))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.attachSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.SinkReturn ε → Whatwg.Streams.Writable.State α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.acceptAnswer :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkKind → Nat → Whatwg.Streams.Writable.SinkAnswer ε → Option (Whatwg.Streams.Writable.State α ε))

-- WRITE
#check (@Whatwg.Streams.Writable.decide :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.Decision α ε → Option (Whatwg.Streams.Writable.State α ε))

-- ADVANCE
#check (@Whatwg.Streams.Writable.tick :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Whatwg.Streams.Writable.State α ε))

-- ADVANCE
#check (@Whatwg.Streams.Writable.Step :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Option (Whatwg.Streams.Writable.Decision α ε) → Whatwg.Streams.Writable.State α ε → Prop)

-- ADVANCE
#check (@Whatwg.Streams.Writable.Reaches :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Option (Whatwg.Streams.Writable.Decision α ε)) → Whatwg.Streams.Writable.State α ε → Prop)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkInput :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List α)

-- DESIRED
#check (@Whatwg.Streams.Writable.visibleEvents :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Whatwg.Streams.Writable.VisibleEvent ε))

-- WRITEOK
#check (@Whatwg.Streams.Writable.settlementTrace :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → List (Nat × Except (Whatwg.Streams.Boundary.Exception ε) Unit))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.observeSink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.SinkObservation α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.observeOrdered :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.State α ε → Whatwg.Streams.Writable.OrderedObservation α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkObservation.mk :
  ∀ {α ε : Type}, List α → Whatwg.Streams.Writable.Status ε → Whatwg.Streams.Writable.SinkObservation α ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkObservation.chunks :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkObservation α ε → List α)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkObservation.status :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkObservation α ε → Whatwg.Streams.Writable.Status ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.OrderedObservation.mk :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkObservation α ε → List (Whatwg.Streams.Writable.VisibleEvent ε) → Whatwg.Streams.Writable.OrderedObservation α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.OrderedObservation.sink :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.OrderedObservation α ε → Whatwg.Streams.Writable.SinkObservation α ε)

-- DESIRED
#check (@Whatwg.Streams.Writable.OrderedObservation.events :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.OrderedObservation α ε → List (Whatwg.Streams.Writable.VisibleEvent ε))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkJob.kind :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkJob α ε → Whatwg.Streams.Writable.SinkKind)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.SinkJob.request :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkJob α ε → Nat)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationKind :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkOperation α ε → Whatwg.Streams.Writable.SinkKind)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationRequest :
  ∀ {α ε : Type}, Whatwg.Streams.Writable.SinkOperation α ε → Nat)

-- SINKSETUP
#check (@Whatwg.Streams.Writable.SinkAlgorithm :
  Type)

-- SINKSETUP
#check (@Whatwg.Streams.Writable.SinkAlgorithm.fulfilled :
  Whatwg.Streams.Writable.SinkAlgorithm)

-- SINKSETUP
#check (@Whatwg.Streams.Writable.SinkAlgorithm.foreign :
  Nat → Whatwg.Streams.Writable.SinkAlgorithm)

-- GETBACKPRESSURE
#check (@Whatwg.Streams.Writable.sizeNonPositive :
  Whatwg.Streams.Writable.Size → Bool)

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.Control.returnUnit :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Writable.Control α ε)

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.Event.controllerReturned :
  ∀ {α ε : Type}, Nat → Whatwg.Streams.Writable.Event α ε)

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.VisibleEvent.controllerReturned :
  ∀ {ε : Type}, Nat → Whatwg.Streams.Writable.VisibleEvent ε)
