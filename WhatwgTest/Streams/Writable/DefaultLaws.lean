import Whatwg.Streams

/-! Frozen P5a exact algorithm-stage equations, 2026-09-05.
Public signature battery: DefaultContract. Graph: WRITABLE-PG-DEFAULT.
State/trace laws name the local sink-input or ordered view, or support those named views.
Invalid raw assertion states are outside the admitted-initial/reachability obligation. -/

set_option autoImplicit false

-- SIZE
#check (@Whatwg.Streams.Writable.size_eq :
  Whatwg.Streams.Writable.Size = Whatwg.Streams.Data.DyadicSize)

-- SIZE
#check (@Whatwg.Streams.Writable.sizes_eq :
  Whatwg.Streams.Writable.sizes = Whatwg.Streams.Data.DyadicSize.sizes)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromise_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.UnitPromise ε = Whatwg.Streams.Readable.PromiseState Unit ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromiseToShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.UnitPromise ε), Whatwg.Streams.Writable.unitPromiseToShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromiseFromShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Readable.PromiseState Unit ε), Whatwg.Streams.Writable.unitPromiseFromShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.unitPromise_roundtrip :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.UnitPromise ε),
    Whatwg.Streams.Writable.unitPromiseFromShared (Whatwg.Streams.Writable.unitPromiseToShared a) = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswer_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkAnswer ε = Whatwg.Streams.Readable.PullAnswer ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswerToShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkAnswer ε), Whatwg.Streams.Writable.sinkAnswerToShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswerFromShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Readable.PullAnswer ε), Whatwg.Streams.Writable.sinkAnswerFromShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkAnswer_roundtrip :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.sinkAnswerFromShared (Whatwg.Streams.Writable.sinkAnswerToShared a) = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturn_eq :
  ∀ {ε : Type}, Whatwg.Streams.Writable.SinkReturn ε = Whatwg.Streams.Readable.PullReturn ε)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturnToShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkReturn ε), Whatwg.Streams.Writable.sinkReturnToShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturnFromShared_eq :
  ∀ {ε : Type} (a : Whatwg.Streams.Readable.PullReturn ε), Whatwg.Streams.Writable.sinkReturnFromShared a = a)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkReturn_roundtrip :
  ∀ {ε : Type} (a : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.sinkReturnFromShared (Whatwg.Streams.Writable.sinkReturnToShared a) = a)

-- WRITERSETUP
#check (@Whatwg.Streams.Writable.initial_eq :
  ∀ {α ε : Type} (hwm : Whatwg.Streams.Writable.Size) (alg : Whatwg.Streams.Writable.Algorithms) (promiseSeed errorSeed : Nat),
    Whatwg.Streams.Writable.initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed =
      { status := .writable, queue := Whatwg.Streams.Data.Queue.empty Whatwg.Streams.Writable.sizes, highWaterMark := hwm,
        backpressure := Whatwg.Streams.Writable.sizeNonPositive hwm, algorithms := alg,
        readyPromise := promiseSeed, closedPromise := promiseSeed + 1,
        promises := [(promiseSeed, if Whatwg.Streams.Writable.sizeNonPositive hwm then .pending else .fulfilled ()),
          (promiseSeed + 1, .pending)], handled := [], writeRequests := [], closeState := .none,
        inFlightWrite := none, abortInFlight := none, pendingAbort := none, signalArgument := none,
        nextCall := 0, nextPromise := promiseSeed + 2, nextError := errorSeed,
        control := [], jobs := [], trace := [] })

-- WRITEOK
#check (@Whatwg.Streams.Writable.lookupPromise_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.lookupPromise s id = (s.promises.find? (fun p => p.1 == id)).map Prod.snd)

-- WRITE
#check (@Whatwg.Streams.Writable.freshPromise_pending :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.freshPromise s .pending =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .pending)],
          nextPromise := s.nextPromise + 1 }, s.nextPromise))

-- WRITE
#check (@Whatwg.Streams.Writable.freshPromise_fulfilled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.freshPromise s (.fulfilled ()) =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .fulfilled ())],
          nextPromise := s.nextPromise + 1,
          trace := s.trace ++ [.settled s.nextPromise (.ok ())] }, s.nextPromise))

-- WRITE
#check (@Whatwg.Streams.Writable.freshPromise_rejected :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.freshPromise s (.rejected e) =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .rejected e)],
          nextPromise := s.nextPromise + 1,
          trace := s.trace ++ [.settled s.nextPromise (.error e)] }, s.nextPromise))

-- WRITEOK
#check (@Whatwg.Streams.Writable.settle_pending :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat) (a : Except (Whatwg.Streams.Boundary.Exception ε) Unit),
    Whatwg.Streams.Writable.lookupPromise s id = some .pending →
    Whatwg.Streams.Writable.settle s id a = { s with
      promises := s.promises.map (fun p => if p.1 == id then
        (id, match a with | .ok _ => .fulfilled () | .error e => .rejected e) else p),
      trace := s.trace ++ [.settled id a] })

-- WRITEOK
#check (@Whatwg.Streams.Writable.settle_other :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat) (a : Except (Whatwg.Streams.Boundary.Exception ε) Unit),
    Whatwg.Streams.Writable.lookupPromise s id ≠ some .pending → Whatwg.Streams.Writable.settle s id a = s)

-- READYERROR
#check (@Whatwg.Streams.Writable.markHandled_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (id : Nat),
    Whatwg.Streams.Writable.markHandled s id = if id ∈ s.handled then s else { s with handled := s.handled ++ [id] })

-- READYERROR
#check (@Whatwg.Streams.Writable.ensureReadyRejected_pending :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.lookupPromise s s.readyPromise = some .pending →
    Whatwg.Streams.Writable.ensureReadyRejected s e = Whatwg.Streams.Writable.markHandled (Whatwg.Streams.Writable.settle s s.readyPromise (.error e)) s.readyPromise)

-- READYERROR
#check (@Whatwg.Streams.Writable.ensureReadyRejected_other :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (e : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.lookupPromise s s.readyPromise ≠ some .pending →
    Whatwg.Streams.Writable.ensureReadyRejected s e =
      let r := Whatwg.Streams.Writable.freshPromise s (.rejected e)
      Whatwg.Streams.Writable.markHandled { r.1 with readyPromise := r.2 } r.2)

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.updateBackpressure_same :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (b : Bool), s.backpressure = b → Whatwg.Streams.Writable.updateBackpressure s b = s)

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.updateBackpressure_true :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), s.backpressure = false →
    Whatwg.Streams.Writable.updateBackpressure s true =
      let r := Whatwg.Streams.Writable.freshPromise s .pending
      { r.1 with readyPromise := r.2, backpressure := true })

-- BACKPRESSURE
#check (@Whatwg.Streams.Writable.updateBackpressure_false :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), s.backpressure = true →
    Whatwg.Streams.Writable.updateBackpressure s false =
      { Whatwg.Streams.Writable.settle s s.readyPromise (.ok ()) with backpressure := false })

-- DESIRED
#check (@Whatwg.Streams.Writable.desiredSize_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.desiredSize s = match s.status with
      | .writable => some (Whatwg.Streams.Writable.sizes.sub s.highWaterMark s.queue.totalSize)
      | .closed => some Whatwg.Streams.Writable.sizes.zero
      | .erroring _ | .errored _ => none)

-- GETBACKPRESSURE; CONTROLLERDESIRED
#check (@Whatwg.Streams.Writable.getBackpressure_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.getBackpressure s = Whatwg.Streams.Writable.sizeNonPositive (Whatwg.Streams.Writable.sizes.sub s.highWaterMark s.queue.totalSize))

-- CLEAR
#check (@Whatwg.Streams.Writable.clearAlgorithms_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.clearAlgorithms s =
    { s with algorithms := { size := none, write := none, close := none, abort := none } })

-- CLOSEPENDING
#check (@Whatwg.Streams.Writable.closeQueuedOrInFlight_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.closeQueuedOrInFlight s = match s.closeState with | .none => false | _ => true)

-- INFLIGHT
#check (@Whatwg.Streams.Writable.hasInFlight_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.hasInFlight s = s.inFlightWrite.isSome ||
      (match s.closeState with | .inFlight _ _ => true | _ => false))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.externalFrontier_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.externalFrontier s = match s.control with
      | [] | .awaitSize _ _ :: _ | .awaitSink _ :: _ | .awaitSignal _ _ :: _ => true
      | _ => false)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationKind_eq :
  ∀ {α ε : Type} (op : Whatwg.Streams.Writable.SinkOperation α ε),
    Whatwg.Streams.Writable.operationKind op = match op with | .write _ _ => .write | .close _ => .close | .abort _ _ => .abort)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationRequest_eq :
  ∀ {α ε : Type} (op : Whatwg.Streams.Writable.SinkOperation α ε),
    Whatwg.Streams.Writable.operationRequest op = match op with | .write id _ | .close id | .abort id _ => id)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.operationPhase_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (kind : Whatwg.Streams.Writable.SinkKind) (id : Nat),
    Whatwg.Streams.Writable.operationPhase s kind id =
      let slot := match kind with
        | .write => s.inFlightWrite
        | .close => match s.closeState with | .inFlight n phase => some (n, phase) | _ => none
        | .abort => s.abortInFlight
      slot.bind (fun p => if p.1 == id then some p.2 else none))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.setOperationPhase_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (op : Whatwg.Streams.Writable.SinkOperation α ε) (phase : Whatwg.Streams.Writable.OperationPhase),
    Whatwg.Streams.Writable.setOperationPhase s op phase = match op with
      | .write id _ => { s with inFlightWrite := some (id, phase) }
      | .close id => { s with closeState := .inFlight id phase }
      | .abort id _ => { s with abortInFlight := some (id, phase) })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.attachSink_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (op : Whatwg.Streams.Writable.SinkOperation α ε) (ret : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.attachSink s op ret =
      let b := match op with | .write _ _ => s | .close _ | .abort _ _ => Whatwg.Streams.Writable.clearAlgorithms s
      match ret with
      | .pending => Whatwg.Streams.Writable.setOperationPhase b op .awaiting
      | .settled answer =>
        { Whatwg.Streams.Writable.setOperationPhase b op .queued with
          jobs := b.jobs ++ [⟨Whatwg.Streams.Writable.operationKind op, Whatwg.Streams.Writable.operationRequest op, answer⟩] })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.invokeSink_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (op : Whatwg.Streams.Writable.SinkOperation α ε),
    Whatwg.Streams.Writable.invokeSink s op =
      let alg := match op with
        | .write _ _ => s.algorithms.write
        | .close _ => s.algorithms.close
        | .abort _ _ => s.algorithms.abort
      match alg with
      | none => none
      | some .fulfilled => some (Whatwg.Streams.Writable.attachSink s op (.settled .fulfilled))
      | some (.foreign name) => some
        { Whatwg.Streams.Writable.setOperationPhase s op .invoking with
          control := .awaitSink op :: s.control,
          trace := s.trace ++ [.sinkCalled name op] })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.acceptAnswer_waiting :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (kind : Whatwg.Streams.Writable.SinkKind) (id : Nat) (a : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.operationPhase s kind id = some .awaiting →
    Whatwg.Streams.Writable.acceptAnswer s kind id a =
      let b := match kind with
        | .write => { s with inFlightWrite := some (id, .queued) }
        | .close => { s with closeState := .inFlight id .queued }
        | .abort => { s with abortInFlight := some (id, .queued) }
      some { b with jobs := s.jobs ++ [⟨kind, id, a⟩] })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.acceptAnswer_other :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (kind : Whatwg.Streams.Writable.SinkKind) (id : Nat) (a : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.operationPhase s kind id ≠ some .awaiting → Whatwg.Streams.Writable.acceptAnswer s kind id a = none)

-- GETBACKPRESSURE
#check (@Whatwg.Streams.Writable.sizeNonPositive_eq :
  ∀ (v : Whatwg.Streams.Writable.Size), Whatwg.Streams.Writable.sizeNonPositive v =
    match v with | .finite units => decide (units ≤ 0) | .negInfinity => true | _ => false)

-- WRITE
#check (@Whatwg.Streams.Writable.decide_blocked :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (d : Whatwg.Streams.Writable.Decision α ε), Whatwg.Streams.Writable.externalFrontier s = false → Whatwg.Streams.Writable.decide s d = none)

-- WRITE
#check (@Whatwg.Streams.Writable.decide_write :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (chunk : α), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s (.write chunk) = some
      { s with nextCall := s.nextCall + 1, control := .getSize s.nextCall chunk :: s.control })

-- CLOSE
#check (@Whatwg.Streams.Writable.decide_close :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) , Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s (.close) = some
      { s with nextCall := s.nextCall + 1, control := .beginClose s.nextCall :: s.control })

-- ABORT
#check (@Whatwg.Streams.Writable.decide_abort :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (reason : Whatwg.Streams.Boundary.Exception ε), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s (.abort reason) = some
      { s with nextCall := s.nextCall + 1, control := .beginAbort s.nextCall reason :: s.control })

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.decide_controllerError :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (reason : Whatwg.Streams.Boundary.Exception ε), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s (.controllerError reason) = some
      { s with
        nextCall := s.nextCall + 1,
        control := .controllerError reason :: .returnUnit s.nextCall :: s.control })

-- READYGET
#check (@Whatwg.Streams.Writable.decide_queryReady :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s .queryReady = some
      { s with nextCall := s.nextCall + 1, trace := s.trace ++ [.readyRead s.nextCall s.readyPromise] })

-- CLOSEDGET
#check (@Whatwg.Streams.Writable.decide_queryClosed :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s .queryClosed = some
      { s with nextCall := s.nextCall + 1, trace := s.trace ++ [.closedRead s.nextCall s.closedPromise] })

-- DESIRED
#check (@Whatwg.Streams.Writable.decide_queryDesiredSize :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.externalFrontier s = true →
    Whatwg.Streams.Writable.decide s .queryDesiredSize = some
      { s with nextCall := s.nextCall + 1, trace := s.trace ++ [.desiredSizeRead s.nextCall (Whatwg.Streams.Writable.desiredSize s)] })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.decide_answer :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (kind : Whatwg.Streams.Writable.SinkKind) (id : Nat) (answer : Whatwg.Streams.Writable.SinkAnswer ε),
    Whatwg.Streams.Writable.externalFrontier s = true → Whatwg.Streams.Writable.decide s (.answer kind id answer) =
      Whatwg.Streams.Writable.acceptAnswer s kind id answer)

-- SIZE
#check (@Whatwg.Streams.Writable.returnSize_value :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size),
    Whatwg.Streams.Writable.decide { s with control := .awaitSize call chunk :: tail } (.returnSize (.value size)) =
      some { s with control := .afterSize call chunk size :: tail })

-- SIZE
#check (@Whatwg.Streams.Writable.returnSize_thrown :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (reason : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.decide { s with control := .awaitSize call chunk :: tail } (.returnSize (.thrown reason)) =
      some { s with control := .errorIfNeeded reason :: .afterSize call chunk Whatwg.Streams.Writable.sizes.one :: tail })

-- SIZE
#check (@Whatwg.Streams.Writable.returnSize_unmatched :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (a : Whatwg.Streams.Data.SizeAnswer Whatwg.Streams.Writable.Size (Whatwg.Streams.Boundary.Exception ε)),
    (∀ call chunk tail, s.control ≠ .awaitSize call chunk :: tail) →
    Whatwg.Streams.Writable.decide s (.returnSize a) = none)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.returnSink_invoking :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (op : Whatwg.Streams.Writable.SinkOperation α ε) (ret : Whatwg.Streams.Writable.SinkReturn ε),
    Whatwg.Streams.Writable.operationPhase s (Whatwg.Streams.Writable.operationKind op) (Whatwg.Streams.Writable.operationRequest op) = some .invoking →
    Whatwg.Streams.Writable.decide { s with control := .awaitSink op :: tail } (.returnSink ret) =
      some (Whatwg.Streams.Writable.attachSink { s with control := tail } op ret))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.returnSink_unmatched :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (ret : Whatwg.Streams.Writable.SinkReturn ε),
    (∀ op tail, s.control ≠ .awaitSink op :: tail ∨
      Whatwg.Streams.Writable.operationPhase s (Whatwg.Streams.Writable.operationKind op) (Whatwg.Streams.Writable.operationRequest op) ≠ some .invoking) →
    Whatwg.Streams.Writable.decide s (.returnSink ret) = none)

-- ABORT
#check (@Whatwg.Streams.Writable.returnSignal_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.decide { s with control := .awaitSignal call reason :: tail } .returnSignal =
      some { s with control := .afterSignal call reason :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.returnSignal_unmatched :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    (∀ call reason tail, s.control ≠ .awaitSignal call reason :: tail) →
    Whatwg.Streams.Writable.decide s .returnSignal = none)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.tick_foreign_marker :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), s.control ≠ [] → Whatwg.Streams.Writable.externalFrontier s = true → Whatwg.Streams.Writable.tick s = none)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.tick_no_job :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), s.control = [] → s.jobs = [] → Whatwg.Streams.Writable.tick s = none)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.tick_job_fifo :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (job : Whatwg.Streams.Writable.SinkJob α ε) (jobs : List (Whatwg.Streams.Writable.SinkJob α ε)),
    Whatwg.Streams.Writable.tick { s with control := [], jobs := job :: jobs } =
      some { s with control := [.react job], jobs := jobs })

-- WRITE
#check (@Whatwg.Streams.Writable.tick_returnPromise :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call id : Nat),
    Whatwg.Streams.Writable.tick { s with control := .returnPromise call id :: tail } =
      some { s with control := tail, trace := s.trace ++ [.returned call id] })

-- PUBLICERROR
#check (@Whatwg.Streams.Writable.tick_returnUnit :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat),
    Whatwg.Streams.Writable.tick { s with control := .returnUnit call :: tail } =
      some { s with control := tail, trace := s.trace ++ [.controllerReturned call] })

-- SIZE
#check (@Whatwg.Streams.Writable.tick_getSize :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α),
    Whatwg.Streams.Writable.tick { s with control := .getSize call chunk :: tail } =
      some (match s.algorithms.size with
        | none | some .one => { s with control := .afterSize call chunk Whatwg.Streams.Writable.sizes.one :: tail }
        | some (.foreign name) => { s with
            control := .awaitSize call chunk :: tail,
            trace := s.trace ++ [.sizeCalled name call chunk] }))

-- WRITE
#check (@Whatwg.Streams.Writable.tick_afterSize_errored :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.status = .errored reason →
    Whatwg.Streams.Writable.tick { s with control := .afterSize call chunk size :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } (.rejected reason)
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- WRITE
#check (@Whatwg.Streams.Writable.tick_afterSize_closing :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size),
    (∀ reason, s.status ≠ .errored reason) →
    (Whatwg.Streams.Writable.closeQueuedOrInFlight s = true ∨ s.status = .closed) →
    Whatwg.Streams.Writable.tick { s with control := .afterSize call chunk size :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail, nextError := s.nextError + 1 }
        (.rejected (.typeError s.nextError))
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- WRITE
#check (@Whatwg.Streams.Writable.tick_afterSize_erroring :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.status = .erroring reason → Whatwg.Streams.Writable.closeQueuedOrInFlight s = false →
    Whatwg.Streams.Writable.tick { s with control := .afterSize call chunk size :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } (.rejected reason)
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- WRITE
#check (@Whatwg.Streams.Writable.tick_afterSize_writable :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size),
    s.status = .writable → Whatwg.Streams.Writable.closeQueuedOrInFlight s = false →
    Whatwg.Streams.Writable.tick { s with control := .afterSize call chunk size :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } .pending
      some { r.1 with
        writeRequests := s.writeRequests ++ [r.2],
        control := .enqueueWrite chunk size :: .returnPromise call r.2 :: tail })

-- ENQUEUE
#check (@Whatwg.Streams.Writable.tick_enqueueWrite_error :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (chunk : α) (size : Whatwg.Streams.Writable.Size),
    Whatwg.Streams.Data.enqueueValueWithSize Whatwg.Streams.Writable.sizes s.queue (.chunk chunk) size = .error .rangeError →
    Whatwg.Streams.Writable.tick { s with control := .enqueueWrite chunk size :: tail } =
      some { s with
        nextError := s.nextError + 1,
        control := .errorIfNeeded (.rangeError s.nextError) :: tail })

-- ENQUEUE
#check (@Whatwg.Streams.Writable.tick_enqueueWrite_ok :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (chunk : α) (size : Whatwg.Streams.Writable.Size) (queue : Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size),
    Whatwg.Streams.Data.enqueueValueWithSize Whatwg.Streams.Writable.sizes s.queue (.chunk chunk) size = .ok queue →
    Whatwg.Streams.Writable.tick { s with control := .enqueueWrite chunk size :: tail } =
      let b := { s with queue := queue, control := .advance :: tail }
      some (match s.status with
        | .writable => if Whatwg.Streams.Writable.closeQueuedOrInFlight s then b else
            Whatwg.Streams.Writable.updateBackpressure b (Whatwg.Streams.Writable.getBackpressure b)
        | _ => b))

-- ADVANCE
#check (@Whatwg.Streams.Writable.tick_advance_busy :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (phase : Whatwg.Streams.Writable.OperationPhase),
    s.inFlightWrite = some (id, phase) →
    Whatwg.Streams.Writable.tick { s with control := .advance :: tail } = some { s with control := tail })

-- ADVANCE
#check (@Whatwg.Streams.Writable.tick_advance_erroring :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.inFlightWrite = none → s.status = .erroring reason →
    Whatwg.Streams.Writable.tick { s with control := .advance :: tail } =
      some { s with control := .finishErroring :: tail })

-- ADVANCE
#check (@Whatwg.Streams.Writable.tick_advance_empty :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)), s.inFlightWrite = none → s.status = .writable →
    s.queue.entries = [] → Whatwg.Streams.Writable.tick { s with control := .advance :: tail } =
      some { s with control := tail })

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.tick_advance_write :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (ids : List Nat) (chunk : α) (size : Whatwg.Streams.Writable.Size)
    (items : List (Whatwg.Streams.Data.QueueEntry (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size)),
    s.inFlightWrite = none → s.status = .writable →
    s.queue.entries = ⟨.chunk chunk, size⟩ :: items → s.writeRequests = id :: ids →
    Whatwg.Streams.Writable.tick { s with control := .advance :: tail } =
      Whatwg.Streams.Writable.invokeSink { s with
        control := tail, writeRequests := ids,
        inFlightWrite := some (id, .invoking) } (.write id chunk))

-- PROCESSCLOSE
#check (@Whatwg.Streams.Writable.tick_advance_close :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (queue : Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size),
    s.inFlightWrite = none → s.status = .writable → s.closeState = .queued id →
    Whatwg.Streams.Data.dequeueValue Whatwg.Streams.Writable.sizes s.queue = some (.close, queue) → queue.entries = [] →
    Whatwg.Streams.Writable.tick { s with control := .advance :: tail } =
      Whatwg.Streams.Writable.invokeSink { s with
        control := tail, queue := queue,
        closeState := .inFlight id .invoking } (.close id))

-- PUBLICCLOSE; CLOSE
#check (@Whatwg.Streams.Writable.tick_beginClose_rejected :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat),
    (Whatwg.Streams.Writable.closeQueuedOrInFlight s = true ∨ s.status = .closed ∨ ∃ e, s.status = .errored e) →
    Whatwg.Streams.Writable.tick { s with control := .beginClose call :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail, nextError := s.nextError + 1 }
        (.rejected (.typeError s.nextError))
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- CLOSE
#check (@Whatwg.Streams.Writable.tick_beginClose_admitted :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (queue : Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Whatwg.Streams.Writable.closeQueuedOrInFlight s = false →
    Whatwg.Streams.Data.enqueueValueWithSize Whatwg.Streams.Writable.sizes s.queue .close Whatwg.Streams.Writable.sizes.zero = .ok queue →
    Whatwg.Streams.Writable.tick { s with control := .beginClose call :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } .pending
      let b := { r.1 with
        closeState := .queued r.2, queue := queue,
        control := .advance :: .returnPromise call r.2 :: tail }
      some (match s.status with
        | .writable => if s.backpressure then Whatwg.Streams.Writable.settle b s.readyPromise (.ok ()) else b
        | _ => b))

-- ABORT
#check (@Whatwg.Streams.Writable.tick_beginAbort_terminal :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    (s.status = .closed ∨ ∃ e, s.status = .errored e) →
    Whatwg.Streams.Writable.tick { s with control := .beginAbort call reason :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } (.fulfilled ())
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_afterSignal_terminal :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    (s.status = .closed ∨ ∃ e, s.status = .errored e) →
    Whatwg.Streams.Writable.tick { s with control := .afterSignal call reason :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } (.fulfilled ())
      some { r.1 with control := .returnPromise call r.2 :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_beginAbort_signal :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.signalArgument = none →
    Whatwg.Streams.Writable.tick { s with control := .beginAbort call reason :: tail } =
      some { s with
        signalArgument := some reason, control := .awaitSignal call reason :: tail,
        trace := s.trace ++ [.signalCalled call reason] })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_beginAbort_signaled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason first : Whatwg.Streams.Boundary.Exception ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.signalArgument = some first →
    Whatwg.Streams.Writable.tick { s with control := .beginAbort call reason :: tail } =
      some { s with control := .afterSignal call reason :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_afterSignal_existing :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call id : Nat) (reason : Whatwg.Streams.Boundary.Exception ε)
    (pending : Whatwg.Streams.Writable.PendingAbort ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.pendingAbort = some pending →
    (match pending with | .requested n _ | .alreadyErroring n => n) = id →
    Whatwg.Streams.Writable.tick { s with control := .afterSignal call reason :: tail } =
      some { s with control := .returnPromise call id :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_afterSignal_writable :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.status = .writable → s.pendingAbort = none →
    Whatwg.Streams.Writable.tick { s with control := .afterSignal call reason :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } .pending
      some { r.1 with
        pendingAbort := some (.requested r.2 reason),
        control := .startErroring reason :: .returnPromise call r.2 :: tail })

-- ABORT
#check (@Whatwg.Streams.Writable.tick_afterSignal_erroring :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (call : Nat) (reason stored : Whatwg.Streams.Boundary.Exception ε),
    s.status = .erroring stored → s.pendingAbort = none →
    Whatwg.Streams.Writable.tick { s with control := .afterSignal call reason :: tail } =
      let r := Whatwg.Streams.Writable.freshPromise { s with control := tail } .pending
      some { r.1 with
        pendingAbort := some (.alreadyErroring r.2),
        control := .returnPromise call r.2 :: tail })

-- ERRORIF
#check (@Whatwg.Streams.Writable.tick_errorIfNeeded :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (reason : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.tick { s with control := .errorIfNeeded reason :: tail } =
      some { s with
        control := match s.status with
        | .writable => .controllerError reason :: tail | _ => tail })

-- PUBLICERROR; ERROR
#check (@Whatwg.Streams.Writable.tick_controllerError :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (reason : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.tick { s with control := .controllerError reason :: tail } =
      some (match s.status with
        | .writable => Whatwg.Streams.Writable.clearAlgorithms { s with control := .startErroring reason :: tail }
        | _ => { s with control := tail }))

-- STARTERROR
#check (@Whatwg.Streams.Writable.tick_startErroring :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (reason : Whatwg.Streams.Boundary.Exception ε), s.status = .writable →
    Whatwg.Streams.Writable.tick { s with control := .startErroring reason :: tail } =
      some (Whatwg.Streams.Writable.ensureReadyRejected
        { s with
          status := .erroring reason,
          control := if Whatwg.Streams.Writable.hasInFlight s then tail else .finishErroring :: tail } reason))

-- DEAL
#check (@Whatwg.Streams.Writable.tick_dealRejection :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (reason : Whatwg.Streams.Boundary.Exception ε),
    Whatwg.Streams.Writable.tick { s with control := .dealRejection reason :: tail } =
      match s.status with
      | .writable => some { s with control := .startErroring reason :: tail }
      | .erroring _ => some { s with control := .finishErroring :: tail }
      | _ => none)

-- FINISHERROR; ERRORSTEPS; ABORTSTEPS
#check (@Whatwg.Streams.Writable.tick_finishErroring :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (stored : Whatwg.Streams.Boundary.Exception ε),
    s.status = .erroring stored → Whatwg.Streams.Writable.hasInFlight s = false →
    Whatwg.Streams.Writable.tick { s with control := .finishErroring :: tail } =
      let b := s.writeRequests.foldl (fun st id => Whatwg.Streams.Writable.settle st id (.error stored))
        { s with
          status := .errored stored, queue := Whatwg.Streams.Data.Queue.empty Whatwg.Streams.Writable.sizes,
          writeRequests := [], pendingAbort := none, control := tail }
      match s.pendingAbort with
      | none => some { b with control := .rejectCloseClosed stored :: tail }
      | some (.alreadyErroring id) =>
        some { Whatwg.Streams.Writable.settle b id (.error stored) with control := .rejectCloseClosed stored :: tail }
      | some (.requested id reason) => Whatwg.Streams.Writable.invokeSink b (.abort id reason))

-- FINISHERROR; INFLIGHT
#check (@Whatwg.Streams.Writable.tick_finishErroring_inFlight :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)), Whatwg.Streams.Writable.hasInFlight s = true →
    Whatwg.Streams.Writable.tick { s with control := .finishErroring :: tail } = none)

-- REJECTCLOSED
#check (@Whatwg.Streams.Writable.tick_rejectCloseClosed :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (stored : Whatwg.Streams.Boundary.Exception ε), s.status = .errored stored →
    (∀ id phase, s.closeState ≠ .inFlight id phase) →
    Whatwg.Streams.Writable.tick { s with control := .rejectCloseClosed stored :: tail } =
      let b := match s.closeState with
        | .queued id => { Whatwg.Streams.Writable.settle s id (.error stored) with closeState := .none }
        | _ => s
      some (Whatwg.Streams.Writable.markHandled (Whatwg.Streams.Writable.settle { b with control := tail }
        b.closedPromise (.error stored)) b.closedPromise))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.tick_react_unmatched :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (job : Whatwg.Streams.Writable.SinkJob α ε),
    Whatwg.Streams.Writable.operationPhase s job.kind job.request ≠ some .queued →
    Whatwg.Streams.Writable.tick { s with control := .react job :: tail } = none)

-- WRITEOK
#check (@Whatwg.Streams.Writable.tick_write_fulfilled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (chunk : α) (queue : Whatwg.Streams.Data.Queue (Whatwg.Streams.Writable.QueueItem α) Whatwg.Streams.Writable.Size),
    s.inFlightWrite = some (id, .queued) →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Whatwg.Streams.Data.dequeueValue Whatwg.Streams.Writable.sizes s.queue = some (.chunk chunk, queue) →
    Whatwg.Streams.Writable.tick { s with control := .react ⟨.write, id, .fulfilled⟩ :: tail } =
      let b := { Whatwg.Streams.Writable.settle s id (.ok ()) with
        inFlightWrite := none, queue := queue,
        control := .advance :: tail }
      some (match s.status with
        | .writable => if Whatwg.Streams.Writable.closeQueuedOrInFlight s then b else
            Whatwg.Streams.Writable.updateBackpressure b (Whatwg.Streams.Writable.getBackpressure b)
        | _ => b))

-- WRITEFAIL
#check (@Whatwg.Streams.Writable.tick_write_rejected :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.inFlightWrite = some (id, .queued) →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Whatwg.Streams.Writable.tick { s with control := .react ⟨.write, id, .rejected reason⟩ :: tail } =
      let b := match s.status with | .writable => Whatwg.Streams.Writable.clearAlgorithms s | _ => s
      some { Whatwg.Streams.Writable.settle b id (.error reason) with
        inFlightWrite := none,
        control := .dealRejection reason :: tail })

-- CLOSEOK
#check (@Whatwg.Streams.Writable.tick_close_fulfilled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat),
    s.closeState = .inFlight id .queued →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Whatwg.Streams.Writable.tick { s with control := .react ⟨.close, id, .fulfilled⟩ :: tail } =
      let b := { Whatwg.Streams.Writable.settle s id (.ok ()) with closeState := .none, control := tail }
      let c := match s.status, s.pendingAbort with
        | .erroring _, some (.requested abortId _) => Whatwg.Streams.Writable.settle b abortId (.ok ())
        | .erroring _, some (.alreadyErroring abortId) => Whatwg.Streams.Writable.settle b abortId (.ok ())
        | _, _ => b
      some (Whatwg.Streams.Writable.settle { c with status := .closed, pendingAbort := none } c.closedPromise (.ok ())))

-- CLOSEFAIL
#check (@Whatwg.Streams.Writable.tick_close_rejected :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (reason : Whatwg.Streams.Boundary.Exception ε),
    s.closeState = .inFlight id .queued →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Whatwg.Streams.Writable.tick { s with control := .react ⟨.close, id, .rejected reason⟩ :: tail } =
      let b := { Whatwg.Streams.Writable.settle s id (.error reason) with closeState := .none }
      let c := match s.pendingAbort with
        | some (.requested abortId _) | some (.alreadyErroring abortId) =>
          Whatwg.Streams.Writable.settle b abortId (.error reason)
        | none => b
      some { c with pendingAbort := none, control := .dealRejection reason :: tail })

-- ABORTSTEPS
#check (@Whatwg.Streams.Writable.tick_abort_settled :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (tail : List (Whatwg.Streams.Writable.Control α ε)) (id : Nat) (stored : Whatwg.Streams.Boundary.Exception ε) (a : Whatwg.Streams.Writable.SinkAnswer ε),
    s.abortInFlight = some (id, .queued) → s.status = .errored stored →
    Whatwg.Streams.Writable.tick { s with control := .react ⟨.abort, id, a⟩ :: tail } =
      let result := match a with | .fulfilled => .ok () | .rejected e => .error e
      some { Whatwg.Streams.Writable.settle s id result with
        abortInFlight := none,
        control := .rejectCloseClosed stored :: tail })

-- ADVANCE
#check (@Whatwg.Streams.Writable.step_iff :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (d : Option (Whatwg.Streams.Writable.Decision α ε)) (t : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.Step s d t ↔ match d with | none => Whatwg.Streams.Writable.tick s = some t | some a => Whatwg.Streams.Writable.decide s a = some t)

-- ADVANCE
#check (@Whatwg.Streams.Writable.reaches_nil :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (t : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.Reaches s [] t ↔ s = t)

-- ADVANCE
#check (@Whatwg.Streams.Writable.reaches_cons :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (d : Option (Whatwg.Streams.Writable.Decision α ε)) (ds : List (Option (Whatwg.Streams.Writable.Decision α ε)))
    (t : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.Reaches s (d :: ds) t ↔
      ∃ u, Whatwg.Streams.Writable.Step s d u ∧ Whatwg.Streams.Writable.Reaches u ds t)

-- ADVANCE
#check (@Whatwg.Streams.Writable.reaches_append_iff :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (ds es : List (Option (Whatwg.Streams.Writable.Decision α ε))) (t : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.Reaches s (ds ++ es) t ↔ ∃ u, Whatwg.Streams.Writable.Reaches s ds u ∧ Whatwg.Streams.Writable.Reaches u es t)

-- ADVANCE
#check (@Whatwg.Streams.Writable.step_deterministic :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε) (d : Option (Whatwg.Streams.Writable.Decision α ε)) (t u : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.Step s d t → Whatwg.Streams.Writable.Step s d u → t = u)

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.sinkInput_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.sinkInput s = s.trace.filterMap (fun e =>
    match e with | .sinkCalled _ (.write _ chunk) => some chunk | _ => none))

-- DESIRED
#check (@Whatwg.Streams.Writable.visibleEvents_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.visibleEvents s = s.trace.filterMap (fun e =>
    match e with
    | .settled id a => some (.settled id a)
    | .returned call id => some (.returned call id)
    | .readyRead call id => some (.readyRead call id)
    | .closedRead call id => some (.closedRead call id)
    | .desiredSizeRead call size => some (.desiredSizeRead call size)
    | .controllerReturned call => some (.controllerReturned call)
    | _ => none))

-- WRITEOK
#check (@Whatwg.Streams.Writable.settlementTrace_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.settlementTrace s = s.trace.filterMap (fun e =>
    match e with | .settled id a => some (id, a) | _ => none))

-- PROCESSWRITE
#check (@Whatwg.Streams.Writable.observeSink_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.observeSink s = ⟨Whatwg.Streams.Writable.sinkInput s, s.status⟩)

-- DESIRED
#check (@Whatwg.Streams.Writable.observeOrdered_eq :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), Whatwg.Streams.Writable.observeOrdered s = ⟨Whatwg.Streams.Writable.observeSink s, Whatwg.Streams.Writable.visibleEvents s⟩)

-- DESIRED
#check (@Whatwg.Streams.Writable.observeOrdered_toSink :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε), (Whatwg.Streams.Writable.observeOrdered s).sink = Whatwg.Streams.Writable.observeSink s)
