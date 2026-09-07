import Whatwg.Streams.Writable.Step

/-!
# Frozen writable stage and view laws

WRITABLE-PG-DEFAULT owns these exact statements. State equations support the
local sink-input and ordered candidate views; DB-04 and global embeddings remain
separate obligations. The breaker battery ascribes every theorem below.
-/

namespace Whatwg.Streams.Writable

/--
`op.writable-stream-default-controller-get-chunk-size`:
size eq for the local candidate observations.
-/
theorem size_eq :
  Size = Data.DyadicSize := by
  intros
  rfl

/--
`op.writable-stream-default-controller-get-chunk-size`:
sizes eq for the local candidate observations.
-/
theorem sizes_eq :
  sizes = Data.DyadicSize.sizes := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
unitPromise eq for the local candidate observations.
-/
theorem unitPromise_eq :
  ∀ {ε : Type}, UnitPromise ε = Readable.PromiseState Unit ε := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
unitPromiseToShared eq for the local candidate observations.
-/
theorem unitPromiseToShared_eq :
  ∀ {ε : Type} (a : UnitPromise ε), unitPromiseToShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
unitPromiseFromShared eq for the local candidate observations.
-/
theorem unitPromiseFromShared_eq :
  ∀ {ε : Type} (a : Readable.PromiseState Unit ε), unitPromiseFromShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
unitPromise roundtrip for the local candidate observations.
-/
theorem unitPromise_roundtrip :
  ∀ {ε : Type} (a : UnitPromise ε),
    unitPromiseFromShared (unitPromiseToShared a) = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkAnswer eq for the local candidate observations.
-/
theorem sinkAnswer_eq :
  ∀ {ε : Type}, SinkAnswer ε = Readable.PullAnswer ε := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkAnswerToShared eq for the local candidate observations.
-/
theorem sinkAnswerToShared_eq :
  ∀ {ε : Type} (a : SinkAnswer ε), sinkAnswerToShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkAnswerFromShared eq for the local candidate observations.
-/
theorem sinkAnswerFromShared_eq :
  ∀ {ε : Type} (a : Readable.PullAnswer ε), sinkAnswerFromShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkAnswer roundtrip for the local candidate observations.
-/
theorem sinkAnswer_roundtrip :
  ∀ {ε : Type} (a : SinkAnswer ε),
    sinkAnswerFromShared (sinkAnswerToShared a) = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkReturn eq for the local candidate observations.
-/
theorem sinkReturn_eq :
  ∀ {ε : Type}, SinkReturn ε = Readable.PullReturn ε := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkReturnToShared eq for the local candidate observations.
-/
theorem sinkReturnToShared_eq :
  ∀ {ε : Type} (a : SinkReturn ε), sinkReturnToShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkReturnFromShared eq for the local candidate observations.
-/
theorem sinkReturnFromShared_eq :
  ∀ {ε : Type} (a : Readable.PullReturn ε), sinkReturnFromShared a = a := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
sinkReturn roundtrip for the local candidate observations.
-/
theorem sinkReturn_roundtrip :
  ∀ {ε : Type} (a : SinkReturn ε),
    sinkReturnFromShared (sinkReturnToShared a) = a := by
  intros
  rfl

/--
`op.set-up-writable-stream-default-writer`:
initial eq for the local candidate observations.
-/
theorem initial_eq :
  ∀ {α ε : Type} (hwm : Size) (alg : Algorithms) (promiseSeed errorSeed : Nat),
    initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed =
      { status := .writable, queue := Data.Queue.empty sizes, highWaterMark := hwm,
        backpressure := sizeNonPositive hwm, algorithms := alg,
        readyPromise := promiseSeed, closedPromise := promiseSeed + 1,
        promises := [(promiseSeed, if sizeNonPositive hwm then .pending else .fulfilled ()),
          (promiseSeed + 1, .pending)], handled := [], writeRequests := [], closeState := .none,
        inFlightWrite := none, abortInFlight := none, pendingAbort := none, signalArgument := none,
        nextCall := 0, nextPromise := promiseSeed + 2, nextError := errorSeed,
        control := [], jobs := [], trace := [] } := by
  intros
  rfl

/--
`op.writable-stream-finish-in-flight-write`:
lookupPromise eq for the local candidate observations.
-/
theorem lookupPromise_eq :
  ∀ {α ε : Type} (s : State α ε) (id : Nat),
    lookupPromise s id = (s.promises.find? (fun p => p.1 == id)).map Prod.snd := by
  intros
  rfl

/--
`op.writable-stream-default-writer-write`:
freshPromise pending for the local candidate observations.
-/
theorem freshPromise_pending :
  ∀ {α ε : Type} (s : State α ε),
    freshPromise s .pending =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .pending)],
          nextPromise := s.nextPromise + 1 }, s.nextPromise) := by
  intros
  rfl

/--
`op.writable-stream-default-writer-write`:
freshPromise fulfilled for the local candidate observations.
-/
theorem freshPromise_fulfilled :
  ∀ {α ε : Type} (s : State α ε),
    freshPromise s (.fulfilled ()) =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .fulfilled ())],
          nextPromise := s.nextPromise + 1,
          trace := s.trace ++ [.settled s.nextPromise (.ok ())] }, s.nextPromise) := by
  intros
  rfl

/--
`op.writable-stream-default-writer-write`:
freshPromise rejected for the local candidate observations.
-/
theorem freshPromise_rejected :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    freshPromise s (.rejected e) =
      ({ s with
          promises := s.promises ++ [(s.nextPromise, .rejected e)],
          nextPromise := s.nextPromise + 1,
          trace := s.trace ++ [.settled s.nextPromise (.error e)] }, s.nextPromise) := by
  intros
  rfl

/--
`op.writable-stream-finish-in-flight-write`:
settle pending for the local candidate observations.
-/
theorem settle_pending :
  ∀ {α ε : Type} (s : State α ε) (id : Nat) (a : Except (Boundary.Exception ε) Unit),
    lookupPromise s id = some .pending →
    settle s id a = { s with
      promises := s.promises.map (fun p => if p.1 == id then
        (id, match a with | .ok _ => .fulfilled () | .error e => .rejected e) else p),
      trace := s.trace ++ [.settled id a] } := by
  intro α ε s id a h
  cases a <;> simp [settle, h]

/--
`op.writable-stream-finish-in-flight-write`:
settle other for the local candidate observations.
-/
theorem settle_other :
  ∀ {α ε : Type} (s : State α ε) (id : Nat) (a : Except (Boundary.Exception ε) Unit),
    lookupPromise s id ≠ some .pending → settle s id a = s := by
  intro α ε s id a h
  cases hcell : lookupPromise s id with
  | none => simp [settle, hcell]
  | some cell => cases cell <;> simp_all [settle]

/--
`op.writable-stream-default-writer-ensure-ready-promise-rejected`:
markHandled eq for the local candidate observations.
-/
theorem markHandled_eq :
  ∀ {α ε : Type} (s : State α ε) (id : Nat),
    markHandled s id = if id ∈ s.handled then s else { s with handled := s.handled ++ [id] } := by
  intros
  rfl

/--
`op.writable-stream-default-writer-ensure-ready-promise-rejected`:
ensureReadyRejected pending for the local candidate observations.
-/
theorem ensureReadyRejected_pending :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    lookupPromise s s.readyPromise = some .pending →
    ensureReadyRejected s e = markHandled (settle s s.readyPromise (.error e)) s.readyPromise := by
  intros
  simp_all [ensureReadyRejected]

/--
`op.writable-stream-default-writer-ensure-ready-promise-rejected`:
ensureReadyRejected other for the local candidate observations.
-/
theorem ensureReadyRejected_other :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    lookupPromise s s.readyPromise ≠ some .pending →
    ensureReadyRejected s e =
      let r := freshPromise s (.rejected e)
      markHandled { r.1 with readyPromise := r.2 } r.2 := by
  intro α ε s e h
  cases hcell : lookupPromise s s.readyPromise with
  | none => simp [ensureReadyRejected, hcell]
  | some cell => cases cell <;> simp_all [ensureReadyRejected]

/--
`op.writable-stream-update-backpressure`:
updateBackpressure same for the local candidate observations.
-/
theorem updateBackpressure_same :
  ∀ {α ε : Type} (s : State α ε) (b : Bool), s.backpressure = b → updateBackpressure s b = s := by
  intros
  simp_all [updateBackpressure]

/--
`op.writable-stream-update-backpressure`:
updateBackpressure true for the local candidate observations.
-/
theorem updateBackpressure_true :
  ∀ {α ε : Type} (s : State α ε), s.backpressure = false →
    updateBackpressure s true =
      let r := freshPromise s .pending
      { r.1 with readyPromise := r.2, backpressure := true } := by
  intros
  simp_all [updateBackpressure]

/--
`op.writable-stream-update-backpressure`:
updateBackpressure false for the local candidate observations.
-/
theorem updateBackpressure_false :
  ∀ {α ε : Type} (s : State α ε), s.backpressure = true →
    updateBackpressure s false =
      { settle s s.readyPromise (.ok ()) with backpressure := false } := by
  intros
  simp_all [updateBackpressure]

/--
`op.writable-stream-default-writer-get-desired-size`:
desiredSize eq for the local candidate observations.
-/
theorem desiredSize_eq :
  ∀ {α ε : Type} (s : State α ε),
    desiredSize s = match s.status with
      | .writable => some (sizes.sub s.highWaterMark s.queue.totalSize)
      | .closed => some sizes.zero
      | .erroring _ | .errored _ => none := by
  intros
  rfl

/--
`op.writable-stream-default-controller-get-backpressure`,
`op.writable-stream-default-controller-get-desired-size`:
getBackpressure eq for the local candidate observations.
-/
theorem getBackpressure_eq :
  ∀ {α ε : Type} (s : State α ε),
    getBackpressure s = sizeNonPositive (sizes.sub s.highWaterMark s.queue.totalSize) := by
  intros
  rfl

/--
`op.writable-stream-default-controller-clear-algorithms`:
clearAlgorithms eq for the local candidate observations.
-/
theorem clearAlgorithms_eq :
  ∀ {α ε : Type} (s : State α ε), clearAlgorithms s =
    { s with algorithms := { size := none, write := none, close := none, abort := none } } := by
  intros
  rfl

/--
`op.writable-stream-close-queued-or-in-flight`:
closeQueuedOrInFlight eq for the local candidate observations.
-/
theorem closeQueuedOrInFlight_eq :
  ∀ {α ε : Type} (s : State α ε),
    closeQueuedOrInFlight s = match s.closeState with | .none => false | _ => true := by
  intros
  rfl

/--
`op.writable-stream-has-operation-marked-in-flight`:
hasInFlight eq for the local candidate observations.
-/
theorem hasInFlight_eq :
  ∀ {α ε : Type} (s : State α ε),
    hasInFlight s = s.inFlightWrite.isSome ||
      (match s.closeState with | .inFlight _ _ => true | _ => false) := by
  intro α ε s
  cases hs : s.closeState <;> simp [hasInFlight, hs]

/--
`op.writable-stream-default-controller-process-write`:
externalFrontier eq for the local candidate observations.
-/
theorem externalFrontier_eq :
  ∀ {α ε : Type} (s : State α ε),
    externalFrontier s = match s.control with
      | [] | .awaitSize _ _ :: _ | .awaitSink _ :: _ | .awaitSignal _ _ :: _ => true
      | _ => false := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
operationKind eq for the local candidate observations.
-/
theorem operationKind_eq :
  ∀ {α ε : Type} (op : SinkOperation α ε),
    operationKind op =
      match op with | .write _ _ => .write | .close _ => .close | .abort _ _ => .abort := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
operationRequest eq for the local candidate observations.
-/
theorem operationRequest_eq :
  ∀ {α ε : Type} (op : SinkOperation α ε),
    operationRequest op = match op with | .write id _ | .close id | .abort id _ => id := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
operationPhase eq for the local candidate observations.
-/
theorem operationPhase_eq :
  ∀ {α ε : Type} (s : State α ε) (kind : SinkKind) (id : Nat),
    operationPhase s kind id =
      let slot := match kind with
        | .write => s.inFlightWrite
        | .close => match s.closeState with | .inFlight n phase => some (n, phase) | _ => none
        | .abort => s.abortInFlight
      slot.bind (fun p => if p.1 == id then some p.2 else none) := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
setOperationPhase eq for the local candidate observations.
-/
theorem setOperationPhase_eq :
  ∀ {α ε : Type} (s : State α ε) (op : SinkOperation α ε) (phase : OperationPhase),
    setOperationPhase s op phase = match op with
      | .write id _ => { s with inFlightWrite := some (id, phase) }
      | .close id => { s with closeState := .inFlight id phase }
      | .abort id _ => { s with abortInFlight := some (id, phase) } := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
attachSink eq for the local candidate observations.
-/
theorem attachSink_eq :
  ∀ {α ε : Type} (s : State α ε) (op : SinkOperation α ε) (ret : SinkReturn ε),
    attachSink s op ret =
      let b := match op with | .write _ _ => s | .close _ | .abort _ _ => clearAlgorithms s
      match ret with
      | .pending => setOperationPhase b op .awaiting
      | .settled answer =>
        { setOperationPhase b op .queued with
          jobs := b.jobs ++ [⟨operationKind op, operationRequest op, answer⟩] } := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
invokeSink eq for the local candidate observations.
-/
theorem invokeSink_eq :
  ∀ {α ε : Type} (s : State α ε) (op : SinkOperation α ε),
    invokeSink s op =
      let alg := match op with
        | .write _ _ => s.algorithms.write
        | .close _ => s.algorithms.close
        | .abort _ _ => s.algorithms.abort
      match alg with
      | none => none
      | some .fulfilled => some (attachSink s op (.settled .fulfilled))
      | some (.foreign name) => some
        { setOperationPhase s op .invoking with
          control := .awaitSink op :: s.control,
          trace := s.trace ++ [.sinkCalled name op] } := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
acceptAnswer waiting for the local candidate observations.
-/
theorem acceptAnswer_waiting :
  ∀ {α ε : Type} (s : State α ε) (kind : SinkKind) (id : Nat) (a : SinkAnswer ε),
    operationPhase s kind id = some .awaiting →
    acceptAnswer s kind id a =
      let b := match kind with
        | .write => { s with inFlightWrite := some (id, .queued) }
        | .close => { s with closeState := .inFlight id .queued }
        | .abort => { s with abortInFlight := some (id, .queued) }
      some { b with jobs := s.jobs ++ [⟨kind, id, a⟩] } := by
  intro α ε s kind id a h
  cases kind <;> simp_all [acceptAnswer]

/--
`op.writable-stream-default-controller-process-write`:
acceptAnswer other for the local candidate observations.
-/
theorem acceptAnswer_other :
  ∀ {α ε : Type} (s : State α ε) (kind : SinkKind) (id : Nat) (a : SinkAnswer ε),
    operationPhase s kind id ≠ some .awaiting → acceptAnswer s kind id a = none := by
  intros
  simp_all [acceptAnswer]

/--
`op.writable-stream-default-controller-get-backpressure`:
sizeNonPositive eq for the local candidate observations.
-/
theorem sizeNonPositive_eq :
  ∀ (v : Size), sizeNonPositive v =
    match v with
    | .finite units => Decidable.decide (units ≤ 0)
    | .negInfinity => true
    | _ => false := by
  intros
  rfl

/--
`op.writable-stream-default-writer-write`:
decide blocked for the local candidate observations.
-/
theorem decide_blocked :
  ∀ {α ε : Type} (s : State α ε) (d : Decision α ε),
    externalFrontier s = false → decide s d = none := by
  intros
  simp_all [decide]

/--
`op.writable-stream-default-writer-write`:
decide write for the local candidate observations.
-/
theorem decide_write :
  ∀ {α ε : Type} (s : State α ε) (chunk : α), externalFrontier s = true →
    decide s (.write chunk) = some
      { s with nextCall := s.nextCall + 1, control := .getSize s.nextCall chunk :: s.control } := by
  intros
  simp_all [decide]

/--
`op.writable-stream-close`:
decide close for the local candidate observations.
-/
theorem decide_close :
  ∀ {α ε : Type} (s : State α ε) , externalFrontier s = true →
    decide s (.close) = some
      { s with nextCall := s.nextCall + 1, control := .beginClose s.nextCall :: s.control } := by
  intros
  simp_all [decide]

/--
`op.writable-stream-abort`:
decide abort for the local candidate observations.
-/
theorem decide_abort :
  ∀ {α ε : Type} (s : State α ε) (reason : Boundary.Exception ε), externalFrontier s = true →
    decide s (.abort reason) = some
      { s with
        nextCall := s.nextCall + 1, control := .beginAbort s.nextCall reason :: s.control } := by
  intros
  simp_all [decide]

/--
`op.ws-default-controller-error`:
decide controllerError for the local candidate observations.
-/
theorem decide_controllerError :
  ∀ {α ε : Type} (s : State α ε) (reason : Boundary.Exception ε), externalFrontier s = true →
    decide s (.controllerError reason) = some
      { s with
        nextCall := s.nextCall + 1,
        control := .controllerError reason :: .returnUnit s.nextCall :: s.control } := by
  intros
  simp_all [decide]

/--
`op.default-writer-ready`:
decide queryReady for the local candidate observations.
-/
theorem decide_queryReady :
  ∀ {α ε : Type} (s : State α ε), externalFrontier s = true →
    decide s .queryReady = some
      { s with
        nextCall := s.nextCall + 1,
        trace := s.trace ++ [.readyRead s.nextCall s.readyPromise] } := by
  intros
  simp_all [decide]

/--
`op.default-writer-closed`:
decide queryClosed for the local candidate observations.
-/
theorem decide_queryClosed :
  ∀ {α ε : Type} (s : State α ε), externalFrontier s = true →
    decide s .queryClosed = some
      { s with
        nextCall := s.nextCall + 1,
        trace := s.trace ++ [.closedRead s.nextCall s.closedPromise] } := by
  intros
  simp_all [decide]

/--
`op.writable-stream-default-writer-get-desired-size`:
decide queryDesiredSize for the local candidate observations.
-/
theorem decide_queryDesiredSize :
  ∀ {α ε : Type} (s : State α ε), externalFrontier s = true →
    decide s .queryDesiredSize = some
      { s with
        nextCall := s.nextCall + 1,
        trace := s.trace ++ [.desiredSizeRead s.nextCall (desiredSize s)] } := by
  intros
  simp_all [decide]

/--
`op.writable-stream-default-controller-process-write`:
decide answer for the local candidate observations.
-/
theorem decide_answer :
  ∀ {α ε : Type} (s : State α ε) (kind : SinkKind) (id : Nat) (answer : SinkAnswer ε),
    externalFrontier s = true → decide s (.answer kind id answer) =
      acceptAnswer s kind id answer := by
  intros
  simp_all [decide]

/--
`op.writable-stream-default-controller-get-chunk-size`:
returnSize value for the local candidate observations.
-/
theorem returnSize_value :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat) (chunk : α) (size : Size),
    decide { s with control := .awaitSize call chunk :: tail } (.returnSize (.value size)) =
      some { s with control := .afterSize call chunk size :: tail } := by
  intros
  rfl

/--
`op.writable-stream-default-controller-get-chunk-size`:
returnSize thrown for the local candidate observations.
-/
theorem returnSize_thrown :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (chunk : α) (reason : Boundary.Exception ε),
    decide { s with control := .awaitSize call chunk :: tail } (.returnSize (.thrown reason)) =
      some { s with
        control := .errorIfNeeded reason :: .afterSize call chunk sizes.one :: tail } := by
  intros
  rfl

/--
`op.writable-stream-default-controller-get-chunk-size`:
returnSize unmatched for the local candidate observations.
-/
theorem returnSize_unmatched :
  ∀ {α ε : Type} (s : State α ε) (a : Data.SizeAnswer Size (Boundary.Exception ε)),
    (∀ call chunk tail, s.control ≠ .awaitSize call chunk :: tail) →
    decide s (.returnSize a) = none := by
  intro α ε s a h
  cases hc : s.control with
  | nil => simp [decide, externalFrontier, hc]
  | cons head tail => cases head <;> simp_all [decide, externalFrontier]

/--
`op.writable-stream-default-controller-process-write`:
returnSink invoking for the local candidate observations.
-/
theorem returnSink_invoking :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (op : SinkOperation α ε) (ret : SinkReturn ε),
    operationPhase s (operationKind op) (operationRequest op) = some .invoking →
    decide { s with control := .awaitSink op :: tail } (.returnSink ret) =
      some (attachSink { s with control := tail } op ret) := by
  intros
  simp_all [decide, externalFrontier, operationPhase]

/--
`op.writable-stream-default-controller-process-write`:
returnSink unmatched for the local candidate observations.
-/
theorem returnSink_unmatched :
  ∀ {α ε : Type} (s : State α ε) (ret : SinkReturn ε),
    (∀ op tail, s.control ≠ .awaitSink op :: tail ∨
      operationPhase s (operationKind op) (operationRequest op) ≠ some .invoking) →
    decide s (.returnSink ret) = none := by
  intro α ε s ret h
  cases hc : s.control with
  | nil => simp [decide, externalFrontier, hc]
  | cons head tail =>
      cases head <;> simp_all [decide, externalFrontier]
      rename_i op
      simpa using h op tail

/--
`op.writable-stream-abort`:
returnSignal eq for the local candidate observations.
-/
theorem returnSignal_eq :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason : Boundary.Exception ε),
    decide { s with control := .awaitSignal call reason :: tail } .returnSignal =
      some { s with control := .afterSignal call reason :: tail } := by
  intros
  rfl

/--
`op.writable-stream-abort`:
returnSignal unmatched for the local candidate observations.
-/
theorem returnSignal_unmatched :
  ∀ {α ε : Type} (s : State α ε),
    (∀ call reason tail, s.control ≠ .awaitSignal call reason :: tail) →
    decide s .returnSignal = none := by
  intro α ε s h
  cases hc : s.control with
  | nil => simp [decide, externalFrontier, hc]
  | cons head tail => cases head <;> simp_all [decide, externalFrontier]

/--
`op.writable-stream-default-controller-process-write`:
tick foreign marker for the local candidate observations.
-/
theorem tick_foreign_marker :
  ∀ {α ε : Type} (s : State α ε), s.control ≠ [] → externalFrontier s = true → tick s = none := by
  intro α ε s hn hf
  cases hc : s.control with
  | nil => exact (hn hc).elim
  | cons head tail => cases head <;> simp_all [externalFrontier, tick]

/-! ## `PROMISE-PG-FIRST` bridging: the sink-job queue

`E-45`, `E-46` (generalize). `E-46` records why this is the honest shape: the queue stage
is one branch of a twenty-branch `tick`, so the general law is `Queue.dequeue`'s equation
plus a Streams bridging lemma, not a relocation of `tick`. -/

/-- `E-45`: the view is exactly the sink-job list. Mask M1. -/
theorem jobQueue_eq {α ε : Type} (s : State α ε) :
    jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs := rfl

/--
`E-46` (generalize). Under the writable component's own spelling of
`requirement.jobs.1` — an empty administrative control stack — `tick` reduces to
`Whatwg.Ecma262.Jobs.Queue.dequeue`. Mask M2.
-/
theorem tick_dequeue_bridge {α ε : Type} (s : State α ε) :
    s.control = [] →
      tick s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (jobQueue s)).map
          (fun p => { s with control := [.react p.1], jobs := p.2.pending }) := by
  intro hc
  cases hj : s.jobs <;>
    simp [tick, jobQueue, Whatwg.Ecma262.Jobs.Queue.dequeue, hc, hj]

/--
`op.writable-stream-default-controller-process-write`:
tick no job for the local candidate observations.
Re-derived through `tick_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_empty`, never re-proved from `tick`.
-/
theorem tick_no_job :
  ∀ {α ε : Type} (s : State α ε), s.control = [] → s.jobs = [] → tick s = none := by
  intro α ε s hc hj
  rw [tick_dequeue_bridge s hc, jobQueue_eq, hj]
  exact congrArg _ Whatwg.Ecma262.Jobs.Queue.dequeue_empty

/--
`op.writable-stream-default-controller-process-write`:
tick job fifo for the local candidate observations.
Re-derived through `tick_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_cons` (the `later := []` instance of
`Queue.dequeue_fifo`), never re-proved from `tick`. Mask M2.
-/
theorem tick_job_fifo :
  ∀ {α ε : Type} (s : State α ε) (job : SinkJob α ε) (jobs : List (SinkJob α ε)),
    tick { s with control := [], jobs := job :: jobs } =
      some { s with control := [.react job], jobs := jobs } := by
  intro α ε s job jobs
  rw [tick_dequeue_bridge { s with control := [], jobs := job :: jobs } rfl, jobQueue_eq]
  rw [show ({ s with control := [], jobs := job :: jobs } : State α ε).jobs = job :: jobs from rfl,
    Whatwg.Ecma262.Jobs.Queue.dequeue_cons]
  rfl

/-- `E-37` (generalize), the queueing half only: `attachSink` also clears the close and
abort algorithm slots, which the general `react` must not do, so the bridge is stated on
the job queue alone. Mask M2. -/
theorem attachSink_settled_jobs {α ε : Type} (s : State α ε) (op : SinkOperation α ε)
    (answer : SinkAnswer ε) :
    jobQueue (attachSink s op (.settled answer)) =
      Whatwg.Ecma262.Jobs.Queue.enqueue (jobQueue s)
        ⟨operationKind op, operationRequest op, answer⟩ := by
  cases op <;>
    simp [attachSink, jobQueue, setOperationPhase, clearAlgorithms, operationKind,
      operationRequest, Whatwg.Ecma262.Jobs.Queue.enqueue]

/-- `E-37`: a callback that returned pending queues no reaction yet. Mask M2. -/
theorem attachSink_pending_jobs {α ε : Type} (s : State α ε) (op : SinkOperation α ε) :
    jobQueue (attachSink s op .pending) = jobQueue s := by
  cases op <;> simp [attachSink, jobQueue, setOperationPhase, clearAlgorithms]

/-- `E-38` (generalize), the queueing half only: the `operationPhase … = some .awaiting`
guard stays in Streams. Mask M2. -/
theorem acceptAnswer_jobs {α ε : Type} (s t : State α ε) (kind : SinkKind) (id : Nat)
    (answer : SinkAnswer ε) :
    acceptAnswer s kind id answer = some t →
      jobQueue t = Whatwg.Ecma262.Jobs.Queue.enqueue (jobQueue s) ⟨kind, id, answer⟩ := by
  intro h
  simp only [acceptAnswer] at h
  by_cases hg : operationPhase s kind id = some OperationPhase.awaiting
  · rw [if_pos hg] at h
    rw [← Option.some.inj h]
    cases kind <;> simp [jobQueue, Whatwg.Ecma262.Jobs.Queue.enqueue]
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/--
`op.writable-stream-default-writer-write`:
tick returnPromise for the local candidate observations.
-/
theorem tick_returnPromise :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call id : Nat),
    tick { s with control := .returnPromise call id :: tail } =
      some { s with control := tail, trace := s.trace ++ [.returned call id] } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.ws-default-controller-error`:
tick returnUnit for the local candidate observations.
-/
theorem tick_returnUnit :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat),
    tick { s with control := .returnUnit call :: tail } =
      some { s with control := tail, trace := s.trace ++ [.controllerReturned call] } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-get-chunk-size`:
tick getSize for the local candidate observations.
-/
theorem tick_getSize :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat) (chunk : α),
    tick { s with control := .getSize call chunk :: tail } =
      some (match s.algorithms.size with
        | none | some .one => { s with control := .afterSize call chunk sizes.one :: tail }
        | some (.foreign name) => { s with
            control := .awaitSize call chunk :: tail,
            trace := s.trace ++ [.sizeCalled name call chunk] }) := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-writer-write`:
tick afterSize errored for the local candidate observations.
-/
theorem tick_afterSize_errored :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (chunk : α) (size : Size) (reason : Boundary.Exception ε),
    s.status = .errored reason →
    tick { s with control := .afterSize call chunk size :: tail } =
      let r := freshPromise { s with control := tail } (.rejected reason)
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-writer-write`:
tick afterSize closing for the local candidate observations.
-/
theorem tick_afterSize_closing :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat) (chunk : α) (size : Size),
    (∀ reason, s.status ≠ .errored reason) →
    (closeQueuedOrInFlight s = true ∨ s.status = .closed) →
    tick { s with control := .afterSize call chunk size :: tail } =
      let r := freshPromise { s with control := tail, nextError := s.nextError + 1 }
        (.rejected (.typeError s.nextError))
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intro α ε s tail call chunk size hn h
  cases hs : s.status <;> simp_all [tick, closeQueuedOrInFlight]

/--
`op.writable-stream-default-writer-write`:
tick afterSize erroring for the local candidate observations.
-/
theorem tick_afterSize_erroring :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (chunk : α) (size : Size) (reason : Boundary.Exception ε),
    s.status = .erroring reason → closeQueuedOrInFlight s = false →
    tick { s with control := .afterSize call chunk size :: tail } =
      let r := freshPromise { s with control := tail } (.rejected reason)
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intros
  simp_all [tick, closeQueuedOrInFlight]

/--
`op.writable-stream-default-writer-write`:
tick afterSize writable for the local candidate observations.
-/
theorem tick_afterSize_writable :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat) (chunk : α) (size : Size),
    s.status = .writable → closeQueuedOrInFlight s = false →
    tick { s with control := .afterSize call chunk size :: tail } =
      let r := freshPromise { s with control := tail } .pending
      some { r.1 with
        writeRequests := s.writeRequests ++ [r.2],
        control := .enqueueWrite chunk size :: .returnPromise call r.2 :: tail } := by
  intros
  simp_all [tick, closeQueuedOrInFlight]

/--
`op.writable-stream-default-controller-write`:
tick enqueueWrite error for the local candidate observations.
-/
theorem tick_enqueueWrite_error :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (chunk : α) (size : Size),
    Data.enqueueValueWithSize sizes s.queue (.chunk chunk) size = .error .rangeError →
    tick { s with control := .enqueueWrite chunk size :: tail } =
      some { s with
        nextError := s.nextError + 1,
        control := .errorIfNeeded (.rangeError s.nextError) :: tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-write`:
tick enqueueWrite ok for the local candidate observations.
-/
theorem tick_enqueueWrite_ok :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (chunk : α) (size : Size) (queue : Data.Queue (QueueItem α) Size),
    Data.enqueueValueWithSize sizes s.queue (.chunk chunk) size = .ok queue →
    tick { s with control := .enqueueWrite chunk size :: tail } =
      let b := { s with queue := queue, control := .advance :: tail }
      some (match s.status with
        | .writable => if closeQueuedOrInFlight s then b else
            updateBackpressure b (getBackpressure b)
        | _ => b) := by
  intro α ε s tail chunk size queue hq
  cases hs : s.status <;> simp_all [tick, closeQueuedOrInFlight]
  rfl

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
tick advance busy for the local candidate observations.
-/
theorem tick_advance_busy :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (id : Nat) (phase : OperationPhase),
    s.inFlightWrite = some (id, phase) →
    tick { s with control := .advance :: tail } = some { s with control := tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
tick advance erroring for the local candidate observations.
-/
theorem tick_advance_erroring :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (reason : Boundary.Exception ε),
    s.inFlightWrite = none → s.status = .erroring reason →
    tick { s with control := .advance :: tail } =
      some { s with control := .finishErroring :: tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
tick advance empty for the local candidate observations.
-/
theorem tick_advance_empty :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)),
    s.inFlightWrite = none → s.status = .writable →
    s.queue.entries = [] → tick { s with control := .advance :: tail } =
      some { s with control := tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-process-write`:
tick advance write for the local candidate observations.
-/
theorem tick_advance_write :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (ids : List Nat) (chunk : α) (size : Size)
    (items : List (Data.QueueEntry (QueueItem α) Size)),
    s.inFlightWrite = none → s.status = .writable →
    s.queue.entries = ⟨.chunk chunk, size⟩ :: items → s.writeRequests = id :: ids →
    tick { s with control := .advance :: tail } =
      invokeSink { s with
        control := tail, writeRequests := ids,
        inFlightWrite := some (id, .invoking) } (.write id chunk) := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-process-close`:
tick advance close for the local candidate observations.
-/
theorem tick_advance_close :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (queue : Data.Queue (QueueItem α) Size),
    s.inFlightWrite = none → s.status = .writable → s.closeState = .queued id →
    Data.dequeueValue sizes s.queue = some (.close, queue) → queue.entries = [] →
    tick { s with control := .advance :: tail } =
      invokeSink { s with
        control := tail, queue := queue,
        closeState := .inFlight id .invoking } (.close id) := by
  intro α ε s tail id queue hw hs hc hd he
  cases hq : s.queue.entries with
  | nil => simp [Data.dequeueValue, hq] at hd
  | cons entry items =>
      rcases entry with ⟨value, size⟩
      cases value with
      | chunk chunk => simp [Data.dequeueValue, hq] at hd
      | close => simp [tick, hw, hs, hc, hq, hd, he]

/--
`op.default-writer-close`,
`op.writable-stream-close`:
tick beginClose rejected for the local candidate observations.
-/
theorem tick_beginClose_rejected :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (call : Nat),
    (closeQueuedOrInFlight s = true ∨ s.status = .closed ∨ ∃ e, s.status = .errored e) →
    tick { s with control := .beginClose call :: tail } =
      let r := freshPromise { s with control := tail, nextError := s.nextError + 1 }
        (.rejected (.typeError s.nextError))
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intro α ε s tail call h
  rcases h with h | h | ⟨e, h⟩
  · simp_all [tick, closeQueuedOrInFlight]
  · simp [tick, h]
  · simp [tick, h]

/--
`op.writable-stream-close`:
tick beginClose admitted for the local candidate observations.
-/
theorem tick_beginClose_admitted :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (queue : Data.Queue (QueueItem α) Size),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    closeQueuedOrInFlight s = false →
    Data.enqueueValueWithSize sizes s.queue .close sizes.zero = .ok queue →
    tick { s with control := .beginClose call :: tail } =
      let r := freshPromise { s with control := tail } .pending
      let b := { r.1 with
        closeState := .queued r.2, queue := queue,
        control := .advance :: .returnPromise call r.2 :: tail }
      some (match s.status with
        | .writable => if s.backpressure then settle b s.readyPromise (.ok ()) else b
        | _ => b) := by
  intro α ε s tail call queue hs hc hq
  rcases hs with hs | ⟨e, hs⟩ <;> simp_all [tick, closeQueuedOrInFlight]

/--
`op.writable-stream-abort`:
tick beginAbort terminal for the local candidate observations.
-/
theorem tick_beginAbort_terminal :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason : Boundary.Exception ε),
    (s.status = .closed ∨ ∃ e, s.status = .errored e) →
    tick { s with control := .beginAbort call reason :: tail } =
      let r := freshPromise { s with control := tail } (.fulfilled ())
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intro α ε s tail call reason hs
  rcases hs with hs | ⟨e, hs⟩ <;> simp [tick, hs]

/--
`op.writable-stream-abort`:
tick afterSignal terminal for the local candidate observations.
-/
theorem tick_afterSignal_terminal :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason : Boundary.Exception ε),
    (s.status = .closed ∨ ∃ e, s.status = .errored e) →
    tick { s with control := .afterSignal call reason :: tail } =
      let r := freshPromise { s with control := tail } (.fulfilled ())
      some { r.1 with control := .returnPromise call r.2 :: tail } := by
  intro α ε s tail call reason hs
  rcases hs with hs | ⟨e, hs⟩ <;> simp [tick, hs]

/--
`op.writable-stream-abort`:
tick beginAbort signal for the local candidate observations.
-/
theorem tick_beginAbort_signal :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason : Boundary.Exception ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.signalArgument = none →
    tick { s with control := .beginAbort call reason :: tail } =
      some { s with
        signalArgument := some reason, control := .awaitSignal call reason :: tail,
        trace := s.trace ++ [.signalCalled call reason] } := by
  intro α ε s tail call reason hs ha
  rcases hs with hs | ⟨e, hs⟩ <;> simp [tick, hs, ha]

/--
`op.writable-stream-abort`:
tick beginAbort signaled for the local candidate observations.
-/
theorem tick_beginAbort_signaled :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason first : Boundary.Exception ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.signalArgument = some first →
    tick { s with control := .beginAbort call reason :: tail } =
      some { s with control := .afterSignal call reason :: tail } := by
  intro α ε s tail call reason first hs ha
  rcases hs with hs | ⟨e, hs⟩ <;> simp [tick, hs, ha]

/--
`op.writable-stream-abort`:
tick afterSignal existing for the local candidate observations.
-/
theorem tick_afterSignal_existing :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call id : Nat) (reason : Boundary.Exception ε)
    (pending : PendingAbort ε),
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) → s.pendingAbort = some pending →
    (match pending with | .requested n _ | .alreadyErroring n => n) = id →
    tick { s with control := .afterSignal call reason :: tail } =
      some { s with control := .returnPromise call id :: tail } := by
  intro α ε s tail call id reason pending hs hp hi
  rcases hs with hs | ⟨e, hs⟩ <;> cases pending <;> simp_all [tick]

/--
`op.writable-stream-abort`:
tick afterSignal writable for the local candidate observations.
-/
theorem tick_afterSignal_writable :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason : Boundary.Exception ε),
    s.status = .writable → s.pendingAbort = none →
    tick { s with control := .afterSignal call reason :: tail } =
      let r := freshPromise { s with control := tail } .pending
      some { r.1 with
        pendingAbort := some (.requested r.2 reason),
        control := .startErroring reason :: .returnPromise call r.2 :: tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-abort`:
tick afterSignal erroring for the local candidate observations.
-/
theorem tick_afterSignal_erroring :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (call : Nat) (reason stored : Boundary.Exception ε),
    s.status = .erroring stored → s.pendingAbort = none →
    tick { s with control := .afterSignal call reason :: tail } =
      let r := freshPromise { s with control := tail } .pending
      some { r.1 with
        pendingAbort := some (.alreadyErroring r.2),
        control := .returnPromise call r.2 :: tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-default-controller-error-if-needed`:
tick errorIfNeeded for the local candidate observations.
-/
theorem tick_errorIfNeeded :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (reason : Boundary.Exception ε),
    tick { s with control := .errorIfNeeded reason :: tail } =
      some { s with
        control := match s.status with
        | .writable => .controllerError reason :: tail | _ => tail } := by
  intros
  first | rfl | simp_all [tick]

/--
`op.ws-default-controller-error`,
`op.writable-stream-default-controller-error`:
tick controllerError for the local candidate observations.
-/
theorem tick_controllerError :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (reason : Boundary.Exception ε),
    tick { s with control := .controllerError reason :: tail } =
      some (match s.status with
        | .writable => clearAlgorithms { s with control := .startErroring reason :: tail }
        | _ => { s with control := tail }) := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-start-erroring`:
tick startErroring for the local candidate observations.
-/
theorem tick_startErroring :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (reason : Boundary.Exception ε), s.status = .writable →
    tick { s with control := .startErroring reason :: tail } =
      some (ensureReadyRejected
        { s with
          status := .erroring reason,
          control := if hasInFlight s then tail else .finishErroring :: tail } reason) := by
  intros
  simp_all [tick, hasInFlight]

/--
`op.writable-stream-deal-with-rejection`:
tick dealRejection for the local candidate observations.
-/
theorem tick_dealRejection :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (reason : Boundary.Exception ε),
    tick { s with control := .dealRejection reason :: tail } =
      match s.status with
      | .writable => some { s with control := .startErroring reason :: tail }
      | .erroring _ => some { s with control := .finishErroring :: tail }
      | _ => none := by
  intros
  first | rfl | simp_all [tick]

/--
`op.writable-stream-finish-erroring`,
`op.ws-default-controller-private-error`,
`op.ws-default-controller-private-abort`:
tick finishErroring for the local candidate observations.
-/
theorem tick_finishErroring :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (stored : Boundary.Exception ε),
    s.status = .erroring stored → hasInFlight s = false →
    tick { s with control := .finishErroring :: tail } =
      let b := s.writeRequests.foldl (fun st id => settle st id (.error stored))
        { s with
          status := .errored stored, queue := Data.Queue.empty sizes,
          writeRequests := [], pendingAbort := none, control := tail }
      match s.pendingAbort with
      | none => some { b with control := .rejectCloseClosed stored :: tail }
      | some (.alreadyErroring id) =>
        some { settle b id (.error stored) with control := .rejectCloseClosed stored :: tail }
      | some (.requested id reason) => invokeSink b (.abort id reason) := by
  intro α ε s tail stored hs hi
  cases hp : s.pendingAbort with
  | none => simp_all [tick, hasInFlight]
  | some p => cases p <;> simp_all [tick, hasInFlight]

/--
`op.writable-stream-finish-erroring`,
`op.writable-stream-has-operation-marked-in-flight`:
tick finishErroring inFlight for the local candidate observations.
-/
theorem tick_finishErroring_inFlight :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)), hasInFlight s = true →
    tick { s with control := .finishErroring :: tail } = none := by
  intros
  simp_all [tick, hasInFlight]

/--
`op.writable-stream-reject-close-and-closed-promise-if-needed`:
tick rejectCloseClosed for the local candidate observations.
-/
theorem tick_rejectCloseClosed :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (stored : Boundary.Exception ε), s.status = .errored stored →
    (∀ id phase, s.closeState ≠ .inFlight id phase) →
    tick { s with control := .rejectCloseClosed stored :: tail } =
      let b := match s.closeState with
        | .queued id => { settle s id (.error stored) with closeState := .none }
        | _ => s
      some (markHandled (settle { b with control := tail }
        b.closedPromise (.error stored)) b.closedPromise) := by
  intro α ε s tail stored hs hc
  cases hclose : s.closeState <;> simp_all [tick, settle, lookupPromise] <;> rfl

/--
`op.writable-stream-default-controller-process-write`:
tick react unmatched for the local candidate observations.
-/
theorem tick_react_unmatched :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (job : SinkJob α ε),
    operationPhase s job.kind job.request ≠ some .queued →
    tick { s with control := .react job :: tail } = none := by
  intros
  simp_all [tick, operationPhase]

/--
`op.writable-stream-finish-in-flight-write`:
tick write fulfilled for the local candidate observations.
-/
theorem tick_write_fulfilled :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (chunk : α) (queue : Data.Queue (QueueItem α) Size),
    s.inFlightWrite = some (id, .queued) →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    Data.dequeueValue sizes s.queue = some (.chunk chunk, queue) →
    tick { s with control := .react ⟨.write, id, .fulfilled⟩ :: tail } =
      let b := { settle s id (.ok ()) with
        inFlightWrite := none, queue := queue,
        control := .advance :: tail }
      some (match s.status with
        | .writable => if closeQueuedOrInFlight s then b else
            updateBackpressure b (getBackpressure b)
        | _ => b) := by
  intro α ε s tail id chunk queue hi hs hq
  rcases hs with hs | ⟨e, hs⟩ <;>
    simp [tick, hi, hs, hq, operationPhase, closeQueuedOrInFlight, settle, lookupPromise] <;> rfl

/--
`op.writable-stream-finish-in-flight-write-with-error`:
tick write rejected for the local candidate observations.
-/
theorem tick_write_rejected :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (reason : Boundary.Exception ε),
    s.inFlightWrite = some (id, .queued) →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    tick { s with control := .react ⟨.write, id, .rejected reason⟩ :: tail } =
      let b := match s.status with | .writable => clearAlgorithms s | _ => s
      some { settle b id (.error reason) with
        inFlightWrite := none,
        control := .dealRejection reason :: tail } := by
  intro α ε s tail id reason hi hs
  rcases hs with hs | ⟨e, hs⟩ <;>
    simp [tick, hi, hs, operationPhase, clearAlgorithms, settle, lookupPromise]

/--
`op.writable-stream-finish-in-flight-close`:
tick close fulfilled for the local candidate observations.
-/
theorem tick_close_fulfilled :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε)) (id : Nat),
    s.closeState = .inFlight id .queued →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    tick { s with control := .react ⟨.close, id, .fulfilled⟩ :: tail } =
      let b := { settle s id (.ok ()) with closeState := .none, control := tail }
      let c := match s.status, s.pendingAbort with
        | .erroring _, some (.requested abortId _) => settle b abortId (.ok ())
        | .erroring _, some (.alreadyErroring abortId) => settle b abortId (.ok ())
        | _, _ => b
      some (settle { c with status := .closed, pendingAbort := none }
        c.closedPromise (.ok ())) := by
  intro α ε s tail id hi hs
  rcases hs with hs | ⟨e, hs⟩ <;>
    cases hp : s.pendingAbort with
    | none => simp [tick, hi, hs, hp, operationPhase, settle, lookupPromise] <;> rfl
    | some p => cases p <;> simp [tick, hi, hs, hp, operationPhase, settle, lookupPromise] <;> rfl

/--
`op.writable-stream-finish-in-flight-close-with-error`:
tick close rejected for the local candidate observations.
-/
theorem tick_close_rejected :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (reason : Boundary.Exception ε),
    s.closeState = .inFlight id .queued →
    (s.status = .writable ∨ ∃ e, s.status = .erroring e) →
    tick { s with control := .react ⟨.close, id, .rejected reason⟩ :: tail } =
      let b := { settle s id (.error reason) with closeState := .none }
      let c := match s.pendingAbort with
        | some (.requested abortId _) | some (.alreadyErroring abortId) =>
          settle b abortId (.error reason)
        | none => b
      some { c with pendingAbort := none, control := .dealRejection reason :: tail } := by
  intro α ε s tail id reason hi hs
  rcases hs with hs | ⟨e, hs⟩ <;>
    cases hp : s.pendingAbort with
    | none => simp [tick, hi, hs, hp, operationPhase, settle, lookupPromise] <;> rfl
    | some p => cases p <;> simp [tick, hi, hs, hp, operationPhase, settle, lookupPromise] <;> rfl

/--
`op.ws-default-controller-private-abort`:
tick abort settled for the local candidate observations.
-/
theorem tick_abort_settled :
  ∀ {α ε : Type} (s : State α ε) (tail : List (Control α ε))
    (id : Nat) (stored : Boundary.Exception ε) (a : SinkAnswer ε),
    s.abortInFlight = some (id, .queued) → s.status = .errored stored →
    tick { s with control := .react ⟨.abort, id, a⟩ :: tail } =
      let result := match a with | .fulfilled => .ok () | .rejected e => .error e
      some { settle s id result with
        abortInFlight := none,
        control := .rejectCloseClosed stored :: tail } := by
  intro α ε s tail id stored a hi hs
  simp [tick, hi, hs, operationPhase, settle, lookupPromise]
  constructor <;> rfl

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
step iff for the local candidate observations.
-/
theorem step_iff :
  ∀ {α ε : Type} (s : State α ε) (d : Option (Decision α ε)) (t : State α ε),
    Step s d t ↔ match d with | none => tick s = some t | some a => decide s a = some t := by
  intro α ε s d t
  cases d <;> rfl

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
reaches nil for the local candidate observations.
-/
theorem reaches_nil :
  ∀ {α ε : Type} (s : State α ε) (t : State α ε), Reaches s [] t ↔ s = t := by
  intro α ε s t
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil s

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
reaches cons for the local candidate observations.
-/
theorem reaches_cons :
  ∀ {α ε : Type} (s : State α ε) (d : Option (Decision α ε)) (ds : List (Option (Decision α ε)))
    (t : State α ε), Reaches s (d :: ds) t ↔
      ∃ u, Step s d u ∧ Reaches u ds t := by
  intro α ε s d ds t
  constructor
  · intro h; cases h with | cons first rest => exact ⟨_, first, rest⟩
  · rintro ⟨u, first, rest⟩; exact .cons first rest

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
reaches append iff for the local candidate observations.
-/
theorem reaches_append_iff :
  ∀ {α ε : Type} (s : State α ε) (ds es : List (Option (Decision α ε))) (t : State α ε),
    Reaches s (ds ++ es) t ↔ ∃ u, Reaches s ds u ∧ Reaches u es t := by
  intro α ε s ds es t
  induction ds generalizing s with
  | nil => simp [reaches_nil]
  | cons d ds ih =>
      simp only [List.cons_append, reaches_cons, ih]
      constructor
      · rintro ⟨mid, first, endpoint, before, after⟩
        exact ⟨endpoint, ⟨mid, first, before⟩, after⟩
      · rintro ⟨endpoint, ⟨mid, first, before⟩, after⟩
        exact ⟨mid, first, endpoint, before, after⟩

/--
`op.writable-stream-default-controller-advance-queue-if-needed`:
step deterministic for the local candidate observations.
-/
theorem step_deterministic :
  ∀ {α ε : Type} (s : State α ε) (d : Option (Decision α ε)) (t u : State α ε),
    Step s d t → Step s d u → t = u := by
  intro α ε s d t u ht hu
  exact Option.some.inj (ht.symm.trans hu)

/--
`op.writable-stream-default-controller-process-write`:
sinkInput eq for the local candidate observations.
-/
theorem sinkInput_eq :
  ∀ {α ε : Type} (s : State α ε), sinkInput s = s.trace.filterMap (fun e =>
    match e with | .sinkCalled _ (.write _ chunk) => some chunk | _ => none) := by
  intros
  rfl

/--
`op.writable-stream-default-writer-get-desired-size`:
visibleEvents eq for the local candidate observations.
-/
theorem visibleEvents_eq :
  ∀ {α ε : Type} (s : State α ε), visibleEvents s = s.trace.filterMap (fun e =>
    match e with
    | .settled id a => some (.settled id a)
    | .returned call id => some (.returned call id)
    | .readyRead call id => some (.readyRead call id)
    | .closedRead call id => some (.closedRead call id)
    | .desiredSizeRead call size => some (.desiredSizeRead call size)
    | .controllerReturned call => some (.controllerReturned call)
    | _ => none) := by
  intros
  rfl

/--
`op.writable-stream-finish-in-flight-write`:
settlementTrace eq for the local candidate observations.
-/
theorem settlementTrace_eq :
  ∀ {α ε : Type} (s : State α ε), settlementTrace s = s.trace.filterMap (fun e =>
    match e with | .settled id a => some (id, a) | _ => none) := by
  intros
  rfl

/--
`op.writable-stream-default-controller-process-write`:
observeSink eq for the local candidate observations.
-/
theorem observeSink_eq :
  ∀ {α ε : Type} (s : State α ε), observeSink s = ⟨sinkInput s, s.status⟩ := by
  intros
  rfl

/--
`op.writable-stream-default-writer-get-desired-size`:
observeOrdered eq for the local candidate observations.
-/
theorem observeOrdered_eq :
  ∀ {α ε : Type} (s : State α ε), observeOrdered s = ⟨observeSink s, visibleEvents s⟩ := by
  intros
  rfl

/--
`op.writable-stream-default-writer-get-desired-size`:
observeOrdered toSink for the local candidate observations.
-/
theorem observeOrdered_toSink :
  ∀ {α ε : Type} (s : State α ε), (observeOrdered s).sink = observeSink s := by
  intros
  rfl

/--
`op.writable-stream-has-operation-marked-in-flight`: exact Boolean result.
The separately frozen CE-017 addendum requires this parenthesized equation;
the original `hasInFlight_eq` remains its weaker coerced predicate.
-/
theorem hasInFlight_exact {α ε : Type} (s : State α ε) :
    hasInFlight s =
      (s.inFlightWrite.isSome ||
        (match s.closeState with | .inFlight _ _ => true | _ => false)) := rfl

/-! ## `PROMISE-PG-FIRST` bridging: the promise table view

`E-13`..`E-15`, `E-18`..`E-21`, `E-23` (generalize). The Streams slots and
operations stay exactly where they are, with their bodies and their equation
lemmas unchanged, so every `attribute [local simp]` set keeps rewriting with
them. These lemmas relate each operation to its general counterpart in
`Whatwg.Ecma262.Promise`. All of them are mask M1. -/

/-- The view folds the Streams identity list into decision 9's per-cell flag. Mask M1. -/
theorem promiseTable_eq {α ε : Type} (s : State α ε) :
    promiseTable s =
      Whatwg.Ecma262.Promise.Table.mk
        (s.promises.map (fun p =>
          (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 (Decidable.decide (p.1 ∈ s.handled)))))
        s.nextPromise := rfl

/-- `E-18`: `lookupPromise` is `Table.get` through the view. Mask M1. -/
theorem lookupPromise_bridge {α ε : Type} (s : State α ε) (id : Nat) :
    lookupPromise s id = Whatwg.Ecma262.Promise.Table.get (promiseTable s) id := by
  have key : ∀ (l : List (Nat × UnitPromise ε)),
      (l.find? (fun p => p.1 == id)).map Prod.snd =
        Option.map Whatwg.Ecma262.Promise.Cell.state
          (Option.map Prod.snd
            (List.find? (fun e => e.1 == id)
              (l.map (fun p =>
                (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 (Decidable.decide (p.1 ∈ s.handled))))))) := by
    intro l
    induction l with
    | nil => rfl
    | cons q rest ih =>
        simp only [List.map_cons, List.find?_cons]
        cases hb : (q.1 == id) with
        | true => rfl
        | false => exact ih
  exact key s.promises

/-- `E-19`: allocation is `Table.fresh` through the view, provided the cursor
has not already been marked handled. The Streams instance additionally appends
a `.settled` trace event, which the view does not read. Mask M1. -/
theorem freshPromise_bridge {α ε : Type} (s : State α ε) (outcome : UnitPromise ε) :
    s.nextPromise ∉ s.handled →
      (promiseTable (freshPromise s outcome).1, (freshPromise s outcome).2) =
        Whatwg.Ecma262.Promise.Table.fresh (promiseTable s) outcome := by
  intro hne
  cases outcome
  all_goals simp [promiseTable, freshPromise, Whatwg.Ecma262.Promise.Table.fresh, hne]
  all_goals intro a b _
  all_goals rfl

/-- `E-20`: settling is `Table.settle` through the view, guard and all. Mask M1. -/
theorem settle_bridge {α ε : Type} (s : State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) Unit) :
    promiseTable (settle s id result) =
      Whatwg.Ecma262.Promise.Table.settle (promiseTable s) id result := by
  have hbridge := lookupPromise_bridge s id
  by_cases hp : lookupPromise s id = some Whatwg.Ecma262.Promise.State.pending
  · rw [settle_pending s id result hp,
      Whatwg.Ecma262.Promise.Table.settle_pending (promiseTable s) id result (hbridge ▸ hp)]
    simp only [promiseTable, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    by_cases hb : q.1 = id
    · subst hb; cases result <;> simp
    · simp [hb]
  · rw [settle_other s id result hp,
      Whatwg.Ecma262.Promise.Table.settle_other (promiseTable s) id result (hbridge ▸ hp)]

/-- `E-21`: marking handled is `Table.markHandled` through the view. Mask M1. -/
theorem markHandled_bridge {α ε : Type} (s : State α ε) (id : Nat) :
    promiseTable (markHandled s id) =
      Whatwg.Ecma262.Promise.Table.markHandled (promiseTable s) id := by
  by_cases hm : id ∈ s.handled
  · have hid : markHandled s id = s := by simp [markHandled, hm]
    rw [hid]
    simp only [promiseTable, Whatwg.Ecma262.Promise.Table.markHandled, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    by_cases hb : q.1 = id
    · subst hb; simp [hm]
    · simp [hb]
  · have hid : markHandled s id = { s with handled := s.handled ++ [id] } := by
      simp [markHandled, hm]
    rw [hid]
    simp only [promiseTable, Whatwg.Ecma262.Promise.Table.markHandled, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    by_cases hb : q.1 = id
    · subst hb; simp
    · simp [hb]

/-- Decision 9's bridging lemma: the per-cell flag agrees with membership of the
Streams identity list wherever the cell exists. Mask M1. -/
theorem handled_bridge {α ε : Type} (s : State α ε) (id : Nat) :
    (Whatwg.Ecma262.Promise.Table.getCell (promiseTable s) id).map
        Whatwg.Ecma262.Promise.Cell.handled =
      (lookupPromise s id).map (fun _ => Decidable.decide (id ∈ s.handled)) := by
  have key : ∀ (l : List (Nat × UnitPromise ε)),
      Option.map Whatwg.Ecma262.Promise.Cell.handled
          (Option.map Prod.snd
            (List.find? (fun e => e.1 == id)
              (l.map (fun p =>
                (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 (Decidable.decide (p.1 ∈ s.handled))))))) =
        Option.map (fun _ => Decidable.decide (id ∈ s.handled))
          ((l.find? (fun p => p.1 == id)).map Prod.snd) := by
    intro l
    induction l with
    | nil => rfl
    | cons q rest ih =>
        simp only [List.map_cons, List.find?_cons]
        cases hb : (q.1 == id) with
        | true =>
            have hq : q.1 = id := by simpa using hb
            simp [hq]
        | false => exact ih
  exact key s.promises

end Whatwg.Streams.Writable
