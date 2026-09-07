import Whatwg.Streams.Readable.Step

/-!
# Frozen default-readable equations

Owner: READABLE-PG-DEFAULT. These proofs discharge the exact P4a battery statements.
They contribute to the local M1/M2 views; global reachability and host embeddings remain open.
The state, controller, reader and step modules own their underlying operations and anchors.
-/

namespace Whatwg.Streams.Readable

/-- The frozen post-start projection condition; no claim about the full setup algorithm. -/
theorem initial_eq :
  ∀ {α ε : Type} (algorithms : Algorithms) (hwm :
    Size),
    initial (α := α) (ε := ε) algorithms hwm =
      { status := .readable, queue := Data.Queue.empty
          sizes, highWaterMark := hwm,
        started := true, closeRequested := false, pulling := false, pullAgain := false,
        algorithms := some algorithms, readRequests := [], nextRead := 0, nextEnqueue := 0,
          nextError := 0,
        closedPromise := .pending, readPromises := [], frames := [], pullAwaiting := false,
        jobs := [], trace := [] } := by
  intros
  rfl

/--
`op.readable-stream-default-controller-should-call-pull`.
Frozen branch equation for `sizePositive_eq`, under the local M1/M2 views.
-/
theorem sizePositive_eq :
  ∀ (v : Size), sizePositive v =
    match v with
    | .posInfinity => true
    | .finite units => decide (0 < units)
    | _ => false := by
  intro v
  cases v <;> rfl

/--
`op.readable-stream-default-controller-get-desired-size`.
Frozen branch equation for `desiredSize_readable`, under the local M1/M2 views.
-/
theorem desiredSize_readable :
  ∀ {α ε : Type} (s : State α ε), s.status = .readable →
    desiredSize s = some (sizes.sub s.highWaterMark
      s.queue.totalSize) := by
  intros
  simp_all [desiredSize]

/--
`op.readable-stream-default-controller-get-desired-size`.
Frozen branch equation for `desiredSize_closed`, under the local M1/M2 views.
-/
theorem desiredSize_closed :
  ∀ {α ε : Type} (s : State α ε), s.status = .closed →
    desiredSize s = some sizes.zero := by
  intros
  simp_all [desiredSize]

/--
`op.readable-stream-default-controller-get-desired-size`.
Frozen branch equation for `desiredSize_errored`, under the local M1/M2 views.
-/
theorem desiredSize_errored :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    s.status = .errored e → desiredSize s = none := by
  intros
  simp_all [desiredSize]

/--
`op.readable-stream-default-controller-can-close-or-enqueue`.
Frozen branch equation for `canCloseOrEnqueue_iff`, under the local M1/M2 views.
-/
theorem canCloseOrEnqueue_iff :
  ∀ {α ε : Type} (s : State α ε),
    canCloseOrEnqueue s = true ↔ s.status = .readable ∧ s.closeRequested =
      false := by
  intro α ε s
  cases hs : s.status <;> simp [canCloseOrEnqueue, hs]

/--
`op.readable-stream-default-controller-should-call-pull`.
Frozen branch equation for `shouldCallPull_iff`, under the local M1/M2 views.
-/
theorem shouldCallPull_iff :
  ∀ {α ε : Type} (s : State α ε),
    shouldCallPull s = true ↔
      s.status = .readable ∧ s.closeRequested = false ∧ s.started = true ∧
        (s.readRequests ≠ [] ∨
          sizePositive (sizes.sub s.highWaterMark
            s.queue.totalSize) = true) := by
  intro α ε s
  cases hs : s.status <;> cases hc : s.closeRequested <;>
    cases ht : s.started <;> cases hr : s.readRequests <;>
    simp [shouldCallPull, canCloseOrEnqueue, hs, hc, ht, hr]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeeded_idle`, under the local M1/M2 views.
-/
theorem callPullIfNeeded_idle :
  ∀ {α ε : Type} (s : State α ε),
    shouldCallPull s = false → callPullIfNeeded s =
      s := by
  intros
  simp_all [callPullIfNeeded, callPullIfNeededWith, continuePull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeeded_busy`, under the local M1/M2 views.
-/
theorem callPullIfNeeded_busy :
  ∀ {α ε : Type} (s : State α ε),
    shouldCallPull s = true → s.pulling = true →
      callPullIfNeeded s = { s with pullAgain := true } := by
  intros
  simp_all [callPullIfNeeded, callPullIfNeededWith, continuePull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeeded_start`, under the local M1/M2 views.
-/
theorem callPullIfNeeded_start :
  ∀ {α ε : Type} (s : State α ε) (a : Algorithms),
    shouldCallPull s = true → s.pulling = false → s.algorithms = some a →
      callPullIfNeeded s =
        { s with
          pulling := true, pullAwaiting := false, frames := .pull .done :: s.frames,
          trace := s.trace ++ [.pullCalled a.pull] } := by
  intros
  simp_all [callPullIfNeeded, callPullIfNeededWith]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeeded_missing`, under the local M1/M2 views.
-/
theorem callPullIfNeeded_missing :
  ∀ {α ε : Type} (s : State α ε),
    shouldCallPull s = true → s.pulling = false → s.algorithms = none →
      callPullIfNeeded s = s := by
  intros
  simp_all [callPullIfNeeded, callPullIfNeededWith, continuePull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `acceptPullAnswer_waiting`, under the local M1/M2 views.
-/
theorem acceptPullAnswer_waiting :
  ∀ {α ε : Type} (s : State α ε) (a : PullAnswer ε),
    s.pullAwaiting = true → acceptPullAnswer s a =
      some { s with pullAwaiting := false, jobs := s.jobs ++ [a] } := by
  intros
  simp_all [acceptPullAnswer]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `acceptPullAnswer_unmatched`, under the local M1/M2 views.
-/
theorem acceptPullAnswer_unmatched :
  ∀ {α ε : Type} (s : State α ε) (a : PullAnswer ε),
    s.pullAwaiting = false → acceptPullAnswer s a = none := by
  intros
  simp_all [acceptPullAnswer]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `reactPull_fulfilled`, under the local M1/M2 views.
-/
theorem reactPull_fulfilled :
  ∀ {α ε : Type} (s : State α ε),
    reactPull s .fulfilled =
      if s.pullAgain then
        callPullIfNeeded
          { s with pulling := false, pullAgain := false }
      else { s with pulling := false } := by
  intros
  rfl

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `reactPull_rejected`, under the local M1/M2 views.
-/
theorem reactPull_rejected :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    reactPull s (.rejected e) = error s e := by
  intros
  rfl

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_suspended`, under the local M1/M2 views.
-/
theorem runPullJob_suspended :
  ∀ {α ε : Type} (s : State α ε),
    s.frames ≠ [] → runPullJob s = none := by
  intros
  simp_all [runPullJob]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_empty`, under the local M1/M2 views.
-/
theorem runPullJob_empty :
  ∀ {α ε : Type} (s : State α ε),
    s.jobs = [] → runPullJob s = none := by
  intros
  simp_all [runPullJob]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_cons`, under the local M1/M2 views.
-/
theorem runPullJob_cons :
  ∀ {α ε : Type} (s : State α ε) (a : PullAnswer ε)
    (rest : List (PullAnswer ε)),
    s.frames = [] → s.jobs = a :: rest →
      runPullJob s = some (reactPull { s with jobs
        := rest } a) := by
  intros
  simp_all [runPullJob]

/--
`op.readable-stream-default-controller-close`.
Frozen branch equation for `close_blocked`, under the local M1/M2 views.
-/
theorem close_blocked :
  ∀ {α ε : Type} (s : State α ε),
    canCloseOrEnqueue s = false → close s = s := by
  intros
  simp_all [close]

/--
`op.readable-stream-default-controller-close`.
Frozen branch equation for `close_deferred`, under the local M1/M2 views.
-/
theorem close_deferred :
  ∀ {α ε : Type} (s : State α ε),
    canCloseOrEnqueue s = true → s.queue.entries ≠ [] →
      close s = { s with closeRequested := true } := by
  intros
  simp_all [close]

/--
`op.readable-stream-default-controller-close`.
Frozen branch equation for `close_empty`, under the local M1/M2 views.
-/
theorem close_empty :
  ∀ {α ε : Type} (s : State α ε),
    canCloseOrEnqueue s = true → s.queue.entries = [] →
      close s =
        { s with
          status := .closed, closeRequested := true, algorithms := none,
          readRequests := [], closedPromise := .fulfilled (),
          readPromises := s.readPromises.map (fun p ↦
            if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p),
          trace := s.trace ++ [.settled (.closed (.ok ()))] ++
            s.readRequests.map (fun id ↦ .settled (.read id (.ok .done))) } := by
  intro α ε s hg hq
  have hs := (canCloseOrEnqueue_iff s).mp hg
  simp [close, streamClose, hg, hq, hs.1]

/--
`op.readable-stream-default-controller-error`.
Frozen branch equation for `error_terminal`, under the local M1/M2 views.
-/
theorem error_terminal :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    s.status ≠ .readable → error s e = s := by
  intro α ε s e hs
  cases h : s.status <;> simp_all [error]

/--
`op.readable-stream-default-controller-error`.
Frozen branch equation for `error_readable`, under the local M1/M2 views.
-/
theorem error_readable :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    s.status = .readable → error s e =
      { s with
        status := .errored e, queue := Data.resetQueue sizes
          s.queue,
        algorithms := none, readRequests := [], closedPromise := .rejected e,
        readPromises := s.readPromises.map (fun p ↦
          if p.1 ∈ s.readRequests then (p.1, .rejected e) else p),
        trace := s.trace ++ [.settled (.closed (.error e))] ++
          s.readRequests.map (fun id ↦ .settled (.read id (.error e))) } := by
  intros
  simp_all [error]

/--
`op.readable-stream-default-reader-read`.
Frozen branch equation for `read_closed`, under the local M1/M2 views.
-/
theorem read_closed :
  ∀ {α ε : Type} (s : State α ε), s.status = .closed →
    read s =
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .fulfilled .done)],
        trace := s.trace ++ [.settled (.read s.nextRead (.ok .done))] } := by
  intros
  simp_all [read]

/--
`op.readable-stream-default-reader-read`.
Frozen branch equation for `read_errored`, under the local M1/M2 views.
-/
theorem read_errored :
  ∀ {α ε : Type} (s : State α ε) (e : Boundary.Exception ε),
    s.status = .errored e → read s =
      { s with
        nextRead := s.nextRead + 1,
        readPromises := s.readPromises ++ [(s.nextRead, .rejected e)],
        trace := s.trace ++ [.settled (.read s.nextRead (.error e))] } := by
  intros
  simp_all [read]

/--
`op.readable-stream-default-reader-read`.
Frozen branch equation for `read_empty`, under the local M1/M2 views.
-/
theorem read_empty :
  ∀ {α ε : Type} (s : State α ε),
    s.status = .readable → s.queue.entries = [] →
      read s = callPullIfNeeded
        { s with
          nextRead := s.nextRead + 1,
          readPromises := s.readPromises ++ [(s.nextRead, .pending)],
          readRequests := s.readRequests ++ [s.nextRead] } := by
  intros
  simp_all [read, Data.dequeueValue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `beginEnqueue_blocked`, under the local M1/M2 views.
-/
theorem beginEnqueue_blocked :
  ∀ {α ε : Type} (s : State α ε) (chunk : α),
    canCloseOrEnqueue s = false → beginEnqueue s
      chunk = s := by
  intros
  simp_all [beginEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `beginEnqueue_pending`, under the local M1/M2 views.
-/
theorem beginEnqueue_pending :
  ∀ {α ε : Type} (s : State α ε) (chunk : α) (id : Nat)
    (rest : List Nat), canCloseOrEnqueue s = true → s.readRequests = id ::
      rest →
      beginEnqueue s chunk =
        callPullIfNeededWith
          { s with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            readPromises := s.readPromises.map (fun p ↦
              if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p),
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue) := by
  intros
  simp_all [beginEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `beginEnqueue_one`, under the local M1/M2 views.
-/
theorem beginEnqueue_one :
  ∀ {α ε : Type} (s : State α ε) (chunk : α) (a :
    Algorithms),
    canCloseOrEnqueue s = true → s.readRequests = [] →
    s.algorithms = some a → a.size = .one →
      beginEnqueue s chunk = finishEnqueue
        { s with
          nextEnqueue := s.nextEnqueue + 1 } s.nextEnqueue chunk (.value
            sizes.one) := by
  intros
  simp_all [beginEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `beginEnqueue_foreign`, under the local M1/M2 views.
-/
theorem beginEnqueue_foreign :
  ∀ {α ε : Type} (s : State α ε) (chunk : α) (a :
    Algorithms)
    (name : Nat), canCloseOrEnqueue s = true → s.readRequests = [] →
    s.algorithms = some a → a.size = .foreign name →
      beginEnqueue s chunk =
        { s with
          nextEnqueue := s.nextEnqueue + 1,
          frames := .size s.nextEnqueue chunk :: s.frames,
          trace := s.trace ++ [.sizeCalled s.nextEnqueue name chunk] } := by
  intros
  simp_all [beginEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `beginEnqueue_missing`, under the local M1/M2 views.
-/
theorem beginEnqueue_missing :
  ∀ {α ε : Type} (s : State α ε) (chunk : α),
    canCloseOrEnqueue s = true → s.readRequests = [] → s.algorithms = none →
      beginEnqueue s chunk = s := by
  intros
  simp_all [beginEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `finishEnqueue_value`, under the local M1/M2 views.
-/
theorem finishEnqueue_value :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (size : Size) (q : Data.Queue α
      Size),
    Data.enqueueValueWithSize sizes s.queue chunk size = .ok
      q →
      finishEnqueue s call chunk (.value size) =
        callPullIfNeededWith { s with queue := q } (.returnEnqueue call) := by
  intros
  simp_all [finishEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `finishEnqueue_invalid`, under the local M1/M2 views.
-/
theorem finishEnqueue_invalid :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (size : Size),
    Data.enqueueValueWithSize sizes s.queue chunk size =
      .error .rangeError →
      finishEnqueue s call chunk (.value size) =
        let e : Boundary.Exception ε :=
          Boundary.Exception.ofRangeError s.nextError .rangeError
        let t := error { s with nextError := s.nextError + 1 } e
        { t with
          trace := t.trace ++ [.enqueueReturned call (.error e)] } := by
  intros
  simp_all [finishEnqueue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `finishEnqueue_thrown`, under the local M1/M2 views.
-/
theorem finishEnqueue_thrown :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (e : Boundary.Exception ε),
    finishEnqueue s call chunk (.thrown e) =
      let t := error s e
      { t with
        trace := t.trace ++ [.enqueueReturned call (.error e)] } := by
  intros
  rfl

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `resumeSize_empty`, under the local M1/M2 views.
-/
theorem resumeSize_empty :
  ∀ {α ε : Type} (s : State α ε)
    (answer : Data.SizeAnswer Size
      (Boundary.Exception ε)),
    s.frames = [] → resumeSize s answer = none := by
  intros
  simp_all [resumeSize]

/-- Local observation law for `settlementTrace_eq` under DB-04; global embedding remains open. -/
theorem settlementTrace_eq :
  ∀ {α ε : Type} (s : State α ε),
    settlementTrace s = s.trace.filterMap (fun event ↦
      match event with
      | .settled settlement => some settlement
      | _ => none) := by
  intros
  rfl

/-- Local DB-04 law for `chunksOfSettlements_eq`; global embedding remains open. -/
theorem chunksOfSettlements_eq :
  ∀ {α ε : Type} (events : List (Settlement α ε)),
    chunksOfSettlements events = events.filterMap (fun event ↦
      match event with
      | .read _ (.ok (.chunk chunk)) => some chunk
      | _ => none) := by
  intros
  rfl

/-- Local observation law for `observeM1_eq` under DB-04; global embedding remains open. -/
theorem observeM1_eq :
  ∀ {α ε : Type} (s : State α ε),
    observeM1 s = (chunksOfSettlements
      (settlementTrace s), s.status) := by
  intros
  rfl

/-- Local DB-04 law for `chunksOfSettlements_append`; global embedding remains open. -/
theorem chunksOfSettlements_append :
  ∀ {α ε : Type} (left right : List (Settlement α ε)),
    chunksOfSettlements (left ++ right) =
      chunksOfSettlements left ++
        chunksOfSettlements right := by
  intros
  simp [chunksOfSettlements, List.filterMap_append]

/--
`op.rs-default-controller-private-pull`.
Frozen branch equation for `continuePull_done`, under the local M1/M2 views.
-/
theorem continuePull_done :
  ∀ {α ε : Type} (s : State α ε), continuePull s
    .done = s := by
  intros
  rfl

/--
`op.rs-default-controller-private-pull`.
Frozen branch equation for `continuePull_read`, under the local M1/M2 views.
-/
theorem continuePull_read :
  ∀ {α ε : Type} (s : State α ε) (id : Nat) (chunk : α),
    continuePull s (.settleRead id chunk) =
      { s with
        readPromises := s.readPromises.map (fun p ↦
          if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p),
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] } := by
  intros
  rfl

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `continuePull_enqueue`, under the local M1/M2 views.
-/
theorem continuePull_enqueue :
  ∀ {α ε : Type} (s : State α ε) (call : Nat),
    continuePull s (.returnEnqueue call) =
      { s with
        trace := s.trace ++ [.enqueueReturned call (.ok ())] } := by
  intros
  rfl

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeeded_eq`, under the local M1/M2 views.
-/
theorem callPullIfNeeded_eq :
  ∀ {α ε : Type} (s : State α ε),
    callPullIfNeeded s = callPullIfNeededWith s
      .done := by
  intros
  rfl

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeededWith_idle`, under the local M1/M2 views.
-/
theorem callPullIfNeededWith_idle :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α),
    shouldCallPull s = false →
      callPullIfNeededWith s k = continuePull s k := by
  intros
  simp_all [callPullIfNeededWith]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeededWith_busy`, under the local M1/M2 views.
-/
theorem callPullIfNeededWith_busy :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α),
    shouldCallPull s = true → s.pulling = true →
      callPullIfNeededWith s k = continuePull { s
        with pullAgain := true } k := by
  intros
  simp_all [callPullIfNeededWith]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeededWith_start`, under the local M1/M2 views.
-/
theorem callPullIfNeededWith_start :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α)
    (a : Algorithms), shouldCallPull s = true →
      s.pulling = false →
    s.algorithms = some a → callPullIfNeededWith s k =
      { s with
        pulling := true, pullAwaiting := false, frames := .pull k :: s.frames,
        trace := s.trace ++ [.pullCalled a.pull] } := by
  intros
  simp_all [callPullIfNeededWith]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `callPullIfNeededWith_missing`, under the local M1/M2 views.
-/
theorem callPullIfNeededWith_missing :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α),
    shouldCallPull s = true → s.pulling = false → s.algorithms = none →
      callPullIfNeededWith s k = continuePull s k := by
  intros
  simp_all [callPullIfNeededWith]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `returnPull_empty`, under the local M1/M2 views.
-/
theorem returnPull_empty :
  ∀ {α ε : Type} (s : State α ε) (result :
    PullReturn ε),
    s.frames = [] → returnPull s result = none := by
  intros
  simp_all [returnPull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `returnPull_size`, under the local M1/M2 views.
-/
theorem returnPull_size :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (rest : List (Frame α)) (result : PullReturn ε),
    s.frames = .size call chunk :: rest → returnPull s result = none := by
  intros
  simp_all [returnPull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `returnPull_pending`, under the local M1/M2 views.
-/
theorem returnPull_pending :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α)
    (rest : List (Frame α)), s.frames = .pull k :: rest →
      returnPull s .pending =
        some (continuePull { s with frames := rest, pullAwaiting := true }
          k) := by
  intros
  simp_all [returnPull]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `returnPull_settled`, under the local M1/M2 views.
-/
theorem returnPull_settled :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α)
    (rest : List (Frame α)) (answer : PullAnswer ε),
    s.frames = .pull k :: rest → returnPull s (.settled answer) =
      some (continuePull
        { s with
          frames := rest, pullAwaiting := false, jobs := s.jobs ++ [answer] } k) := by
  intros
  simp_all [returnPull]

/--
`op.readable-stream-close`.
Frozen branch equation for `streamClose_readable`, under the local M1/M2 views.
-/
theorem streamClose_readable :
  ∀ {α ε : Type} (s : State α ε), s.status = .readable →
    streamClose s =
      { s with
        status := .closed, readRequests := [], closedPromise := .fulfilled (),
        readPromises := s.readPromises.map (fun p ↦
          if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p),
        trace := s.trace ++ [.settled (.closed (.ok ()))] ++
          s.readRequests.map (fun id ↦ .settled (.read id (.ok .done))) } := by
  intros
  simp_all [streamClose]

/--
`op.readable-stream-close`.
Frozen branch equation for `streamClose_terminal`, under the local M1/M2 views.
-/
theorem streamClose_terminal :
  ∀ {α ε : Type} (s : State α ε),
    s.status ≠ .readable → streamClose s = s := by
  intro α ε s hs
  cases h : s.status <;> simp_all [streamClose]

/--
`op.readable-stream-default-reader-read`.
`op.rs-default-controller-private-pull` owns dequeue and final-chunk settlement order.
Frozen branch equation for `read_queued_eq`, under the local M1/M2 views.
-/
theorem read_queued_eq :
  ∀ {α ε : Type} (s : State α ε) (chunk : α)
    (q : Data.Queue α Size), s.status = .readable →
    Data.dequeueValue sizes s.queue = some (chunk, q) →
      read s =
        let t : State α ε :=
          { s with
            queue := q, nextRead := s.nextRead + 1,
            readPromises := s.readPromises ++ [(s.nextRead, .pending)] }
        if s.closeRequested = true ∧ q.entries = [] then
          continuePull (streamClose { t with
            algorithms := none })
            (.settleRead s.nextRead chunk)
        else callPullIfNeededWith t (.settleRead s.nextRead chunk) := by
  intros
  simp_all [read, Data.dequeueValue]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `finishEnqueue_thrown_nextError`, under the local M1/M2 views.
-/
theorem finishEnqueue_thrown_nextError :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (e : Boundary.Exception ε),
    (finishEnqueue s call chunk (.thrown e)).nextError = s.nextError := by
  intro α ε s call chunk e
  cases hs : s.status <;> simp [finishEnqueue, error, hs]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `resumeSize_size`, under the local M1/M2 views.
-/
theorem resumeSize_size :
  ∀ {α ε : Type} (s : State α ε) (call : Nat) (chunk : α)
    (rest : List (Frame α))
    (answer : Data.SizeAnswer Size
      (Boundary.Exception ε)),
    s.frames = .size call chunk :: rest → resumeSize s answer =
      some (finishEnqueue { s with frames := rest } call chunk answer) := by
  intros
  simp_all [resumeSize]

/--
`op.readable-stream-default-controller-enqueue`.
Frozen branch equation for `resumeSize_pull`, under the local M1/M2 views.
-/
theorem resumeSize_pull :
  ∀ {α ε : Type} (s : State α ε) (k :
    PullContinuation α)
    (rest : List (Frame α))
    (answer : Data.SizeAnswer Size
      (Boundary.Exception ε)),
    s.frames = .pull k :: rest → resumeSize s answer = none := by
  intros
  simp_all [resumeSize]

/--
`op.readable-stream-default-controller-get-desired-size`.
Frozen branch equation for `queryDesiredSize_eq`, under the local M1/M2 views.
-/
theorem queryDesiredSize_eq :
  ∀ {α ε : Type} (s : State α ε),
    queryDesiredSize s =
      { s with
        trace := s.trace ++ [.desiredSizeRead (desiredSize s)] } := by
  intros
  rfl

/-- Local observation law for `observeM2_eq` under DB-04; global embedding remains open. -/
theorem observeM2_eq :
  ∀ {α ε : Type} (s : State α ε), observeM2 s =
    { m1 := observeM1 s,
      visible := s.trace.filterMap (fun event ↦
        match event with
        | .settled settlement => some (.settlement settlement)
        | .desiredSizeRead size => some (.desiredSizeRead size)
        | .enqueueReturned call result => some (.enqueueReturned call result)
        | _ => none) } := by
  intros
  rfl

/-- Local observation law for `observeM2_toM1` under DB-04; global embedding remains open. -/
theorem observeM2_toM1 :
  ∀ {α ε : Type} (s : State α ε),
    (observeM2 s).m1 = observeM1 s := by
  intros
  rfl

/--
`op.readable-stream-default-controller-get-desired-size`.
Frozen branch equation for `queryDesiredSize_m2`, under the local M1/M2 views.
-/
theorem queryDesiredSize_m2 :
  ∀ {α ε : Type} (s : State α ε),
    (observeM2 (queryDesiredSize s)).visible =
      (observeM2 s).visible ++ [.desiredSizeRead
        (desiredSize s)] := by
  intros
  simp [queryDesiredSize, observeM2, List.filterMap_append]

private theorem continuePull_nextRead {α ε : Type} (s : State α ε)
    (k : PullContinuation α) : (continuePull s k).nextRead = s.nextRead := by
  cases k <;> rfl

private theorem callPullIfNeededWith_nextRead {α ε : Type} (s : State α ε)
    (k : PullContinuation α) : (callPullIfNeededWith s k).nextRead = s.nextRead := by
  cases hd : shouldCallPull s <;> cases hp : s.pulling <;> cases ha : s.algorithms <;>
    simp [callPullIfNeededWith, hd, hp, ha, continuePull_nextRead]

private theorem streamClose_nextRead {α ε : Type} (s : State α ε) :
    (streamClose s).nextRead = s.nextRead := by
  cases hs : s.status <;> simp [streamClose, hs]

/--
`op.readable-stream-default-reader-read`: allocate one read ID before suspension.
The local M2 continuation retains the ID across subsequent nested read allocations.
-/
theorem read_nextRead {α ε : Type} (s : State α ε) :
    (read s).nextRead = s.nextRead + 1 := by
  unfold read
  split
  · rfl
  · rfl
  · split
    · exact callPullIfNeededWith_nextRead _ .done
    · split
      · rw [continuePull_nextRead, streamClose_nextRead]
      · exact callPullIfNeededWith_nextRead _ _

/-! ## `PROMISE-PG-FIRST` bridging: the read-promise table view

`E-22` (generalize). The Streams slots stay exactly where they are; these two
lemmas present them as `Whatwg.Ecma262.Promise.Table`. `E-22` is deliberately
partial in this packet: `readPromises` has no `lookup`/`fresh`/`settle` of its
own, so only the view and its `get` law land now. Mask M1. -/

/-- `E-22`: the table view is exactly the read-promise slots, with no cell
marked handled — nothing in the readable calculus reads the bit. Mask M1. -/
theorem readTable_eq {α ε : Type} (s : State α ε) :
    readTable s =
      Whatwg.Ecma262.Promise.Table.mk
        (s.readPromises.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false)))
        s.nextRead := rfl

/-- `E-22`: the general lookup agrees with the inline slot lookup. Mask M1. -/
theorem readTable_get {α ε : Type} (s : State α ε) (id : Nat) :
    Whatwg.Ecma262.Promise.Table.get (readTable s) id =
      (s.readPromises.find? (fun p => p.1 == id)).map Prod.snd := by
  have key : ∀ (l : List (Nat × PromiseState (ReadResult α) ε)),
      Option.map Whatwg.Ecma262.Promise.Cell.state
          (Option.map Prod.snd
            (List.find? (fun e => e.1 == id)
              (l.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))))) =
        (l.find? (fun p => p.1 == id)).map Prod.snd := by
    intro l
    induction l with
    | nil => rfl
    | cons q rest ih =>
        simp only [List.map_cons, List.find?_cons]
        cases hb : (q.1 == id) with
        | true => rfl
        | false => exact ih
  exact key s.readPromises

end Whatwg.Streams.Readable
