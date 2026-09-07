import Whatwg.Streams.Readable.Step

/-!
# Frozen default-readable equations

Owner: READABLE-PG-DEFAULT. These proofs discharge the exact P4a battery statements.
They contribute to the local M1/M2 views; global reachability and host embeddings remain open.
The state, controller, reader and step modules own their underlying operations and anchors.
-/

namespace Whatwg.Streams.Readable

/-! ## `E-22` (generalize, Q4): the five equation lemmas that keep every dependent proof

Slice Q4 re-expresses five definition **bodies** through `freshReadCell`,
`settleReadCell` and `settleReadCells`. Each lemma below restates the pre-Q4
body of one rewritten definition verbatim, and each closes definitionally, which
is what keeps `simp [continuePull]`, `simp [streamClose]` and the
`attribute [local simp]` normal forms of the four `simp`-set modules rewriting
exactly as before. Contract: `test/contracts/configuration-ordering.contract.md`
§5.4. Mask M1. -/

/-- `E-22` (Q4): `continuePull`'s settle branch, at its pre-Q4 body. Mask M1. -/
theorem continuePull_settleRead_body {α ε : Type} (s : State α ε) (id : Nat) (chunk : α) :
    continuePull s (.settleRead id chunk) =
      { s with
        readPromises := s.readPromises.map fun p =>
          if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] } := rfl

/-- `E-22` (Q4): `streamClose`'s readable branch, at its pre-Q4 body. Mask M1. -/
theorem streamClose_body {α ε : Type} (s : State α ε) :
    s.status = .readable →
      streamClose s =
        { s with
          status := .closed, readRequests := [], closedPromise := .fulfilled (),
          readPromises := s.readPromises.map fun p =>
            if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p
          trace := s.trace ++ [.settled (.closed (.ok ()))] ++
            s.readRequests.map (fun id => .settled (.read id (.ok .done))) } := by
  intro h
  unfold streamClose
  rw [h]
  rfl

/-- `E-22` (Q4): `error`'s readable branch, at its pre-Q4 body. Mask M1. -/
theorem error_body {α ε : Type} (s : State α ε) (e : Boundary.Exception ε) :
    s.status = .readable →
      error s e =
        { s with
          status := .errored e, queue := Data.resetQueue sizes s.queue,
          algorithms := none, readRequests := [], closedPromise := .rejected e,
          readPromises := s.readPromises.map fun p =>
            if p.1 ∈ s.readRequests then (p.1, .rejected e) else p
          trace := s.trace ++ [.settled (.closed (.error e))] ++
            s.readRequests.map (fun id => .settled (.read id (.error e))) } := by
  intro h
  unfold error
  rw [h]
  rfl

/-- `E-22` (Q4): `beginEnqueue`'s pending-read branch, at its pre-Q4 body. Mask M1. -/
theorem beginEnqueue_settle_body {α ε : Type} (s : State α ε) (chunk : α) (id : Nat)
    (rest : List Nat) :
    canCloseOrEnqueue s = true → s.readRequests = id :: rest →
      beginEnqueue s chunk =
        callPullIfNeededWith
          { s with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            readPromises := s.readPromises.map fun p =>
              if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue) := by
  intro h1 h2
  unfold beginEnqueue
  rw [h1, h2]
  rfl

/-- `E-22` (Q4): `read`, at its pre-Q4 body. Mask M1. -/
theorem read_body {α ε : Type} (s : State α ε) :
    read s =
      (match s.status with
      | .closed =>
          { s with
            nextRead := s.nextRead + 1,
            readPromises := s.readPromises ++ [(s.nextRead, .fulfilled .done)],
            trace := s.trace ++ [.settled (.read s.nextRead (.ok .done))] }
      | .errored e =>
          { s with
            nextRead := s.nextRead + 1,
            readPromises := s.readPromises ++ [(s.nextRead, .rejected e)],
            trace := s.trace ++ [.settled (.read s.nextRead (.error e))] }
      | .readable =>
          match Data.dequeueValue sizes s.queue with
          | none =>
              callPullIfNeeded
                { s with
                  nextRead := s.nextRead + 1,
                  readPromises := s.readPromises ++ [(s.nextRead, .pending)],
                  readRequests := s.readRequests ++ [s.nextRead] }
          | some (chunk, q) =>
              let t :=
                { s with
                  queue := q, nextRead := s.nextRead + 1,
                  readPromises := s.readPromises ++ [(s.nextRead, .pending)] }
              if s.closeRequested = true ∧ q.entries = [] then
                continuePull (streamClose { t with algorithms := none })
                  (.settleRead s.nextRead chunk)
              else callPullIfNeededWith t (.settleRead s.nextRead chunk)) := rfl

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

/-- `E-48` (generalize, `PROMISE-PG-FIRST`): the view is exactly the pull-answer job list. Mask M1. -/
theorem jobQueue_eq {α ε : Type} (s : State α ε) :
    jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs := rfl

/--
`E-49` (generalize, `PROMISE-PG-FIRST`). The honest bridging shape: under the readable
component's own spelling of `requirement.jobs.1` — an empty synchronous frame stack —
`runPullJob` *reduces to* `Whatwg.Ecma262.Jobs.Queue.dequeue`. Mask M2.
-/
theorem runPullJob_dequeue_bridge {α ε : Type} (s : State α ε) :
    s.frames = [] →
      runPullJob s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (jobQueue s)).map
          (fun p => reactPull { s with jobs := p.2.pending } p.1) := by
  intro hf
  cases hj : s.jobs <;>
    simp [runPullJob, jobQueue, Whatwg.Ecma262.Jobs.Queue.dequeue, hf, hj]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_suspended`, under the local M1/M2 views.
This one is the component's frame guard rather than a queue law, so it is not a
consequence of `runPullJob_dequeue_bridge`, whose hypothesis it denies.
-/
theorem runPullJob_suspended :
  ∀ {α ε : Type} (s : State α ε),
    s.frames ≠ [] → runPullJob s = none := by
  intros
  simp_all [runPullJob]

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_empty`, under the local M1/M2 views.
Re-derived through `runPullJob_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_empty`, never re-proved from `runPullJob`.
-/
theorem runPullJob_empty :
  ∀ {α ε : Type} (s : State α ε),
    s.jobs = [] → runPullJob s = none := by
  intro α ε s hj
  by_cases hf : s.frames = []
  · rw [runPullJob_dequeue_bridge s hf, jobQueue_eq, hj]
    exact congrArg _ Whatwg.Ecma262.Jobs.Queue.dequeue_empty
  · exact runPullJob_suspended s hf

/--
`op.readable-stream-default-controller-call-pull-if-needed`.
Frozen branch equation for `runPullJob_cons`, under the local M1/M2 views.
Re-derived through `runPullJob_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_cons`, never re-proved from `runPullJob`.
-/
theorem runPullJob_cons :
  ∀ {α ε : Type} (s : State α ε) (a : PullAnswer ε)
    (rest : List (PullAnswer ε)),
    s.frames = [] → s.jobs = a :: rest →
      runPullJob s = some (reactPull { s with jobs
        := rest } a) := by
  intro α ε s a rest hf hj
  rw [runPullJob_dequeue_bridge s hf, jobQueue_eq, hj,
    Whatwg.Ecma262.Jobs.Queue.dequeue_cons]
  rfl

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
  rw [read_body]
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

/-! ## `E-22` (generalize, Q4): the three operations bridged onto the landed table

`freshReadCell`, `settleReadCell` and `settleReadCells` are the Streams
instances of `Whatwg.Ecma262.Promise.Table.fresh` and `.settle` at value
parameter `ReadResult α`, read through `readTable`. Anchors:
`op.newpromisecapability` (2696238..2698770) for `fresh`, `op.fulfillpromise`
(2695419..2696230) and `op.rejectpromise` (2699323..2700252) for `settle`.
Mask M1: none of the three observes a settlement order. Contract §5.4. -/

/-- `E-22` (Q4): allocating a read cell is the landed append-only allocation
read through the view, cursor included. Mask M1. -/
theorem readTable_freshReadCell {α ε : Type} (s : State α ε)
    (outcome : PromiseState (ReadResult α) ε) :
    (readTable (freshReadCell s outcome).1, (freshReadCell s outcome).2) =
      Whatwg.Ecma262.Promise.Table.fresh (readTable s) outcome := by
  simp [readTable, Whatwg.Ecma262.Promise.Table.fresh]

/-- `E-22` (Q4): overwriting one pending read cell is the landed guarded settle
read through the view. The pending hypothesis is where the unguarded Streams
body and the guarded general operation agree (decision 7). Mask M1. -/
theorem readTable_settleReadCell {α ε : Type} (s : State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) :
    Whatwg.Ecma262.Promise.Table.get (readTable s) id =
        some Whatwg.Ecma262.Promise.State.pending →
      readTable (settleReadCell s id result) =
        Whatwg.Ecma262.Promise.Table.settle (readTable s) id result := by
  intro h
  rw [Whatwg.Ecma262.Promise.Table.settle_pending _ _ _ h]
  simp only [readTable, settleReadCell, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p _
  cases result <;> by_cases hb : p.1 = id <;> simp [hb]

/-! The three facts the set-shaped bridge needs: settling one identity leaves
every lookup at a different identity alone, and two successive keyed updates
with the same replacement are one update on the union of their keys. -/

private theorem table_get_settle_other {value reason : Type}
    (t : Whatwg.Ecma262.Promise.Table value reason) (a i : Nat)
    (r : Except reason value) (hne : ¬ i = a) :
    Whatwg.Ecma262.Promise.Table.get (Whatwg.Ecma262.Promise.Table.settle t a r) i =
      Whatwg.Ecma262.Promise.Table.get t i := by
  by_cases hp :
      Whatwg.Ecma262.Promise.Table.get t a = some Whatwg.Ecma262.Promise.State.pending
  · have key : ∀ (g : Whatwg.Ecma262.Promise.Cell value reason →
          Whatwg.Ecma262.Promise.Cell value reason)
        (l : List (Nat × Whatwg.Ecma262.Promise.Cell value reason)),
        List.find? (fun e => e.1 == i) (l.map (fun e => if e.1 == a then (e.1, g e.2) else e)) =
          List.find? (fun e => e.1 == i) l := by
      intro g l
      induction l with
      | nil => rfl
      | cons e rest ih =>
          by_cases hb : (e.1 == a) = true
          · have hea : e.1 = a := by simpa using hb
            have hei : (e.1 == i) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro hh
              exact hne (hh ▸ hea)
            simp only [List.map_cons, if_pos hb, List.find?_cons, hei]
            exact ih
          · simp only [List.map_cons, if_neg hb, List.find?_cons]
            cases hbi : (e.1 == i) with
            | true => rfl
            | false => exact ih
    rw [Whatwg.Ecma262.Promise.Table.settle_pending _ _ _ hp]
    simp only [Whatwg.Ecma262.Promise.Table.get, Whatwg.Ecma262.Promise.Table.getCell]
    exact congrArg (Option.map Whatwg.Ecma262.Promise.Cell.state)
      (congrArg (Option.map Prod.snd)
        (key (fun c => Whatwg.Ecma262.Promise.Cell.mk
          (match r with
            | .ok v => Whatwg.Ecma262.Promise.State.fulfilled v
            | .error x => Whatwg.Ecma262.Promise.State.rejected x) c.handled) t.entries))
  · rw [Whatwg.Ecma262.Promise.Table.settle_other t a r hp]

private theorem map_settle_cons {α ε : Type} (a : Nat) (ids : List Nat)
    (V : PromiseState (ReadResult α) ε)
    (l : List (Nat × PromiseState (ReadResult α) ε)) :
    (l.map (fun p => if p.1 = a then (p.1, V) else p)).map
        (fun p => if p.1 ∈ ids then (p.1, V) else p) =
      l.map (fun p => if p.1 ∈ a :: ids then (p.1, V) else p) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  by_cases hb : p.1 = a <;> by_cases hi : p.1 ∈ ids <;> simp [hb, hi]

private theorem foldl_settle_readTable {α ε : Type}
    (result : Except (Boundary.Exception ε) (ReadResult α))
    (V : PromiseState (ReadResult α) ε)
    (hsettle : ∀ (t : Whatwg.Ecma262.Promise.Table (ReadResult α) (Boundary.Exception ε))
        (i : Nat),
      Whatwg.Ecma262.Promise.Table.get t i = some Whatwg.Ecma262.Promise.State.pending →
        Whatwg.Ecma262.Promise.Table.settle t i result =
          Whatwg.Ecma262.Promise.Table.mk
            (t.entries.map (fun e =>
              if e.1 == i then (e.1, Whatwg.Ecma262.Promise.Cell.mk V e.2.handled) else e))
            t.next)
    (ids : List Nat) :
    ∀ (l : List (Nat × PromiseState (ReadResult α) ε)) (next : Nat),
      ids.Nodup →
      (∀ i ∈ ids, Whatwg.Ecma262.Promise.Table.get
          (Whatwg.Ecma262.Promise.Table.mk
            (l.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next) i =
        some Whatwg.Ecma262.Promise.State.pending) →
        ids.foldl (fun t i => Whatwg.Ecma262.Promise.Table.settle t i result)
            (Whatwg.Ecma262.Promise.Table.mk
              (l.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next) =
          Whatwg.Ecma262.Promise.Table.mk
            ((l.map (fun p => if p.1 ∈ ids then (p.1, V) else p)).map
              (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next := by
  induction ids with
  | nil => intro l next _ _; simp
  | cons a rest ih =>
      intro l next hnd hp
      have hpa := hp a (by simp)
      have hstep :
          Whatwg.Ecma262.Promise.Table.settle
              (Whatwg.Ecma262.Promise.Table.mk
                (l.map (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next)
              a result =
            Whatwg.Ecma262.Promise.Table.mk
              ((l.map (fun p => if p.1 = a then (p.1, V) else p)).map
                (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next := by
        rw [hsettle _ _ hpa]
        simp only [List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro p _
        by_cases hb : p.1 = a <;> simp [hb]
      have hrest : ∀ i ∈ rest, Whatwg.Ecma262.Promise.Table.get
          (Whatwg.Ecma262.Promise.Table.mk
            ((l.map (fun p => if p.1 = a then (p.1, V) else p)).map
              (fun p => (p.1, Whatwg.Ecma262.Promise.Cell.mk p.2 false))) next) i =
          some Whatwg.Ecma262.Promise.State.pending := by
        intro i hi
        have hne : ¬ i = a := fun hh => (List.nodup_cons.mp hnd).1 (hh ▸ hi)
        rw [← hstep, table_get_settle_other _ a i result hne]
        exact hp i (by simp [hi])
      rw [List.foldl_cons, hstep, ih _ _ (List.nodup_cons.mp hnd).2 hrest, map_settle_cons]

/-- `E-22` (Q4): overwriting a set of distinct pending read cells is the landed
guarded settle applied once per identity, in list order, read through the view.
Mask M1. -/
theorem readTable_settleReadCells {α ε : Type} (s : State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) :
    ids.Nodup →
    (∀ id ∈ ids, Whatwg.Ecma262.Promise.Table.get (readTable s) id =
        some Whatwg.Ecma262.Promise.State.pending) →
      readTable (settleReadCells s ids result) =
        ids.foldl (fun t id => Whatwg.Ecma262.Promise.Table.settle t id result)
          (readTable s) := by
  intro hnd hp
  obtain ⟨V, hsettle, hcells⟩ :
      ∃ V : PromiseState (ReadResult α) ε,
        (∀ (t : Whatwg.Ecma262.Promise.Table (ReadResult α) (Boundary.Exception ε)) (i : Nat),
          Whatwg.Ecma262.Promise.Table.get t i = some Whatwg.Ecma262.Promise.State.pending →
            Whatwg.Ecma262.Promise.Table.settle t i result =
              Whatwg.Ecma262.Promise.Table.mk
                (t.entries.map (fun e =>
                  if e.1 == i then (e.1, Whatwg.Ecma262.Promise.Cell.mk V e.2.handled) else e))
                t.next) ∧
        (∀ (u : State α ε) (js : List Nat),
          settleReadCells u js result =
            { u with readPromises := u.readPromises.map (fun p =>
                if p.1 ∈ js then (p.1, V) else p) }) := by
    cases result with
    | ok v =>
        exact ⟨Whatwg.Ecma262.Promise.State.fulfilled v,
          fun t i h => Whatwg.Ecma262.Promise.Table.settle_pending t i _ h,
          fun _ _ => rfl⟩
    | error e =>
        exact ⟨Whatwg.Ecma262.Promise.State.rejected e,
          fun t i h => Whatwg.Ecma262.Promise.Table.settle_pending t i _ h,
          fun _ _ => rfl⟩
  rw [hcells s ids]
  simp only [readTable]
  exact (foldl_settle_readTable result V hsettle ids s.readPromises s.nextRead hnd hp).symm

end Whatwg.Streams.Readable
