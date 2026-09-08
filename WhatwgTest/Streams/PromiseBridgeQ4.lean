import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q4 battery for the four generalizations slice Q3 deferred.

Contract: `test/contracts/configuration-ordering.contract.md`, §5.
Graph: `PROMISE-PG-FIRST` (`docs/PROMISE-DAG.md`, "Q4" section).
Declared red: `test/fixtures/trust-gate/known-red.txt`.

Three of the four are rows 14, 15 and 16 of §4.4 of
`test/contracts/promise-first-packet.contract.md`, each a `generalize` row
whose bridge Q3 deferred with a stated reason. The fourth is `E-22`'s
operation-level generalization, deferred by §4.3 of the same contract because
it is a Streams *definition-body* change and the Q3 fence forbade one.
R-P20 records all four as Q4 work.

38 ascriptions: 18 for the four deferred generalizations, which are red today,
and 20 for the view conversions of §4 of the contract, which are green today
and must stay green. The builder must not change a statement in this file.

`E-22` is the only item here that changes an existing Streams definition body.
The exact new bodies are §5.4 of the contract; the five equation lemmas below
restate each pre-Q4 body verbatim and must close by `rfl`, which is what keeps
every dependent proof and every `attribute [local simp]` normal form. The
dependents the breaker verified by grep are listed in §5.4 too.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## `E-22` — the three operations that replace the five inline updates

`Readable.State.readPromises` has no `lookup`/`fresh`/`settle` of its own: the
five definitions `continuePull`, `streamClose`, `error`, `beginEnqueue` and
`read` update it inline, four by `List.map` and one by four appends. These
three operations are the Streams instances of
`Whatwg.Ecma262.Promise.Table.fresh` and `.settle` at value parameter
`Readable.ReadResult α`, which is the second instance R-P13 needed two type
parameters for.

`settleReadCell` is deliberately **unguarded**, exactly as the inline `List.map`
updates were: the landed `Table.settle` is guarded by `isPending` and a
non-pending settle is the identity (decision 7), so an unguarded body and the
guarded general operation agree only under the pending hypothesis. That
hypothesis is where `Table.settle_pending` puts them in agreement, and it is
carried explicitly by `readTable_settleReadCell` below. Silently adopting the
guard would change the meaning of four landed Streams bodies. -/

#check (@Whatwg.Streams.Readable.freshReadCell :
  ∀ {α ε : Type}, Readable.State α ε →
    Readable.PromiseState (Readable.ReadResult α) ε → Readable.State α ε × Nat)

#check (@Whatwg.Streams.Readable.settleReadCell :
  ∀ {α ε : Type}, Readable.State α ε → Nat →
    Except (Boundary.Exception ε) (Readable.ReadResult α) → Readable.State α ε)

#check (@Whatwg.Streams.Readable.settleReadCells :
  ∀ {α ε : Type}, Readable.State α ε → List Nat →
    Except (Boundary.Exception ε) (Readable.ReadResult α) → Readable.State α ε)

/-! ## `E-22` — the three bridges onto the landed table

`readTable` and `readTable_eq` landed at Q3. These three say that the Streams
operations are `Whatwg.Ecma262.Promise.Table.fresh` and `.settle` read through
it, at `value := Readable.ReadResult α`. Anchors: `op.newpromisecapability`
(2696238..2698770) for `fresh`, `op.fulfillpromise` (2695419..2696230) and
`op.rejectpromise` (2699323..2700252) for `settle`. Mask M1: none of the three
observes a settlement order. -/

#check (@Whatwg.Streams.Readable.readTable_freshReadCell :
  ∀ {α ε : Type} (s : Readable.State α ε)
    (outcome : Readable.PromiseState (Readable.ReadResult α) ε),
    (Readable.readTable (Readable.freshReadCell s outcome).1,
        (Readable.freshReadCell s outcome).2) =
      Whatwg.Ecma262.Promise.Table.fresh (Readable.readTable s) outcome)

#check (@Whatwg.Streams.Readable.readTable_settleReadCell :
  ∀ {α ε : Type} (s : Readable.State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) (Readable.ReadResult α)),
    Whatwg.Ecma262.Promise.Table.get (Readable.readTable s) id =
        some Whatwg.Ecma262.Promise.State.pending →
      Readable.readTable (Readable.settleReadCell s id result) =
        Whatwg.Ecma262.Promise.Table.settle (Readable.readTable s) id result)

#check (@Whatwg.Streams.Readable.readTable_settleReadCells :
  ∀ {α ε : Type} (s : Readable.State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) (Readable.ReadResult α)),
    ids.Nodup →
    (∀ id ∈ ids, Whatwg.Ecma262.Promise.Table.get (Readable.readTable s) id =
        some Whatwg.Ecma262.Promise.State.pending) →
      Readable.readTable (Readable.settleReadCells s ids result) =
        ids.foldl (fun t id => Whatwg.Ecma262.Promise.Table.settle t id result)
          (Readable.readTable s))

/-! ## `E-22` — the five equation lemmas that keep every dependent proof

Each restates the pre-Q4 body of one rewritten definition, verbatim, and must
close by `rfl`. A builder that cannot prove one of these by `rfl` has changed
the meaning of a Streams definition and is refused: the point of the
generalization is that the *body* is re-expressed, not that it computes
something else. Mask M1. -/

#check (@Whatwg.Streams.Readable.continuePull_settleRead_body :
  ∀ {α ε : Type} (s : Readable.State α ε) (id : Nat) (chunk : α),
    Readable.continuePull s (.settleRead id chunk) =
      { s with
        readPromises := s.readPromises.map fun p =>
          if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] })

#check (@Whatwg.Streams.Readable.streamClose_body :
  ∀ {α ε : Type} (s : Readable.State α ε),
    s.status = .readable →
      Readable.streamClose s =
        { s with
          status := .closed, readRequests := [], closedPromise := .fulfilled (),
          readPromises := s.readPromises.map fun p =>
            if p.1 ∈ s.readRequests then (p.1, .fulfilled .done) else p
          trace := s.trace ++ [.settled (.closed (.ok ()))] ++
            s.readRequests.map (fun id => .settled (.read id (.ok .done))) })

#check (@Whatwg.Streams.Readable.error_body :
  ∀ {α ε : Type} (s : Readable.State α ε) (e : Boundary.Exception ε),
    s.status = .readable →
      Readable.error s e =
        { s with
          status := .errored e, queue := Data.resetQueue Readable.sizes s.queue,
          algorithms := none, readRequests := [], closedPromise := .rejected e,
          readPromises := s.readPromises.map fun p =>
            if p.1 ∈ s.readRequests then (p.1, .rejected e) else p
          trace := s.trace ++ [.settled (.closed (.error e))] ++
            s.readRequests.map (fun id => .settled (.read id (.error e))) })

#check (@Whatwg.Streams.Readable.beginEnqueue_settle_body :
  ∀ {α ε : Type} (s : Readable.State α ε) (chunk : α) (id : Nat) (rest : List Nat),
    Readable.canCloseOrEnqueue s = true → s.readRequests = id :: rest →
      Readable.beginEnqueue s chunk =
        Readable.callPullIfNeededWith
          { s with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            readPromises := s.readPromises.map fun p =>
              if p.1 = id then (p.1, .fulfilled (.chunk chunk)) else p
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue))

#check (@Whatwg.Streams.Readable.read_body :
  ∀ {α ε : Type} (s : Readable.State α ε),
    Readable.read s =
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
          match Data.dequeueValue Readable.sizes s.queue with
          | none =>
              Readable.callPullIfNeeded
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
                Readable.continuePull (Readable.streamClose { t with algorithms := none })
                  (.settleRead s.nextRead chunk)
              else Readable.callPullIfNeededWith t (.settleRead s.nextRead chunk)))

/-! ## Row 14 — `Transform.notify` (`E-32`, generalize)

§4.4 row 14 of the Q3 contract defers this bridge because "only the queueing
half generalizes, and the component dispatch stays in Streams". `notifyJob` is
the queueing half made explicit: the tag each branch appends, independently of
the dispatch into `Readable.acceptPullAnswer` or `Writable.acceptAnswer` that
precedes it. The bridge then says the queue half is exactly the landed tail
append.

Anchor: `op.newpromisereactionjob` (2702885..2705591) followed by
`hook.hostenqueuepromisejob` (633447..635836). The landed
`Whatwg.Ecma262.Jobs.ReactionJob` is *not* the carrier: `Transform.Job`
carries three component tags of which only one is a reaction, and
`Jobs.Queue` is payload-polymorphic (decision 4) precisely so that its client
supplies the payload. Mask M2: the statement observes the job entering the
queue. -/

#check (@Whatwg.Streams.Transform.notifyJob :
  ∀ {α ε : Type}, Transform.Subscription α → Readable.PullAnswer ε → Transform.Job α ε)

#check (@Whatwg.Streams.Transform.notify_jobQueue_bridge :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (sub : Transform.Subscription α)
    (answer : Readable.PullAnswer ε) (t : Transform.State α β ε),
    Transform.notify s sub answer = some t →
      Transform.jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueue (Transform.jobQueue s)
          (Transform.notifyJob sub answer))

/-! ## Row 15 — `Transform.settle` (`E-33`, generalize)

§4.4 row 15 defers this bridge because relating the `foldlM` over the filtered
subscription list to `Table.settleAndTrigger` needs `notify`'s bridge first.
It now exists, so the three halves can be stated.

The reaction half is **not** an equality of reaction lists.
`Whatwg.Ecma262.Promise.triggerReactions` advances a triggered registration's
phase to `queued` and keeps it; `Transform.settle` deletes it from
`s.subscriptions`. The honest general statements are therefore the two the
landed module proves — `triggerReactions_order` (M2) and
`triggerReactions_once` (M1) — instantiated at this state: the jobs enter in
registration order, and no subscription on that identity is left waiting.

Anchors: `op.fulfillpromise` (2695419..2696230), `op.rejectpromise`
(2699323..2700252), `op.triggerpromisereactions` (2700260..2701212). -/

#check (@Whatwg.Streams.Transform.settle_table_bridge :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : Transform.State α β ε),
    Transform.lookupPromise s id = some .pending → Transform.settle s id answer = some t →
      Writable.promiseTable t.writable =
        Whatwg.Ecma262.Promise.Table.settle (Writable.promiseTable s.writable) id
          (match answer with
            | .fulfilled => Except.ok ()
            | .rejected e => Except.error e))

#check (@Whatwg.Streams.Transform.settle_jobQueue_order :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : Transform.State α β ε),
    Transform.lookupPromise s id = some .pending → Transform.settle s id answer = some t →
      Transform.jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (Transform.jobQueue s)
          ((s.subscriptions.filter (fun sub => Transform.subscriptionPromise sub == id)).map
            (fun sub => Transform.notifyJob sub answer)))

#check (@Whatwg.Streams.Transform.settle_waiting_once :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : Transform.State α β ε),
    Transform.lookupPromise s id = some .pending → Transform.settle s id answer = some t →
      Whatwg.Ecma262.Promise.Reactions.waitingOn (Transform.reactions t) id .fulfill = [])

/-! ## Row 16 — `Transform.runJob` (`E-51`, generalize)

§4.4 row 16 defers this bridge because the `.writable` branch re-checks that
the writable mailbox head matches the token, which is the CFG-TOKENS
correspondence and is stream-specific. The generalizable half is the dequeue:
the branch runs only when the landed `Jobs.Queue.dequeue` over Q3's
`Writable.jobQueue` offers a head, and it is blocked otherwise. The tick half
is already landed as `Writable.tick_dequeue_bridge`, so these two close the
row without restating it.

Anchors: `hook.hostenqueuepromisejob` (633447..635836) and its ordering bullet
`requirement.hostenqueuepromisejob.3` (634739..634841), under the run
condition `requirement.jobs.1` (625769..626250). Mask M2 for the first, M1 for
the second. -/

#check (@Whatwg.Streams.Transform.runJob_writable_dequeue :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat)
    (first : Writable.SinkJob α ε) (rest : List (Writable.SinkJob α ε)),
    s.writable.control = [] →
    Whatwg.Ecma262.Jobs.Queue.dequeue (Writable.jobQueue s.writable) =
        some (first, Whatwg.Ecma262.Jobs.Queue.mk rest) →
    first.kind = Writable.SinkKind.write → first.request = request →
      Transform.runJob s (.writable request) =
        (Writable.tick s.writable).map (Transform.withWritable s))

#check (@Whatwg.Streams.Transform.runJob_writable_blocked :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat),
    Whatwg.Ecma262.Jobs.Queue.dequeue (Writable.jobQueue s.writable) = none →
      Transform.runJob s (.writable request) = none)

/-! ## The view conversions, `E-07`..`E-12` — green today, and they must stay green

§4 of the contract. The P4–P7 declaration records for `Readable.PromiseState`,
`Writable.UnitPromise` and the `promises` slots change from naming Streams the
canonical owner to naming them **views** of
`Whatwg.Ecma262.Promise.State`/`.Table`, with the shared owner named. The
inventory's rows `E-07` through `E-12` record that the six conversions and
their eighteen `_eq` and roundtrip receipts already *are* those conversion
theorems, and that they survive Q3's moves by definitional equality.

The eighteen ascriptions below are the acceptance condition for that record
change: each names one of those declarations at its frozen P5 statement. They
elaborate today. If one stops elaborating after the Q4 landing, the record
change has no receipt and the landing is refused — a `view` row whose named
conversion does not elaborate is a second owner, not a view.

Anchors: PROCESSWRITE (`op.writable-stream-default-controller-process-write`,
277701..279180) for the family, and `slot.PromiseState` (2744957..2745252)
fused with `slot.PromiseResult` (2745263..2745619) for the shared owner. All
mask M1. -/

#check (@Whatwg.Streams.Writable.unitPromiseToShared :
  ∀ {ε : Type}, Writable.UnitPromise ε → Readable.PromiseState Unit ε)
#check (@Whatwg.Streams.Writable.unitPromiseFromShared :
  ∀ {ε : Type}, Readable.PromiseState Unit ε → Writable.UnitPromise ε)
#check (@Whatwg.Streams.Writable.sinkAnswerToShared :
  ∀ {ε : Type}, Writable.SinkAnswer ε → Readable.PullAnswer ε)
#check (@Whatwg.Streams.Writable.sinkAnswerFromShared :
  ∀ {ε : Type}, Readable.PullAnswer ε → Writable.SinkAnswer ε)
#check (@Whatwg.Streams.Writable.sinkReturnToShared :
  ∀ {ε : Type}, Writable.SinkReturn ε → Readable.PullReturn ε)
#check (@Whatwg.Streams.Writable.sinkReturnFromShared :
  ∀ {ε : Type}, Readable.PullReturn ε → Writable.SinkReturn ε)

#check (@Whatwg.Streams.Writable.unitPromise_eq :
  ∀ {ε : Type}, Writable.UnitPromise ε = Readable.PromiseState Unit ε)
#check (@Whatwg.Streams.Writable.unitPromiseToShared_eq :
  ∀ {ε : Type} (a : Writable.UnitPromise ε), Writable.unitPromiseToShared a = a)
#check (@Whatwg.Streams.Writable.unitPromiseFromShared_eq :
  ∀ {ε : Type} (a : Readable.PromiseState Unit ε), Writable.unitPromiseFromShared a = a)
#check (@Whatwg.Streams.Writable.unitPromise_roundtrip :
  ∀ {ε : Type} (a : Writable.UnitPromise ε),
    Writable.unitPromiseFromShared (Writable.unitPromiseToShared a) = a)

#check (@Whatwg.Streams.Writable.sinkAnswer_eq :
  ∀ {ε : Type}, Writable.SinkAnswer ε = Readable.PullAnswer ε)
#check (@Whatwg.Streams.Writable.sinkAnswerToShared_eq :
  ∀ {ε : Type} (a : Writable.SinkAnswer ε), Writable.sinkAnswerToShared a = a)
#check (@Whatwg.Streams.Writable.sinkAnswerFromShared_eq :
  ∀ {ε : Type} (a : Readable.PullAnswer ε), Writable.sinkAnswerFromShared a = a)
#check (@Whatwg.Streams.Writable.sinkAnswer_roundtrip :
  ∀ {ε : Type} (a : Writable.SinkAnswer ε),
    Writable.sinkAnswerFromShared (Writable.sinkAnswerToShared a) = a)

#check (@Whatwg.Streams.Writable.sinkReturn_eq :
  ∀ {ε : Type}, Writable.SinkReturn ε = Readable.PullReturn ε)
#check (@Whatwg.Streams.Writable.sinkReturnToShared_eq :
  ∀ {ε : Type} (a : Writable.SinkReturn ε), Writable.sinkReturnToShared a = a)
#check (@Whatwg.Streams.Writable.sinkReturnFromShared_eq :
  ∀ {ε : Type} (a : Readable.PullReturn ε), Writable.sinkReturnFromShared a = a)
#check (@Whatwg.Streams.Writable.sinkReturn_roundtrip :
  ∀ {ε : Type} (a : Writable.SinkReturn ε),
    Writable.sinkReturnFromShared (Writable.sinkReturnToShared a) = a)

/-! ## The two landed table views the `view` record rows name

`Writable.promiseTable` and `Readable.readTable` landed at Q3. They are the
declarations the amended duplicate-prevention rows point at as the shared
owner, so they are ascribed here too and must keep elaborating. Mask M1. -/

#check (@Whatwg.Streams.Writable.promiseTable :
  ∀ {α ε : Type}, Writable.State α ε →
    Whatwg.Ecma262.Promise.Table Unit (Boundary.Exception ε))
#check (@Whatwg.Streams.Readable.readTable :
  ∀ {α ε : Type}, Readable.State α ε →
    Whatwg.Ecma262.Promise.Table (Readable.ReadResult α) (Boundary.Exception ε))
