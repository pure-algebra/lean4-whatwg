import Whatwg.Streams

/-! Frozen P6a representative stage equations and three composed runs, 2026-09-05.
Graph: TRANSFORM-PG-BACKPRESSURE. These are local adapter/transition obligations.
Their joint trace supports the future named DB-04 embedding; it is not yet global M2.
-/

set_option autoImplicit false
open Whatwg.Streams

#check (@Transform.withReadable_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (r : Readable.State β ε),
   Transform.withReadable s r = { s with
     readable := r,
     trace := s.trace ++ (r.trace.drop s.readable.trace.length).map Transform.Event.readable })

#check (@Transform.withWritable_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (w : Writable.State α ε),
   Transform.withWritable s w = { s with
     writable := w,
     trace := s.trace ++ (w.trace.drop s.writable.trace.length).map Transform.Event.writable })

#check (@Transform.lookupPromise_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat),
   Transform.lookupPromise s id =
     (Writable.lookupPromise s.writable id).map Writable.unitPromiseToShared)

#check (@Transform.freshInternal_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.freshInternal s =
     (let (w, id) := Writable.freshPromise s.writable .pending
      let t := Transform.withWritable s w
      ({ t with internalPromises := t.internalPromises ++ [id] }, id)))

#check (@Transform.freshInternal_old :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat), id ≠ s.writable.nextPromise →
   Transform.lookupPromise (Transform.freshInternal s).1 id = Transform.lookupPromise s id)

#check (@Transform.freshInternal_new :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Writable.lookupPromise s.writable s.writable.nextPromise = none →
   Transform.lookupPromise (Transform.freshInternal s).1 (Transform.freshInternal s).2 =
     some .pending)

#check (@Transform.freshInternal_identity :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   (Transform.freshInternal s).2 = s.writable.nextPromise ∧
   (Transform.freshInternal s).1.writable.readyPromise = s.writable.readyPromise ∧
   (Transform.freshInternal s).1.writable.closedPromise = s.writable.closedPromise ∧
   (Transform.freshInternal s).1.writable.inFlightWrite = s.writable.inFlightWrite)

#check (@Transform.subscriptionPromise_readable :
  ∀ {α : Type} (id : Nat),
   Transform.subscriptionPromise (Transform.Subscription.readable (α := α) id) = id)

#check (@Transform.subscriptionPromise_writable :
  ∀ {α : Type} (id request : Nat),
   Transform.subscriptionPromise (Transform.Subscription.writable (α := α) id request) = id)

#check (@Transform.subscriptionPromise_reaction :
  ∀ {α : Type} (id : Nat) (k : Transform.Reaction α),
   Transform.subscriptionPromise (.reaction id k) = id)

#check (@Transform.notify_readable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (promise : Nat) (a : Readable.PullAnswer ε) (r :
    Readable.State β ε),
   Readable.acceptPullAnswer s.readable a = some r →
   Transform.notify s (.readable promise) a =
     some { Transform.withReadable s r with jobs := s.jobs ++ [.readable promise] })

#check (@Transform.notify_writable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (promise request : Nat) (a : Readable.PullAnswer
    ε)
   (w : Writable.State α ε),
   Writable.acceptAnswer s.writable .write request (Writable.sinkAnswerFromShared a) = some w →
   Transform.notify s (.writable promise request) a =
     some { Transform.withWritable s w with jobs := s.jobs ++ [.writable request] })

#check (@Transform.notify_reaction :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (promise : Nat) (k : Transform.Reaction α) (a :
    Readable.PullAnswer ε),
   Transform.notify s (.reaction promise k) a = some { s with jobs := s.jobs ++ [.reaction k a] })

#check (@Transform.subscribe_pending :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (sub : Transform.Subscription α),
   Transform.lookupPromise s (Transform.subscriptionPromise sub) = some .pending →
   Transform.subscribe s sub = some { s with subscriptions := s.subscriptions ++ [sub] })

#check (@Transform.subscribe_fulfilled :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (sub : Transform.Subscription α),
   Transform.lookupPromise s (Transform.subscriptionPromise sub) = some (.fulfilled ()) →
   Transform.subscribe s sub = Transform.notify s sub .fulfilled)

#check (@Transform.subscribe_rejected :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (sub : Transform.Subscription α) (e :
    Boundary.Exception ε),
   Transform.lookupPromise s (Transform.subscriptionPromise sub) = some (.rejected e) →
   Transform.subscribe s sub = Transform.notify s sub (.rejected e))

#check (@Transform.subscribe_missing :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (sub : Transform.Subscription α),
   Transform.lookupPromise s (Transform.subscriptionPromise sub) = none →
   Transform.subscribe s sub = none)

#check (@Transform.settle_other :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat) (a : Readable.PullAnswer ε),
   Transform.lookupPromise s id ≠ some .pending →
   Transform.settle s id a = some s)

#check (@Transform.settle_pending :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (id : Nat) (a : Readable.PullAnswer ε),
   Transform.lookupPromise s id = some .pending →
   Transform.settle s id a =
     (let outcome : Except (Boundary.Exception ε) Unit :=
        match a with | .fulfilled => .ok () | .rejected e => .error e
      let t := Transform.withWritable s (Writable.settle s.writable id outcome)
      let resting := { t with
        subscriptions := s.subscriptions.filter (fun sub ↦ Transform.subscriptionPromise sub !=
          id) }
      (s.subscriptions.filter (fun sub ↦ Transform.subscriptionPromise sub == id)).foldlM
        (fun u sub ↦ Transform.notify u sub a) resting))

#check (@Transform.setBackpressure_same :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (b : Bool), s.backpressure = b →
   Transform.setBackpressure s b = some s)

#check (@Transform.setBackpressure_change :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (b : Bool), s.backpressure ≠ b →
   Transform.setBackpressure s b =
     (do
       let t ← Transform.settle s s.backpressurePromise .fulfilled
       let (u, fresh) := Transform.freshInternal t
       pure { u with backpressure := b, backpressurePromise := fresh }))

#check (@Transform.unblockWrite_true :
  ∀ {α β ε : Type} (s : Transform.State α β ε), s.backpressure = true →
   Transform.unblockWrite s = Transform.setBackpressure s false)

#check (@Transform.unblockWrite_false :
  ∀ {α β ε : Type} (s : Transform.State α β ε), s.backpressure = false →
   Transform.unblockWrite s = some s)

#check (@Transform.sourcePull_realizes :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (k : Readable.PullContinuation β)
   (rest : List (Readable.Frame β)) (t u : Transform.State α β ε) (r : Readable.State β ε),
   s.readable.frames = .pull k :: rest → s.backpressure = true →
   Transform.setBackpressure s false = some t →
   Readable.returnPull t.readable .pending = some r →
   Transform.subscribe (Transform.withReadable t r) (.readable t.backpressurePromise) = some u →
   Transform.sourcePull s = some (u, t.backpressurePromise))

#check (@Transform.sourcePull_requires_pressure :
  ∀ {α β ε : Type} (s : Transform.State α β ε), s.backpressure = false →
   Transform.sourcePull s = none)

#check (@Transform.sourcePull_requires_frame :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   (∀ k rest, s.readable.frames ≠ .pull k :: rest) → Transform.sourcePull s = none)

#check (@Transform.servicePull_empty :
  ∀ {α β ε : Type} (s : Transform.State α β ε), s.readable.frames = [] → Transform.servicePull s
    = some s)

#check (@Transform.servicePull_pull :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (k : Readable.PullContinuation β)
   (rest : List (Readable.Frame β)), s.readable.frames = .pull k :: rest →
   Transform.servicePull s = (Transform.sourcePull s).map Prod.fst)

#check (@Transform.servicePull_size :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (call : Nat) (chunk : β) (rest : List
    (Readable.Frame β)),
   s.readable.frames = .size call chunk :: rest → Transform.servicePull s = none)

#check (@Transform.read_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.read s = Transform.servicePull (Transform.withReadable s (Readable.read s.readable)))

#check (@Transform.performTransform_present :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (a : Transform.Algorithms) (request : Nat) (chunk
    : α)
   (completion : Transform.Completion), s.algorithms = some a →
   Transform.performTransform s request chunk completion =
     some { s with
       control := .awaitTransform request completion s.writable.control.length :: s.control,
       trace := s.trace ++ [.transformCalled request a.transform chunk] })

#check (@Transform.performTransform_missing :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (chunk : α)
   (completion : Transform.Completion), s.algorithms = none →
   Transform.performTransform s request chunk completion = none)

#check (@Transform.react_write_writable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (chunk : α),
   s.writable.status = .writable →
   Transform.react s (.write request chunk result) .fulfilled =
     Transform.performTransform s request chunk (.adopt result))

#check (@Transform.react_write_erroring :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   s.writable.status = .erroring e →
   Transform.react s (.write request chunk result) .fulfilled =
     Transform.settle s result (.rejected e))

#check (@Transform.react_write_closed :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (chunk : α),
   s.writable.status = .closed →
   Transform.react s (.write request chunk result) .fulfilled = none)

#check (@Transform.react_write_errored :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   s.writable.status = .errored e →
   Transform.react s (.write request chunk result) .fulfilled = none)

#check (@Transform.react_write_rejected :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   Transform.react s (.write request chunk result) (.rejected e) =
     Transform.settle s result (.rejected e))

#check (@Transform.react_transform_fulfilled :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (result : Nat),
   Transform.react s (.transform result) .fulfilled = Transform.settle s result .fulfilled)

#check (@Transform.react_transform_rejected :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (result : Nat) (e : Boundary.Exception ε),
   Transform.react s (.transform result) (.rejected e) =
     (let t := Transform.withReadable s (Readable.error s.readable e)
      some { t with
        algorithms := none,
        control := .errorWritable e :: .unblock :: .settle result (.rejected e) :: s.control }))

#check (@Transform.react_adopt :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (result : Nat) (a : Readable.PullAnswer ε),
   Transform.react s (.adopt result) a = Transform.settle s result a)

#check (@Transform.error_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (e : Boundary.Exception ε),
   Transform.error s e =
     (let t := Transform.withReadable s (Readable.error s.readable e)
      { t with algorithms := none, control := .errorWritable e :: .unblock :: s.control }))

#check (@Transform.terminate_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.terminate s =
     (let reason : Boundary.Exception ε := .typeError s.writable.nextError
      let t := Transform.withReadable s (Readable.close s.readable)
      let u := Transform.withWritable t { t.writable with nextError := t.writable.nextError + 1 }
      { u with algorithms := none, control := .errorWritable reason :: .unblock :: s.control }))

#check (@Transform.sinkWrite_blocked :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.readable.frames = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   s.writable.status = .writable →
   s.writable.algorithms.write = some (.foreign s.ports.write) →
   Writable.operationPhase s.writable .write request = some .invoking →
   s.backpressure = true →
   Transform.sinkWrite s =
     (do
       let (t, result) := Transform.freshInternal s
       let w ← Writable.decide t.writable (.returnSink .pending)
       let u ← Transform.subscribe (Transform.withWritable t w) (.writable result request)
       Transform.subscribe u (.reaction s.backpressurePromise (.write request chunk result))))

#check (@Transform.sinkWrite_direct :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.readable.frames = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   s.writable.status = .writable →
   s.writable.algorithms.write = some (.foreign s.ports.write) →
   Writable.operationPhase s.writable .write request = some .invoking →
   s.backpressure = false →
   Transform.sinkWrite s = Transform.performTransform s request chunk .direct)

#check (@Transform.sinkWrite_inside_transform :
  ∀ {α β ε : Type} (s : Transform.State α β ε), s.control ≠ [] → Transform.sinkWrite s = none)

#check (@Transform.sinkWrite_requires_frame :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   (∀ request chunk tail, s.writable.control ≠ .awaitSink (.write request chunk) :: tail) →
   Transform.sinkWrite s = none)

#check (@Transform.answerTransform_waiting :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request result : Nat) (a : Readable.PullAnswer
    ε),
   s.pendingTransforms.find? (fun p ↦ p.1 == request) = some (request, result) →
   Transform.answerTransform s request a =
     some { s with
       pendingTransforms := s.pendingTransforms.filter (fun p ↦ p.1 != request),
       jobs := s.jobs ++ [.reaction (.transform result) a] })

#check (@Transform.answerTransform_unmatched :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (a : Readable.PullAnswer ε),
   s.pendingTransforms.find? (fun p ↦ p.1 == request) = none →
   Transform.answerTransform s request a = none)

#check (@Transform.returnTransform_frame :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request depth : Nat) (completion :
    Transform.Completion)
   (tail : List (Transform.Control ε)) (ret : Readable.PullReturn ε),
   s.control = .awaitTransform request completion depth :: tail →
   s.readable.frames = [] → s.writable.control.length = depth →
   Transform.returnTransform s ret =
     (do
       let (t, result) := Transform.freshInternal { s with control := tail }
       let u : Transform.State α β ε := match ret with
         | .pending => { t with pendingTransforms := t.pendingTransforms ++ [(request, result)] }
         | .settled a => { t with jobs := t.jobs ++ [.reaction (.transform result) a] }
       let v := { u with trace := u.trace ++ [.transformReturned request result] }
       match completion with
       | .direct =>
           match v.writable.control with
           | .awaitSink (.write request' _) :: _ =>
               if request' == request then
                 let w ← Writable.decide v.writable (.returnSink .pending)
                 Transform.subscribe (Transform.withWritable v w) (.writable result request)
               else none
           | _ => none
       | .adopt target => Transform.subscribe v (.reaction result (.adopt target))))

#check (@Transform.returnTransform_unmatched :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (ret : Readable.PullReturn ε),
   (∀ request completion depth tail,
     s.control ≠ .awaitTransform request completion depth :: tail) →
   Transform.returnTransform s ret = none)

#check (@Transform.returnTransform_nested_writable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request depth : Nat)
   (completion : Transform.Completion) (tail : List (Transform.Control ε))
   (ret : Readable.PullReturn ε),
   s.control = .awaitTransform request completion depth :: tail →
   s.writable.control.length ≠ depth → Transform.returnTransform s ret = none)

#check (@Transform.returnTransform_readable_frame :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (ret : Readable.PullReturn ε),
   s.readable.frames ≠ [] → Transform.returnTransform s ret = none)

#check (@Transform.enqueue_guard :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : β), Readable.canCloseOrEnqueue s.readable
    = false →
   Transform.enqueue s chunk =
     (let reason : Boundary.Exception ε := .typeError s.writable.nextError
      let t := Transform.withWritable s { s.writable with nextError := s.writable.nextError + 1 }
      some { t with
        nextCall := s.nextCall + 1,
        trace := t.trace ++ [.enqueueReturned s.nextCall (.error reason)] }))

#check (@Transform.enqueue_same_pressure :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : β) (u : Transform.State α β ε),
   Readable.canCloseOrEnqueue s.readable = true →
   (∃ a, s.readable.algorithms = some a ∧ a.size = .one) →
   Transform.servicePull (Transform.withReadable s (Readable.beginEnqueue s.readable chunk)) =
     some u →
   (!Readable.shouldCallPull u.readable) = u.backpressure →
   Transform.enqueue s chunk =
     some { u with
       nextCall := s.nextCall + 1,
       trace := u.trace ++ [.enqueueReturned s.nextCall (.ok ())] })

#check (@Transform.enqueue_raises_pressure :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : β) (u v : Transform.State α β ε),
   Readable.canCloseOrEnqueue s.readable = true →
   (∃ a, s.readable.algorithms = some a ∧ a.size = .one) →
   Transform.servicePull (Transform.withReadable s (Readable.beginEnqueue s.readable chunk)) =
     some u →
   Readable.shouldCallPull u.readable = false → u.backpressure = false →
   Transform.setBackpressure u true = some v →
   Transform.enqueue s chunk =
     some { v with
       nextCall := s.nextCall + 1,
       trace := v.trace ++ [.enqueueReturned s.nextCall (.ok ())] })

#check (@Transform.enqueue_requires_count :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : β),
   Readable.canCloseOrEnqueue s.readable = true →
   (∀ a, s.readable.algorithms = some a → a.size ≠ .one) →
   Transform.enqueue s chunk = none)

#check (@Transform.runJob_reaction :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (k : Transform.Reaction α) (a :
    Readable.PullAnswer ε),
   Transform.runJob s (.reaction k a) = Transform.react s k a)

#check (@Transform.runJob_readable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (promise : Nat),
   Transform.runJob s (.readable promise) =
     (do
       let r ← Readable.runPullJob s.readable
       Transform.servicePull (Transform.withReadable s r)))

#check (@Transform.runJob_writable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (job : Writable.SinkJob α ε)
   (tail : List (Writable.SinkJob α ε)),
   s.writable.control = [] → s.writable.jobs = job :: tail →
   job.kind = .write → job.request = request →
   Transform.runJob s (.writable request) =
     (Writable.tick s.writable).map (Transform.withWritable s))

#check (@Transform.runJob_writable_requires_matching :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat),
   (s.writable.control ≠ [] ∨
     ∀ job tail, s.writable.jobs = job :: tail → job.kind ≠ .write ∨ job.request ≠ request) →
   Transform.runJob s (.writable request) = none)

#check (@Transform.tick_errorWritable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (e : Boundary.Exception ε) (tail : List
    (Transform.Control ε)),
   s.control = .errorWritable e :: tail →
   Transform.tick s =
     (let t := Transform.withWritable s
        { s.writable with control := .errorIfNeeded e :: s.writable.control }
      some { t with control := .waitWritable s.writable.control.length :: tail }))

#check (@Transform.tick_waitWritable_done :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (depth : Nat) (tail : List (Transform.Control ε)),
   s.control = .waitWritable depth :: tail → s.writable.control.length = depth →
   Transform.tick s = some { s with control := tail })

#check (@Transform.tick_waitWritable_step :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (depth : Nat) (tail : List (Transform.Control ε)),
   s.control = .waitWritable depth :: tail → depth < s.writable.control.length →
   Transform.tick s = (Writable.tick s.writable).map (Transform.withWritable s))

#check (@Transform.tick_unblock :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (tail : List (Transform.Control ε)), s.control =
    .unblock :: tail →
   Transform.tick s = Transform.unblockWrite { s with control := tail })

#check (@Transform.tick_settle :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (result : Nat) (a : Readable.PullAnswer ε)
   (tail : List (Transform.Control ε)), s.control = .settle result a :: tail →
   Transform.tick s = Transform.settle { s with control := tail } result a)

#check (@Transform.tick_await_nested_writable :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request depth : Nat)
   (completion : Transform.Completion) (tail : List (Transform.Control ε)),
   s.control = .awaitTransform request completion depth :: tail →
   depth < s.writable.control.length →
   Transform.tick s = (Writable.tick s.writable).map (Transform.withWritable s))

#check (@Transform.tick_await_suspended :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request depth : Nat)
   (completion : Transform.Completion) (tail : List (Transform.Control ε)),
   s.control = .awaitTransform request completion depth :: tail →
   s.writable.control.length ≤ depth → Transform.tick s = none)

#check (@Transform.tick_writable_control :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   s.control = [] → s.writable.control ≠ [] →
   Writable.externalFrontier s.writable = false →
   Transform.tick s = (Writable.tick s.writable).map (Transform.withWritable s))

#check (@Transform.tick_native_write :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)), s.control = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   Transform.tick s = Transform.sinkWrite s)

#check (@Transform.tick_job_fifo :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (job : Transform.Job α ε) (tail : List
    (Transform.Job α ε)),
   s.control = [] → s.writable.control = [] → s.readable.frames = [] →
   s.jobs = job :: tail →
   Transform.tick s = Transform.runJob { s with jobs := tail } job)

#check (@Transform.tick_no_job :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   s.control = [] → s.writable.control = [] → s.readable.frames = [] → s.jobs = [] →
   Transform.tick s = none)

#check (@Transform.tick_native_pull :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   s.control = [] → s.writable.control = [] → s.readable.frames ≠ [] →
   Transform.tick s = Transform.servicePull s)

#check (@Transform.externalFrontier_native_write :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.writable.control = .awaitSink (.write request chunk) :: tail →
   Transform.externalFrontier s = false)

#check (@Transform.externalFrontier_administrative :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   (∀ request completion depth tail,
     s.control ≠ .awaitTransform request completion depth :: tail) →
   s.control ≠ [] → Transform.externalFrontier s = false)

#check (@Transform.decide_nonfrontier :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (d : Transform.Decision α β ε),
   Transform.externalFrontier s = false → Transform.decide s d = none)

#check (@Transform.step_iff :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (d : Option (Transform.Decision α β ε)) (t :
    Transform.State α β ε),
   Transform.Step s d t ↔
     (match d with | none => Transform.tick s | some a => Transform.decide s a) = some t)

#check (@Transform.reaches_nil :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.Reaches s [] s)

#check (@Transform.reaches_cons :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (d : Option (Transform.Decision α β ε))
   (middle last : Transform.State α β ε) (tape : List (Option (Transform.Decision α β ε))),
   Transform.Step s d middle → Transform.Reaches middle tape last →
   Transform.Reaches s (d :: tape) last)

#check (@Transform.reaches_append :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (middle last : Transform.State α β ε)
   (before after : List (Option (Transform.Decision α β ε))),
   Transform.Reaches s before middle → Transform.Reaches middle after last →
   Transform.Reaches s (before ++ after) last)

#check (@Transform.tick_waitWritable_undershoot :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (depth : Nat) (tail : List (Transform.Control ε)),
   s.control = .waitWritable depth :: tail → s.writable.control.length < depth →
   Transform.tick s = none)

#check (@Transform.initial_eq :
  ∀ {α β ε : Type} (readHwm writeHwm : Data.DyadicSize)
   (inputSize : Data.SizeAlgorithm Nat) (ports : Transform.Ports)
   (algorithms : Transform.Algorithms) (promiseSeed errorSeed : Nat),
   Transform.initial (α := α) (β := β) (ε := ε)
     readHwm writeHwm inputSize ports algorithms promiseSeed errorSeed =
     (let r := Readable.callPullIfNeeded (Readable.initial
        { size := .one, pull := ports.pull, cancel := ports.readCancel } readHwm)
      let w := Writable.initial writeHwm
        { size := some inputSize, write := some (.foreign ports.write),
          close := some (.foreign ports.close), abort := some (.foreign ports.abort) }
        promiseSeed errorSeed
      let (w', bp) := Writable.freshPromise w .pending
      { readable := r, writable := w', ports := ports, backpressure := true,
        backpressurePromise := bp, internalPromises := [bp], algorithms := some algorithms,
        subscriptions := [], jobs := [], control := [], pendingTransforms := [],
        nextCall := 0, trace := r.trace.map Transform.Event.readable }))

#check (@Transform.externalFrontier_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.externalFrontier s =
     (if s.readable.frames.isEmpty then
        match s.control with
        | [] =>
            match s.writable.control with
            | .awaitSink _ :: _ => false
            | _ => Writable.externalFrontier s.writable
        | .awaitTransform _ _ depth :: _ =>
            decide (depth ≤ s.writable.control.length) && Writable.externalFrontier s.writable
        | _ => false
      else false))

#check (@Transform.decide_read :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .read = Transform.read s)

#check (@Transform.decide_enqueue :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : β), Transform.externalFrontier s = true →
   Transform.decide s (.enqueue chunk) = Transform.enqueue s chunk)

#check (@Transform.decide_error :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (reason : Boundary.Exception ε),
    Transform.externalFrontier s = true →
   Transform.decide s (.error reason) = some (Transform.error s reason))

#check (@Transform.decide_terminate :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .terminate = some (Transform.terminate s))

#check (@Transform.decide_write :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (chunk : α), Transform.externalFrontier s = true →
   Transform.decide s (.write chunk) =
     (Writable.decide s.writable (.write chunk)).map (Transform.withWritable s))

#check (@Transform.decide_returnSize :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (a : Data.SizeAnswer Data.DyadicSize
    (Boundary.Exception ε)),
   Transform.externalFrontier s = true →
   Transform.decide s (.returnSize a) =
     (Writable.decide s.writable (.returnSize a)).map (Transform.withWritable s))

#check (@Transform.decide_ready :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .ready =
     (Writable.decide s.writable .queryReady).map (Transform.withWritable s))

#check (@Transform.decide_closed :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .closed =
     (Writable.decide s.writable .queryClosed).map (Transform.withWritable s))

#check (@Transform.decide_writerDesiredSize :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .writerDesiredSize =
     (Writable.decide s.writable .queryDesiredSize).map (Transform.withWritable s))

#check (@Transform.decide_desiredSize :
  ∀ {α β ε : Type} (s : Transform.State α β ε), Transform.externalFrontier s = true →
   Transform.decide s .desiredSize =
     some (Transform.withReadable s (Readable.queryDesiredSize s.readable)))

#check (@Transform.decide_returnTransform :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (ret : Readable.PullReturn ε),
   Transform.externalFrontier s = true →
   Transform.decide s (.returnTransform ret) = Transform.returnTransform s ret)

#check (@Transform.decide_answerTransform :
  ∀ {α β ε : Type} (s : Transform.State α β ε) (request : Nat) (a : Readable.PullAnswer ε),
   Transform.externalFrontier s = true →
   Transform.decide s (.answerTransform request a) = Transform.answerTransform s request a)

#check (@Transform.coupled_write_read_enqueue :
  ∀ {α β ε : Type} (input : α) (output : β) (seed : Nat),
   let start : Transform.State α β ε :=
     Transform.initial Data.DyadicSize.sizes.zero Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Transform.Decision.write input, .read, .enqueue output,
         .returnTransform (.settled .fulfilled)] ∧
     Transform.Reaches start tape last ∧
     Readable.observeM1 last.readable = ([output], .readable) ∧
     last.writable.status = .writable ∧
     Writable.lookupPromise last.writable (seed + 3) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.fulfilled ()) ∧
     last.backpressure = true ∧
     last.backpressurePromise = seed + 7 ∧
     Transform.lookupPromise last (seed + 2) = some (.fulfilled ()) ∧
     Transform.lookupPromise last (seed + 6) = some (.fulfilled ()) ∧
     Transform.lookupPromise last (seed + 7) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 3, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [])

#check (@Transform.coupled_error_during_transform :
  ∀ {α β ε : Type} (input : α) (reason : ε) (seed : Nat),
   let start : Transform.State α β ε :=
     Transform.initial Data.DyadicSize.sizes.zero Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Transform.Decision.write input, .read, .error (.foreign reason),
         .returnTransform (.settled .fulfilled)] ∧
     Transform.Reaches start tape last ∧
     Readable.observeM1 last.readable = ([], .errored (.foreign reason)) ∧
     last.writable.status = .errored (.foreign reason) ∧
     Writable.lookupPromise last.writable (seed + 3) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.rejected (.foreign reason)) ∧
     Writable.lookupPromise last.writable (seed + 1) = some (.rejected (.foreign reason)) ∧
     last.algorithms = none ∧ last.backpressure = false ∧
     last.backpressurePromise = seed + 6 ∧
     Transform.lookupPromise last (seed + 6) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 3, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [])

#check (@Transform.observeOutput_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.observeOutput s =
     ⟨(Readable.observeM1 s.readable).1, s.readable.status, s.writable.status⟩)

#check (@Transform.observeOrdered_eq :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   Transform.observeOrdered s =
     ⟨Transform.observeOutput s, s.trace.filterMap (Transform.visibleEvent s.internalPromises)⟩)

#check (@Transform.observeOrdered_output :
  ∀ {α β ε : Type} (s : Transform.State α β ε),
   (Transform.observeOrdered s).output = Transform.observeOutput s)

#check (@Transform.visible_readable_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (x : Readable.Settlement β ε),
   Transform.visibleEvent ids (Transform.Event.readable (α := α) (.settled x)) =
     some (.readableSettlement x))

#check (@Transform.visible_readable_query :
  ∀ {α β ε : Type} (ids : List Nat) (x : Option Readable.Size),
   Transform.visibleEvent ids
     (Transform.Event.readable (α := α) (β := β) (ε := ε) (.desiredSizeRead x)) =
     some (.readableDesiredSize x))

#check (@Transform.visible_internal_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (id : Nat)
   (a : Except (Boundary.Exception ε) Unit), id ∈ ids →
   Transform.visibleEvent ids (Transform.Event.writable (α := α) (β := β) (.settled id a)) = none)

#check (@Transform.visible_external_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (id : Nat)
   (a : Except (Boundary.Exception ε) Unit), id ∉ ids →
   Transform.visibleEvent ids (Transform.Event.writable (α := α) (β := β) (.settled id a)) =
     some (.writable (.settled id a)))

#check (@Transform.visible_writer_returned :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (ε := ε) (.returned call promise)) =
     some (.writable (.returned call promise)))

#check (@Transform.visible_ready_query :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (ε := ε) (.readyRead call promise)) =
     some (.writable (.readyRead call promise)))

#check (@Transform.visible_closed_query :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (ε := ε) (.closedRead call promise)) =
     some (.writable (.closedRead call promise)))

#check (@Transform.visible_writer_size_query :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (value : Option Writable.Size),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (ε := ε) (.desiredSizeRead call value)) =
     some (.writable (.desiredSizeRead call value)))

#check (@Transform.visible_writer_controller_return :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (ε := ε) (.controllerReturned call)) =
     some (.writable (.controllerReturned call)))

#check (@Transform.visible_enqueue_return :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (a : Except (Boundary.Exception ε) Unit),
   Transform.visibleEvent ids (Transform.Event.enqueueReturned (α := α) (β := β) call a) =
     some (.enqueueReturned call a))

#check (@Transform.visible_nested_readable_enqueue :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (a : Except (Boundary.Exception ε) Unit),
   Transform.visibleEvent ids
     (Transform.Event.readable (α := α) (β := β) (.enqueueReturned call a)) = none)

#check (@Transform.visible_transform_call :
  ∀ {α β ε : Type} (ids : List Nat) (request algorithm : Nat) (chunk : α),
   Transform.visibleEvent ids
     (Transform.Event.transformCalled (β := β) (ε := ε) request algorithm chunk) = none)

#check (@Transform.visible_transform_return :
  ∀ {α β ε : Type} (ids : List Nat) (request result : Nat),
   Transform.visibleEvent ids
     (Transform.Event.transformReturned (α := α) (β := β) (ε := ε) request result) = none)

#check (@Transform.visible_readable_pull_call :
  ∀ {α β ε : Type} (ids : List Nat) (algorithm : Nat),
   Transform.visibleEvent ids
     (Transform.Event.readable (α := α) (β := β) (ε := ε) (.pullCalled algorithm)) = none)

#check (@Transform.visible_readable_size_call :
  ∀ {α β ε : Type} (ids : List Nat) (call algorithm : Nat) (chunk : β),
   Transform.visibleEvent ids
     (Transform.Event.readable (α := α) (ε := ε) (.sizeCalled call algorithm chunk)) = none)

#check (@Transform.visible_writable_sink_call :
  ∀ {α β ε : Type} (ids : List Nat) (algorithm : Nat)
   (op : Writable.SinkOperation α ε),
   Transform.visibleEvent ids
     (Transform.Event.writable (β := β) (.sinkCalled algorithm op)) = none)

#check (@Transform.visible_writable_size_call :
  ∀ {α β ε : Type} (ids : List Nat) (call algorithm : Nat) (chunk : α),
   Transform.visibleEvent ids
     (Transform.Event.writable (β := β) (ε := ε) (.sizeCalled call algorithm chunk)) = none)

#check (@Transform.visible_writable_signal_call :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (e : Boundary.Exception ε),
   Transform.visibleEvent ids
     (Transform.Event.writable (α := α) (β := β) (.signalCalled call e)) = none)

#check (@Transform.coupled_positive_readable_capacity :
  ∀ {α β ε : Type} (input : α) (output : β) (seed : Nat),
   let start : Transform.State α β ε :=
     Transform.initial Data.DyadicSize.sizes.one Data.DyadicSize.sizes.one .one
       ⟨1, 2, 3, 4, 5⟩ ⟨20, 21, 22⟩ seed 0
   ∃ tape last,
     tape.filterMap id =
       [Transform.Decision.write input, .enqueue output, .returnTransform (.settled .fulfilled)]
         ∧
     Transform.Reaches start tape last ∧
     last.readable.queue.entries.map Data.QueueEntry.value = [output] ∧
     Readable.observeM1 last.readable = ([], .readable) ∧
     last.writable.status = .writable ∧
     Writable.lookupPromise last.writable (seed + 4) = some (.fulfilled ()) ∧
     Writable.lookupPromise last.writable (seed + 5) = some (.fulfilled ()) ∧
     last.backpressure = true ∧ last.backpressurePromise = seed + 6 ∧
     Transform.lookupPromise last (seed + 2) = some (.fulfilled ()) ∧
     Transform.lookupPromise last (seed + 3) = some (.fulfilled ()) ∧
     Transform.lookupPromise last (seed + 6) = some .pending ∧
     (last.trace.filterMap fun event ↦ match event with
       | .transformCalled request algorithm chunk => some (request, algorithm, chunk)
       | _ => none) = [(seed + 4, 20, input)] ∧
     last.control = [] ∧ last.jobs = [] ∧ last.writable.control = [] ∧
     last.writable.jobs = [] ∧ last.readable.jobs = [] ∧ last.pendingTransforms = [])
