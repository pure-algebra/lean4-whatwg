import Whatwg.Streams.Transform.Step
import Whatwg.Streams.Transform.Observation
-- Q4 (`test/contracts/configuration-ordering.contract.md` §5.2): the row 15
-- table bridge is stated over `Whatwg.Streams.Writable.settle_bridge`, which
-- slice Q3 landed in `Whatwg/Streams/Writable/Laws.lean`. Additive; the module
-- declares no instance and no global `simp` lemma, and `Piping/Laws.lean`
-- already imports it, so no dependency edge is new to `Whatwg/Streams/**`.
import Whatwg.Streams.Writable.Laws

/-!
# Frozen transform stage and view laws

TRANSFORM-PG-BACKPRESSURE owns the exact statements. These are local component
and count-profile equations; global job order, reachability and DB-04 remain open.
-/

namespace Whatwg.Streams.Transform

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem withReadable_eq :
  ∀ {α β ε : Type} (s : State α β ε) (r : Readable.State β ε),
   withReadable s r = { s with
     readable := r,
     trace := s.trace ++ (r.trace.drop s.readable.trace.length).map Event.readable } := by
  intros
  first | rfl | (simp_all [withReadable] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem withWritable_eq :
  ∀ {α β ε : Type} (s : State α β ε) (w : Writable.State α ε),
   withWritable s w = { s with
     writable := w,
     trace := s.trace ++ (w.trace.drop s.writable.trace.length).map Event.writable } := by
  intros
  first | rfl | (simp_all [withWritable] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem lookupPromise_eq :
  ∀ {α β ε : Type} (s : State α β ε) (id : Nat),
   lookupPromise s id =
     (Writable.lookupPromise s.writable id).map Writable.unitPromiseToShared := by
  intros
  first | rfl | (simp_all [lookupPromise] <;> rfl)

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem freshInternal_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   freshInternal s =
     (let (w, id) := Writable.freshPromise s.writable .pending
      let t := withWritable s w
      ({ t with internalPromises := t.internalPromises ++ [id] }, id)) := by
  intros
  first
  | rfl
  | (simp_all [freshInternal, withWritable, lookupPromise, Writable.freshPromise,
      Writable.lookupPromise, List.find?_append] <;> rfl)

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem freshInternal_old :
  ∀ {α β ε : Type} (s : State α β ε) (id : Nat), id ≠ s.writable.nextPromise →
   lookupPromise (freshInternal s).1 id = lookupPromise s id := by
  intro α β ε s id h
  simp [freshInternal, withWritable, lookupPromise, Writable.freshPromise,
    Writable.lookupPromise, List.find?_append, Ne.symm h]

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem freshInternal_new :
  ∀ {α β ε : Type} (s : State α β ε),
   Writable.lookupPromise s.writable s.writable.nextPromise = none →
   lookupPromise (freshInternal s).1 (freshInternal s).2 =
     some .pending := by
  intro α β ε s h
  unfold Writable.lookupPromise at h
  cases hf : s.writable.promises.find? (fun p => p.1 == s.writable.nextPromise) with
  | none =>
      simp [freshInternal, withWritable, lookupPromise, Writable.freshPromise,
        Writable.lookupPromise, List.find?_append, hf, Writable.unitPromiseToShared]
  | some p => simp [hf] at h

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem freshInternal_identity :
  ∀ {α β ε : Type} (s : State α β ε),
   (freshInternal s).2 = s.writable.nextPromise ∧
   (freshInternal s).1.writable.readyPromise = s.writable.readyPromise ∧
   (freshInternal s).1.writable.closedPromise = s.writable.closedPromise ∧
   (freshInternal s).1.writable.inFlightWrite = s.writable.inFlightWrite := by
  intros
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscriptionPromise_readable :
  ∀ {α : Type} (id : Nat),
   subscriptionPromise (Subscription.readable (α := α) id) = id := by
  intros
  first | rfl | (simp_all [subscriptionPromise] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscriptionPromise_writable :
  ∀ {α : Type} (id request : Nat),
   subscriptionPromise (Subscription.writable (α := α) id request) = id := by
  intros
  first | rfl | (simp_all [subscriptionPromise] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscriptionPromise_reaction :
  ∀ {α : Type} (id : Nat) (k : Reaction α),
   subscriptionPromise (.reaction id k) = id := by
  intros
  first | rfl | (simp_all [subscriptionPromise] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem notify_readable :
  ∀ {α β ε : Type} (s : State α β ε) (promise : Nat) (a : Readable.PullAnswer ε) (r :
    Readable.State β ε),
   Readable.acceptPullAnswer s.readable a = some r →
   notify s (.readable promise) a =
     some { withReadable s r with jobs := s.jobs ++ [.readable promise] } := by
  intros
  first | rfl | (simp_all [notify] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem notify_writable :
  ∀ {α β ε : Type} (s : State α β ε) (promise request : Nat) (a : Readable.PullAnswer
    ε)
   (w : Writable.State α ε),
   Writable.acceptAnswer s.writable .write request (Writable.sinkAnswerFromShared a) = some w →
   notify s (.writable promise request) a =
     some { withWritable s w with jobs := s.jobs ++ [.writable request] } := by
  intros
  first | rfl | (simp_all [notify] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem notify_reaction :
  ∀ {α β ε : Type} (s : State α β ε) (promise : Nat) (k : Reaction α) (a :
    Readable.PullAnswer ε),
   notify s (.reaction promise k) a = some { s with jobs := s.jobs ++ [.reaction k a] } := by
  intros
  first | rfl | (simp_all [notify] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscribe_pending :
  ∀ {α β ε : Type} (s : State α β ε) (sub : Subscription α),
   lookupPromise s (subscriptionPromise sub) = some .pending →
   subscribe s sub = some { s with subscriptions := s.subscriptions ++ [sub] } := by
  intros
  first | rfl | (simp_all [subscribe] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscribe_fulfilled :
  ∀ {α β ε : Type} (s : State α β ε) (sub : Subscription α),
   lookupPromise s (subscriptionPromise sub) = some (.fulfilled ()) →
   subscribe s sub = notify s sub .fulfilled := by
  intros
  first | rfl | (simp_all [subscribe] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscribe_rejected :
  ∀ {α β ε : Type} (s : State α β ε) (sub : Subscription α) (e :
    Boundary.Exception ε),
   lookupPromise s (subscriptionPromise sub) = some (.rejected e) →
   subscribe s sub = notify s sub (.rejected e) := by
  intros
  first | rfl | (simp_all [subscribe] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem subscribe_missing :
  ∀ {α β ε : Type} (s : State α β ε) (sub : Subscription α),
   lookupPromise s (subscriptionPromise sub) = none →
   subscribe s sub = none := by
  intros
  first | rfl | (simp_all [subscribe] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem settle_other :
  ∀ {α β ε : Type} (s : State α β ε) (id : Nat) (a : Readable.PullAnswer ε),
   lookupPromise s id ≠ some .pending →
   settle s id a = some s := by
  intros
  first | rfl | (simp_all [settle] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem settle_pending :
  ∀ {α β ε : Type} (s : State α β ε) (id : Nat) (a : Readable.PullAnswer ε),
   lookupPromise s id = some .pending →
   settle s id a =
     (let outcome : Except (Boundary.Exception ε) Unit :=
        match a with | .fulfilled => .ok () | .rejected e => .error e
      let t := withWritable s (Writable.settle s.writable id outcome)
      let resting := { t with
        subscriptions := s.subscriptions.filter (fun sub ↦ subscriptionPromise sub !=
          id) }
      (s.subscriptions.filter (fun sub ↦ subscriptionPromise sub == id)).foldlM
        (fun u sub ↦ notify u sub a) resting) := by
  intros
  first | rfl | (simp_all [settle] <;> rfl)

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem setBackpressure_same :
  ∀ {α β ε : Type} (s : State α β ε) (b : Bool), s.backpressure = b →
   setBackpressure s b = some s := by
  intros
  first | rfl | (simp_all [setBackpressure] <;> rfl)

/-- `op.transform-stream-set-backpressure`: the frozen local equation. -/
theorem setBackpressure_change :
  ∀ {α β ε : Type} (s : State α β ε) (b : Bool), s.backpressure ≠ b →
   setBackpressure s b =
     (do
       let t ← settle s s.backpressurePromise .fulfilled
       let (u, fresh) := freshInternal t
       pure { u with backpressure := b, backpressurePromise := fresh }) := by
  intros
  first | rfl | (simp_all [setBackpressure] <;> rfl)

/-- `op.transform-stream-unblock-write`: the frozen local equation. -/
theorem unblockWrite_true :
  ∀ {α β ε : Type} (s : State α β ε), s.backpressure = true →
   unblockWrite s = setBackpressure s false := by
  intros
  first | rfl | (simp_all [unblockWrite] <;> rfl)

/-- `op.transform-stream-unblock-write`: the frozen local equation. -/
theorem unblockWrite_false :
  ∀ {α β ε : Type} (s : State α β ε), s.backpressure = false →
   unblockWrite s = some s := by
  intros
  first | rfl | (simp_all [unblockWrite] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem sourcePull_realizes :
  ∀ {α β ε : Type} (s : State α β ε) (k : Readable.PullContinuation β)
   (rest : List (Readable.Frame β)) (t u : State α β ε) (r : Readable.State β ε),
   s.readable.frames = .pull k :: rest → s.backpressure = true →
   setBackpressure s false = some t →
   Readable.returnPull t.readable .pending = some r →
   subscribe (withReadable t r) (.readable t.backpressurePromise) = some u →
   sourcePull s = some (u, t.backpressurePromise) := by
  intros
  first | rfl | (simp_all [sourcePull] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem sourcePull_requires_pressure :
  ∀ {α β ε : Type} (s : State α β ε), s.backpressure = false →
   sourcePull s = none := by
  intro α β ε s h
  cases hf : s.readable.frames with
  | nil => simp [sourcePull, hf]
  | cons frame tail => cases frame <;> simp_all [sourcePull]

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem sourcePull_requires_frame :
  ∀ {α β ε : Type} (s : State α β ε),
   (∀ k rest, s.readable.frames ≠ .pull k :: rest) → sourcePull s = none := by
  intros
  first | rfl | (simp_all [sourcePull] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem servicePull_empty :
  ∀ {α β ε : Type} (s : State α β ε), s.readable.frames = [] → servicePull s
    = some s := by
  intros
  first | rfl | (simp_all [servicePull] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem servicePull_pull :
  ∀ {α β ε : Type} (s : State α β ε) (k : Readable.PullContinuation β)
   (rest : List (Readable.Frame β)), s.readable.frames = .pull k :: rest →
   servicePull s = (sourcePull s).map Prod.fst := by
  intros
  first | rfl | (simp_all [servicePull] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem servicePull_size :
  ∀ {α β ε : Type} (s : State α β ε) (call : Nat) (chunk : β) (rest : List
    (Readable.Frame β)),
   s.readable.frames = .size call chunk :: rest → servicePull s = none := by
  intros
  first | rfl | (simp_all [servicePull] <;> rfl)

/-- `op.transform-stream-default-source-pull`: the frozen local equation. -/
theorem read_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   read s = servicePull (withReadable s (Readable.read s.readable)) := by
  intros
  first | rfl | (simp_all [read] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem performTransform_present :
  ∀ {α β ε : Type} (s : State α β ε) (a : Algorithms) (request : Nat) (chunk
    : α)
   (completion : Completion), s.algorithms = some a →
   performTransform s request chunk completion =
     some { s with
       control := .awaitTransform request completion s.writable.control.length :: s.control,
       trace := s.trace ++ [.transformCalled request a.transform chunk] } := by
  intros
  first | rfl | (simp_all [performTransform] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem performTransform_missing :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
   (completion : Completion), s.algorithms = none →
   performTransform s request chunk completion = none := by
  intros
  first | rfl | (simp_all [performTransform] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem react_write_writable :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (chunk : α),
   s.writable.status = .writable →
   react s (.write request chunk result) .fulfilled =
     performTransform s request chunk (.adopt result) := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem react_write_erroring :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   s.writable.status = .erroring e →
   react s (.write request chunk result) .fulfilled =
     settle s result (.rejected e) := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem react_write_closed :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (chunk : α),
   s.writable.status = .closed →
   react s (.write request chunk result) .fulfilled = none := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem react_write_errored :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   s.writable.status = .errored e →
   react s (.write request chunk result) .fulfilled = none := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem react_write_rejected :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (chunk : α) (e :
    Boundary.Exception ε),
   react s (.write request chunk result) (.rejected e) =
     settle s result (.rejected e) := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem react_transform_fulfilled :
  ∀ {α β ε : Type} (s : State α β ε) (result : Nat),
   react s (.transform result) .fulfilled = settle s result .fulfilled := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem react_transform_rejected :
  ∀ {α β ε : Type} (s : State α β ε) (result : Nat) (e : Boundary.Exception ε),
   react s (.transform result) (.rejected e) =
     (let t := withReadable s (Readable.error s.readable e)
      some { t with
        algorithms := none,
        control := .errorWritable e :: .unblock :: .settle result (.rejected e) ::
          s.control }) := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem react_adopt :
  ∀ {α β ε : Type} (s : State α β ε) (result : Nat) (a : Readable.PullAnswer ε),
   react s (.adopt result) a = settle s result a := by
  intros
  first | rfl | (simp_all [react] <;> rfl)

/-- `op.transform-stream-error`: the frozen local equation. -/
theorem error_eq :
  ∀ {α β ε : Type} (s : State α β ε) (e : Boundary.Exception ε),
   error s e =
     (let t := withReadable s (Readable.error s.readable e)
      { t with algorithms := none, control := .errorWritable e :: .unblock :: s.control }) := by
  intros
  first | rfl | (simp_all [error] <;> rfl)

/-- `op.transform-stream-default-controller-terminate`: the frozen local equation. -/
theorem terminate_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   terminate s =
     (let reason : Boundary.Exception ε := .typeError s.writable.nextError
      let t := withReadable s (Readable.close s.readable)
      let u := withWritable t { t.writable with nextError := t.writable.nextError + 1 }
      { u with
        algorithms := none,
        control := .errorWritable reason :: .unblock :: s.control }) := by
  intros
  first | rfl | (simp_all [terminate] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem sinkWrite_blocked :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.readable.frames = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   s.writable.status = .writable →
   s.writable.algorithms.write = some (.foreign s.ports.write) →
   Writable.operationPhase s.writable .write request = some .invoking →
   s.backpressure = true →
   sinkWrite s =
     (do
       let (t, result) := freshInternal s
       let w ← Writable.decide t.writable (.returnSink .pending)
       let u ← subscribe (withWritable t w) (.writable result request)
       subscribe u (.reaction s.backpressurePromise (.write request chunk result))) := by
  intros
  first | rfl | (simp_all [sinkWrite] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem sinkWrite_direct :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.readable.frames = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   s.writable.status = .writable →
   s.writable.algorithms.write = some (.foreign s.ports.write) →
   Writable.operationPhase s.writable .write request = some .invoking →
   s.backpressure = false →
   sinkWrite s = performTransform s request chunk .direct := by
  intros
  first | rfl | (simp_all [sinkWrite] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem sinkWrite_inside_transform :
  ∀ {α β ε : Type} (s : State α β ε), s.control ≠ [] → sinkWrite s = none := by
  intros
  first | rfl | (simp_all [sinkWrite] <;> rfl)

/-- `op.transform-stream-default-sink-write-algorithm`: the frozen local equation. -/
theorem sinkWrite_requires_frame :
  ∀ {α β ε : Type} (s : State α β ε),
   (∀ request chunk tail, s.writable.control ≠ .awaitSink (.write request chunk) :: tail) →
   sinkWrite s = none := by
  intros
  first | rfl | (simp_all [sinkWrite] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem answerTransform_waiting :
  ∀ {α β ε : Type} (s : State α β ε) (request result : Nat) (a : Readable.PullAnswer
    ε),
   s.pendingTransforms.find? (fun p ↦ p.1 == request) = some (request, result) →
   answerTransform s request a =
     some { s with
       pendingTransforms := s.pendingTransforms.filter (fun p ↦ p.1 != request),
       jobs := s.jobs ++ [.reaction (.transform result) a] } := by
  intros
  first | rfl | (simp_all [answerTransform] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem answerTransform_unmatched :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (a : Readable.PullAnswer ε),
   s.pendingTransforms.find? (fun p ↦ p.1 == request) = none →
   answerTransform s request a = none := by
  intro α β ε s request a h
  simp only [answerTransform, h]

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem returnTransform_frame :
  ∀ {α β ε : Type} (s : State α β ε) (request depth : Nat) (completion :
    Completion)
   (tail : List (Control ε)) (ret : Readable.PullReturn ε),
   s.control = .awaitTransform request completion depth :: tail →
   s.readable.frames = [] → s.writable.control.length = depth →
   returnTransform s ret =
     (do
       let (t, result) := freshInternal { s with control := tail }
       let u : State α β ε := match ret with
         | .pending => { t with pendingTransforms := t.pendingTransforms ++ [(request, result)] }
         | .settled a => { t with jobs := t.jobs ++ [.reaction (.transform result) a] }
       let v := { u with trace := u.trace ++ [.transformReturned request result] }
       match completion with
       | .direct =>
           match v.writable.control with
           | .awaitSink (.write request' _) :: _ =>
               if request' == request then
                 let w ← Writable.decide v.writable (.returnSink .pending)
                 subscribe (withWritable v w) (.writable result request)
               else none
           | _ => none
       | .adopt target => subscribe v (.reaction result (.adopt target))) := by
  intros
  first | rfl | (simp_all [returnTransform] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem returnTransform_unmatched :
  ∀ {α β ε : Type} (s : State α β ε) (ret : Readable.PullReturn ε),
   (∀ request completion depth tail,
     s.control ≠ .awaitTransform request completion depth :: tail) →
   returnTransform s ret = none := by
  intros
  first | rfl | (simp_all [returnTransform] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem returnTransform_nested_writable :
  ∀ {α β ε : Type} (s : State α β ε) (request depth : Nat)
   (completion : Completion) (tail : List (Control ε))
   (ret : Readable.PullReturn ε),
   s.control = .awaitTransform request completion depth :: tail →
   s.writable.control.length ≠ depth → returnTransform s ret = none := by
  intros
  first | rfl | (simp_all [returnTransform] <;> rfl)

/-- `op.transform-stream-default-controller-perform-transform`: the frozen local equation. -/
theorem returnTransform_readable_frame :
  ∀ {α β ε : Type} (s : State α β ε) (ret : Readable.PullReturn ε),
   s.readable.frames ≠ [] → returnTransform s ret = none := by
  intros
  first | rfl | (simp_all [returnTransform] <;> rfl)

/-- `op.transform-stream-default-controller-enqueue`: the frozen local equation. -/
theorem enqueue_guard :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : β), Readable.canCloseOrEnqueue s.readable
    = false →
   enqueue s chunk =
     (let reason : Boundary.Exception ε := .typeError s.writable.nextError
      let t := withWritable s { s.writable with nextError := s.writable.nextError + 1 }
      some { t with
        nextCall := s.nextCall + 1,
        trace := t.trace ++ [.enqueueReturned s.nextCall (.error reason)] }) := by
  intros
  first | rfl | (simp_all [enqueue] <;> rfl)

/-- `op.transform-stream-default-controller-enqueue`: the frozen local equation. -/
theorem enqueue_same_pressure :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : β) (u : State α β ε),
   Readable.canCloseOrEnqueue s.readable = true →
   (∃ a, s.readable.algorithms = some a ∧ a.size = .one) →
   servicePull (withReadable s (Readable.beginEnqueue s.readable chunk)) =
     some u →
   (!Readable.shouldCallPull u.readable) = u.backpressure →
   enqueue s chunk =
     some { u with
       nextCall := s.nextCall + 1,
       trace := u.trace ++ [.enqueueReturned s.nextCall (.ok ())] } := by
  intro α β ε s chunk u hg ⟨a, ha, hs⟩ hu hb
  cases hp : Readable.shouldCallPull u.readable <;> cases hb' : u.backpressure <;>
    simp_all [enqueue]

/-- `op.transform-stream-default-controller-enqueue`: the frozen local equation. -/
theorem enqueue_raises_pressure :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : β) (u v : State α β ε),
   Readable.canCloseOrEnqueue s.readable = true →
   (∃ a, s.readable.algorithms = some a ∧ a.size = .one) →
   servicePull (withReadable s (Readable.beginEnqueue s.readable chunk)) =
     some u →
   Readable.shouldCallPull u.readable = false → u.backpressure = false →
   setBackpressure u true = some v →
   enqueue s chunk =
     some { v with
       nextCall := s.nextCall + 1,
       trace := v.trace ++ [.enqueueReturned s.nextCall (.ok ())] } := by
  intro α β ε s chunk u v hg ⟨a, ha, hs⟩ hu hp hb hv
  simp [enqueue, hg, ha, hs, hu, hp, hb, hv]

/-- `op.transform-stream-default-controller-enqueue`: the frozen local equation. -/
theorem enqueue_requires_count :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : β),
   Readable.canCloseOrEnqueue s.readable = true →
   (∀ a, s.readable.algorithms = some a → a.size ≠ .one) →
   enqueue s chunk = none := by
  intro α β ε s chunk hg h
  cases ha : s.readable.algorithms with
  | none => simp [enqueue, hg, ha]
  | some a => simp [enqueue, hg, ha, h a ha]

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem runJob_reaction :
  ∀ {α β ε : Type} (s : State α β ε) (k : Reaction α) (a :
    Readable.PullAnswer ε),
   runJob s (.reaction k a) = react s k a := by
  intros
  first | rfl | (simp_all [runJob] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem runJob_readable :
  ∀ {α β ε : Type} (s : State α β ε) (promise : Nat),
   runJob s (.readable promise) =
     (do
       let r ← Readable.runPullJob s.readable
       servicePull (withReadable s r)) := by
  intros
  first | rfl | (simp_all [runJob] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem runJob_writable :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (job : Writable.SinkJob α ε)
   (tail : List (Writable.SinkJob α ε)),
   s.writable.control = [] → s.writable.jobs = job :: tail →
   job.kind = .write → job.request = request →
   runJob s (.writable request) =
     (Writable.tick s.writable).map (withWritable s) := by
  intros
  first | rfl | (simp_all [runJob] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem runJob_writable_requires_matching :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat),
   (s.writable.control ≠ [] ∨
     ∀ job tail, s.writable.jobs = job :: tail → job.kind ≠ .write ∨ job.request ≠ request) →
   runJob s (.writable request) = none := by
  intro α β ε s request h
  cases hc : s.writable.control <;> cases hj : s.writable.jobs <;> simp_all [runJob]
  intro hk hr
  exact (h.elim (fun hn => hn hk) (fun hn => hn hr)).elim

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_errorWritable :
  ∀ {α β ε : Type} (s : State α β ε) (e : Boundary.Exception ε) (tail : List
    (Control ε)),
   s.control = .errorWritable e :: tail →
   tick s =
     (let t := withWritable s
        { s.writable with control := .errorIfNeeded e :: s.writable.control }
      some { t with control := .waitWritable s.writable.control.length :: tail }) := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_waitWritable_done :
  ∀ {α β ε : Type} (s : State α β ε) (depth : Nat) (tail : List (Control ε)),
   s.control = .waitWritable depth :: tail → s.writable.control.length = depth →
   tick s = some { s with control := tail } := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_waitWritable_step :
  ∀ {α β ε : Type} (s : State α β ε) (depth : Nat) (tail : List (Control ε)),
   s.control = .waitWritable depth :: tail → depth < s.writable.control.length →
   tick s = (Writable.tick s.writable).map (withWritable s) := by
  intro α β ε s depth tail hc hlt
  have hne : s.writable.control.length ≠ depth := by omega
  simp [tick, hc, hne, hlt]

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_unblock :
  ∀ {α β ε : Type} (s : State α β ε) (tail : List (Control ε)), s.control =
    .unblock :: tail →
   tick s = unblockWrite { s with control := tail } := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_settle :
  ∀ {α β ε : Type} (s : State α β ε) (result : Nat) (a : Readable.PullAnswer ε)
   (tail : List (Control ε)), s.control = .settle result a :: tail →
   tick s = settle { s with control := tail } result a := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_await_nested_writable :
  ∀ {α β ε : Type} (s : State α β ε) (request depth : Nat)
   (completion : Completion) (tail : List (Control ε)),
   s.control = .awaitTransform request completion depth :: tail →
   depth < s.writable.control.length →
   tick s = (Writable.tick s.writable).map (withWritable s) := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_await_suspended :
  ∀ {α β ε : Type} (s : State α β ε) (request depth : Nat)
   (completion : Completion) (tail : List (Control ε)),
   s.control = .awaitTransform request completion depth :: tail →
   s.writable.control.length ≤ depth → tick s = none := by
  intro α β ε s request depth completion tail hc hle
  have hnot : ¬depth < s.writable.control.length := by omega
  simp [tick, hc, hnot]

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_writable_control :
  ∀ {α β ε : Type} (s : State α β ε),
   s.control = [] → s.writable.control ≠ [] →
   Writable.externalFrontier s.writable = false →
   tick s = (Writable.tick s.writable).map (withWritable s) := by
  intro α β ε s hc hn hf
  cases hw : s.writable.control with
  | nil => exact (hn hw).elim
  | cons head tail => cases head <;> simp_all [tick, Writable.externalFrontier]

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_native_write :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)), s.control = [] →
   s.writable.control = .awaitSink (.write request chunk) :: tail →
   tick s = sinkWrite s := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-! ## `PROMISE-PG-FIRST` bridging: the coupled job queue

`E-52`, `E-53` (generalize). The three-part guard below is the clearest statement in the
repository of `requirement.jobs.1`, and it is stated today only as a hypothesis of
`tick_job_fifo`; here it is the hypothesis of the bridge. -/

/-- `E-52`: the view is exactly the coupled-job list. Mask M1. -/
theorem jobQueue_eq {α β ε : Type} (s : State α β ε) :
    jobQueue s = Whatwg.Ecma262.Jobs.Queue.mk s.jobs := rfl

/--
`E-53` (generalize). Under the transform's own three-way spelling of
`requirement.jobs.1`, `tick` reduces to `Whatwg.Ecma262.Jobs.Queue.dequeue` followed by
the coupled component dispatch. Mask M2.
-/
theorem tick_dequeue_bridge {α β ε : Type} (s : State α β ε) :
    s.control = [] → s.writable.control = [] → s.readable.frames = [] →
      tick s =
        (Whatwg.Ecma262.Jobs.Queue.dequeue (jobQueue s)).bind
          (fun p => runJob { s with jobs := p.2.pending } p.1) := by
  intro hc hw hf
  cases hj : s.jobs <;>
    simp [tick, jobQueue, Whatwg.Ecma262.Jobs.Queue.dequeue, hc, hw, hf, hj]

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE.
Re-derived through `tick_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_cons` (the `later := []` instance of
`Queue.dequeue_fifo`), never re-proved from `tick`. Mask M2. -/
theorem tick_job_fifo :
  ∀ {α β ε : Type} (s : State α β ε) (job : Job α ε) (tail : List
    (Job α ε)),
   s.control = [] → s.writable.control = [] → s.readable.frames = [] →
   s.jobs = job :: tail →
   tick s = runJob { s with jobs := tail } job := by
  intro α β ε s job tail hc hw hf hj
  rw [tick_dequeue_bridge s hc hw hf, jobQueue_eq, hj,
    Whatwg.Ecma262.Jobs.Queue.dequeue_cons]
  rfl

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE.
Re-derived through `tick_dequeue_bridge` and the general
`Whatwg.Ecma262.Jobs.Queue.dequeue_empty`, never re-proved from `tick`. -/
theorem tick_no_job :
  ∀ {α β ε : Type} (s : State α β ε),
   s.control = [] → s.writable.control = [] → s.readable.frames = [] → s.jobs = [] →
   tick s = none := by
  intro α β ε s hc hw hf hj
  rw [tick_dequeue_bridge s hc hw hf, jobQueue_eq, hj,
    ← Whatwg.Ecma262.Jobs.Queue.empty_eq, Whatwg.Ecma262.Jobs.Queue.dequeue_empty]
  rfl

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_native_pull :
  ∀ {α β ε : Type} (s : State α β ε),
   s.control = [] → s.writable.control = [] → s.readable.frames ≠ [] →
   tick s = servicePull s := by
  intros
  first | rfl | (simp_all [tick] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem externalFrontier_native_write :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (chunk : α)
   (tail : List (Writable.Control α ε)),
   s.control = [] → s.writable.control = .awaitSink (.write request chunk) :: tail →
   externalFrontier s = false := by
  intros
  first | rfl | (simp_all [externalFrontier] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem externalFrontier_administrative :
  ∀ {α β ε : Type} (s : State α β ε),
   (∀ request completion depth tail,
     s.control ≠ .awaitTransform request completion depth :: tail) →
   s.control ≠ [] → externalFrontier s = false := by
  intros
  first | rfl | (simp_all [externalFrontier] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_nonfrontier :
  ∀ {α β ε : Type} (s : State α β ε) (d : Decision α β ε),
   externalFrontier s = false → decide s d = none := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem step_iff :
  ∀ {α β ε : Type} (s : State α β ε) (d : Option (Decision α β ε)) (t :
    State α β ε),
   Step s d t ↔
     (match d with | none => tick s | some a => decide s a) = some t := by
  intros
  first | rfl | (simp_all [Step] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem reaches_nil :
  ∀ {α β ε : Type} (s : State α β ε), Reaches s [] s := by
  intro α β ε s
  exact Reaches.nil s

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem reaches_cons :
  ∀ {α β ε : Type} (s : State α β ε) (d : Option (Decision α β ε))
   (middle last : State α β ε) (tape : List (Option (Decision α β ε))),
   Step s d middle → Reaches middle tape last →
   Reaches s (d :: tape) last := by
  intro α β ε s d middle last tape first rest
  exact Reaches.cons first rest

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem reaches_append :
  ∀ {α β ε : Type} (s : State α β ε) (middle last : State α β ε)
   (before after : List (Option (Decision α β ε))),
   Reaches s before middle → Reaches middle after last →
   Reaches s (before ++ after) last := by
  intro α β ε s middle last before after hbefore hafter
  induction hbefore with
  | nil => exact hafter
  | cons first _ ih => exact Reaches.cons first (ih hafter)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem tick_waitWritable_undershoot :
  ∀ {α β ε : Type} (s : State α β ε) (depth : Nat) (tail : List (Control ε)),
   s.control = .waitWritable depth :: tail → s.writable.control.length < depth →
   tick s = none := by
  intro α β ε s depth tail hc hlt
  have hne : s.writable.control.length ≠ depth := by omega
  have hnot : ¬depth < s.writable.control.length := by omega
  simp [tick, hc, hne, hnot]

/--
op.initialize-transform-stream and op.set-up-readable-stream-default-controller:
the frozen count-profile successful-start tail equation.
-/
theorem initial_eq :
  ∀ {α β ε : Type} (readHwm writeHwm : Data.DyadicSize)
   (inputSize : Data.SizeAlgorithm Nat) (ports : Ports)
   (algorithms : Algorithms) (promiseSeed errorSeed : Nat),
   initial (α := α) (β := β) (ε := ε)
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
        nextCall := 0, trace := r.trace.map Event.readable }) := by
  intros
  first | rfl | (simp_all [initial] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem externalFrontier_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   externalFrontier s =
     (if s.readable.frames.isEmpty then
        match s.control with
        | [] =>
            match s.writable.control with
            | .awaitSink _ :: _ => false
            | _ => Writable.externalFrontier s.writable
        | .awaitTransform _ _ depth :: _ =>
            Decidable.decide (depth ≤ s.writable.control.length) &&
              Writable.externalFrontier s.writable
        | _ => false
      else false) := by
  intros
  first | rfl | (simp_all [externalFrontier] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_read :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .read = read s := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_enqueue :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : β), externalFrontier s = true →
   decide s (.enqueue chunk) = enqueue s chunk := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_error :
  ∀ {α β ε : Type} (s : State α β ε) (reason : Boundary.Exception ε),
    externalFrontier s = true →
   decide s (.error reason) = some (error s reason) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_terminate :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .terminate = some (terminate s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_write :
  ∀ {α β ε : Type} (s : State α β ε) (chunk : α), externalFrontier s = true →
   decide s (.write chunk) =
     (Writable.decide s.writable (.write chunk)).map (withWritable s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_returnSize :
  ∀ {α β ε : Type} (s : State α β ε) (a : Data.SizeAnswer Data.DyadicSize
    (Boundary.Exception ε)),
   externalFrontier s = true →
   decide s (.returnSize a) =
     (Writable.decide s.writable (.returnSize a)).map (withWritable s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_ready :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .ready =
     (Writable.decide s.writable .queryReady).map (withWritable s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_closed :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .closed =
     (Writable.decide s.writable .queryClosed).map (withWritable s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_writerDesiredSize :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .writerDesiredSize =
     (Writable.decide s.writable .queryDesiredSize).map (withWritable s) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_desiredSize :
  ∀ {α β ε : Type} (s : State α β ε), externalFrontier s = true →
   decide s .desiredSize =
     some (withReadable s (Readable.queryDesiredSize s.readable)) := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_returnTransform :
  ∀ {α β ε : Type} (s : State α β ε) (ret : Readable.PullReturn ε),
   externalFrontier s = true →
   decide s (.returnTransform ret) = returnTransform s ret := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem decide_answerTransform :
  ∀ {α β ε : Type} (s : State α β ε) (request : Nat) (a : Readable.PullAnswer ε),
   externalFrontier s = true →
   decide s (.answerTransform request a) = answerTransform s request a := by
  intros
  first | rfl | (simp_all [decide] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem observeOutput_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   observeOutput s =
     ⟨(Readable.observeM1 s.readable).1, s.readable.status, s.writable.status⟩ := by
  intros
  first | rfl | (simp_all [observeOutput] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem observeOrdered_eq :
  ∀ {α β ε : Type} (s : State α β ε),
   observeOrdered s =
     ⟨observeOutput s, s.trace.filterMap (visibleEvent s.internalPromises)⟩ := by
  intros
  first | rfl | (simp_all [observeOrdered] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem observeOrdered_output :
  ∀ {α β ε : Type} (s : State α β ε),
   (observeOrdered s).output = observeOutput s := by
  intros
  first | rfl | (simp_all [observeOrdered] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_readable_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (x : Readable.Settlement β ε),
   visibleEvent ids (Event.readable (α := α) (.settled x)) =
     some (.readableSettlement x) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_readable_query :
  ∀ {α β ε : Type} (ids : List Nat) (x : Option Readable.Size),
   visibleEvent ids (Event.readable (α := α) (β := β) (ε := ε) (.desiredSizeRead x)) =
     some (.readableDesiredSize x) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_internal_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (id : Nat)
   (a : Except (Boundary.Exception ε) Unit), id ∈ ids →
   visibleEvent ids (Event.writable (α := α) (β := β) (.settled id a)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_external_settlement :
  ∀ {α β ε : Type} (ids : List Nat) (id : Nat)
   (a : Except (Boundary.Exception ε) Unit), id ∉ ids →
   visibleEvent ids (Event.writable (α := α) (β := β) (.settled id a)) =
     some (.writable (.settled id a)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writer_returned :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (ε := ε) (.returned call promise)) =
     some (.writable (.returned call promise)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_ready_query :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (ε := ε) (.readyRead call promise)) =
     some (.writable (.readyRead call promise)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_closed_query :
  ∀ {α β ε : Type} (ids : List Nat) (call promise : Nat),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (ε := ε) (.closedRead call promise)) =
     some (.writable (.closedRead call promise)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writer_size_query :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (value : Option Writable.Size),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (ε := ε) (.desiredSizeRead call value)) =
     some (.writable (.desiredSizeRead call value)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writer_controller_return :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (ε := ε) (.controllerReturned call)) =
     some (.writable (.controllerReturned call)) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_enqueue_return :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (a : Except (Boundary.Exception ε) Unit),
   visibleEvent ids (Event.enqueueReturned (α := α) (β := β) call a) =
     some (.enqueueReturned call a) := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_nested_readable_enqueue :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (a : Except (Boundary.Exception ε) Unit),
   visibleEvent ids
     (Event.readable (α := α) (β := β) (.enqueueReturned call a)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_transform_call :
  ∀ {α β ε : Type} (ids : List Nat) (request algorithm : Nat) (chunk : α),
   visibleEvent ids
     (Event.transformCalled (β := β) (ε := ε) request algorithm chunk) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_transform_return :
  ∀ {α β ε : Type} (ids : List Nat) (request result : Nat),
   visibleEvent ids
     (Event.transformReturned (α := α) (β := β) (ε := ε) request result) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_readable_pull_call :
  ∀ {α β ε : Type} (ids : List Nat) (algorithm : Nat),
   visibleEvent ids
     (Event.readable (α := α) (β := β) (ε := ε) (.pullCalled algorithm)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_readable_size_call :
  ∀ {α β ε : Type} (ids : List Nat) (call algorithm : Nat) (chunk : β),
   visibleEvent ids
     (Event.readable (α := α) (ε := ε) (.sizeCalled call algorithm chunk)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writable_sink_call :
  ∀ {α β ε : Type} (ids : List Nat) (algorithm : Nat)
   (op : Writable.SinkOperation α ε),
   visibleEvent ids
     (Event.writable (β := β) (.sinkCalled algorithm op)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writable_size_call :
  ∀ {α β ε : Type} (ids : List Nat) (call algorithm : Nat) (chunk : α),
   visibleEvent ids
     (Event.writable (β := β) (ε := ε) (.sizeCalled call algorithm chunk)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-- Frozen derived component/judgment equation under TRANSFORM-PG-BACKPRESSURE. -/
theorem visible_writable_signal_call :
  ∀ {α β ε : Type} (ids : List Nat) (call : Nat)
   (e : Boundary.Exception ε),
   visibleEvent ids
     (Event.writable (α := α) (β := β) (.signalCalled call e)) = none := by
  intros
  first | rfl | (simp_all [visibleEvent] <;> rfl)

/-! ## `PROMISE-PG-FIRST` bridging: the reaction list

`E-29`, `E-30`, `E-31` (generalize) and decision 8. `Transform.State.subscriptions` is the
one-list view of the two general lists: `reactions` builds both positionally, giving the
paired entries one id, and `Reactions.registered` is the fulfil list, so the registration
order Streams records is preserved. All three are mask M1. -/

/-- The shared registration cursor counts exactly the recorded subscriptions. Mask M1. -/
theorem reactions_next {α β ε : Type} (s : State α β ε) :
    (reactions s).next = s.subscriptions.length := by
  have key : ∀ (l : List (Subscription α))
      (rs : Whatwg.Ecma262.Promise.Reactions (Subscription α)),
      (l.foldl (fun rs sub =>
        (Whatwg.Ecma262.Promise.Reactions.add rs (subscriptionPromise sub)
          (some sub) (some sub) none).1) rs).next = rs.next + l.length := by
    intro l
    induction l with
    | nil => intro rs; simp
    | cons sub rest ih =>
        intro rs
        rw [List.foldl_cons, ih]
        simp only [Whatwg.Ecma262.Promise.Reactions.add, List.length_cons]
        omega
  simpa [reactions, Whatwg.Ecma262.Promise.Reactions.empty] using
    key s.subscriptions Whatwg.Ecma262.Promise.Reactions.empty

/-- Decision 8: the fulfil list alone carries the registration order that
`Transform.State.subscriptions` records (`E-29`). Mask M1. -/
theorem reactions_registered {α β ε : Type} (s : State α β ε) :
    (Whatwg.Ecma262.Promise.Reactions.registered (reactions s)).filterMap
        Whatwg.Ecma262.Promise.Reaction.handler = s.subscriptions := by
  have key : ∀ (l : List (Subscription α))
      (rs : Whatwg.Ecma262.Promise.Reactions (Subscription α)),
      (l.foldl (fun rs sub =>
        (Whatwg.Ecma262.Promise.Reactions.add rs (subscriptionPromise sub)
          (some sub) (some sub) none).1) rs).fulfill.filterMap
          Whatwg.Ecma262.Promise.Reaction.handler =
        rs.fulfill.filterMap Whatwg.Ecma262.Promise.Reaction.handler ++ l := by
    intro l
    induction l with
    | nil => intro rs; simp
    | cons sub rest ih =>
        intro rs
        rw [List.foldl_cons, ih]
        simp [Whatwg.Ecma262.Promise.Reactions.add]
  simpa [reactions, Whatwg.Ecma262.Promise.Reactions.registered,
    Whatwg.Ecma262.Promise.Reactions.empty] using
      key s.subscriptions Whatwg.Ecma262.Promise.Reactions.empty

/-- `E-30`: the identity captured at registration, independent of later slot
replacement, agrees with the general accessor. Mask M1. -/
theorem reactions_promises {α β ε : Type} (s : State α β ε) :
    (Whatwg.Ecma262.Promise.Reactions.registered (reactions s)).map
        Whatwg.Ecma262.Promise.Reaction.promise =
      s.subscriptions.map subscriptionPromise := by
  have key : ∀ (l : List (Subscription α))
      (rs : Whatwg.Ecma262.Promise.Reactions (Subscription α)),
      (l.foldl (fun rs sub =>
        (Whatwg.Ecma262.Promise.Reactions.add rs (subscriptionPromise sub)
          (some sub) (some sub) none).1) rs).fulfill.map
          Whatwg.Ecma262.Promise.Reaction.promise =
        rs.fulfill.map Whatwg.Ecma262.Promise.Reaction.promise ++ l.map subscriptionPromise := by
    intro l
    induction l with
    | nil => intro rs; simp
    | cons sub rest ih =>
        intro rs
        rw [List.foldl_cons, ih]
        simp [Whatwg.Ecma262.Promise.Reactions.add]
  simpa [reactions, Whatwg.Ecma262.Promise.Reactions.registered,
    Whatwg.Ecma262.Promise.Reactions.empty] using
      key s.subscriptions Whatwg.Ecma262.Promise.Reactions.empty

/-- `E-31`: the pending branch of `subscribe` is `Reactions.add`. The two settled branches
dispatch into the canonical component (`E-32` risk) and are therefore bridged on the job
queue, not here. Mask M1.

Amended by the Q3b fidelity addendum (finding F4, WS-PROM-CE-026): `Reactions.add` takes
the shared `_resultCapability_` of `op.performpromisethen` steps 7 and 8, and Streams
supplies `none` — `G-11`'s remainder, which `E-31` already records. -/
theorem subscribe_reactions_bridge {α β ε : Type} (s : State α β ε) (sub : Subscription α) :
    lookupPromise s (subscriptionPromise sub) = some .pending →
      (subscribe s sub).map reactions =
        some (Whatwg.Ecma262.Promise.Reactions.add (reactions s)
          (subscriptionPromise sub) (some sub) (some sub) none).1 := by
  intro h
  rw [subscribe_pending s sub h]
  simp [reactions, List.foldl_append]


/-! ## Q4: the three `generalize` bridges slice Q3 deferred

Rows 14, 15 and 16 of §4.4 of `test/contracts/promise-first-packet.contract.md`,
landed by `test/contracts/configuration-ordering.contract.md` §5.1–§5.3. Each
row was deferred with a stated reason; these are the halves that generalize,
with the stream-specific halves left where they are. -/

/-- Row 14 (`E-32`, generalize, Q4): the queueing half of `notify`, made
explicit. The component dispatch into `Readable.acceptPullAnswer` and
`Writable.acceptAnswer` stays in Streams; this is only the tag each branch
appends. `Jobs.ReactionJob` is not the carrier: `Transform.Job` carries three
component tags of which only one is a reaction, and `Jobs.Queue` is
payload-polymorphic (decision 4) precisely so its client supplies the payload.
Anchors: `op.newpromisereactionjob` (2702885..2705591) then
`hook.hostenqueuepromisejob` (633447..635836). -/
def notifyJob {α ε : Type} (sub : Subscription α) (answer : Readable.PullAnswer ε) :
    Job α ε :=
  match sub with
  | .readable promise => .readable promise
  | .writable _ request => .writable request
  | .reaction _ reaction => .reaction reaction answer

/-- Admitting an eventual answer never touches the shared promise table: the
writable branch only records the answer as a sink job. Mask M1. -/
private theorem acceptAnswer_promiseTable {α ε : Type} (s : Writable.State α ε)
    (kind : Writable.SinkKind) (id : Nat) (a : Writable.SinkAnswer ε)
    (w : Writable.State α ε) :
    Writable.acceptAnswer s kind id a = some w →
      Writable.promiseTable w = Writable.promiseTable s := by
  intro h
  unfold Writable.acceptAnswer at h
  by_cases hp : Writable.operationPhase s kind id = some .awaiting
  · rw [if_pos hp] at h
    injection h with h
    subst h
    cases kind <;> rfl
  · rw [if_neg hp] at h
    exact absurd h (by simp)

/-- The whole effect of one `notify` on the three slots the Q4 bridges read:
one job at the tail, the shared table untouched, the subscription list
untouched. Mask M2 for the first component, M1 for the others. -/
private theorem notify_effect {α β ε : Type} (s : State α β ε) (sub : Subscription α)
    (answer : Readable.PullAnswer ε) (t : State α β ε) :
    notify s sub answer = some t →
      t.jobs = s.jobs ++ [notifyJob sub answer] ∧
        Writable.promiseTable t.writable = Writable.promiseTable s.writable ∧
        t.subscriptions = s.subscriptions := by
  intro h
  cases sub with
  | readable promise =>
      cases hr : Readable.acceptPullAnswer s.readable answer with
      | none =>
          rw [notify, hr] at h
          exact absurd h (by simp)
      | some r =>
          rw [notify_readable s promise answer r hr] at h
          injection h with h
          subst h
          exact ⟨rfl, rfl, rfl⟩
  | writable promise request =>
      cases hw : Writable.acceptAnswer s.writable .write request
          (Writable.sinkAnswerFromShared answer) with
      | none =>
          rw [notify, hw] at h
          exact absurd h (by simp)
      | some w =>
          rw [notify_writable s promise request answer w hw] at h
          injection h with h
          subst h
          exact ⟨rfl, acceptAnswer_promiseTable _ _ _ _ _ hw, rfl⟩
  | reaction promise reaction =>
      rw [notify_reaction s promise reaction answer] at h
      injection h with h
      subst h
      exact ⟨rfl, rfl, rfl⟩

/-- Row 14 (`E-32`, generalize, Q4): the queue half of `notify` is exactly the
landed tail append. Mask M2: the statement observes the job entering the
queue. -/
theorem notify_jobQueue_bridge {α β ε : Type} (s : State α β ε) (sub : Subscription α)
    (answer : Readable.PullAnswer ε) (t : State α β ε) :
    notify s sub answer = some t →
      jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueue (jobQueue s) (notifyJob sub answer) := by
  intro h
  simp only [jobQueue, Whatwg.Ecma262.Jobs.Queue.enqueue, (notify_effect s sub answer t h).1]

/-- The same three facts, carried through the whole notification fold. -/
private theorem foldlM_notify_effect {α β ε : Type} (answer : Readable.PullAnswer ε)
    (subs : List (Subscription α)) :
    ∀ (u v : State α β ε),
      subs.foldlM (fun x sub => notify x sub answer) u = some v →
        v.jobs = u.jobs ++ subs.map (fun sub => notifyJob sub answer) ∧
          Writable.promiseTable v.writable = Writable.promiseTable u.writable ∧
          v.subscriptions = u.subscriptions := by
  induction subs with
  | nil =>
      intro u v h
      have huv : u = v := by simpa using h
      subst huv
      exact ⟨by simp, rfl, rfl⟩
  | cons sub rest ih =>
      intro u v h
      rw [List.foldlM_cons] at h
      cases hn : notify u sub answer with
      | none => rw [hn] at h; exact absurd h (by simp)
      | some w =>
          rw [hn] at h
          obtain ⟨h1, h2, h3⟩ := ih w v h
          obtain ⟨g1, g2, g3⟩ := notify_effect u sub answer w hn
          refine ⟨?_, ?_, ?_⟩
          · rw [h1, g1]
            simp
          · rw [h2, g2]
          · rw [h3, g3]

/-- Row 15 (`E-33`, generalize, Q4): the table half of `Transform.settle` is the
landed guarded settle, and the notification fold does not touch the table.
Anchors: `op.fulfillpromise` (2695419..2696230), `op.rejectpromise`
(2699323..2700252). Mask M1. -/
theorem settle_table_bridge {α β ε : Type} (s : State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : State α β ε) :
    lookupPromise s id = some .pending → settle s id answer = some t →
      Writable.promiseTable t.writable =
        Whatwg.Ecma262.Promise.Table.settle (Writable.promiseTable s.writable) id
          (match answer with
            | .fulfilled => Except.ok ()
            | .rejected e => Except.error e) := by
  intro hp hs
  rw [settle_pending s id answer hp] at hs
  rw [(foldlM_notify_effect answer _ _ t hs).2.1]
  exact Writable.settle_bridge s.writable id _

/-- Row 15 (`E-33`, generalize, Q4): the reaction half is **not** an equality of
reaction lists — `triggerReactions` advances a triggered registration's phase
and keeps it, while `Transform.settle` deletes it. This is the honest general
statement: the notification jobs enter the landed queue in registration order.
Anchor: `op.triggerpromisereactions` (2700260..2701212). Mask M2. -/
theorem settle_jobQueue_order {α β ε : Type} (s : State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : State α β ε) :
    lookupPromise s id = some .pending → settle s id answer = some t →
      jobQueue t =
        Whatwg.Ecma262.Jobs.Queue.enqueueAll (jobQueue s)
          ((s.subscriptions.filter (fun sub => subscriptionPromise sub == id)).map
            (fun sub => notifyJob sub answer)) := by
  intro hp hs
  rw [settle_pending s id answer hp] at hs
  simp only [jobQueue, Whatwg.Ecma262.Jobs.Queue.enqueueAll,
    (foldlM_notify_effect answer _ _ t hs).1, withWritable]

/-- Row 15 (`E-33`, generalize, Q4): the once-only half, the instance of
`triggerReactions_once` at this state — no subscription on the settled identity
is left waiting. Mask M1. -/
theorem settle_waiting_once {α β ε : Type} (s : State α β ε) (id : Nat)
    (answer : Readable.PullAnswer ε) (t : State α β ε) :
    lookupPromise s id = some .pending → settle s id answer = some t →
      Whatwg.Ecma262.Promise.Reactions.waitingOn (reactions t) id .fulfill = [] := by
  intro hp hs
  rw [settle_pending s id answer hp] at hs
  have hsub : t.subscriptions =
      s.subscriptions.filter (fun sub => subscriptionPromise sub != id) :=
    (foldlM_notify_effect answer _ _ t hs).2.2
  have hprom := reactions_promises t
  simp only [Whatwg.Ecma262.Promise.Reactions.registered] at hprom
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  have hmem : Whatwg.Ecma262.Promise.Reaction.promise r ∈
      (reactions t).fulfill.map Whatwg.Ecma262.Promise.Reaction.promise :=
    List.mem_map_of_mem hr
  rw [hprom, hsub] at hmem
  simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at hmem
  obtain ⟨sub, ⟨_, hne⟩, heq⟩ := hmem
  simp only [Bool.not_eq_true, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  left
  rw [← heq]
  exact hne

/-- Row 16 (`E-51`, generalize, Q4): the `.writable` branch runs exactly when
the landed `Jobs.Queue.dequeue` over Q3's `Writable.jobQueue` offers the
matching head. The tick half is the already-landed
`Writable.tick_dequeue_bridge`. Anchors: `hook.hostenqueuepromisejob`
(633447..635836) with `requirement.hostenqueuepromisejob.3` (634739..634841).
Mask M2. -/
theorem runJob_writable_dequeue {α β ε : Type} (s : State α β ε) (request : Nat)
    (first : Writable.SinkJob α ε) (rest : List (Writable.SinkJob α ε)) :
    s.writable.control = [] →
    Whatwg.Ecma262.Jobs.Queue.dequeue (Writable.jobQueue s.writable) =
        some (first, Whatwg.Ecma262.Jobs.Queue.mk rest) →
    first.kind = Writable.SinkKind.write → first.request = request →
      runJob s (.writable request) =
        (Writable.tick s.writable).map (withWritable s) := by
  intro hc hd hk hr
  have hjobs : s.writable.jobs = first :: rest := by
    cases hj : s.writable.jobs with
    | nil =>
        rw [Writable.jobQueue, hj] at hd
        exact absurd hd (by simp [Whatwg.Ecma262.Jobs.Queue.dequeue])
    | cons a b =>
        rw [Writable.jobQueue, hj] at hd
        simp only [Whatwg.Ecma262.Jobs.Queue.dequeue, Option.some.injEq, Prod.mk.injEq,
          Whatwg.Ecma262.Jobs.Queue.mk.injEq] at hd
        rw [hd.1, hd.2]
  exact runJob_writable s request first rest hc hjobs hk hr

/-- Row 16 (`E-51`, generalize, Q4): and it is blocked when the landed queue
offers no head at all. Mask M1, under the run condition
`requirement.jobs.1` (625769..626250). -/
theorem runJob_writable_blocked {α β ε : Type} (s : State α β ε) (request : Nat) :
    Whatwg.Ecma262.Jobs.Queue.dequeue (Writable.jobQueue s.writable) = none →
      runJob s (.writable request) = none := by
  intro hd
  have hjobs : s.writable.jobs = [] := by
    cases hj : s.writable.jobs with
    | nil => rfl
    | cons a b =>
        rw [Writable.jobQueue, hj] at hd
        exact absurd hd (by simp [Whatwg.Ecma262.Jobs.Queue.dequeue])
  refine runJob_writable_requires_matching s request (Or.inr ?_)
  intro job tail hjt
  rw [hjobs] at hjt
  exact absurd hjt (by simp)

end Whatwg.Streams.Transform
