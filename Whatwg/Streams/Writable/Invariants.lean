import Whatwg.Streams.Writable.Step

/-!
# The writable queue invariant

Owner: `WRITABLE-PG-DEFAULT`, construction edge. `QueueInv` is the
queue-with-sizes invariant of `DATA-PG-QUEUE` (`Data.Queue.WF` and
`Data.Queue.SizesAdmissible` at `sizes`) read off the writable `[[queue]]`.
It is inductive for both stages: neither `tick_queueInv` nor
`decide_queueInv` carries a reachability hypothesis, and the closure theorem
`reaches_queueInv` is `Kernel.Path.invariant` through `reaches_iff_path`.

`decide` never changes the queue. A `tick` step leaves it as it was, grows it
by `Data.enqueueValueWithSize` (`enqueueWrite`, `beginClose`), shrinks it by
`Data.dequeueValue` (the close sentinel in `advance`, a fulfilled write
reaction), or resets it to `Data.Queue.empty` (`finishErroring`); the sink
invocation `invokeSink` keeps it.

Opened by slice W8a.3 (ruling R-W4). Packet:
`test/contracts/transition-kernel.contract.md`, section 5.2, and the W8a
amendment of `test/contracts/writable-default.contract.md`. No observation
mask is named: the invariant concerns the local derivation closure, and the
local machine is not exclusive (`WS-KERNEL-CE-002`).
-/

namespace Whatwg.Streams.Writable

variable {α ε : Type}

/-- The queue-with-sizes invariant of `DATA-PG-QUEUE` at the writable size
class, read off `[[queue]]`. -/
def QueueInv (s : State α ε) : Prop :=
  Data.Queue.WF sizes s.queue ∧ Data.Queue.SizesAdmissible sizes s.queue

private theorem queueInv_of_eq {t : State α ε} {q : Data.Queue (QueueItem α) Size}
    (h : t.queue = q) (hq : Data.Queue.WF sizes q ∧ Data.Queue.SizesAdmissible sizes q) :
    QueueInv t := by
  unfold QueueInv; rw [h]; exact hq

private theorem queueInv_of_queue {s t : State α ε} (h : t.queue = s.queue) :
    QueueInv s → QueueInv t :=
  queueInv_of_eq h

/-! ## Operations that keep the queue -/

private theorem freshPromise_queue (s : State α ε) (o : UnitPromise ε) :
    (freshPromise s o).1.queue = s.queue := by
  cases o <;> rfl

private theorem settle_queue (s : State α ε) (id : Nat) (r : Except (Boundary.Exception ε) Unit) :
    (settle s id r).queue = s.queue := rfl

private theorem markHandled_queue (s : State α ε) (id : Nat) :
    (markHandled s id).queue = s.queue := by
  fun_cases markHandled s id <;> rfl

private theorem updateBackpressure_queue (s : State α ε) (b : Bool) :
    (updateBackpressure s b).queue = s.queue := by
  fun_cases updateBackpressure s b
  · rfl
  · exact freshPromise_queue s .pending
  · rfl

private theorem ensureReadyRejected_queue (s : State α ε) (e : Boundary.Exception ε) :
    (ensureReadyRejected s e).queue = s.queue := by
  fun_cases ensureReadyRejected s e
  · exact markHandled_queue _ _
  · exact (markHandled_queue _ _).trans (freshPromise_queue s _)

private theorem foldl_settle_queue (l : List Nat) (r : Except (Boundary.Exception ε) Unit)
    (s : State α ε) : (l.foldl (fun st id => settle st id r) s).queue = s.queue := by
  induction l generalizing s with
  | nil => rfl
  | cons id rest ih => exact ih _

private theorem attachSink_queue (s : State α ε) (op : SinkOperation α ε) (ret : SinkReturn ε) :
    (attachSink s op ret).queue = s.queue := by
  fun_cases attachSink s op ret <;> cases op <;> rfl

/-- The sink invocation keeps the queue, so it keeps the invariant. -/
private theorem invokeSink_queueInv {s t : State α ε} {op : SinkOperation α ε} :
    invokeSink s op = some t → QueueInv s → QueueInv t := by
  fun_cases invokeSink s op
  · intro h; cases h
  · intro h; cases h; exact queueInv_of_queue (attachSink_queue s op _)
  · intro h; cases h; exact queueInv_of_queue (by cases op <;> rfl)

private theorem acceptAnswer_queue {s t : State α ε} {k : SinkKind} {id : Nat}
    {a : SinkAnswer ε} : acceptAnswer s k id a = some t → t.queue = s.queue := by
  fun_cases acceptAnswer s k id a
  · intro h; cases h; cases k <;> rfl
  · intro h; cases h

/-! ## Operations that change the queue -/

private theorem enqueue_queueInv {s : State α ε} {item : QueueItem α} {size : Size}
    {q : Data.Queue (QueueItem α) Size} (hs : QueueInv s)
    (hq : Data.enqueueValueWithSize sizes s.queue item size = .ok q) :
    Data.Queue.WF sizes q ∧ Data.Queue.SizesAdmissible sizes q :=
  ⟨Data.enqueueValueWithSize_wf sizes s.queue q item size hs.1 hq,
    Data.enqueueValueWithSize_sizesAdmissible sizes s.queue q item size hs.2 hq⟩

private theorem dequeue_queueInv {s : State α ε} {item : QueueItem α}
    {q : Data.Queue (QueueItem α) Size} (hs : QueueInv s)
    (hq : Data.dequeueValue sizes s.queue = some (item, q)) :
    Data.Queue.WF sizes q ∧ Data.Queue.SizesAdmissible sizes q :=
  ⟨Data.dequeueValue_wf sizes s.queue q item Data.DyadicSize.classified
      Data.DyadicSize.ordered Data.DyadicSize.exact hs.1 hs.2 hq,
    Data.dequeueValue_sizesAdmissible sizes s.queue q item hs.2 hq⟩

private theorem empty_queueInv :
    Data.Queue.WF sizes (Data.Queue.empty (α := QueueItem α) sizes) ∧
      Data.Queue.SizesAdmissible sizes (Data.Queue.empty (α := QueueItem α) sizes) :=
  ⟨Data.Queue.WF_empty sizes, Data.Queue.SizesAdmissible_empty sizes⟩

/-! ## The two stages -/

/-- The deterministic stage keeps the queue invariant. No reachability
hypothesis: the invariant is inductive. -/
theorem tick_queueInv (s t : State α ε) : QueueInv s → tick s = some t → QueueInv t := by
  intro hs
  fun_cases tick s
  all_goals intro h
  -- Inline the `let` bindings of `tick` into the step hypothesis.
  all_goals try simp (config := { zetaDelta := true }) only at h
  -- A branch that does not step closes here; a branch through `invokeSink`
  -- reduces to its argument; any other branch names its successor.
  all_goals first
    | (cases h; done)
    | refine invokeSink_queueInv h ?_
    | cases h
  -- The successor's queue is the old one, a grown one, a shrunk one, or empty.
  all_goals first
    | (refine queueInv_of_queue ?_ hs
       repeat' split
       all_goals try simp (config := { zetaDelta := true }) only [freshPromise_queue,
         settle_queue, markHandled_queue, updateBackpressure_queue, ensureReadyRejected_queue,
         foldl_settle_queue]
       all_goals rfl)
    | (refine queueInv_of_eq ?_ (enqueue_queueInv hs ‹Data.enqueueValueWithSize _ _ _ _ = _›)
       repeat' split
       all_goals try simp (config := { zetaDelta := true }) only [settle_queue,
         updateBackpressure_queue]
       all_goals rfl)
    | (refine queueInv_of_eq ?_ (dequeue_queueInv hs ‹Data.dequeueValue _ _ = _›)
       repeat' split
       all_goals try simp (config := { zetaDelta := true }) only [updateBackpressure_queue]
       all_goals rfl)
    | (refine queueInv_of_eq ?_ empty_queueInv
       repeat' split
       all_goals try simp (config := { zetaDelta := true }) only [settle_queue,
         foldl_settle_queue]
       all_goals rfl)

/-- The admission stage keeps the queue invariant; no decision touches the
queue. -/
theorem decide_queueInv (s t : State α ε) (d : Decision α ε) :
    QueueInv s → decide s d = some t → QueueInv t := by
  intro hs
  fun_cases decide s d
  all_goals intro h
  all_goals first
    | (cases h; done)
    | exact queueInv_of_queue (acceptAnswer_queue h) hs
    | (cases h; exact queueInv_of_queue (attachSink_queue _ _ _) hs)
    | (cases h; exact hs)

/-- Every step keeps the queue invariant. -/
theorem step_queueInv {s t : State α ε} {d : Option (Decision α ε)} :
    QueueInv s → Step s d t → QueueInv t := by
  intro hs h
  cases d with
  | none => exact tick_queueInv s t hs h
  | some a => exact decide_queueInv s t a hs h

/-- The invariant is carried along every finite derivation:
`Kernel.Path.invariant` through `reaches_iff_path`. -/
theorem reaches_queueInv {s t : State α ε} {ds : List (Option (Decision α ε))} :
    Reaches s ds t → QueueInv s → QueueInv t :=
  fun h => Kernel.Path.invariant (fun _ _ _ hs hst => step_queueInv hs hst)
    (reaches_iff_path.mp h)

/-- The admitted post-start projection starts with the empty queue, which
satisfies the invariant. -/
theorem initial_queueInv (hwm : Size) (alg : Algorithms) (promiseSeed errorSeed : Nat) :
    QueueInv (initial (α := α) (ε := ε) hwm alg promiseSeed errorSeed) :=
  empty_queueInv

end Whatwg.Streams.Writable
