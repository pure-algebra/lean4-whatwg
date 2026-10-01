import Whatwg.Streams.Readable.Step

/-!
# The readable queue invariant

Owner: `READABLE-PG-DEFAULT`, construction edge. `QueueInv` is the
queue-with-sizes invariant of `DATA-PG-QUEUE` (`Data.Queue.WF` and
`Data.Queue.SizesAdmissible` at `sizes`) read off the readable `[[queue]]`.
It is inductive: `step_queueInv` carries no reachability hypothesis, and the
closure theorem `steps_queueInv` is `Kernel.Path.invariant` through
`steps_iff_path`.

Three operations change the queue: `error` resets it (`Data.resetQueue`),
`finishEnqueue` grows it (`Data.enqueueValueWithSize`) and `read` shrinks it
(`Data.dequeueValue`, which needs the dyadic size class to be classified,
ordered and exact). Every other operation keeps it. Counterexample
`WS-KERNEL-CE-005` is the `finishEnqueue` that appends without
`Data.enqueueValueWithSize`.

Opened by slice W8a.3 (ruling R-W4). Packet:
`test/contracts/transition-kernel.contract.md`, section 5.1, and the W8a
amendment of `test/contracts/readable-default.contract.md`. No observation
mask is named: the invariant concerns the local derivation closure.
-/

namespace Whatwg.Streams.Readable

variable {α ε : Type}

/-- The queue-with-sizes invariant of `DATA-PG-QUEUE` at the readable size
class, read off `[[queue]]`. -/
def QueueInv (s : State α ε) : Prop :=
  Data.Queue.WF sizes s.queue ∧ Data.Queue.SizesAdmissible sizes s.queue

private theorem queueInv_of_eq {t : State α ε} {q : Data.Queue α Size} (h : t.queue = q)
    (hq : Data.Queue.WF sizes q ∧ Data.Queue.SizesAdmissible sizes q) : QueueInv t := by
  unfold QueueInv; rw [h]; exact hq

private theorem queueInv_of_queue {s t : State α ε} (h : t.queue = s.queue) :
    QueueInv s → QueueInv t :=
  queueInv_of_eq h

private theorem continuePull_queue (s : State α ε) (k : PullContinuation α) :
    (continuePull s k).queue = s.queue := by
  fun_cases continuePull s k <;> rfl

private theorem callPullIfNeededWith_queue (s : State α ε) (k : PullContinuation α) :
    (callPullIfNeededWith s k).queue = s.queue := by
  fun_cases callPullIfNeededWith s k <;> first | rfl | exact continuePull_queue _ k

private theorem streamClose_queue (s : State α ε) : (streamClose s).queue = s.queue := by
  fun_cases streamClose s <;> rfl

/-- Dequeueing a value keeps both halves of the invariant. -/
private theorem dequeue_queueInv {s : State α ε} {chunk : α} {q : Data.Queue α Size}
    (hq : Data.dequeueValue sizes s.queue = some (chunk, q)) (hs : QueueInv s) :
    Data.Queue.WF sizes q ∧ Data.Queue.SizesAdmissible sizes q :=
  ⟨Data.dequeueValue_wf sizes s.queue q chunk (sizes_eq ▸ Data.DyadicSize.classified)
      (sizes_eq ▸ Data.DyadicSize.ordered) (sizes_eq ▸ Data.DyadicSize.exact) hs.1 hs.2 hq,
    Data.dequeueValue_sizesAdmissible sizes s.queue q chunk hs.2 hq⟩

private theorem error_queueInv (s : State α ε) (e : Boundary.Exception ε) :
    QueueInv s → QueueInv (error s e) := by
  intro hs
  fun_cases error s e
  · exact ⟨Data.resetQueue_wf sizes s.queue, Data.resetQueue_sizesAdmissible sizes s.queue⟩
  · exact hs

private theorem finishEnqueue_queueInv (s : State α ε) (call : Nat) (chunk : α)
    (answer : Data.SizeAnswer Size (Boundary.Exception ε)) :
    QueueInv s → QueueInv (finishEnqueue s call chunk answer) := by
  intro hs
  fun_cases finishEnqueue s call chunk answer
  · exact error_queueInv s _ hs
  · refine queueInv_of_eq (callPullIfNeededWith_queue _ _) ?_
    exact ⟨Data.enqueueValueWithSize_wf sizes s.queue _ chunk _ hs.1 ‹_›,
      Data.enqueueValueWithSize_sizesAdmissible sizes s.queue _ chunk _ hs.2 ‹_›⟩
  · exact error_queueInv _ _ hs

private theorem read_queueInv (s : State α ε) : QueueInv s → QueueInv (read s) := by
  intro hs
  fun_cases read s
  all_goals cases ‹freshReadCell _ _ = _›
  · exact hs
  · exact hs
  · exact queueInv_of_queue (callPullIfNeededWith_queue _ _) hs
  · exact queueInv_of_eq ((continuePull_queue _ _).trans (streamClose_queue _))
      (dequeue_queueInv ‹_› hs)
  · exact queueInv_of_eq (callPullIfNeededWith_queue _ _) (dequeue_queueInv ‹_› hs)

private theorem beginEnqueue_queueInv (s : State α ε) (chunk : α) :
    QueueInv s → QueueInv (beginEnqueue s chunk) := by
  intro hs
  fun_cases beginEnqueue s chunk
  · exact queueInv_of_queue (callPullIfNeededWith_queue _ _) hs
  · exact hs
  · exact finishEnqueue_queueInv _ _ _ _ hs
  · exact hs
  · exact hs

private theorem close_queueInv (s : State α ε) : QueueInv s → QueueInv (close s) := by
  intro hs
  fun_cases close s
  · exact queueInv_of_queue (streamClose_queue _) hs
  · exact hs
  · exact hs

private theorem resumeSize_queueInv {s t : State α ε}
    {answer : Data.SizeAnswer Size (Boundary.Exception ε)} :
    QueueInv s → resumeSize s answer = some t → QueueInv t := by
  intro hs
  fun_cases resumeSize s answer
  · intro h; cases h; exact finishEnqueue_queueInv _ _ _ _ hs
  · intro h; cases h

private theorem acceptPullAnswer_queueInv {s t : State α ε} {answer : PullAnswer ε} :
    QueueInv s → acceptPullAnswer s answer = some t → QueueInv t := by
  intro hs
  fun_cases acceptPullAnswer s answer
  · intro h; cases h; exact hs
  · intro h; cases h

private theorem returnPull_queueInv {s t : State α ε} {result : PullReturn ε} :
    QueueInv s → returnPull s result = some t → QueueInv t := by
  intro hs
  fun_cases returnPull s result
  · intro h; cases h
    refine queueInv_of_queue ((continuePull_queue _ _).trans ?_) hs
    cases result <;> rfl
  · intro h; cases h

/-- Every external step keeps the queue invariant. No reachability hypothesis:
the invariant is inductive. -/
theorem step_queueInv {s t : State α ε} {d : Decision α ε} :
    QueueInv s → Step s d t → QueueInv t := by
  intro hs
  rw [step_iff]
  fun_cases step s d
  · intro h; cases h; exact read_queueInv s hs
  · intro h; cases h; exact beginEnqueue_queueInv s _ hs
  · intro h; cases h; exact close_queueInv s hs
  · intro h; cases h; exact error_queueInv s _ hs
  · exact resumeSize_queueInv hs
  · exact acceptPullAnswer_queueInv hs
  · exact returnPull_queueInv hs
  · intro h; cases h; exact hs

/-- The invariant is carried along every finite external derivation:
`Kernel.Path.invariant` through `steps_iff_path`. -/
theorem steps_queueInv {s t : State α ε} {ds : List (Decision α ε)} :
    Steps s ds t → QueueInv s → QueueInv t :=
  fun h => Kernel.Path.invariant (fun _ _ _ hs hst => step_queueInv hs hst)
    (steps_iff_path.mp h)

/-- The frozen post-start view starts with the empty queue, which satisfies the
invariant. -/
theorem initial_queueInv (algorithms : Algorithms) (hwm : Size) :
    QueueInv (initial (α := α) (ε := ε) algorithms hwm) :=
  ⟨Data.Queue.WF_empty sizes, Data.Queue.SizesAdmissible_empty sizes⟩

end Whatwg.Streams.Readable
