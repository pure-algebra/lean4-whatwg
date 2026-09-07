import Whatwg.Infra

/-!
# ECMAScript jobs and job queues

Owner: the Jobs and Host Operations to Enqueue Jobs clause of the pinned
ES2026 source, at the first-packet surface `PROMISE-PG-FIRST` freezes
(`test/contracts/promise-first-packet.contract.md`).

Landed here: the payload-polymorphic FIFO queue (`E-45`, `E-48`, `E-52`,
generalize; gap `G-07`), the reaction-job record (`E-44`, generalize; `G-07`),
the activation state and run condition (`G-08`), and the DB-05
specification/realizer pair `requirement.hostenqueuepromisejob.3` needs
(`E-46`, `E-49`, `E-53`, generalize).

Ruling DB-03 models the queue as deterministic FIFO state inside the
configuration, not as a decision. `run` is not a semantic fuel parameter:
`run_split` states that whatever it did not run is still queued, so exhaustion
is a live frontier and never a terminal outcome (DB-07).

Still open, with their gap ids: the realm parameter, the Job Abstract Closure
carrier beyond a first-order descriptor, `HostMakeJobCallback`,
`HostCallJobCallback` and the JobCallback record's `[[HostDefined]]` field
(`G-07` remainder); a single global configuration that observes the run
condition (`G-08` remainder, P8).

Layering (DB-11): this module imports only `Whatwg.Infra`, and nothing here
mentions a promise state, so the queue stays payload-polymorphic (decision 4).
-/

namespace Whatwg.Ecma262.Jobs

/--
`hook.hostenqueuepromisejob` (633447..635836): the realm-independent job queue
as first-order state. `E-45`, `E-48`, `E-52` (generalize): the three Streams
job lists are its instances at three payloads, so `DecidableEq` and `Repr` are
conditional on the payload.
-/
structure Queue (payload : Type) where
  pending : List payload
  deriving DecidableEq, Repr

/-- The empty job queue. -/
def Queue.empty {payload : Type} : Queue payload := Queue.mk []

/-- `HostEnqueuePromiseJob` appends at the tail, so the oldest job leaves first. -/
def Queue.enqueue {payload : Type} (q : Queue payload) (job : payload) : Queue payload :=
  Queue.mk (q.pending ++ [job])

/-- Schedule several jobs, retaining their argument order behind the queued ones. -/
def Queue.enqueueAll {payload : Type} (q : Queue payload) (jobs : List payload) :
    Queue payload :=
  Queue.mk (q.pending ++ jobs)

/-- The job that was scheduled first, without removing it. -/
def Queue.oldest {payload : Type} (q : Queue payload) : Option payload := q.pending.head?

/-- Dequeue-oldest: the FIFO step `requirement.hostenqueuepromisejob.3` constrains. -/
def Queue.dequeue {payload : Type} (q : Queue payload) :
    Option (payload × Queue payload) :=
  match q.pending with
  | [] => none
  | job :: rest => some (job, Queue.mk rest)

/--
`op.newpromisereactionjob` (2702885..2705591) and `record.jobcallback-records`
(628436..630247), reduced to the capture list. `E-44` (generalize) keeps the
argument payload-polymorphic so that this module never mentions a promise
state.
-/
structure ReactionJob (arg : Type) where
  reaction : Nat
  argument : arg
  deriving DecidableEq, Repr

/-- `op.newpromisereactionjob`: capture the reaction identity and its argument. -/
def newReactionJob {arg : Type} (reaction : Nat) (argument : arg) : ReactionJob arg :=
  ReactionJob.mk reaction argument

/--
The agent's current activation. P8a rename class "rename only":
`Semantics.Ordering.Active`, with `observer` renamed `job` and both
job-carrying constructors taking a serial rather than the whole record.
`E-47` (keep) fixes that `Writable.Control.react` is not re-stated here.
-/
inductive Active where
  | script
  | intrinsic (id : Nat)
  | job (id : Nat)
  | checkpoint
  deriving DecidableEq

/-- `requirement.jobs.1` (625769..626250) as a decidable observation. -/
def mayRun : Active → Bool
  | .checkpoint => true
  | _ => false

/--
`requirement.jobs.1` and `requirement.jobs.2` (626257..626350) as one
condition: a job may start only at a checkpoint, where the agent has no
running execution context and its stack is empty, and only one job is
undergoing evaluation. `G-08`: the three Streams spellings approximate this
per component.
-/
def RunCondition (active : Active) : Prop := active = Active.checkpoint

/--
`requirement.hostenqueuepromisejob.3` (634739..634841) as the specification
over runs: what was executed is a prefix of what was scheduled, so a job
scheduled after another never overtakes it. DB-05: this is the specification
half of the pair, and `run` below is its realizer.
-/
def FifoRequirement {payload : Type} (scheduled executed : List payload) : Prop :=
  List.IsPrefix executed scheduled

/-- One realizer step: dequeue-oldest, and only under the run condition. -/
def step {payload : Type} (active : Active) (q : Queue payload) :
    Option (payload × Queue payload) :=
  match active with
  | .checkpoint => Queue.dequeue q
  | _ => none

/--
The deterministic FIFO realizer `E-46`, `E-49` and `E-53` extract from three
places. The `Nat` argument bounds how far this observation reaches; it is not
a semantic fuel parameter, because `run_split` returns whatever was not run.
-/
def run {payload : Type} : Nat → Queue payload → List payload × Queue payload
  | 0, q => ([], q)
  | fuel + 1, q =>
      match q.pending with
      | [] => ([], q)
      | job :: rest =>
          (job :: (run fuel (Queue.mk rest)).1, (run fuel (Queue.mk rest)).2)

/-- `hook.hostenqueuepromisejob` (633447..635836): the host schedules at the tail. -/
def hostEnqueuePromiseJob {payload : Type} (q : Queue payload) (job : payload) :
    Queue payload :=
  Queue.enqueue q job

/-! ## Queue equations — mask M1 -/

/-- The empty queue holds no job. Mask M1. -/
theorem Queue.empty_eq {payload : Type} :
    (Queue.empty : Queue payload) = Queue.mk [] := rfl

/-- `HostEnqueuePromiseJob` appends at the tail. Mask M1. -/
theorem Queue.enqueue_eq {payload : Type} (q : Queue payload) (job : payload) :
    Queue.enqueue q job = Queue.mk (q.pending ++ [job]) := rfl

/-- Bulk scheduling retains argument order behind the queued jobs. Mask M1. -/
theorem Queue.enqueueAll_eq {payload : Type} (q : Queue payload) (jobs : List payload) :
    Queue.enqueueAll q jobs = Queue.mk (q.pending ++ jobs) := rfl

/-- The oldest job is the head of the pending list. Mask M1. -/
theorem Queue.oldest_eq {payload : Type} (q : Queue payload) :
    Queue.oldest q = q.pending.head? := rfl

/-- An empty queue has no next job. Mask M1. -/
theorem Queue.dequeue_empty {payload : Type} :
    Queue.dequeue (Queue.empty : Queue payload) = none := rfl

/--
The branch equation both Streams corollaries instantiate: `E-46`'s
`Writable.tick_job_fifo` and `E-53`'s `Transform.tick_job_fifo` are its
consequences under their own empty-execution-context guards. Mask M2.
-/
theorem Queue.dequeue_cons {payload : Type} (job : payload) (rest : List payload) :
    Queue.dequeue (Queue.mk (job :: rest)) = some (job, Queue.mk rest) := rfl

/--
`requirement.hostenqueuepromisejob.3` (634739..634841, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`): a job
scheduled after the oldest never overtakes it. Taking `later := []` gives
`dequeue_cons`, which is what both Streams corollaries need. Mask M2.
-/
theorem Queue.dequeue_fifo {payload : Type} (oldest : payload) (queued later : List payload) :
    Queue.dequeue (Queue.enqueueAll (Queue.mk (oldest :: queued)) later) =
      some (oldest, Queue.mk (queued ++ later)) := rfl

/-! ## The run condition — mask M1 -/

/-- Only a checkpoint activation may start a job. Mask M1. -/
theorem mayRun_iff (active : Active) : mayRun active = true ↔ active = Active.checkpoint := by
  cases active <;> simp [mayRun]

/-- The `Prop` and `Bool` faces of `requirement.jobs.1` agree. Mask M1. -/
theorem RunCondition_iff (active : Active) :
    RunCondition active ↔ active = Active.checkpoint := Iff.rfl

/-- At a checkpoint the realizer step is exactly dequeue-oldest. Mask M1. -/
theorem step_checkpoint {payload : Type} (q : Queue payload) :
    step Active.checkpoint q = Queue.dequeue q := rfl

/--
`requirement.jobs.2` (626257..626350): no job starts in any other activation,
so only one job is actively undergoing evaluation. Mask M1.
-/
theorem step_blocked {payload : Type} (active : Active) (q : Queue payload) :
    active ≠ Active.checkpoint → step active q = none := by
  cases active <;> intro h <;> first | rfl | exact absurd rfl h

/-! ## The realizer of `requirement.hostenqueuepromisejob.3` — mask M2 -/

/-- The specification is exactly the prefix relation over runs. Mask M1. -/
theorem FifoRequirement_iff {payload : Type} (scheduled executed : List payload) :
    FifoRequirement scheduled executed ↔ List.IsPrefix executed scheduled := Iff.rfl

/-- A zero-reach observation runs nothing and queues everything. Mask M1. -/
theorem run_zero {payload : Type} (q : Queue payload) : run 0 q = ([], q) := rfl

/-- An empty queue runs nothing at any reach. Mask M1. -/
theorem run_nil {payload : Type} (fuel : Nat) :
    run fuel (Queue.mk ([] : List payload)) = ([], Queue.mk []) := by
  cases fuel <;> rfl

/-- One step of the realizer delivers the oldest job first. Mask M2. -/
theorem run_cons {payload : Type} (fuel : Nat) (job : payload) (rest : List payload) :
    run (fuel + 1) (Queue.mk (job :: rest)) =
      (job :: (run fuel (Queue.mk rest)).1, (run fuel (Queue.mk rest)).2) := rfl

/--
DB-07: whatever the observation did not run is still queued, so exhaustion is
a live frontier and never a terminal outcome. Mask M1.
-/
theorem run_split {payload : Type} (fuel : Nat) (q : Queue payload) :
    (run fuel q).1 ++ (run fuel q).2.pending = q.pending := by
  induction fuel generalizing q with
  | zero => simp [run]
  | succ n ih =>
      obtain ⟨pending⟩ := q
      cases pending with
      | nil => simp [run]
      | cons job rest =>
          have step := ih (Queue.mk rest)
          simp only [run, List.cons_append]
          exact congrArg (fun l => job :: l) step

/--
The realizer theorem for `requirement.hostenqueuepromisejob.3`: what the
realizer executed is a prefix of what was scheduled. Mask M2.
-/
theorem run_fifo {payload : Type} (fuel : Nat) (q : Queue payload) :
    FifoRequirement q.pending (run fuel q).1 :=
  ⟨(run fuel q).2.pending, run_split fuel q⟩

/--
The realizer still satisfies the requirement when further jobs are scheduled
before the run. Mask M2.
-/
theorem hostEnqueuePromiseJob_order {payload : Type} (fuel : Nat) (q : Queue payload)
    (later : List payload) :
    FifoRequirement (q.pending ++ later) (run fuel (Queue.enqueueAll q later)).1 :=
  run_fifo fuel (Queue.enqueueAll q later)

/-- The host hook is the tail enqueue and nothing else. Mask M1. -/
theorem hostEnqueuePromiseJob_eq {payload : Type} (q : Queue payload) (job : payload) :
    hostEnqueuePromiseJob q job = Queue.enqueue q job := rfl

/-- `op.newpromisereactionjob` builds exactly the capture record. Mask M1. -/
theorem newReactionJob_eq {arg : Type} (reaction : Nat) (argument : arg) :
    newReactionJob reaction argument = ReactionJob.mk reaction argument := rfl

end Whatwg.Ecma262.Jobs
