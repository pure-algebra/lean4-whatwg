import Whatwg.Ecma262

/-!
Breaker-owned Q3 law battery for `Whatwg.Ecma262.Jobs`.
Contract: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`.

Masks (DB-04). A law whose statement observes the *order* in which jobs are
delivered is **M2**; a law that observes only a value, a branch or a terminal
result is **M1**. Each block below names its mask. No law here is a claim about
a host, a stream, or a coverage row.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ### Queue equations — mask M1 (no order is observed) -/

#check (@Whatwg.Ecma262.Jobs.Queue.empty_eq :
  ∀ {payload : Type},
    (Whatwg.Ecma262.Jobs.Queue.empty : Whatwg.Ecma262.Jobs.Queue payload) =
      Whatwg.Ecma262.Jobs.Queue.mk [])

#check (@Whatwg.Ecma262.Jobs.Queue.enqueue_eq :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload) (job : payload),
    Whatwg.Ecma262.Jobs.Queue.enqueue q job =
      Whatwg.Ecma262.Jobs.Queue.mk (q.pending ++ [job]))

#check (@Whatwg.Ecma262.Jobs.Queue.enqueueAll_eq :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload) (jobs : List payload),
    Whatwg.Ecma262.Jobs.Queue.enqueueAll q jobs =
      Whatwg.Ecma262.Jobs.Queue.mk (q.pending ++ jobs))

#check (@Whatwg.Ecma262.Jobs.Queue.oldest_eq :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload),
    Whatwg.Ecma262.Jobs.Queue.oldest q = q.pending.head?)

#check (@Whatwg.Ecma262.Jobs.Queue.dequeue_empty :
  ∀ {payload : Type},
    Whatwg.Ecma262.Jobs.Queue.dequeue
        (Whatwg.Ecma262.Jobs.Queue.empty : Whatwg.Ecma262.Jobs.Queue payload) = none)

/-! The branch equation both Streams corollaries instantiate: `E-46`'s
`Writable.tick_job_fifo` and `E-53`'s `Transform.tick_job_fifo` are its
consequences under their own empty-execution-context guards. Mask M2. -/
#check (@Whatwg.Ecma262.Jobs.Queue.dequeue_cons :
  ∀ {payload : Type} (job : payload) (rest : List payload),
    Whatwg.Ecma262.Jobs.Queue.dequeue (Whatwg.Ecma262.Jobs.Queue.mk (job :: rest)) =
      some (job, Whatwg.Ecma262.Jobs.Queue.mk rest))

/-! ### The general FIFO law — mask M2

This is the one general law of the packet from which `Writable.tick_job_fifo`
and `Transform.tick_job_fifo` are re-derived. Taking `later := []` gives
`dequeue_cons`, which is what both corollaries need; taking `later` nonempty is
the ordering content of `requirement.hostenqueuepromisejob.3`: a job scheduled
after `oldest` never overtakes it. -/

#check (@Whatwg.Ecma262.Jobs.Queue.dequeue_fifo :
  ∀ {payload : Type} (oldest : payload) (queued later : List payload),
    Whatwg.Ecma262.Jobs.Queue.dequeue
        (Whatwg.Ecma262.Jobs.Queue.enqueueAll
          (Whatwg.Ecma262.Jobs.Queue.mk (oldest :: queued)) later) =
      some (oldest, Whatwg.Ecma262.Jobs.Queue.mk (queued ++ later)))

/-! ### The run condition — mask M1

`requirement.jobs.1` (625769..626250) allows a job to start only when the agent
has no running execution context and its stack is empty;
`requirement.jobs.2` (626257..626350) allows only one at a time. Both are the
single condition `RunCondition active`, which the three Streams spellings
(`Readable.State.frames = []`, `Writable.State.control = []`, and the
transform's three-way guard) approximate per component (`G-08`). -/

#check (@Whatwg.Ecma262.Jobs.mayRun_iff :
  ∀ (active : Whatwg.Ecma262.Jobs.Active),
    Whatwg.Ecma262.Jobs.mayRun active = true ↔ active = Whatwg.Ecma262.Jobs.Active.checkpoint)

#check (@Whatwg.Ecma262.Jobs.RunCondition_iff :
  ∀ (active : Whatwg.Ecma262.Jobs.Active),
    Whatwg.Ecma262.Jobs.RunCondition active ↔
      active = Whatwg.Ecma262.Jobs.Active.checkpoint)

#check (@Whatwg.Ecma262.Jobs.step_checkpoint :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload),
    Whatwg.Ecma262.Jobs.step Whatwg.Ecma262.Jobs.Active.checkpoint q =
      Whatwg.Ecma262.Jobs.Queue.dequeue q)

#check (@Whatwg.Ecma262.Jobs.step_blocked :
  ∀ {payload : Type} (active : Whatwg.Ecma262.Jobs.Active)
    (q : Whatwg.Ecma262.Jobs.Queue payload),
    active ≠ Whatwg.Ecma262.Jobs.Active.checkpoint →
      Whatwg.Ecma262.Jobs.step active q = none)

/-! ### The realizer of `requirement.hostenqueuepromisejob.3` — mask M2

`run fuel q` is the deterministic FIFO realizer; `FifoRequirement` is the
specification. This is the DB-05 pair R-P5 requires, in the same shape as
`ReadableStreamPipeTo`. `run` is not a semantic fuel parameter: `run_split`
states that whatever it did not run is still queued, so exhaustion is a live
frontier and never a terminal outcome (DB-07). -/

#check (@Whatwg.Ecma262.Jobs.FifoRequirement_iff :
  ∀ {payload : Type} (scheduled executed : List payload),
    Whatwg.Ecma262.Jobs.FifoRequirement scheduled executed ↔
      List.IsPrefix executed scheduled)

#check (@Whatwg.Ecma262.Jobs.run_zero :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload),
    Whatwg.Ecma262.Jobs.run 0 q = ([], q))

#check (@Whatwg.Ecma262.Jobs.run_nil :
  ∀ {payload : Type} (fuel : Nat),
    Whatwg.Ecma262.Jobs.run fuel
        (Whatwg.Ecma262.Jobs.Queue.mk ([] : List payload)) =
      ([], Whatwg.Ecma262.Jobs.Queue.mk []))

/-! Mask **M2**, confirmed by the Q3b fidelity addendum, 2026-09-07
(WS-PROM-CE-037). The statement is unchanged and stays frozen. §7 of the base
packet enumerates twelve M2 theorems and does not list this one, but its rule
does: the statement observes that the *oldest* job is the one delivered, which
is an order over jobs. `Whatwg/Ecma262/Jobs.lean`'s docstring already says
"Mask M2", so the divergence is in §7's table and not in the tree; the addendum
amends that table to thirteen. `run_zero`, `run_nil` and `run_split` sit under
the same block heading and remain M1, as their own docstrings say. -/
#check (@Whatwg.Ecma262.Jobs.run_cons :
  ∀ {payload : Type} (fuel : Nat) (job : payload) (rest : List payload),
    Whatwg.Ecma262.Jobs.run (fuel + 1) (Whatwg.Ecma262.Jobs.Queue.mk (job :: rest)) =
      (job :: (Whatwg.Ecma262.Jobs.run fuel (Whatwg.Ecma262.Jobs.Queue.mk rest)).1,
        (Whatwg.Ecma262.Jobs.run fuel (Whatwg.Ecma262.Jobs.Queue.mk rest)).2))

#check (@Whatwg.Ecma262.Jobs.run_split :
  ∀ {payload : Type} (fuel : Nat) (q : Whatwg.Ecma262.Jobs.Queue payload),
    (Whatwg.Ecma262.Jobs.run fuel q).1 ++ (Whatwg.Ecma262.Jobs.run fuel q).2.pending =
      q.pending)

/-! The realizer theorem. Mask M2. -/
#check (@Whatwg.Ecma262.Jobs.run_fifo :
  ∀ {payload : Type} (fuel : Nat) (q : Whatwg.Ecma262.Jobs.Queue payload),
    Whatwg.Ecma262.Jobs.FifoRequirement q.pending (Whatwg.Ecma262.Jobs.run fuel q).1)

/-! The realizer still satisfies the requirement when further jobs are
scheduled before the run. Mask M2. -/
#check (@Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob_order :
  ∀ {payload : Type} (fuel : Nat) (q : Whatwg.Ecma262.Jobs.Queue payload)
    (later : List payload),
    Whatwg.Ecma262.Jobs.FifoRequirement (q.pending ++ later)
      (Whatwg.Ecma262.Jobs.run fuel (Whatwg.Ecma262.Jobs.Queue.enqueueAll q later)).1)

#check (@Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob_eq :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload) (job : payload),
    Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob q job =
      Whatwg.Ecma262.Jobs.Queue.enqueue q job)

#check (@Whatwg.Ecma262.Jobs.newReactionJob_eq :
  ∀ {arg : Type} (reaction : Nat) (argument : arg),
    Whatwg.Ecma262.Jobs.newReactionJob reaction argument =
      Whatwg.Ecma262.Jobs.ReactionJob.mk reaction argument)
