import Whatwg.Ecma262

/-!
Breaker-owned Q3b battery for `requirement.jobs.3`, the run-to-completion
requirement the base packet claims in the `semantics` edge and realizes
nowhere.
Addendum: `test/contracts/promise-first-packet-q3b.contract.md`.
Base packet: `test/contracts/promise-first-packet.contract.md`.
Graph: `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`, "Q3b addendum".
Attack: `test/counterexamples/promise/ATTACKS.md`, WS-PROM-CE-028.

Finding F5 of ruling R-P20: `requirement.jobs.3` (626357..626479, digest
`3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378`) — "Once
evaluation of a Job starts, it must run to completion before evaluation of any
other Job starts in an agent" — is named in the `semantics` edge's close-on set
and has no declaration and no discharge-by-typing statement. `Jobs.Active.job`
is produced by no operation and `Jobs.run` never consults the activation, so
the requirement is not merely unproved: nothing in the model can make it false,
which is the shape a vacuous discharge takes.

**Recommendation, stated in full in §5 of the addendum: the `Active`-threaded
step, not discharge by typing.** `startJob` is the missing producer of
`Active.job`; `RunToCompletion` is the DB-05 specification half;
`run_to_completion` is the realizer theorem; and `run_to_completion_nonvacuous`
is the receipt that the specification bites, because the activation `startJob`
produces is one in which `RunCondition` fails. The typing statement is kept as
well, as `run_one_job_per_step`, and `startJob_run_agree` is the receipt that
threading the activation changes nothing about the FIFO realizer, so
`Jobs.run_fifo`, `Jobs.run_split` and both Streams `tick_job_fifo` corollaries
stand unchanged.

Byte spans are 0-based, ends exclusive, into `vendor/ecma262-0248456c/spec.html`
(SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`).
Row ids are those of `generated/ecma262-census.tsv`; citing one anchors a
declaration and moves no coverage state.

Masks (DB-04), under §7's rule: a law whose statement observes the order in
which jobs are delivered is **M2**; a law that observes only an activation, a
branch or a terminal result is **M1**.

Every ascription names an inventory row with its reuse mode or a gap id
(R-P12). `G-08` is the gap; `E-47` (`Writable.Control.react`, keep) is the
Streams marker that is *not* re-stated here, and `E-51` (`Transform.runJob`,
generalize) is the Streams row whose general "run one job" step this is.

The builder must not change a statement in this file.
-/

set_option autoImplicit false

/-! ## The producer `Active.job` lacked

`requirement.jobs.1` (625769..626250, digest
`c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2`) says when a
job may start; `requirement.jobs.2` (626257..626350, digest
`dec0ab05daf30a7def2efe98018bbdf58750e2f762313b2b50d8184b00720ec5`) says only
one may be evaluating. The base packet states both as `RunCondition` and
`step_blocked`, over an activation nothing ever moves. `startJob` moves it:
it dequeues the oldest job **and** enters `Active.job`, and `completeJob` is
the only way back to a checkpoint. `G-08`; `E-51` (generalize). -/

#check (@Whatwg.Ecma262.Jobs.startJob :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Active → Whatwg.Ecma262.Jobs.Queue payload →
    Nat → Option (payload × Whatwg.Ecma262.Jobs.Active × Whatwg.Ecma262.Jobs.Queue payload))

#check (@Whatwg.Ecma262.Jobs.completeJob :
  Whatwg.Ecma262.Jobs.Active → Whatwg.Ecma262.Jobs.Active)

/-! `requirement.jobs.3` as the DB-05 specification half, in the shape R-P5
already requires for `hook.hostenqueuepromisejob`: while a job is the agent's
activation, no job starts. `G-08`. -/
#check (@Whatwg.Ecma262.Jobs.RunToCompletion :
  ∀ {payload : Type}, Whatwg.Ecma262.Jobs.Active → Prop)

/-! ## The laws -/

/-! Mask M2: the statement observes which job leaves the queue. `startJob` at a
checkpoint is `Queue.dequeue` with the activation threaded through it. -/
#check (@Whatwg.Ecma262.Jobs.startJob_checkpoint :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload) (serial : Nat),
    Whatwg.Ecma262.Jobs.startJob Whatwg.Ecma262.Jobs.Active.checkpoint q serial =
      (Whatwg.Ecma262.Jobs.Queue.dequeue q).map
        (fun p => (p.1, Whatwg.Ecma262.Jobs.Active.job serial, p.2)))

/-! Mask M2: the oldest job is the one that starts, which is `requirement.jobs.1`
composed with `requirement.hostenqueuepromisejob.3` (634739..634841). -/
#check (@Whatwg.Ecma262.Jobs.startJob_queue :
  ∀ {payload : Type} (job : payload) (rest : List payload) (serial : Nat),
    Whatwg.Ecma262.Jobs.startJob Whatwg.Ecma262.Jobs.Active.checkpoint
        (Whatwg.Ecma262.Jobs.Queue.mk (job :: rest)) serial =
      some (job, Whatwg.Ecma262.Jobs.Active.job serial,
        Whatwg.Ecma262.Jobs.Queue.mk rest))

/-! Mask M1: `requirement.jobs.1` and `requirement.jobs.2`. No job starts in
any activation but a checkpoint — the same content as `step_blocked`, now for
the operation that actually enters a job. -/
#check (@Whatwg.Ecma262.Jobs.startJob_blocked :
  ∀ {payload : Type} (active : Whatwg.Ecma262.Jobs.Active)
    (q : Whatwg.Ecma262.Jobs.Queue payload) (serial : Nat),
    active ≠ Whatwg.Ecma262.Jobs.Active.checkpoint →
      Whatwg.Ecma262.Jobs.startJob active q serial = none)

/-! Mask M1: **the producer**. Starting a job leaves the agent in
`Active.job`, so that constructor is no longer reachable by nothing. -/
#check (@Whatwg.Ecma262.Jobs.startJob_active :
  ∀ {payload : Type} (active : Whatwg.Ecma262.Jobs.Active)
    (q : Whatwg.Ecma262.Jobs.Queue payload) (serial : Nat)
    (res : payload × Whatwg.Ecma262.Jobs.Active × Whatwg.Ecma262.Jobs.Queue payload),
    Whatwg.Ecma262.Jobs.startJob active q serial = some res →
      res.2.1 = Whatwg.Ecma262.Jobs.Active.job serial)

/-! Mask M1: completion, and the only route back to a checkpoint. -/
#check (@Whatwg.Ecma262.Jobs.completeJob_job :
  ∀ (id : Nat),
    Whatwg.Ecma262.Jobs.completeJob (Whatwg.Ecma262.Jobs.Active.job id) =
      Whatwg.Ecma262.Jobs.Active.checkpoint)

/-! Mask M1: completing when no job is running changes nothing, so a script or
intrinsic activation cannot be laundered into a checkpoint. -/
#check (@Whatwg.Ecma262.Jobs.completeJob_other :
  ∀ (active : Whatwg.Ecma262.Jobs.Active),
    (∀ id : Nat, active ≠ Whatwg.Ecma262.Jobs.Active.job id) →
      Whatwg.Ecma262.Jobs.completeJob active = active)

/-! Mask M1: the specification unfolded, so the reader can check what is being
claimed without reading the definition. -/
#check (@Whatwg.Ecma262.Jobs.RunToCompletion_iff :
  ∀ {payload : Type} (active : Whatwg.Ecma262.Jobs.Active),
    Whatwg.Ecma262.Jobs.RunToCompletion (payload := payload) active ↔
      ((∃ id : Nat, active = Whatwg.Ecma262.Jobs.Active.job id) →
        ∀ q : Whatwg.Ecma262.Jobs.Queue payload,
          Whatwg.Ecma262.Jobs.step active q = none))

/-! Mask M1: **the realizer theorem for `requirement.jobs.3`**. Once evaluation
of a job has started — that is, once the agent's activation is `Active.job` —
no job starts, in any queue and at any payload, until `completeJob` returns the
agent to a checkpoint. `G-08`. -/
#check (@Whatwg.Ecma262.Jobs.run_to_completion :
  ∀ {payload : Type} (active : Whatwg.Ecma262.Jobs.Active),
    Whatwg.Ecma262.Jobs.RunToCompletion (payload := payload) active)

/-! Mask M1: the receipt that the theorem above is not vacuous. The activation
`startJob` produces is one in which `RunCondition` fails, so the requirement
constrains a state the model can actually reach — which is exactly what the
base packet could not say, because nothing produced `Active.job`. -/
#check (@Whatwg.Ecma262.Jobs.run_to_completion_nonvacuous :
  ∀ {payload : Type} (job : payload) (rest : List payload) (serial : Nat),
    ∃ res : payload × Whatwg.Ecma262.Jobs.Active × Whatwg.Ecma262.Jobs.Queue payload,
      Whatwg.Ecma262.Jobs.startJob Whatwg.Ecma262.Jobs.Active.checkpoint
          (Whatwg.Ecma262.Jobs.Queue.mk (job :: rest)) serial = some res ∧
        res.2.1 = Whatwg.Ecma262.Jobs.Active.job serial ∧
        ¬ Whatwg.Ecma262.Jobs.RunCondition res.2.1)

/-! Mask M2: the typing half of the discharge, stated as §5 of the addendum
requires it to be stated either way. `run` delivers exactly the oldest job and
then continues on the rest: there is no point at which a second job's
evaluation could begin inside the first, because `run` has one recursive call
and it is on the tail. Composition is `run_split`, which the base packet
already froze. -/
#check (@Whatwg.Ecma262.Jobs.run_one_job_per_step :
  ∀ {payload : Type} (fuel : Nat) (job : payload) (rest : List payload),
    (Whatwg.Ecma262.Jobs.run (fuel + 1)
        (Whatwg.Ecma262.Jobs.Queue.mk (job :: rest))).1 =
      job :: (Whatwg.Ecma262.Jobs.run fuel (Whatwg.Ecma262.Jobs.Queue.mk rest)).1)

/-! Mask M2: threading the activation is conservative. Forgetting the
activation from `startJob` at a checkpoint gives `Queue.dequeue` back exactly,
so `Jobs.run_fifo`, `Jobs.run_split`, `Jobs.hostEnqueuePromiseJob_order`,
`Writable.tick_job_fifo` and `Transform.tick_job_fifo` keep their statements
and their proofs. This is the receipt that F5's repair is additive. -/
#check (@Whatwg.Ecma262.Jobs.startJob_run_agree :
  ∀ {payload : Type} (q : Whatwg.Ecma262.Jobs.Queue payload) (serial : Nat),
    (Whatwg.Ecma262.Jobs.startJob Whatwg.Ecma262.Jobs.Active.checkpoint q serial).map
        (fun p => (p.1, p.2.2)) =
      Whatwg.Ecma262.Jobs.Queue.dequeue q)
