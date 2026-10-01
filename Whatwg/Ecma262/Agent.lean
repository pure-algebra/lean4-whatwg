import Whatwg.Ecma262.Promise

/-!
# The ECMAScript agent

Owner: promise slice Q5 (ruling R-W3), graph `PROMISE-PG-AGENT`
(`docs/PROMISE-AGENT-DAG.md`), at the surface
`test/contracts/promise-agent-q5.contract.md` freezes (ruling R-W13). This
module is builder slice B1; its battery is
`WhatwgTest/Ecma262/AgentContract.lean`.

Modelled here: one agent's promise and job state as a first-order record,
anchored by `clause.jobs` (JOBS, 624525..636548, digest
`871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf`) and
`clause.properties-of-promise-instances` (PINST, 2744135..2746691, digest
`f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d`), and one
total step function over nine first-order operations (DB-02). The record
*contains* the landed `Promise.Table`, `Promise.Reactions` and reaction-job
`Jobs.Queue` by value, and adds what the store-level operations had nowhere to
keep: the stored resolving functions, whose shared one-shot marker is state
(`G-03`; debts D17 and D46); the records a settled `PerformPromiseThen`
branch hands to its caller (`held`, Q3b finding F2); the activation with the
job under evaluation (`G-08` remainder); the settlement trace (finding F6,
with the producer debt D20 lacked); and the function cursor. Three cursors
stay (`table.next`, `reactions.next`, `nextFunction`), and a job's serial is
its reaction identity, so there is no fourth supply (`WS-PROM-CE-046`).

Relation to the landed store-level operations: each operation here calls the
landed one and adds only the agent's bookkeeping; nothing landed is copied or
replaced. `newPromise` is `newPromiseCapability` with
`createResolvingFunctions` stored; `settle` is `Table.settleAndTrigger`
beside `Table.settleTraced`; `perform` is `performPromiseThen`;
`markHandled` is `Table.markHandled`; `startJob` is `Jobs.startJob` at the
job's reaction identity; `finishJob` is `reactionHandlerResult` routed through
the stored functions, then `Jobs.completeJob`. Section 7 states each relation
as a theorem whose right side is the landed operation. Debt D46 (Web IDL
"react" followed by "resolve" enqueues no job, because
`WebIdl.Promise.resolve` is `Table.settle`) is repaired additively: `resolve`
and `reject` call the capability's stored functions, which settle and trigger
(`react_resolve_enqueues`), and the frozen `WebIdl.Promise.resolve` and
`reject` keep their statements as the table views (`resolve_table`,
`reject_table`).

Not modelled, with gap ids: thenable adoption and
`NewPromiseResolveThenableJob` (`G-05`), with `IsPromise` and the value
universe (`G-04`), so `resolve` takes a plain value, never looks up `then`
and has no self-resolution branch, and `WF.resolvedSettled` holds only while
adoption stays out (R-W3); the rejection tracker,
`hook.host-promise-rejection-tracker` (the `G-02` remainder), so the handled
bit is written by `perform` and `markHandled` and read by nothing; job
callbacks (the `G-07` remainder): no realm, no Job Abstract Closure carrier,
no `HostMakeJobCallback` or `HostCallJobCallback`, a handler is a first-order
descriptor and its completion is the host's decision on `finishJob` (DB-02);
the Completion carrier beyond `Except` (`G-10`); and the binding layer that
converts IDL values. `held` never shrinks, and `finishJob` leaves a reaction's
phase at `.queued`; the contract's claim scope names both.

`Minted` and `WF` are defined here, with `WF.get_lt`. Every other lemma about
them, the world order `Le`, the handler-adequacy theorems and the lifted laws
are slice B2's `Whatwg/Ecma262/AgentLaws.lean`.

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2". For this layer a
statement is DB-04 M2 when it observes the order of the settlement trace or of
the job queue, and DB-04 M1 when it observes a cell value, a branch, a table
shape, an answer or a terminal agent. No declaration here spells a mask.

Layering (DB-11): this module imports `Whatwg.Ecma262.Promise`, and through it
`Whatwg.Ecma262.Jobs`, and nothing else: no `Effects` module and no
`Whatwg.Infra` module (R-W3). Every census row cited here anchors a
declaration and is never a numerator; no coverage state moves.
-/

namespace Whatwg.Ecma262.Agent

/-! ## 1. The instance set

Ruling R-W3 (the design's decision 2, option a), frozen by the battery's
first section. `Promise.Reaction` and `Promise.Reactions` gain a global
`DecidableEq` conditional on `body`, and `Promise.Reactions`,
`Promise.ResolvingFunctions` and `Jobs.Active` gain `Repr`, through the four
`deriving instance` commands below. This supersedes inventory row `E-29`'s
sentence that the general reaction record "must not gain one silently";
`Transform.State` stays `Repr`-only because its own `deriving` clause is
unchanged. `DecidableEq (Except ε α)` is scoped to this namespace and never
global; the instances `Agent` and `Op` derive use it inside the namespace and
take no `Except` instance argument. -/

/-- `DecidableEq (Except ε α)`, a **scoped** instance of the namespace
`Whatwg.Ecma262.Agent` (ruling R-W3). Core declares none at this toolchain and
Batteries declares a global one, so a global instance here would be a second
one for any consumer that imports both (lean4-effect4 requires Batteries
through `aesop`). Outside the scope it does not synthesize; the battery pins
both directions. Helper of the instance set; no census row. -/
scoped instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error x, .error y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok x, .ok y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error _, .ok _ => isFalse (fun e => nomatch e)
  | .ok _, .error _ => isFalse (fun e => nomatch e)

deriving instance DecidableEq for Promise.Reaction
deriving instance DecidableEq, Repr for Promise.Reactions
deriving instance Repr for Promise.ResolvingFunctions
deriving instance Repr for Jobs.Active

/-! ## 2. The record -/

/-- `op.newpromisereactionjob` (REACTJOB, 2702885..2705591) as the landed
capture record `Jobs.ReactionJob`, at the one payload every landed operation
writes (ruling R-W3): the reaction identity, which is also the job's serial,
and the argument, whose `ok`/`error` tag is the `~fulfill~`/`~reject~` that
`TriggerPromiseReactions` and `PerformPromiseThen` put on it. View; an
`abbrev`, so instance search sees `Jobs.ReactionJob (Except reason value)`. -/
abbrev Job (value reason : Type) : Type := Jobs.ReactionJob (Except reason value)

/-- `clause.jobs` (JOBS, 624525..636548) and
`clause.properties-of-promise-instances` (PINST, 2744135..2746691): one
agent's promise and job state, the canonical carrier of `PROMISE-PG-AGENT`.
The three landed stores are contained by value and replaced by nothing
(ruling R-W3); the other six fields are what the store-level operations had
nowhere to keep. Three cursors (`table.next`, `reactions.next`,
`nextFunction`), and a job's serial is its reaction identity. Every type is
in `Type`; `DecidableEq` and `Repr` are derived conditionally on the three
parameters. `Agent.empty` is the agent before any promise. -/
structure Agent (value reason body : Type) where
  /-- The landed promise table: `[[PromiseState]]`, `[[PromiseResult]]` and
  `[[PromiseIsHandled]]` of every allocated identity, and the allocation
  cursor. -/
  table : Promise.Table value reason
  /-- The landed `[[PromiseFulfillReactions]]` and
  `[[PromiseRejectReactions]]` of every promise, and the shared registration
  cursor. -/
  reactions : Promise.Reactions body
  /-- The PromiseReaction Records a settled `PerformPromiseThen` branch built
  and handed to the job it enqueued (THEN steps 10 and 11, Q3b finding F2):
  no list holds them, so the agent does, for `reactionOf`. Never shrinks. -/
  held : List (Promise.Reaction body)
  /-- The landed reaction-job queue that `HostEnqueuePromiseJob` appends to,
  oldest first (`hook.hostenqueuepromisejob`). -/
  queue : Jobs.Queue (Job value reason)
  /-- The resolving functions of every capability `newPromise` minted
  (`op.createresolvingfunctions`); their shared one-shot marker is state here
  (`G-03`; debts D17 and D46). -/
  functions : List Promise.ResolvingFunctions
  /-- The function cursor, the landed `functionSeed` of the next capability;
  each capability consumes two identities. -/
  nextFunction : Nat
  /-- The landed activation: a checkpoint, a script, an intrinsic, or the job
  of a serial (`requirement.jobs.1`). -/
  active : Jobs.Active
  /-- The job under evaluation; `Jobs.Active.job` carries its serial only. -/
  running : Option (Job value reason)
  /-- The landed settlement trace (Q3b finding F6), oldest first; `settle` is
  its producer, which debt D20 lacked. -/
  settlements : Promise.SettlementTrace value reason
  deriving DecidableEq, Repr

/-- The agent before any promise exists: every store empty, every cursor at
zero, no job running, at a checkpoint. Helper; no census row. -/
def empty {value reason body : Type} : Agent value reason body :=
  ⟨Promise.Table.empty, Promise.Reactions.empty, [], Jobs.Queue.empty, [], 0,
    Jobs.Active.checkpoint, none, []⟩

/-! ## 3. The operations

Each operation is total. A disabled one leaves the agent unchanged (R-W3),
which DB-07 reads as a live frontier, never a failure; section 5 fixes every
branch by an equation. -/

/-- `op.newpromisecapability` (NEWCAP, 2696238..2698770, digest
`9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9`) at the
intrinsic `%Promise%`, with `op.createresolvingfunctions` (RESOLVING,
2692679..2695411, digest
`8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944`): allocate a
pending promise through the landed `newPromiseCapability`, store its two
resolving functions at the function cursor with the one-shot marker clear, and
answer the capability. Canonical operation; always enabled. -/
def newPromise {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body × Promise.Capability :=
  ({ a with
      table := (Promise.newPromiseCapability a.table a.nextFunction).1,
      functions := a.functions ++
        [Promise.createResolvingFunctions a.table.next a.nextFunction],
      nextFunction := a.nextFunction + 2 },
    (Promise.newPromiseCapability a.table a.nextFunction).2)

/-- `op.fulfillpromise` (FULFILL, 2695419..2696230) and `op.rejectpromise`
(REJECT, 2699323..2700252) with `op.triggerpromisereactions` (TRIGGER,
2700260..2701212): the landed `Table.settleAndTrigger` on the three stores and
the landed `Table.settleTraced` on the trace. Decision 7's guard stands for
the specifications' assertion that the promise is pending: a non-pending
settle changes none of the four. REJECT step 6, `HostPromiseRejectionTracker`,
is the `G-02` remainder and is not performed. Canonical operation, reached
through `callFunctions`. -/
def settle {value reason body : Type} (a : Agent value reason body) (promise : Nat)
    (result : Except reason value) : Agent value reason body :=
  { a with
    table := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).1,
    reactions := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.1,
    queue := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.2,
    settlements := (Promise.Table.settleTraced a.table a.settlements promise result).2 }

/-- `op.createresolvingfunctions` (RESOLVING, 2692679..2695411), the resolve
and reject steps 1 to 3 with the settle they lead to: call the stored
resolving function `pick` selects. A function this agent never stored is inert
(`WS-PROM-CE-041`), and so is one whose shared one-shot marker is set; on a
fresh one the marker is set on every record `pick` selects and the function's
own promise is settled and triggered. Canonical operation. -/
def callFunctions {value reason body : Type} (a : Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value) :
    Agent value reason body :=
  match a.functions.find? pick with
  | none => a
  | some f =>
      if f.alreadyResolved then a
      else
        { settle a f.promise result with
          functions := a.functions.map (fun g =>
            if pick g then { g with alreadyResolved := true } else g) }

/-- `Call(cap.[[Resolve]], undefined, « v »)`: Web IDL `op.resolve`
(349216..349783) step 3, through the resolve steps of
`op.createresolvingfunctions` on their non-thenable branch, which performs
FulfillPromise. The stored function is the one whose `[[Resolve]]` identity
is the capability's. The IDL-to-ECMAScript conversion, the self-resolution
branch and thenable adoption are out (`G-04`, `G-05`). Canonical operation;
the repair of debt D46. -/
def resolve {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (v : value) : Agent value reason body :=
  callFunctions a (fun f => f.resolve == cap.resolve) (Except.ok v)

/-- `Call(cap.[[Reject]], undefined, « r »)`: Web IDL `op.reject`
(349785..350073), through the reject steps of `op.createresolvingfunctions`,
which perform RejectPromise. The stored function is the one whose `[[Reject]]`
identity is the capability's, and the marker it sets is the one `resolve`
reads (`WS-PROM-CE-042`). Canonical operation. -/
def reject {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (r : reason) : Agent value reason body :=
  callFunctions a (fun f => f.reject == cap.reject) (Except.error r)

/-- Web IDL `op.dfn-perform-steps-once-promise-is-settled` (REACT,
350075..352408) step 6, `NewPromiseCapability(%Promise%)`, performed only when
`derive` is set: the step's note admits callers that never use the returned
promise, and `derive = false` is that caller, for which `PerformPromiseThen`
receives no result capability. Canonical operation over `newPromise`. -/
def mintFor {value reason body : Type} (a : Agent value reason body) :
    Bool → Agent value reason body × Option Promise.Capability
  | true => ((newPromise a).1, some (newPromise a).2)
  | false => (a, none)

/-- `op.performpromisethen` (THEN, 2740635..2743669, digest
`ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce`) through the
landed `performPromiseThen`, with the result capability minted first by
`mintFor` (Web IDL REACT steps 6 to 8 when `derive` is set). Every branch
marks the promise handled (step 12); the pending branch appends one record to
each list (step 9); a settled branch enqueues one job and hands its record to
`held` (steps 10 and 11). The answer is the derived capability, if any, behind
`some`. A missing promise answers `none` and leaves the agent unchanged, with
no capability minted (`E-31`'s `Option`, where THEN asserts `IsPromise`). The
rejected branch's `HostPromiseRejectionTracker` call is the `G-02` remainder.
Canonical operation. -/
def perform {value reason body : Type} (a : Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool) :
    Agent value reason body × Option (Option Promise.Capability) :=
  match a.table.get promise with
  | none => (a, none)
  | some _ =>
      match Promise.performPromiseThen (mintFor a derive).1.table (mintFor a derive).1.reactions
          (mintFor a derive).1.queue promise onFulfilled onRejected (mintFor a derive).2 with
      | none => (a, none)
      | some res =>
          ({ (mintFor a derive).1 with
              table := res.1, reactions := res.2.1, queue := res.2.2.1,
              held := (mintFor a derive).1.held ++ res.2.2.2.1.toList },
            some (mintFor a derive).2)

/-- Web IDL `op.mark-a-promise-as-handled` (HANDLEDOP, 356060..356713): the
landed `Table.markHandled`; a missing promise leaves the table unchanged.
Canonical operation; always enabled. -/
def markHandled {value reason body : Type} (a : Agent value reason body) (promise : Nat) :
    Agent value reason body :=
  { a with table := Promise.Table.markHandled a.table promise }

/-- `record.promisereaction-records` (2690445..2692671): the record a job was
built from. A job carries the reaction identity, not the record (`E-44`), so
the record is found again: the held record of that identity if there is one,
otherwise the registered record in the list the argument's tag selects, which
is the list `TriggerPromiseReactions` took it from. A job reads only
`[[Handler]]`, `[[Capability]]` and `[[Type]]`, and no operation changes them
after the record is built, so finding the record later reads what REACTJOB
step 1 captured. View. -/
def reactionOf {value reason body : Type} (a : Agent value reason body)
    (job : Job value reason) : Option (Promise.Reaction body) :=
  match a.held.find? (fun r => r.id == job.reaction) with
  | some r => some r
  | none =>
      Promise.Reactions.get a.reactions
        (match job.argument with
          | .ok _ => Promise.ReactionType.fulfill
          | .error _ => Promise.ReactionType.reject) job.reaction

/-- `requirement.jobs.1` (RUNCOND, 625769..626250), `requirement.jobs.2`
(ONEJOB, 626257..626350) and `requirement.hostenqueuepromisejob.3` (ORDER,
634739..634841): at a checkpoint, where no execution context runs and the
stack is empty, the oldest queued job starts; its serial is its reaction
identity, and it becomes the running job. The answer is the job with its
record's handler descriptor, which the host needs to answer `finishJob`. At
any other activation, or on an empty queue, nothing starts and the agent is
unchanged. Canonical operation. -/
def startJob {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body × Option (Job value reason × Option body) :=
  match a.active, a.queue.pending with
  | .checkpoint, job :: rest =>
      ({ a with
          queue := Jobs.Queue.mk rest
          active := Jobs.Active.job job.reaction
          running := some job },
        some (job, (reactionOf a job).bind Promise.Reaction.handler))
  | _, _ => (a, none)

/-- `op.newpromisereactionjob` (REACTJOB, 2702885..2705591, digest
`3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b`) inner steps
4 to 9 and `requirement.jobs.3` (COMPLETE, 626357..626479): the running job
ends. `decision` is the host's answer for a non-empty handler (DB-02: the
handler is never run here), and `reactionHandlerResult` takes it, or the
argument for an empty handler. With a `[[Capability]]` its stored functions
settle its promise with that result (inner steps 8 and 9; debt D17); with
`[[Capability]]` *undefined*, or no record, nothing settles (inner step 6;
D18, `WS-PROM-CE-044`). Then the agent is at a checkpoint with no running job.
With no job running it is inert.

Two readings of the text, both frozen by `finishJob_capability` and
`finishJob_no_capability`. The stored function is found by the `[[Resolve]]`
identity for an abrupt result too, where inner step 8 calls `[[Reject]]`; one
record holds both functions and their shared marker, and for a capability this
agent minted, `WF`'s `functionsBelow` and `functionsNodup` make the record the
`[[Reject]]` identity finds the same one. Inner step 6's assertion that the
result is not abrupt is not checked, so an abrupt result there settles
nothing. Canonical operation. -/
def finishJob {value reason body : Type} (a : Agent value reason body)
    (decision : Except reason value) : Agent value reason body :=
  match a.active, a.running with
  | .job _, some job =>
      let settled : Agent value reason body :=
        match reactionOf a job with
        | none => a
        | some r =>
            match r.capability with
            | none => a
            | some cap =>
                callFunctions a (fun f => f.resolve == cap.resolve)
                  (Promise.reactionHandlerResult r job.argument decision)
      { settled with active := Jobs.completeJob a.active, running := none }
  | _, _ => a

/-- `requirement.jobs.1` (RUNCOND, 625769..626250) from the other side: script
evaluation starts at a checkpoint, and an execution context is then running,
so no job may start. Inert at any other activation. Canonical operation
(`G-08` remainder). -/
def enterScript {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body :=
  match a.active with
  | .checkpoint => { a with active := Jobs.Active.script }
  | _ => a

/-- `requirement.jobs.1` (RUNCOND, 625769..626250): script evaluation returns,
the execution context stack is empty again, and the agent is at a checkpoint.
Inert at any other activation. Canonical operation (`G-08` remainder). -/
def leaveScript {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body :=
  match a.active with
  | .script => { a with active := Jobs.Active.checkpoint }
  | _ => a

/-! ## 4. The alphabet, the answers and the step -/

/-- The canonical alphabet of the agent: nine first-order operations, every
argument data (DB-02), no Lean function and no handler body. `DecidableEq` and
`Repr` are derived conditionally on the three parameters. No census row; each
constructor's anchor is the operation it names. -/
inductive Op (value reason body : Type) where
  /-- Run `newPromise`; the answer is the capability. -/
  | newPromise
  /-- Run `resolve` through `capability`; the answer is `()`. -/
  | resolve (capability : Promise.Capability) (v : value)
  /-- Run `reject` through `capability`; the answer is `()`. -/
  | reject (capability : Promise.Capability) (r : reason)
  /-- Run `perform`; the answer is `none` for a missing promise and otherwise
  `some` of the derived capability, which is `none` unless `derive` is set. -/
  | perform (promise : Nat) (onFulfilled onRejected : Option body) (derive : Bool)
  /-- Run `markHandled`; the answer is `()`. -/
  | markHandled (promise : Nat)
  /-- Run `startJob`; the answer is the started job with its handler, if any
  job started. -/
  | startJob
  /-- Run `finishJob` with the host's decision; the answer is `()`. -/
  | finishJob (decision : Except reason value)
  /-- Run `enterScript`; the answer is `()`. -/
  | enterScript
  /-- Run `leaveScript`; the answer is `()`. -/
  | leaveScript
  deriving DecidableEq, Repr

/-- The answer each operation returns beside the next agent; the nine `step_*`
equations fix it, since each typechecks only when this reduces to the stated
type. Canonical alphabet. -/
def Op.Answer {value reason body : Type} : Op value reason body → Type
  | .newPromise => Promise.Capability
  | .resolve _ _ => Unit
  | .reject _ _ => Unit
  | .perform _ _ _ _ => Option (Option Promise.Capability)
  | .markHandled _ => Unit
  | .startJob => Option (Job value reason × Option body)
  | .finishJob _ => Unit
  | .enterScript => Unit
  | .leaveScript => Unit

/-- The one total transition: run the operation, enabled or not, and return
the next agent with the answer. A disabled operation leaves the agent unchanged
(R-W3). It emits no event: the settlement trace carries DB-04 M2's settlement
order, the queue carries job order, and the `startJob` answers of a run carry
start order. Canonical transition; no census row. -/
def step {value reason body : Type} (a : Agent value reason body) :
    (op : Op value reason body) → Agent value reason body × op.Answer
  | .newPromise => newPromise a
  | .resolve cap v => (resolve a cap v, ())
  | .reject cap r => (reject a cap r, ())
  | .perform p f r d => perform a p f r d
  | .markHandled p => (markHandled a p, ())
  | .startJob => startJob a
  | .finishJob d => (finishJob a d, ())
  | .enterScript => (enterScript a, ())
  | .leaveScript => (leaveScript a, ())

/-- The step runs `newPromise`, and its answer is a `Promise.Capability`. Step
equation (NEWCAP); DB-04 M1. -/
theorem step_newPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.newPromise = Agent.newPromise a := by
  intros; rfl

/-- The step runs `resolve`, and its answer is `()`. Step equation (RESOLVING,
Web IDL `op.resolve`); DB-04 M1. -/
theorem step_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value),
      Agent.step a (Agent.Op.resolve cap v) = (Agent.resolve a cap v, ()) := by
  intros; rfl

/-- The step runs `reject`, and its answer is `()`. Step equation (RESOLVING,
Web IDL `op.reject`); DB-04 M1. -/
theorem step_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason),
      Agent.step a (Agent.Op.reject cap r) = (Agent.reject a cap r, ()) := by
  intros; rfl

/-- The step runs `perform`, and its answer is an
`Option (Option Promise.Capability)`. Step equation (THEN); DB-04 M1. -/
theorem step_perform :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      Agent.step a (Agent.Op.perform promise onFulfilled onRejected derive) =
        Agent.perform a promise onFulfilled onRejected derive := by
  intros; rfl

/-- The step runs `markHandled`, and its answer is `()`. Step equation
(HANDLEDOP); DB-04 M1. -/
theorem step_markHandled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      Agent.step a (Agent.Op.markHandled promise) = (Agent.markHandled a promise, ()) := by
  intros; rfl

/-- The step runs `startJob`, and its answer is an optional job with its
handler. Step equation (RUNCOND, ONEJOB, ORDER); DB-04 M1. -/
theorem step_startJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.startJob = Agent.startJob a := by
  intros; rfl

/-- The step runs `finishJob`, and its answer is `()`. Step equation
(REACTJOB, COMPLETE); DB-04 M1. -/
theorem step_finishJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value),
      Agent.step a (Agent.Op.finishJob decision) = (Agent.finishJob a decision, ()) := by
  intros; rfl

/-- The step runs `enterScript`, and its answer is `()`. Step equation
(RUNCOND); DB-04 M1. -/
theorem step_enterScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.enterScript = (Agent.enterScript a, ()) := by
  intros; rfl

/-- The step runs `leaveScript`, and its answer is `()`. Step equation
(RUNCOND); DB-04 M1. -/
theorem step_leaveScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.leaveScript = (Agent.leaveScript a, ()) := by
  intros; rfl

/-! ## 5. Defining equations

Each operation's content, every disabled branch included. An equation whose
right side moves the queue or the settlement trace is DB-04 M2; every other one
is DB-04 M1. -/

/-- The empty agent, field by field. Defining equation; DB-04 M1. -/
theorem empty_eq :
    ∀ {value reason body : Type},
      (Agent.empty : Agent.Agent value reason body) =
        Agent.Agent.mk Promise.Table.empty Promise.Reactions.empty [] Jobs.Queue.empty [] 0
          Jobs.Active.checkpoint none [] := by
  intros; rfl

/-- `newPromise` allocates through the landed `newPromiseCapability`, stores
`createResolvingFunctions` at the function cursor and advances it by two.
Defining equation (NEWCAP, RESOLVING); DB-04 M1. -/
theorem newPromise_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.newPromise a =
        ({ a with
            table := (Promise.newPromiseCapability a.table a.nextFunction).1,
            functions := a.functions ++
              [Promise.createResolvingFunctions a.table.next a.nextFunction],
            nextFunction := a.nextFunction + 2 },
          (Promise.newPromiseCapability a.table a.nextFunction).2) := by
  intros; rfl

/-- `settle` is the landed settle-and-trigger on the three stores and the
landed traced settle on the trace. Defining equation (FULFILL, REJECT,
TRIGGER); DB-04 M2. -/
theorem settle_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (result : Except reason value),
      Agent.settle a promise result =
        { a with
          table := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).1,
          reactions :=
            (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.1,
          queue := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.2,
          settlements := (Promise.Table.settleTraced a.table a.settlements promise result).2 } := by
  intros; rfl

/-- A function this agent never stored is inert (`WS-PROM-CE-041`).
Defining equation of the disabled branch (RESOLVING); DB-04 M1. -/
theorem callFunctions_none :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value),
      a.functions.find? pick = none → Agent.callFunctions a pick result = a := by
  intro value reason body a pick result h
  unfold callFunctions
  rw [h]

/-- A function whose shared one-shot marker is set is inert (RESOLVING resolve
and reject steps 1). Defining equation of the disabled branch; DB-04 M1. -/
theorem callFunctions_fired :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value)
      (f : Promise.ResolvingFunctions),
      a.functions.find? pick = some f → f.alreadyResolved = true →
        Agent.callFunctions a pick result = a := by
  intro value reason body a pick result f h hr
  unfold callFunctions
  rw [h]
  dsimp only
  rw [if_pos hr]

/-- A fresh function sets the marker (RESOLVING steps 3) and settles and
triggers its own promise. Defining equation; DB-04 M2. -/
theorem callFunctions_fresh :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value)
      (f : Promise.ResolvingFunctions),
      a.functions.find? pick = some f → f.alreadyResolved = false →
        Agent.callFunctions a pick result =
          { Agent.settle a f.promise result with
            functions := a.functions.map (fun (g : Promise.ResolvingFunctions) =>
              if pick g then { g with alreadyResolved := true } else g) } := by
  intro value reason body a pick result f h hr
  unfold callFunctions
  rw [h]
  dsimp only
  rw [if_neg (by rw [hr]; exact Bool.false_ne_true)]

/-- `resolve` calls the stored function of the capability's `[[Resolve]]`
identity with a fulfilment. Defining equation (Web IDL `op.resolve`); DB-04
M1. -/
theorem resolve_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value),
      Agent.resolve a cap v =
        Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
          (Except.ok v) := by
  intros; rfl

/-- `reject` calls the stored function of the capability's `[[Reject]]`
identity with a rejection. Defining equation (Web IDL `op.reject`); DB-04
M1. -/
theorem reject_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason),
      Agent.reject a cap r =
        Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject)
          (Except.error r) := by
  intros; rfl

/-- With `derive` set, the result capability is `newPromise`'s. Defining
equation (REACT step 6); DB-04 M1. -/
theorem mintFor_true :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.mintFor a true = ((Agent.newPromise a).1, some (Agent.newPromise a).2) := by
  intros; rfl

/-- Without `derive`, nothing is minted. Defining equation; DB-04 M1. -/
theorem mintFor_false :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.mintFor a false = (a, none) := by
  intros; rfl

/-- Minting a derived capability allocates at the cursor and keeps every
earlier identity's state. -/
private theorem mintFor_get {value reason body : Type} (a : Agent value reason body)
    (derive : Bool) (p : Nat) (s : Promise.State value reason) :
    a.table.get p = some s → (mintFor a derive).1.table.get p = some s := by
  intro h
  cases derive with
  | false => exact h
  | true =>
      show Option.map Promise.Cell.state (Option.map Prod.snd (List.find? (fun e => e.1 == p)
        (a.table.entries ++ [(a.table.next, Promise.Cell.mk Promise.State.pending false)]))) =
          some s
      rw [List.find?_append]
      unfold Promise.Table.get Promise.Table.getCell at h
      cases hf : List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == p)
          a.table.entries with
      | none => rw [hf] at h; cases h
      | some e => rw [hf] at h; exact h

/-- A missing promise: `none`, the agent unchanged, nothing minted (`E-31`).
Defining equation of the disabled branch (THEN); DB-04 M1. -/
theorem perform_missing :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      a.table.get promise = none →
        Agent.perform a promise onFulfilled onRejected derive = (a, none) := by
  intro value reason body a promise onFulfilled onRejected derive h
  unfold perform
  rw [h]

/-- The pending branch (THEN step 9 and step 12): both records registered,
the promise marked handled, the queue and `held` unchanged. Defining equation;
DB-04 M1. -/
theorem perform_pending :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      a.table.get promise = some Promise.State.pending →
        Agent.perform a promise onFulfilled onRejected derive =
          ({ (Agent.mintFor a derive).1 with
              table := Promise.Table.markHandled (Agent.mintFor a derive).1.table promise,
              reactions := (Promise.Reactions.add a.reactions promise onFulfilled onRejected
                (Agent.mintFor a derive).2).1 },
            some (Agent.mintFor a derive).2) := by
  intro value reason body a promise onFulfilled onRejected derive h
  have h1 := mintFor_get a derive promise _ h
  unfold perform
  rw [h]
  dsimp only
  rw [Promise.performPromiseThen_pending _ _ _ _ _ _ _ h1]
  dsimp only
  cases derive <;> simp only [List.append_nil, Option.toList] <;> rfl

/-- The fulfilled branch (THEN step 10 and step 12): one fulfil job enqueued at
the next registration identity, its record held, no list appended to.
Defining equation; DB-04 M2. -/
theorem perform_fulfilled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (v : value) (onFulfilled onRejected : Option body) (derive : Bool),
      a.table.get promise = some (Promise.State.fulfilled v) →
        Agent.perform a promise onFulfilled onRejected derive =
          ({ (Agent.mintFor a derive).1 with
              table := Promise.Table.markHandled (Agent.mintFor a derive).1.table promise,
              reactions := (Promise.Reactions.mint a.reactions promise
                Promise.ReactionType.fulfill onFulfilled (Agent.mintFor a derive).2).1,
              queue := Jobs.Queue.enqueue a.queue
                (Jobs.ReactionJob.mk a.reactions.next (Except.ok v)),
              held := a.held ++ [(Promise.Reactions.mint a.reactions promise
                Promise.ReactionType.fulfill onFulfilled (Agent.mintFor a derive).2).2] },
            some (Agent.mintFor a derive).2) := by
  intro value reason body a promise v onFulfilled onRejected derive h
  have h1 := mintFor_get a derive promise _ h
  unfold perform
  rw [h]
  dsimp only
  rw [Promise.performPromiseThen_fulfilled _ _ _ _ _ _ _ _ h1]
  cases derive <;> rfl

/-- The rejected branch (THEN step 11 and step 12; its tracker call is `G-02`'s):
one reject job enqueued at the next registration identity, its record held.
Defining equation; DB-04 M2. -/
theorem perform_rejected :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (r : reason) (onFulfilled onRejected : Option body) (derive : Bool),
      a.table.get promise = some (Promise.State.rejected r) →
        Agent.perform a promise onFulfilled onRejected derive =
          ({ (Agent.mintFor a derive).1 with
              table := Promise.Table.markHandled (Agent.mintFor a derive).1.table promise,
              reactions := (Promise.Reactions.mint a.reactions promise
                Promise.ReactionType.reject onRejected (Agent.mintFor a derive).2).1,
              queue := Jobs.Queue.enqueue a.queue
                (Jobs.ReactionJob.mk a.reactions.next (Except.error r)),
              held := a.held ++ [(Promise.Reactions.mint a.reactions promise
                Promise.ReactionType.reject onRejected (Agent.mintFor a derive).2).2] },
            some (Agent.mintFor a derive).2) := by
  intro value reason body a promise r onFulfilled onRejected derive h
  have h1 := mintFor_get a derive promise _ h
  unfold perform
  rw [h]
  dsimp only
  rw [Promise.performPromiseThen_rejected _ _ _ _ _ _ _ _ h1]
  cases derive <;> rfl

/-- `markHandled` writes the landed `Table.markHandled` into the table and
nothing else. Defining equation (HANDLEDOP); DB-04 M1. -/
theorem markHandled_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      Agent.markHandled a promise =
        { a with table := Promise.Table.markHandled a.table promise } := by
  intros; rfl

/-- A held record of the job's identity is the job's record. Defining
equation; DB-04 M1. -/
theorem reactionOf_held :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (r : Promise.Reaction body),
      a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = some r →
        Agent.reactionOf a job = some r := by
  intro value reason body a job r h
  unfold reactionOf
  rw [h]

/-- Otherwise a fulfilment's record is on the fulfil list. Defining equation;
DB-04 M1. -/
theorem reactionOf_ok :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (v : value),
      a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = none →
        job.argument = Except.ok v →
        Agent.reactionOf a job =
          Promise.Reactions.get a.reactions Promise.ReactionType.fulfill job.reaction := by
  intro value reason body a job v h hv
  unfold reactionOf
  rw [h, hv]

/-- Otherwise a rejection's record is on the reject list. Defining equation;
DB-04 M1. -/
theorem reactionOf_error :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (r : reason),
      a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = none →
        job.argument = Except.error r →
        Agent.reactionOf a job =
          Promise.Reactions.get a.reactions Promise.ReactionType.reject job.reaction := by
  intro value reason body a job r h hv
  unfold reactionOf
  rw [h, hv]

/-- At a checkpoint the oldest job leaves the queue and runs, at the serial of
its reaction identity. Defining equation (RUNCOND, ONEJOB, ORDER); DB-04 M2. -/
theorem startJob_checkpoint :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
      a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
        Agent.startJob a =
          ({ a with
              queue := Jobs.Queue.mk rest,
              active := Jobs.Active.job job.reaction,
              running := some job },
            some (job, (Agent.reactionOf a job).bind Promise.Reaction.handler)) := by
  intro value reason body a job rest ha hq
  unfold startJob
  rw [ha, hq]

/-- An empty queue starts nothing (DB-07: a live frontier). Defining equation
of the disabled branch; DB-04 M1. -/
theorem startJob_empty :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.queue.pending = [] → Agent.startJob a = (a, none) := by
  intro value reason body a hq
  unfold startJob
  rw [hq]
  cases a.active <;> rfl

/-- Away from a checkpoint nothing starts (`requirement.jobs.1`,
`WS-PROM-CE-045`). Defining equation of the disabled branch; DB-04 M1. -/
theorem startJob_blocked :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active ≠ Jobs.Active.checkpoint → Agent.startJob a = (a, none) := by
  intro value reason body a h
  unfold startJob
  cases ha : a.active with
  | checkpoint => exact absurd ha h
  | script => rfl
  | intrinsic _ => rfl
  | job _ => rfl

/-- With no job running, `finishJob` is inert. Defining equation of the
disabled branch; DB-04 M1. -/
theorem finishJob_idle :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value),
      a.running = none → Agent.finishJob a decision = a := by
  intro value reason body a decision h
  unfold finishJob
  rw [h]
  cases a.active <;> rfl

/-- Away from a job activation, `finishJob` is inert. Defining equation of the
disabled branch; DB-04 M1. -/
theorem finishJob_not_job :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value),
      (∀ s : Nat, a.active ≠ Jobs.Active.job s) → Agent.finishJob a decision = a := by
  intro value reason body a decision h
  unfold finishJob
  cases ha : a.active with
  | job s => exact absurd ha (h s)
  | checkpoint => rfl
  | script => rfl
  | intrinsic _ => rfl

/-- A running job with no record settles nothing and returns to a checkpoint.
Defining equation (COMPLETE); DB-04 M1. -/
theorem finishJob_unknown :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason),
      a.active = Jobs.Active.job s → a.running = some job → Agent.reactionOf a job = none →
        Agent.finishJob a decision =
          { a with active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job ha hr hn
  unfold finishJob
  rw [ha, hr]
  dsimp only
  rw [hn]
  rfl

/-- With `[[Capability]]` *undefined* the job settles nothing and returns to a
checkpoint (REACTJOB inner step 6; D18, `WS-PROM-CE-044`). Defining equation;
DB-04 M1. -/
theorem finishJob_no_capability :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
      (r : Promise.Reaction body),
      a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = none →
        Agent.finishJob a decision =
          { a with active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job r ha hr hn hc
  unfold finishJob
  rw [ha, hr]
  dsimp only
  rw [hn]
  dsimp only
  rw [hc]
  rfl

/-- With a `[[Capability]]`, the handler's result goes through the
capability's stored functions, found by its `[[Resolve]]` identity, and the
agent returns to a checkpoint (REACTJOB inner steps 7 to 9, COMPLETE).
Defining equation; DB-04 M2. -/
theorem finishJob_capability :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
      (r : Promise.Reaction body) (cap : Promise.Capability),
      a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = some cap →
        Agent.finishJob a decision =
          { Agent.callFunctions a
              (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
              (Promise.reactionHandlerResult r job.argument decision) with
            active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job r cap ha hr hn hc
  unfold finishJob
  rw [ha, hr]
  dsimp only
  rw [hn]
  dsimp only
  rw [hc]
  rfl

/-- At a checkpoint, script evaluation starts. Defining equation (RUNCOND);
DB-04 M1. -/
theorem enterScript_checkpoint :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active = Jobs.Active.checkpoint →
        Agent.enterScript a = { a with active := Jobs.Active.script } := by
  intro value reason body a h
  unfold enterScript
  rw [h]

/-- Anywhere else, `enterScript` is inert. Defining equation of the disabled
branch; DB-04 M1. -/
theorem enterScript_other :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active ≠ Jobs.Active.checkpoint → Agent.enterScript a = a := by
  intro value reason body a h
  unfold enterScript
  cases ha : a.active with
  | checkpoint => exact absurd ha h
  | script => rfl
  | intrinsic _ => rfl
  | job _ => rfl

/-- In a script, script evaluation returns to a checkpoint. Defining equation
(RUNCOND); DB-04 M1. -/
theorem leaveScript_script :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active = Jobs.Active.script →
        Agent.leaveScript a = { a with active := Jobs.Active.checkpoint } := by
  intro value reason body a h
  unfold leaveScript
  rw [h]

/-- Anywhere else, `leaveScript` is inert. Defining equation of the disabled
branch; DB-04 M1. -/
theorem leaveScript_other :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active ≠ Jobs.Active.script → Agent.leaveScript a = a := by
  intro value reason body a h
  unfold leaveScript
  cases ha : a.active with
  | script => exact absurd ha h
  | checkpoint => rfl
  | intrinsic _ => rfl
  | job _ => rfl

/-! ## 6. `Minted` and the fourteen clauses of `WF`

Slice B1 defines both, because `resolve_table` below and the Web IDL
`resolve_view` of slice B3 are stated under `WF`; apart from `WF.get_lt`,
slice B2 proves every lemma about them, including that `Agent.empty` is well
formed and every operation keeps `WF`. -/

/-- `record.promisecapability-records` (CAPREC, 2687751..2690437): a
capability this agent minted, meaning some stored resolving-function record
carries its `[[Resolve]]`, `[[Reject]]` and `[[Promise]]`. Invariant helper
(debt D17); `Minted_iff` is its defining equation. -/
def Minted {value reason body : Type} (a : Agent value reason body) (cap : Promise.Capability) :
    Prop :=
  ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject = cap.reject ∧ f.promise = cap.promise

/-- The defining equation of `Minted`. Invariant helper (CAPREC); DB-04 M1. -/
theorem Minted_iff :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability),
      Agent.Minted a cap ↔
        ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject = cap.reject ∧
          f.promise = cap.promise := by
  intros; exact Iff.rfl

/-- The agent's invariant: identity and reference coherence over the
contained stores, in fourteen clauses, each frozen by its projection.
`WF.resolvedSettled` holds only while thenable adoption (`G-05`) is out and
must be weakened when it enters (R-W3); `WF.settlementsCoherent` is debt D20's
coherence of trace and table. Invariant; no census row. -/
structure WF {value reason body : Type} (a : Agent value reason body) : Prop where
  /-- Promise identities are unique. `Table.mk` stays public, so a duplicate is
  ill formed rather than unconstructible (`WS-PROM-CE-043`). -/
  tableNodup : (a.table.entries.map Prod.fst).Nodup
  /-- Every allocated identity is below the table cursor, so the cursor is
  fresh. -/
  tableBelow : ∀ e ∈ a.table.entries, e.1 < a.table.next
  /-- Each stored record's `[[Reject]]` identity follows its `[[Resolve]]`
  identity, below the function cursor, so the cursor is fresh. -/
  functionsBelow : ∀ f ∈ a.functions, f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction
  /-- Every stored function names an allocated promise. -/
  functionsAllocated : ∀ f ∈ a.functions, (a.table.getCell f.promise).isSome = true
  /-- A fired function's promise is settled; true only while `G-05` is out. -/
  resolvedSettled : ∀ f ∈ a.functions, f.alreadyResolved = true →
    Promise.Table.isPending a.table f.promise = false
  /-- Every registered or held reaction identity is below the registration
  cursor, so the cursor is fresh. -/
  reactionsBelow : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
    r.id < a.reactions.next
  /-- Every queued job's serial is a reaction identity already issued. -/
  queueBelow : ∀ j ∈ a.queue.pending, j.reaction < a.reactions.next
  /-- The two lists carry the same identities in the same order, the landed
  `Reactions.add_paired` shape. -/
  paired : a.reactions.fulfill.map Promise.Reaction.id = a.reactions.reject.map Promise.Reaction.id
  /-- `[[Resolve]]` identities are unique, so `find?` names one record; with
  `functionsBelow` the `[[Reject]]` identities are unique too. -/
  functionsNodup : (a.functions.map Promise.ResolvingFunctions.resolve).Nodup
  /-- Held and registered identities are disjoint and repeat within neither,
  so `reactionOf` names one record. -/
  heldDistinct : (a.held.map Promise.Reaction.id ++ a.reactions.fulfill.map Promise.Reaction.id).Nodup
  /-- Every queued job names a record. -/
  queuedKnown : ∀ j ∈ a.queue.pending, (Agent.reactionOf a j).isSome = true
  /-- The running job and the activation agree, in both directions. -/
  runningActive :
    (∀ j : Agent.Job value reason, a.running = some j →
        a.active = Jobs.Active.job j.reaction) ∧
      (∀ s : Nat, a.active = Jobs.Active.job s → a.running.isSome = true)
  /-- Every capability a stored reaction carries has its functions stored
  (debt D17). -/
  capabilityStored :
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      ∀ cap : Promise.Capability, r.capability = some cap → Agent.Minted a cap
  /-- Every trace entry is the table's settled state, and no identity is
  traced twice (debt D20). -/
  settlementsCoherent :
    (a.settlements.map Prod.fst).Nodup ∧
      (∀ (p : Nat) (v : value), (p, Except.ok v) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.fulfilled v)) ∧
      (∀ (p : Nat) (r : reason), (p, Except.error r) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.rejected r))

/-- An allocated identity is below the table cursor, so it is never the
identity the next allocation takes. Invariant lemma; DB-04 M1. -/
theorem WF.get_lt :
    ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
      ∀ {p : Nat} {s : Promise.State value reason},
        Promise.Table.get a.table p = some s → p < a.table.next := by
  intro value reason body a hw p s h
  unfold Promise.Table.get Promise.Table.getCell at h
  cases hf : a.table.entries.find? (fun e => e.1 == p) with
  | none => rw [hf] at h; cases h
  | some e =>
      have hmem := List.mem_of_find?_eq_some hf
      have hb : (e.1 == p) = true :=
        List.find?_some (p := fun (x : Nat × Promise.Cell value reason) => x.1 == p) hf
      have heq : e.1 = p := beq_iff_eq.mp hb
      rw [← heq]
      exact hw.tableBelow e hmem

/-! ## 7. Views onto the landed store-level operations

Each right side is the landed operation, not a copy. -/

/-- The table component of the landed `Table.settleAndTrigger` is
`Table.settle`, on both branches of its guard (FULFILL, REJECT). View; DB-04
M1. -/
theorem settleAndTrigger_table :
    ∀ {value reason body : Type} (t : Promise.Table value reason)
      (rs : Promise.Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
      (id : Nat) (result : Except reason value),
      (Promise.Table.settleAndTrigger t rs q id result).1 = Promise.Table.settle t id result := by
  intro value reason body t rs q id result
  unfold Promise.Table.settleAndTrigger Promise.Table.settle
  cases Promise.Table.isPending t id <;> rfl

/-- `settle` at a fulfilment is the landed `fulfillPromise` (FULFILL, TRIGGER)
on the three stores. View; DB-04 M2, since the triple carries the queue. -/
theorem settle_ok_fulfillPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (v : value),
      ((Agent.settle a promise (Except.ok v)).table,
          (Agent.settle a promise (Except.ok v)).reactions,
          (Agent.settle a promise (Except.ok v)).queue) =
        Promise.fulfillPromise a.table a.reactions a.queue promise v := by
  intros; rfl

/-- `settle` at a rejection is the landed `rejectPromise` (REJECT, TRIGGER) on
the three stores. View; DB-04 M2, since the triple carries the queue. -/
theorem settle_error_rejectPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (r : reason),
      ((Agent.settle a promise (Except.error r)).table,
          (Agent.settle a promise (Except.error r)).reactions,
          (Agent.settle a promise (Except.error r)).queue) =
        Promise.rejectPromise a.table a.reactions a.queue promise r := by
  intros; rfl

/-- The trace `settle` leaves is the landed `Table.settleTraced`'s, the
producer debt D20 lacked. View; DB-04 M2. -/
theorem settle_settlements :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (result : Except reason value),
      (Agent.settle a promise result).settlements =
        (Promise.Table.settleTraced a.table a.settlements promise result).2 := by
  intros; rfl

/-- The capability `newPromise` answers is the landed `newPromiseCapability`'s
at the function cursor (NEWCAP). View; DB-04 M1. -/
theorem newPromise_capability :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      (Agent.newPromise a).2 = (Promise.newPromiseCapability a.table a.nextFunction).2 := by
  intros; rfl

/-- The table `markHandled` leaves is the landed `Table.markHandled`'s
(HANDLEDOP). View; DB-04 M1. -/
theorem markHandled_table :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      (Agent.markHandled a promise).table = Promise.Table.markHandled a.table promise := by
  intros; rfl

/-- Marking any promise handled changes no promise state at any identity
(HANDLEDOP; the handled bit is read by nothing, `G-02`). View; DB-04 M1. -/
theorem markHandled_get :
    ∀ {value reason : Type} (t : Promise.Table value reason) (p q : Nat),
      Promise.Table.get (Promise.Table.markHandled t p) q = Promise.Table.get t q := by
  intro value reason t p q
  unfold Promise.Table.get Promise.Table.getCell Promise.Table.markHandled
  rw [List.find?_map]
  have hcomp : ((fun (e : Nat × Promise.Cell value reason) => e.1 == q) ∘
      (fun (e : Nat × Promise.Cell value reason) =>
        if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e)) =
      (fun (e : Nat × Promise.Cell value reason) => e.1 == q) := by
    funext e
    show ((if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).1 == q) = (e.1 == q)
    cases (e.1 == p) <;> rfl
  rw [hcomp]
  cases List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == q) t.entries with
  | none => rfl
  | some e =>
      show some (if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).2.state =
        some e.2.state
      cases (e.1 == p) <;> rfl

/-- At a checkpoint, the job `startJob` starts and the activation and queue it
leaves are the landed `Jobs.startJob`'s at the job's own reaction identity, so
the job serial and the reaction identity are one supply (RUNCOND, ORDER;
`WS-PROM-CE-046`). View; DB-04 M2, since it observes which job leaves the
queue. -/
theorem startJob_agree :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
      a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
        Jobs.startJob a.active a.queue job.reaction =
          some (job, (Agent.startJob a).1.active, (Agent.startJob a).1.queue) := by
  intro value reason body a job rest hact hq
  unfold startJob Jobs.startJob Jobs.Queue.dequeue
  rw [hact, hq]
  rfl

/-- **D46 re-described.** For a capability whose resolving function this agent
stored, under `WF`, `resolve` changes the table exactly as the landed
`Table.settle` does, which is what the frozen `WebIdl.Promise.resolve` is; a
function that already fired is covered by `WF.resolvedSettled`, where both
sides are the identity. Web IDL `op.resolve` (349216..349783) via
`op.createresolvingfunctions`. View; DB-04 M1. -/
theorem resolve_table :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value),
      Agent.WF a →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
          some f →
        f.promise = cap.promise →
        (Agent.resolve a cap v).table =
          Promise.Table.settle a.table cap.promise (Except.ok v) := by
  intro value reason body a cap f v hw hf hfp
  unfold resolve callFunctions
  rw [hf]
  dsimp only
  cases hr : f.alreadyResolved with
  | false =>
      rw [if_neg (by exact Bool.false_ne_true)]
      show (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise
        (Except.ok v)).1 = _
      rw [settleAndTrigger_table, hfp]
  | true =>
      rw [if_pos rfl]
      have hset := hw.resolvedSettled f (List.mem_of_find?_eq_some hf) hr
      rw [hfp] at hset
      exact (Promise.Table.settle_other a.table cap.promise (Except.ok v) (fun hp =>
        Bool.false_ne_true (hset.symm.trans ((Promise.Table.isPending_iff _ _).mpr hp)))).symm

/-- The same for `reject`, through the `[[Reject]]` identity and a rejection:
the frozen `WebIdl.Promise.reject` is the table view. Web IDL `op.reject`
(349785..350073). View; DB-04 M1. -/
theorem reject_table :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (r : reason),
      Agent.WF a →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) =
          some f →
        f.promise = cap.promise →
        (Agent.reject a cap r).table =
          Promise.Table.settle a.table cap.promise (Except.error r) := by
  intro value reason body a cap f r hw hf hfp
  unfold reject callFunctions
  rw [hf]
  dsimp only
  cases hr : f.alreadyResolved with
  | false =>
      rw [if_neg (by exact Bool.false_ne_true)]
      show (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise
        (Except.error r)).1 = _
      rw [settleAndTrigger_table, hfp]
  | true =>
      rw [if_pos rfl]
      have hset := hw.resolvedSettled f (List.mem_of_find?_eq_some hf) hr
      rw [hfp] at hset
      exact (Promise.Table.settle_other a.table cap.promise (Except.error r) (fun hp =>
        Bool.false_ne_true (hset.symm.trans ((Promise.Table.isPending_iff _ _).mpr hp)))).symm

/-! ## 8. D46: `react` followed by `resolve` enqueues the new reaction's job

`op.triggerpromisereactions` (TRIGGER, 2700260..2701212, digest
`ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839`) and
`op.performpromisethen` (THEN). Rows `WS-PROM-CE-040`; Web IDL's restatement
is slice B3's `WebIdl.Agent.react_resolve`. -/

/-- A registration on a promise joins the end of that promise's waiting fulfil
list (THEN step 9, read by TRIGGER). Law (D46); DB-04 M2. -/
theorem waitingOn_add_fulfill :
    ∀ {body : Type} (rs : Promise.Reactions body) (promise : Nat)
      (onFulfilled onRejected : Option body) (cap : Option Promise.Capability),
      Promise.Reactions.waitingOn (Promise.Reactions.add rs promise onFulfilled onRejected cap).1
          promise Promise.ReactionType.fulfill =
        Promise.Reactions.waitingOn rs promise Promise.ReactionType.fulfill ++
          [Promise.Reaction.mk rs.next promise Promise.ReactionType.fulfill onFulfilled cap
            Promise.ReactionPhase.waiting] := by
  intro body rs promise onFulfilled onRejected cap
  have hnew : (fun (r : Promise.Reaction body) =>
      r.promise == promise && r.phase == Promise.ReactionPhase.waiting)
      (Promise.Reaction.mk rs.next promise Promise.ReactionType.fulfill onFulfilled cap
        Promise.ReactionPhase.waiting) = true := by
    show (promise == promise && Promise.ReactionPhase.waiting == Promise.ReactionPhase.waiting) = true
    rw [show (promise == promise) = true from decide_eq_true rfl]
    rfl
  show List.filter _ (rs.fulfill ++ _) = _
  rw [List.filter_append, List.filter_cons_of_pos (p := fun (r : Promise.Reaction body) =>
      r.promise == promise && r.phase == Promise.ReactionPhase.waiting) hnew, List.filter_nil]
  rfl

/-- **D46.** Web IDL "react" (`perform` with a derived capability) followed by
"resolve", on a pending promise whose resolving functions are stored and
unfired: behind every job already queued, the jobs of the reactions already
waiting on that promise, in registration order, and then exactly the new
reaction's job. The store-level `WebIdl.Promise.resolve` enqueues none of them
(`WS-PROM-CE-040`). The hypothesis `cap.promise ≠ a.table.next` says the
derived promise is not the reacted one; `_wf` discharges it. Law (TRIGGER,
THEN); DB-04 M2. -/
theorem react_resolve_enqueues :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
      a.table.get cap.promise = some Promise.State.pending →
        cap.promise ≠ a.table.next →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
          some f →
        f.alreadyResolved = false → f.promise = cap.promise →
        (Agent.resolve (Agent.perform a cap.promise (some h) none true).1 cap v).queue.pending =
          a.queue.pending ++
            ((Promise.Reactions.waitingOn a.reactions cap.promise
                Promise.ReactionType.fulfill).map
              (fun (r : Promise.Reaction body) => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
            [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) := by
  intro value reason body a cap f h v hp hne hf hfr hfp
  have h1 : Promise.Table.get (newPromise a).1.table cap.promise = some Promise.State.pending := by
    show Option.map Promise.Cell.state
      (Promise.Table.getCell (Promise.Table.fresh a.table Promise.State.pending).1 cap.promise) = _
    rw [Promise.Table.fresh_old a.table _ cap.promise hne]
    exact hp
  have hperf : (perform a cap.promise (some h) none true).1 =
      { (newPromise a).1 with
        table := Promise.Table.markHandled (newPromise a).1.table cap.promise,
        reactions := (Promise.Reactions.add a.reactions cap.promise (some h) none
          (some (newPromise a).2)).1,
        queue := a.queue,
        held := a.held ++ [] } := by
    unfold perform
    rw [hp]
    show (match Promise.performPromiseThen (newPromise a).1.table (newPromise a).1.reactions
          (newPromise a).1.queue cap.promise (some h) none (some (newPromise a).2) with
        | none => (a, none)
        | some res =>
          ({ (newPromise a).1 with
              table := res.1, reactions := res.2.1, queue := res.2.2.1,
              held := (newPromise a).1.held ++ res.2.2.2.1.toList },
            some (some (newPromise a).2))).1 = _
    rw [Promise.performPromiseThen_pending _ _ _ _ _ _ _ h1]
    rfl
  have hpend : Promise.Table.get (Promise.Table.markHandled (newPromise a).1.table cap.promise)
      cap.promise = some Promise.State.pending := by
    rw [Promise.Table.markHandled_state]
    exact h1
  have hfind : ((newPromise a).1).functions.find?
        (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) = some f := by
    show (a.functions ++ [Promise.createResolvingFunctions a.table.next a.nextFunction]).find?
        (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) = some f
    rw [List.find?_append, hf]
    rfl
  rw [hperf]
  unfold resolve callFunctions
  rw [hfind]
  dsimp only
  rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)]
  show (Promise.Table.settleAndTrigger
      (Promise.Table.markHandled (newPromise a).1.table cap.promise)
      (Promise.Reactions.add a.reactions cap.promise (some h) none (some (newPromise a).2)).1
      a.queue f.promise (Except.ok v)).2.2.pending = _
  rw [hfp, Promise.Table.settleAndTrigger_pending _ _ _ _ _ hpend]
  show (Promise.triggerReactions _ cap.promise Promise.ReactionType.fulfill (Except.ok v)
      a.queue).2.pending = _
  rw [Promise.triggerReactions_order, waitingOn_add_fulfill, List.map_append]
  rfl

/-- **D46** under `WF`, which makes every allocated identity differ from the
next one (`WF.get_lt`). Law (TRIGGER, THEN); DB-04 M2. -/
theorem react_resolve_enqueues_wf :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
      Agent.WF a → a.table.get cap.promise = some Promise.State.pending →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
          some f →
        f.alreadyResolved = false → f.promise = cap.promise →
        (Agent.resolve (Agent.perform a cap.promise (some h) none true).1 cap v).queue.pending =
          a.queue.pending ++
            ((Promise.Reactions.waitingOn a.reactions cap.promise
                Promise.ReactionType.fulfill).map
              (fun (r : Promise.Reaction body) => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
            [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) := by
  intro value reason body a cap f h v hw hp hf hfr hfp
  exact react_resolve_enqueues a cap f h v hp (Nat.ne_of_lt (hw.get_lt hp)) hf hfr hfp

/-- **D46**, the FIFO position: with nothing yet waiting on the promise, the
queue gains exactly the new reaction's job, at its tail. Law (TRIGGER, THEN);
DB-04 M2. -/
theorem react_resolve_enqueues_exactly :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
      a.table.get cap.promise = some Promise.State.pending →
        cap.promise ≠ a.table.next →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
          some f →
        f.alreadyResolved = false → f.promise = cap.promise →
        Promise.Reactions.waitingOn a.reactions cap.promise Promise.ReactionType.fulfill = [] →
        (Agent.resolve (Agent.perform a cap.promise (some h) none true).1 cap v).queue.pending =
          a.queue.pending ++ [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)] := by
  intro value reason body a cap f h v hp hne hf hfr hfp hnone
  rw [react_resolve_enqueues a cap f h v hp hne hf hfr hfp, hnone]
  rfl

/-! ## 9. D17 and run to completion at the agent -/

/-- **D17.** The capability a running job's record carries is settled through
the functions this agent stored for it, exactly as `Table.settle` would with
the handler's result, and the agent returns to a checkpoint.
`op.newpromisereactionjob` (REACTJOB) inner steps 6 to 9 with COMPLETE. Law;
DB-04 M1. -/
theorem finishJob_settles_capability :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (s : Nat) (r : Promise.Reaction body)
      (cap : Promise.Capability) (f : Promise.ResolvingFunctions)
      (decision : Except reason value),
      a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = some cap →
        a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
          some f →
        f.alreadyResolved = false → f.promise = cap.promise →
        (Agent.finishJob a decision).table =
            Promise.Table.settle a.table cap.promise
              (Promise.reactionHandlerResult r job.argument decision) ∧
          (Agent.finishJob a decision).active = Jobs.Active.checkpoint := by
  intro value reason body a job s r cap f decision hact hrun hr hcap hf hfr hfp
  unfold finishJob
  rw [hact, hrun]
  dsimp only
  rw [hr]
  dsimp only
  rw [hcap]
  dsimp only
  unfold callFunctions
  rw [hf]
  dsimp only
  rw [if_neg (by rw [hfr]; exact Bool.false_ne_true)]
  refine ⟨?_, rfl⟩
  show (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise _).1 = _
  rw [settleAndTrigger_table, hfp]

/-- `requirement.jobs.3` (COMPLETE, 626357..626479, digest
`3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378`) at the
agent: while a job runs, no job starts, whatever is queued
(`WS-PROM-CE-045`). It lifts the landed `Jobs.run_to_completion`. Law;
DB-04 M1. -/
theorem startJob_running :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (s : Nat),
      a.active = Jobs.Active.job s → Agent.startJob a = (a, none) := by
  intro value reason body a s h
  unfold startJob
  rw [h]

end Whatwg.Ecma262.Agent
