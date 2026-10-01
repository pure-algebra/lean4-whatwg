import Whatwg.Ecma262

/-!
Breaker-owned Q5 battery for slice B2: the agent's invariant, its laws in
the handler-adequacy shape of the W9 design's §3.7, and the lifted laws of
its §3.5.

Packet: `test/contracts/promise-agent-q5.contract.md`.
Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`.
Attacks: `test/counterexamples/promise/ATTACKS.md`, section "Q5 agent
packet", rows WS-PROM-CE-040..047.

Every ascription names a declaration that does not exist at `b0d35e2`: this
module is red until builder slice B2 lands `Whatwg/Ecma262/AgentLaws.lean` and
imports it from `Whatwg/Ecma262.lean`. B2 depends on B1, which lands `WF`'s
definition and its fourteen clauses (ascribed in
`WhatwgTest/Ecma262/AgentContract.lean`); B2 lands every lemma about them. The
builder must not change a statement in this file.

The shape is lean4-effect4's at `b9d0d19f`, read in its source
(`src/Effect4/Laws/Program/Typed/Adequacy.lean`, `StoreImplements`): a
well-formedness predicate every operation keeps, a pre the request must
satisfy, "the handler steps, no frontier", and the answer in the post at a
later, well-formed state. That reading is not a claim about that repository.
`Agent.WF` reads as `StoreTyped`, `Agent.Le` as `World.leHost`, `Agent.Cert`
as `StoreCert`, `Agent.pre` and `Agent.post` as `storePre` and `storePost`,
and `Agent.Implements` as `StoreImplements`. No generic law is copied: the
program-level `run_adequate` over lean4-effect4's `Protocol` waits until that
module is in the `effects` package (R-W3).

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no Lean name here
spells a mask. Every law of this module is DB-04 M1 except `Le.trace`'s
prefix clause (DB-04 M2, the settlement order), `settle_trace`,
`runOps_fifo` and `runOps_fifoRequirement` (DB-04 M2, settlement and job
order), and the nine `*_implements` and `implements`, which carry DB-04 M2
through `Le`'s trace clause.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The world order

What a later agent keeps: an allocated cell stays allocated, a settled state
never changes, the handled bit never clears, the three cursors grow, every
stored function record survives, and the settlement trace is a prefix. The
eight clauses are frozen by their projections. -/

#check (@Whatwg.Ecma262.Agent.Le :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body → Prop)

#check (@Whatwg.Ecma262.Agent.Le.allocated :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    ∀ (p : Nat), (a.table.getCell p).isSome = true → (a'.table.getCell p).isSome = true)
#check (@Whatwg.Ecma262.Agent.Le.settled :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    ∀ (p : Nat) (s : Promise.State value reason), a.table.get p = some s →
      s ≠ Promise.State.pending → a'.table.get p = some s)
#check (@Whatwg.Ecma262.Agent.Le.handled :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    ∀ (p : Nat), (a.table.getCell p).map Promise.Cell.handled = some true →
      (a'.table.getCell p).map Promise.Cell.handled = some true)
#check (@Whatwg.Ecma262.Agent.Le.tableNext :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    a.table.next ≤ a'.table.next)
#check (@Whatwg.Ecma262.Agent.Le.reactionsNext :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    a.reactions.next ≤ a'.reactions.next)
#check (@Whatwg.Ecma262.Agent.Le.functionCursor :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    a.nextFunction ≤ a'.nextFunction)
#check (@Whatwg.Ecma262.Agent.Le.minted :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    ∀ f ∈ a.functions, ∃ g ∈ a'.functions,
      g.resolve = f.resolve ∧ g.reject = f.reject ∧ g.promise = f.promise)
#check (@Whatwg.Ecma262.Agent.Le.trace :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Le a a' →
    a.settlements <+: a'.settlements)

#check (@Whatwg.Ecma262.Agent.Le.refl :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body), Agent.Le a a)
#check (@Whatwg.Ecma262.Agent.Le.trans :
  ∀ {value reason body : Type} {a b c : Agent.Agent value reason body},
    Agent.Le a b → Agent.Le b c → Agent.Le a c)

/-! Every operation moves a well-formed agent up the order, enabled or not. -/
#check (@Whatwg.Ecma262.Agent.Le.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.WF a → Agent.Le a (Agent.step a op).1)

/-! ## 2. The invariant is kept

`WF.empty` and `WF.step` together make every agent `runOps` reaches from
`Agent.empty` well formed. `WF.step` holds for every operation, enabled or
disabled: a disabled operation leaves the agent unchanged. -/

#check (@Whatwg.Ecma262.Agent.WF.empty :
  ∀ {value reason body : Type}, Agent.WF (Agent.empty : Agent.Agent value reason body))
#check (@Whatwg.Ecma262.Agent.WF.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.WF a → Agent.WF (Agent.step a op).1)

/-! ## 3. The certificate, the pre and the post

`Cert` is `Unit`: the table is homogeneous in `value` and `reason`, so no
ghost certificate is needed. `pre` is the operation's enabledness, except
that `resolve` and `reject` admit a capability whose functions already fired
(the step is then inert and the post still holds, by `resolvedSettled`). The
posts are facts at the answering agent; the activation posts of `startJob`
and `finishJob` are true there only, and every other post is upward closed in
`Le`. The eighteen `pre_*` and `post_*` equations freeze the content. -/

#check (@Whatwg.Ecma262.Agent.Cert :
  ∀ {value reason body : Type}, Agent.Op value reason body → Type)
#check (@Whatwg.Ecma262.Agent.pre :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    (op : Agent.Op value reason body) → Agent.Cert op → Prop)
#check (@Whatwg.Ecma262.Agent.post :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    (op : Agent.Op value reason body) → Agent.Cert op → Agent.Op.Answer op → Prop)

/-- The certificate carries no information. -/
example : Agent.Cert (Agent.Op.newPromise : Agent.Op Unit Nat Nat) = Unit := rfl

#check (@Whatwg.Ecma262.Agent.pre_newPromise :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body)),
    Agent.pre a Agent.Op.newPromise c ↔ True)
#check (@Whatwg.Ecma262.Agent.pre_resolve :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value)
    (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)),
    Agent.pre a (Agent.Op.resolve cap v) c ↔ Agent.Minted a cap)
#check (@Whatwg.Ecma262.Agent.pre_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason)
    (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)),
    Agent.pre a (Agent.Op.reject cap r) c ↔ Agent.Minted a cap)
#check (@Whatwg.Ecma262.Agent.pre_perform :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool)
    (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body)),
    Agent.pre a (Agent.Op.perform promise onFulfilled onRejected derive) c ↔
      (a.table.get promise).isSome = true)
#check (@Whatwg.Ecma262.Agent.pre_markHandled :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body)),
    Agent.pre a (Agent.Op.markHandled promise) c ↔ (a.table.get promise).isSome = true)
#check (@Whatwg.Ecma262.Agent.pre_startJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body)),
    Agent.pre a Agent.Op.startJob c ↔
      a.active = Jobs.Active.checkpoint ∧ a.queue.pending ≠ [])
#check (@Whatwg.Ecma262.Agent.pre_finishJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value)
    (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)),
    Agent.pre a (Agent.Op.finishJob decision) c ↔ ∃ s : Nat, a.active = Jobs.Active.job s)
#check (@Whatwg.Ecma262.Agent.pre_enterScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)),
    Agent.pre a Agent.Op.enterScript c ↔ a.active = Jobs.Active.checkpoint)
#check (@Whatwg.Ecma262.Agent.pre_leaveScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)),
    Agent.pre a Agent.Op.leaveScript c ↔ a.active = Jobs.Active.script)

#check (@Whatwg.Ecma262.Agent.post_newPromise :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body))
    (cap : Promise.Capability),
    Agent.post a Agent.Op.newPromise c cap ↔
      Agent.Minted a cap ∧ a.table.get cap.promise = some Promise.State.pending)
#check (@Whatwg.Ecma262.Agent.post_resolve :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value)
    (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)) (ans : Unit),
    Agent.post a (Agent.Op.resolve cap v) c ans ↔
      ∃ s : Promise.State value reason, a.table.get cap.promise = some s ∧
        s ≠ Promise.State.pending)
#check (@Whatwg.Ecma262.Agent.post_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason)
    (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)) (ans : Unit),
    Agent.post a (Agent.Op.reject cap r) c ans ↔
      ∃ s : Promise.State value reason, a.table.get cap.promise = some s ∧
        s ≠ Promise.State.pending)
#check (@Whatwg.Ecma262.Agent.post_perform :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool)
    (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body))
    (ans : Option (Option Promise.Capability)),
    Agent.post a (Agent.Op.perform promise onFulfilled onRejected derive) c ans ↔
      (a.table.getCell promise).map Promise.Cell.handled = some true ∧
        (derive = true → ∃ cap : Promise.Capability, ans = some (some cap) ∧
          Agent.Minted a cap ∧ a.table.get cap.promise = some Promise.State.pending) ∧
        (derive = false → ans = some none))
#check (@Whatwg.Ecma262.Agent.post_markHandled :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body))
    (ans : Unit),
    Agent.post a (Agent.Op.markHandled promise) c ans ↔
      (a.table.getCell promise).map Promise.Cell.handled = some true)
#check (@Whatwg.Ecma262.Agent.post_startJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body))
    (ans : Option (Agent.Job value reason × Option body)),
    Agent.post a Agent.Op.startJob c ans ↔
      ∃ j : Agent.Job value reason,
        ans = some (j, (Agent.reactionOf a j).bind Promise.Reaction.handler) ∧
          a.active = Jobs.Active.job j.reaction ∧ a.running = some j)
#check (@Whatwg.Ecma262.Agent.post_finishJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value)
    (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)) (ans : Unit),
    Agent.post a (Agent.Op.finishJob decision) c ans ↔
      a.active = Jobs.Active.checkpoint ∧ a.running = none)
#check (@Whatwg.Ecma262.Agent.post_enterScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)) (ans : Unit),
    Agent.post a Agent.Op.enterScript c ans ↔ a.active = Jobs.Active.script)
#check (@Whatwg.Ecma262.Agent.post_leaveScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)) (ans : Unit),
    Agent.post a Agent.Op.leaveScript c ans ↔ a.active = Jobs.Active.checkpoint)

/-! ## 4. The handler fulfils every row

`Implements op`: from a well-formed agent, a request the pre admits steps (the
step is total, so there is no frontier) to a later agent, which is well formed
again and in whose state the answer lies in the post. The middle conjunct of
each `*_implements` is the operation's `WF` preservation. -/

#check (@Whatwg.Ecma262.Agent.Implements :
  ∀ {value reason body : Type}, Agent.Op value reason body → Prop)
#check (@Whatwg.Ecma262.Agent.Implements_iff :
  ∀ {value reason body : Type} (op : Agent.Op value reason body),
    Agent.Implements op ↔
      ∀ (a : Agent.Agent value reason body) (c : Agent.Cert op), Agent.WF a →
        Agent.pre a op c →
        Agent.Le a (Agent.step a op).1 ∧ Agent.WF (Agent.step a op).1 ∧
          Agent.post (Agent.step a op).1 op c (Agent.step a op).2)

#check (@Whatwg.Ecma262.Agent.newPromise_implements :
  ∀ {value reason body : Type},
    Agent.Implements (Agent.Op.newPromise : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.resolve_implements :
  ∀ {value reason body : Type} (cap : Promise.Capability) (v : value),
    Agent.Implements (Agent.Op.resolve cap v : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.reject_implements :
  ∀ {value reason body : Type} (cap : Promise.Capability) (r : reason),
    Agent.Implements (Agent.Op.reject cap r : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.perform_implements :
  ∀ {value reason body : Type} (promise : Nat) (onFulfilled onRejected : Option body)
    (derive : Bool),
    Agent.Implements (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.markHandled_implements :
  ∀ {value reason body : Type} (promise : Nat),
    Agent.Implements (Agent.Op.markHandled promise : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.startJob_implements :
  ∀ {value reason body : Type},
    Agent.Implements (Agent.Op.startJob : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.finishJob_implements :
  ∀ {value reason body : Type} (decision : Except reason value),
    Agent.Implements (Agent.Op.finishJob decision : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.enterScript_implements :
  ∀ {value reason body : Type},
    Agent.Implements (Agent.Op.enterScript : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.leaveScript_implements :
  ∀ {value reason body : Type},
    Agent.Implements (Agent.Op.leaveScript : Agent.Op value reason body))
#check (@Whatwg.Ecma262.Agent.implements :
  ∀ {value reason body : Type} (op : Agent.Op value reason body), Agent.Implements op)

/-! ## 5. Runs, and the FIFO law lifted to the agent

`Jobs.run_fifo` and `Jobs.hostEnqueuePromiseJob_order` lifted: over any run,
the jobs `startJob` started, followed by the jobs still queued, are the jobs
queued at the start followed by the jobs enqueued during the run, so a job
scheduled after another never starts before it. `requirement.hostenqueuepromisejob.3`
(634739..634841, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`), the DB-05
specification `Jobs.FifoRequirement`. DB-04 M2. -/

#check (@Whatwg.Ecma262.Agent.Op.started :
  ∀ {value reason body : Type} (op : Agent.Op value reason body),
    Agent.Op.Answer op → List (Agent.Job value reason))
#check (@Whatwg.Ecma262.Agent.Op.started_startJob :
  ∀ {value reason body : Type}
    (ans : Agent.Op.Answer (Agent.Op.startJob : Agent.Op value reason body)),
    Agent.Op.started Agent.Op.startJob ans = (ans.map Prod.fst).toList)
#check (@Whatwg.Ecma262.Agent.Op.started_other :
  ∀ {value reason body : Type} (op : Agent.Op value reason body) (ans : Agent.Op.Answer op),
    op ≠ Agent.Op.startJob → Agent.Op.started op ans = [])

#check (@Whatwg.Ecma262.Agent.runOps :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    List (Agent.Op value reason body) →
    Agent.Agent value reason body × List (Agent.Job value reason))
#check (@Whatwg.Ecma262.Agent.runOps_nil :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.runOps a [] = (a, []))
#check (@Whatwg.Ecma262.Agent.runOps_cons :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body) (ops : List (Agent.Op value reason body)),
    Agent.runOps a (op :: ops) =
      ((Agent.runOps (Agent.step a op).1 ops).1,
        Agent.Op.started op (Agent.step a op).2 ++ (Agent.runOps (Agent.step a op).1 ops).2))

#check (@Whatwg.Ecma262.Agent.runOps_fifo :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (ops : List (Agent.Op value reason body)),
    ∃ later : List (Agent.Job value reason),
      (Agent.runOps a ops).2 ++ (Agent.runOps a ops).1.queue.pending = a.queue.pending ++ later)
#check (@Whatwg.Ecma262.Agent.runOps_fifoRequirement :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (ops : List (Agent.Op value reason body)),
    ∃ later : List (Agent.Job value reason),
      Jobs.FifoRequirement (a.queue.pending ++ later) (Agent.runOps a ops).2)

#check (@Whatwg.Ecma262.Agent.WF.runOps :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (ops : List (Agent.Op value reason body)),
    Agent.WF a → Agent.WF (Agent.runOps a ops).1)

/-! ## 6. The other lifted laws

F1 (`performPromiseThen_handled`): `perform` marks the promise handled on every
branch. F2 (`mint_no_waiting`): a settled branch grows `held` by the minted
record only, which carries the derived capability (D17's link). F3 and F6
(`settleAndTrigger_cleared`, `settleTraced_pending`): `settle` clears both
lists and appends one trace entry. `callResolve_disables_reject` at the
agent: the shared marker makes `resolve` then `reject` inert, and the reverse
(`WS-PROM-CE-042`). A capability whose functions were never stored settles
nothing (`WS-PROM-CE-041`). A started job's serial is its reaction identity
(`WS-PROM-CE-046`). -/

#check (@Whatwg.Ecma262.Agent.perform_handled :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool),
    (a.table.getCell promise).isSome = true →
      ((Agent.perform a promise onFulfilled onRejected derive).1.table.getCell promise).map
        Promise.Cell.handled = some true)
#check (@Whatwg.Ecma262.Agent.perform_settled_lists :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool) (s : Promise.State value reason),
    a.table.get promise = some s → s ≠ Promise.State.pending →
      (Agent.perform a promise onFulfilled onRejected derive).1.reactions.fulfill =
          a.reactions.fulfill ∧
        (Agent.perform a promise onFulfilled onRejected derive).1.reactions.reject =
          a.reactions.reject ∧
        ∃ m : Promise.Reaction body,
          (Agent.perform a promise onFulfilled onRejected derive).1.held = a.held ++ [m] ∧
            m.id = a.reactions.next ∧ m.capability = (Agent.mintFor a derive).2)
#check (@Whatwg.Ecma262.Agent.settle_cleared :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (result : Except reason value) (kind : Promise.ReactionType),
    a.table.get promise = some Promise.State.pending →
      Promise.Reactions.waitingOn (Agent.settle a promise result).reactions promise kind = [])
#check (@Whatwg.Ecma262.Agent.settle_trace :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (result : Except reason value),
    a.table.get promise = some Promise.State.pending →
      (Agent.settle a promise result).settlements = a.settlements ++ [(promise, result)])
#check (@Whatwg.Ecma262.Agent.resolve_then_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value) (r : reason),
    Agent.WF a → Agent.Minted a cap →
      Agent.reject (Agent.resolve a cap v) cap r = Agent.resolve a cap v)
#check (@Whatwg.Ecma262.Agent.reject_then_resolve :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason) (v : value),
    Agent.WF a → Agent.Minted a cap →
      Agent.resolve (Agent.reject a cap r) cap v = Agent.reject a cap r)
#check (@Whatwg.Ecma262.Agent.resolve_unminted :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value),
    (∀ f ∈ a.functions, f.resolve ≠ cap.resolve) → Agent.resolve a cap v = a)
#check (@Whatwg.Ecma262.Agent.reject_unminted :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason),
    (∀ f ∈ a.functions, f.reject ≠ cap.reject) → Agent.reject a cap r = a)
#check (@Whatwg.Ecma262.Agent.startJob_serial :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
    a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
      (Agent.startJob a).1.active = Jobs.Active.job job.reaction ∧
        (Agent.startJob a).1.running = some job)

/-! ## 7. A reachable agent is well formed (the reviewer's check of the
design's §6.4), and the D46 hypotheses hold there -/

namespace WhatwgTest.Ecma262.AgentLaws

/-- `newPromise`, `perform` with a derived capability, `resolve`, `startJob`. -/
def ops : List (Agent.Op Unit Nat Nat) :=
  [Agent.Op.newPromise, Agent.Op.perform 0 (some 7) none true,
    Agent.Op.resolve (Promise.Capability.mk 0 0 1) (), Agent.Op.startJob]

example : Agent.WF (Agent.runOps (Agent.empty : Agent.Agent Unit Nat Nat) ops).1 :=
  Agent.WF.runOps Agent.empty ops Agent.WF.empty

/-- The run started the one job, reaction `0`, and left the queue empty. -/
example :
    (Agent.runOps (Agent.empty : Agent.Agent Unit Nat Nat) ops).2 =
        [Jobs.ReactionJob.mk 0 (Except.ok ())] ∧
      (Agent.runOps (Agent.empty : Agent.Agent Unit Nat Nat) ops).1.queue.pending = [] :=
  ⟨rfl, rfl⟩

end WhatwgTest.Ecma262.AgentLaws
