import Whatwg.Ecma262
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned Q5 battery for slice B1: the agent record, its nine
operations, the one step function, the instance set, the views onto the
landed store-level operations, and the D46 law.

Packet: `test/contracts/promise-agent-q5.contract.md`.
Graph: `PROMISE-PG-AGENT`, `docs/PROMISE-AGENT-DAG.md`.
Attacks: `test/counterexamples/promise/ATTACKS.md`, section "Q5 agent
packet", rows WS-PROM-CE-040..047.
Rulings: R-W3 (the brief), R-W5 (mask names), R-W9 (no axiom-report module).

Every ascription names a declaration that does not exist at `b0d35e2`: this
module is red until builder slice B1 lands `Whatwg/Ecma262/Agent.lean` and
imports it from `Whatwg/Ecma262.lean`. The builder must not change a
statement in this file; it may repair the elaboration of an `example`'s
proof without changing the example's statement.

Byte spans are 0-based, ends exclusive, into `vendor/ecma262-0248456c/spec.html`
(SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`).
Row ids are those of `generated/ecma262-census.tsv`. Citing a row anchors a
declaration; it moves no coverage state.

Masks are DB-04's, written "DB-04 M1" (chunk sequence and terminal outcome;
for this layer: a cell value, a branch, a table shape or a terminal agent)
and "DB-04 M2" (full settlement order; for this layer: the order of the
settlement trace or of the job queue). No Lean name here spells a mask.
-/

set_option autoImplicit false

open Whatwg.Ecma262

/-! ## 1. The instance set (R-W3; the design's decision 2, option a)

`Promise.Reaction` and `Promise.Reactions` gain a global `DecidableEq`
conditional on `body`; `Promise.Reactions`, `Promise.ResolvingFunctions` and
`Jobs.Active` gain `Repr`. This supersedes the `E-29` sentence "must not gain
one silently" by ruling, and `WS-PROM-CE-015` is re-dispositioned at the Q5
landing. -/

#check (inferInstance : DecidableEq (Whatwg.Ecma262.Promise.Reaction Nat))
#check (inferInstance : DecidableEq (Whatwg.Ecma262.Promise.Reactions Nat))
#check (inferInstance : Repr (Whatwg.Ecma262.Promise.Reactions Nat))
#check (inferInstance : Repr Whatwg.Ecma262.Promise.ResolvingFunctions)
#check (inferInstance : Repr Whatwg.Ecma262.Jobs.Active)

/-! The landed instances stay: `Repr (Reaction Nat)` is the `E-50` receipt of
the Q3b addendum, and `DecidableEq ResolvingFunctions`, `DecidableEq Active`
are the base packet's. -/
#check (inferInstance : Repr (Whatwg.Ecma262.Promise.Reaction Nat))
#check (inferInstance : DecidableEq Whatwg.Ecma262.Promise.ResolvingFunctions)
#check (inferInstance : DecidableEq Whatwg.Ecma262.Jobs.Active)

/-! `DecidableEq (Except ε α)` is a *scoped* instance of the namespace
`Whatwg.Ecma262.Agent`, never a global one, because Batteries declares a global
one and lean4-effect4 requires Batteries through `aesop`. Outside the scope
the instance must fail to synthesize; inside it, it must succeed. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.instDecidableEqExcept :
  ∀ {ε α : Type} [DecidableEq ε] [DecidableEq α], DecidableEq (Except ε α))

/--
info: failed to synthesize instance of type class
  DecidableEq (Except Nat Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#check_failure (inferInstance : DecidableEq (Except Nat Nat))

open Whatwg.Ecma262.Agent in
#check (inferInstance : DecidableEq (Except Nat Nat))

/-! The agent and its alphabet derive both instances, conditional on the three
parameters, with no instance argument for `Except`: the derived instances use
the scoped one internally. -/
#check (inferInstance : DecidableEq (Whatwg.Ecma262.Agent.Agent Unit Nat Nat))
#check (inferInstance : Repr (Whatwg.Ecma262.Agent.Agent Unit Nat Nat))
#check (inferInstance : DecidableEq (Whatwg.Ecma262.Agent.Op Unit Nat Nat))
#check (inferInstance : Repr (Whatwg.Ecma262.Agent.Op Unit Nat Nat))

/-! ## 2. The record

`clause.jobs` (624525..636548, digest
`871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf`) and
`clause.properties-of-promise-instances` (2744135..2746691, digest
`f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d`). The agent
*contains* the landed `Promise.Table`, `Promise.Reactions` and reaction-job
`Jobs.Queue` by value (R-W3); it adds the stored resolving functions, `held`,
the activation with its running job, the settlement trace and the function
cursor. Three cursors stay (`table.next`, `reactions.next`, `nextFunction`);
a job's serial is its reaction identity. The queue payload is fixed at
`Jobs.ReactionJob (Except reason value)` and every type is in `Type`. Gap
`G-08` remainder (the global configuration that threads the activation),
`G-03` (the resolving functions as state). -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.Job : Type → Type → Type)

#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent : Type → Type → Type → Type)

#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.mk :
  ∀ {value reason body : Type}, Promise.Table value reason → Promise.Reactions body →
    List (Promise.Reaction body) → Jobs.Queue (Agent.Job value reason) →
    List Promise.ResolvingFunctions → Nat → Jobs.Active → Option (Agent.Job value reason) →
    Promise.SettlementTrace value reason → Agent.Agent value reason body)

#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.table :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Table value reason)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.reactions :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Reactions body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.held :
  ∀ {value reason body : Type}, Agent.Agent value reason body → List (Promise.Reaction body))
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.queue :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Jobs.Queue (Agent.Job value reason))
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.functions :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    List Promise.ResolvingFunctions)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.nextFunction :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Nat)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.active :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Jobs.Active)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.running :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Option (Agent.Job value reason))
#whatwg_freeze (@Whatwg.Ecma262.Agent.Agent.settlements :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Promise.SettlementTrace value reason)

#whatwg_freeze (@Whatwg.Ecma262.Agent.empty :
  ∀ {value reason body : Type}, Agent.Agent value reason body)

/-! ## 3. The operations

Each is anchored by its row in the design's §3.2 table, restated in the
contract's §4. Gap ids: `G-03` (`newPromise`, `resolve`, `reject`,
`callFunctions`), `G-01` and `G-11` (`perform`, `mintFor`), `G-02` remainder
(`markHandled`), `G-07` remainder and `G-08` remainder (`reactionOf`,
`startJob`, `finishJob`, `enterScript`, `leaveScript`). -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.newPromise :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body × Promise.Capability)
#whatwg_freeze (@Whatwg.Ecma262.Agent.settle :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Nat →
    Except reason value → Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.callFunctions :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    (Promise.ResolvingFunctions → Bool) → Except reason value →
    Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.resolve :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    value → Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.reject :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability →
    reason → Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.mintFor :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Bool →
    Agent.Agent value reason body × Option Promise.Capability)
#whatwg_freeze (@Whatwg.Ecma262.Agent.perform :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Nat → Option body →
    Option body → Bool →
    Agent.Agent value reason body × Option (Option Promise.Capability))
#whatwg_freeze (@Whatwg.Ecma262.Agent.markHandled :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Nat →
    Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.reactionOf :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Job value reason → Option (Promise.Reaction body))
#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body × Option (Agent.Job value reason × Option body))
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Except reason value →
    Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.enterScript :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.leaveScript :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body)

/-! ## 4. The alphabet, the answers and the step

Nine first-order operations; every argument is data (DB-02). `step` is total,
and the nine `step_*` equations fix each operation's answer type, since each
typechecks only when `Op.Answer` reduces to the stated type. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.Op : Type → Type → Type → Type)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.newPromise :
  ∀ {value reason body : Type}, Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.resolve :
  ∀ {value reason body : Type}, Promise.Capability → value → Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.reject :
  ∀ {value reason body : Type}, Promise.Capability → reason → Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.perform :
  ∀ {value reason body : Type}, Nat → Option body → Option body → Bool →
    Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.markHandled :
  ∀ {value reason body : Type}, Nat → Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.startJob :
  ∀ {value reason body : Type}, Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.finishJob :
  ∀ {value reason body : Type}, Except reason value → Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.enterScript :
  ∀ {value reason body : Type}, Agent.Op value reason body)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.leaveScript :
  ∀ {value reason body : Type}, Agent.Op value reason body)

#whatwg_freeze (@Whatwg.Ecma262.Agent.Op.Answer :
  ∀ {value reason body : Type}, Agent.Op value reason body → Type)

#whatwg_freeze (@Whatwg.Ecma262.Agent.step :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    (op : Agent.Op value reason body) → Agent.Agent value reason body × Agent.Op.Answer op)

/-! DB-04 M1 for all nine: each states which operation runs, and the answers'
types; the order content is in the operation's own laws below. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_newPromise :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.step a Agent.Op.newPromise = Agent.newPromise a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_resolve :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value),
    Agent.step a (Agent.Op.resolve cap v) = (Agent.resolve a cap v, ())) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason),
    Agent.step a (Agent.Op.reject cap r) = (Agent.reject a cap r, ())) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_perform :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool),
    Agent.step a (Agent.Op.perform promise onFulfilled onRejected derive) =
      Agent.perform a promise onFulfilled onRejected derive) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_markHandled :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
    Agent.step a (Agent.Op.markHandled promise) = (Agent.markHandled a promise, ())) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_startJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.step a Agent.Op.startJob = Agent.startJob a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_finishJob :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value),
    Agent.step a (Agent.Op.finishJob decision) = (Agent.finishJob a decision, ())) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_enterScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.step a Agent.Op.enterScript = (Agent.enterScript a, ())) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.step_leaveScript :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.step a Agent.Op.leaveScript = (Agent.leaveScript a, ())) axioms [propext]

/-! ## 5. Defining equations

These fix each operation's semantics exactly, including every disabled
branch, which R-W3 requires to leave the agent unchanged. Masks: an equation
whose right side moves the queue or the settlement trace is DB-04 M2
(`settle_eq`, `callFunctions_fresh`, `perform_fulfilled`, `perform_rejected`,
`startJob_checkpoint`, `finishJob_capability`); every other one is DB-04 M1. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.empty_eq :
  ∀ {value reason body : Type},
    (Agent.empty : Agent.Agent value reason body) =
      Agent.Agent.mk Promise.Table.empty Promise.Reactions.empty [] Jobs.Queue.empty [] 0
        Jobs.Active.checkpoint none []) axioms []

/-! `op.newpromisecapability` (2696238..2698770, digest
`9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9`) at the
intrinsic constructor, with `op.createresolvingfunctions` (2692679..2695411,
digest `8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944`)
storing the functions. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.newPromise_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.newPromise a =
      ({ a with
          table := (Promise.newPromiseCapability a.table a.nextFunction).1,
          functions := a.functions ++
            [Promise.createResolvingFunctions a.table.next a.nextFunction],
          nextFunction := a.nextFunction + 2 },
        (Promise.newPromiseCapability a.table a.nextFunction).2)) axioms []

/-! `op.fulfillpromise` (2695419..2696230) and `op.rejectpromise`
(2699323..2700252) with `op.triggerpromisereactions` (2700260..2701212), the
settlement recorded by the landed `Table.settleTraced` (D20's producer). -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.settle_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (result : Except reason value),
    Agent.settle a promise result =
      { a with
        table := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).1,
        reactions :=
          (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.1,
        queue := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.2,
        settlements := (Promise.Table.settleTraced a.table a.settlements promise result).2 }) axioms [propext]

/-! `op.createresolvingfunctions` resolve and reject steps 1 to 3: the shared
one-shot marker. An unknown function and a fired one are both inert. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.callFunctions_none :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value),
    a.functions.find? pick = none → Agent.callFunctions a pick result = a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.callFunctions_fired :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value)
    (f : Promise.ResolvingFunctions),
    a.functions.find? pick = some f → f.alreadyResolved = true →
      Agent.callFunctions a pick result = a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.callFunctions_fresh :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value)
    (f : Promise.ResolvingFunctions),
    a.functions.find? pick = some f → f.alreadyResolved = false →
      Agent.callFunctions a pick result =
        { Agent.settle a f.promise result with
          functions := a.functions.map (fun (g : Promise.ResolvingFunctions) =>
            if pick g then { g with alreadyResolved := true } else g) }) axioms [propext]

/-! `Call(cap.[[Resolve]], undefined, « v »)` and `Call(cap.[[Reject]], …)`
on the non-thenable branch (`G-04`, `G-05` stay out). -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.resolve_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value),
    Agent.resolve a cap v =
      Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
        (Except.ok v)) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.reject_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason),
    Agent.reject a cap r =
      Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject)
        (Except.error r)) axioms [propext]

/-! Web IDL `op.dfn-perform-steps-once-promise-is-settled` step 6: the derived
capability is minted only when `derive` is set. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.mintFor_true :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.mintFor a true = ((Agent.newPromise a).1, some (Agent.newPromise a).2)) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.mintFor_false :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    Agent.mintFor a false = (a, none)) axioms []

/-! `op.performpromisethen` (2740635..2743669, digest
`ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce`), its three
branches through the landed `performPromiseThen`, and the missing cell
(`E-31`'s `Option`). The settled branches hand the minted record to `held`. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.perform_missing :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool),
    a.table.get promise = none →
      Agent.perform a promise onFulfilled onRejected derive = (a, none)) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.perform_pending :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool),
    a.table.get promise = some Promise.State.pending →
      Agent.perform a promise onFulfilled onRejected derive =
        ({ (Agent.mintFor a derive).1 with
            table := Promise.Table.markHandled (Agent.mintFor a derive).1.table promise,
            reactions := (Promise.Reactions.add a.reactions promise onFulfilled onRejected
              (Agent.mintFor a derive).2).1 },
          some (Agent.mintFor a derive).2)) axioms [propext, Quot.sound]
#whatwg_freeze (@Whatwg.Ecma262.Agent.perform_fulfilled :
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
          some (Agent.mintFor a derive).2)) axioms [propext, Quot.sound]
#whatwg_freeze (@Whatwg.Ecma262.Agent.perform_rejected :
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
          some (Agent.mintFor a derive).2)) axioms [propext, Quot.sound]

/-! Web IDL `op.mark-a-promise-as-handled` (356060..356713). -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.markHandled_eq :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
    Agent.markHandled a promise =
      { a with table := Promise.Table.markHandled a.table promise }) axioms []

/-! The record a job was built from: a held record first, otherwise the
registered one in the list its argument's tag selects (`G-01`). -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.reactionOf_held :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (r : Promise.Reaction body),
    a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = some r →
      Agent.reactionOf a job = some r) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.reactionOf_ok :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (v : value),
    a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = none →
      job.argument = Except.ok v →
      Agent.reactionOf a job =
        Promise.Reactions.get a.reactions Promise.ReactionType.fulfill job.reaction) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.reactionOf_error :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (r : reason),
    a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = none →
      job.argument = Except.error r →
      Agent.reactionOf a job =
        Promise.Reactions.get a.reactions Promise.ReactionType.reject job.reaction) axioms []

/-! `requirement.jobs.1` (625769..626250), `requirement.jobs.2`
(626257..626350) and `requirement.hostenqueuepromisejob.3` (634739..634841):
at a checkpoint the oldest job starts, and its serial is its reaction
identity; anywhere else, or on an empty queue, nothing starts (DB-07: an
empty queue is a live frontier). -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob_checkpoint :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
    a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
      Agent.startJob a =
        ({ a with
            queue := Jobs.Queue.mk rest,
            active := Jobs.Active.job job.reaction,
            running := some job },
          some (job, (Agent.reactionOf a job).bind Promise.Reaction.handler))) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob_empty :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.queue.pending = [] → Agent.startJob a = (a, none)) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob_blocked :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.active ≠ Jobs.Active.checkpoint → Agent.startJob a = (a, none)) axioms [propext]

/-! `op.newpromisereactionjob` (2702885..2705591, digest
`3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b`) inner steps
4 to 9 with `requirement.jobs.3` (626357..626479): the handler's completion is
the host's decision (DB-02); the derived capability is settled through its
stored resolving functions; with `[[Capability]]` *undefined* nothing settles
(D18, `WS-PROM-CE-044`); the agent returns to a checkpoint. Inert when no job
is running. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_idle :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value),
    a.running = none → Agent.finishJob a decision = a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_not_job :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value),
    (∀ s : Nat, a.active ≠ Jobs.Active.job s) → Agent.finishJob a decision = a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_unknown :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason),
    a.active = Jobs.Active.job s → a.running = some job → Agent.reactionOf a job = none →
      Agent.finishJob a decision =
        { a with active := Jobs.Active.checkpoint, running := none }) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_no_capability :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = none →
      Agent.finishJob a decision =
        { a with active := Jobs.Active.checkpoint, running := none }) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_capability :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (cap : Promise.Capability),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = some cap →
      Agent.finishJob a decision =
        { Agent.callFunctions a
            (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
            (Promise.reactionHandlerResult r job.argument decision) with
          active := Jobs.Active.checkpoint, running := none }) axioms [propext]

/-! `requirement.jobs.1`: an execution context is running, then the stack is
empty again. No other activation is entered or left. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.enterScript_checkpoint :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.active = Jobs.Active.checkpoint →
      Agent.enterScript a = { a with active := Jobs.Active.script }) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.enterScript_other :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.active ≠ Jobs.Active.checkpoint → Agent.enterScript a = a) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.leaveScript_script :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.active = Jobs.Active.script →
      Agent.leaveScript a = { a with active := Jobs.Active.checkpoint }) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.leaveScript_other :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    a.active ≠ Jobs.Active.script → Agent.leaveScript a = a) axioms [propext]

/-! ## 6. `Minted` and the fourteen clauses of `WF`

Slice B1 lands the definitions, because `resolve_table` below and the Web IDL
`resolve_view` of slice B3 are stated under `WF` and B3 does not wait for B2.
Slice B2 lands every lemma about them. The clauses are frozen one by one by
their projections. `resolvedSettled` holds only while thenable adoption
(`G-05`) is out, and carries the obligation to be weakened when it enters
(R-W3). `settlementsCoherent` closes debt D20. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.Minted :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Promise.Capability → Prop)
#whatwg_freeze (@Whatwg.Ecma262.Agent.Minted_iff :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability),
    Agent.Minted a cap ↔
      ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject = cap.reject ∧
        f.promise = cap.promise) axioms []

#whatwg_freeze (@Whatwg.Ecma262.Agent.WF :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Prop)

#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.tableNodup :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    (a.table.entries.map Prod.fst).Nodup) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.tableBelow :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ e ∈ a.table.entries, e.1 < a.table.next) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.functionsBelow :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ f ∈ a.functions, f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.functionsAllocated :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ f ∈ a.functions, (a.table.getCell f.promise).isSome = true) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.resolvedSettled :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ f ∈ a.functions, f.alreadyResolved = true →
      Promise.Table.isPending a.table f.promise = false) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.reactionsBelow :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held, r.id < a.reactions.next) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.queueBelow :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ j ∈ a.queue.pending, j.reaction < a.reactions.next) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.paired :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    a.reactions.fulfill.map Promise.Reaction.id = a.reactions.reject.map Promise.Reaction.id) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.functionsNodup :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    (a.functions.map Promise.ResolvingFunctions.resolve).Nodup) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.heldDistinct :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    (a.held.map Promise.Reaction.id ++ a.reactions.fulfill.map Promise.Reaction.id).Nodup) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.queuedKnown :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ j ∈ a.queue.pending, (Agent.reactionOf a j).isSome = true) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.runningActive :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    (∀ j : Agent.Job value reason, a.running = some j →
        a.active = Jobs.Active.job j.reaction) ∧
      (∀ s : Nat, a.active = Jobs.Active.job s → a.running.isSome = true)) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.capabilityStored :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      ∀ cap : Promise.Capability, r.capability = some cap → Agent.Minted a cap) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.settlementsCoherent :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    (a.settlements.map Prod.fst).Nodup ∧
      (∀ (p : Nat) (v : value), (p, Except.ok v) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.fulfilled v)) ∧
      (∀ (p : Nat) (r : reason), (p, Except.error r) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.rejected r))) axioms [propext]

/-! An allocated identity is below the table cursor, so it is never the
identity the next allocation takes. DB-04 M1. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.WF.get_lt :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.WF a →
    ∀ {p : Nat} {s : Promise.State value reason},
      Promise.Table.get a.table p = some s → p < a.table.next) axioms [propext, Quot.sound]

/-! ## 7. Views onto the landed store-level operations

Each right side is the landed operation, not a copy (the reviewer's check of
the design's §6.4). All DB-04 M1 except `settle_ok_fulfillPromise` and
`settle_error_rejectPromise`, whose triples include the job queue and are
DB-04 M2, and `settle_settlements`, DB-04 M2. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.settleAndTrigger_table :
  ∀ {value reason body : Type} (t : Promise.Table value reason)
    (rs : Promise.Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value),
    (Promise.Table.settleAndTrigger t rs q id result).1 = Promise.Table.settle t id result) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.settle_ok_fulfillPromise :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (v : value),
    ((Agent.settle a promise (Except.ok v)).table,
        (Agent.settle a promise (Except.ok v)).reactions,
        (Agent.settle a promise (Except.ok v)).queue) =
      Promise.fulfillPromise a.table a.reactions a.queue promise v) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.settle_error_rejectPromise :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (r : reason),
    ((Agent.settle a promise (Except.error r)).table,
        (Agent.settle a promise (Except.error r)).reactions,
        (Agent.settle a promise (Except.error r)).queue) =
      Promise.rejectPromise a.table a.reactions a.queue promise r) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.settle_settlements :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
    (result : Except reason value),
    (Agent.settle a promise result).settlements =
      (Promise.Table.settleTraced a.table a.settlements promise result).2) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.newPromise_capability :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body),
    (Agent.newPromise a).2 = (Promise.newPromiseCapability a.table a.nextFunction).2) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.markHandled_table :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
    (Agent.markHandled a promise).table = Promise.Table.markHandled a.table promise) axioms []
#whatwg_freeze (@Whatwg.Ecma262.Agent.markHandled_get :
  ∀ {value reason : Type} (t : Promise.Table value reason) (p q : Nat),
    Promise.Table.get (Promise.Table.markHandled t p) q = Promise.Table.get t q) axioms [propext, Quot.sound]

/-! The oldest job starts, at its own reaction identity, which is the landed
`Jobs.startJob` with that serial. DB-04 M2: it observes which job leaves the
queue. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob_agree :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
    a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
      Jobs.startJob a.active a.queue job.reaction =
        some (job, (Agent.startJob a).1.active, (Agent.startJob a).1.queue)) axioms [propext]

/-! **D46 re-described.** The frozen `Whatwg.WebIdl.Promise.resolve` and
`reject` are `Table.settle`; for a capability this agent stored, the agent's
`resolve` and `reject` change the table exactly as `Table.settle` does, under
`WF` (whose `resolvedSettled` covers functions that already fired).
`op.resolve` (Web IDL 349216..349783) via `op.createresolvingfunctions`.
DB-04 M1. -/
#whatwg_freeze (@Whatwg.Ecma262.Agent.resolve_table :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value),
    Agent.WF a →
      a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
        some f →
      f.promise = cap.promise →
      (Agent.resolve a cap v).table =
        Promise.Table.settle a.table cap.promise (Except.ok v)) axioms [propext]
#whatwg_freeze (@Whatwg.Ecma262.Agent.reject_table :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (r : reason),
    Agent.WF a →
      a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) =
        some f →
      f.promise = cap.promise →
      (Agent.reject a cap r).table =
        Promise.Table.settle a.table cap.promise (Except.error r)) axioms [propext]

/-! ## 8. D46: `react` followed by `resolve` enqueues the new reaction's job

`op.triggerpromisereactions` (2700260..2701212, digest
`ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839`) and
`op.performpromisethen`. All four are DB-04 M2: they observe queue order. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.waitingOn_add_fulfill :
  ∀ {body : Type} (rs : Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (cap : Option Promise.Capability),
    Promise.Reactions.waitingOn (Promise.Reactions.add rs promise onFulfilled onRejected cap).1
        promise Promise.ReactionType.fulfill =
      Promise.Reactions.waitingOn rs promise Promise.ReactionType.fulfill ++
        [Promise.Reaction.mk rs.next promise Promise.ReactionType.fulfill onFulfilled cap
          Promise.ReactionPhase.waiting]) axioms [propext]

#whatwg_freeze (@Whatwg.Ecma262.Agent.react_resolve_enqueues :
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
          [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)])) axioms [propext, Quot.sound]

#whatwg_freeze (@Whatwg.Ecma262.Agent.react_resolve_enqueues_wf :
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
          [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)])) axioms [propext, Quot.sound]

#whatwg_freeze (@Whatwg.Ecma262.Agent.react_resolve_enqueues_exactly :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
    a.table.get cap.promise = some Promise.State.pending →
      cap.promise ≠ a.table.next →
      a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) =
        some f →
      f.alreadyResolved = false → f.promise = cap.promise →
      Promise.Reactions.waitingOn a.reactions cap.promise Promise.ReactionType.fulfill = [] →
      (Agent.resolve (Agent.perform a cap.promise (some h) none true).1 cap v).queue.pending =
        a.queue.pending ++ [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) axioms [propext, Quot.sound]

/-! ## 9. D17 and run to completion at the agent

`finishJob_settles_capability` closes debt D17: the capability a reaction
record carries is settled through the functions this agent stored for it.
`op.newpromisereactionjob` steps 6 to 9; DB-04 M1. `startJob_running` is
`requirement.jobs.3` (626357..626479, digest
`3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378`) at the
agent (`WS-PROM-CE-045`); DB-04 M1. -/

#whatwg_freeze (@Whatwg.Ecma262.Agent.finishJob_settles_capability :
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
        (Agent.finishJob a decision).active = Jobs.Active.checkpoint) axioms [propext]

#whatwg_freeze (@Whatwg.Ecma262.Agent.startJob_running :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body) (s : Nat),
    a.active = Jobs.Active.job s → Agent.startJob a = (a, none)) axioms [propext]

/-! ## 10. Finite witnesses over `Unit`, `Nat` and `Nat`

Executable evidence beside the quantified laws, for the rows of
`test/counterexamples/promise/ATTACKS.md` that the B1 surface can reach. Each
is closed by `rfl` (kernel evaluation). The builder may repair a proof here;
it may not change a statement. -/

namespace WhatwgTest.Ecma262.AgentContract

/-- One pending promise with its capability, from the empty agent. -/
def start : Agent.Agent Unit Nat Nat × Promise.Capability := Agent.newPromise Agent.empty

/-- `WS-PROM-CE-040`, ECMA-262 level: `perform` with a derived capability, then
`resolve`, enqueues exactly the new reaction's job, `⟨0, .ok ()⟩`. -/
example :
    (Agent.resolve (Agent.perform start.1 start.2.promise (some 7) none true).1
        start.2 ()).queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ())] := rfl

/-- `WS-PROM-CE-040`: the hypotheses of `react_resolve_enqueues_wf` hold at
`start`, so the D46 law is not vacuous. `WF` is shown clause by clause. -/
example : Agent.WF start.1 :=
  { tableNodup := by decide
    tableBelow := by decide
    functionsBelow := by decide
    functionsAllocated := by decide
    resolvedSettled := by decide
    reactionsBelow := by decide
    queueBelow := by decide
    paired := rfl
    functionsNodup := by decide
    heldDistinct := by decide
    queuedKnown := by decide
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := fun _ h => absurd h List.not_mem_nil
    settlementsCoherent :=
      ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
        fun _ _ h => absurd h List.not_mem_nil⟩ }

example :
    start.1.table.get start.2.promise = some Promise.State.pending ∧
      start.1.functions.find?
          (fun (g : Promise.ResolvingFunctions) => g.resolve == start.2.resolve) =
        some (Promise.createResolvingFunctions 0 0) ∧
      (Promise.createResolvingFunctions 0 0).alreadyResolved = false ∧
      (Promise.createResolvingFunctions 0 0).promise = start.2.promise :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `WS-PROM-CE-041`: a forged capability, whose functions this agent never
stored, settles nothing; the agent is unchanged. -/
example : Agent.resolve start.1 (Promise.Capability.mk 0 5 6) () = start.1 := rfl
example : Agent.reject start.1 (Promise.Capability.mk 0 5 6) 9 = start.1 := rfl

/-- `WS-PROM-CE-042`: the one-shot marker is shared; `reject` after `resolve`
through the same capability is inert. -/
example :
    Agent.reject (Agent.resolve start.1 start.2 ()) start.2 9 =
      Agent.resolve start.1 start.2 () := rfl
example :
    (Agent.resolve start.1 start.2 ()).table.get start.2.promise =
      some (Promise.State.fulfilled ()) := rfl

/-- `WS-PROM-CE-043`: duplicate identifiers through the public `Table.mk` are
constructible, and such an agent is not well formed. -/
def duplicate : Agent.Agent Unit Nat Nat :=
  { (Agent.empty : Agent.Agent Unit Nat Nat) with
    table := Promise.Table.mk
      [(0, Promise.Cell.mk Promise.State.pending false),
        (0, Promise.Cell.mk (Promise.State.fulfilled ()) false)] 1 }

example : ¬ Agent.WF duplicate := fun h => absurd h.tableNodup (by decide)

/-- A pending promise with one reaction registered without a derived
capability, settled, its job started: the agent `finishJob` meets. -/
def plainRunning : Agent.Agent Unit Nat Nat :=
  (Agent.startJob
    (Agent.resolve (Agent.perform start.1 start.2.promise (some 7) none false).1
      start.2 ())).1

/-- The same with a derived capability. -/
def derivedRunning : Agent.Agent Unit Nat Nat :=
  (Agent.startJob
    (Agent.resolve (Agent.perform start.1 start.2.promise (some 7) none true).1
      start.2 ())).1

/-- `WS-PROM-CE-044`: with `[[Capability]]` *undefined* the job settles nothing:
the table is unchanged and the agent is back at a checkpoint (D18). -/
example :
    (Agent.finishJob plainRunning (Except.ok ())).table = plainRunning.table ∧
      (Agent.finishJob plainRunning (Except.ok ())).active = Jobs.Active.checkpoint :=
  ⟨rfl, rfl⟩

/-- The contrast (D17's non-vacuity): with a derived capability, the job
settles the derived promise, identity `1`, with the handler's result. -/
example :
    (Agent.finishJob derivedRunning (Except.ok ())).table.get 1 =
      some (Promise.State.fulfilled ()) ∧
      derivedRunning.table.get 1 = some Promise.State.pending := ⟨rfl, rfl⟩

/-- `WS-PROM-CE-045` and `WS-PROM-CE-046`: the started job's serial is its
reaction identity `0`, the record of that identity is `.queued 0`, and while
it runs no job starts even though another is queued. -/
def twoQueued : Agent.Agent Unit Nat Nat :=
  (Agent.resolve
    (Agent.perform (Agent.perform start.1 start.2.promise (some 7) none false).1
      start.2.promise (some 8) none false).1
    start.2 ())

example :
    twoQueued.queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ()), Jobs.ReactionJob.mk 1 (Except.ok ())] := rfl

example :
    (Agent.startJob twoQueued).1.active = Jobs.Active.job 0 ∧
      (Promise.Reactions.get twoQueued.reactions Promise.ReactionType.fulfill 0).map
          Promise.Reaction.phase =
        some (Promise.ReactionPhase.queued 0) := ⟨rfl, rfl⟩

example :
    (Agent.startJob (Agent.startJob twoQueued).1).2 = none ∧
      (Agent.startJob (Agent.startJob twoQueued).1).1 = (Agent.startJob twoQueued).1 :=
  ⟨rfl, rfl⟩

end WhatwgTest.Ecma262.AgentContract
