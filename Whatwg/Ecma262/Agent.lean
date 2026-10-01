import Whatwg.Ecma262.Promise

/-!
# The ECMAScript agent

Owner: promise slice Q5, graph `PROMISE-PG-AGENT` (`docs/PROMISE-AGENT-DAG.md`),
frozen by `test/contracts/promise-agent-q5.contract.md` (rulings R-W3 and
R-W13); this module is builder slice B1, and its battery is
`WhatwgTest/Ecma262/AgentContract.lean`.
-/

namespace Whatwg.Ecma262.Agent

/-! ## The instance set -/

/-- Core `Except` has no `DecidableEq` at this toolchain, and Batteries
derives one globally. This one is scoped, so a consumer that imports both meets
no second global instance. -/
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

/-! ## The record -/

/-- The job payload the landed operations already write. -/
abbrev Job (value reason : Type) : Type := Jobs.ReactionJob (Except reason value)

/-- The agent: the three landed stores, contained, not replaced. -/
structure Agent (value reason body : Type) where
  table : Promise.Table value reason
  reactions : Promise.Reactions body
  held : List (Promise.Reaction body)
  queue : Jobs.Queue (Job value reason)
  functions : List Promise.ResolvingFunctions
  nextFunction : Nat
  active : Jobs.Active
  running : Option (Job value reason)
  settlements : Promise.SettlementTrace value reason
  deriving DecidableEq, Repr

/-- The agent before any promise exists, at a checkpoint. -/
def empty {value reason body : Type} : Agent value reason body :=
  ⟨Promise.Table.empty, Promise.Reactions.empty, [], Jobs.Queue.empty, [], 0,
    Jobs.Active.checkpoint, none, []⟩

/-! ## The operations -/

/-- `op.newpromisecapability` with the resolving functions stored. -/
def newPromise {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body × Promise.Capability :=
  ({ a with
      table := (Promise.newPromiseCapability a.table a.nextFunction).1,
      functions := a.functions ++
        [Promise.createResolvingFunctions a.table.next a.nextFunction],
      nextFunction := a.nextFunction + 2 },
    (Promise.newPromiseCapability a.table a.nextFunction).2)

/-- `op.fulfillpromise` and `op.rejectpromise` with `op.triggerpromisereactions`. -/
def settle {value reason body : Type} (a : Agent value reason body) (promise : Nat)
    (result : Except reason value) : Agent value reason body :=
  { a with
    table := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).1,
    reactions := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.1,
    queue := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.2,
    settlements := (Promise.Table.settleTraced a.table a.settlements promise result).2 }

/-- Call a stored resolving function selected by `pick`. -/
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

/-- `Call(cap.[[Resolve]], undefined, « v »)`. -/
def resolve {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (v : value) : Agent value reason body :=
  callFunctions a (fun f => f.resolve == cap.resolve) (Except.ok v)

/-- `Call(cap.[[Reject]], undefined, « r »)`. -/
def reject {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (r : reason) : Agent value reason body :=
  callFunctions a (fun f => f.reject == cap.reject) (Except.error r)

/-- Mint the result capability when `derive` is set. -/
def mintFor {value reason body : Type} (a : Agent value reason body) :
    Bool → Agent value reason body × Option Promise.Capability
  | true => ((newPromise a).1, some (newPromise a).2)
  | false => (a, none)

/-- `op.performpromisethen`, with the result capability minted first. -/
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

/-- Web IDL `op.mark-a-promise-as-handled`. -/
def markHandled {value reason body : Type} (a : Agent value reason body) (promise : Nat) :
    Agent value reason body :=
  { a with table := Promise.Table.markHandled a.table promise }

/-- The reaction record a job was built from. -/
def reactionOf {value reason body : Type} (a : Agent value reason body)
    (job : Job value reason) : Option (Promise.Reaction body) :=
  match a.held.find? (fun r => r.id == job.reaction) with
  | some r => some r
  | none =>
      Promise.Reactions.get a.reactions
        (match job.argument with
          | .ok _ => Promise.ReactionType.fulfill
          | .error _ => Promise.ReactionType.reject) job.reaction

/-- At a checkpoint, start the oldest job. -/
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

/-- Finish the running job with the host's decision. -/
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

/-- Script evaluation begins at a checkpoint. -/
def enterScript {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body :=
  match a.active with
  | .checkpoint => { a with active := Jobs.Active.script }
  | _ => a

/-- Script evaluation returns. -/
def leaveScript {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body :=
  match a.active with
  | .script => { a with active := Jobs.Active.checkpoint }
  | _ => a

/-! ## The alphabet, the answers and the step -/

/-- First-order operations. -/
inductive Op (value reason body : Type) where
  | newPromise
  | resolve (capability : Promise.Capability) (v : value)
  | reject (capability : Promise.Capability) (r : reason)
  | perform (promise : Nat) (onFulfilled onRejected : Option body) (derive : Bool)
  | markHandled (promise : Nat)
  | startJob
  | finishJob (decision : Except reason value)
  | enterScript
  | leaveScript
  deriving DecidableEq, Repr

/-- The answer each operation returns. -/
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

/-- The one step function. -/
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

/-! ## Step equations -/

/-- DB-04 M1. -/
theorem step_newPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.newPromise = Agent.newPromise a := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value),
      Agent.step a (Agent.Op.resolve cap v) = (Agent.resolve a cap v, ()) := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason),
      Agent.step a (Agent.Op.reject cap r) = (Agent.reject a cap r, ()) := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_perform :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      Agent.step a (Agent.Op.perform promise onFulfilled onRejected derive) =
        Agent.perform a promise onFulfilled onRejected derive := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_markHandled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      Agent.step a (Agent.Op.markHandled promise) = (Agent.markHandled a promise, ()) := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_startJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.startJob = Agent.startJob a := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_finishJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value),
      Agent.step a (Agent.Op.finishJob decision) = (Agent.finishJob a decision, ()) := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_enterScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.enterScript = (Agent.enterScript a, ()) := by
  intros; rfl

/-- DB-04 M1. -/
theorem step_leaveScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.step a Agent.Op.leaveScript = (Agent.leaveScript a, ()) := by
  intros; rfl

/-! ## Defining equations -/

/-- DB-04 M1. -/
theorem empty_eq :
    ∀ {value reason body : Type},
      (Agent.empty : Agent.Agent value reason body) =
        Agent.Agent.mk Promise.Table.empty Promise.Reactions.empty [] Jobs.Queue.empty [] 0
          Jobs.Active.checkpoint none [] := by
  intros; rfl

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
theorem callFunctions_none :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value),
      a.functions.find? pick = none → Agent.callFunctions a pick result = a := by
  intro value reason body a pick result h
  unfold callFunctions
  rw [h]

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
theorem resolve_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value),
      Agent.resolve a cap v =
        Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
          (Except.ok v) := by
  intros; rfl

/-- DB-04 M1. -/
theorem reject_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason),
      Agent.reject a cap r =
        Agent.callFunctions a (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject)
          (Except.error r) := by
  intros; rfl

/-- DB-04 M1. -/
theorem mintFor_true :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.mintFor a true = ((Agent.newPromise a).1, some (Agent.newPromise a).2) := by
  intros; rfl

/-- DB-04 M1. -/
theorem mintFor_false :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.mintFor a false = (a, none) := by
  intros; rfl

/-- Minting a derived capability allocates at the cursor and keeps every
earlier cell's state. -/
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

/-- DB-04 M1. -/
theorem perform_missing :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      a.table.get promise = none →
        Agent.perform a promise onFulfilled onRejected derive = (a, none) := by
  intro value reason body a promise onFulfilled onRejected derive h
  unfold perform
  rw [h]

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
theorem markHandled_eq :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      Agent.markHandled a promise =
        { a with table := Promise.Table.markHandled a.table promise } := by
  intros; rfl

/-- DB-04 M1. -/
theorem reactionOf_held :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (r : Promise.Reaction body),
      a.held.find? (fun (x : Promise.Reaction body) => x.id == job.reaction) = some r →
        Agent.reactionOf a job = some r := by
  intro value reason body a job r h
  unfold reactionOf
  rw [h]

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
theorem startJob_empty :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.queue.pending = [] → Agent.startJob a = (a, none) := by
  intro value reason body a hq
  unfold startJob
  rw [hq]
  cases a.active <;> rfl

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
theorem finishJob_idle :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value),
      a.running = none → Agent.finishJob a decision = a := by
  intro value reason body a decision h
  unfold finishJob
  rw [h]
  cases a.active <;> rfl

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
theorem enterScript_checkpoint :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active = Jobs.Active.checkpoint →
        Agent.enterScript a = { a with active := Jobs.Active.script } := by
  intro value reason body a h
  unfold enterScript
  rw [h]

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
theorem leaveScript_script :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      a.active = Jobs.Active.script →
        Agent.leaveScript a = { a with active := Jobs.Active.checkpoint } := by
  intro value reason body a h
  unfold leaveScript
  rw [h]

/-- DB-04 M1. -/
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

/-! ## `Minted` and the fourteen clauses of `WF` -/

/-- The capability's resolving functions are stored. -/
def Minted {value reason body : Type} (a : Agent value reason body) (cap : Promise.Capability) :
    Prop :=
  ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject = cap.reject ∧ f.promise = cap.promise

/-- DB-04 M1. -/
theorem Minted_iff :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability),
      Agent.Minted a cap ↔
        ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject = cap.reject ∧
          f.promise = cap.promise := by
  intros; exact Iff.rfl

/-- The agent's invariant. -/
structure WF {value reason body : Type} (a : Agent value reason body) : Prop where
  tableNodup : (a.table.entries.map Prod.fst).Nodup
  tableBelow : ∀ e ∈ a.table.entries, e.1 < a.table.next
  functionsBelow : ∀ f ∈ a.functions, f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction
  functionsAllocated : ∀ f ∈ a.functions, (a.table.getCell f.promise).isSome = true
  resolvedSettled : ∀ f ∈ a.functions, f.alreadyResolved = true →
    Promise.Table.isPending a.table f.promise = false
  reactionsBelow : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
    r.id < a.reactions.next
  queueBelow : ∀ j ∈ a.queue.pending, j.reaction < a.reactions.next
  paired : a.reactions.fulfill.map Promise.Reaction.id = a.reactions.reject.map Promise.Reaction.id
  functionsNodup : (a.functions.map Promise.ResolvingFunctions.resolve).Nodup
  heldDistinct : (a.held.map Promise.Reaction.id ++ a.reactions.fulfill.map Promise.Reaction.id).Nodup
  queuedKnown : ∀ j ∈ a.queue.pending, (Agent.reactionOf a j).isSome = true
  runningActive :
    (∀ j : Agent.Job value reason, a.running = some j →
        a.active = Jobs.Active.job j.reaction) ∧
      (∀ s : Nat, a.active = Jobs.Active.job s → a.running.isSome = true)
  capabilityStored :
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      ∀ cap : Promise.Capability, r.capability = some cap → Agent.Minted a cap
  settlementsCoherent :
    (a.settlements.map Prod.fst).Nodup ∧
      (∀ (p : Nat) (v : value), (p, Except.ok v) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.fulfilled v)) ∧
      (∀ (p : Nat) (r : reason), (p, Except.error r) ∈ a.settlements →
        Promise.Table.get a.table p = some (Promise.State.rejected r))

/-- DB-04 M1. -/
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

/-! ## Views onto the landed store-level operations -/

/-- DB-04 M1. -/
theorem settleAndTrigger_table :
    ∀ {value reason body : Type} (t : Promise.Table value reason)
      (rs : Promise.Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
      (id : Nat) (result : Except reason value),
      (Promise.Table.settleAndTrigger t rs q id result).1 = Promise.Table.settle t id result := by
  intro value reason body t rs q id result
  unfold Promise.Table.settleAndTrigger Promise.Table.settle
  cases Promise.Table.isPending t id <;> rfl

/-- DB-04 M2. -/
theorem settle_ok_fulfillPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (v : value),
      ((Agent.settle a promise (Except.ok v)).table,
          (Agent.settle a promise (Except.ok v)).reactions,
          (Agent.settle a promise (Except.ok v)).queue) =
        Promise.fulfillPromise a.table a.reactions a.queue promise v := by
  intros; rfl

/-- DB-04 M2. -/
theorem settle_error_rejectPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (r : reason),
      ((Agent.settle a promise (Except.error r)).table,
          (Agent.settle a promise (Except.error r)).reactions,
          (Agent.settle a promise (Except.error r)).queue) =
        Promise.rejectPromise a.table a.reactions a.queue promise r := by
  intros; rfl

/-- DB-04 M2. -/
theorem settle_settlements :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (result : Except reason value),
      (Agent.settle a promise result).settlements =
        (Promise.Table.settleTraced a.table a.settlements promise result).2 := by
  intros; rfl

/-- DB-04 M1. -/
theorem newPromise_capability :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      (Agent.newPromise a).2 = (Promise.newPromiseCapability a.table a.nextFunction).2 := by
  intros; rfl

/-- DB-04 M1. -/
theorem markHandled_table :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat),
      (Agent.markHandled a promise).table = Promise.Table.markHandled a.table promise := by
  intros; rfl

/-- DB-04 M1. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
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

/-! ## D46: `react` followed by `resolve` enqueues the new reaction's job -/

/-- DB-04 M2. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M2. -/
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

/-- DB-04 M2. -/
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

/-! ## D17 and run to completion at the agent -/

/-- DB-04 M1. -/
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

/-- DB-04 M1. -/
theorem startJob_running :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (s : Nat),
      a.active = Jobs.Active.job s → Agent.startJob a = (a, none) := by
  intro value reason body a s h
  unfold startJob
  rw [h]

end Whatwg.Ecma262.Agent
