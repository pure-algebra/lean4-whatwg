import Whatwg.Ecma262.Agent

/-!
# Laws of the ECMAScript agent

Owner: promise slice Q5 (ruling R-W3), graph `PROMISE-PG-AGENT`
(`docs/PROMISE-AGENT-DAG.md`), at the surface
`test/contracts/promise-agent-q5.contract.md` freezes (ruling R-W13). This
module is builder slice B2; its battery is
`WhatwgTest/Ecma262/AgentLaws.lean`. Slice B1, `Whatwg/Ecma262/Agent.lean`,
owns the agent record, its nine operations, the step and the definitions of
`Minted` and `WF`; this module owns every other lemma about `WF`.

Landed here: the world order `Le`; the certificate, pre and post of every
operation; the judgment `Implements` with one `*_implements` theorem per
operation and `implements` over all nine; `WF.empty`, `WF.step` and
`WF.runOps`, so every agent a run reaches from `Agent.empty` is well formed;
runs of the step (`Op.started`, `runOps`) with the landed FIFO law lifted to
them; and the other lifted laws of the contract's section 9.

## The adequacy shape

Each operation's law has four parts: a well-formed agent `a`, a request `op`
that `pre a op c` admits, the step, and the answer in the post. The step is
total, so an admitted request always steps and there is no frontier. The
later agent is the stepped one, `(step a op).1`, and `Implements op` says
three things of it: it is above `a` in `Le`, it is well formed again, and
`post` holds of it and the answer `(step a op).2`. The middle conjunct is
the operation's `WF` preservation.

`pre` is enabledness, so under it the step takes no disabled branch, with one
exception: the pre of `resolve` and `reject` is `Minted a cap`, which admits a
capability whose functions already fired, because a program may call
"resolve" twice. That step is inert and the post still holds, by
`WF.resolvedSettled` and `WF.functionsAllocated`. `Cert` is `Unit`: the table
is homogeneous in `value` and `reason`, so no ghost certificate is needed.
The posts are facts at the answering agent. The activation posts of
`startJob` and `finishJob` hold there only, because a job's activation ends;
every other post is upward closed in `Le`.

## What the shape is a reading of

The shape is lean4-effect4's handler-adequacy judgment, read in its source at
commit `b9d0d19f` (`src/Effect4/Laws/Program/Typed/Adequacy.lean`, with
`src/Effect4/Laws/Effects/Protocol.lean`). What follows is a reading of that
source, not a claim about that repository, its intent or its gate. There,
`StoreImplements root op` says that for every world and certificate, a store
that `StoreTyped` types and a request that `storePre` admits step
(`syncOpStep op w.state = some (st', ans)`), and some later world `w'` over
`st'`, above `w` in `World.leHost`, is typed again with the answer in
`storePost`. Read that way:

- `Agent.WF` is `StoreTyped`;
- `Agent.Le` is `World.leHost`;
- `Agent.Cert` is `StoreCert op`;
- `Agent.pre` and `Agent.post` are `storePre` and `storePost`;
- `Agent.Implements op` is `StoreImplements root op`, and the nine
  `*_implements` theorems are its per-row `*_implements`.

Three differences, each a reading. Their step is partial and ours is total,
so their `∃ st' ans` is our step's own components. Their later world is any
`w'` above `w` over the new store; ours is the stepped agent, with
`Le a (step a op).1` as a conjunct. Their typing is "every value fits its
declared type" over a heterogeneous store; ours is identity and reference
coherence over a homogeneous one. `Cert`, `pre` and `post` have the types of
`Protocol`'s `Cert`, `pre` and `post` at the face's signature, and `Le`,
`Le.refl` and `Le.trans` those of `WorldOrder`'s `le`, `refl` and `trans`.
No generic law is copied: the program-level `run_adequate` over `Protocol`
waits until that module is in the `effects` package and this repository moves
its pin (R-W3), because a second owner of a generic law is what
`Whatwg/AGENTS.md` forbids.

## Masks

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no declaration here
spells a mask. A statement is DB-04 M2 when it observes the order of the
settlement trace or of the job queue, and DB-04 M1 otherwise. `Le.trace` is a
prefix of the settlement order, so every law that concludes `Le` is DB-04 M2:
`Le.refl`, `Le.trans`, `Le.step`, `Implements_iff`, the nine `*_implements`
and `implements`. `runOps_cons`, `runOps_fifo` and `runOps_fifoRequirement`
observe start order and `settle_trace` settlement order, so they are DB-04 M2
too. Every other law here is DB-04 M1.

## Anchors and claim scope

Anchor aliases (NEWCAP, RESOLVING, FULFILL, REJECT, TRIGGER, THEN, REACTJOB,
RUNCOND, ONEJOB, ORDER, COMPLETE, REACT, HANDLEDOP) expand through
`docs/PROMISE-DAG.md`'s alias table. Byte spans are 0-based, ends exclusive,
into `vendor/ecma262-0248456c/spec.html`, or into
`vendor/whatwg-webidl-a652053f/index.bs` for a Web IDL row. Every census row
cited here anchors a declaration and is never a numerator; no coverage state
moves.

Not modelled, as in `Whatwg/Ecma262/Agent.lean`: thenable adoption (`G-05`),
so `WF.resolvedSettled` holds only while adoption stays out, and the posts of
`resolve` and `reject` lean on it (the `G-05` obligation of R-W3); the
rejection tracker (the `G-02` remainder); job callbacks (the `G-07`
remainder). `held` never shrinks and `finishJob` leaves a reaction's phase at
`.queued`.

Layering (DB-11): this module imports `Whatwg.Ecma262.Agent` and nothing
else, so no `Effects` module and no `Whatwg.Infra` module (R-W3). A lemma the
battery does not ascribe is private, except the seventeen that ruling R-W20(c)
published for `Whatwg/Ecma262/AgentInvariant.lean`.
-/

namespace Whatwg.Ecma262.Agent

/-! ## 1. The world order

What a later agent keeps of an earlier one. Every operation moves a
well-formed agent up this order (`Le.step`, section 13). -/

/-- The world order of the adequacy shape: the earlier agent's allocated cells
stay allocated, its settled states never change, its handled bits never clear,
its three cursors grow, every stored resolving-function record survives with
its three identities, and its settlement trace is a prefix of the later one.
Adequacy definition, read as lean4-effect4's `World.leHost`; its eight clauses
are frozen by their projections. -/
structure Le {value reason body : Type} (a a' : Agent value reason body) : Prop where
  /-- An allocated cell stays allocated. -/
  allocated : ∀ (p : Nat), (a.table.getCell p).isSome = true → (a'.table.getCell p).isSome = true
  /-- A settled state never changes. -/
  settled : ∀ (p : Nat) (s : Promise.State value reason), a.table.get p = some s →
    s ≠ Promise.State.pending → a'.table.get p = some s
  /-- The handled bit never clears. -/
  handled : ∀ (p : Nat), (a.table.getCell p).map Promise.Cell.handled = some true →
    (a'.table.getCell p).map Promise.Cell.handled = some true
  /-- The table cursor grows. -/
  tableNext : a.table.next ≤ a'.table.next
  /-- The registration cursor grows. -/
  reactionsNext : a.reactions.next ≤ a'.reactions.next
  /-- The function cursor grows. -/
  functionCursor : a.nextFunction ≤ a'.nextFunction
  /-- Every stored resolving-function record survives with its `[[Resolve]]`,
  `[[Reject]]` and `[[Promise]]` identities; its one-shot marker may change. -/
  minted : ∀ f ∈ a.functions, ∃ g ∈ a'.functions,
    g.resolve = f.resolve ∧ g.reject = f.reject ∧ g.promise = f.promise
  /-- The settlement trace only grows, at its end. -/
  trace : a.settlements <+: a'.settlements

/-- Every agent is later than itself (the type of `WorldOrder`'s `refl`).
Adequacy law; DB-04 M2, through `Le.trace`. -/
theorem Le.refl :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body), Agent.Le a a := by
  intro value reason body a
  exact ⟨fun _ h => h, fun _ _ h _ => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, fun f hf => ⟨f, hf, rfl, rfl, rfl⟩, List.prefix_refl _⟩

/-- Later than later is later (the type of `WorldOrder`'s `trans`). Adequacy
law; DB-04 M2, through `Le.trace`. -/
theorem Le.trans :
    ∀ {value reason body : Type} {a b c : Agent.Agent value reason body},
      Agent.Le a b → Agent.Le b c → Agent.Le a c := by
  intro value reason body a b c h₁ h₂
  exact ⟨fun p h => h₂.allocated p (h₁.allocated p h),
    fun p s h hs => h₂.settled p s (h₁.settled p s h hs) hs,
    fun p h => h₂.handled p (h₁.handled p h),
    Nat.le_trans h₁.tableNext h₂.tableNext, Nat.le_trans h₁.reactionsNext h₂.reactionsNext,
    Nat.le_trans h₁.functionCursor h₂.functionCursor,
    fun f hf => by
      obtain ⟨g, hg, h1, h2, h3⟩ := h₁.minted f hf
      obtain ⟨g', hg', h1', h2', h3'⟩ := h₂.minted g hg
      exact ⟨g', hg', h1'.trans h1, h2'.trans h2, h3'.trans h3⟩,
    List.IsPrefix.trans h₁.trace h₂.trace⟩

/-! ## 2. The certificate, the pre and the post

The content of each is frozen by the eighteen `pre_*` and `post_*` equations,
each `Iff.rfl` of the definition, and `Implements` by `Implements_iff`. -/

/-- The certificate a request carries: `Unit`, because the table is
homogeneous in `value` and `reason`, so no ghost certificate is needed.
Adequacy definition, read as `StoreCert op`; an `abbrev`. -/
abbrev Cert {value reason body : Type} (_ : Op value reason body) : Type := Unit

/-- The requests the adequacy shape admits: each operation's enabledness (the
contract's section 5), except that `resolve` and `reject` admit any minted
capability, its functions fired or not. Adequacy definition, read as
`storePre`; the nine `pre_*` equations fix it. -/
def pre {value reason body : Type} (a : Agent value reason body) :
    (op : Op value reason body) → Cert op → Prop
  | .newPromise, _ => True
  | .resolve cap _, _ => Minted a cap
  | .reject cap _, _ => Minted a cap
  | .perform p _ _ _, _ => (a.table.get p).isSome = true
  | .markHandled p, _ => (a.table.get p).isSome = true
  | .startJob, _ => a.active = Jobs.Active.checkpoint ∧ a.queue.pending ≠ []
  | .finishJob _, _ => ∃ s, a.active = Jobs.Active.job s
  | .enterScript, _ => a.active = Jobs.Active.checkpoint
  | .leaveScript, _ => a.active = Jobs.Active.script

/-- What an answer satisfies at the answering agent `a`: a new capability is
minted and pending; a resolved or rejected capability's promise is settled; a
performed promise is handled, with the derived capability minted and pending
when one was asked for; a marked promise is handled; a started job is the
running job at its own serial; a finished job leaves a checkpoint with nothing
running; a script operation reaches its activation. Adequacy definition, read
as `storePost`; the nine `post_*` equations fix it. -/
def post {value reason body : Type} (a : Agent value reason body) :
    (op : Op value reason body) → Cert op → op.Answer → Prop
  | .newPromise, _, cap => Minted a cap ∧ a.table.get cap.promise = some Promise.State.pending
  | .resolve cap _, _, _ =>
      ∃ s, a.table.get cap.promise = some s ∧ s ≠ Promise.State.pending
  | .reject cap _, _, _ =>
      ∃ s, a.table.get cap.promise = some s ∧ s ≠ Promise.State.pending
  | .perform p _ _ d, _, ans =>
      (a.table.getCell p).map Promise.Cell.handled = some true ∧
        (d = true → ∃ cap, ans = some (some cap) ∧ Minted a cap ∧
          a.table.get cap.promise = some Promise.State.pending) ∧
        (d = false → ans = some none)
  | .markHandled p, _, _ => (a.table.getCell p).map Promise.Cell.handled = some true
  | .startJob, _, ans =>
      ∃ j, ans = some (j, (reactionOf a j).bind Promise.Reaction.handler) ∧
        a.active = Jobs.Active.job j.reaction ∧ a.running = some j
  | .finishJob _, _, _ => a.active = Jobs.Active.checkpoint ∧ a.running = none
  | .enterScript, _, _ => a.active = Jobs.Active.script
  | .leaveScript, _, _ => a.active = Jobs.Active.checkpoint

/-- The handler-adequacy judgment of one operation: from every well-formed
agent and every request its pre admits, the step reaches an agent that is
later in `Le`, well formed again, and holds the answer in the post. Adequacy
definition, read as `StoreImplements root op`; `Implements_iff` fixes it. -/
def Implements {value reason body : Type} (op : Op value reason body) : Prop :=
  ∀ (a : Agent value reason body) (c : Cert op), WF a → pre a op c →
    Le a (step a op).1 ∧ WF (step a op).1 ∧ post (step a op).1 op c (step a op).2

/-- `newPromise` is always admitted (NEWCAP). Defining equation; DB-04 M1. -/
theorem pre_newPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body)),
      Agent.pre a Agent.Op.newPromise c ↔ True := by
  intros; exact Iff.rfl

/-- `resolve` is admitted through any capability this agent minted, its
functions fired or not (RESOLVING; Web IDL `op.resolve`). Defining equation;
DB-04 M1. -/
theorem pre_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value)
      (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)),
      Agent.pre a (Agent.Op.resolve cap v) c ↔ Agent.Minted a cap := by
  intros; exact Iff.rfl

/-- `reject` is admitted through any capability this agent minted, its
functions fired or not (RESOLVING; Web IDL `op.reject`). Defining equation;
DB-04 M1. -/
theorem pre_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason)
      (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)),
      Agent.pre a (Agent.Op.reject cap r) c ↔ Agent.Minted a cap := by
  intros; exact Iff.rfl

/-- `perform` is admitted on an allocated promise (THEN, where the
specification asserts `IsPromise`). Defining equation; DB-04 M1. -/
theorem pre_perform :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool)
      (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
        Agent.Op value reason body)),
      Agent.pre a (Agent.Op.perform promise onFulfilled onRejected derive) c ↔
        (a.table.get promise).isSome = true := by
  intros; exact Iff.rfl

/-- `markHandled` is admitted on an allocated promise (HANDLEDOP). Defining
equation; DB-04 M1. -/
theorem pre_markHandled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body)),
      Agent.pre a (Agent.Op.markHandled promise) c ↔ (a.table.get promise).isSome = true := by
  intros; exact Iff.rfl

/-- `startJob` is admitted at a checkpoint with a job queued (RUNCOND, ONEJOB).
Defining equation; DB-04 M1. -/
theorem pre_startJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body)),
      Agent.pre a Agent.Op.startJob c ↔
        a.active = Jobs.Active.checkpoint ∧ a.queue.pending ≠ [] := by
  intros; exact Iff.rfl

/-- `finishJob` is admitted while the activation is a job (REACTJOB, COMPLETE).
Defining equation; DB-04 M1. -/
theorem pre_finishJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value)
      (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)),
      Agent.pre a (Agent.Op.finishJob decision) c ↔ ∃ s : Nat, a.active = Jobs.Active.job s := by
  intros; exact Iff.rfl

/-- `enterScript` is admitted at a checkpoint (RUNCOND). Defining equation;
DB-04 M1. -/
theorem pre_enterScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)),
      Agent.pre a Agent.Op.enterScript c ↔ a.active = Jobs.Active.checkpoint := by
  intros; exact Iff.rfl

/-- `leaveScript` is admitted in a script (RUNCOND). Defining equation; DB-04
M1. -/
theorem pre_leaveScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)),
      Agent.pre a Agent.Op.leaveScript c ↔ a.active = Jobs.Active.script := by
  intros; exact Iff.rfl

/-- After `newPromise`, the answered capability is minted and its promise is
pending (NEWCAP, RESOLVING). Defining equation; DB-04 M1. -/
theorem post_newPromise :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body))
      (cap : Promise.Capability),
      Agent.post a Agent.Op.newPromise c cap ↔
        Agent.Minted a cap ∧ a.table.get cap.promise = some Promise.State.pending := by
  intros; exact Iff.rfl

/-- After `resolve`, the capability's promise is settled, fulfilled or
rejected (RESOLVING, FULFILL; Web IDL `op.resolve`). Defining equation; DB-04
M1. -/
theorem post_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value)
      (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)) (ans : Unit),
      Agent.post a (Agent.Op.resolve cap v) c ans ↔
        ∃ s : Promise.State value reason, a.table.get cap.promise = some s ∧
          s ≠ Promise.State.pending := by
  intros; exact Iff.rfl

/-- After `reject`, the capability's promise is settled, fulfilled or rejected
(RESOLVING, REJECT; Web IDL `op.reject`). Defining equation; DB-04 M1. -/
theorem post_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason)
      (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)) (ans : Unit),
      Agent.post a (Agent.Op.reject cap r) c ans ↔
        ∃ s : Promise.State value reason, a.table.get cap.promise = some s ∧
          s ≠ Promise.State.pending := by
  intros; exact Iff.rfl

/-- After `perform`, the promise is handled (THEN step 12); with `derive` the
answer carries a capability that is minted and pending (REACT step 6), and
without it the answer is `some none`. Defining equation; DB-04 M1. -/
theorem post_perform :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool)
      (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
        Agent.Op value reason body))
      (ans : Option (Option Promise.Capability)),
      Agent.post a (Agent.Op.perform promise onFulfilled onRejected derive) c ans ↔
        (a.table.getCell promise).map Promise.Cell.handled = some true ∧
          (derive = true → ∃ cap : Promise.Capability, ans = some (some cap) ∧
            Agent.Minted a cap ∧ a.table.get cap.promise = some Promise.State.pending) ∧
          (derive = false → ans = some none) := by
  intros; exact Iff.rfl

/-- After `markHandled`, the promise's handled bit is set (HANDLEDOP).
Defining equation; DB-04 M1. -/
theorem post_markHandled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body))
      (ans : Unit),
      Agent.post a (Agent.Op.markHandled promise) c ans ↔
        (a.table.getCell promise).map Promise.Cell.handled = some true := by
  intros; exact Iff.rfl

/-- After `startJob`, the answer is some job with its record's handler, and
that job is the running job at the serial of its own reaction identity
(RUNCOND, ONEJOB). Defining equation; DB-04 M1. -/
theorem post_startJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body))
      (ans : Option (Agent.Job value reason × Option body)),
      Agent.post a Agent.Op.startJob c ans ↔
        ∃ j : Agent.Job value reason,
          ans = some (j, (Agent.reactionOf a j).bind Promise.Reaction.handler) ∧
            a.active = Jobs.Active.job j.reaction ∧ a.running = some j := by
  intros; exact Iff.rfl

/-- After `finishJob`, the agent is at a checkpoint with no job running
(COMPLETE). It lifts the landed `Jobs.completeJob_job`. Defining equation;
DB-04 M1. -/
theorem post_finishJob :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value)
      (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)) (ans : Unit),
      Agent.post a (Agent.Op.finishJob decision) c ans ↔
        a.active = Jobs.Active.checkpoint ∧ a.running = none := by
  intros; exact Iff.rfl

/-- After `enterScript`, the agent is in a script (RUNCOND). Defining equation;
DB-04 M1. -/
theorem post_enterScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)) (ans : Unit),
      Agent.post a Agent.Op.enterScript c ans ↔ a.active = Jobs.Active.script := by
  intros; exact Iff.rfl

/-- After `leaveScript`, the agent is at a checkpoint (RUNCOND). Defining
equation; DB-04 M1. -/
theorem post_leaveScript :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)) (ans : Unit),
      Agent.post a Agent.Op.leaveScript c ans ↔ a.active = Jobs.Active.checkpoint := by
  intros; exact Iff.rfl

/-- The judgment `Implements op`, spelled out: from a well-formed agent and an
admitted request, the stepped agent is later, well formed, and holds the
answer in the post. Defining equation; DB-04 M2, through `Le.trace`. -/
theorem Implements_iff :
    ∀ {value reason body : Type} (op : Agent.Op value reason body),
      Agent.Implements op ↔
        ∀ (a : Agent.Agent value reason body) (c : Agent.Cert op), Agent.WF a →
          Agent.pre a op c →
          Agent.Le a (Agent.step a op).1 ∧ Agent.WF (Agent.step a op).1 ∧
            Agent.post (Agent.step a op).1 op c (Agent.step a op).2 := by
  intros; exact Iff.rfl

/-! ## 3. Lemmas about the promise table

The landed table operations, at any identity: what a settle, a mark and an
allocation keep. The battery ascribes none of them; eleven are public since
ruling R-W20(c). -/

/-- A map that keeps every key commutes with a lookup by key. -/
theorem find?_map_fst {α : Type} (l : List (Nat × α)) (g : Nat × α → Nat × α)
    (hg : ∀ e, (g e).1 = e.1) (q : Nat) :
    List.find? (fun e => e.1 == q) (l.map g) = (List.find? (fun e => e.1 == q) l).map g := by
  rw [List.find?_map]
  have : ((fun e : Nat × α => e.1 == q) ∘ g) = (fun e => e.1 == q) := by
    funext e
    show ((g e).1 == q) = (e.1 == q)
    rw [hg e]
  rw [this]

/-- A settle keeps the identities and the cursor. -/
private theorem settle_ids {value reason : Type} (t : Promise.Table value reason) (id : Nat)
    (result : Except reason value) :
    (Promise.Table.settle t id result).entries.map Prod.fst = t.entries.map Prod.fst ∧
      (Promise.Table.settle t id result).next = t.next := by
  unfold Promise.Table.settle
  cases Promise.Table.isPending t id with
  | false => exact ⟨rfl, rfl⟩
  | true =>
      refine ⟨?_, rfl⟩
      show (t.entries.map _).map Prod.fst = _
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      show (if _ then _ else e).1 = e.1
      split <;> rfl

/-- A settle keeps, at every identity, whether a cell is allocated and its
handled bit. -/
theorem getCell_settle {value reason : Type} (t : Promise.Table value reason)
    (id q : Nat) (result : Except reason value) :
    (Promise.Table.getCell (Promise.Table.settle t id result) q).isSome =
        (Promise.Table.getCell t q).isSome ∧
      (Promise.Table.getCell (Promise.Table.settle t id result) q).map Promise.Cell.handled =
        (Promise.Table.getCell t q).map Promise.Cell.handled := by
  unfold Promise.Table.settle
  cases Promise.Table.isPending t id with
  | false => exact ⟨rfl, rfl⟩
  | true =>
      show (Option.map Prod.snd (List.find? (fun e => e.1 == q) (t.entries.map _))).isSome =
          (Option.map Prod.snd (List.find? (fun e => e.1 == q) t.entries)).isSome ∧
        Option.map Promise.Cell.handled
            (Option.map Prod.snd (List.find? (fun e => e.1 == q) (t.entries.map _))) =
          Option.map Promise.Cell.handled
            (Option.map Prod.snd (List.find? (fun e => e.1 == q) t.entries))
      rw [find?_map_fst t.entries]
      · cases List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == q) t.entries with
        | none => exact ⟨rfl, rfl⟩
        | some e =>
            refine ⟨rfl, ?_⟩
            show some (if e.1 == id then _ else e).2.handled = some e.2.handled
            split <;> rfl
      · intro e
        show (if _ then _ else e).1 = e.1
        split <;> rfl

/-- A settle changes no state at another identity. -/
theorem settle_get_other {value reason : Type} (t : Promise.Table value reason)
    (id q : Nat) (result : Except reason value) (hne : q ≠ id) :
    Promise.Table.get (Promise.Table.settle t id result) q = Promise.Table.get t q := by
  unfold Promise.Table.settle
  cases Promise.Table.isPending t id with
  | false => rfl
  | true =>
      show Option.map Promise.Cell.state (Option.map Prod.snd
        (List.find? (fun e => e.1 == q) (t.entries.map _))) =
          Option.map Promise.Cell.state (Option.map Prod.snd
            (List.find? (fun e => e.1 == q) t.entries))
      rw [find?_map_fst t.entries]
      · cases hf : List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == q)
            t.entries with
        | none => rfl
        | some e =>
            have hq : e.1 = q := beq_iff_eq.mp
              (List.find?_some (p := fun (x : Nat × Promise.Cell value reason) => x.1 == q) hf)
            have hid : (e.1 == id) = false := by
              cases hb : (e.1 == id) with
              | false => rfl
              | true => exact absurd ((beq_iff_eq.mp hb).symm.trans hq).symm hne
            show some (if _ then _ else e).2.state = some e.2.state
            rw [if_neg (by rw [hid]; exact Bool.false_ne_true)]
      · intro e
        show (if _ then _ else e).1 = e.1
        split <;> rfl

/-- A settle leaves a non-pending identity non-pending. -/
private theorem settle_notPending {value reason : Type} (t : Promise.Table value reason)
    (id q : Nat) (result : Except reason value) (h : Promise.Table.isPending t q = false) :
    Promise.Table.isPending (Promise.Table.settle t id result) q = false := by
  cases hq : decide (q = id) with
  | true =>
      have hqe : q = id := of_decide_eq_true hq
      subst hqe
      have hnp : Promise.Table.get t q ≠ some Promise.State.pending := fun hp =>
        Bool.false_ne_true (h.symm.trans ((Promise.Table.isPending_iff t q).mpr hp))
      rw [Promise.Table.settle_other t q result hnp]
      exact h
  | false =>
      have hne : q ≠ id := of_decide_eq_false hq
      unfold Promise.Table.isPending
      rw [settle_get_other t id q result hne]
      exact h

/-- After a settle at `p`, `p` is not pending. -/
private theorem isPending_settle_self {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) (result : Except reason value) :
    Promise.Table.isPending (Promise.Table.settle t p result) p = false := by
  cases hp : Promise.Table.isPending t p with
  | false => exact settle_notPending t p p result hp
  | true =>
      unfold Promise.Table.isPending
      rw [Promise.Table.settle_assert t p result ((Promise.Table.isPending_iff t p).mp hp)]
      cases result <;> rfl

/-- After a settle at `p`, an allocated `p` is settled. -/
private theorem settle_settled {value reason : Type} (t : Promise.Table value reason) (p : Nat)
    (result : Except reason value) (h : (Promise.Table.getCell t p).isSome = true) :
    ∃ s, Promise.Table.get (Promise.Table.settle t p result) p = some s ∧
      s ≠ Promise.State.pending := by
  cases hp : Promise.Table.isPending t p with
  | true =>
      have hpend := (Promise.Table.isPending_iff t p).mp hp
      rw [Promise.Table.settle_assert t p result hpend]
      cases result with
      | ok v => exact ⟨_, rfl, fun e => by cases e⟩
      | error r => exact ⟨_, rfl, fun e => by cases e⟩
  | false =>
      have hnp : Promise.Table.get t p ≠ some Promise.State.pending := fun hq =>
        Bool.false_ne_true (hp.symm.trans ((Promise.Table.isPending_iff t p).mpr hq))
      rw [Promise.Table.settle_other t p result hnp]
      unfold Promise.Table.get
      cases hc : Promise.Table.getCell t p with
      | none => rw [hc] at h; cases h
      | some c =>
          refine ⟨c.state, rfl, fun e => hnp ?_⟩
          unfold Promise.Table.get
          rw [hc, ← e]
          rfl

/-- An allocated promise that is not pending is settled. -/
private theorem settled_of_notPending {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) (h : (Promise.Table.getCell t p).isSome = true)
    (hp : Promise.Table.isPending t p = false) :
    ∃ s, Promise.Table.get t p = some s ∧ s ≠ Promise.State.pending := by
  have hnp : Promise.Table.get t p ≠ some Promise.State.pending := fun hq =>
    Bool.false_ne_true (hp.symm.trans ((Promise.Table.isPending_iff t p).mpr hq))
  unfold Promise.Table.get
  cases hc : Promise.Table.getCell t p with
  | none => rw [hc] at h; cases h
  | some c =>
      refine ⟨c.state, rfl, fun e => hnp ?_⟩
      unfold Promise.Table.get
      rw [hc, ← e]
      rfl

/-- The cell a mark leaves at `q`: the old one, with the bit set when `q` is
the marked identity. -/
theorem getCell_markHandled {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) :
    Promise.Table.getCell (Promise.Table.markHandled t p) q =
      (Promise.Table.getCell t q).map
        (fun c => if q == p then Promise.Cell.mk c.state true else c) := by
  unfold Promise.Table.getCell Promise.Table.markHandled
  rw [List.find?_map]
  have hcomp : ((fun (e : Nat × Promise.Cell value reason) => e.1 == q) ∘
      (fun (e : Nat × Promise.Cell value reason) =>
        if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e)) =
      (fun (e : Nat × Promise.Cell value reason) => e.1 == q) := by
    funext e
    show ((if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).1 == q) = (e.1 == q)
    cases (e.1 == p) <;> rfl
  rw [hcomp]
  cases hf : List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == q) t.entries with
  | none => rfl
  | some e =>
      have hq : e.1 = q := beq_iff_eq.mp
        (List.find?_some (p := fun (x : Nat × Promise.Cell value reason) => x.1 == q) hf)
      show some (if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).2 =
        some (if q == p then Promise.Cell.mk e.2.state true else e.2)
      rw [hq]
      cases (q == p) <;> rfl

/-- A mark allocates and frees nothing. -/
theorem markHandled_isSome {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) :
    (Promise.Table.getCell (Promise.Table.markHandled t p) q).isSome =
      (Promise.Table.getCell t q).isSome := by
  rw [getCell_markHandled]
  cases Promise.Table.getCell t q <;> rfl

/-- A mark clears no handled bit. -/
private theorem markHandled_handled {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) (h : (Promise.Table.getCell t q).map Promise.Cell.handled = some true) :
    (Promise.Table.getCell (Promise.Table.markHandled t p) q).map Promise.Cell.handled =
      some true := by
  rw [getCell_markHandled]
  cases hc : Promise.Table.getCell t q with
  | none => rw [hc] at h; cases h
  | some c =>
      rw [hc] at h
      show some (if q == p then Promise.Cell.mk c.state true else c).handled = some true
      cases (q == p) with
      | true => rfl
      | false => exact h

/-- A mark changes no pending flag. -/
private theorem markHandled_isPending {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) :
    Promise.Table.isPending (Promise.Table.markHandled t p) q = Promise.Table.isPending t q := by
  unfold Promise.Table.isPending
  rw [markHandled_get]

/-- A mark keeps the identities and the cursor. -/
private theorem markHandled_ids {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) :
    (Promise.Table.markHandled t p).entries.map Prod.fst = t.entries.map Prod.fst ∧
      (Promise.Table.markHandled t p).next = t.next := by
  refine ⟨?_, rfl⟩
  show (t.entries.map _).map Prod.fst = _
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  show (if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).1 = e.1
  cases (e.1 == p) <;> rfl

/-- Allocation keeps every old cell, at any identity. -/
theorem getCell_fresh {value reason : Type} (t : Promise.Table value reason)
    (o : Promise.State value reason) (p : Nat) (c : Promise.Cell value reason)
    (h : Promise.Table.getCell t p = some c) :
    Promise.Table.getCell (Promise.Table.fresh t o).1 p = some c := by
  show Option.map Prod.snd (List.find? (fun e => e.1 == p)
    (t.entries ++ [(t.next, Promise.Cell.mk o false)])) = some c
  rw [List.find?_append]
  unfold Promise.Table.getCell at h
  cases hf : List.find? (fun (e : Nat × Promise.Cell value reason) => e.1 == p) t.entries with
  | none => rw [hf] at h; cases h
  | some e => rw [hf] at h; exact h

/-- Allocation keeps every old state, at any identity. -/
theorem get_fresh {value reason : Type} (t : Promise.Table value reason)
    (o : Promise.State value reason) (p : Nat) (s : Promise.State value reason)
    (h : Promise.Table.get t p = some s) :
    Promise.Table.get (Promise.Table.fresh t o).1 p = some s := by
  unfold Promise.Table.get at h ⊢
  cases hc : Promise.Table.getCell t p with
  | none => rw [hc] at h; cases h
  | some c =>
      rw [hc] at h
      rw [getCell_fresh t o p c hc]
      exact h

/-- Allocation keeps every allocated identity allocated. -/
theorem getCell_fresh_isSome {value reason : Type} (t : Promise.Table value reason)
    (o : Promise.State value reason) (p : Nat) (h : (Promise.Table.getCell t p).isSome = true) :
    (Promise.Table.getCell (Promise.Table.fresh t o).1 p).isSome = true := by
  cases hc : Promise.Table.getCell t p with
  | none => rw [hc] at h; cases h
  | some c => rw [getCell_fresh t o p c hc]; rfl

/-- A state lookup that succeeds has a cell behind it. -/
theorem getCell_isSome_of_get {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) (s : Promise.State value reason) (h : Promise.Table.get t p = some s) :
    (Promise.Table.getCell t p).isSome = true := by
  unfold Promise.Table.get at h
  cases hc : Promise.Table.getCell t p with
  | none => rw [hc] at h; cases h
  | some _ => rfl

/-- An allocated identity has a state. -/
private theorem get_of_getCell_isSome {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) (h : (Promise.Table.getCell t p).isSome = true) :
    ∃ s, Promise.Table.get t p = some s := by
  unfold Promise.Table.get
  cases hc : Promise.Table.getCell t p with
  | none => rw [hc] at h; cases h
  | some c => exact ⟨c.state, rfl⟩

/-- Under `WF`, an allocated identity is below the table cursor. -/
theorem WF.getCell_lt {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) {p : Nat} (h : (a.table.getCell p).isSome = true) : p < a.table.next := by
  unfold Promise.Table.getCell at h
  cases hf : a.table.entries.find? (fun e => e.1 == p) with
  | none => rw [hf] at h; cases h
  | some e =>
      have hb : (e.1 == p) = true :=
        List.find?_some (p := fun (x : Nat × Promise.Cell value reason) => x.1 == p) hf
      rw [← beq_iff_eq.mp hb]
      exact hw.tableBelow e (List.mem_of_find?_eq_some hf)

/-- Under `WF`, the table cursor names no cell, so the next allocation is
fresh. -/
theorem WF.getCell_next {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) : Promise.Table.getCell a.table a.table.next = none := by
  cases hc : Promise.Table.getCell a.table a.table.next with
  | none => rfl
  | some _ =>
      have := hw.getCell_lt (p := a.table.next) (by rw [hc]; rfl)
      exact absurd this (Nat.lt_irrefl _)

/-! ## 4. Lemmas about reactions, lookups and identities

What trigger-then-clear keeps of the two reaction lists, when `reactionOf`
finds a record, and uniqueness through a `Nodup` key. Private, except the
three that ruling R-W20(c) published. The lemmas over
a reaction kind are stated for every kind `k`, never with an inline `match`
on the result, because an inline `match` elaborates to a matcher other than
the landed one. -/

/-- Trigger-then-clear keeps the identities of the fulfil list, for either
kind. -/
private theorem trigger_clear_fulfill_ids {value reason body : Type}
    (rs : Promise.Reactions body) (p : Nat) (k : Promise.ReactionType)
    (argument : Except reason value) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).fulfill.map
        Promise.Reaction.id = rs.fulfill.map Promise.Reaction.id := by
  cases k with
  | fulfill =>
      show List.map Promise.Reaction.id (List.map _ (List.map _ rs.fulfill)) = _
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro r _
      show (if _ then _ else (if _ then _ else r)).id = r.id
      split <;> (show (if _ then _ else r).id = r.id; split <;> rfl)
  | reject =>
      show List.map Promise.Reaction.id (List.map _ rs.fulfill) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      show (if _ then _ else r).id = r.id
      split <;> rfl

/-- Trigger-then-clear keeps the identities of the reject list, for either
kind. -/
private theorem trigger_clear_reject_ids {value reason body : Type}
    (rs : Promise.Reactions body) (p : Nat) (k : Promise.ReactionType)
    (argument : Except reason value) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).reject.map
        Promise.Reaction.id = rs.reject.map Promise.Reaction.id := by
  cases k with
  | reject =>
      show List.map Promise.Reaction.id (List.map _ (List.map _ rs.reject)) = _
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro r _
      show (if _ then _ else (if _ then _ else r)).id = r.id
      split <;> (show (if _ then _ else r).id = r.id; split <;> rfl)
  | fulfill =>
      show List.map Promise.Reaction.id (List.map _ rs.reject) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro r _
      show (if _ then _ else r).id = r.id
      split <;> rfl

/-- Trigger-then-clear keeps the registration cursor. -/
private theorem trigger_clear_next {value reason body : Type} (rs : Promise.Reactions body)
    (p : Nat) (k : Promise.ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).next =
      rs.next := by
  cases k <;> rfl

/-- A map that keeps identity and capability keeps them for every member. -/
private theorem mem_map_keeps {body : Type} (l : List (Promise.Reaction body))
    (g : Promise.Reaction body → Promise.Reaction body)
    (hg : ∀ r, (g r).id = r.id ∧ (g r).capability = r.capability) (r' : Promise.Reaction body)
    (h : r' ∈ l.map g) : ∃ r ∈ l, r'.id = r.id ∧ r'.capability = r.capability := by
  obtain ⟨r, hr, he⟩ := List.mem_map.mp h
  exact ⟨r, hr, he ▸ hg r⟩

/-- The clearing map keeps identity and capability. -/
private theorem clearMap_keeps {body : Type} (p : Nat) (r : Promise.Reaction body) :
    ((fun (r : Promise.Reaction body) =>
        if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
          { r with phase := Promise.ReactionPhase.done }
        else r) r).id = r.id ∧
      ((fun (r : Promise.Reaction body) =>
        if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
          { r with phase := Promise.ReactionPhase.done }
        else r) r).capability = r.capability := by
  show (if _ then _ else r).id = r.id ∧ (if _ then _ else r).capability = r.capability
  split <;> exact ⟨rfl, rfl⟩

/-- The triggering map keeps identity and capability. -/
private theorem advanceMap_keeps {body : Type} (p : Nat) (r : Promise.Reaction body) :
    ((fun (r : Promise.Reaction body) =>
        if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
          { r with phase := Promise.ReactionPhase.queued r.id }
        else r) r).id = r.id ∧
      ((fun (r : Promise.Reaction body) =>
        if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
          { r with phase := Promise.ReactionPhase.queued r.id }
        else r) r).capability = r.capability := by
  show (if _ then _ else r).id = r.id ∧ (if _ then _ else r).capability = r.capability
  split <;> exact ⟨rfl, rfl⟩

/-- Every record trigger-then-clear leaves on the fulfil list is an old record
with a new phase. -/
private theorem trigger_clear_fulfill_mem {value reason body : Type}
    (rs : Promise.Reactions body) (p : Nat) (k : Promise.ReactionType)
    (argument : Except reason value) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (r' : Promise.Reaction body)
    (h : r' ∈ (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).fulfill) :
    ∃ r ∈ rs.fulfill, r'.id = r.id ∧ r'.capability = r.capability := by
  cases k with
  | fulfill =>
      obtain ⟨r'', hr'', h1, h2⟩ := mem_map_keeps _ _ (clearMap_keeps p) r' h
      obtain ⟨r, hr, h3, h4⟩ := mem_map_keeps _ _ (advanceMap_keeps p) r'' hr''
      exact ⟨r, hr, h1.trans h3, h2.trans h4⟩
  | reject => exact mem_map_keeps _ _ (clearMap_keeps p) r' h

/-- Every record trigger-then-clear leaves on the reject list is an old record
with a new phase. -/
private theorem trigger_clear_reject_mem {value reason body : Type}
    (rs : Promise.Reactions body) (p : Nat) (k : Promise.ReactionType)
    (argument : Except reason value) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (r' : Promise.Reaction body)
    (h : r' ∈ (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).reject) :
    ∃ r ∈ rs.reject, r'.id = r.id ∧ r'.capability = r.capability := by
  cases k with
  | reject =>
      obtain ⟨r'', hr'', h1, h2⟩ := mem_map_keeps _ _ (clearMap_keeps p) r' h
      obtain ⟨r, hr, h3, h4⟩ := mem_map_keeps _ _ (advanceMap_keeps p) r'' hr''
      exact ⟨r, hr, h1.trans h3, h2.trans h4⟩
  | fulfill => exact mem_map_keeps _ _ (clearMap_keeps p) r' h

/-- A bound on every identity transfers between lists with the same
identities. -/
private theorem lt_of_ids {body : Type} (l l' : List (Promise.Reaction body)) (n : Nat)
    (h : l'.map Promise.Reaction.id = l.map Promise.Reaction.id)
    (hl : ∀ r ∈ l, r.id < n) : ∀ r ∈ l', r.id < n := by
  intro r hr
  have hm : r.id ∈ l.map Promise.Reaction.id := h ▸ List.mem_map_of_mem hr
  obtain ⟨r0, hr0, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hl r0 hr0

/-- The waiting set is drawn from the list its kind names. -/
theorem mem_waitingOn {body : Type} (rs : Promise.Reactions body) (p : Nat)
    (k : Promise.ReactionType) (r : Promise.Reaction body)
    (h : r ∈ Promise.Reactions.waitingOn rs p k) :
    r ∈ (match k with
      | .fulfill => rs.fulfill
      | .reject => rs.reject) := by
  cases k <;> exact (List.mem_filter.mp h).1

/-- A lookup by identity finds something exactly when the identity is listed. -/
private theorem find_id_isSome {body : Type} (l : List (Promise.Reaction body)) (x : Nat) :
    (l.find? (fun r => r.id == x)).isSome = true ↔ x ∈ l.map Promise.Reaction.id := by
  constructor
  · intro h
    cases hf : l.find? (fun r => r.id == x) with
    | none => rw [hf] at h; cases h
    | some r =>
        have hb : (r.id == x) = true :=
          List.find?_some (p := fun (y : Promise.Reaction body) => y.id == x) hf
        rw [← beq_iff_eq.mp hb]
        exact List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
  · intro h
    obtain ⟨r, hr, he⟩ := List.mem_map.mp h
    rw [List.find?_isSome]
    exact ⟨r, hr, beq_iff_eq.mpr he⟩

/-- `Reactions.get` finds a record exactly when the identity is on the list
of its kind. -/
private theorem reactionsGet_isSome {body : Type} (rs : Promise.Reactions body)
    (k : Promise.ReactionType) (x : Nat) :
    (Promise.Reactions.get rs k x).isSome = true ↔
      x ∈ (match k with
        | .fulfill => rs.fulfill
        | .reject => rs.reject).map Promise.Reaction.id := by
  cases k <;> exact find_id_isSome _ x

/-- `reactionOf` finds a record exactly when the job's identity is held, or
is on the list its argument's tag selects. -/
private theorem reactionOf_isSome {value reason body : Type} (a : Agent value reason body)
    (j : Job value reason) :
    (reactionOf a j).isSome = true ↔
      (j.reaction ∈ a.held.map Promise.Reaction.id ∨
        j.reaction ∈ (match j.argument with
          | .ok _ => a.reactions.fulfill
          | .error _ => a.reactions.reject).map Promise.Reaction.id) := by
  unfold reactionOf
  cases hh : a.held.find? (fun r => r.id == j.reaction) with
  | some r =>
      have hin : j.reaction ∈ a.held.map Promise.Reaction.id :=
        (find_id_isSome a.held j.reaction).mp (by rw [hh]; rfl)
      exact ⟨fun _ => Or.inl hin, fun _ => rfl⟩
  | none =>
      have hnot : ¬ j.reaction ∈ a.held.map Promise.Reaction.id := fun hin => by
        have := (find_id_isSome a.held j.reaction).mpr hin
        rw [hh] at this
        cases this
      dsimp only
      cases harg : j.argument with
      | ok v =>
          show (Promise.Reactions.get a.reactions Promise.ReactionType.fulfill j.reaction).isSome =
            true ↔ _
          rw [reactionsGet_isSome]
          exact ⟨Or.inr, fun h => h.elim (fun h' => absurd h' hnot) id⟩
      | error r =>
          show (Promise.Reactions.get a.reactions Promise.ReactionType.reject j.reaction).isSome =
            true ↔ _
          rw [reactionsGet_isSome]
          exact ⟨Or.inr, fun h => h.elim (fun h' => absurd h' hnot) id⟩

/-- Membership through a `Nodup` key map identifies the element. -/
theorem eq_of_nodup_key {α : Type} (key : α → Nat) :
    ∀ (l : List α), (l.map key).Nodup → ∀ x ∈ l, ∀ y ∈ l, key x = key y → x = y
  | [], _, x, hx, _, _, _ => absurd hx List.not_mem_nil
  | z :: l, hnd, x, hx, y, hy, hk => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hx with hxz | hxl
      · rcases List.mem_cons.mp hy with hyz | hyl
        · rw [hxz, hyz]
        · rw [hxz] at hk
          exact absurd (hk ▸ List.mem_map_of_mem hyl) hnd.1
      · rcases List.mem_cons.mp hy with hyz | hyl
        · rw [hyz] at hk
          exact absurd (hk.symm ▸ List.mem_map_of_mem hxl) hnd.1
        · exact eq_of_nodup_key key l hnd.2 x hxl y hyl hk

/-- When at most one member satisfies `pick`, `find?` names a member that
does. -/
theorem find?_unique {α : Type} (l : List α) (pick : α → Bool)
    (huniq : ∀ g ∈ l, ∀ g' ∈ l, pick g = true → pick g' = true → g = g') (f : α) (hf : f ∈ l)
    (hp : pick f = true) : l.find? pick = some f := by
  cases h : l.find? pick with
  | none =>
      have := List.find?_eq_none.mp h f hf
      rw [hp] at this
      exact absurd rfl this
  | some g =>
      rw [huniq g (List.mem_of_find?_eq_some h) f hf (List.find?_some h) hp]

/-! ## 5. The empty agent -/

/-- The agent before any promise is well formed: every store is empty, so every
clause holds vacuously or by `rfl`. Invariant law; DB-04 M1. -/
theorem WF.empty :
    ∀ {value reason body : Type}, Agent.WF (Agent.empty : Agent.Agent value reason body) := by
  intro value reason body
  exact {
    tableNodup := List.nodup_nil
    tableBelow := fun _ h => absurd h List.not_mem_nil
    functionsBelow := fun _ h => absurd h List.not_mem_nil
    functionsAllocated := fun _ h => absurd h List.not_mem_nil
    resolvedSettled := fun _ h => absurd h List.not_mem_nil
    reactionsBelow := fun _ h => absurd h List.not_mem_nil
    queueBelow := fun _ h => absurd h List.not_mem_nil
    paired := rfl
    functionsNodup := List.nodup_nil
    heldDistinct := List.nodup_nil
    queuedKnown := fun _ h => absurd h List.not_mem_nil
    runningActive := ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
    capabilityStored := fun _ h => absurd h List.not_mem_nil
    settlementsCoherent := ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
      fun _ _ h => absurd h List.not_mem_nil⟩ }

/-! ## 6. `settle`

The settle-and-trigger every resolving function and every finished job with a
capability reaches. On a promise that is not pending it changes nothing; on a
pending one it settles the table, triggers and clears the waiting reactions
and appends one trace entry, and each of these keeps `WF` and moves the agent
up `Le`. -/

/-- On a promise that is not pending, `settle` is the identity. -/
private theorem settle_notPending_eq {value reason body : Type} (a : Agent value reason body)
    (p : Nat) (result : Except reason value) (h : Promise.Table.isPending a.table p = false) :
    settle a p result = a := by
  unfold settle Promise.Table.settleAndTrigger Promise.Table.settleTraced
  rw [h]
  rfl

/-- On a pending promise, `settle` is the landed settle, trigger-then-clear
and one appended trace entry. -/
private theorem settle_pending_eq {value reason body : Type} (a : Agent value reason body)
    (p : Nat) (result : Except reason value) (h : Promise.Table.isPending a.table p = true) :
    settle a p result =
      { a with
        table := Promise.Table.settle a.table p result,
        reactions := Promise.Reactions.clear
          (Promise.triggerReactions a.reactions p
            (match result with
              | .ok _ => Promise.ReactionType.fulfill
              | .error _ => Promise.ReactionType.reject) result a.queue).1 p,
        queue := (Promise.triggerReactions a.reactions p
            (match result with
              | .ok _ => Promise.ReactionType.fulfill
              | .error _ => Promise.ReactionType.reject) result a.queue).2,
        settlements := a.settlements ++ [(p, result)] } := by
  unfold settle Promise.Table.settleAndTrigger Promise.Table.settleTraced
  rw [h]
  rfl

/-- The pending branch of `settle` keeps `WF`: identities, cursors and pairing
survive trigger-then-clear, every newly queued job names a listed record, and
the new trace entry is the table's new settled state at an identity not yet
traced. -/
private theorem WF.settlePending {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (p : Nat) (result : Except reason value)
    (hp : Promise.Table.isPending a.table p = true) : WF (settle a p result) := by
  rw [settle_pending_eq a p result hp]
  have hpend : Promise.Table.get a.table p = some Promise.State.pending :=
    (Promise.Table.isPending_iff a.table p).mp hp
  have hids := settle_ids a.table p result
  have hF : ∀ r ∈ a.reactions.fulfill, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hR : ∀ r ∈ a.reactions.reject, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_right _ hr))
  have hH : ∀ r ∈ a.held, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_right _ hr)
  -- The identities of the two lists and the cursor are unchanged, for either kind.
  have hfi : ∀ k : Promise.ReactionType,
      (Promise.Reactions.clear (Promise.triggerReactions a.reactions p k result a.queue).1
        p).fulfill.map Promise.Reaction.id = a.reactions.fulfill.map Promise.Reaction.id :=
    fun k => trigger_clear_fulfill_ids a.reactions p k result a.queue
  have hri : ∀ k : Promise.ReactionType,
      (Promise.Reactions.clear (Promise.triggerReactions a.reactions p k result a.queue).1
        p).reject.map Promise.Reaction.id = a.reactions.reject.map Promise.Reaction.id :=
    fun k => trigger_clear_reject_ids a.reactions p k result a.queue
  have hnx : ∀ k : Promise.ReactionType,
      (Promise.Reactions.clear (Promise.triggerReactions a.reactions p k result a.queue).1
        p).next = a.reactions.next :=
    fun k => trigger_clear_next a.reactions p k result a.queue
  -- No trace entry names the pending `p`, by `settlementsCoherent`.
  have htr : ∀ e ∈ a.settlements, e.1 ≠ p := by
    intro e he hep
    obtain ⟨q, x⟩ := e
    dsimp only at hep
    subst hep
    cases x with
    | ok v =>
        have := hw.settlementsCoherent.2.1 q v he
        rw [hpend] at this
        cases this
    | error r =>
        have := hw.settlementsCoherent.2.2 q r he
        rw [hpend] at this
        cases this
  refine ⟨?_, ?_, hw.functionsBelow, ?_, ?_, ?_, ?_, ?_, hw.functionsNodup, ?_, ?_,
    hw.runningActive, ?_, ?_⟩
  · -- tableNodup
    show ((Promise.Table.settle a.table p result).entries.map Prod.fst).Nodup
    rw [hids.1]
    exact hw.tableNodup
  · -- tableBelow
    intro e he
    show e.1 < (Promise.Table.settle a.table p result).next
    rw [hids.2]
    have hmem : e.1 ∈ (Promise.Table.settle a.table p result).entries.map Prod.fst :=
      List.mem_map_of_mem he
    rw [hids.1] at hmem
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp hmem
    rw [← h0]
    exact hw.tableBelow e0 he0
  · -- functionsAllocated
    intro f hf
    show (Promise.Table.getCell (Promise.Table.settle a.table p result) f.promise).isSome = true
    rw [(getCell_settle a.table p f.promise result).1]
    exact hw.functionsAllocated f hf
  · -- resolvedSettled
    intro f hf hres
    exact settle_notPending a.table p f.promise result (hw.resolvedSettled f hf hres)
  · -- reactionsBelow
    intro r hr
    rw [hnx]
    rcases List.mem_append.mp hr with hfr | hheld
    · rcases List.mem_append.mp hfr with hful | hrej
      · exact lt_of_ids a.reactions.fulfill _ _ (hfi _) hF r hful
      · exact lt_of_ids a.reactions.reject _ _ (hri _) hR r hrej
    · exact hH r hheld
  · -- queueBelow
    intro j hj
    show j.reaction < (Promise.Reactions.clear _ p).next
    rw [hnx]
    change j ∈ (Promise.triggerReactions a.reactions p _ result a.queue).2.pending at hj
    rw [Promise.triggerReactions_order] at hj
    rcases List.mem_append.mp hj with hold | hnew
    · exact hw.queueBelow j hold
    · obtain ⟨r, hr, hjr⟩ := List.mem_map.mp hnew
      rw [← hjr]
      have hr' := mem_waitingOn _ _ _ r hr
      cases result with
      | ok _ => exact hF r hr'
      | error _ => exact hR r hr'
  · -- paired
    show (Promise.Reactions.clear _ p).fulfill.map Promise.Reaction.id =
      (Promise.Reactions.clear _ p).reject.map Promise.Reaction.id
    rw [hfi, hri]
    exact hw.paired
  · -- heldDistinct
    show (a.held.map Promise.Reaction.id ++
      (Promise.Reactions.clear _ p).fulfill.map Promise.Reaction.id).Nodup
    rw [hfi]
    exact hw.heldDistinct
  · -- queuedKnown
    intro j hj
    change j ∈ (Promise.triggerReactions a.reactions p _ result a.queue).2.pending at hj
    rw [Promise.triggerReactions_order] at hj
    rw [reactionOf_isSome]
    show j.reaction ∈ a.held.map Promise.Reaction.id ∨
      j.reaction ∈ (match j.argument with
        | .ok _ => (Promise.Reactions.clear _ p).fulfill
        | .error _ => (Promise.Reactions.clear _ p).reject).map Promise.Reaction.id
    rcases List.mem_append.mp hj with hold | hnew
    · have hk := (reactionOf_isSome a j).mp (hw.queuedKnown j hold)
      cases harg : j.argument with
      | ok v =>
          rw [harg] at hk
          dsimp only at hk ⊢
          rw [hfi]
          exact hk
      | error r =>
          rw [harg] at hk
          dsimp only at hk ⊢
          rw [hri]
          exact hk
    · obtain ⟨r, hr, hjr⟩ := List.mem_map.mp hnew
      rw [← hjr]
      have hr' := mem_waitingOn _ _ _ r hr
      refine Or.inr ?_
      cases result with
      | ok v =>
          dsimp only
          rw [hfi]
          exact List.mem_map_of_mem hr'
      | error x =>
          dsimp only
          rw [hri]
          exact List.mem_map_of_mem hr'
  · -- capabilityStored
    intro r hr cap hcap
    rcases List.mem_append.mp hr with hfr | hheld
    · rcases List.mem_append.mp hfr with hful | hrej
      · obtain ⟨r0, hr0, _, hc⟩ := trigger_clear_fulfill_mem _ _ _ _ _ r hful
        exact hw.capabilityStored r0
          (List.mem_append_left _ (List.mem_append_left _ hr0)) cap (hc ▸ hcap)
      · obtain ⟨r0, hr0, _, hc⟩ := trigger_clear_reject_mem _ _ _ _ _ r hrej
        exact hw.capabilityStored r0
          (List.mem_append_left _ (List.mem_append_right _ hr0)) cap (hc ▸ hcap)
    · exact hw.capabilityStored r (List.mem_append_right _ hheld) cap hcap
  · -- settlementsCoherent
    refine ⟨?_, ?_, ?_⟩
    · show ((a.settlements ++ [(p, result)]).map Prod.fst).Nodup
      rw [List.map_append]
      refine List.nodup_append.mpr ⟨hw.settlementsCoherent.1,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy
      obtain ⟨e, he, hex⟩ := List.mem_map.mp hx
      have hy' : y = p := List.mem_singleton.mp hy
      rw [hy', ← hex]
      exact htr e he
    · intro q v hq
      show Promise.Table.get (Promise.Table.settle a.table p result) q =
        some (Promise.State.fulfilled v)
      rcases List.mem_append.mp hq with hold | hnew
      · rw [settle_get_other a.table p q result (htr (q, Except.ok v) hold)]
        exact hw.settlementsCoherent.2.1 q v hold
      · have he := List.mem_singleton.mp hnew
        cases he
        rw [Promise.Table.settle_assert a.table p (Except.ok v) hpend]
    · intro q r hq
      show Promise.Table.get (Promise.Table.settle a.table p result) q =
        some (Promise.State.rejected r)
      rcases List.mem_append.mp hq with hold | hnew
      · rw [settle_get_other a.table p q result (htr (q, Except.error r) hold)]
        exact hw.settlementsCoherent.2.2 q r hold
      · have he := List.mem_singleton.mp hnew
        cases he
        rw [Promise.Table.settle_assert a.table p (Except.error r) hpend]

/-- `settle` keeps `WF`, whether or not the promise was pending. -/
private theorem WF.settle {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (p : Nat) (result : Except reason value) : WF (settle a p result) := by
  cases hp : Promise.Table.isPending a.table p with
  | false => rw [settle_notPending_eq a p result hp]; exact hw
  | true => exact WF.settlePending hw p result hp

/-- `settle` moves the agent up `Le`: only the settled identity's state
changes, from pending, and the trace gains one entry at its end. -/
private theorem Le.settle {value reason body : Type} (a : Agent value reason body) (p : Nat)
    (result : Except reason value) : Le a (settle a p result) := by
  cases hp : Promise.Table.isPending a.table p with
  | false => rw [settle_notPending_eq a p result hp]; exact Le.refl a
  | true =>
      rw [settle_pending_eq a p result hp]
      have hpend : Promise.Table.get a.table p = some Promise.State.pending :=
        (Promise.Table.isPending_iff a.table p).mp hp
      refine ⟨fun q h => ?_, fun q s h hs => ?_, fun q h => ?_, ?_, ?_, Nat.le_refl _,
        fun f hf => ⟨f, hf, rfl, rfl, rfl⟩, List.prefix_append _ _⟩
      · show (Promise.Table.getCell (Promise.Table.settle a.table p result) q).isSome = true
        rw [(getCell_settle a.table p q result).1]
        exact h
      · show Promise.Table.get (Promise.Table.settle a.table p result) q = some s
        have hne : q ≠ p := by
          intro hqp
          rw [hqp, hpend] at h
          cases h
          exact hs rfl
        rw [settle_get_other a.table p q result hne]
        exact h
      · show (Promise.Table.getCell (Promise.Table.settle a.table p result) q).map
          Promise.Cell.handled = some true
        rw [(getCell_settle a.table p q result).2]
        exact h
      · show a.table.next ≤ (Promise.Table.settle a.table p result).next
        rw [(settle_ids a.table p result).2]
        exact Nat.le_refl _
      · show a.reactions.next ≤ (Promise.Reactions.clear _ p).next
        rw [trigger_clear_next]
        exact Nat.le_refl _

/-! ## 7. `callFunctions`: the stored resolving functions

`resolve`, `reject` and a finished job with a capability all go through
`callFunctions`, which settles and then sets the shared one-shot marker on the
records `pick` selects. Under `WF` a `[[Resolve]]` or `[[Reject]]` identity
selects at most one record. -/

/-- Setting the marker keeps a record's three identities. -/
theorem mark_fields (pick : Promise.ResolvingFunctions → Bool)
    (g : Promise.ResolvingFunctions) :
    (if pick g then { g with alreadyResolved := true } else g).resolve = g.resolve ∧
      (if pick g then { g with alreadyResolved := true } else g).reject = g.reject ∧
      (if pick g then { g with alreadyResolved := true } else g).promise = g.promise := by
  cases pick g <;> exact ⟨rfl, rfl, rfl⟩

/-- A marker set after marking was selected or already set. -/
private theorem mark_fired (pick : Promise.ResolvingFunctions → Bool)
    (g : Promise.ResolvingFunctions)
    (h : (if pick g then { g with alreadyResolved := true } else g).alreadyResolved = true) :
    pick g = true ∨ g.alreadyResolved = true := by
  cases hp : pick g with
  | true => exact Or.inl rfl
  | false =>
      rw [hp] at h
      exact Or.inr h

/-- Marking keeps `WF` when every selected record's promise is already
settled. -/
private theorem WF.mark {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (pick : Promise.ResolvingFunctions → Bool)
    (hp : ∀ g ∈ a.functions, pick g = true → Promise.Table.isPending a.table g.promise = false) :
    WF { a with functions := a.functions.map (fun g =>
      if pick g then { g with alreadyResolved := true } else g) } := by
  refine ⟨hw.tableNodup, hw.tableBelow, ?_, ?_, ?_, hw.reactionsBelow, hw.queueBelow, hw.paired,
    ?_, hw.heldDistinct, hw.queuedKnown, hw.runningActive, ?_, hw.settlementsCoherent⟩
  · intro f hf
    obtain ⟨g, hg, hgf⟩ := List.mem_map.mp hf
    rw [← hgf, (mark_fields pick g).1, (mark_fields pick g).2.1]
    exact hw.functionsBelow g hg
  · intro f hf
    obtain ⟨g, hg, hgf⟩ := List.mem_map.mp hf
    show (a.table.getCell f.promise).isSome = true
    rw [← hgf, (mark_fields pick g).2.2]
    exact hw.functionsAllocated g hg
  · intro f hf hres
    obtain ⟨g, hg, hgf⟩ := List.mem_map.mp hf
    show Promise.Table.isPending a.table f.promise = false
    rw [← hgf] at hres ⊢
    rw [(mark_fields pick g).2.2]
    rcases mark_fired pick g hres with hpk | hfired
    · exact hp g hg hpk
    · exact hw.resolvedSettled g hg hfired
  · show ((a.functions.map _).map Promise.ResolvingFunctions.resolve).Nodup
    rw [List.map_map]
    have : (Promise.ResolvingFunctions.resolve ∘ (fun g =>
        if pick g then { g with alreadyResolved := true } else g)) =
        Promise.ResolvingFunctions.resolve := by
      funext g
      exact (mark_fields pick g).1
    rw [this]
    exact hw.functionsNodup
  · intro r hr cap hcap
    obtain ⟨f, hf, h1, h2, h3⟩ := hw.capabilityStored r hr cap hcap
    refine ⟨_, List.mem_map_of_mem hf, ?_, ?_, ?_⟩
    · rw [(mark_fields pick f).1]; exact h1
    · rw [(mark_fields pick f).2.1]; exact h2
    · rw [(mark_fields pick f).2.2]; exact h3

/-- Marking moves the agent up `Le`: every record survives with its
identities. -/
private theorem Le.mark {value reason body : Type} (a : Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) :
    Le a { a with functions := a.functions.map (fun g =>
      if pick g then { g with alreadyResolved := true } else g) } :=
  ⟨fun _ h => h, fun _ _ h _ => h, fun _ h => h, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    fun f hf => ⟨_, List.mem_map_of_mem hf, (mark_fields pick f).1, (mark_fields pick f).2.1,
      (mark_fields pick f).2.2⟩, List.prefix_refl _⟩

/-- `callFunctions` keeps `WF` when `pick` selects at most one stored record:
the settle keeps it, and the one marked record's promise is then settled. -/
private theorem WF.callFunctions {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value)
    (huniq : ∀ g ∈ a.functions, ∀ g' ∈ a.functions, pick g = true → pick g' = true → g = g') :
    WF (callFunctions a pick result) := by
  cases hf : a.functions.find? pick with
  | none => rw [callFunctions_none a pick result hf]; exact hw
  | some f =>
      cases hfr : f.alreadyResolved with
      | true => rw [callFunctions_fired a pick result f hf hfr]; exact hw
      | false =>
          rw [callFunctions_fresh a pick result f hf hfr]
          have hfm : f ∈ a.functions := List.mem_of_find?_eq_some hf
          have hfp : pick f = true := List.find?_some hf
          have hs := WF.settle hw f.promise result
          exact WF.mark hs pick (fun g hg hpg => by
            have hgf : g = f := huniq g hg f hfm hpg hfp
            rw [hgf]
            show Promise.Table.isPending
              (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise result).1
              f.promise = false
            rw [settleAndTrigger_table]
            exact isPending_settle_self a.table f.promise result)

/-- `callFunctions` moves the agent up `Le`, on every branch. -/
private theorem Le.callFunctions {value reason body : Type} (a : Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value) :
    Le a (callFunctions a pick result) := by
  cases hf : a.functions.find? pick with
  | none => rw [callFunctions_none a pick result hf]; exact Le.refl a
  | some f =>
      cases hfr : f.alreadyResolved with
      | true => rw [callFunctions_fired a pick result f hf hfr]; exact Le.refl a
      | false =>
          rw [callFunctions_fresh a pick result f hf hfr]
          exact Le.trans (Le.settle a f.promise result)
            (Le.mark (Whatwg.Ecma262.Agent.settle a f.promise result) pick)

/-- Under `WF` (`functionsNodup`), a `[[Resolve]]` identity selects at most one
stored record. -/
theorem resolve_unique {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (cap : Promise.Capability) :
    ∀ g ∈ a.functions, ∀ g' ∈ a.functions,
      (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) g = true →
      (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) g' = true → g = g' := by
  intro g hg g' hg' h1 h2
  exact eq_of_nodup_key Promise.ResolvingFunctions.resolve a.functions hw.functionsNodup g hg g'
    hg' ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm)

/-- Under `WF` (`functionsBelow` with `functionsNodup`), a `[[Reject]]`
identity selects at most one stored record. -/
theorem reject_unique {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (cap : Promise.Capability) :
    ∀ g ∈ a.functions, ∀ g' ∈ a.functions,
      (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) g = true →
      (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) g' = true → g = g' := by
  intro g hg g' hg' h1 h2
  have hrj : g.reject = g'.reject := (beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm
  have hres : g.resolve = g'.resolve := by
    have e1 := (hw.functionsBelow g hg).1
    have e2 := (hw.functionsBelow g' hg').1
    rw [e1, e2] at hrj
    exact Nat.succ.inj hrj
  exact eq_of_nodup_key Promise.ResolvingFunctions.resolve a.functions hw.functionsNodup g hg g'
    hg' hres

/-! ## 8. `newPromise` -/

/-- `newPromise` keeps `WF`: the new cell and the new function record take
the two cursors, which were fresh, and every old fact survives allocation. -/
private theorem WF.newPromise {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) : WF (newPromise a).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hw.reactionsBelow, hw.queueBelow, hw.paired, ?_, hw.heldDistinct,
    hw.queuedKnown, hw.runningActive, ?_, ?_⟩
  · show ((a.table.entries ++ [(a.table.next, Promise.Cell.mk Promise.State.pending false)]).map
      Prod.fst).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hw.tableNodup, List.nodup_cons.mpr ⟨List.not_mem_nil,
      List.nodup_nil⟩, ?_⟩
    intro x hx y hy
    obtain ⟨e, he, hex⟩ := List.mem_map.mp hx
    have hy' : y = a.table.next := List.mem_singleton.mp hy
    rw [hy', ← hex]
    exact Nat.ne_of_lt (hw.tableBelow e he)
  · intro e he
    show e.1 < a.table.next + 1
    rcases List.mem_append.mp he with hold | hnew
    · exact Nat.lt_succ_of_lt (hw.tableBelow e hold)
    · rw [List.mem_singleton.mp hnew]
      exact Nat.lt_succ_self _
  · intro f hf
    show f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction + 2
    rcases List.mem_append.mp hf with hold | hnew
    · exact ⟨(hw.functionsBelow f hold).1,
        Nat.lt_of_lt_of_le (hw.functionsBelow f hold).2 (Nat.le_add_right _ 2)⟩
    · rw [List.mem_singleton.mp hnew]
      exact ⟨rfl, Nat.lt_succ_self _⟩
  · intro f hf
    show (Promise.Table.getCell (Promise.Table.fresh a.table Promise.State.pending).1
      f.promise).isSome = true
    rcases List.mem_append.mp hf with hold | hnew
    · exact getCell_fresh_isSome a.table _ f.promise (hw.functionsAllocated f hold)
    · rw [List.mem_singleton.mp hnew]
      exact getCell_isSome_of_get _ _ _
        (Promise.Table.fresh_get a.table Promise.State.pending hw.getCell_next)
  · intro f hf hres
    rcases List.mem_append.mp hf with hold | hnew
    · show Promise.Table.isPending (Promise.Table.fresh a.table Promise.State.pending).1
        f.promise = false
      unfold Promise.Table.isPending Promise.Table.get
      rw [Promise.Table.fresh_old a.table _ f.promise
        (Nat.ne_of_lt (hw.getCell_lt (hw.functionsAllocated f hold)))]
      exact hw.resolvedSettled f hold hres
    · rw [List.mem_singleton.mp hnew] at hres
      cases hres
  · show ((a.functions ++ [Promise.createResolvingFunctions a.table.next a.nextFunction]).map
      Promise.ResolvingFunctions.resolve).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hw.functionsNodup, List.nodup_cons.mpr ⟨List.not_mem_nil,
      List.nodup_nil⟩, ?_⟩
    intro x hx y hy
    obtain ⟨f, hf, hfx⟩ := List.mem_map.mp hx
    have hy' : y = a.nextFunction := List.mem_singleton.mp hy
    rw [hy', ← hfx]
    have h1 := (hw.functionsBelow f hf).1
    have h2 := (hw.functionsBelow f hf).2
    rw [h1] at h2
    exact Nat.ne_of_lt (Nat.lt_of_succ_lt h2)
  · intro r hr cap hcap
    obtain ⟨f, hf, h1, h2, h3⟩ := hw.capabilityStored r hr cap hcap
    exact ⟨f, List.mem_append_left _ hf, h1, h2, h3⟩
  · refine ⟨hw.settlementsCoherent.1, fun q v hq => ?_, fun q r hq => ?_⟩
    · exact get_fresh a.table _ q _ (hw.settlementsCoherent.2.1 q v hq)
    · exact get_fresh a.table _ q _ (hw.settlementsCoherent.2.2 q r hq)

/-- `newPromise` moves the agent up `Le`: allocation keeps every old cell and
grows the table and function cursors. -/
private theorem Le.newPromise {value reason body : Type} (a : Agent value reason body) :
    Le a (Whatwg.Ecma262.Agent.newPromise a).1 := by
  refine ⟨fun p h => ?_, fun p s h _ => ?_, fun p h => ?_, Nat.le_succ _, Nat.le_refl _,
    Nat.le_add_right _ 2, fun f hf => ⟨f, List.mem_append_left _ hf, rfl, rfl, rfl⟩,
    List.prefix_refl _⟩
  · exact getCell_fresh_isSome a.table _ p h
  · exact get_fresh a.table _ p s h
  · show (Promise.Table.getCell (Promise.Table.fresh a.table _).1 p).map
      Promise.Cell.handled = some true
    cases hc : Promise.Table.getCell a.table p with
    | none => rw [hc] at h; cases h
    | some c => rw [getCell_fresh a.table _ p c hc]; rw [hc] at h; exact h

/-- The capability `newPromise` answers is minted in the agent it leaves. -/
private theorem newPromise_minted {value reason body : Type} (a : Agent value reason body) :
    Minted (newPromise a).1 (newPromise a).2 :=
  ⟨Promise.createResolvingFunctions a.table.next a.nextFunction,
    List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl, rfl, rfl⟩

/-- `newPromise` fulfils its row: from a well-formed agent it moves up `Le`,
keeps `WF`, and answers a capability that is minted and whose promise, the
cell allocated at the old table cursor, is pending. `op.newpromisecapability` (NEWCAP,
2696238..2698770) with `op.createresolvingfunctions` (RESOLVING). Adequacy law;
DB-04 M2. -/
theorem newPromise_implements :
    ∀ {value reason body : Type},
      Agent.Implements (Agent.Op.newPromise : Agent.Op value reason body) := by
  intro value reason body a c hw _
  refine ⟨Le.newPromise a, WF.newPromise hw, newPromise_minted a, ?_⟩
  exact Promise.Table.fresh_get a.table Promise.State.pending hw.getCell_next

/-! ## 9. `resolve` and `reject` -/

/-- `resolve` keeps `WF`. -/
private theorem WF.resolve {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (cap : Promise.Capability) (v : value) : WF (resolve a cap v) :=
  WF.callFunctions hw _ _ (resolve_unique hw cap)

/-- `reject` keeps `WF`. -/
private theorem WF.reject {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (cap : Promise.Capability) (r : reason) : WF (reject a cap r) :=
  WF.callFunctions hw _ _ (reject_unique hw cap)

/-- `resolve` fulfils its row: through a minted capability it moves up `Le`,
keeps `WF`, and leaves the capability's promise settled. An unfired function
settles it now; a fired one is inert, and the promise is already settled by
`WF.resolvedSettled`. `op.createresolvingfunctions` (RESOLVING,
2692679..2695411) resolve steps, with `op.fulfillpromise` (FULFILL); Web IDL
`op.resolve` (349216..349783). Adequacy law; DB-04 M2. -/
theorem resolve_implements :
    ∀ {value reason body : Type} (cap : Promise.Capability) (v : value),
      Agent.Implements (Agent.Op.resolve cap v : Agent.Op value reason body) := by
  intro value reason body cap v a c hw hpre
  refine ⟨Le.callFunctions a _ _, WF.resolve hw cap v, ?_⟩
  obtain ⟨f, hf, h1, _, h3⟩ := hpre
  have hres := find?_unique a.functions _ (resolve_unique hw cap) f hf (beq_iff_eq.mpr h1)
  show ∃ s, Promise.Table.get (Whatwg.Ecma262.Agent.resolve a cap v).table cap.promise =
    some s ∧ s ≠ Promise.State.pending
  rw [← h3]
  cases hfr : f.alreadyResolved with
  | true =>
      rw [show Whatwg.Ecma262.Agent.resolve a cap v = a from callFunctions_fired a _ _ f hres hfr]
      exact settled_of_notPending a.table f.promise (hw.functionsAllocated f hf)
        (hw.resolvedSettled f hf hfr)
  | false =>
      rw [show Whatwg.Ecma262.Agent.resolve a cap v = _ from
        callFunctions_fresh a _ (Except.ok v) f hres hfr]
      show ∃ s, Promise.Table.get
        (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise (Except.ok v)).1
        f.promise = some s ∧ s ≠ Promise.State.pending
      rw [settleAndTrigger_table]
      exact settle_settled a.table f.promise _ (hw.functionsAllocated f hf)

/-- `reject` fulfils its row: through a minted capability it moves up `Le`,
keeps `WF`, and leaves the capability's promise settled, now or already.
`op.createresolvingfunctions` (RESOLVING) reject steps, with
`op.rejectpromise` (REJECT, 2699323..2700252); Web IDL `op.reject`
(349785..350073). Adequacy law; DB-04 M2. -/
theorem reject_implements :
    ∀ {value reason body : Type} (cap : Promise.Capability) (r : reason),
      Agent.Implements (Agent.Op.reject cap r : Agent.Op value reason body) := by
  intro value reason body cap r a c hw hpre
  refine ⟨Le.callFunctions a _ _, WF.reject hw cap r, ?_⟩
  obtain ⟨f, hf, _, h2, h3⟩ := hpre
  have hrej := find?_unique a.functions _ (reject_unique hw cap) f hf (beq_iff_eq.mpr h2)
  show ∃ s, Promise.Table.get (Whatwg.Ecma262.Agent.reject a cap r).table cap.promise =
    some s ∧ s ≠ Promise.State.pending
  rw [← h3]
  cases hfr : f.alreadyResolved with
  | true =>
      rw [show Whatwg.Ecma262.Agent.reject a cap r = a from callFunctions_fired a _ _ f hrej hfr]
      exact settled_of_notPending a.table f.promise (hw.functionsAllocated f hf)
        (hw.resolvedSettled f hf hfr)
  | false =>
      rw [show Whatwg.Ecma262.Agent.reject a cap r = _ from
        callFunctions_fresh a _ (Except.error r) f hrej hfr]
      show ∃ s, Promise.Table.get
        (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise
          (Except.error r)).1 f.promise = some s ∧ s ≠ Promise.State.pending
      rw [settleAndTrigger_table]
      exact settle_settled a.table f.promise _ (hw.functionsAllocated f hf)

/-! ## 10. `markHandled` -/

/-- `markHandled` keeps `WF`: a mark changes no identity, cursor or state. -/
private theorem WF.markHandled {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (p : Nat) : WF (markHandled a p) := by
  have hids := markHandled_ids a.table p
  refine ⟨?_, ?_, hw.functionsBelow, ?_, ?_, hw.reactionsBelow, hw.queueBelow, hw.paired,
    hw.functionsNodup, hw.heldDistinct, hw.queuedKnown, hw.runningActive, hw.capabilityStored,
    ?_⟩
  · show ((Promise.Table.markHandled a.table p).entries.map Prod.fst).Nodup
    rw [hids.1]
    exact hw.tableNodup
  · intro e he
    show e.1 < (Promise.Table.markHandled a.table p).next
    rw [hids.2]
    have hmem : e.1 ∈ (Promise.Table.markHandled a.table p).entries.map Prod.fst :=
      List.mem_map_of_mem he
    rw [hids.1] at hmem
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp hmem
    rw [← h0]
    exact hw.tableBelow e0 he0
  · intro f hf
    show (Promise.Table.getCell (Promise.Table.markHandled a.table p) f.promise).isSome = true
    rw [markHandled_isSome]
    exact hw.functionsAllocated f hf
  · intro f hf hres
    show Promise.Table.isPending (Promise.Table.markHandled a.table p) f.promise = false
    rw [markHandled_isPending]
    exact hw.resolvedSettled f hf hres
  · refine ⟨hw.settlementsCoherent.1, fun q v hq => ?_, fun q r hq => ?_⟩
    · show Promise.Table.get (Promise.Table.markHandled a.table p) q = _
      rw [markHandled_get]
      exact hw.settlementsCoherent.2.1 q v hq
    · show Promise.Table.get (Promise.Table.markHandled a.table p) q = _
      rw [markHandled_get]
      exact hw.settlementsCoherent.2.2 q r hq

/-- `markHandled` moves the agent up `Le`: it only sets a handled bit. -/
private theorem Le.markHandled {value reason body : Type} (a : Agent value reason body)
    (p : Nat) : Le a (Whatwg.Ecma262.Agent.markHandled a p) :=
  ⟨fun q h => by
      show (Promise.Table.getCell (Promise.Table.markHandled a.table p) q).isSome = true
      rw [markHandled_isSome]; exact h,
    fun q s h _ => by
      show Promise.Table.get (Promise.Table.markHandled a.table p) q = some s
      rw [markHandled_get]; exact h,
    fun q h => markHandled_handled a.table p q h,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun f hf => ⟨f, hf, rfl, rfl, rfl⟩,
    List.prefix_refl _⟩

/-- `markHandled` fulfils its row: on an allocated promise it moves up `Le`,
keeps `WF`, and leaves the promise's handled bit set. Web IDL
`op.mark-a-promise-as-handled` (HANDLEDOP, 356060..356713). Adequacy law;
DB-04 M2. -/
theorem markHandled_implements :
    ∀ {value reason body : Type} (promise : Nat),
      Agent.Implements (Agent.Op.markHandled promise : Agent.Op value reason body) := by
  intro value reason body promise a c hw hpre
  refine ⟨Le.markHandled a promise, WF.markHandled hw promise, ?_⟩
  obtain ⟨s, hg⟩ : ∃ s, a.table.get promise = some s := Option.isSome_iff_exists.mp hpre
  exact Promise.Table.markHandled_marked a.table promise (getCell_isSome_of_get _ _ _ hg)

/-! ## 11. `perform` -/

/-- Minting a derived capability keeps every allocated identity allocated. -/
private theorem mintFor_isSome {value reason body : Type} (a : Agent value reason body)
    (derive : Bool) (p : Nat) (h : (a.table.getCell p).isSome = true) :
    ((mintFor a derive).1.table.getCell p).isSome = true := by
  cases derive with
  | false => exact h
  | true => exact getCell_fresh_isSome a.table _ p h

/-- On an allocated promise every branch of `perform` answers the minted
capability behind `some`, keeps the function records `mintFor` left, and
leaves `mintFor`'s table with the promise marked handled. -/
private theorem perform_allocated {value reason body : Type} (a : Agent value reason body)
    (promise : Nat) (onFulfilled onRejected : Option body) (derive : Bool)
    (s : Promise.State value reason) (hg : a.table.get promise = some s) :
    (perform a promise onFulfilled onRejected derive).2 = some (mintFor a derive).2 ∧
      (perform a promise onFulfilled onRejected derive).1.functions =
        (mintFor a derive).1.functions ∧
      (perform a promise onFulfilled onRejected derive).1.table =
        Promise.Table.markHandled (mintFor a derive).1.table promise := by
  cases s with
  | pending =>
      rw [perform_pending a promise onFulfilled onRejected derive hg]; exact ⟨rfl, rfl, rfl⟩
  | fulfilled v =>
      rw [perform_fulfilled a promise v onFulfilled onRejected derive hg]
      exact ⟨rfl, rfl, rfl⟩
  | rejected x =>
      rw [perform_rejected a promise x onFulfilled onRejected derive hg]
      exact ⟨rfl, rfl, rfl⟩

/-- The pending branch of `perform` keeps `WF`: both new records take the
fresh registration identity, which no held or registered record has, and the
capability they carry is minted. -/
private theorem WF.performPending {value reason body : Type} {b : Agent value reason body}
    (hw : WF b) (p : Nat) (onFulfilled onRejected : Option body)
    (cap : Option Promise.Capability) (hcap : ∀ c, cap = some c → Minted b c) :
    WF { b with
      table := Promise.Table.markHandled b.table p,
      reactions := (Promise.Reactions.add b.reactions p onFulfilled onRejected cap).1 } := by
  have hm := WF.markHandled hw p
  have hF : ∀ r ∈ b.reactions.fulfill, r.id < b.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hH : ∀ r ∈ b.held, r.id < b.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_right _ hr)
  refine ⟨hm.tableNodup, hm.tableBelow, hm.functionsBelow, hm.functionsAllocated,
    hm.resolvedSettled, ?_, ?_, ?_, hm.functionsNodup, ?_, ?_, hm.runningActive, ?_,
    hm.settlementsCoherent⟩
  · -- reactionsBelow
    intro r hr
    show r.id < b.reactions.next + 1
    rcases List.mem_append.mp hr with hfr | hheld
    · rcases List.mem_append.mp hfr with hful | hrej
      · rcases List.mem_append.mp hful with hold | hnew
        · exact Nat.lt_succ_of_lt
            (hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_left _ hold)))
        · rw [List.mem_singleton.mp hnew]; exact Nat.lt_succ_self _
      · rcases List.mem_append.mp hrej with hold | hnew
        · exact Nat.lt_succ_of_lt
            (hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_right _ hold)))
        · rw [List.mem_singleton.mp hnew]; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hw.reactionsBelow r (List.mem_append_right _ hheld))
  · -- queueBelow
    intro j hj
    exact Nat.lt_succ_of_lt (hw.queueBelow j hj)
  · -- paired
    exact Promise.Reactions.add_paired b.reactions p onFulfilled onRejected cap hw.paired
  · -- heldDistinct
    show (b.held.map Promise.Reaction.id ++ (b.reactions.fulfill ++
      [Promise.Reaction.mk b.reactions.next p Promise.ReactionType.fulfill onFulfilled cap
        Promise.ReactionPhase.waiting]).map Promise.Reaction.id).Nodup
    rw [List.map_append, ← List.append_assoc]
    refine List.nodup_append.mpr ⟨hw.heldDistinct, List.nodup_cons.mpr ⟨List.not_mem_nil,
      List.nodup_nil⟩, ?_⟩
    intro x hx y hy
    have hy' : y = b.reactions.next := List.mem_singleton.mp hy
    rw [hy']
    rcases List.mem_append.mp hx with hxh | hxf
    · obtain ⟨r, hr, hrx⟩ := List.mem_map.mp hxh
      rw [← hrx]
      exact Nat.ne_of_lt (hH r hr)
    · obtain ⟨r, hr, hrx⟩ := List.mem_map.mp hxf
      rw [← hrx]
      exact Nat.ne_of_lt (hF r hr)
  · -- queuedKnown
    intro j hj
    rw [reactionOf_isSome]
    have hk := (reactionOf_isSome b j).mp (hw.queuedKnown j hj)
    rcases hk with hh | hl
    · exact Or.inl hh
    · refine Or.inr ?_
      cases harg : j.argument with
      | ok v =>
          rw [harg] at hl
          show j.reaction ∈ (b.reactions.fulfill ++ _).map Promise.Reaction.id
          rw [List.map_append]
          exact List.mem_append_left _ hl
      | error x =>
          rw [harg] at hl
          show j.reaction ∈ (b.reactions.reject ++ _).map Promise.Reaction.id
          rw [List.map_append]
          exact List.mem_append_left _ hl
  · -- capabilityStored
    intro r hr c hc
    rcases List.mem_append.mp hr with hfr | hheld
    · rcases List.mem_append.mp hfr with hful | hrej
      · rcases List.mem_append.mp hful with hold | hnew
        · exact hw.capabilityStored r
            (List.mem_append_left _ (List.mem_append_left _ hold)) c hc
        · rw [List.mem_singleton.mp hnew] at hc
          exact hcap c hc
      · rcases List.mem_append.mp hrej with hold | hnew
        · exact hw.capabilityStored r
            (List.mem_append_left _ (List.mem_append_right _ hold)) c hc
        · rw [List.mem_singleton.mp hnew] at hc
          exact hcap c hc
    · exact hw.capabilityStored r (List.mem_append_right _ hheld) c hc

/-- A settled branch of `perform` keeps `WF`: the held record and the queued
job take the fresh registration identity, so the job names that record. -/
private theorem WF.performSettled {value reason body : Type} {b : Agent value reason body}
    (hw : WF b) (p : Nat) (kind : Promise.ReactionType) (handler : Option body)
    (cap : Option Promise.Capability) (hcap : ∀ c, cap = some c → Minted b c)
    (arg : Except reason value) :
    WF { b with
      table := Promise.Table.markHandled b.table p,
      reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
      queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
      held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] } := by
  have hm := WF.markHandled hw p
  have hF : ∀ r ∈ b.reactions.fulfill, r.id < b.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hH : ∀ r ∈ b.held, r.id < b.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_right _ hr)
  refine ⟨hm.tableNodup, hm.tableBelow, hm.functionsBelow, hm.functionsAllocated,
    hm.resolvedSettled, ?_, ?_, hw.paired, hm.functionsNodup, ?_, ?_, hm.runningActive, ?_,
    hm.settlementsCoherent⟩
  · -- reactionsBelow
    intro r hr
    show r.id < b.reactions.next + 1
    rcases List.mem_append.mp hr with hfr | hheld
    · exact Nat.lt_succ_of_lt (hw.reactionsBelow r (List.mem_append_left _ hfr))
    · rcases List.mem_append.mp hheld with hold | hnew
      · exact Nat.lt_succ_of_lt (hH r hold)
      · rw [List.mem_singleton.mp hnew]; exact Nat.lt_succ_self _
  · -- queueBelow
    intro j hj
    show j.reaction < b.reactions.next + 1
    rcases List.mem_append.mp hj with hold | hnew
    · exact Nat.lt_succ_of_lt (hw.queueBelow j hold)
    · rw [List.mem_singleton.mp hnew]; exact Nat.lt_succ_self _
  · -- heldDistinct
    show ((b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2]).map
      Promise.Reaction.id ++ b.reactions.fulfill.map Promise.Reaction.id).Nodup
    have hnd := List.nodup_append.mp hw.heldDistinct
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hnd.1,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩, hnd.2.1, ?_⟩
    · intro x hx y hy
      have hy' : y = b.reactions.next := List.mem_singleton.mp hy
      rw [hy']
      obtain ⟨r, hr, hrx⟩ := List.mem_map.mp hx
      rw [← hrx]
      exact Nat.ne_of_lt (hH r hr)
    · intro x hx y hy
      rcases List.mem_append.mp hx with hxh | hxn
      · exact hnd.2.2 x hxh y hy
      · have hx' : x = b.reactions.next := List.mem_singleton.mp hxn
        rw [hx']
        obtain ⟨r, hr, hry⟩ := List.mem_map.mp hy
        rw [← hry]
        exact (Nat.ne_of_lt (hF r hr)).symm
  · -- queuedKnown
    intro j hj
    rw [reactionOf_isSome]
    show j.reaction ∈ (b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2]).map
        Promise.Reaction.id ∨ _
    rw [List.map_append]
    rcases List.mem_append.mp hj with hold | hnew
    · have hk := (reactionOf_isSome b j).mp (hw.queuedKnown j hold)
      rcases hk with hh | hl
      · exact Or.inl (List.mem_append_left _ hh)
      · exact Or.inr hl
    · rw [List.mem_singleton.mp hnew]
      exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  · -- capabilityStored
    intro r hr c hc
    rcases List.mem_append.mp hr with hfr | hheld
    · exact hw.capabilityStored r (List.mem_append_left _ hfr) c hc
    · rcases List.mem_append.mp hheld with hold | hnew
      · exact hw.capabilityStored r (List.mem_append_right _ hold) c hc
      · rw [List.mem_singleton.mp hnew] at hc
        exact hcap c hc

/-- `perform` keeps `WF`, on every branch and with or without a derived
capability. -/
private theorem WF.perform {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (p : Nat) (onFulfilled onRejected : Option body) (derive : Bool) :
    WF (perform a p onFulfilled onRejected derive).1 := by
  cases hg : a.table.get p with
  | none => rw [perform_missing a p onFulfilled onRejected derive hg]; exact hw
  | some s =>
      cases derive with
      | false =>
          have hcap : ∀ c, (none : Option Promise.Capability) = some c → Minted a c :=
            fun _ h => (by cases h)
          cases s with
          | pending =>
              rw [perform_pending a p onFulfilled onRejected false hg]
              exact WF.performPending hw p onFulfilled onRejected none hcap
          | fulfilled v =>
              rw [perform_fulfilled a p v onFulfilled onRejected false hg]
              exact WF.performSettled hw p _ onFulfilled none hcap (Except.ok v)
          | rejected x =>
              rw [perform_rejected a p x onFulfilled onRejected false hg]
              exact WF.performSettled hw p _ onRejected none hcap (Except.error x)
      | true =>
          have hw1 := WF.newPromise hw
          have hcap : ∀ c, some (Whatwg.Ecma262.Agent.newPromise a).2 = some c →
              Minted (Whatwg.Ecma262.Agent.newPromise a).1 c := by
            intro c hc
            cases hc
            exact newPromise_minted a
          cases s with
          | pending =>
              rw [perform_pending a p onFulfilled onRejected true hg]
              exact WF.performPending hw1 p onFulfilled onRejected _ hcap
          | fulfilled v =>
              rw [perform_fulfilled a p v onFulfilled onRejected true hg]
              exact WF.performSettled hw1 p _ onFulfilled _ hcap (Except.ok v)
          | rejected x =>
              rw [perform_rejected a p x onFulfilled onRejected true hg]
              exact WF.performSettled hw1 p _ onRejected _ hcap (Except.error x)

/-- A step that marks one promise handled, grows the registration cursor and
touches no other part of the order moves the agent up `Le`. -/
private theorem Le.ofMark {value reason body : Type} (b b' : Agent value reason body) (p : Nat)
    (ht : b'.table = Promise.Table.markHandled b.table p)
    (hr : b.reactions.next ≤ b'.reactions.next) (hf : b'.functions = b.functions)
    (hn : b'.nextFunction = b.nextFunction) (hs : b'.settlements = b.settlements) :
    Le b b' := by
  have hm := Le.markHandled b p
  exact ⟨fun q h => ht ▸ hm.allocated q h, fun q s h hs' => ht ▸ hm.settled q s h hs',
    fun q h => ht ▸ hm.handled q h, ht ▸ hm.tableNext, hr, Nat.le_of_eq hn.symm,
    fun f hf' => ⟨f, hf ▸ hf', rfl, rfl, rfl⟩, hs ▸ List.prefix_refl _⟩

/-- `perform` moves the agent up `Le`: minting is a `newPromise`, and every
branch then only marks the promise and grows the registration cursor. -/
private theorem Le.perform {value reason body : Type} (a : Agent value reason body) (p : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool) :
    Le a (Whatwg.Ecma262.Agent.perform a p onFulfilled onRejected derive).1 := by
  cases hg : a.table.get p with
  | none => rw [perform_missing a p onFulfilled onRejected derive hg]; exact Le.refl a
  | some s =>
      have hmint : Le a (mintFor a derive).1 := by
        cases derive with
        | false => exact Le.refl a
        | true => exact Le.newPromise a
      cases s with
      | pending =>
          rw [perform_pending a p onFulfilled onRejected derive hg]
          exact Le.trans hmint (Le.ofMark _ _ p rfl (by cases derive <;> exact Nat.le_succ _) rfl
            rfl rfl)
      | fulfilled v =>
          rw [perform_fulfilled a p v onFulfilled onRejected derive hg]
          exact Le.trans hmint (Le.ofMark _ _ p rfl (by cases derive <;> exact Nat.le_succ _) rfl
            rfl rfl)
      | rejected x =>
          rw [perform_rejected a p x onFulfilled onRejected derive hg]
          exact Le.trans hmint (Le.ofMark _ _ p rfl (by cases derive <;> exact Nat.le_succ _) rfl
            rfl rfl)

/-- `perform` fulfils its row: on an allocated promise it moves up `Le`, keeps
`WF`, and leaves the promise handled; with `derive` it answers a capability
that is minted and whose promise is pending, and without it answers
`some none`. `op.performpromisethen` (THEN, 2740635..2743669); Web IDL
`op.dfn-perform-steps-once-promise-is-settled` (REACT, 350075..352408) steps 6
to 8 when `derive` is set. Adequacy law; DB-04 M2. -/
theorem perform_implements :
    ∀ {value reason body : Type} (promise : Nat) (onFulfilled onRejected : Option body)
      (derive : Bool),
      Agent.Implements (Agent.Op.perform promise onFulfilled onRejected derive :
        Agent.Op value reason body) := by
  intro value reason body promise onFulfilled onRejected derive a c hw hpre
  refine ⟨Le.perform a promise onFulfilled onRejected derive,
    WF.perform hw promise onFulfilled onRejected derive, ?_⟩
  obtain ⟨s, hg⟩ : ∃ s, a.table.get promise = some s := Option.isSome_iff_exists.mp hpre
  obtain ⟨hans, hfun, htab⟩ := perform_allocated a promise onFulfilled onRejected derive s hg
  refine ⟨?_, ?_⟩
  · show (Promise.Table.getCell
      (Whatwg.Ecma262.Agent.perform a promise onFulfilled onRejected derive).1.table
      promise).map Promise.Cell.handled = some true
    rw [htab]
    exact Promise.Table.markHandled_marked _ promise
      (mintFor_isSome a derive promise (getCell_isSome_of_get _ _ _ hg))
  · cases derive with
    | false =>
        refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
        show (Whatwg.Ecma262.Agent.perform a promise onFulfilled onRejected false).2 = some none
        rw [hans]
        rfl
    | true =>
        refine ⟨fun _ => ⟨(Whatwg.Ecma262.Agent.newPromise a).2, ?_, ?_, ?_⟩,
          fun h => Bool.noConfusion h⟩
        · show (Whatwg.Ecma262.Agent.perform a promise onFulfilled onRejected true).2 = _
          rw [hans]
          rfl
        · obtain ⟨f, hf, h1, h2, h3⟩ := newPromise_minted a
          refine ⟨f, ?_, h1, h2, h3⟩
          show f ∈ (Whatwg.Ecma262.Agent.perform a promise onFulfilled onRejected true).1.functions
          rw [hfun]
          exact hf
        · show Promise.Table.get
            (Whatwg.Ecma262.Agent.perform a promise onFulfilled onRejected true).1.table
            a.table.next = _
          rw [htab, markHandled_get]
          exact Promise.Table.fresh_get a.table Promise.State.pending hw.getCell_next

/-! ## 12. `startJob`, `finishJob`, `enterScript` and `leaveScript`

The activation operations. Each disabled branch leaves the agent unchanged;
each enabled one changes only the activation, the running job and, for
`startJob`, the queue's head, or, for `finishJob`, what `callFunctions` does. -/

/-- Returning to a checkpoint with nothing running keeps `WF`. -/
private theorem WF.idle {value reason body : Type} {a : Agent value reason body} (hw : WF a) :
    WF { a with active := Jobs.Active.checkpoint, running := none } :=
  ⟨hw.tableNodup, hw.tableBelow, hw.functionsBelow, hw.functionsAllocated, hw.resolvedSettled,
    hw.reactionsBelow, hw.queueBelow, hw.paired, hw.functionsNodup, hw.heldDistinct,
    hw.queuedKnown, ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩, hw.capabilityStored,
    hw.settlementsCoherent⟩

/-- Under `WF`, away from a job activation nothing runs. -/
private theorem WF.running_none {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (h : ∀ s, a.active ≠ Jobs.Active.job s) : a.running = none := by
  cases hr : a.running with
  | none => rfl
  | some j => exact absurd (hw.runningActive.1 j hr) (h j.reaction)

/-- With nothing running, moving to an activation that is not a job keeps
`WF`. -/
private theorem WF.withActive {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (act : Jobs.Active) (hr : a.running = none)
    (hact : ∀ s, act ≠ Jobs.Active.job s) : WF { a with active := act } :=
  ⟨hw.tableNodup, hw.tableBelow, hw.functionsBelow, hw.functionsAllocated, hw.resolvedSettled,
    hw.reactionsBelow, hw.queueBelow, hw.paired, hw.functionsNodup, hw.heldDistinct,
    hw.queuedKnown,
    ⟨fun j h => absurd (hr.symm.trans h) (fun e => (by cases e)),
      fun s h => absurd h (hact s)⟩,
    hw.capabilityStored, hw.settlementsCoherent⟩

/-- An agent that differs only outside the order's eight clauses is later. -/
private theorem Le.ofEq {value reason body : Type} (b b' : Agent value reason body)
    (ht : b'.table = b.table) (hr : b'.reactions.next = b.reactions.next)
    (hf : b'.functions = b.functions) (hn : b'.nextFunction = b.nextFunction)
    (hs : b'.settlements = b.settlements) : Le b b' := by
  refine ⟨fun p h => ?_, fun p s h _ => ?_, fun p h => ?_, ?_, Nat.le_of_eq hr.symm,
    Nat.le_of_eq hn.symm, fun f hf' => ⟨f, hf ▸ hf', rfl, rfl, rfl⟩, ?_⟩
  · rw [ht]; exact h
  · rw [ht]; exact h
  · rw [ht]; exact h
  · rw [ht]; exact Nat.le_refl _
  · rw [hs]; exact List.prefix_refl _

/-- `startJob` keeps `WF`: the started job leaves the queue and becomes the
running job at its own serial. -/
private theorem WF.startJob {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) : WF (startJob a).1 := by
  cases ha : a.active with
  | checkpoint =>
      cases hq : a.queue.pending with
      | nil => rw [startJob_empty a hq]; exact hw
      | cons job rest =>
          rw [startJob_checkpoint a job rest ha hq]
          refine ⟨hw.tableNodup, hw.tableBelow, hw.functionsBelow, hw.functionsAllocated,
            hw.resolvedSettled, hw.reactionsBelow, ?_, hw.paired, hw.functionsNodup,
            hw.heldDistinct, ?_, ?_, hw.capabilityStored, hw.settlementsCoherent⟩
          · intro j hj
            exact hw.queueBelow j (hq ▸ List.mem_cons_of_mem job hj)
          · intro j hj
            exact hw.queuedKnown j (hq ▸ List.mem_cons_of_mem job hj)
          · refine ⟨fun j h => ?_, fun _ _ => rfl⟩
            cases h
            rfl
  | script =>
      rw [startJob_blocked a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | intrinsic _ =>
      rw [startJob_blocked a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | job _ =>
      rw [startJob_blocked a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw

/-- `startJob` moves the agent up `Le`: it touches none of the order's
clauses. -/
private theorem Le.startJob {value reason body : Type} (a : Agent value reason body) :
    Le a (Whatwg.Ecma262.Agent.startJob a).1 := by
  cases ha : a.active with
  | checkpoint =>
      cases hq : a.queue.pending with
      | nil => rw [startJob_empty a hq]; exact Le.refl a
      | cons job rest =>
          rw [startJob_checkpoint a job rest ha hq]
          exact Le.ofEq _ _ rfl rfl rfl rfl rfl
  | script => rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]; exact Le.refl a
  | intrinsic _ =>
      rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]; exact Le.refl a
  | job _ => rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]; exact Le.refl a

/-- `startJob` fulfils its row: at a checkpoint with a job queued it moves up
`Le`, keeps `WF`, and answers a job with its record's handler, which is then
the running job at its own serial (the job is the queue's head, by
`startJob_serial`). `requirement.jobs.1`
(RUNCOND, 625769..626250), `requirement.jobs.2` (ONEJOB, 626257..626350) and
`requirement.hostenqueuepromisejob.3` (ORDER, 634739..634841). Adequacy law;
DB-04 M2. -/
theorem startJob_implements :
    ∀ {value reason body : Type},
      Agent.Implements (Agent.Op.startJob : Agent.Op value reason body) := by
  intro value reason body a c hw hpre
  refine ⟨Le.startJob a, WF.startJob hw, ?_⟩
  obtain ⟨ha, hne⟩ := hpre
  cases hq : a.queue.pending with
  | nil => exact absurd hq hne
  | cons job rest =>
      show ∃ j, (Whatwg.Ecma262.Agent.startJob a).2 =
          some (j, (reactionOf (Whatwg.Ecma262.Agent.startJob a).1 j).bind
            Promise.Reaction.handler) ∧
        (Whatwg.Ecma262.Agent.startJob a).1.active = Jobs.Active.job j.reaction ∧
        (Whatwg.Ecma262.Agent.startJob a).1.running = some j
      rw [startJob_checkpoint a job rest ha hq]
      exact ⟨job, rfl, rfl, rfl⟩

/-- `finishJob` keeps `WF`: whatever its record and capability, it settles
through `callFunctions` at most and then returns to a checkpoint. -/
private theorem WF.finishJob {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (decision : Except reason value) : WF (finishJob a decision) := by
  cases hrun : a.running with
  | none => rw [finishJob_idle a decision hrun]; exact hw
  | some job =>
      cases ha : a.active with
      | job s =>
          cases hr : reactionOf a job with
          | none => rw [finishJob_unknown a decision s job ha hrun hr]; exact WF.idle hw
          | some r =>
              cases hc : r.capability with
              | none =>
                  rw [finishJob_no_capability a decision s job r ha hrun hr hc]
                  exact WF.idle hw
              | some cap =>
                  rw [finishJob_capability a decision s job r cap ha hrun hr hc]
                  exact WF.idle (WF.callFunctions hw _ _ (resolve_unique hw cap))
      | checkpoint =>
          rw [finishJob_not_job a decision
            (by rw [ha]; exact fun _ h => Jobs.Active.noConfusion h)]
          exact hw
      | script =>
          rw [finishJob_not_job a decision
            (by rw [ha]; exact fun _ h => Jobs.Active.noConfusion h)]
          exact hw
      | intrinsic _ =>
          rw [finishJob_not_job a decision
            (by rw [ha]; exact fun _ h => Jobs.Active.noConfusion h)]
          exact hw

/-- `finishJob` moves the agent up `Le`, on every branch. -/
private theorem Le.finishJob {value reason body : Type} (a : Agent value reason body)
    (decision : Except reason value) : Le a (Whatwg.Ecma262.Agent.finishJob a decision) := by
  cases hrun : a.running with
  | none => rw [finishJob_idle a decision hrun]; exact Le.refl a
  | some job =>
      cases ha : a.active with
      | job s =>
          cases hr : reactionOf a job with
          | none =>
              rw [finishJob_unknown a decision s job ha hrun hr]
              exact Le.ofEq _ _ rfl rfl rfl rfl rfl
          | some r =>
              cases hc : r.capability with
              | none =>
                  rw [finishJob_no_capability a decision s job r ha hrun hr hc]
                  exact Le.ofEq _ _ rfl rfl rfl rfl rfl
              | some cap =>
                  rw [finishJob_capability a decision s job r cap ha hrun hr hc]
                  exact Le.trans (Le.callFunctions a _ _) (Le.ofEq _ _ rfl rfl rfl rfl rfl)
      | checkpoint =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ h => by cases h)]
          exact Le.refl a
      | script =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ h => by cases h)]
          exact Le.refl a
      | intrinsic _ =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ h => by cases h)]
          exact Le.refl a

/-- `finishJob` fulfils its row: while a job runs it moves up `Le`, keeps
`WF`, and leaves the agent at a checkpoint with nothing running; under `WF`
a job activation has a running job, so the enabled branch is taken.
`op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner steps 4 to 9 and
`requirement.jobs.3` (COMPLETE, 626357..626479). Adequacy law; DB-04 M2. -/
theorem finishJob_implements :
    ∀ {value reason body : Type} (decision : Except reason value),
      Agent.Implements (Agent.Op.finishJob decision : Agent.Op value reason body) := by
  intro value reason body decision a c hw hpre
  refine ⟨Le.finishJob a decision, WF.finishJob hw decision, ?_⟩
  obtain ⟨s, ha⟩ := hpre
  show (Whatwg.Ecma262.Agent.finishJob a decision).active = Jobs.Active.checkpoint ∧
    (Whatwg.Ecma262.Agent.finishJob a decision).running = none
  cases hrun : a.running with
  | none =>
      have := hw.runningActive.2 s ha
      rw [hrun] at this
      cases this
  | some job =>
      cases hr : reactionOf a job with
      | none => rw [finishJob_unknown a decision s job ha hrun hr]; exact ⟨rfl, rfl⟩
      | some r =>
          cases hc : r.capability with
          | none =>
              rw [finishJob_no_capability a decision s job r ha hrun hr hc]; exact ⟨rfl, rfl⟩
          | some cap =>
              rw [finishJob_capability a decision s job r cap ha hrun hr hc]; exact ⟨rfl, rfl⟩

/-- `enterScript` keeps `WF`: at a checkpoint nothing runs, and a script is
not a job activation. -/
private theorem WF.enterScript {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) : WF (enterScript a) := by
  cases ha : a.active with
  | checkpoint =>
      rw [enterScript_checkpoint a ha]
      exact WF.withActive hw _
        (hw.running_none (by rw [ha]; exact fun _ h => Jobs.Active.noConfusion h))
        (fun _ h => Jobs.Active.noConfusion h)
  | script =>
      rw [enterScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | intrinsic _ =>
      rw [enterScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | job _ =>
      rw [enterScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw

/-- `enterScript` moves the agent up `Le`: it changes only the activation. -/
private theorem Le.enterScript {value reason body : Type} (a : Agent value reason body) :
    Le a (Whatwg.Ecma262.Agent.enterScript a) := by
  unfold Whatwg.Ecma262.Agent.enterScript
  cases a.active <;> first | exact Le.refl a | exact Le.ofEq _ _ rfl rfl rfl rfl rfl

/-- `enterScript` fulfils its row: at a checkpoint it moves up `Le`, keeps
`WF`, and leaves the agent in a script. `requirement.jobs.1` (RUNCOND). Adequacy
law; DB-04 M2. -/
theorem enterScript_implements :
    ∀ {value reason body : Type},
      Agent.Implements (Agent.Op.enterScript : Agent.Op value reason body) := by
  intro value reason body a c hw hpre
  refine ⟨Le.enterScript a, WF.enterScript hw, ?_⟩
  show (Whatwg.Ecma262.Agent.enterScript a).active = Jobs.Active.script
  rw [enterScript_checkpoint a hpre]

/-- `leaveScript` keeps `WF`: in a script nothing runs, and a checkpoint is
not a job activation. -/
private theorem WF.leaveScript {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) : WF (leaveScript a) := by
  cases ha : a.active with
  | script =>
      rw [leaveScript_script a ha]
      exact WF.withActive hw _
        (hw.running_none (by rw [ha]; exact fun _ h => Jobs.Active.noConfusion h))
        (fun _ h => Jobs.Active.noConfusion h)
  | checkpoint =>
      rw [leaveScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | intrinsic _ =>
      rw [leaveScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw
  | job _ =>
      rw [leaveScript_other a (by rw [ha]; exact fun h => Jobs.Active.noConfusion h)]; exact hw

/-- `leaveScript` moves the agent up `Le`: it changes only the activation. -/
private theorem Le.leaveScript {value reason body : Type} (a : Agent value reason body) :
    Le a (Whatwg.Ecma262.Agent.leaveScript a) := by
  unfold Whatwg.Ecma262.Agent.leaveScript
  cases a.active <;> first | exact Le.refl a | exact Le.ofEq _ _ rfl rfl rfl rfl rfl

/-- `leaveScript` fulfils its row: in a script it moves up `Le`, keeps `WF`,
and returns the agent to a checkpoint. `requirement.jobs.1` (RUNCOND).
Adequacy law; DB-04 M2. -/
theorem leaveScript_implements :
    ∀ {value reason body : Type},
      Agent.Implements (Agent.Op.leaveScript : Agent.Op value reason body) := by
  intro value reason body a c hw hpre
  refine ⟨Le.leaveScript a, WF.leaveScript hw, ?_⟩
  show (Whatwg.Ecma262.Agent.leaveScript a).active = Jobs.Active.checkpoint
  rw [leaveScript_script a hpre]

/-! ## 13. Every operation

The per-operation lemmas assembled over the alphabet. `WF.step` and `Le.step`
hold for every operation, enabled or not, because a disabled one leaves the
agent unchanged. -/

/-- Every operation keeps `WF`, enabled or disabled. With `WF.empty` this is
the contract's "`WF` kept by every operation". Invariant law; DB-04 M1. -/
theorem WF.step :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (op : Agent.Op value reason body),
      Agent.WF a → Agent.WF (Agent.step a op).1 := by
  intro value reason body a op hw
  cases op with
  | newPromise => exact WF.newPromise hw
  | resolve cap v => exact WF.resolve hw cap v
  | reject cap r => exact WF.reject hw cap r
  | perform p f r d => exact WF.perform hw p f r d
  | markHandled p => exact WF.markHandled hw p
  | startJob => exact WF.startJob hw
  | finishJob d => exact WF.finishJob hw d
  | enterScript => exact WF.enterScript hw
  | leaveScript => exact WF.leaveScript hw

/-- Every operation moves a well-formed agent up the order, enabled or not.
Adequacy law; DB-04 M2, through `Le.trace`. -/
theorem Le.step :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (op : Agent.Op value reason body),
      Agent.WF a → Agent.Le a (Agent.step a op).1 := by
  intro value reason body a op _
  cases op with
  | newPromise => exact Le.newPromise a
  | resolve cap v => exact Le.callFunctions a _ _
  | reject cap r => exact Le.callFunctions a _ _
  | perform p f r d => exact Le.perform a p f r d
  | markHandled p => exact Le.markHandled a p
  | startJob => exact Le.startJob a
  | finishJob d => exact Le.finishJob a d
  | enterScript => exact Le.enterScript a
  | leaveScript => exact Le.leaveScript a

/-- The handler fulfils every row: all nine operations satisfy `Implements`.
Adequacy law; DB-04 M2. -/
theorem implements :
    ∀ {value reason body : Type} (op : Agent.Op value reason body), Agent.Implements op := by
  intro value reason body op
  cases op with
  | newPromise => exact newPromise_implements
  | resolve cap v => exact resolve_implements cap v
  | reject cap r => exact reject_implements cap r
  | perform p f r d => exact perform_implements p f r d
  | markHandled p => exact markHandled_implements p
  | startJob => exact startJob_implements
  | finishJob d => exact finishJob_implements d
  | enterScript => exact enterScript_implements
  | leaveScript => exact leaveScript_implements

/-! ## 14. The lifted laws

The landed store-level laws restated at the agent (the contract's section 9),
and the two counterexample rows the agent closes. -/

/-- `op.performpromisethen` (THEN, 2740635..2743669) step 12 at the agent: on
an allocated promise every branch of `perform` leaves the promise handled,
with or without a derived capability. Lifts the landed
`Promise.performPromiseThen_handled` (Q3b finding F1). Lifted law; DB-04 M1. -/
theorem perform_handled :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool),
      (a.table.getCell promise).isSome = true →
        ((Agent.perform a promise onFulfilled onRejected derive).1.table.getCell promise).map
          Promise.Cell.handled = some true := by
  intro value reason body a promise onFulfilled onRejected derive hcell
  obtain ⟨s, hg⟩ := get_of_getCell_isSome a.table promise hcell
  rw [(perform_allocated a promise onFulfilled onRejected derive s hg).2.2]
  exact Promise.Table.markHandled_marked _ promise (mintFor_isSome a derive promise hcell)

/-- THEN steps 10 and 11 at the agent: on a settled promise `perform` appends
to neither reaction list and grows `held` by exactly one record, which carries
the next registration identity and the derived capability, the link D17 needs
from a job to its capability. Lifts the landed `Promise.Reactions.mint_no_waiting`
(Q3b finding F2). Lifted law; DB-04 M1. -/
theorem perform_settled_lists :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool) (s : Promise.State value reason),
      a.table.get promise = some s → s ≠ Promise.State.pending →
        (Agent.perform a promise onFulfilled onRejected derive).1.reactions.fulfill =
            a.reactions.fulfill ∧
          (Agent.perform a promise onFulfilled onRejected derive).1.reactions.reject =
            a.reactions.reject ∧
          ∃ m : Promise.Reaction body,
            (Agent.perform a promise onFulfilled onRejected derive).1.held = a.held ++ [m] ∧
              m.id = a.reactions.next ∧ m.capability = (Agent.mintFor a derive).2 := by
  intro value reason body a promise onFulfilled onRejected derive s hg hs
  cases s with
  | pending => exact absurd rfl hs
  | fulfilled v =>
      rw [perform_fulfilled a promise v onFulfilled onRejected derive hg]
      exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩
  | rejected x =>
      rw [perform_rejected a promise x onFulfilled onRejected derive hg]
      exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩

/-- `op.fulfillpromise` (FULFILL, 2695419..2696230) and `op.rejectpromise`
(REJECT, 2699323..2700252) at the agent: settling a pending promise leaves no
reaction waiting on it in either list, which is how the model reads the
specification setting both reaction slots to undefined. Lifts the landed
`Promise.Table.settleAndTrigger_cleared` (Q3b finding F3). Lifted law; DB-04
M1. -/
theorem settle_cleared :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (result : Except reason value) (kind : Promise.ReactionType),
      a.table.get promise = some Promise.State.pending →
        Promise.Reactions.waitingOn (Agent.settle a promise result).reactions promise kind =
          [] := by
  intro value reason body a promise result kind h
  exact Promise.Table.settleAndTrigger_cleared a.table a.reactions a.queue promise result kind h

/-- FULFILL and REJECT at the agent: settling a pending promise appends exactly
one entry, the promise with its result, at the end of the settlement trace.
Lifts the landed `Promise.Table.settleTraced_pending` (Q3b finding F6). Lifted
law; DB-04 M2, since it observes settlement order. -/
theorem settle_trace :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body) (promise : Nat)
      (result : Except reason value),
      a.table.get promise = some Promise.State.pending →
        (Agent.settle a promise result).settlements = a.settlements ++ [(promise, result)] := by
  intro value reason body a promise result h
  exact Promise.Table.settleTraced_pending a.table a.settlements promise result h

/-- `op.createresolvingfunctions` (RESOLVING, 2692679..2695411) at the agent:
a capability's resolve and reject functions share one `[[AlreadyResolved]]`
record, so after `resolve`, a `reject` through the same capability changes
nothing (`WS-PROM-CE-042`). Lifts the landed
`Promise.ResolvingFunctions.callResolve_disables_reject`. Lifted law; DB-04
M1. -/
theorem resolve_then_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value) (r : reason),
      Agent.WF a → Agent.Minted a cap →
        Agent.reject (Agent.resolve a cap v) cap r = Agent.resolve a cap v := by
  intro value reason body a cap v r hw hm
  obtain ⟨f, hf, h1, h2, _⟩ := hm
  have hres := find?_unique a.functions _ (resolve_unique hw cap) f hf (beq_iff_eq.mpr h1)
  have hrej := find?_unique a.functions _ (reject_unique hw cap) f hf (beq_iff_eq.mpr h2)
  cases hfr : f.alreadyResolved with
  | true =>
      have e : Whatwg.Ecma262.Agent.resolve a cap v = a :=
        callFunctions_fired a _ _ f hres hfr
      rw [e]
      exact callFunctions_fired a _ _ f hrej hfr
  | false =>
      have e : Whatwg.Ecma262.Agent.resolve a cap v = _ :=
        callFunctions_fresh a _ (Except.ok v) f hres hfr
      rw [e]
      apply callFunctions_fired _ _ _
        (if (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) f then
          { f with alreadyResolved := true } else f)
      · show List.find? _ (a.functions.map _) = _
        rw [List.find?_map]
        have hc : ((fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) ∘
            (fun (g : Promise.ResolvingFunctions) =>
              if (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) g then
                { g with alreadyResolved := true } else g)) =
            (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) := by
          funext g
          show ((if _ then { g with alreadyResolved := true } else g).reject == cap.reject) =
            (g.reject == cap.reject)
          rw [(mark_fields (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve)
            g).2.1]
        rw [hc, hrej]
        rfl
      · show (if (f.resolve == cap.resolve) then { f with alreadyResolved := true }
          else f).alreadyResolved = true
        rw [beq_iff_eq.mpr h1]
        rfl

/-- RESOLVING at the agent, the other order: after `reject`, a `resolve`
through the same capability changes nothing (`WS-PROM-CE-042`). Lifts the
landed `Promise.ResolvingFunctions.callResolve_disables_reject`'s shared
marker. Lifted law; DB-04 M1. -/
theorem reject_then_resolve :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason) (v : value),
      Agent.WF a → Agent.Minted a cap →
        Agent.resolve (Agent.reject a cap r) cap v = Agent.reject a cap r := by
  intro value reason body a cap r v hw hm
  obtain ⟨f, hf, h1, h2, _⟩ := hm
  have hres := find?_unique a.functions _ (resolve_unique hw cap) f hf (beq_iff_eq.mpr h1)
  have hrej := find?_unique a.functions _ (reject_unique hw cap) f hf (beq_iff_eq.mpr h2)
  cases hfr : f.alreadyResolved with
  | true =>
      have e : Whatwg.Ecma262.Agent.reject a cap r = a :=
        callFunctions_fired a _ _ f hrej hfr
      rw [e]
      exact callFunctions_fired a _ _ f hres hfr
  | false =>
      have e : Whatwg.Ecma262.Agent.reject a cap r = _ :=
        callFunctions_fresh a _ (Except.error r) f hrej hfr
      rw [e]
      apply callFunctions_fired _ _ _
        (if (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) f then
          { f with alreadyResolved := true } else f)
      · show List.find? _ (a.functions.map _) = _
        rw [List.find?_map]
        have hc : ((fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) ∘
            (fun (g : Promise.ResolvingFunctions) =>
              if (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) g then
                { g with alreadyResolved := true } else g)) =
            (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) := by
          funext g
          show ((if _ then { g with alreadyResolved := true } else g).resolve == cap.resolve) =
            (g.resolve == cap.resolve)
          rw [(mark_fields (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject)
            g).1]
        rw [hc, hres]
        rfl
      · show (if (f.reject == cap.reject) then { f with alreadyResolved := true }
          else f).alreadyResolved = true
        rw [beq_iff_eq.mpr h2]
        rfl

/-- RESOLVING: a capability whose `[[Resolve]]` identity no stored function
carries settles nothing; `resolve` leaves the agent unchanged and has no
fallback to `Table.settle` (`WS-PROM-CE-041`). Law; DB-04 M1. -/
theorem resolve_unminted :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value),
      (∀ f ∈ a.functions, f.resolve ≠ cap.resolve) → Agent.resolve a cap v = a := by
  intro value reason body a cap v h
  apply callFunctions_none
  exact List.find?_eq_none.mpr (fun f hf hb => h f hf (beq_iff_eq.mp hb))

/-- RESOLVING: a capability whose `[[Reject]]` identity no stored function
carries settles nothing; `reject` leaves the agent unchanged
(`WS-PROM-CE-041`). Law; DB-04 M1. -/
theorem reject_unminted :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason),
      (∀ f ∈ a.functions, f.reject ≠ cap.reject) → Agent.reject a cap r = a := by
  intro value reason body a cap r h
  apply callFunctions_none
  exact List.find?_eq_none.mpr (fun f hf hb => h f hf (beq_iff_eq.mp hb))

/-- `requirement.jobs.1` (RUNCOND, 625769..626250): at a checkpoint with `job`
at the queue's head, `startJob` makes `job` the running job at the serial of
its own reaction identity, so job serials and reaction identities are one
supply (`WS-PROM-CE-046`). Law; DB-04 M1. -/
theorem startJob_serial :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
      a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
        (Agent.startJob a).1.active = Jobs.Active.job job.reaction ∧
          (Agent.startJob a).1.running = some job := by
  intro value reason body a job rest ha hq
  rw [startJob_checkpoint a job rest ha hq]
  exact ⟨rfl, rfl⟩

/-! ## 15. Runs, and the FIFO law lifted to them

A run folds the step over a list of operations and collects the jobs
`startJob` answered, in start order. Over any run, the started jobs followed
by the still-queued jobs are the initially queued jobs followed by the jobs
enqueued during the run: `Jobs.run_fifo` and `Jobs.hostEnqueuePromiseJob_order`
lifted to the agent. -/

/-- The jobs one step started: the job `startJob` answered, if it started one,
and none for every other operation. Run device; `Op.started_startJob` and
`Op.started_other` fix it. -/
def Op.started {value reason body : Type} :
    (op : Op value reason body) → op.Answer → List (Job value reason)
  | .startJob, ans => (ans.map Prod.fst).toList
  | _, _ => []

/-- `startJob` started the job it answered, if any. Defining equation; DB-04
M1. -/
theorem Op.started_startJob :
    ∀ {value reason body : Type}
      (ans : Agent.Op.Answer (Agent.Op.startJob : Agent.Op value reason body)),
      Agent.Op.started Agent.Op.startJob ans = (ans.map Prod.fst).toList := by
  intros; rfl

/-- Every other operation starts no job. Defining equation; DB-04 M1. -/
theorem Op.started_other :
    ∀ {value reason body : Type} (op : Agent.Op value reason body) (ans : Agent.Op.Answer op),
      op ≠ Agent.Op.startJob → Agent.Op.started op ans = [] := by
  intro value reason body op ans h
  cases op with
  | startJob => exact absurd rfl h
  | newPromise => rfl
  | resolve _ _ => rfl
  | reject _ _ => rfl
  | perform _ _ _ _ => rfl
  | markHandled _ => rfl
  | finishJob _ => rfl
  | enterScript => rfl
  | leaveScript => rfl

/-- Run a list of operations from an agent: the agent the last step leaves,
and the jobs the run started, oldest first. Run device; `runOps_nil` and
`runOps_cons` fix it. -/
def runOps {value reason body : Type} :
    Agent value reason body → List (Op value reason body) →
      Agent value reason body × List (Job value reason)
  | a, [] => (a, [])
  | a, op :: ops =>
      ((runOps (step a op).1 ops).1,
        Op.started op (step a op).2 ++ (runOps (step a op).1 ops).2)

/-- The empty run leaves the agent and starts nothing. Defining equation;
DB-04 M1. -/
theorem runOps_nil :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body),
      Agent.runOps a [] = (a, []) := by
  intros; rfl

/-- A run is one step and then the rest; the first step's started jobs come
first. Defining equation; DB-04 M2, since it fixes start order. -/
theorem runOps_cons :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (op : Agent.Op value reason body) (ops : List (Agent.Op value reason body)),
      Agent.runOps a (op :: ops) =
        ((Agent.runOps (Agent.step a op).1 ops).1,
          Agent.Op.started op (Agent.step a op).2 ++
            (Agent.runOps (Agent.step a op).1 ops).2) := by
  intros; rfl

/-- Every agent a run reaches from a well-formed agent is well formed; with
`WF.empty`, every agent `runOps` reaches from `Agent.empty` is. Invariant law;
DB-04 M1. -/
theorem WF.runOps :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (ops : List (Agent.Op value reason body)),
      Agent.WF a → Agent.WF (Agent.runOps a ops).1 := by
  intro value reason body a ops
  induction ops generalizing a with
  | nil => exact id
  | cons op ops ih =>
      exact fun hw => ih (Whatwg.Ecma262.Agent.step a op).1 (WF.step a op hw)

/-- `callFunctions` only appends to the queue. -/
private theorem callFunctions_queue {value reason body : Type} (a : Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value) :
    ∃ later : List (Job value reason),
      (Whatwg.Ecma262.Agent.callFunctions a pick result).queue.pending =
        a.queue.pending ++ later := by
  cases hf : a.functions.find? pick with
  | none => rw [callFunctions_none a pick result hf]; exact ⟨[], (List.append_nil _).symm⟩
  | some f =>
      cases hfr : f.alreadyResolved with
      | true =>
          rw [callFunctions_fired a pick result f hf hfr]; exact ⟨[], (List.append_nil _).symm⟩
      | false =>
          rw [callFunctions_fresh a pick result f hf hfr]
          show ∃ later, (Whatwg.Ecma262.Agent.settle a f.promise result).queue.pending = _
          cases hp : Promise.Table.isPending a.table f.promise with
          | false =>
              rw [settle_notPending_eq a f.promise result hp]
              exact ⟨[], (List.append_nil _).symm⟩
          | true =>
              rw [settle_pending_eq a f.promise result hp]
              exact ⟨_, Promise.triggerReactions_order _ _ _ _ _⟩

/-- One step's FIFO: the job it started, followed by the queue it leaves, is
the old queue followed by the jobs it enqueued. -/
private theorem step_fifo {value reason body : Type} (a : Agent value reason body)
    (op : Op value reason body) :
    ∃ later : List (Job value reason),
      Op.started op (Whatwg.Ecma262.Agent.step a op).2 ++
          (Whatwg.Ecma262.Agent.step a op).1.queue.pending = a.queue.pending ++ later := by
  cases op with
  | newPromise => exact ⟨[], (List.append_nil _).symm⟩
  | resolve cap v =>
      obtain ⟨l, hl⟩ := callFunctions_queue a (fun f => f.resolve == cap.resolve) (Except.ok v)
      exact ⟨l, hl⟩
  | reject cap r =>
      obtain ⟨l, hl⟩ := callFunctions_queue a (fun f => f.reject == cap.reject) (Except.error r)
      exact ⟨l, hl⟩
  | perform p f r d =>
      show ∃ later, [] ++ (Whatwg.Ecma262.Agent.perform a p f r d).1.queue.pending = _
      cases hg : a.table.get p with
      | none =>
          rw [perform_missing a p f r d hg]
          exact ⟨[], (List.append_nil _).symm⟩
      | some s =>
          cases s with
          | pending =>
              rw [perform_pending a p f r d hg]
              cases d <;> exact ⟨[], (List.append_nil _).symm⟩
          | fulfilled v =>
              rw [perform_fulfilled a p v f r d hg]
              exact ⟨_, rfl⟩
          | rejected x =>
              rw [perform_rejected a p x f r d hg]
              exact ⟨_, rfl⟩
  | markHandled p => exact ⟨[], (List.append_nil _).symm⟩
  | startJob =>
      show ∃ later, Op.started Op.startJob (Whatwg.Ecma262.Agent.startJob a).2 ++
        (Whatwg.Ecma262.Agent.startJob a).1.queue.pending = _
      cases ha : a.active with
      | checkpoint =>
          cases hq : a.queue.pending with
          | nil =>
              rw [startJob_empty a hq]
              exact ⟨[], show [] ++ a.queue.pending = [] ++ [] by rw [hq]⟩
          | cons job rest =>
              rw [startJob_checkpoint a job rest ha hq]
              exact ⟨[], (List.append_nil _).symm⟩
      | script =>
          rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]
          exact ⟨[], (List.append_nil _).symm⟩
      | intrinsic _ =>
          rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]
          exact ⟨[], (List.append_nil _).symm⟩
      | job _ =>
          rw [startJob_blocked a (by rw [ha]; exact fun h => by cases h)]
          exact ⟨[], (List.append_nil _).symm⟩
  | finishJob d =>
      show ∃ later, [] ++ (Whatwg.Ecma262.Agent.finishJob a d).queue.pending = _
      cases hrun : a.running with
      | none => rw [finishJob_idle a d hrun]; exact ⟨[], (List.append_nil _).symm⟩
      | some job =>
          cases ha : a.active with
          | job s =>
              cases hr : reactionOf a job with
              | none =>
                  rw [finishJob_unknown a d s job ha hrun hr]
                  exact ⟨[], (List.append_nil _).symm⟩
              | some r =>
                  cases hc : r.capability with
                  | none =>
                      rw [finishJob_no_capability a d s job r ha hrun hr hc]
                      exact ⟨[], (List.append_nil _).symm⟩
                  | some cap =>
                      rw [finishJob_capability a d s job r cap ha hrun hr hc]
                      exact callFunctions_queue a _ _
          | checkpoint =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ h => by cases h)]
              exact ⟨[], (List.append_nil _).symm⟩
          | script =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ h => by cases h)]
              exact ⟨[], (List.append_nil _).symm⟩
          | intrinsic _ =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ h => by cases h)]
              exact ⟨[], (List.append_nil _).symm⟩
  | enterScript =>
      show ∃ later, [] ++ (Whatwg.Ecma262.Agent.enterScript a).queue.pending = _
      unfold Whatwg.Ecma262.Agent.enterScript
      cases a.active <;> exact ⟨[], (List.append_nil _).symm⟩
  | leaveScript =>
      show ∃ later, [] ++ (Whatwg.Ecma262.Agent.leaveScript a).queue.pending = _
      unfold Whatwg.Ecma262.Agent.leaveScript
      cases a.active <;> exact ⟨[], (List.append_nil _).symm⟩

/-- `requirement.hostenqueuepromisejob.3` (ORDER, 634739..634841, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`) over runs:
the jobs a run started, followed by the jobs still queued, are the jobs queued
at its start followed by the jobs enqueued during it, so no job starts before
one enqueued earlier. Lifts the landed `Jobs.run_fifo` and
`Jobs.hostEnqueuePromiseJob_order`. Lifted law; DB-04 M2. -/
theorem runOps_fifo :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (ops : List (Agent.Op value reason body)),
      ∃ later : List (Agent.Job value reason),
        (Agent.runOps a ops).2 ++ (Agent.runOps a ops).1.queue.pending =
          a.queue.pending ++ later := by
  intro value reason body a ops
  induction ops generalizing a with
  | nil => exact ⟨[], (List.append_nil _).symm⟩
  | cons op ops ih =>
      obtain ⟨l0, h0⟩ := step_fifo a op
      obtain ⟨l1, h1⟩ := ih (Whatwg.Ecma262.Agent.step a op).1
      refine ⟨l0 ++ l1, ?_⟩
      show (Op.started op (Whatwg.Ecma262.Agent.step a op).2 ++
          (runOps (Whatwg.Ecma262.Agent.step a op).1 ops).2) ++
          (runOps (Whatwg.Ecma262.Agent.step a op).1 ops).1.queue.pending = _
      rw [List.append_assoc, h1, ← List.append_assoc, h0, List.append_assoc]

/-- ORDER as the landed DB-05 specification: the jobs a run started are a
prefix of the order in which jobs were scheduled, `Jobs.FifoRequirement`.
Lifts `Jobs.run_fifo` and `Jobs.hostEnqueuePromiseJob_order`. Lifted law; DB-04
M2. -/
theorem runOps_fifoRequirement :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (ops : List (Agent.Op value reason body)),
      ∃ later : List (Agent.Job value reason),
        Jobs.FifoRequirement (a.queue.pending ++ later) (Agent.runOps a ops).2 := by
  intro value reason body a ops
  obtain ⟨later, h⟩ := runOps_fifo a ops
  exact ⟨later, ⟨_, h⟩⟩

end Whatwg.Ecma262.Agent
