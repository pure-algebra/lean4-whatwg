# The ECMAScript agent record (promise slice Q5, `PROMISE-PG-AGENT`)

Status: FROZEN / RED, Q5 breaker seat of review lane W, 2026-10-01, branch
`review/w9-q5-breaker` from `b0d35e2` (`R-W9: packets reach main only when
green; stacked packets; no new axiom-report modules`). Graph:
`docs/PROMISE-AGENT-DAG.md`. Rulings: R-W3 (binding brief), R-W1, R-W5,
R-W8 and R-W9. Design: `docs/research/2026-10-01-w9-agent-effects-design.md`
(the W9 design seat's record; its §3 is the declaration record this packet
freezes, with the changes §17 lists).

This packet is breaker-owned. Statements are the breaker's: a builder may
repair the elaboration of an `example`'s proof but may not weaken, delete or
replace a frozen ascription, law, mask, decision or acceptance condition.
A builder that finds a frozen statement false stops and reports (R-W9).

The Lean batteries are the authority on names and propositions; the Lean in
this file is a reading aid.

Read first, in this order: `COORDINATION.md` rulings R-W1, R-W3, R-W5, R-W8
and R-W9; the design document in full;
`test/contracts/promise-first-packet.contract.md` and its Q3b addendum
`test/contracts/promise-first-packet-q3b.contract.md` (the landed surface
this packet contains); `docs/PROMISE-DAG.md`;
`test/counterexamples/promise/ATTACKS.md`, section "Q5 agent packet".

## 1. Claim boundary

The packet freezes an ECMAScript agent record that contains the landed
promise table, reaction lists and reaction-job queue, one total step function
over nine first-order operations, an invariant `WF` that every operation
keeps, the operations' laws in the handler-adequacy shape of the design's
§3.7, the repair of debt D46 (Web IDL "react" followed by "resolve" enqueues
the reaction's job), the Web IDL verbs over the agent, and an
`Effects.Signature` face with a canonical, a lens and a sum handler.

It grants no coverage state, no host observation, no equivalence with any
engine, and no claim about `Whatwg.Streams`. Both promise-lane censuses stay
as they are; every census row cited here anchors a declaration and is never a
numerator. Six ES2026 rows are candidates for `green` once the coverage seat
joins them step by step (`requirement.jobs.1`, `.2`, `.3`,
`requirement.hostenqueuepromisejob.3`, `op.fulfillpromise`,
`op.triggerpromisereactions`); this packet moves none of them.

Every theorem names its observation mask in its battery and in §12, as
"DB-04 M1" or "DB-04 M2" (DB-04's masks: M1 is chunk sequence plus terminal
outcome, M2 is full settlement order). For this layer a statement is
DB-04 M2 when it observes the order of the settlement trace or of the job
queue, and DB-04 M1 otherwise. No Lean declaration of this packet is named
`m1` or `m2` (R-W3, R-W5), and `Effects.Trace.Mask` is not used.

What the packet does **not** model is §16.

## 2. Pins

| Item | Value |
| --- | --- |
| this repository | `review/w9-q5-breaker`, based on `b0d35e2bea772fc6dd2fb44a0cdac8f0afc2eaa7` |
| ECMA-262 source | `vendor/ecma262-0248456c/spec.html`, `tc39/ecma262` `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026`, SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |
| Web IDL source | `vendor/whatwg-webidl-a652053f/index.bs`, `whatwg/webidl` `a652053f1e74e4aaf647528deb174012ed6c909f`, SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` |
| ES2026 census | `generated/ecma262-census.tsv`, 77 rows |
| Web IDL census | `generated/webidl-census.tsv`, 124 rows |
| `effects` | `a4ee7a14248ee5976039b73039319efa87834986` (v0.8.0), the face imports `Effects.Algebra.Sum` only |
| lean4-effect4 (read only) | `refactor/phase1-phase3` at `b9d0d19fcb0cd39e87ebd11d4458b34a137f6b75`, read in source for §7.5; nothing built or run there |
| toolchain | `leanprover/lean4:v4.33.1` |

Byte offsets are 0-based and ends exclusive. No line number is cited
anywhere in this packet. Anchor aliases (FULFILL, REJECT, TRIGGER, NEWCAP,
RESOLVING, THEN, REACTJOB, ORDER, RUNCOND, ONEJOB, COMPLETE, NEWP, RESOLVEDW,
REJECTEDW, RESOLVE, REJECTOP, REACT, UPONF, UPONR, HANDLEDOP) expand through
`docs/PROMISE-DAG.md`'s alias table. Two clause rows are new to the lane:

| Alias | Census row | Span | Span digest |
| --- | --- | --- | --- |
| JOBS | `clause.jobs` | 624525..636548 | `871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf` |
| PINST | `clause.properties-of-promise-instances` | 2744135..2746691 | `f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d` |

## 3. The batteries and their counts

One battery per builder slice, so that each `known-red.txt` entry leaves when
its own slice lands. No `*AxiomReport.lean` module is written (R-W9): under a
strict prefix the axiom gate's ceiling is the receipt, and R-W5's conversion
gives each theorem its exact axiom set.

| Module | Slice | `#check (@n : T)` | of which theorems | instance checks | `#check_failure` | `example`s |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `WhatwgTest/Ecma262/AgentContract.lean` | B1 | 112 | 57 | 13 | 1 | 13 |
| `WhatwgTest/Ecma262/AgentLaws.lean` | B2 | 65 | 50 | 0 | 0 | 3 |
| `WhatwgTest/WebIdl/AgentContract.lean` | B3 | 23 | 14 | 0 | 0 | 5 |
| `WhatwgTest/Signatures/Ecma262Contract.lean` | B4 | 15 | 9 | 0 | 0 | 5 |
| **total** | | **215** | **130** | **13** | **1** | **26** |

The 215 ascriptions are 85 definitions (types, constructors, projections,
functions, predicates) and 130 theorem obligations. Every statement is
written in full: no `_` hole, and every implicit argument the body does not
determine is written. The `example`s are finite witnesses over `Unit`, `Nat`
and `Nat` (§15); they are executable evidence beside the laws, not
substitutes for them.

## 4. The record and the instance set

`Whatwg.Ecma262.Agent.Agent value reason body : Type`, in
`Whatwg/Ecma262/Agent.lean`, namespace `Whatwg.Ecma262.Agent`. Anchors JOBS
and PINST. It *contains* the landed stores by value (R-W3); nothing landed is
replaced or edited.

| Field | Type | Role |
| --- | --- | --- |
| `table` | `Promise.Table value reason` | landed; `[[PromiseState]]`, `[[PromiseResult]]`, `[[PromiseIsHandled]]` |
| `reactions` | `Promise.Reactions body` | landed; the two reaction lists and the registration cursor |
| `held` | `List (Promise.Reaction body)` | the records a settled `PerformPromiseThen` branch minted and handed to its caller (`Reactions.mint`, Q3b F2) |
| `queue` | `Jobs.Queue (Agent.Job value reason)` | landed; the reaction-job queue every landed operation writes |
| `functions` | `List Promise.ResolvingFunctions` | the stored resolving functions; the shared one-shot marker is state (D17, D46) |
| `nextFunction` | `Nat` | the function cursor (the landed "function seed") |
| `active` | `Jobs.Active` | landed activation |
| `running` | `Option (Agent.Job value reason)` | the job under evaluation; `Active.job` carries a serial only |
| `settlements` | `Promise.SettlementTrace value reason` | the landed F6 trace, now with an ECMA-262 producer (closes D20's "no producer") |

`Agent.Job value reason` is the `abbrev` `Jobs.ReactionJob (Except reason
value)` (R-W3: the queue payload is fixed). `Agent.empty` is the agent before
any promise, at a checkpoint (`empty_eq`). Three cursors stay: `table.next`,
`reactions.next` and `nextFunction`. A job's serial is its reaction identity:
`startJob` sets `Active.job job.reaction` (`startJob_checkpoint`,
`startJob_agree`, `startJob_serial`), which is the identity
`triggerReactions` writes as `.queued r.id`, so no fourth supply exists
(`WS-PROM-CE-046`). Every type is in `Type`.

**The instance set (R-W3; the design's decision 2, option a).** Frozen by the
B1 battery's §1:

- global `DecidableEq (Promise.Reaction body)` and `DecidableEq
  (Promise.Reactions body)`, conditional on `body` (`deriving instance`);
- global `Repr (Promise.Reactions body)`, `Repr Promise.ResolvingFunctions`,
  `Repr Jobs.Active`;
- `Whatwg.Ecma262.Agent.instDecidableEqExcept : {ε α : Type} →
  [DecidableEq ε] → [DecidableEq α] → DecidableEq (Except ε α)`, a **scoped**
  instance of the namespace `Whatwg.Ecma262.Agent`, never global, because
  Batteries declares a global one. The battery pins both directions:
  `#check_failure (inferInstance : DecidableEq (Except Nat Nat))` with its
  exact diagnostic under `#guard_msgs`, and the same `inferInstance` succeeding
  under `open Whatwg.Ecma262.Agent in`;
- `Agent` and `Op` derive `DecidableEq` and `Repr`, conditional on the three
  parameters, with no `Except` instance argument;
- the landed `Repr (Reaction Nat)` (the `E-50` receipt), `DecidableEq
  ResolvingFunctions` and `DecidableEq Active` stay.

This supersedes the `E-29` sentence "must not gain one silently" by ruling
R-W3; `WS-PROM-CE-015` is re-dispositioned at the Q5 landing, and
`Transform.State` stays `Repr`-only because its own `deriving` clause is
unchanged.

## 5. The nine operations and their answers

`Agent.Op value reason body` has nine constructors; every argument is data
(DB-02). `Agent.step : Agent → (op : Op) → Agent × op.Answer` is total. The
nine `step_*` equations fix each answer type, because each typechecks only
when `Op.Answer` reduces to the stated type.

| `Op` | `Op.Answer` | `step` | Enabled when | Disabled: agent unchanged, answer | Anchor |
| --- | --- | --- | --- | --- | --- |
| `newPromise` | `Promise.Capability` | `newPromise a` | always | — | NEWCAP, RESOLVING |
| `resolve cap v` | `Unit` | `(resolve a cap v, ())` | a stored, unfired function has `resolve = cap.resolve` | `()` (`callFunctions_none`, `_fired`, `resolve_unminted`) | RESOLVING resolve steps, FULFILL, TRIGGER; Web IDL RESOLVE |
| `reject cap r` | `Unit` | `(reject a cap r, ())` | a stored, unfired function has `reject = cap.reject` | `()` (`reject_unminted`) | RESOLVING reject steps, REJECT, TRIGGER; Web IDL REJECTOP |
| `perform p onF onR derive` | `Option (Option Capability)` | `perform a p onF onR derive` | `p` allocated | `none` (`perform_missing`) | THEN; Web IDL REACT steps 6 to 8 when `derive` |
| `markHandled p` | `Unit` | `(markHandled a p, ())` | always (a missing `p` is a no-op on the table) | — | HANDLEDOP |
| `startJob` | `Option (Job × Option body)` | `startJob a` | at a checkpoint with a nonempty queue | `none` (`startJob_empty`, `startJob_blocked`, `startJob_running`) | RUNCOND, ONEJOB, ORDER |
| `finishJob d` | `Unit` | `(finishJob a d, ())` | a job running | `()` (`finishJob_idle`, `finishJob_not_job`) | REACTJOB inner steps 4 to 9, COMPLETE |
| `enterScript` | `Unit` | `(enterScript a, ())` | at a checkpoint | `()` (`enterScript_other`) | RUNCOND (a context is running) |
| `leaveScript` | `Unit` | `(leaveScript a, ())` | in a script | `()` (`leaveScript_other`) | RUNCOND (the stack is empty) |

DB-07 holds: an empty queue, an idle `finishJob` and an unknown function are
live frontiers that leave the agent unchanged, never failures.

The defining equations of the B1 battery's §5 fix each operation exactly,
including every disabled branch. Reading aid:

```lean
newPromise a = ({ a with
    table := (Promise.newPromiseCapability a.table a.nextFunction).1,
    functions := a.functions ++
      [Promise.createResolvingFunctions a.table.next a.nextFunction],
    nextFunction := a.nextFunction + 2 },
  (Promise.newPromiseCapability a.table a.nextFunction).2)
settle a p result = { a with
    table := (Table.settleAndTrigger a.table a.reactions a.queue p result).1,
    reactions := (… settleAndTrigger …).2.1,
    queue := (… settleAndTrigger …).2.2,
    settlements := (Table.settleTraced a.table a.settlements p result).2 }
-- when a.functions.find? pick = some f and f is unfired:
callFunctions a pick result =
  { settle a f.promise result with
    functions := a.functions.map (fun g =>
      if pick g then { g with alreadyResolved := true } else g) }
resolve a cap v =
  callFunctions a (fun f => f.resolve == cap.resolve) (.ok v)
reject a cap r =
  callFunctions a (fun f => f.reject == cap.reject) (.error r)
mintFor a true = ((newPromise a).1, some (newPromise a).2)
mintFor a false = (a, none)
-- when a.table.get p = some .pending:
perform a p onF onR d =
  ({ (mintFor a d).1 with
      table := Table.markHandled (mintFor a d).1.table p,
      reactions :=
        (Reactions.add a.reactions p onF onR (mintFor a d).2).1 },
    some (mintFor a d).2)
-- when a.table.get p = some (.fulfilled v); `.rejected` alike:
perform a p onF onR d =
  ({ (mintFor a d).1 with
      table := Table.markHandled (mintFor a d).1.table p,
      reactions :=
        (Reactions.mint a.reactions p .fulfill onF (mintFor a d).2).1,
      queue := Queue.enqueue a.queue ⟨a.reactions.next, .ok v⟩,
      held := a.held ++
        [(Reactions.mint a.reactions p .fulfill onF (mintFor a d).2).2] },
    some (mintFor a d).2)
-- when a.active = .checkpoint and a.queue.pending = job :: rest:
startJob a =
  ({ a with queue := ⟨rest⟩, active := .job job.reaction,
      running := some job },
    some (job, (reactionOf a job).bind Reaction.handler))
-- when a.active = .job s, a.running = some job,
-- reactionOf a job = some r and r.capability = some cap:
finishJob a d =
  { callFunctions a (fun f => f.resolve == cap.resolve)
      (reactionHandlerResult r job.argument d) with
    active := .checkpoint, running := none }
```

`reactionOf a job` is the held record of identity `job.reaction` if there is
one, otherwise the registered record in the list `job.argument`'s tag selects
(`reactionOf_held`, `reactionOf_ok`, `reactionOf_error`). With
`[[Capability]]` *undefined*, or no record, `finishJob` only returns to a
checkpoint (`finishJob_no_capability`, `finishJob_unknown`; D18,
`WS-PROM-CE-044`).

The step emits no event list. Its observation is the answer together with
the state change: the settlement trace carries DB-04 M2's settlement order,
the queue carries job order, and the `startJob` answers of a run carry start
order (`runOps`, §9).

## 6. The fourteen clauses of `WF`

`Agent.WF a : Prop` is a structure; slice B1 lands it (and `Minted`), because
B1's `resolve_table` and B3's `resolve_view` are stated under it; slice B2
lands every lemma about it. Each clause is frozen by its projection in the B1
battery's §6.

| # | Clause | Statement (reading aid) | Why |
| ---: | --- | --- | --- |
| 1 | `tableNodup` | `(a.table.entries.map Prod.fst).Nodup` | identities unique; `Table.mk` stays public, so duplicates are ill-formed, not unconstructible (`WS-PROM-CE-043`) |
| 2 | `tableBelow` | `∀ e ∈ a.table.entries, e.1 < a.table.next` | the cursor is fresh |
| 3 | `functionsBelow` | `∀ f ∈ a.functions, f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction` | the function cursor is fresh |
| 4 | `functionsAllocated` | `∀ f ∈ a.functions, (a.table.getCell f.promise).isSome = true` | every stored function names an allocated promise |
| 5 | `resolvedSettled` | `∀ f ∈ a.functions, f.alreadyResolved = true → Promise.Table.isPending a.table f.promise = false` | fired functions only on settled promises; holds only while `G-05` is out (R-W3) |
| 6 | `reactionsBelow` | `∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held, r.id < a.reactions.next` | the registration cursor is fresh |
| 7 | `queueBelow` | `∀ j ∈ a.queue.pending, j.reaction < a.reactions.next` | queued serials are reaction identities |
| 8 | `paired` | `a.reactions.fulfill.map Reaction.id = a.reactions.reject.map Reaction.id` | the landed `add_paired` shape |
| 9 | `functionsNodup` | `(a.functions.map ResolvingFunctions.resolve).Nodup` | `find?` names one record; with clause 3 the `reject` identities are unique too |
| 10 | `heldDistinct` | `(a.held.map Reaction.id ++ a.reactions.fulfill.map Reaction.id).Nodup` | held and registered identities disjoint, and each list without repeats, so `reactionOf` is unambiguous |
| 11 | `queuedKnown` | `∀ j ∈ a.queue.pending, (reactionOf a j).isSome = true` | every queued job names a record |
| 12 | `runningActive` | `(∀ j, a.running = some j → a.active = .job j.reaction) ∧ (∀ s, a.active = .job s → a.running.isSome = true)` | the running job and the activation agree |
| 13 | `capabilityStored` | `∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held, ∀ cap, r.capability = some cap → Minted a cap` | every stored capability has its functions stored (D17) |
| 14 | `settlementsCoherent` | `(a.settlements.map Prod.fst).Nodup ∧ (∀ p v, (p, .ok v) ∈ a.settlements → a.table.get p = some (.fulfilled v)) ∧ (∀ p r, (p, .error r) ∈ a.settlements → a.table.get p = some (.rejected r))` | every trace entry is the table's settled state, ids unique; closes D20 |

`Minted a cap ↔ ∃ f ∈ a.functions, f.resolve = cap.resolve ∧ f.reject =
cap.reject ∧ f.promise = cap.promise` (`Minted_iff`).

`WF.empty` and `WF.step : WF a → WF (step a op).1` hold for **every**
operation, enabled or disabled (B2), so every agent `runOps` reaches from
`Agent.empty` is well formed (`WF.runOps`). The B2 battery's §7 example
checks one reachable agent.

## 7. Handler adequacy (the design's §3.7)

All in `Whatwg/Ecma262/AgentLaws.lean` (slice B2), no `Effects` import.

### 7.1 The world order `Agent.Le a a'`

Eight clauses, frozen by their projections: `allocated` (an allocated cell
stays allocated), `settled` (a settled state never changes), `handled` (the
handled bit never clears), `tableNext`, `reactionsNext`, `functionCursor`
(the three cursors grow), `minted` (every stored function record survives
with its three identities), `trace` (`a.settlements <+: a'.settlements`).
`Le.refl`, `Le.trans`, and `Le.step : WF a → Le a (step a op).1` for every
operation.

### 7.2 `Agent.Cert`, `Agent.pre`, `Agent.post`

`Cert op := Unit` (an `abbrev`): the table is homogeneous in `value` and
`reason`, so no ghost certificate is needed. The eighteen `pre_*` and
`post_*` equations freeze the content (each is `Iff.rfl` of the definition).

| `op` | `pre a op c` | `post a' op c ans` (at the answering agent) |
| --- | --- | --- |
| `newPromise` | `True` | `Minted a' ans ∧ a'.table.get ans.promise = some .pending` |
| `resolve cap v` | `Minted a cap` | `∃ s, a'.table.get cap.promise = some s ∧ s ≠ .pending` |
| `reject cap r` | `Minted a cap` | the same |
| `perform p onF onR d` | `(a.table.get p).isSome = true` | `(a'.table.getCell p).map Cell.handled = some true ∧ (d = true → ∃ cap, ans = some (some cap) ∧ Minted a' cap ∧ a'.table.get cap.promise = some .pending) ∧ (d = false → ans = some none)` |
| `markHandled p` | `(a.table.get p).isSome = true` | `(a'.table.getCell p).map Cell.handled = some true` |
| `startJob` | `a.active = .checkpoint ∧ a.queue.pending ≠ []` | `∃ j, ans = some (j, (reactionOf a' j).bind Reaction.handler) ∧ a'.active = .job j.reaction ∧ a'.running = some j` |
| `finishJob d` | `∃ s, a.active = .job s` | `a'.active = .checkpoint ∧ a'.running = none` |
| `enterScript` | `a.active = .checkpoint` | `a'.active = .script` |
| `leaveScript` | `a.active = .script` | `a'.active = .checkpoint` |

`pre` is enabledness, so under it no step takes a disabled branch — "no
frontier" for a total step — with one admitted exception: `resolve` and
`reject` admit a capability whose functions already fired, so that a program
may call "resolve" twice; the step is then inert and the post still holds, by
`resolvedSettled` and `functionsAllocated`. The activation posts of
`startJob` and `finishJob` hold at the answering agent only; every other post
is upward closed in `Le`.

### 7.3 `Agent.Implements` and the nine rows

```lean
Implements op ↔
  ∀ (a : Agent value reason body) (c : Cert op), WF a → pre a op c →
    Le a (step a op).1 ∧ WF (step a op).1 ∧
      post (step a op).1 op c (step a op).2
```

`newPromise_implements`, `resolve_implements cap v`, `reject_implements cap
r`, `perform_implements p onF onR d`, `markHandled_implements p`,
`startJob_implements`, `finishJob_implements d`, `enterScript_implements`,
`leaveScript_implements`, and `implements : ∀ op, Implements op`. The middle
conjunct of each is the operation's `WF` preservation.

### 7.4 Not here: `run_adequate`

The program-level rule over lean4-effect4's `Protocol` waits until that module
is in the `effects` package and this repository moves its pin (R-W3). No
generic law is copied: a second owner of a generic law is what
`Whatwg/AGENTS.md` forbids.

### 7.5 What the shape is a reading of

The reading of lean4-effect4's handler-adequacy judgment below is a reading
of its source at `b9d0d19f`, not a claim about that repository, its intent or
its gate. `src/Effect4/Laws/Effects/Protocol.lean` there is generic over an
`Effects` signature and imports only `Effects.Algebra.Sum`; it declares
`WorldOrder W` (`le`, `refl`, `trans`), `Protocol W S` (`Cert`, `pre`,
`post`), the judgment `Typed o Ψ w Q p` with `Typed.mono`, `bind`, `widen`,
`Protocol.sum`, `Typed.inl` and `Typed.inr`.
`src/Effect4/Laws/Program/Typed/Adequacy.lean` declares `StoreTyped w`, and
`StoreImplements root op` as "for every world and certificate, a typed store
and a request the row's pre admits step (`syncOpStep op w.state = some (st',
ans)`), and some later world `w'` over `st'` (`w.leHost w'`) is typed again
with the answer in the row's post", with the handler rule `storeStep_typed`.

| This packet | lean4-effect4 at `b9d0d19f`, as read |
| --- | --- |
| `Agent.WF` | `StoreTyped` |
| `Agent.Le` | `World.leHost` |
| `Agent.Cert` (`Unit`) | `StoreCert op` |
| `Agent.pre`, `Agent.post` | `storePre`, `storePost` |
| `Agent.Implements op` | `StoreImplements root op` |
| the nine `*_implements` | the per-row `*_implements` |
| `step` total; `pre` is enabledness | "steps, no frontier": `syncOpStep … = some …` |
| (not here) `run_adequate` | `storeStep_typed`, iterated along a run |

Three differences, each a reading: their step is partial and ours is total,
so their `∃ st' ans` is our step's own components; their later world is any
`w'` above `w` over the new store, ours is the stepped agent with `Le a (step
a op).1` as a conjunct; their typing is "every value fits its declared type"
over a heterogeneous store, ours is identity and reference coherence over a
homogeneous one. `Agent.Cert`, `Agent.pre` and `Agent.post` have the types of
`Protocol`'s `Cert`, `pre` and `post` at the face's signature, and `Agent.Le`,
`Le.refl` and `Le.trans` those of `WorldOrder`'s `le`, `refl` and `trans`, so
a consumer fills both by constructor application; the design measured that
glue against a field-for-field copy (its appendix B.8), and this packet does
not freeze it.

## 8. D46 and the views onto the frozen store-level operations

D46: `WebIdl.Promise.resolve` is `Table.settle` and its signature carries no
reaction store or queue, so Web IDL "react" followed by "resolve" enqueues no
reaction job (`WS-PROM-CE-040`). Repaired additively (R-W3): `Agent.resolve`
and `Agent.reject` call the capability's stored resolving functions and then
settle-and-trigger; the frozen `WebIdl.Promise.resolve` and `reject` keep their
statements and are the table views.

```lean
-- B1, DB-04 M2
theorem Agent.react_resolve_enqueues (a) (cap) (f) (h : body) (v : value) :
    a.table.get cap.promise = some .pending → cap.promise ≠ a.table.next →
    a.functions.find? (fun g => g.resolve == cap.resolve) = some f →
    f.alreadyResolved = false → f.promise = cap.promise →
    (resolve (perform a cap.promise (some h) none true).1 cap v).queue.pending =
      a.queue.pending ++
        ((Reactions.waitingOn a.reactions cap.promise .fulfill).map
          (fun r => ⟨r.id, .ok v⟩) ++ [⟨a.reactions.next, .ok v⟩])
-- `_wf`: `WF a →` in place of `cap.promise ≠ a.table.next`.
-- `_exactly`: with `waitingOn a.reactions cap.promise .fulfill = []`, the
--   queue is exactly `a.queue.pending ++ [⟨a.reactions.next, .ok v⟩]`.
-- B3, DB-04 M2: `WebIdl.Agent.react_resolve`, the `_wf` statement with
--   `WebIdl.Agent.resolve` and `WebIdl.Agent.react a p (some h) none`.
```

The views, each right side the landed operation, not a copy:

| Law | Slice | Statement | Mask |
| --- | --- | --- | --- |
| `resolve_table` | B1 | `WF a → find? (resolve ==) = some f → f.promise = cap.promise → (resolve a cap v).table = Table.settle a.table cap.promise (.ok v)` | DB-04 M1 |
| `reject_table` | B1 | the same through `reject ==` and `.error r` | DB-04 M1 |
| `WebIdl.Agent.resolve_view` | B3 | `… → (WebIdl.Agent.resolve a p v).table = WebIdl.Promise.resolve a.table p.promise v` | DB-04 M1 |
| `WebIdl.Agent.reject_view` | B3 | `… → (WebIdl.Agent.reject a p r).table = WebIdl.Promise.reject a.table p.promise r` | DB-04 M1 |
| `settleAndTrigger_table` | B1 | `(Table.settleAndTrigger t rs q id result).1 = Table.settle t id result` | DB-04 M1 |
| `settle_ok_fulfillPromise` | B1 | the agent's three stores after `settle a p (.ok v)` are `fulfillPromise a.table a.reactions a.queue p v` | DB-04 M2 |
| `settle_error_rejectPromise` | B1 | the same at `rejectPromise` | DB-04 M2 |
| `settle_settlements` | B1 | `(settle a p r).settlements = (Table.settleTraced a.table a.settlements p r).2` | DB-04 M2 |
| `newPromise_capability` | B1 | `(newPromise a).2 = (newPromiseCapability a.table a.nextFunction).2` | DB-04 M1 |
| `WebIdl.Agent.newPromise_view` | B3 | the table and capability are `WebIdl.Promise.newPromiseWithCapability`'s | DB-04 M1 |
| `markHandled_table` | B1 | `(markHandled a p).table = Table.markHandled a.table p` | DB-04 M1 |
| `WebIdl.Agent.markAsHandled_view` | B3 | `(markAsHandled a p).table = WebIdl.Promise.markAsHandled a.table p.promise` | DB-04 M1 |
| `markHandled_get` | B1 | `Table.get (Table.markHandled t p) q = Table.get t q` | DB-04 M1 |
| `startJob_agree` | B1 | at a checkpoint with `job :: rest` queued, `Jobs.startJob a.active a.queue job.reaction = some (job, (startJob a).1.active, (startJob a).1.queue)` | DB-04 M2 |

Two production docstrings become stale and are builder-owned (no breaker
amendment): `Whatwg.WebIdl.Promise.resolve` and `reject` should say
"store-level view; the agent operation is `Whatwg.WebIdl.Agent.resolve`"
(B3), and `Promise.Reaction`'s and `Promise.Capability`'s "must not gain
`DecidableEq`" sentences (B1).

## 9. The lifted laws (the design's §3.5)

| Landed law | Agent-level statement | Slice | Mask |
| --- | --- | --- | --- |
| `Jobs.run_to_completion`, `startJob_blocked` | `startJob_running` (and `startJob_blocked`) | B1 | DB-04 M1 |
| `Jobs.startJob_run_agree`, `Queue.dequeue_fifo` | `startJob_agree`, `startJob_checkpoint` | B1 | DB-04 M2 |
| `Jobs.run_fifo`, `hostEnqueuePromiseJob_order` | `runOps_fifo`: over any run, started jobs then still-queued jobs are the initially queued jobs then the jobs enqueued during the run; `runOps_fifoRequirement`: the landed DB-05 specification `Jobs.FifoRequirement` | B2 | DB-04 M2 |
| `completeJob_job` | `finishJob` returns to a checkpoint (`finishJob_settles_capability`, `post_finishJob`) | B1, B2 | DB-04 M1 |
| `fulfillPromise_eq`, `rejectPromise_eq` | `settle_ok_fulfillPromise`, `settle_error_rejectPromise` | B1 | DB-04 M2 |
| `performPromiseThen_handled` (F1) | `perform_handled` | B2 | DB-04 M1 |
| `mint_no_waiting` (F2) | `perform_settled_lists`: a settled branch leaves both lists and grows `held` by one record with the next identity and the derived capability | B2 | DB-04 M1 |
| `settleAndTrigger_cleared` (F3) | `settle_cleared` | B2 | DB-04 M1 |
| `settleTraced_pending` (F6) | `settle_trace` | B2 | DB-04 M2 |
| `runReactionJob_resolve`, `_reject` (F4) with D17 | `finishJob_settles_capability`, `finishJob_capability` | B1 | DB-04 M1 |
| `callResolve_disables_reject` | `resolve_then_reject`, `reject_then_resolve` (`WF a → Minted a cap →` the second call is inert) | B2 | DB-04 M1 |
| `triggerReactions_order` | `react_resolve_enqueues` (D46) | B1 | DB-04 M2 |
| D20 (no coherence of trace and table) | `WF.settlementsCoherent`, kept by `WF.step` | B1, B2 | DB-04 M1 |
| `WF` kept by every operation | `WF.empty`, `WF.step`, `WF.runOps`, and the middle conjunct of each `*_implements` | B2 | DB-04 M1 |
| — (`WS-PROM-CE-041`) | `resolve_unminted`, `reject_unminted`: a capability whose functions were never stored settles nothing | B2 | DB-04 M1 |
| — (`WS-PROM-CE-046`) | `startJob_serial` | B2 | DB-04 M1 |
| Q4 bridges | not lifted here; W8's cutover embeds `Agent` in `Config` | — | — |

`runOps a ops : Agent × List Job` folds `step` over a list of operations and
collects the jobs `startJob` answered, through `Op.started : (op : Op) →
op.Answer → List Job` (`Op.started_startJob`, `Op.started_other`,
`runOps_nil`, `runOps_cons`).

## 10. The `Effects.Signature` face

`Whatwg/Signatures/Ecma262.lean`, namespace `Whatwg.Signatures.Ecma262`, under
the new tree `Whatwg.Signatures` with root module `Whatwg/Signatures.lean`
and Lake library `WhatwgSignatures` (`roots = ["Whatwg.Signatures"]`,
`globs = ["Whatwg.Signatures.*"]`, in `defaultTargets`), imported by the
umbrella `Whatwg.lean` (R-W3). The name `Whatwg.Effects` is refused: inside
`namespace Whatwg.Effects.X`, `Effects.Handler` resolves to
`Whatwg.Effects.Handler` once that exists. The face imports
`Effects.Algebra.Sum` and nothing else from `effects`; the data-model modules
import neither `Effects` nor Infra. `Whatwg.Signatures` joins
`strictCeilingPrefixes` as the sixth prefix; the coordinator applies that
entry at the B4 landing.

| Declaration | Signature or statement (reading aid) | Mask |
| --- | --- | --- |
| `signature` | `Type → Type → Type → Effects.Signature.{0, 0}`, an `abbrev` `⟨Agent.Op v r b, Agent.Op.Answer⟩` | — |
| `handler` | `(value reason body : Type) → Effects.Handler (signature …) (StateT (Agent …) Id)` | — |
| `handlerAt` | `(σ → Agent …) → (Agent … → σ → σ) → Effects.Handler (signature …) (StateT σ Id)` | — |
| `sumHandler` | `{T : Effects.Signature.{0, 0}} → view → update → Effects.Handler T (StateT σ Id) → Effects.Handler (Effects.Signature.sum (signature …) T) (StateT σ Id)` | — |
| `run` | `Effects.Program (signature …) α → Agent … → α × Agent …`, the step-fold | — |
| `run_pure`, `run_vis` | `run`'s two equations | DB-04 M2 |
| `handler_handle` | `((handler v r b).handle op).run a = ((step a op).2, (step a op).1)` | DB-04 M2 |
| `handlerAt_id` | `handlerAt (fun a => a) (fun a _ => a) = handler v r b` | DB-04 M2 |
| `interpret_eq_run` | `(Effects.interpret (handler v r b) p).run a = run p a` | DB-04 M2 |
| `interpret_handlerAt` | under `∀ a s, view (update a s) = a`, the lens handler's answer and viewed final agent are `run p (view s)`'s | DB-04 M2 |
| `interpret_perform_step` | one performed operation is one step (via `Effects.interpret_perform`) | DB-04 M2 |
| `interpret_sumHandler_inl` | `Effects.interpret (sumHandler view update other) (Program.inl p) = Effects.interpret (handlerAt view update) p` | DB-04 M2 |
| `resolvedWith`, `run_resolvedWith` | Web IDL RESOLVEDW as a two-operation program; its run is `((newPromise a).2, resolve (newPromise a).1 (newPromise a).2 v)` | DB-04 M2 |

The B4 battery's §4 is the shape a consumer writes: a toy signature `Tick`
summed with the agent's into `StateT (Agent Unit Nat Nat × Nat) Id` through
`sumHandler Prod.fst (fun a s => (a, s.2)) tickHandler`, with a mixed program
run end to end by `rfl`.

Mask relation, recorded and not frozen: an `Effects` trace of this handler
under `Effects.Trace.Mask.m1` determines the operation word; with
`interpret_eq_run` the word determines the agent, hence DB-04 M2. This is the
design's sentence, `[H]` there, and no theorem here states it.

## 11. Declaration record

Every public declaration of the packet, by module. Route G is an edge of
`PROMISE-PG-AGENT` (`docs/PROMISE-AGENT-DAG.md`), named; route L is a local
receipt linked to that graph. Census row ids are those of the two generated
censuses; "—" means the declaration is a model device with no row. The exact
statement of every declaration is its battery ascription. "Validation" is
§14's classification: P = proved in the design's prototype and re-proved
here; S = proved in this seat's scratch prototype.

### 11.1 Slice B1: `Whatwg/Ecma262/Agent.lean`

Battery `WhatwgTest/Ecma262/AgentContract.lean`.

| Declaration | Role | Anchor (census row) | Route | Mask | Val. |
| --- | --- | --- | --- | --- | --- |
| `instDecidableEqExcept` (scoped) and the four `deriving instance` commands (five instances) | helper (R-W3 instance set) | — | L, decision 2 | — | S |
| `Job` (abbrev) | view | `op.newpromisereactionjob` | L | — | S |
| `Agent`, `Agent.mk`, its nine projections, derived `DecidableEq`, `Repr` | canonical carrier | `clause.jobs`, `clause.properties-of-promise-instances` | G identity, representation | — | S |
| `empty` | helper | — | L | — | S |
| `newPromise` | canonical operation | `op.newpromisecapability`, `op.createresolvingfunctions` | G semantics | — | S |
| `settle` | canonical operation | `op.fulfillpromise`, `op.rejectpromise`, `op.triggerpromisereactions` | G semantics | — | S |
| `callFunctions`, `resolve`, `reject` | canonical operations | `op.createresolvingfunctions`; Web IDL `op.resolve`, `op.reject` | G semantics | — | S |
| `mintFor`, `perform` | canonical operations | `op.performpromisethen`; Web IDL `op.dfn-perform-steps-once-promise-is-settled` step 6 | G semantics | — | S |
| `markHandled` | canonical operation | Web IDL `op.mark-a-promise-as-handled` | G semantics | — | S |
| `reactionOf` | view | `record.promisereaction-records` | G semantics | — | S |
| `startJob` | canonical operation | `requirement.jobs.1`, `requirement.jobs.2`, `requirement.hostenqueuepromisejob.3` | G semantics | — | S |
| `finishJob` | canonical operation | `op.newpromisereactionjob`, `requirement.jobs.3` | G semantics | — | S |
| `enterScript`, `leaveScript` | canonical operations | `requirement.jobs.1` | G semantics | — | S |
| `Op`, its nine constructors, derived instances, `Op.Answer` | canonical alphabet | — | G identity | — | S |
| `step` | canonical transition | — | G semantics | — | S |
| `Minted`, `Minted_iff` | invariant helper | `record.promisecapability-records` | G construction | M1 | S |
| `WF` and its fourteen projections | invariant | — | G construction | — | S |
| `WF.get_lt` | invariant lemma | — | G construction | M1 | P |
| `step_newPromise` … `step_leaveScript` (9) | step equations, answer types | the rows of §5 | G semantics | M1 | S |
| `empty_eq`, `newPromise_eq`, `callFunctions_none`, `callFunctions_fired`, `resolve_eq`, `reject_eq`, `mintFor_true`, `mintFor_false`, `perform_missing`, `perform_pending`, `markHandled_eq`, `reactionOf_held`, `reactionOf_ok`, `reactionOf_error`, `startJob_empty`, `startJob_blocked`, `finishJob_idle`, `finishJob_not_job`, `finishJob_unknown`, `finishJob_no_capability`, `enterScript_checkpoint`, `enterScript_other`, `leaveScript_script`, `leaveScript_other` (24) | defining equations | the rows of §5 | G semantics | M1 | S |
| `settle_eq`, `callFunctions_fresh`, `perform_fulfilled`, `perform_rejected`, `startJob_checkpoint`, `finishJob_capability` (6) | defining equations that move the queue or the trace | the rows of §5 | G semantics | M2 | S |
| `settleAndTrigger_table`, `newPromise_capability`, `markHandled_table`, `markHandled_get` | views | as §8 | G bridges | M1 | P |
| `settle_ok_fulfillPromise`, `startJob_agree` | views | as §8 | G bridges | M2 | P |
| `settle_error_rejectPromise`, `settle_settlements` | views | as §8 | G bridges | M2 | S |
| `resolve_table` | view (D46) | Web IDL `op.resolve` via `op.createresolvingfunctions` | G bridges | M1 | P |
| `reject_table` | view (D46) | Web IDL `op.reject` | G bridges | M1 | S |
| `waitingOn_add_fulfill`, `react_resolve_enqueues`, `react_resolve_enqueues_wf`, `react_resolve_enqueues_exactly` | laws (D46) | `op.triggerpromisereactions`, `op.performpromisethen` | G laws, counterexamples | M2 | P |
| `finishJob_settles_capability` | law (D17) | `op.newpromisereactionjob` inner steps 6 to 9 | G laws | M1 | P |
| `startJob_running` | law | `requirement.jobs.3` | G laws | M1 | P |

### 11.2 Slice B2: `Whatwg/Ecma262/AgentLaws.lean`

Battery `WhatwgTest/Ecma262/AgentLaws.lean`.

| Declaration | Role | Anchor | Route | Mask | Val. |
| --- | --- | --- | --- | --- | --- |
| `Le` and its eight projections | adequacy: world order | — | G laws | — | S |
| `Le.refl`, `Le.trans` | adequacy laws | — | G laws | M2 | P |
| `Le.step` | adequacy law | — | G laws | M2 | S |
| `Cert` (abbrev), `pre`, `post`, `Implements` | adequacy definitions | the rows of §5 | G laws | — | S |
| `pre_*` (9), `post_*` (9) | defining equations | the rows of §5 | G laws | M1 | S |
| `Implements_iff` | defining equation | — | G laws | M2 | S |
| `newPromise_implements`, `markHandled_implements` | adequacy laws | NEWCAP; HANDLEDOP | G laws | M2 | S (P for the design's seven clauses and two posts) |
| `resolve_implements`, `reject_implements`, `perform_implements`, `startJob_implements`, `finishJob_implements`, `enterScript_implements`, `leaveScript_implements`, `implements` | adequacy laws | the rows of §5 | G laws | M2 | S |
| `WF.empty`, `WF.step`, `WF.runOps` | invariant laws | — | G construction, laws | M1 | S |
| `Op.started`, `runOps` | run devices | — | G laws | — | S |
| `Op.started_startJob`, `Op.started_other`, `runOps_nil` | defining equations | — | G laws | M1 | S |
| `runOps_cons` | defining equation | — | G laws | M2 | S |
| `runOps_fifo`, `runOps_fifoRequirement` | lifted laws | `requirement.hostenqueuepromisejob.3` | G laws | M2 | S |
| `perform_handled`, `perform_settled_lists`, `settle_cleared` | lifted laws (F1, F2, F3) | `op.performpromisethen`, `op.fulfillpromise`, `op.rejectpromise` | G laws | M1 | S |
| `settle_trace` | lifted law (F6) | `op.fulfillpromise`, `op.rejectpromise` | G laws | M2 | S |
| `resolve_then_reject`, `reject_then_resolve` | lifted laws | `op.createresolvingfunctions` | G laws, counterexamples | M1 | S |
| `resolve_unminted`, `reject_unminted`, `startJob_serial` | laws | `op.createresolvingfunctions`; `requirement.jobs.1` | G counterexamples | M1 | S |

### 11.3 Slice B3: `Whatwg/WebIdl/Agent.lean`

Battery `WhatwgTest/WebIdl/AgentContract.lean`.

| Declaration | Role | Anchor (Web IDL census row) | Route | Mask | Val. |
| --- | --- | --- | --- | --- | --- |
| `newPromise` | adapter | `op.a-new-promise` | G semantics | — | P |
| `resolve`, `reject` | adapters | `op.resolve`, `op.reject` | G semantics | — | P |
| `react` | adapter | `op.dfn-perform-steps-once-promise-is-settled` | G semantics | — | P |
| `uponFulfillment`, `uponRejection` | adapters | `op.upon-fulfillment`, `op.upon-rejection` | G semantics | — | S |
| `markAsHandled` | adapter | `op.mark-a-promise-as-handled` | G semantics | — | S |
| `resolvedWith` | adapter | `op.a-promise-resolved-with` | G semantics | — | P |
| `rejectedWith` | adapter | `op.a-promise-rejected-with` | G semantics | — | S |
| the nine `*_eq` | defining equations | as above | G semantics | M1 | S |
| `newPromise_view`, `markAsHandled_view`, `reject_view` | bridges | as above | G bridges | M1 | S |
| `resolve_view` | bridge (D46) | `op.resolve` | G bridges | M1 | P |
| `react_resolve` | law (D46) | `op.resolve`, `op.dfn-perform-steps-once-promise-is-settled` | G laws | M2 | P |

### 11.4 Slice B4: `Whatwg/Signatures/Ecma262.lean`, `Whatwg/Signatures.lean`

Battery `WhatwgTest/Signatures/Ecma262Contract.lean`.

| Declaration | Role | Anchor | Route | Mask | Val. |
| --- | --- | --- | --- | --- | --- |
| `signature`, `handler`, `handlerAt`, `sumHandler`, `run` | face (adapter) | — | G targets | — | P |
| `run_pure`, `run_vis` | face laws | — | G targets | M2 | S |
| `handler_handle`, `handlerAt_id`, `interpret_eq_run`, `interpret_handlerAt`, `interpret_perform_step`, `interpret_sumHandler_inl` | face laws | — | G targets | M2 | P |
| `resolvedWith`, `run_resolvedWith` | face program and law | Web IDL `op.a-promise-resolved-with` | G targets | M2 | P |

Private helpers may be added without changing these signatures. A new public
helper needs a record here and a theorem receipt (`docs/PROMISE-AGENT-DAG.md`).

## 12. Masks

Every theorem's mask is in §11's tables and beside its ascription in its
battery. The rule (DB-04, as the Q3b addendum's §4.1 applies it): a statement
is DB-04 M2 when it observes the order of the settlement trace or of the job
queue, and DB-04 M1 when it observes a cell value, a branch, a table shape, an
answer or a terminal agent. Three consequences:

- an equation whose right side moves the queue or the trace is DB-04 M2, and
  an equation that leaves both unchanged is DB-04 M1;
- every law that concludes `Le` is DB-04 M2, through `Le.trace`;
- every law of the face is DB-04 M2, because its observable is the whole
  agent.

Counts: of the 130 theorem obligations, 88 are DB-04 M1 and 42 are DB-04 M2:
14 of B1's 57, 18 of B2's 50, 1 of B3's 14 and all 9 of B4's are DB-04 M2.

## 13. Builder slices

R-W3 order: B1 first; B2, B3 and B4 then in parallel worktrees. R-W9: each
slice branches from this breaker's head (B2, B3 and B4 from B1's head) and
merges when its battery is green, its `known-red.txt` entry is gone and the
root gate passes on the slice branch. The builder that turns a battery green
adds its root import to `WhatwgTest.lean`. While a battery is red the root
gate cannot run on that branch, so builders check the strict ceiling with
`Lean.collectAxioms` over their own modules in a scratch script.

| Slice | Fence | Depends on | Battery |
| --- | --- | --- | --- |
| B1 record, operations, step, `Minted`, `WF`, views, D46 | new `Whatwg/Ecma262/Agent.lean`; the import and docstring of `Whatwg/Ecma262.lean`; the `Promise.Reaction` and `Promise.Capability` docstrings in `Whatwg/Ecma262/Promise.lean`; its `known-red.txt` line; its root import | this packet | `WhatwgTest/Ecma262/AgentContract.lean` |
| B2 invariant lemmas, adequacy, lifted laws | new `Whatwg/Ecma262/AgentLaws.lean`; one import line in `Whatwg/Ecma262.lean`; its `known-red.txt` line; its root import | B1 | `WhatwgTest/Ecma262/AgentLaws.lean` |
| B3 Web IDL verbs | new `Whatwg/WebIdl/Agent.lean`; the import and docstring of `Whatwg/WebIdl.lean`; the `Promise.resolve` and `Promise.reject` docstrings in `Whatwg/WebIdl/Promise.lean`; its `known-red.txt` line; its root import | B1 | `WhatwgTest/WebIdl/AgentContract.lean` |
| B4 face | new `Whatwg/Signatures.lean` and `Whatwg/Signatures/Ecma262.lean`; one `[[lean_lib]]` block and the `defaultTargets` entry in `lakefile.toml`; one import and its line in the docstring of `Whatwg.lean`; its `known-red.txt` line; its root import. The `strictCeilingPrefixes` entry is the coordinator's | B1 | `WhatwgTest/Signatures/Ecma262Contract.lean` |

What each builder must know:

- **All slices.** Declare each theorem with its ascribed statement copied
  verbatim as its type, binders in the ascribed order: R-W5's conversion turns
  every `#check (@n : T)` into `#whatwg_freeze (@n : T)`, which compares the
  declared type with `T` by `Expr.eqv`, unfolding nothing but `let`/`have` and
  auxiliary matchers. The B1 battery's `#guard_msgs` docstring is Lean
  4.33.1's exact diagnostic text; a toolchain change that rewords it needs a
  breaker amendment, not a builder edit.
- **B1.** `WF` and `Minted` are B1's, with the fourteen clauses exactly as
  ascribed; their lemmas are B2's. The instance set goes in
  `Whatwg/Ecma262/Agent.lean` as `scoped instance` and `deriving instance`
  (the gate accepts both, and `nomatch`). `perform_pending`'s right side has
  `held` unchanged where `performPromiseThen` appends `[]`: the proof needs
  `List.append_nil`. Every disabled branch is the agent unchanged. The
  thirteen `example`s are closed by `rfl` or `decide` in the kernel, so keep
  the operations non-recursive or structurally recursive.
- **B2.** About 2,000 lines measured in this seat's prototype, the bulk in
  `WF.settle`, `WF.performPending`, `WF.performSettled` and
  `runOps_fifo`. Inside a theorem named `WF.x` or `Le.x`, the unqualified
  `step`, `newPromise`, `settle` and `markHandled` resolve to `WF.step`,
  `Le.newPromise` and so on: write `Whatwg.Ecma262.Agent.step`. A lemma about
  the settle-and-trigger kind, stated with an inline `match result with`,
  elaborates to a different matcher than the landed one: state helper
  lemmas for every kind (`∀ k : ReactionType`) and rewrite with them.
  `Option.noConfusion h` does not close `none = some j → …` at this
  toolchain; `cases h` does. Choice traps measured by lane V and the design
  (`Whatwg/AGENTS.md`, "Ceiling") apply; the prototype used none of `simp`,
  `omega`, `by_cases` or `grind`.
- **B3.** Thin wrappers; `resolve_view` and `react_resolve` are one-line
  appeals to B1's `resolve_table` and `react_resolve_enqueues_wf`.
- **B4.** `signature` must be an `abbrev`. `run` is structural over
  `Effects.Program`. `Whatwg.Signatures` is a new tree, so the umbrella import
  is what makes the audit root reach it (trust-gate addendum V2c rule 5).

## 14. Validation (R-W9)

Every statement of the four batteries was elaborated against production
modules reinstated from the design's appendix A and extended to this surface,
uncommitted, in this seat's worktree; every law was proved there, and the
prototype was then removed. Nothing of it is on any branch.

| Class | Theorem obligations |
| --- | ---: |
| proved in the design's prototype (appendix A and B), re-proved here | 25 |
| proved in this seat's scratch prototype | 105 |
| probed on instances only | 0 |
| unprobed | 0 |

The 25 are `WF.get_lt`, `settleAndTrigger_table`, `settle_ok_fulfillPromise`,
`newPromise_capability`, `markHandled_table`, `markHandled_get`,
`startJob_agree`, `startJob_running`, `resolve_table`, `waitingOn_add_fulfill`,
`react_resolve_enqueues` with `_wf` and `_exactly`,
`finishJob_settles_capability`, `Le.refl`, `Le.trans`,
`WebIdl.Agent.resolve_view`, `WebIdl.Agent.react_resolve`, and the seven face
laws `handler_handle`, `handlerAt_id`, `interpret_eq_run`,
`interpret_handlerAt`, `interpret_perform_step`, `interpret_sumHandler_inl`
and `run_resolvedWith`. The design proved `WF.empty`, `WF.newPromise`,
`WF.markHandled` and `WF.settle` for its seven clauses and
`newPromise_implements` and `markHandled_implements` with two posts spelled
out; those are counted under the 105, because the frozen statements are the
fourteen-clause ones. The 26 `example`s are probes on instances in addition
to the laws.

Measured with the prototype in place, the batteries imported by the root and
`Whatwg.Signatures` added to `strictCeilingPrefixes` (all uncommitted):
`lake build` completed 405 jobs, and the gate line read "checked 231 source
files and 17284 declarations; Classical.choice is reached by 84 of 13297
declarations in Whatwg, 122 of 2390 in WhatwgTest and 176 of 1597 in
WhatwgGates; strict ceiling propext and Quot.sound over 6 module prefix(es)
with 0 exact exception(s); 0 source-token exemption(s)". The base at `b0d35e2`
reads 222 source files, 16723 declarations and 84 of 12766 in `Whatwg`: the
prototype adds 531 declarations to `Whatwg` and none of them reaches
`Classical.choice`. `lake env leanchecker` over the four prototype modules and
the four batteries exited 0. Prototype sizes: `Whatwg/Ecma262/Agent.lean`
833 lines (58 theorems), `Whatwg/Ecma262/AgentLaws.lean` 2118 lines (121
theorems), `Whatwg/WebIdl/Agent.lean` 123 lines and
`Whatwg/Signatures/Ecma262.lean` 100 lines.

## 15. Counterexample rows

Eight rows, `WS-PROM-CE-040` to `047`, registered before any implementation
in `test/counterexamples/REGISTER.md` and described in
`test/counterexamples/promise/ATTACKS.md`, section "Q5 agent packet". Every
one is `SEEDED`: its rejecting statement is frozen and red until its slice
lands. The witnesses are the batteries' statements and `example`s, the
promise-lane convention; no separate witness module is written.

| Id | Attack | Rejecting statements | Finite witness |
| --- | --- | --- | --- |
| `WS-PROM-CE-040` | Web IDL "react" then "resolve" enqueues nothing, because the store-level `resolve` is `Table.settle` (D46) | `react_resolve_enqueues`, `_wf`, `_exactly` (B1); `WebIdl.Agent.react_resolve` (B3) | B3 battery §5: store level 0 jobs, agent level `[⟨0, .ok ()⟩]`; B1 battery §10: the hypotheses hold at a `WF` agent |
| `WS-PROM-CE-041` | a forged capability (functions never stored) settles its promise, as a fallback to `Table.settle` would | `resolve_unminted`, `reject_unminted` (B2); `callFunctions_none` (B1) | B1 battery §10 |
| `WS-PROM-CE-042` | a per-function one-shot marker: `reject` after `resolve` still settles | `resolve_then_reject`, `reject_then_resolve` (B2) | B1 battery §10; B3 battery §5 |
| `WS-PROM-CE-043` | duplicate identifiers through the public `Table.mk` are accepted as an agent | `WF.tableNodup` (B1) | B1 battery §10: `¬ WF` on a two-entry `Table.mk` with identity `0` twice |
| `WS-PROM-CE-044` | `finishJob` with `[[Capability]]` *undefined* settles something (D18) | `finishJob_no_capability` (B1) | B1 battery §10, with the derived-capability contrast |
| `WS-PROM-CE-045` | `startJob` ignores the activation (run to completion) | `startJob_running`, `startJob_blocked` (B1) | B1 battery §10 |
| `WS-PROM-CE-046` | a separate job-serial supply (the `WS-PROM-CE-039` shape) | `startJob_agree`, `startJob_checkpoint` (B1); `startJob_serial` (B2) | B1 battery §10: serial `0` and the record's phase `.queued 0` |
| `WS-PROM-CE-047` | a lens without `view (update a s) = a`, or a handler that steps twice | `interpret_handlerAt`'s hypothesis; `interpret_eq_run` (B4) | B4 battery §5: both refuted by `decide` |

## 16. Claim scope: what the packet does not model

- **Thenable adoption (`G-05`)**, `op.newpromiseresolvethenablejob`
  (2705599..2707541) and the adoption branch of `op.createresolvingfunctions`:
  `resolve` takes a plain `value` and never looks up `then`. `resolvedSettled`
  holds only because adoption is out; when it enters, adoption leaves a
  resolved promise pending and the clause must be weakened (R-W3, the
  design's decision 9). `G-04` (`IsPromise`, the value universe) stays out with
  it.
- **The rejection tracker (`G-02` remainder)**,
  `hook.host-promise-rejection-tracker` (2701220..2702791): the handled bit is
  set by `perform` and `markHandled` and read by nothing. `op.rejectpromise`
  step 6 and `op.performpromisethen`'s rejected-branch call are not modelled,
  so both rows stay `partial` at best.
- **Job callbacks (`G-07` remainder)**: no realm parameter, no Job Abstract
  Closure carrier, no `HostMakeJobCallback` or `HostCallJobCallback`; a
  handler is a first-order descriptor and its completion is the host's
  decision `d` of `finishJob` (DB-02). `op.newpromisereactionjob` stays
  `partial`.
- **The binding layer**: every Web IDL verb here omits the step that converts
  an IDL value to an ECMAScript value; that layer stays `hostOnly`, so the Web
  IDL `op.resolve`, `op.reject` and react rows stay `partial` at best.
- `G-10` (the Completion carrier beyond `Except`) and the `G-11` remainder
  (`then`, `catch`, `finally`, the combinators, the `Promise` constructor).
  `uponFulfillment` and `uponRejection` keep the landed `G-11` restriction:
  the other handler is `none`.
- **Not frozen here**: the program-level `run_adequate` (§7.4); the
  mask-relation sentence of §10; the Q4 bridges and the one-table cutover
  (W8); the coverage join (the coverage seat); a Streams face (P12).
- `held` never shrinks and `finishJob` does not advance a reaction's phase
  past `.queued`: both are departures the reviewer names (the design's
  §6.4), and no statement here claims otherwise.

## 17. Deviations from the design and the rulings

| Deviation | Reason |
| --- | --- |
| Four batteries, no `WhatwgTest/Ecma262/AgentAxiomReport.lean` | R-W9 forbids new axiom-report modules; it supersedes the design's §6.2 and R-W3's "five batteries" |
| `WF` and `Minted` are landed by B1, in `Whatwg/Ecma262/Agent.lean`, and their projections are ascribed in the B1 battery; B2 lands every `WF` lemma | B1's `resolve_table` and B3's `resolve_view` are stated under `WF` (R-W3: "re-described as the table view by `resolve_table` under `WF`"), and B3 must not wait for B2 (R-W3: "B2, B3 and B4 follow in parallel"). The design's §6.3 put "invariant" in B2's module, which would make B3 wait |
| `functionsAllocated` is `(a.table.getCell f.promise).isSome = true`, not the prototype's `f.promise < a.table.next` | "allocation of every stored reference" (the design's §3.1); the post of `resolve` and `reject` ("the promise is settled") is false for a function naming an unallocated identity below the cursor, which the weaker clause admits |
| `heldDistinct` is `(held ids ++ fulfill ids).Nodup` | it implies the design's disjointness and adds no repeat within either list, which `reactionOf`'s `find?` needs to name one record; every operation keeps it |
| `runningActive` is two implications, not `running = some j ↔ active = .job j.reaction` | the biconditional, quantified over `j`, is false for every agent with a running job (any other `j'` with the same reaction identity satisfies the right side) |
| `settlementsCoherent` is three conjuncts over `.ok` and `.error` entries | states "the table's settled state" without an inline `match`, which would elaborate to a matcher of the battery's own |
| `pre` of `resolve` and `reject` is `Minted a cap`, which admits fired functions | the design's §3.7 says "exactly enabledness"; a fired function is a disabled branch, yet a second "resolve" is legal and the post still holds |
| Added names (additive): the 30 defining equations and the 9 step equations of B1, `Minted_iff`, `settle_error_rejectPromise`, `settle_settlements`, `reject_table`; in B2 `Le.step`, `WF.step`, `WF.runOps`, the 18 `pre_*`/`post_*`, `Implements_iff`, `Op.started`, `runOps` and their four equations, `runOps_fifo`, `runOps_fifoRequirement`, `perform_handled`, `perform_settled_lists`, `settle_cleared`, `settle_trace`, `resolve_then_reject`, `reject_then_resolve`, `resolve_unminted`, `reject_unminted`, `startJob_serial`; in B3 the nine `*_eq`, `newPromise_view`, `markAsHandled_view`, `reject_view`; in B4 `run_pure`, `run_vis` | the design's §3.5 lifted laws needed statements, "a disabled operation leaves the agent unchanged" (R-W3) needed one per branch, and a definition's content is frozen only by an equation |
| Not frozen as public names: the design's `WF.newPromise`, `WF.markHandled`, `WF.settle` | `WF.step` states all nine; a builder may keep them as helpers |
| `Cert` is frozen although R-W3 names only `Le`, `pre`, `post`, `Implements` | R-W3 adopts the design "as designed", and the design's §3.7 has `Cert`; `pre` and `post` take it |

No frozen ascription, battery or contract of this repository is altered.

## 18. Acceptance conditions

1. Every ascription and `example` of the four batteries elaborates with no
   edit to a statement; a builder may repair an `example`'s proof only.
2. The gate passes with the batteries imported by the root, under the strict
   ceiling over six prefixes with no exception: no declaration under
   `Whatwg.Ecma262`, `Whatwg.WebIdl` or `Whatwg.Signatures` reaches
   `Classical.choice`.
3. No landed definition, statement, ascription or battery changes; the only
   edits to landed modules are the docstrings and import lines of §13.
4. The data-model modules import no `Effects.*` and no `Whatwg.Infra.*`
   module; the face imports `Effects.Algebra.Sum` only.
5. `DecidableEq (Except ε α)` is synthesized only inside the scope: the B1
   battery's `#guard_msgs`-pinned `#check_failure` stays green.
6. Each `known-red.txt` entry is removed by the slice that turns its battery
   green, and only then (R-W9).
7. Both censuses are unchanged; no coverage row moves.
8. `lake exe whatwg_vendorseal`, `lake exe whatwg_citations` and
   `lake exe whatwg_trustselftest` pass at each landing.

## 19. Freeze receipt

Observed in this worktree at this branch's head, Lean 4.33.1, Windows 11,
after the prototype was removed and every tracked file restored. Before the
removal the batteries were green against it (§14).

`lake build` fails, and the failing targets are the four modules declared in
`test/fixtures/trust-gate/known-red.txt` and the root `WhatwgTest`, whose
module-closure gate reports exactly those four sources as "not reachable from
the WhatwgTest audit root". That root failure is R-W9's arrangement, not a
fifth red module: breakers do not edit `WhatwgTest.lean`, the builder that
turns a battery green adds its root import, and `lake exe
whatwg_trustselftest` excises the declared modules from its probe copy
before it builds.

Each battery's complete diagnostic list, collected with
`lake env lean -DmaxErrors=5000 <file>` after `lake build Whatwg WhatwgEcma262
WhatwgWebIdl`:

| Module | Exit | Diagnostics | Classes |
| --- | ---: | ---: | --- |
| `WhatwgTest.Ecma262.AgentContract` | 1 | 430 | 386 `lean.unknownIdentifier`; 6 `lean.synthInstanceFailed`, one per instance slice B1 adds (the five global ones, and the scoped `Except` one under `open Whatwg.Ecma262.Agent in`); 1 "unknown namespace `Whatwg.Ecma262.Agent`" (that `open … in`); 37 error-recovery consequences of the unknown names in dependent statements and `example`s: 11 invalid field notation, 1 invalid projection, 9 "`sorryAx` is not a structure", 5 "expected structure", 10 "don't know how to synthesize implicit argument", 1 "expected type must not contain metavariables" |
| `WhatwgTest.Ecma262.AgentLaws` | 1 | 281 | 273 `lean.unknownIdentifier`; 8 invalid field notation on a binder whose type is the unknown `Agent.Agent` |
| `WhatwgTest.WebIdl.AgentContract` | 1 | 94 | 92 `lean.unknownIdentifier`; 2 "invalid match expression: this pattern contains metavariables", in the two store-level witnesses whose scrutinee mentions the unknown `start` |
| `WhatwgTest.Signatures.Ecma262Contract` | 1 | 101 | 100 `lean.unknownIdentifier`; 1 warning "declaration uses `sorry`" on the test-local theorem `lens`, whose type mentions the unknown agent: the `sorry` is Lean's error-recovery term, not source text |

**906 diagnostics in total.** There is no parse error, no import error and no
type mismatch, and the only failed instance syntheses are the six instances
B1 adds: every battery is red only because the names it ascribes do not exist
yet. The `#guard_msgs`-pinned `#check_failure` of a global `DecidableEq
(Except Nat Nat)` elaborates green already, as it must after B1.

### 19.1 The other gates

- `lake exe whatwg_vendorseal`: PASS ("manifest and vendor/ agree in both
  directions; every path is valid on Windows").
- `lake exe whatwg_citations`: PASS ("455 files scanned; no line-numbered
  citation into a protected authored document").
- `lake exe whatwg_trustselftest`: PASS, exit 0 ("every planted declaration
  was rejected for its stated reason, every control was accepted, and every
  narrow run exited 0 with its frozen summary"). It excises the four declared
  modules from its probe copy, so this is the receipt that the declared red set
  is exact in both directions.
- The prototype was reinstated once more after the last battery edit: the
  full gate line was unchanged (231 source files, 17284 declarations, six
  strict prefixes, zero exceptions), and after its second removal the four
  batteries gave the same 906 diagnostics.
## 20. Fence

Breaker files, which the builders may not edit: this contract; the four
batteries; the "Q5 agent packet" section of
`test/counterexamples/promise/ATTACKS.md`; rows `WS-PROM-CE-040` to `047` of
`test/counterexamples/REGISTER.md`; the declaration, statement and
correspondence rows of `docs/PROMISE-AGENT-DAG.md`. The four `known-red.txt`
lines are the builders' to remove, one per slice.

This breaker edited no file under `Whatwg/`, no existing battery or
contract, and not `WhatwgTest.lean`, `COORDINATION.md`, `PLAN.md`, any
`AGENTS.md` or `lakefile.toml`.

## Addendum Q5b: what `WF` and the posts leave unsaid

Status: FROZEN / RED, Q5b breaker seat of review lane W, 2026-10-01, branch
`review/w9-q5b-breaker` from `5999363` (`main`: `Ledger: PROMISE-PG-FIRST
acknowledges R-W16, which names it and changes no edge`). Opened by ruling
R-W16 for debts D62 and D65. Rulings: R-W1(b) and R-W9 (additive; a law is
frozen only once proved in scratch or probed, and this addendum says which),
R-W3, R-W13 and R-W16.

This addendum is breaker-owned under the rules of this packet's preamble. It
is appended: no line above it changes. The Lean batteries are the authority on
names and propositions; the Lean here is a reading aid. Sections are numbered
Q5b.1 to Q5b.16.

### Q5b.1 Claim boundary

Additive (R-W1(b), R-W9). No frozen ascription, battery, statement or
definition body of Q5 changes: `WF`, `Minted`, `Le`, `Cert`, `pre`, `post`,
`Implements`, every Q5 law and every Q5 battery keep their text. Beside them
the addendum freezes a stronger invariant `Agent.Coherent`, which extends
`Agent.WF`; a stronger order `Agent.Extends`, which extends `Agent.Le`; a
two-state post `Agent.postFrom` and a second adequacy judgment
`Agent.ImplementsFrom` over the Q5 `pre`; the laws of the reaction job's two
completions; the reachability corollary; and the face law
`interpret_sumHandler_inr`.

It grants no coverage state, no host observation, no equivalence with any
engine and no claim about `Whatwg.Streams`. Every census row cited here
anchors a declaration and is never a numerator. Masks follow this packet's
§1 and §12; no Lean declaration is named `m1` or `m2`.

The gaps, by the letters of the coordinator's brief (debts D62 and D65):

| Gap | What `WF` and the Q5 posts leave unsaid | Answered by |
| --- | --- | --- |
| A | an unfired resolving function's promise is pending (only the converse, `resolvedSettled`, is stated), so the posts of `resolve` and `reject` say "settled" and not "fulfilled with `v`" or "rejected with `r`" | `Coherent.unfiredPending`, kept inductive by `Coherent.functionPromisesNodup`; `postFrom` of `resolve` and `reject` |
| B | every settled cell is in the settlement trace | `Coherent.settledTraced` |
| C | a waiting reaction waits on a pending promise | `Coherent.waitingPending` |
| D | the running job names a reaction record, so `post_finishJob` cannot say the capability's promise is settled | `Coherent.jobsTyped` (its running half); `postFrom` of `finishJob` |
| E | a registered or held reaction names an allocated promise | `Coherent.reactionsAllocated`; `postFrom` of `newPromise` |
| F | a job's argument tag is its record's `[[Type]]` | `Coherent.jobsTyped`, kept inductive by `Coherent.listKinds` |
| G | an abrupt result goes through the record the `[[Resolve]]` identity finds | `callFunctions_resolve_reject`, `finishJob_abrupt` (with `finishJob_normal`) |
| H | REACTJOB's unchecked assertion: an abrupt result with `[[Capability]]` *undefined* is dropped | `finishJob_abrupt_dropped` |
| I | `startJob` answers the head of the queue | `postFrom` of `startJob` |
| J | a one-shot marker never clears, and `held` only grows | `Extends.markerKept`, `Extends.heldGrows` |
| K | the face has `interpret_sumHandler_inl` and no `inr` twin | `Whatwg.Signatures.Ecma262.interpret_sumHandler_inr` |

### Q5b.2 The stronger invariant `Agent.Coherent`

`Agent.Coherent a : Prop`, in `Whatwg/Ecma262/AgentInvariant.lean`, namespace
`Whatwg.Ecma262.Agent`, is a structure that `extends Agent.WF a` (projection
`Coherent.toWF`, so `Coherent` implies `WF`) with seven clauses, each frozen by
its projection in the B5 battery's §1. The name says what the clauses add to
`WF`'s identity and reference coherence: the stores cohere with one another the
way the specification's algorithms leave them. Clause numbers continue `WF`'s
fourteen (§6).

| # | Clause | Statement (reading aid) | Gap | Anchor |
| ---: | --- | --- | --- | --- |
| 15 | `functionPromisesNodup` | `(a.functions.map ResolvingFunctions.promise).Nodup` | keeps A inductive | NEWCAP with RESOLVING: one pair of resolving functions per promise |
| 16 | `unfiredPending` | `∀ f ∈ a.functions, f.alreadyResolved = false → Table.isPending a.table f.promise = true` | A | RESOLVING: a promise leaves `~pending~` only through FULFILL or REJECT, which only its own functions reach, after setting the shared marker |
| 17 | `settledTraced` | `(∀ p v, get p = some (.fulfilled v) → (p, .ok v) ∈ a.settlements) ∧ (∀ p r, get p = some (.rejected r) → (p, .error r) ∈ a.settlements)` | B | FULFILL, REJECT; with `WF.settlementsCoherent` the trace and the settled cells determine each other (the other half of D20) |
| 18 | `waitingPending` | `∀ r ∈ fulfill ++ reject, r.phase = .waiting → get r.promise = some .pending` | C | FULFILL and REJECT steps 2 to 5: TRIGGER takes the list, and both lists are set to *undefined* |
| 19 | `reactionsAllocated` | `∀ r ∈ fulfill ++ reject ++ held, (getCell r.promise).isSome = true` | E | `builtin.promise-executor` (2708413..2711495): a new promise's reaction lists are new and empty; THEN registers only on a promise |
| 20 | `listKinds` | `(∀ r ∈ fulfill, r.kind = .fulfill) ∧ (∀ r ∈ reject, r.kind = .reject)` | keeps F inductive | THEN steps 7 to 9; `field.promisereaction-records.Type` (2691815..2692138) |
| 21 | `jobsTyped` | `∀ j, (j ∈ a.queue.pending ∨ a.running = some j) → ∃ r, reactionOf a j = some r ∧ (∀ v, j.argument = .ok v → r.kind = .fulfill ∧ get r.promise = some (.fulfilled v)) ∧ (∀ e, j.argument = .error e → r.kind = .reject ∧ get r.promise = some (.rejected e))` | D, F | REACTJOB step 1 (the job captures the reaction and the argument); TRIGGER (the argument is the promise's result); `field.promisereaction-records.Type` |

**Why two clauses no gap names.** `Coherent` must be inductive: kept by every
operation from every agent it holds of, not only from reachable ones. Two
clauses are there for that alone, and each was found by the obstruction it
removes.

- Without `functionPromisesNodup`, an agent with two unfired records for one
  pending promise satisfies the other clauses. `resolve` through one of them
  settles the promise and marks only that record (the pick selects by the
  `[[Resolve]]` identity), and the other is left unfired on a settled promise:
  `unfiredPending` is not kept. Every reachable agent has exactly one record per
  allocated promise; the clause states the half the proof needs.
- Without `listKinds`, an agent whose fulfil list holds a record of `[[Type]]`
  `~reject~`, waiting on a pending promise, satisfies the other clauses.
  Fulfilling that promise queues `⟨r.id, .ok v⟩`, and `reactionOf` finds the
  `~reject~` record for it: `jobsTyped` is not kept.

**`jobsTyped` says more than gap F asks.** Besides "the tag is the
`[[Type]]`" it says the record's promise is settled with the job's argument,
which is what TRIGGER passes and what REACTJOB step 1 captures. With it,
`reactionOf`'s re-reading of the record by identity reads what step 1
captured, so the docstring of `reactionOf` becomes a consequence of
`Coherent`. It covers the running job as well as the queued ones, so it also
answers gap D.

**What `Coherent` is not.** It is an invariant, not a characterization of the
reachable agents: an agent with one pending cell and no stored function
satisfies it and no run reaches it. Facts true of every reachable agent and not
stated: every allocated promise has exactly one stored function record; a held
record's phase is `.queued` of its own identity. No post below needs them.

Laws (B5 battery §2), all DB-04 M1: `Coherent.empty`; `Coherent.step`, for
every operation, enabled or disabled; `Coherent.runOps`; and the reachability
corollary `Coherent.reachable : ∀ ops, Coherent (runOps Agent.empty ops).1`,
which is `Coherent.runOps` at `Coherent.empty`.

### Q5b.3 The stronger order `Agent.Extends`

`Agent.Extends a a' : Prop`, a structure that `extends Agent.Le a a'`
(projection `Extends.toLe`, so `Extends` implies `Le`) with two clauses:

| Clause | Statement | Gap |
| --- | --- | --- |
| `markerKept` | `∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ a'.functions` | J: a fired record survives as it is, so its one-shot marker never clears |
| `heldGrows` | `a.held <+: a'.held` | J: `held` only grows, at its end |

`markerKept` names the record itself rather than a marker over `[[Resolve]]`
identities: it is the stronger statement, and it needs no `WF`, because setting
the marker of a fired record returns the record. Laws (B5 battery §3), all
DB-04 M2 through `Le.trace` and `heldGrows`: `Extends.refl`, `Extends.trans`,
and `Extends.step : WF a → Extends a (step a op).1` for every operation, the
hypothesis as in `Le.step`.

### Q5b.4 The two-state post and the second judgment

`Agent.postFrom a a' op c ans : Prop` is the post of the second judgment. It
reads the agent `a` the step starts from as well as the agent `a'` it answers
at, because every fact the gaps ask for is relative to `a`: "the head of the
queue", "the running job's capability" and "an unfired function" are facts of
`a`, and at `a'` the job has left the queue, nothing runs and the function has
fired. Each row begins with the Q5 post `post a' op c ans ∧`; `postFrom_post`
states that the stronger post implies it, for every operation. The nine
`postFrom_*` equations are `Iff.rfl` of the definition.

| `op` | What `postFrom a a' op c ans` adds to `post a' op c ans` | Gap |
| --- | --- | --- |
| `newPromise` | `∀ r ∈ a'.reactions.fulfill ++ a'.reactions.reject ++ a'.held, r.promise ≠ ans.promise` | E |
| `resolve cap v` | `∀ f ∈ a.functions, f.resolve = cap.resolve → f.alreadyResolved = false → get a'.table cap.promise = some (.fulfilled v)` | A |
| `reject cap r` | `∀ f ∈ a.functions, f.reject = cap.reject → f.alreadyResolved = false → get a'.table cap.promise = some (.rejected r)` | A |
| `perform`, `markHandled`, `enterScript`, `leaveScript` | nothing | — |
| `startJob` | `∃ j rest, a.queue.pending = j :: rest ∧ a'.queue.pending = rest ∧ ans.map Prod.fst = some j` | I |
| `finishJob d` | `∃ j r, a.running = some j ∧ reactionOf a j = some r ∧ (r.capability = none → a' = { a with active := .checkpoint, running := none }) ∧ ∀ cap, r.capability = some cap → ∀ f ∈ a.functions, f.resolve = cap.resolve → (f.alreadyResolved = true → a' = { a with active := .checkpoint, running := none }) ∧ (f.alreadyResolved = false → (∀ v, res = .ok v → get a'.table cap.promise = some (.fulfilled v)) ∧ (∀ e, res = .error e → get a'.table cap.promise = some (.rejected e)))`, where `res` is `reactionHandlerResult r j.argument d` | D (H in its first case) |

`finishJob`'s row covers each case the model has: `[[Capability]]`
*undefined* (nothing settles, whatever the result: gap H's departure), a
capability whose function already fired (nothing settles: a program may
settle a derived promise before its reaction job runs, and the job's call is
then inert, as RESOLVING's step 1 says), and an unfired function (the promise
is settled with the handler's result, `[[Reject]]` for an abrupt one by gap
G's law).

**Unfired and pending.** The posts of `resolve`, `reject` and `finishJob` are
conditioned on the stored function being unfired, the hypothesis gap A is
about. A consumer that knows the promise is pending reaches it through Q5's
`WF.resolvedSettled` (a fired function's promise is not pending); one that
knows the function is unfired learns the promise is pending through
`Coherent.unfiredPending`. At a `WF` agent that is not `Coherent` the
conditional fails (`WS-PROM-CE-048`).

The judgment (B5 battery §5):

```lean
ImplementsFrom op ↔
  ∀ (a : Agent value reason body) (c : Cert op), Coherent a → pre a op c →
    Extends a (step a op).1 ∧ Coherent (step a op).1 ∧
      postFrom a (step a op).1 op c (step a op).2
```

`ImplementsFrom_iff` fixes it; `newPromise_implementsFrom`,
`resolve_implementsFrom cap v`, `reject_implementsFrom cap r`,
`perform_implementsFrom p onF onR d`, `markHandled_implementsFrom p`,
`startJob_implementsFrom`, `finishJob_implementsFrom d`,
`enterScript_implementsFrom`, `leaveScript_implementsFrom` give one theorem per
operation, the four whose post did not change included, and `implementsFrom`
covers all nine. The middle conjunct of each is the operation's `Coherent`
preservation; the pre is Q5's `pre`, unchanged, so a request is admitted
exactly when Q5 admits it.

Against lean4-effect4 as §7.5 reads it: `Coherent` plays `StoreTyped` and
`Extends` plays `World.leHost`, as `WF` and `Le` do. There the post is a
predicate of the answering world, and whatever it needs of the earlier world
travels in the request's certificate; Q5's `Cert` is `Unit` and frozen, so the
earlier agent is an argument of `postFrom` instead. That is the one change of
shape, and it is recorded as a deviation (Q5b.13). Nothing here is a claim
about that repository.

### Q5b.5 The reaction job's two completions (gaps G and H)

`op.newpromisereactionjob` (REACTJOB, 2702885..2705591, digest
`3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b`) inner
steps 6 to 9. B5 battery §6.

| Law | Statement (reading aid) | Census row | Mask |
| --- | --- | --- | --- |
| `callFunctions_resolve_reject` | `WF a → Minted a cap → callFunctions a (·.resolve == cap.resolve) result = callFunctions a (·.reject == cap.reject) result` | `op.createresolvingfunctions`, `record.promisecapability-records` | DB-04 M2 |
| `finishJob_abrupt` | `WF a → a.active = .job s → a.running = some job → reactionOf a job = some r → r.capability = some cap → reactionHandlerResult r job.argument d = .error e → finishJob a d = { reject a cap e with active := .checkpoint, running := none }` | `op.newpromisereactionjob` (inner step 8) | DB-04 M2 |
| `finishJob_normal` | the same with `.ok v` and `resolve a cap v`, without `WF` | `op.newpromisereactionjob` (inner step 9) | DB-04 M2 |
| `finishJob_abrupt_dropped` | `a.active = .job s → a.running = some job → reactionOf a job = some r → r.capability = none → reactionHandlerResult r job.argument d = .error e → finishJob a d = { a with active := .checkpoint, running := none }` | `op.newpromisereactionjob` (inner step 6) | DB-04 M1 |

Gap G: `finishJob` finds the stored functions by the `[[Resolve]]` identity
for both completions. Under `WF` (`functionsBelow`: `[[Reject]]` is
`[[Resolve]] + 1`; `functionsNodup`) and for a minted capability the two picks
select the same records, so the two `callFunctions` are equal, and an abrupt
result is `Agent.reject` through the capability, as inner step 8 says.
`finishJob_abrupt` needs no `Minted` hypothesis: `WF.capabilityStored` supplies
it for the record `reactionOf` finds.

Gap H: inner step 6.a asserts that the result is not abrupt when
`[[Capability]]` is *undefined*; the model takes the host's decision unchecked
(DB-02), so the case is representable, and the law says what the model does:
nothing settles, nothing is traced and nothing is queued; the agent only
returns to a checkpoint. The departure is now a theorem and no longer only a
docstring. Where the model reaches it: a Web IDL reaction with `derive =
false` (§5, `mintFor`) whose handler throws. The specification's REACT would
reject a derived promise there; the model has none, and with the rejection
tracker (`G-02`) out, nothing reports the drop.

### Q5b.6 The face law (gap K)

`Whatwg.Signatures.Ecma262.interpret_sumHandler_inr`, in
`Whatwg/Signatures/Ecma262.lean` (B6 battery §1), the mirror of the landed
`interpret_sumHandler_inl`: a consumer program `p : Effects.Program T α`,
injected by `Effects.Program.inr (S := signature value reason body)`, is
interpreted through `sumHandler view update other` exactly as through `other`
alone. It is `Effects.interpret_inr (handlerAt view update) other p` stated at
`sumHandler`, which `rw` cannot see through. No hypothesis on the lens is
needed: the agent's half takes no step. DB-04 M2, as every face law. The
battery's §2 runs a consumer program and a mixed program, consumer half first,
through the summed handler by `rfl`.

### Q5b.7 Declaration record

Every new public declaration. Module B5 is `Whatwg/Ecma262/AgentInvariant.lean`
(namespace `Whatwg.Ecma262.Agent`), B6 is `Whatwg/Signatures/Ecma262.lean`
(namespace `Whatwg.Signatures.Ecma262`). Route G is an edge of
`PROMISE-PG-AGENT`, named; no declaration here is on a leaf route. "—" means a
model device with no census row. Validation (Val.) is Q5b.12's class; `pend.` marks a law not yet
classified at this commit.

| Declaration | Slice | Role | Anchor (census row) | Route | Mask | Gap | Val. |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Coherent`, `Coherent.toWF` and its seven clause projections | B5 | invariant | the clause anchors of Q5b.2 | G construction | — | A to F | pend. |
| `Coherent.empty`, `Coherent.step`, `Coherent.runOps`, `Coherent.reachable` | B5 | invariant laws | — | G construction, laws | M1 | A to F | pend. |
| `Extends`, `Extends.toLe`, `Extends.markerKept`, `Extends.heldGrows` | B5 | adequacy: world order | `op.createresolvingfunctions` (the marker) | G laws | — | J | pend. |
| `Extends.refl`, `Extends.trans`, `Extends.step` | B5 | adequacy laws | — | G laws | M2 | J | pend. |
| `postFrom` | B5 | adequacy definition | the rows of §5 | G laws | — | A, D, E, I | pend. |
| `postFrom_newPromise`, `_resolve`, `_reject`, `_perform`, `_markHandled`, `_finishJob`, `_enterScript`, `_leaveScript` (8) | B5 | defining equations | the rows of §5; `builtin.promise-executor` for `newPromise` | G laws | M1 | A, D, E | pend. |
| `postFrom_startJob` | B5 | defining equation | `requirement.jobs.1`, `requirement.hostenqueuepromisejob.3` | G laws | M2 | I | pend. |
| `postFrom_post` | B5 | adequacy law | — | G laws | M1 | — | pend. |
| `ImplementsFrom`, `ImplementsFrom_iff` | B5 | adequacy definition and its equation | — | G laws | — (`_iff`: M2) | — | pend. |
| `newPromise_implementsFrom` | B5 | adequacy law | NEWCAP, `builtin.promise-executor` | G laws | M2 | E | pend. |
| `resolve_implementsFrom`, `reject_implementsFrom` | B5 | adequacy laws | RESOLVING, FULFILL, REJECT | G laws | M2 | A | pend. |
| `perform_implementsFrom`, `markHandled_implementsFrom`, `enterScript_implementsFrom`, `leaveScript_implementsFrom` | B5 | adequacy laws | THEN; HANDLEDOP; RUNCOND | G laws | M2 | — | pend. |
| `startJob_implementsFrom` | B5 | adequacy law | RUNCOND, ONEJOB, ORDER | G laws | M2 | I | pend. |
| `finishJob_implementsFrom` | B5 | adequacy law | REACTJOB, COMPLETE | G laws | M2 | D | pend. |
| `implementsFrom` | B5 | adequacy law | — | G laws | M2 | — | pend. |
| `callFunctions_resolve_reject` | B5 | law | `op.createresolvingfunctions`, `record.promisecapability-records` | G laws, semantics | M2 | G | pend. |
| `finishJob_abrupt`, `finishJob_normal` | B5 | laws | `op.newpromisereactionjob` | G laws, semantics | M2 | G | pend. |
| `finishJob_abrupt_dropped` | B5 | law (a named departure) | `op.newpromisereactionjob` | G semantics, counterexamples | M1 | H | pend. |
| `interpret_sumHandler_inr` | B6 | face law | — | G targets | M2 | K | pend. |

The exact signature of every declaration is its battery ascription; this
block is those ascriptions, extracted from the two batteries by script and
pasted unchanged (prefix `Whatwg.Ecma262.Agent.` or
`Whatwg.Signatures.Ecma262.` dropped):

```lean
Coherent :
  ∀ {value reason body : Type}, Agent.Agent value reason body → Prop
Coherent.toWF :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    Agent.WF a
Coherent.functionPromisesNodup :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (a.functions.map Promise.ResolvingFunctions.promise).Nodup
Coherent.unfiredPending :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ f ∈ a.functions, f.alreadyResolved = false →
      Promise.Table.isPending a.table f.promise = true
Coherent.settledTraced :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (∀ (p : Nat) (v : value),
        Promise.Table.get a.table p = some (Promise.State.fulfilled v) →
          (p, Except.ok v) ∈ a.settlements) ∧
      (∀ (p : Nat) (r : reason),
        Promise.Table.get a.table p = some (Promise.State.rejected r) →
          (p, Except.error r) ∈ a.settlements)
Coherent.waitingPending :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject,
      r.phase = Promise.ReactionPhase.waiting →
        Promise.Table.get a.table r.promise = some Promise.State.pending
Coherent.reactionsAllocated :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
      (a.table.getCell r.promise).isSome = true
Coherent.listKinds :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    (∀ r ∈ a.reactions.fulfill, r.kind = Promise.ReactionType.fulfill) ∧
      (∀ r ∈ a.reactions.reject, r.kind = Promise.ReactionType.reject)
Coherent.jobsTyped :
  ∀ {value reason body : Type} {a : Agent.Agent value reason body}, Agent.Coherent a →
    ∀ j : Agent.Job value reason, (j ∈ a.queue.pending ∨ a.running = some j) →
      ∃ r : Promise.Reaction body, Agent.reactionOf a j = some r ∧
        (∀ v : value, j.argument = Except.ok v →
          r.kind = Promise.ReactionType.fulfill ∧
            Promise.Table.get a.table r.promise = some (Promise.State.fulfilled v)) ∧
        (∀ e : reason, j.argument = Except.error e →
          r.kind = Promise.ReactionType.reject ∧
            Promise.Table.get a.table r.promise = some (Promise.State.rejected e))
Coherent.empty :
  ∀ {value reason body : Type},
    Agent.Coherent (Agent.empty : Agent.Agent value reason body)
Coherent.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.Coherent a → Agent.Coherent (Agent.step a op).1
Coherent.runOps :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (ops : List (Agent.Op value reason body)),
    Agent.Coherent a → Agent.Coherent (Agent.runOps a ops).1
Coherent.reachable :
  ∀ {value reason body : Type} (ops : List (Agent.Op value reason body)),
    Agent.Coherent (Agent.runOps (Agent.empty : Agent.Agent value reason body) ops).1
Extends :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body → Prop
Extends.toLe :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    Agent.Le a a'
Extends.markerKept :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    ∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ a'.functions
Extends.heldGrows :
  ∀ {value reason body : Type} {a a' : Agent.Agent value reason body}, Agent.Extends a a' →
    a.held <+: a'.held
Extends.refl :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body), Agent.Extends a a
Extends.trans :
  ∀ {value reason body : Type} {a b c : Agent.Agent value reason body},
    Agent.Extends a b → Agent.Extends b c → Agent.Extends a c
Extends.step :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (op : Agent.Op value reason body),
    Agent.WF a → Agent.Extends a (Agent.step a op).1
postFrom :
  ∀ {value reason body : Type}, Agent.Agent value reason body →
    Agent.Agent value reason body → (op : Agent.Op value reason body) → Agent.Cert op →
      Agent.Op.Answer op → Prop
postFrom_newPromise :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body))
    (cap : Promise.Capability),
    Agent.postFrom a a' Agent.Op.newPromise c cap ↔
      Agent.post a' Agent.Op.newPromise c cap ∧
        ∀ r ∈ a'.reactions.fulfill ++ a'.reactions.reject ++ a'.held,
          r.promise ≠ cap.promise
postFrom_resolve :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (cap : Promise.Capability) (v : value)
    (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.resolve cap v) c ans ↔
      Agent.post a' (Agent.Op.resolve cap v) c ans ∧
        ∀ f ∈ a.functions, f.resolve = cap.resolve → f.alreadyResolved = false →
          Promise.Table.get a'.table cap.promise = some (Promise.State.fulfilled v)
postFrom_reject :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (cap : Promise.Capability) (r : reason)
    (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.reject cap r) c ans ↔
      Agent.post a' (Agent.Op.reject cap r) c ans ∧
        ∀ f ∈ a.functions, f.reject = cap.reject → f.alreadyResolved = false →
          Promise.Table.get a'.table cap.promise = some (Promise.State.rejected r)
postFrom_perform :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
    (onFulfilled onRejected : Option body) (derive : Bool)
    (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body))
    (ans : Option (Option Promise.Capability)),
    Agent.postFrom a a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans ↔
      Agent.post a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans
postFrom_markHandled :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
    (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body))
    (ans : Unit),
    Agent.postFrom a a' (Agent.Op.markHandled promise) c ans ↔
      Agent.post a' (Agent.Op.markHandled promise) c ans
postFrom_startJob :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body))
    (ans : Option (Agent.Job value reason × Option body)),
    Agent.postFrom a a' Agent.Op.startJob c ans ↔
      Agent.post a' Agent.Op.startJob c ans ∧
        ∃ (j : Agent.Job value reason) (rest : List (Agent.Job value reason)),
          a.queue.pending = j :: rest ∧ a'.queue.pending = rest ∧
            ans.map Prod.fst = some j
postFrom_finishJob :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (decision : Except reason value)
    (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' (Agent.Op.finishJob decision) c ans ↔
      Agent.post a' (Agent.Op.finishJob decision) c ans ∧
        ∃ (j : Agent.Job value reason) (r : Promise.Reaction body),
          a.running = some j ∧ Agent.reactionOf a j = some r ∧
          (r.capability = none →
            a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
          ∀ cap : Promise.Capability, r.capability = some cap →
            ∀ f ∈ a.functions, f.resolve = cap.resolve →
              (f.alreadyResolved = true →
                a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
              (f.alreadyResolved = false →
                (∀ v : value,
                  Promise.reactionHandlerResult r j.argument decision = Except.ok v →
                    Promise.Table.get a'.table cap.promise =
                      some (Promise.State.fulfilled v)) ∧
                (∀ e : reason,
                  Promise.reactionHandlerResult r j.argument decision = Except.error e →
                    Promise.Table.get a'.table cap.promise =
                      some (Promise.State.rejected e)))
postFrom_enterScript :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' Agent.Op.enterScript c ans ↔
      Agent.post a' Agent.Op.enterScript c ans
postFrom_leaveScript :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)) (ans : Unit),
    Agent.postFrom a a' Agent.Op.leaveScript c ans ↔
      Agent.post a' Agent.Op.leaveScript c ans
postFrom_post :
  ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
    (op : Agent.Op value reason body) (c : Agent.Cert op) (ans : Agent.Op.Answer op),
    Agent.postFrom a a' op c ans → Agent.post a' op c ans
ImplementsFrom :
  ∀ {value reason body : Type}, Agent.Op value reason body → Prop
ImplementsFrom_iff :
  ∀ {value reason body : Type} (op : Agent.Op value reason body),
    Agent.ImplementsFrom op ↔
      ∀ (a : Agent.Agent value reason body) (c : Agent.Cert op), Agent.Coherent a →
        Agent.pre a op c →
        Agent.Extends a (Agent.step a op).1 ∧ Agent.Coherent (Agent.step a op).1 ∧
          Agent.postFrom a (Agent.step a op).1 op c (Agent.step a op).2
newPromise_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.newPromise : Agent.Op value reason body)
resolve_implementsFrom :
  ∀ {value reason body : Type} (cap : Promise.Capability) (v : value),
    Agent.ImplementsFrom (Agent.Op.resolve cap v : Agent.Op value reason body)
reject_implementsFrom :
  ∀ {value reason body : Type} (cap : Promise.Capability) (r : reason),
    Agent.ImplementsFrom (Agent.Op.reject cap r : Agent.Op value reason body)
perform_implementsFrom :
  ∀ {value reason body : Type} (promise : Nat) (onFulfilled onRejected : Option body)
    (derive : Bool),
    Agent.ImplementsFrom (Agent.Op.perform promise onFulfilled onRejected derive :
      Agent.Op value reason body)
markHandled_implementsFrom :
  ∀ {value reason body : Type} (promise : Nat),
    Agent.ImplementsFrom (Agent.Op.markHandled promise : Agent.Op value reason body)
startJob_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.startJob : Agent.Op value reason body)
finishJob_implementsFrom :
  ∀ {value reason body : Type} (decision : Except reason value),
    Agent.ImplementsFrom (Agent.Op.finishJob decision : Agent.Op value reason body)
enterScript_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.enterScript : Agent.Op value reason body)
leaveScript_implementsFrom :
  ∀ {value reason body : Type},
    Agent.ImplementsFrom (Agent.Op.leaveScript : Agent.Op value reason body)
implementsFrom :
  ∀ {value reason body : Type} (op : Agent.Op value reason body), Agent.ImplementsFrom op
callFunctions_resolve_reject :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (cap : Promise.Capability) (result : Except reason value),
    Agent.WF a → Agent.Minted a cap →
      Agent.callFunctions a
          (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) result =
        Agent.callFunctions a
          (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) result
finishJob_abrupt :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (cap : Promise.Capability) (e : reason),
    Agent.WF a → a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = some cap →
      Promise.reactionHandlerResult r job.argument decision = Except.error e →
      Agent.finishJob a decision =
        { Agent.reject a cap e with active := Jobs.Active.checkpoint, running := none }
finishJob_normal :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (cap : Promise.Capability) (v : value),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = some cap →
      Promise.reactionHandlerResult r job.argument decision = Except.ok v →
      Agent.finishJob a decision =
        { Agent.resolve a cap v with active := Jobs.Active.checkpoint, running := none }
finishJob_abrupt_dropped :
  ∀ {value reason body : Type} (a : Agent.Agent value reason body)
    (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
    (r : Promise.Reaction body) (e : reason),
    a.active = Jobs.Active.job s → a.running = some job →
      Agent.reactionOf a job = some r → r.capability = none →
      Promise.reactionHandlerResult r job.argument decision = Except.error e →
      Agent.finishJob a decision =
        { a with active := Jobs.Active.checkpoint, running := none }
interpret_sumHandler_inr :
  ∀ {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
    (p : Effects.Program T α),
    Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
        (Effects.Program.inr (S := Whatwg.Signatures.Ecma262.signature value reason body) p) =
      Effects.interpret other p
```

### Q5b.8 Builder slices

Ruling R-W9: each slice branches from this breaker's head and merges when its
battery is green, its `known-red.txt` entry is gone and the root gate passes on
the slice branch. The two slices are independent and may run in parallel.

| Slice | Fence | Depends on | Battery |
| --- | --- | --- | --- |
| B5 the invariant, the order, the second judgment, the job's completions | new `Whatwg/Ecma262/AgentInvariant.lean`, importing `Whatwg.Ecma262.AgentLaws` and nothing else; one import line and one docstring bullet in `Whatwg/Ecma262.lean`; its `known-red.txt` line; its root import in `WhatwgTest.lean` | Q5 (landed) | `WhatwgTest/Ecma262/AgentInvariantContract.lean` |
| B6 the face law | one theorem, `interpret_sumHandler_inr`, in `Whatwg/Signatures/Ecma262.lean`, and the sentence of its module docstring ("Summing with another signature") that sends a consumer to `Effects.interpret_inr`; its `known-red.txt` line; its root import | Q5 (landed) | `WhatwgTest/Signatures/Ecma262SumContract.lean` |

What each builder must know:

- **Both.** Declare each theorem with its ascribed statement copied verbatim as
  its type, binders in the ascribed order (R-W5's conversion compares by
  `Expr.eqv`). `Coherent` and `Extends` are structures that `extends` `WF a`
  and `Le a a'`, with the fields in the ascribed order and statements, so that
  the generated projections have the ascribed types. `postFrom` is defined by
  matching on the operation, with each row's first conjunct `post a' op c ans`
  as written in the ascriptions, so that the nine `postFrom_*` are `Iff.rfl`.
  No `simp`, `omega`, `by_cases` or `grind` was needed in the prototype; the
  ceiling traps of `Whatwg/AGENTS.md` ("Ceiling") apply.
- **B5.** The private lemmas of `Whatwg/Ecma262/AgentLaws.lean` are not visible
  from a new module. The prototype carries private copies of the ones it needs,
  restated and re-proved under the same names; a builder may instead make them
  public in `AgentLaws.lean`, which edits a landed module and needs a record per
  name. Inside a theorem named `Coherent.x` or `Extends.x`, the unqualified
  `step`, `runOps`, `empty` and `refl` resolve to `Coherent.step` and so on:
  write `Whatwg.Ecma262.Agent.step`. The examples of the battery's §§7 to 9 are
  closed by `rfl` or `decide` in the kernel and use the B5 laws themselves
  (`Coherent.reachable`, `resolve_implementsFrom`, `postFrom_resolve`,
  `postFrom_startJob`, `post_startJob`).
- **B6.** One line: `exact Effects.interpret_inr (handlerAt view update) other
  p`. The docstring's consumer note becomes "by `interpret_sumHandler_inr`".

### Q5b.9 Masks and counts

The rule is §12's. A law that concludes `Extends` is DB-04 M2 (through
`Le.trace` and `heldGrows`); `postFrom_startJob` observes the queue's order and
is DB-04 M2; `callFunctions_resolve_reject`, `finishJob_abrupt` and
`finishJob_normal` are equations whose sides move the queue and the trace,
DB-04 M2; `finishJob_abrupt_dropped` is an equation that leaves both
unchanged, DB-04 M1; every face law is DB-04 M2.

| Module | Slice | `#check (@n : T)` | of which theorems | DB-04 M1 | DB-04 M2 | `example`s |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `WhatwgTest/Ecma262/AgentInvariantContract.lean` | B5 | 47 | 32 | 14 | 18 | 39 |
| `WhatwgTest/Signatures/Ecma262SumContract.lean` | B6 | 1 | 1 | 0 | 1 | 3 |
| **total** | | **48** | **33** | **14** | **19** | **42** |

The 15 non-theorem ascriptions are the two structures with their eleven
projections (`toWF`, `toLe` and nine clauses) and the two definitions
`postFrom` and `ImplementsFrom`. Every statement is written in full: no `_`
hole, and every implicit argument the body does not determine is written. The
battery also declares, inside its own namespace, the reached witness agents,
the hand-built counterexample agents and their `WF` proofs (Q5b.10); the
`example` count includes the refutations and non-vacuity checks.

### Q5b.10 Counterexample rows

Nine rows, `WS-PROM-CE-048` to `056`, registered in
`test/counterexamples/REGISTER.md` and described in
`test/counterexamples/promise/ATTACKS.md`, section "Q5b agent addendum". Each
is `SEEDED`: its rejecting statement is frozen and red until slice B5 lands.
The witnesses are the B5 battery's §§8 and 9; each counterexample agent is
shown well formed clause by clause, so `WF` admits it, and refuted through the
named clause.

| Id | Gap | Witness (B5 battery) | `WF` admits it | Rejecting statement |
| --- | --- | --- | --- | --- |
| `WS-PROM-CE-048` | A | `ceA`: promise `0` rejected with `5`, its function unfired; `resolve` fires the function and the promise stays rejected | `ceA_wf` | `Coherent.unfiredPending`; `postFrom_resolve` |
| `WS-PROM-CE-049` | B | `ceB`: promise `0` fulfilled, its function fired, the trace empty | `ceB_wf` | `Coherent.settledTraced` |
| `WS-PROM-CE-050` | C | `ceC`: a reaction pair waits on the fulfilled promise `0`; its job can never be queued | `ceC_wf` | `Coherent.waitingPending` |
| `WS-PROM-CE-051` | D | `ceD`: job `⟨0, .ok ()⟩` runs and no record has identity `0`; `finishJob` settles nothing | `ceD_wf` | `Coherent.jobsTyped`; `postFrom_finishJob` |
| `WS-PROM-CE-052` | E | `ceE`: a `.done` reaction pair names the unallocated promise `0`, which `newPromise` then allocates; `ceE'`, the same pair waiting, gets its job queued when the new promise resolves | `ceE_wf` | `Coherent.reactionsAllocated`; `postFrom_newPromise` |
| `WS-PROM-CE-053` | F | `ceF`: a held `~fulfill~` record with an empty handler, and its queued job carries a rejection; REACTJOB step 4.a would give `NormalCompletion`, the model gives the rejection | `ceF_wf` | `Coherent.jobsTyped` (the `[[Type]]` half) |
| `WS-PROM-CE-054` | F | `ceF'`: the tag and the `[[Type]]` agree, and the job carries `6` where the promise was rejected with `5` | `ceF'_wf` | `Coherent.jobsTyped` (the argument half) |
| `WS-PROM-CE-055` | I | `ceI`: the second of two queued jobs runs; the Q5 post of `startJob` holds and `postFrom` refutes it | — (an answer, not an agent) | `postFrom_startJob`; `startJob_implementsFrom` |
| `WS-PROM-CE-056` | J | `fired` and `cleared`: `Le fired cleared` holds though `cleared` clears a fired marker | — (an order) | `Extends.markerKept` |

### Q5b.11 Claim scope: what the addendum does not model

Everything §16 lists stays out, and the addendum depends on it staying out:

- **Thenable adoption (`G-05`)**, `op.newpromiseresolvethenablejob`
  (2705599..2707541). When it enters, a resolving function fires and leaves its
  promise pending, so Q5's `resolvedSettled` must weaken (R-W3), and so must the
  posts of `resolve` and `finishJob` here, which then fulfil only for a
  non-thenable value. `unfiredPending`, `settledTraced` and `waitingPending`
  stay true under adoption as the specification has it; `jobsTyped` gains a
  second job kind (`NewPromiseResolveThenableJob`) that the queue payload does
  not have today (R-W3 fixed it).
- **The rejection tracker (`G-02` remainder)**: the handled bit is read by
  nothing, so the drop of `finishJob_abrupt_dropped` is reported nowhere.
- **Job callbacks (`G-07` remainder)**: a handler is a first-order descriptor
  and its completion is the host's decision (DB-02); `finishJob_abrupt_dropped`
  exists because that decision is unchecked.
- **The binding layer**: the Web IDL verbs omit the IDL-to-ECMAScript value
  conversion; nothing here moves a Web IDL row.
- Not claimed: that `Coherent` characterizes the reachable agents (Q5b.2); a
  program-level adequacy rule over runs (`run_adequate`, §7.4); any coverage
  join.

### Q5b.12 Validation (R-W9)

Status at this commit: every statement of the two batteries elaborates, with no
error, against a scratch prototype whose definitions are final and whose 22
non-equation laws are not yet proved; the `example`s of the batteries, which
are kernel evaluations, pass against it. The per-law classes are recorded here
when the proofs are done, by a later commit of this seat.

### Q5b.13 Deviations from the brief and from the Q5 shape

| Deviation | Reason |
| --- | --- |
| The stronger post reads the starting agent (`postFrom a a' op c ans`) where Q5's post reads the answering agent only | every fact the gaps name is a fact of the starting agent; Q5's `Cert` is `Unit` and frozen, so the earlier agent cannot travel in a certificate (Q5b.4) |
| `Coherent` has two clauses no gap names, `functionPromisesNodup` and `listKinds` | without either, `Coherent` is not inductive; each obstruction is named in Q5b.2 |
| `jobsTyped` also says the record's promise is settled with the job's argument, and covers the running job | the argument is what TRIGGER passes; covering the running job is gap D; one clause answers both D and F |
| The posts of `resolve`, `reject` and `finishJob` are conditioned on the stored function being unfired, not on the promise being pending | the brief's wording for gap A; the pending form is reached through `WF.resolvedSettled` (Q5b.4) |
| Names beyond the brief: `postFrom_post`, `finishJob_normal`, `callFunctions_resolve_reject` (the core of gap G), the `newPromise` row of `postFrom` (gap E as a post) | the brief asks that the stronger post be stronger, that gap G be a lemma, and that gap E be closed; each needs a statement |
| `Extends.step` takes `WF a`, as `Le.step` does | uniformity with the landed order; the proof does not use it |
| Rows beyond A to F: `055` (I) and `056` (J), and two rows for F (`053` the `[[Type]]`, `054` the argument) | each is a statement the addendum refutes; the brief asks for at least one per gap A to F |
| The validation prototype was compiled as one scratch file with each battery, not reinstated into the worktree with the root gate | this seat's environment refused an uncommitted edit of `Whatwg/Ecma262.lean`; Q5b.12 says what was measured instead |

### Q5b.14 Acceptance conditions

1. Every ascription and `example` of the two batteries elaborates with no edit
   to a statement; a builder may repair an `example`'s proof only.
2. The gate passes with the batteries imported by the root, under the strict
   ceiling over the six prefixes with no exception.
3. No landed definition, statement, ascription or battery changes; the only
   edits to landed modules are the import line and docstrings of Q5b.8 and the
   one added theorem of B6.
4. `Whatwg/Ecma262/AgentInvariant.lean` imports `Whatwg.Ecma262.AgentLaws` only:
   no `Effects` and no `Whatwg.Infra` module.
5. Each `known-red.txt` entry is removed by the slice that turns its battery
   green, and only then (R-W9).
6. Both censuses are unchanged; no coverage row moves.
7. `lake exe whatwg_vendorseal`, `lake exe whatwg_citations` and
   `lake exe whatwg_trustselftest` pass at each landing.

### Q5b.15 Freeze receipt

Recorded by a later commit of this seat, after the prototype is removed.

### Q5b.16 Fence

Breaker files, which the builders may not edit: this addendum; the two
batteries; the "Q5b agent addendum" section of
`test/counterexamples/promise/ATTACKS.md`; rows `WS-PROM-CE-048` to `056` of
`test/counterexamples/REGISTER.md`; the Q5b rows of
`docs/PROMISE-AGENT-DAG.md`. The two `known-red.txt` entries are the builders'
to remove, one per slice. This breaker edited no file under `Whatwg/`, no
existing battery, no existing line of a contract, and not `WhatwgTest.lean`,
`COORDINATION.md`, `PLAN.md`, any `AGENTS.md`, `lakefile.toml` or
`WhatwgTest/Ledger/`.
