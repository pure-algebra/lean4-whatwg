# W9 design: `Ecma262.Agent`, one step function, an `Effects` face

Status: research record of the W9 design seat of review lane W (rulings
R-W0 and R-W1 in `COORDINATION.md`). It recommends a design and states the
decisions it leaves to the coordinator. It makes no Model Claim, closes no
graph edge, changes no disposition and moves no coverage row. Every Lean
declaration named below as "prototype" elaborated in this seat's worktree,
was measured, and was then removed; none is on any branch.

| Subject | Pin |
| --- | --- |
| this repository | `main` at `97a871522ce18f792449f51300c9d93288abb398` |
| lean4-effect4 | `refactor/phase1-phase3` at `efcf1ae2f4d4ef7b599e5038572c66a977fe35b2` |
| `effects` | `a4ee7a14248ee5976039b73039319efa87834986` (v0.8.0), both repositories |
| toolchain | `leanprover/lean4:v4.33.1` |

Evidence labels follow the review: `[C]` measured by this seat, with its
command; `[S]` read in source; `[H]` a hypothesis not tried. Masks M1 and M2
are DB-04's unless a sentence says `Effects.Trace.Mask.m1` or `m2`.

## 1. Recommendation

1. Add `Whatwg.Ecma262.Agent.Agent value reason body`. It *contains* the
   landed `Promise.Table`, `Promise.Reactions` and reaction-job `Jobs.Queue`,
   and adds the stored resolving functions (the one-shot markers), the
   records a settled `then` hands back (`held`), the activation with its
   running job, the settlement trace and the function cursor. Nothing landed
   is replaced or edited.
2. One total step function, `Agent.step : Agent v r b → (op : Op v r b) →
   Agent v r b × op.Answer`, over nine first-order operations. A disabled
   operation leaves the agent unchanged and answers `none` or `()`.
3. D46 is repaired additively: `Agent.resolve` and `Agent.reject` call the
   capability's stored resolving functions and then `Table.settleAndTrigger`.
   `react_resolve_enqueues` proves, under mask M2, that Web IDL "react"
   followed by "resolve" enqueues the new reaction's job behind every queued
   job and every reaction already waiting. The frozen `WebIdl.Promise.resolve`
   stays and is re-described as the table view (`resolve_table`), under `WF`.
4. `Agent.WF` states identity freshness and uniqueness, allocation of every
   stored reference, and "resolved functions only on settled promises"; every
   operation must keep it.
5. The `Effects.Signature` face goes in a new tree `Whatwg.Signatures`, Lake
   library `WhatwgSignatures`, under the strict ceiling; the data model
   imports no `Effects` and no Infra. It offers a canonical handler into
   `StateT Agent Id`, a lens handler into any `StateT σ Id` and a sum
   handler: the shape of lean4-effect4's `StoreSig` and `rHandler`.
6. Measured: the three prototypes add 315 constants, all inside `propext` and
   `Quot.sound`, and the full gate passes with a sixth strict prefix. The
   pinned `effects` package's 2,613 constants reach no `Classical.choice`.
7. Run it as promise slice Q5, before P8 proper, with its own graph
   `PROMISE-PG-AGENT`. Order: rulings (section 7); a breaker freezes Q5 with
   eight counterexample rows; builder B1 (record, step, D46); then B2
   (invariant), B3 (Web IDL verbs) and B4 (face) in parallel; review;
   landing. W8's one-table cutover builds on the record, with Streams tokens
   as reactions whose `body` is a Streams descriptor.
8. lean4-effect4 can consume it once it requires `whatwg`. DI-30 refused the
   34 promise declarations unless reproved without choice; since lane V none
   reaches it. Re-ruling DI-30 is lean4-effect4's.

## 2. Evidence

### 2.1 Measurements in this repository

| What | Result | Command |
| --- | --- | --- |
| base build | 386 jobs; gate: 222 sources, 16,723 declarations, choice reached by 84 of 12,766 in `Whatwg`, 5 strict prefixes, 0 exceptions | `lake build` `[C]` |
| ES2026 coverage | denominator 75, owned-with-green 0/75, absent 75 | `lake exe whatwg_census --standard ecma262 --report` `[C]` |
| `effects` v0.8.0 axioms | 2,613 constants in 19 modules (`Effects` and `Effects.Experimental` roots); 0 reach `Classical.choice`; no axiom outside `propext`, `Quot.sound` | `lake build Effects Effects.Experimental`, then `lake env lean EffectsAxioms.lean` (appendix B) `[C]` |
| cited `Effects` constants | `Signature`, `Signature.sum`, `Program`, `Program.perform`, `Program.inl`, `Handler`, `Handler.sum`, `interpret`, `interpret_perform`: none; `interpret_bind`, `interpret_inl`, `interpret_through`: `propext`, `Quot.sound`; `Trace.Mask.m1`, `m2`: none | same script `[C]` |
| prototype axioms | 315 constants (`Whatwg.Ecma262.Agent` 291, `Whatwg.WebIdl.Agent` 7, the face 17); 0 outside `propext`, `Quot.sound` | `lake env lean ModuleAxioms.lean` (appendix B) `[C]` |
| gate with prototypes | 398 jobs; 226 sources, 17,038 declarations; choice reached by 84 of 13,081 in `Whatwg`; 6 strict prefixes (with `Whatwg.Signatures`), 0 exceptions | `lake build` with the tracked-file diff of appendix A.4 `[C]` |
| kernel replay | exit 0 in 7 s | `lake env leanchecker Whatwg.Ecma262.Agent Whatwg.WebIdl.Agent Whatwg.Effects.Ecma262` (face under its first name) `[C]` |
| library cost | `lake build WhatwgEcma262` 6 jobs (5 before); `WhatwgWebIdl` 10; `WhatwgSignatures` 14 | `lake build <lib>` `[C]` |
| data-model closure | importing `Whatwg.Ecma262.Agent` and `Whatwg.WebIdl.Agent` loads 0 `Effects.*` and 0 `Whatwg.Infra.*` modules | `lake env lean Imports.lean` `[C]` |
| core `Except` | `DecidableEq (Except Nat Nat)` fails to synthesize, so `Jobs.ReactionJob (Except reason value)`, the landed reaction-job queue and `SettlementTrace` have no `DecidableEq` | `#synth` probe `[C]` |
| landed instances | `ResolvingFunctions` and `Jobs.Active` derive `DecidableEq` only, `Reaction` derives `Repr` only, and `Reactions` derives nothing; positive ascriptions only in `WhatwgTest/Ecma262/PromiseContract.lean`, `JobsContract.lean`, `PromiseFidelityContract.lean` | grep `[C]` |
| namespace hazard | inside `namespace Whatwg.Effects.X`, `Effects.Handler` resolves to `Whatwg.Effects.Handler` once that exists | `lake env lean Shadow.lean` `[C]` |
| D46 witness | at the agent after one `newPromise` from `Agent.empty`: store-level `react` then `resolve` leaves 0 jobs; agent-level leaves `[⟨0, .ok ()⟩]`; the hypotheses of `react_resolve_enqueues_wf` hold there; all by `rfl`, inside `propext`, `Quot.sound` | `lake env lean Witness040.lean` (appendix B) `[C]` |
| `WF.settle` | `settle` keeps the seven prototype clauses: 185 non-blank lines with five reusable helpers, inside `propext`, `Quot.sound` | `lake env lean WFSettle.lean` (appendix B) `[C]` |
| choice traps | `rw [beq_self_eq_true]` at `Nat` reaches `Classical.choice`; `decide_eq_true rfl` reaches nothing; a `simp` that rewrites an `if` condition reached choice in `waitingOn_add_fulfill` until replaced by `List.filter_cons_of_pos` | probes `[C]` |

The prototype took the face first as `Whatwg.Effects.Ecma262`, measured it,
then renamed it to `Whatwg.Signatures.Ecma262` because of the namespace
hazard. The renamed tree passed the full gate (the "gate with prototypes"
row is the renamed run). The `leanchecker` run predates the rename.

### 2.2 lean4-effect4 at `efcf1ae2`: what it needs and can consume

- It neither requires nor names this package: `git grep -n -i whatwg
  efcf1ae2 -- lakefile.toml lake-manifest.json` is empty. `[C]` Its manifest
  lists `effects`, `typescript` and `hash` at this repository's pins, plus
  `aesop`, which brings `batteries`. `[S]`
- Trust: `Test/Audit/AxiomGate.lean` holds every `Effect4.*` and `Test.*`
  declaration to `allowedAxioms := [propext, Quot.sound]`, following
  axioms transitively. A provider constant fails it only if an audited
  declaration cites a constant that reaches choice. `[C]`
- DI-30 (ruled 2026-09-09): "the 34 WHATWG Promise/Jobs declarations are
  **refused** unless reproved". `[C]` Since R-V6 none under
  `Whatwg.Ecma262` or `Whatwg.WebIdl` reaches choice, and the strict ceiling
  enforces it. DI-30's ground is discharged here; its text is unchanged
  there.
- Proof form. Signatures are `Effects.Signature.{0, 0}` with handlers into
  `StateT Stores Id`, summed by `Signature.sum` and `Handler.sum`: `StoreSig`
  and `storeHandler` in `src/Effect4/Laws/Program/Denote.lean`, `FiberSig`
  and `RSig` in `Sched.lean`. `[C]` It does not use `Effects.Family`,
  `Effects.Trace` masks or `Effects.Experimental`. `[S]`
- Its core root no longer imports `Effects` (commit `7a12f485`). `[S]`
  DI-90 (ruled 2026-09-16) brings "the consumed algebra core in-tree under
  the same names and drop the pin". Decisions row 53 ("no vendoring",
  open) disagrees. `[C]`
- Runtime form. Host rows are answered by keyed `Completion` replies. A row
  whose answer carries an internal handle (fiber, cell, deferred) is refused
  at admission (row 97, `findInternalHandleInTable`). So a provider cannot
  hand a program a promise handle. `[S]`
- Its `DeferredStore` resumes waiters inline (`WakeMode.now`), where
  ECMAScript enqueues reaction jobs. The two agree on cell state at most and
  disagree on settlement order. So this agent is an authority for its host
  tail (`runPromise`, the sync scheduler's microtasks), as its own
  gitignored notes already say, not a replacement for `DeferredStore`. `[S]`
- Stream kernel: unchanged (section 6.6).

The smallest provider API lean4-effect4 could import, once the slices land:

| Item | Value |
| --- | --- |
| Lake | `[[require]] name = "whatwg"` at the landing commit; library `WhatwgEcma262` (and optionally `WhatwgSignatures`) |
| modules | `Whatwg.Ecma262.Agent` (data model and laws); optionally `Whatwg.Signatures.Ecma262` (face) |
| types | `Agent.Agent value reason body`, `Agent.Op`, `Agent.Op.Answer`, `Agent.WF`; the landed `Promise.Table`, `Promise.State`, `Promise.Capability`, `Jobs.Queue`, `Jobs.ReactionJob`, `Jobs.Active` |
| operations | `Agent.empty`, `Agent.step` and the nine named operations |
| properties | every constant inside `propext`, `Quot.sound`, enforced by this repository's gate; all types in `Type`, matching `.{0, 0}`; `DecidableEq` and `Repr` on `Agent` given instances for the three parameters; no Infra, no `Effects` in the data model; `step` total; the D46, FIFO, run-to-completion and `WF` laws |
| sum route | `Whatwg.Signatures.Ecma262.sumHandler view update storeHandler`, given a field of `Stores` that holds an `Agent` |

### 2.3 The review's "Fit with lean4-effect4", sentence by sentence

| Sentence (review, section "Fit with lean4-effect4") | At `efcf1ae2` | Evidence |
| --- | --- | --- |
| Its gate audits only `Effect4.*` and `Test.*` and follows axioms transitively | holds; the cited line numbers moved | `belongsToAuditedTree`, `allowedAxioms` `[C]` |
| Importing this package costs nothing at that gate | holds | same `[C]` |
| A declaration fails only when it cites a provider constant that reaches choice | holds | same `[C]` |
| The definitions are citable today; the six theorems of appendix A are what DI-30's refusal applies to | superseded: since R-V6 no declaration under the two prefixes reaches choice; DI-30's text still refuses | gate line at `97a8715` `[C]`; DI-30 `[C]` |
| It built an unproved promise host and archived it in `ab9f464b` | holds; no file named `Promise` at HEAD | `git log -- '*Promise*'` `[S]` |
| `Whatwg.Ecma262` is the proved counterpart | holds; nothing replaced it | `[S]` |
| Its `DeferredStore` relates to `Promise.Table` by a projection under M1 | weakened: the cell state projects (`none` to pending, `ofExit` success and failure to fulfilled and rejected; die, interrupt and `ofRefGet` have no counterpart); waiter order differs, and no M1 or M2 observation exists there | `Machine/Stores.lean`, `Completion.lean` `[S]` |
| Its stream kernel is three external rows with answer `Option (List α)` | holds; the file is unchanged | `git diff 0f16828a efcf1ae2 -- src/Effect4/Program/Stream.lean` is empty `[C]` |
| It has no Channel calculus, so P12's Effect Channel embedding has no target | holds | `[S]` |
| It retired the Flow route | holds | `README.md`: "retained in git history and on branch `archive/flow-route`" `[C]` |
| RS-3 says a Signature with one Handler; nothing under `Whatwg/` imports `Effects` | holds at the base | grep `[C]` |
| Bespoke step functions, so it cannot sum a provider signature | holds at the base; this design repairs it for the promise layer | section 3.4 |
| `m1` keeps operations, answers and outcome; `m2` keeps every event | holds; `m1` also keeps failures and the frontier | `Effects/Trace.lean` `[C]` |
| The names agree and the meanings differ | holds; lean4-effect4 uses neither (its observation is `Obs`) | `[S]` |
| `Morphism` and `Transport` moved under `Effects.Experimental` with no contract | holds; they reach no choice either | `Effects/Experimental.lean`; axiom script `[C]` |
| A bridge on signature morphisms would rest on that | holds; this design needs no morphism (a view and update replace `mapHom`) | section 3.4 |
| API shape: no agent record | holds at the base | `[C]` |
| `Reaction` derives `Repr` only, `Reactions` nothing | holds; also `ResolvingFunctions` and `Active` lack `Repr`, and `Except` lacks `DecidableEq` | section 2.1 `[C]` |
| Every type outside `Streams.Data` is fixed at `Type` | holds; costs lean4-effect4 nothing, its signatures are `.{0, 0}` | `[S]` |
| 334 `private` declarations; 1,492 theorems under `Whatwg/` | not re-measured | — |

## 3. Public declaration record

### 3.1 The agent record (question b)

`Agent value reason body : Type` has nine fields, three of them the landed
stores, held by value:

| Field | Type | Role |
| --- | --- | --- |
| `table` | `Promise.Table value reason` | landed; `[[PromiseState]]`, `[[PromiseResult]]`, `[[PromiseIsHandled]]` |
| `reactions` | `Promise.Reactions body` | landed; the two reaction lists |
| `held` | `List (Promise.Reaction body)` | records `Reactions.mint` hands to the caller on a settled `then` (F2); a job needs its handler and capability |
| `queue` | `Jobs.Queue (Jobs.ReactionJob (Except reason value))` | landed; exactly the queue every landed operation writes |
| `functions` | `List Promise.ResolvingFunctions` | the one-shot markers; D17 and D46 need them as state |
| `nextFunction` | `Nat` | the function cursor (the landed "function seed") |
| `active` | `Jobs.Active` | landed activation |
| `running` | `Option (Jobs.ReactionJob …)` | the job under evaluation; `Active.job` carries a serial only |
| `settlements` | `Promise.SettlementTrace value reason` | the landed F6 carrier, now with an ECMA-262 producer (closes D20's "no producer") |

Three cursors stay: `table.next`, `reactions.next` and `nextFunction`. A
job's serial is its reaction identity, so no fourth supply exists. That is
the point of WS-PROM-CE-039 and the Q4 amendment A4: Q4's
`Config.nextJob` is a second supply, and the landed `triggerReactions`
writes `.queued r.id`. On the agent the two agree by construction, and W8's
cutover can drop `phaseErase` and `reactionErase` (section 6.5).

One cursor for all identities was rejected. The landed `Table.fresh`,
`Reactions.add` and `newPromiseCapability` each consume their own counter,
so a single supply would make none of them an exact view.

Instances. `Agent` derives `DecidableEq` and `Repr`, conditional on the
three parameters. That needs four instances the landed carriers lack:

- a *scoped* `DecidableEq (Except ε α)`. Batteries derives one globally
  (`Batteries.Lean.Except`; lean4-effect4 requires Batteries through
  `aesop`), so a global one here would be a second instance for that
  consumer;
- `deriving instance DecidableEq for Promise.Reaction`;
- `deriving instance DecidableEq, Repr for Promise.Reactions`;
- `deriving instance Repr` for `ResolvingFunctions` and `Jobs.Active`.

The second contradicts `E-29`'s "must not gain one silently", so it is
decision 2. The gate accepts `deriving instance`, `scoped instance` and
`nomatch` in an audited module `[C]`.

`WF a : Prop`, as prototyped, has seven clauses:

- `tableNodup`, `tableBelow`: identities unique and below `table.next`;
- `functionsBelow`: `reject = resolve + 1` and below `nextFunction`;
- `functionsAllocated`;
- `resolvedSettled`: a fired function's promise is not pending;
- `reactionsBelow`, `queueBelow`.

The packet adds seven, for fourteen in all:

- `paired`: the landed `add_paired` shape;
- `functionsNodup`: on `resolve` identities, so `find?` names one record;
- `heldDistinct`: registered and held identities disjoint, so `reactionOf`
  is unambiguous;
- `queuedKnown`: every queued job names a record;
- `runningActive`: `running = some j ↔ active = .job j.reaction`;
- `capabilityStored`: every stored capability has its functions stored;
- `settlementsCoherent`: every trace entry is the table's settled state and
  ids are unique. This closes D20.

`resolvedSettled` holds only while thenable adoption (`G-05`) is out.
Adoption leaves a resolved promise pending, and the clause must then be
weakened (decision 9).

`Table.mk` stays public. `WF` answers "duplicate identifiers are
constructible" by making such an agent ill-formed, not unconstructible.
That is additive.

### 3.2 The alphabet and the step function (question c)

| `Op` constructor | `Op.Answer` | Anchor (census row) | Landed store-level view |
| --- | --- | --- | --- |
| `newPromise` | `Promise.Capability` | `op.newpromisecapability`, `op.createresolvingfunctions` | `Promise.newPromiseCapability` (`newPromise_capability`) |
| `resolve cap v` | `Unit` | `op.createresolvingfunctions` resolve steps 1 to 3 and 5; `op.fulfillpromise`; `op.triggerpromisereactions`; Web IDL `op.resolve` | `Table.settle` (`resolve_table`), `fulfillPromise` (`settle_ok_fulfillPromise`) |
| `reject cap r` | `Unit` | reject steps; `op.rejectpromise`; Web IDL `op.reject` | `Table.settle`, `rejectPromise` |
| `perform p onF onR derive` | `Option (Option Capability)` | `op.performpromisethen`; Web IDL `op.dfn-perform-steps-once-promise-is-settled` steps 6 to 8 when `derive` | `performPromiseThen`; `WebIdl.Promise.react` |
| `markHandled p` | `Unit` | `op.mark-a-promise-as-handled` | `Table.markHandled` (`markHandled_table`) |
| `startJob` | `Option (Job × Option body)` | `requirement.jobs.1`, `.2`, `requirement.hostenqueuepromisejob.3` | `Jobs.startJob` (`startJob_agree`) |
| `finishJob d` | `Unit` | `op.newpromisereactionjob` steps 4 to 9, `requirement.jobs.3` | `runReactionJob`'s table, `Jobs.completeJob` |
| `enterScript` | `Unit` | `requirement.jobs.1` (an execution context is running) | — |
| `leaveScript` | `Unit` | `requirement.jobs.1` (the stack is empty) | — |

Disabled cases:

- `startJob` away from a checkpoint or on an empty queue;
- `finishJob` with no job running;
- `perform` on a missing promise;
- `resolve` through a capability whose functions this agent never stored,
  or that has fired.

Each leaves the agent unchanged. This is decision 7's guarded-total
style. DB-07 holds: an empty queue is a live frontier, not a failure.

The step emits no event list. Its observation is the answer together with
the state change. The settlement suffix (`settlements`) carries M2's
settlement order. The queue carries job order, and the `startJob` answers
of a run carry start order. lean4-effect4's observations are state-based
too (`Obs`, "deliberately without the trace"). A separate `Agent.Event`
alphabet would duplicate state that is already first-order.

Handlers are first-order descriptors (`body`). The continuation of a
`perform` belongs to the program, not to the state. So, against RS-3's note
that "a promise reaction" fails Plotkin and Power's algebraic test, every
operation here passes it: the higher-order shape never enters (DB-02).
RS-Q1 is answered both ways. The FIFO queue is state (DB-03), and the host
scheduler's two interactions, start and finish, are operations whose order
the program chooses and whose job choice it does not.

Anchors attach as in the landed modules. Each operation's docstring names
its census row id, span and, where frozen, its digest. A witness theorem
names the row id. The join happens test-side in
`WhatwgTest/Audit/Ecma262/SpecCoverage.lean`. This slice moves no number.

Six ES2026 rows are candidates for `green` once the coverage seat joins them
step by step. They are `requirement.jobs.1`, `.2` and `.3`, and
`requirement.hostenqueuepromisejob.3`; R-P24 kept these out because nothing
global reached `startJob`, and the agent's `step` now does. The other two
are `op.fulfillpromise` and `op.triggerpromisereactions`, whose steps the
landed laws already cover. `[H]`

`op.rejectpromise` stays `partial` (step 6, `HostPromiseRejectionTracker`,
`G-02`). So do `op.performpromisethen` (step 11.b, `G-02`),
`op.newpromisereactionjob` (`HostMakeJobCallback`, `G-07`) and
`op.createresolvingfunctions` (thenables, `G-05`). The Web IDL `op.resolve`,
`op.reject` and `react` rows stay `partial` at best: each has a step that
converts an IDL value to an ECMAScript value, which is the binding layer
(`hostOnly`).

### 3.3 `resolve` that triggers reactions (question d)

The names are `Whatwg.Ecma262.Agent.resolve` and `reject` (ES:
`Call(cap.[[Resolve]])`), with Web IDL wrappers `Whatwg.WebIdl.Agent.resolve`
and `reject` in a new module `Whatwg/WebIdl/Agent.lean`. The landed
`Whatwg.WebIdl.Promise.resolve` and `reject` keep their signatures and laws.
They become the store-level view, proved by:

- `Agent.resolve_table`: under `WF`, for a capability this agent stored,
  `(resolve a cap v).table = Table.settle a.table cap.promise (.ok v)`. When
  the functions have already fired, `resolvedSettled` makes the promise
  settled, and `Table.settle` is the identity there too.
- `WebIdl.Agent.resolve_view`: the same, ending in
  `WebIdl.Promise.resolve a.table cap.promise v`.

The D46 law is `Agent.react_resolve_enqueues`, with `_wf` and `_exactly`
corollaries and the Web IDL restatement `WebIdl.Agent.react_resolve`; mask
M2. Hypotheses: the promise is pending, the capability's functions are
stored and unfired, and they name the capability's promise. Conclusion: the
queue after Web IDL `react` (with its derived capability) and `resolve` is

```text
a.queue.pending ++ ((waitingOn a.reactions p .fulfill).map (job · (.ok v))
                    ++ [⟨a.reactions.next, .ok v⟩])
```

With nothing waiting on `p`, it is exactly
`a.queue.pending ++ [⟨a.reactions.next, .ok v⟩]`.

No frozen sentence is false after this slice. Two production docstrings in
`Whatwg/WebIdl/Promise.lean` (`Promise.resolve`, `Promise.reject`) should
say "store-level view; the agent operation is `Whatwg.WebIdl.Agent.resolve`".
They are builder-owned, so no breaker amendment is needed.

Seed row, `WS-PROM-CE-040`: "Web IDL `react` followed by `resolve` enqueues
no reaction job, because `WebIdl.Promise.resolve` is `Table.settle` and its
signature carries no reaction store or queue (D46)." The witness, finite and
decidable over `Nat` and `Unit`, runs in two parts; both elaborated by `rfl`
`[C]`.

1. Store level. From `Agent.empty`, call `newPromise`, then
   `WebIdl.Promise.react` on the table, reactions and queue. Call
   `WebIdl.Promise.resolve` on the table. The caller's queue is still
   `Queue.empty`.
2. Agent level. Call `WebIdl.Agent.react`, then `WebIdl.Agent.resolve`. The
   queue is `[⟨0, .ok ()⟩]`.

### 3.4 The `Effects.Signature` face (question e)

Module `Whatwg/Signatures/Ecma262.lean`, namespace
`Whatwg.Signatures.Ecma262`. It imports `Effects.Algebra.Sum` and, through
it, `Signature`, `Program`, `Handler`, `MonadLaws` and `Laws`; no `Family`,
`Trace`, `Flow` or `Experimental`. Contents:

- `signature v r b : Effects.Signature.{0, 0} := ⟨Agent.Op v r b,
  Agent.Op.Answer⟩`, an `abbrev`, as lean4-effect4's `StoreSig` is. As a
  `def` it blocks `Effects.interpret_perform`'s unification `[C]`.
- `handler v r b : Effects.Handler (signature v r b) (StateT (Agent v r b)
  Id)`, the canonical handler, one `step` per operation.
- `handlerAt view update : Effects.Handler (signature v r b) (StateT σ Id)`:
  the same handler for any state that holds an agent. `handlerAt_id`
  recovers the canonical one by `rfl`.
- `sumHandler view update other := Handler.sum (handlerAt view update)
  other`, the shape of lean4-effect4's `rHandler`.
- `run`, the step-fold a program denotes.
- The handler and step agree through four laws:
  - `interpret_eq_run`: for every program, interpretation through `handler`
    equals `run`;
  - `interpret_handlerAt`: under `view (update a s) = a`, the lens handler
    runs the same fold on the viewed agent and writes back its final agent;
  - `interpret_perform_step`: via `Effects.interpret_perform`;
  - `interpret_sumHandler_inl`: via `Effects.interpret_inl`.
- `resolvedWith v`, Web IDL "a promise resolved with" as a two-operation
  program, with `run_resolvedWith`.

The face needs no signature morphism and so nothing from
`Effects.Experimental`.

Placement. Every cited `Effects` constant is choice-free `[C]`, so the
strict ceiling is not the reason to separate the face. Three facts are:

- dependency hygiene: a data-model consumer must not need `effects` to
  build. `[C]`: 0 `Effects` modules in its closure.
- DI-90: if lean4-effect4 vendors `Effects.*` under the same module names
  and drops the pin, a build that also has this package's `effects` require
  has two packages providing `Effects.Algebra.Signature`. Keeping the face
  optional keeps the record usable either way. `[H]` on Lake's exact
  behaviour.
- the namespace hazard of section 2.1, which is why the tree is
  `Whatwg.Signatures`, not `Whatwg.Effects`.

A library per standard (R-V7(d)) means the face cannot sit under
`Whatwg.Ecma262.*` in another library, because Lake gives every submodule of
`Whatwg.Ecma262` to `WhatwgEcma262`. Hence a new prefix and library.
Recommended layout:

```toml
[[lean_lib]]
name = "WhatwgSignatures"
roots = ["Whatwg.Signatures"]
globs = ["Whatwg.Signatures.*"]
```

The plan, measured in the prototype run:

- add the library to `defaultTargets`;
- import `Whatwg.Signatures` from the umbrella `Whatwg.lean`, so the audit
  root reaches it;
- add `Whatwg.Signatures` to `strictCeilingPrefixes`. It joins at zero
  residue (R-V1).

A future `Whatwg.Signatures.Streams` lives beside it. The `[[require]]` of
`effects` is package-level already; every consumer clones it today.

Masks. Keep the names apart. Prose writes "DB-04 M1" and "DB-04 M2". When W6
makes masks data, the DB-04 masks get names by meaning (for example
`chunksAndOutcome` and `settlementOrder`), never `m1` and `m2`. For this
layer, DB-04 M2 is the settlement trace and the job order.
`Effects.Trace.Mask.m2` keeps every event of an `Effects` trace and
`m1` keeps operations, answers, failures and outcome; neither observes the
agent's internal settlements, which are state, not events. The relation to
record is "an `Effects` trace of this handler under `m1` determines the
operation word; with `interpret_eq_run` the word determines the agent, hence
DB-04 M2". `[H]`: not prototyped.

### 3.5 Lifting the landed laws (question f)

| Landed law | Agent-level statement | Route |
| --- | --- | --- |
| `Jobs.run_to_completion`, `startJob_blocked` | `startJob_running` | one line `[C]` |
| `Jobs.startJob_run_agree`, `Queue.dequeue_fifo` | `startJob_agree`; the oldest job starts | one line `[C]` |
| `Jobs.run_fifo`, `hostEnqueuePromiseJob_order` | the `startJob` answers of a run form a prefix of the enqueue order | new induction over runs, about 40 lines `[H]` |
| `completeJob_job` | `finishJob` returns to a checkpoint | inside `finishJob_settles_capability` `[C]` |
| `fulfillPromise_eq`, `rejectPromise_eq` | `settle_ok_fulfillPromise` and its reject twin | `rfl` `[C]` |
| `performPromiseThen_handled` (F1), `mint_no_waiting` (F2) | `perform` marks handled; a settled branch grows `held` only | case split on `derive`, one line each `[H]` |
| `settleAndTrigger_cleared` (F3), `settleTraced_pending` (F6) | `settle` clears both lists and appends one trace entry | one line `[H]` |
| `runReactionJob_resolve`, `_reject` (F4) with D17 | `finishJob_settles_capability` | new proof `[C]` |
| `callResolve_disables_reject` | agent `resolve` then `reject` is inert | new short proof `[H]` |
| `triggerReactions_order` | `react_resolve_enqueues` (D46) | new proof `[C]` |
| D20 (no coherence of trace and table) | `WF.settlementsCoherent` | new proof `[H]` |
| `WF` kept by every operation | 9 operations by 14 clauses | new; `WF.empty`, `WF.newPromise`, `WF.markHandled` and `WF.settle` proved for the 7 prototype clauses `[C]`; `WF.settle` took 185 lines with helpers that `callFunctions` and `finishJob` reuse; the rest, about 900 to 1,200 lines in all `[H]` |
| Q4 bridges (`register_reactions_bridge`, `notifySettled_*`) | not lifted here | W8's cutover embeds `Agent` in `Config` |

Proof style that stayed under the strict ceiling `[C]`:

- `decide_eq_true rfl` for `n == n`;
- `List.filter_cons_of_pos (p := …)` instead of a `simp` over `if`;
- `rw [if_neg …]` after `dsimp only`;
- `List.find?_some (p := …)` with the predicate explicit.

### 3.6 Declarations, roles, anchors and routes

Roles follow `docs/AGENT-ROUTING.md`. Routes:

- G = a graph edge of `PROMISE-PG-AGENT`;
- L = a local receipt linked to that graph.

| Declaration | Module | Role | Anchor | Route |
| --- | --- | --- | --- | --- |
| `Agent.Agent`, `Agent.Agent.mk` | `Whatwg.Ecma262.Agent` | canonical carrier | `clause.jobs`, `clause.properties-of-promise-instances` | G (identity, representation) |
| `Agent.empty` | same | helper | — | L |
| `Agent.Job` (abbrev) | same | view | `op.newpromisereactionjob` | L |
| `instDecidableEqExcept` (scoped) and 4 `deriving instance` | same | helper | — | L (decision 2) |
| `newPromise`, `settle`, `callFunctions`, `resolve`, `reject`, `mintFor`, `perform`, `markHandled`, `reactionOf`, `startJob`, `finishJob`, `enterScript`, `leaveScript` | same | canonical operations | rows of the table in 3.2 | G (semantics) |
| `Op`, `Op.Answer` | same | canonical alphabet | — | G (identity) |
| `step` | same | canonical transition | — | G (semantics) |
| `WF` and its lemmas | same | invariant | — | G (construction, laws) |
| `settleAndTrigger_table`, `settle_ok_fulfillPromise`, `newPromise_capability`, `markHandled_table`, `markHandled_get`, `startJob_agree` | same | bridges to landed operations | as above | G (bridges) |
| `resolve_table` | same | view of `Table.settle` | `op.resolve` via RESOLVING | G (bridges) |
| `waitingOn_add_fulfill`, `react_resolve_enqueues`, `_wf`, `_exactly` | same | laws (D46) | `op.triggerpromisereactions`, `op.performpromisethen` | G (laws, counterexamples) |
| `finishJob_settles_capability` | same | law (D17) | `op.newpromisereactionjob` steps 6 to 9 | G (laws) |
| `startJob_running` | same | law | `requirement.jobs.3` | G (laws) |
| `WebIdl.Agent.newPromise`, `resolve`, `reject`, `react`, `resolvedWith` | `Whatwg.WebIdl.Agent` | adapters | Web IDL `op.a-new-promise`, `op.resolve`, `op.reject`, `op.dfn-perform-steps-once-promise-is-settled`, `op.a-promise-resolved-with` | G (semantics) |
| `WebIdl.Agent.resolve_view`, `react_resolve` | same | bridge, law | `op.resolve` | G (bridges, laws) |
| `signature`, `handler`, `handlerAt`, `sumHandler`, `run` | `Whatwg.Signatures.Ecma262` | face (adapter) | — | G (targets) |
| `handler_handle`, `handlerAt_id`, `interpret_eq_run`, `interpret_handlerAt`, `interpret_perform_step`, `interpret_sumHandler_inl`, `resolvedWith`, `run_resolvedWith` | same | face laws | — | G (targets) |

The packet adds, unprototyped: the seven further `WF` clauses and the lemmas
that every operation keeps them; `rejectedWith`, `uponFulfillment`,
`uponRejection` and `markAsHandled` in `Whatwg.WebIdl.Agent`; and the lifted
laws of 3.5.

Exact signatures as they elaborated, printed with `pp.fieldNotation false`
and `open Whatwg.Ecma262`. The face was printed under its first name
`Whatwg.Effects.Ecma262`; the names below are renamed textually, with
nothing else changed.

```text
Agent.Agent : Type → Type → Type → Type
@Agent.Agent.mk : {value reason body : Type} → Promise.Table value reason →
  Promise.Reactions body → List (Promise.Reaction body) →
  Jobs.Queue (Agent.Job value reason) → List Promise.ResolvingFunctions → Nat →
  Jobs.Active → Option (Agent.Job value reason) →
  Promise.SettlementTrace value reason → Agent.Agent value reason body
@Agent.empty : {value reason body : Type} → Agent.Agent value reason body
@Agent.newPromise : {value reason body : Type} →
  Agent.Agent value reason body → Agent.Agent value reason body × Promise.Capability
@Agent.settle : {value reason body : Type} →
  Agent.Agent value reason body → Nat → Except reason value → Agent.Agent value reason body
@Agent.callFunctions : {value reason body : Type} → Agent.Agent value reason body →
  (Promise.ResolvingFunctions → Bool) → Except reason value → Agent.Agent value reason body
@Agent.resolve : {value reason body : Type} →
  Agent.Agent value reason body → Promise.Capability → value → Agent.Agent value reason body
@Agent.reject : {value reason body : Type} →
  Agent.Agent value reason body → Promise.Capability → reason → Agent.Agent value reason body
@Agent.mintFor : {value reason body : Type} →
  Agent.Agent value reason body → Bool → Agent.Agent value reason body × Option Promise.Capability
@Agent.perform : {value reason body : Type} → Agent.Agent value reason body →
  Nat → Option body → Option body → Bool →
  Agent.Agent value reason body × Option (Option Promise.Capability)
@Agent.markHandled : {value reason body : Type} →
  Agent.Agent value reason body → Nat → Agent.Agent value reason body
@Agent.reactionOf : {value reason body : Type} →
  Agent.Agent value reason body → Agent.Job value reason → Option (Promise.Reaction body)
@Agent.startJob : {value reason body : Type} → Agent.Agent value reason body →
  Agent.Agent value reason body × Option (Agent.Job value reason × Option body)
@Agent.finishJob : {value reason body : Type} →
  Agent.Agent value reason body → Except reason value → Agent.Agent value reason body
@Agent.enterScript : {value reason body : Type} →
  Agent.Agent value reason body → Agent.Agent value reason body
@Agent.leaveScript : {value reason body : Type} →
  Agent.Agent value reason body → Agent.Agent value reason body
Agent.Op : Type → Type → Type → Type
@Agent.Op.Answer : {value reason body : Type} → Agent.Op value reason body → Type
@Agent.step : {value reason body : Type} → Agent.Agent value reason body →
  (op : Agent.Op value reason body) → Agent.Agent value reason body × Agent.Op.Answer op
@Agent.WF : {value reason body : Type} → Agent.Agent value reason body → Prop
@Agent.WF.empty : ∀ {value reason body : Type}, Agent.WF Agent.empty
@Agent.WF.get_lt : ∀ {value reason body : Type} {a : Agent.Agent value reason body},
  Agent.WF a → ∀ {p : Nat} {s : Promise.State value reason},
    Promise.Table.get (Agent.Agent.table a) p = some s →
      p < Promise.Table.next (Agent.Agent.table a)
@Agent.WF.markHandled : ∀ {value reason body : Type} {a : Agent.Agent value reason body},
  Agent.WF a → ∀ (p : Nat), Agent.WF (Agent.markHandled a p)
@Agent.WF.newPromise : ∀ {value reason body : Type} {a : Agent.Agent value reason body},
  Agent.WF a → Agent.WF (Prod.fst (Agent.newPromise a))
@Agent.markHandled_get : ∀ {value reason : Type} (t : Promise.Table value reason) (p q : Nat),
  Promise.Table.get (Promise.Table.markHandled t p) q = Promise.Table.get t q
@Agent.settleAndTrigger_table : ∀ {value reason body : Type} (t : Promise.Table value reason)
  (rs : Promise.Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
  (id : Nat) (result : Except reason value),
  Prod.fst (Promise.Table.settleAndTrigger t rs q id result) = Promise.Table.settle t id result
@Agent.settle_ok_fulfillPromise : ∀ {value reason body : Type}
  (a : Agent.Agent value reason body) (promise : Nat) (v : value),
  (Agent.Agent.table (Agent.settle a promise (Except.ok v)),
      Agent.Agent.reactions (Agent.settle a promise (Except.ok v)),
      Agent.Agent.queue (Agent.settle a promise (Except.ok v))) =
    Promise.fulfillPromise (Agent.Agent.table a) (Agent.Agent.reactions a)
      (Agent.Agent.queue a) promise v
@Agent.newPromise_capability : ∀ {value reason body : Type} (a : Agent.Agent value reason body),
  Prod.snd (Agent.newPromise a) =
    Prod.snd (Promise.newPromiseCapability (Agent.Agent.table a) (Agent.Agent.nextFunction a))
@Agent.markHandled_table : ∀ {value reason body : Type} (a : Agent.Agent value reason body)
  (promise : Nat),
  Agent.Agent.table (Agent.markHandled a promise) =
    Promise.Table.markHandled (Agent.Agent.table a) promise
@Agent.startJob_agree : ∀ {value reason body : Type} (a : Agent.Agent value reason body)
  (job : Agent.Job value reason) (rest : List (Agent.Job value reason)),
  Agent.Agent.active a = Jobs.Active.checkpoint →
    Jobs.Queue.pending (Agent.Agent.queue a) = job :: rest →
      Jobs.startJob (Agent.Agent.active a) (Agent.Agent.queue a) (Jobs.ReactionJob.reaction job) =
        some (job, Agent.Agent.active (Prod.fst (Agent.startJob a)),
          Agent.Agent.queue (Prod.fst (Agent.startJob a)))
@Agent.startJob_running : ∀ {value reason body : Type} (a : Agent.Agent value reason body)
  (s : Nat), Agent.Agent.active a = Jobs.Active.job s → Agent.startJob a = (a, none)
@Agent.waitingOn_add_fulfill : ∀ {body : Type} (rs : Promise.Reactions body) (promise : Nat)
  (onFulfilled onRejected : Option body) (cap : Option Promise.Capability),
  Promise.Reactions.waitingOn (Prod.fst (Promise.Reactions.add rs promise onFulfilled onRejected cap))
      promise Promise.ReactionType.fulfill =
    Promise.Reactions.waitingOn rs promise Promise.ReactionType.fulfill ++
      [{ id := Promise.Reactions.next rs, promise := promise, kind := Promise.ReactionType.fulfill,
          handler := onFulfilled, capability := cap, phase := Promise.ReactionPhase.waiting }]
@Agent.react_resolve_enqueues : ∀ {value reason body : Type} (a : Agent.Agent value reason body)
  (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value),
  Promise.Table.get (Agent.Agent.table a) (Promise.Capability.promise cap) =
      some Promise.State.pending →
    Promise.Capability.promise cap ≠ Promise.Table.next (Agent.Agent.table a) →
      List.find? (fun g => Promise.ResolvingFunctions.resolve g == Promise.Capability.resolve cap)
            (Agent.Agent.functions a) = some f →
        Promise.ResolvingFunctions.alreadyResolved f = false →
          Promise.ResolvingFunctions.promise f = Promise.Capability.promise cap →
            Jobs.Queue.pending (Agent.Agent.queue
                (Agent.resolve (Prod.fst (Agent.perform a (Promise.Capability.promise cap)
                  (some h) none true)) cap v)) =
              Jobs.Queue.pending (Agent.Agent.queue a) ++
                (List.map (fun r => { reaction := Promise.Reaction.id r, argument := Except.ok v })
                    (Promise.Reactions.waitingOn (Agent.Agent.reactions a)
                      (Promise.Capability.promise cap) Promise.ReactionType.fulfill) ++
                  [{ reaction := Promise.Reactions.next (Agent.Agent.reactions a),
                     argument := Except.ok v }])
@Agent.react_resolve_enqueues_wf : the statement of react_resolve_enqueues with
  `Agent.WF a →` in place of the hypothesis `cap.promise ≠ table.next`
@Agent.react_resolve_enqueues_exactly : the statement of react_resolve_enqueues with the
  further hypothesis `Promise.Reactions.waitingOn (Agent.Agent.reactions a)
  (Promise.Capability.promise cap) Promise.ReactionType.fulfill = []` and the conclusion
  `… = Jobs.Queue.pending (Agent.Agent.queue a) ++ [{ reaction := Promise.Reactions.next
  (Agent.Agent.reactions a), argument := Except.ok v }]`
@Agent.resolve_table : ∀ {value reason body : Type} (a : Agent.Agent value reason body)
  (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value),
  Agent.WF a →
    List.find? (fun g => Promise.ResolvingFunctions.resolve g == Promise.Capability.resolve cap)
          (Agent.Agent.functions a) = some f →
      Promise.ResolvingFunctions.promise f = Promise.Capability.promise cap →
        Agent.Agent.table (Agent.resolve a cap v) =
          Promise.Table.settle (Agent.Agent.table a) (Promise.Capability.promise cap) (Except.ok v)
@Agent.finishJob_settles_capability : ∀ {value reason body : Type}
  (a : Agent.Agent value reason body) (job : Agent.Job value reason) (s : Nat)
  (r : Promise.Reaction body) (cap : Promise.Capability) (f : Promise.ResolvingFunctions)
  (decision : Except reason value),
  Agent.Agent.active a = Jobs.Active.job s → Agent.Agent.running a = some job →
    Agent.reactionOf a job = some r → Promise.Reaction.capability r = some cap →
      List.find? (fun g => Promise.ResolvingFunctions.resolve g == Promise.Capability.resolve cap)
            (Agent.Agent.functions a) = some f →
        Promise.ResolvingFunctions.alreadyResolved f = false →
          Promise.ResolvingFunctions.promise f = Promise.Capability.promise cap →
            Agent.Agent.table (Agent.finishJob a decision) =
                Promise.Table.settle (Agent.Agent.table a) (Promise.Capability.promise cap)
                  (Promise.reactionHandlerResult r (Jobs.ReactionJob.argument job) decision) ∧
              Agent.Agent.active (Agent.finishJob a decision) = Jobs.Active.checkpoint
@Agent.instDecidableEqExcept : {ε α : Type} → [DecidableEq ε] → [DecidableEq α] →
  DecidableEq (Except ε α)
Whatwg.Signatures.Ecma262.signature : Type → Type → Type → Effects.Signature
Whatwg.Signatures.Ecma262.handler : (value reason body : Type) →
  Effects.Handler (Whatwg.Signatures.Ecma262.signature value reason body)
    (StateT (Agent.Agent value reason body) Id)
@Whatwg.Signatures.Ecma262.handlerAt : {value reason body σ : Type} →
  (σ → Agent.Agent value reason body) → (Agent.Agent value reason body → σ → σ) →
    Effects.Handler (Whatwg.Signatures.Ecma262.signature value reason body) (StateT σ Id)
@Whatwg.Signatures.Ecma262.run : {value reason body α : Type} →
  Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α →
    Agent.Agent value reason body → α × Agent.Agent value reason body
@Whatwg.Signatures.Ecma262.handler_handle : ∀ {value reason body : Type}
  (op : Agent.Op value reason body) (a : Agent.Agent value reason body),
  StateT.run (Effects.Handler.handle (Whatwg.Signatures.Ecma262.handler value reason body) op) a =
    (Prod.snd (Agent.step a op), Prod.fst (Agent.step a op))
@Whatwg.Signatures.Ecma262.handlerAt_id : ∀ {value reason body : Type},
  (Whatwg.Signatures.Ecma262.handlerAt (fun a => a) fun a x => a) =
    Whatwg.Signatures.Ecma262.handler value reason body
@Whatwg.Signatures.Ecma262.interpret_eq_run : ∀ {value reason body α : Type}
  (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α)
  (a : Agent.Agent value reason body),
  StateT.run (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body) p) a =
    Whatwg.Signatures.Ecma262.run p a
@Whatwg.Signatures.Ecma262.interpret_handlerAt : ∀ {value reason body σ α : Type}
  (view : σ → Agent.Agent value reason body) (update : Agent.Agent value reason body → σ → σ),
  (∀ (a : Agent.Agent value reason body) (s : σ), view (update a s) = a) →
    ∀ (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α) (s : σ),
      Prod.fst (StateT.run (Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p) s) =
          Prod.fst (Whatwg.Signatures.Ecma262.run p (view s)) ∧
        view (Prod.snd (StateT.run
            (Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p) s)) =
          Prod.snd (Whatwg.Signatures.Ecma262.run p (view s))
@Whatwg.Signatures.Ecma262.interpret_perform_step : ∀ {value reason body : Type}
  (op : Agent.Op value reason body) (a : Agent.Agent value reason body),
  StateT.run (Effects.interpret (Whatwg.Signatures.Ecma262.handler value reason body)
      (Effects.Program.perform op)) a =
    (Prod.snd (Agent.step a op), Prod.fst (Agent.step a op))
@Whatwg.Signatures.Ecma262.resolvedWith : {value reason body : Type} →
  value → Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) Promise.Capability
@Whatwg.Signatures.Ecma262.run_resolvedWith : ∀ {value reason body : Type} (v : value)
  (a : Agent.Agent value reason body),
  Whatwg.Signatures.Ecma262.run (Whatwg.Signatures.Ecma262.resolvedWith v) a =
    (Prod.snd (Agent.newPromise a),
      Agent.resolve (Prod.fst (Agent.newPromise a)) (Prod.snd (Agent.newPromise a)) v)
@Whatwg.Signatures.Ecma262.sumHandler : {value reason body σ : Type} → {T : Effects.Signature} →
  (σ → Agent.Agent value reason body) → (Agent.Agent value reason body → σ → σ) →
    Effects.Handler T (StateT σ Id) →
      Effects.Handler (Whatwg.Signatures.Ecma262.signature value reason body ⊕ₛ T) (StateT σ Id)
@Whatwg.Signatures.Ecma262.interpret_sumHandler_inl : ∀ {value reason body σ α : Type}
  {T : Effects.Signature} (view : σ → Agent.Agent value reason body)
  (update : Agent.Agent value reason body → σ → σ) (other : Effects.Handler T (StateT σ Id))
  (p : Effects.Program (Whatwg.Signatures.Ecma262.signature value reason body) α),
  Effects.interpret (Whatwg.Signatures.Ecma262.sumHandler view update other)
      (Effects.Program.inl p) =
    Effects.interpret (Whatwg.Signatures.Ecma262.handlerAt view update) p
@Whatwg.WebIdl.Agent.newPromise : {value reason body : Type} →
  Agent.Agent value reason body → Agent.Agent value reason body × Promise.Capability
@Whatwg.WebIdl.Agent.resolve : {value reason body : Type} →
  Agent.Agent value reason body → Promise.Capability → value → Agent.Agent value reason body
@Whatwg.WebIdl.Agent.reject : {value reason body : Type} →
  Agent.Agent value reason body → Promise.Capability → reason → Agent.Agent value reason body
@Whatwg.WebIdl.Agent.react : {value reason body : Type} → Agent.Agent value reason body →
  Promise.Capability → Option body → Option body →
  Agent.Agent value reason body × Option (Option Promise.Capability)
@Whatwg.WebIdl.Agent.resolvedWith : {value reason body : Type} →
  Agent.Agent value reason body → value → Agent.Agent value reason body × Promise.Capability
@Whatwg.WebIdl.Agent.resolve_view : ∀ {value reason body : Type}
  (a : Agent.Agent value reason body) (p : Promise.Capability) (f : Promise.ResolvingFunctions)
  (v : value), Agent.WF a →
    List.find? (fun g => Promise.ResolvingFunctions.resolve g == Promise.Capability.resolve p)
          (Agent.Agent.functions a) = some f →
      Promise.ResolvingFunctions.promise f = Promise.Capability.promise p →
        Agent.Agent.table (Whatwg.WebIdl.Agent.resolve a p v) =
          Whatwg.WebIdl.Promise.resolve (Agent.Agent.table a) (Promise.Capability.promise p) v
@Whatwg.WebIdl.Agent.react_resolve : the statement of Agent.react_resolve_enqueues_wf with
  `Whatwg.WebIdl.Agent.resolve` and `Whatwg.WebIdl.Agent.react a p (some h) none` in place
  of `Agent.resolve` and `Agent.perform a p.promise (some h) none true`
```

The three statements abbreviated in prose were printed in full and differ
from the shown statement only as described. Line breaks were re-wrapped;
no token changed.

## 4. Effect on frozen surfaces

| Surface | Count | Breaker amendment? |
| --- | --- | --- |
| frozen `#check` ascriptions altered | 0; every declaration is new | no |
| frozen batteries edited | 0 | no |
| landed definitions or statements edited | 0 | no |
| landed types gaining global instances | 4: `DecidableEq (Reaction body)` conditional, `DecidableEq` and `Repr (Reactions body)`, `Repr ResolvingFunctions`, `Repr Jobs.Active`. The only ascriptions about them are positive (`inferInstance : Repr (Reaction Nat)`, `DecidableEq ResolvingFunctions`, `DecidableEq Jobs.Active`) and stay true; the full build with the four instances passed every frozen battery `[C]` | no; decision 2 |
| inventory and register sentences contradicted | 2: the `E-29` risk cell of `docs/PROMISE-EXTRACTION-INVENTORY.md` ("must not gain one silently") and the `WS-PROM-CE-015` row ("`DecidableEq` is derived unconditionally …"). Conditional is not unconditional, but the row's intent is the `E-29` sentence | a ruling (decision 2), recorded as the register row's disposition at landing |
| production docstrings that become stale | 4: `Promise.Reaction` ("must not gain `DecidableEq`"), `Promise.Capability` ("`Reaction` still gains none"), `WebIdl.Promise.resolve`, `WebIdl.Promise.reject` | no; the builder amends them |
| root docstrings | `Whatwg/Ecma262.lean`, `Whatwg/WebIdl.lean`, `Whatwg.lean` gain one module line each | no |
| Q4 configuration | unchanged | no; W8 |
| graph documents | `docs/PROMISE-DAG.md`: the semantics ground (D46, `G-08` remainder) and the counterexamples ground (`WS-PROM-CE-026`, via D17) gain a pointer to `PROMISE-PG-AGENT` at landing | coordinator |

## 5. Effect on the trust gate, the strict ceiling and the Lake libraries

- Strict ceiling. The new modules under `Whatwg.Ecma262` and `Whatwg.WebIdl`
  are bound by it and pass (0 of 298). `Whatwg.Signatures` joins the strict
  list at zero residue (0 of 17). Measured with the full gate. `[C]`
- Dependency axioms. Every `effects` constant the face reaches is inside
  `propext` and `Quot.sound`, and so is the whole package. lean4-effect4's
  gate, which follows axioms into providers, therefore accepts a citation of
  any prototype declaration. `[C]` for the axiom sets; `[H]` that its gate
  was run.
- Object level (R-V10). No new metaprogramming module, no `syntax`, `macro`,
  `elab`, `#eval` or `run_cmd` under `Whatwg/`. `deriving instance`, `scoped
  instance` and `nomatch` are accepted. R-W1(c) and (d) hold with no
  addendum. `[C]`
- Token hygiene (V2c rule 2). Importing `Effects.Algebra.Sum` puts the
  package's one token, `⊕ₛ` (`Effects.Algebra.Signature`), in the final
  token table. Rule 2 accepts it. `[C]` grep finds no other `syntax`,
  `notation`, `infix`, `macro` or `elab` in `effects`.
- Module closure (V2c rule 5). The face must be reachable from the audit
  root. The umbrella import does that. `[C]`
- Kernel replay. `leanchecker` on the three prototype modules exits 0. `[C]`
- Libraries:
  - `WhatwgEcma262` grows from 5 to 6 jobs and `WhatwgWebIdl` gains one
    module. `[C]`
  - `WhatwgSignatures` is new (14 jobs), joins `defaultTargets`, and is the
    only library that builds `Effects`. `[C]`
  - The CI `leanchecker` step over `Whatwg` covers it by prefix. `[H]`
- Gate summary line. It will read 6 module prefixes.

## 6. Slices

### 6.1 Phase and graph (question g)

Recommendation: a promise slice of its own, Q5, landed before P8 proper. P8
is "configuration and WPT replay". It needs this record as its promise and
job substrate and adds the masks as projections, the bounded runner and the
harness. Making W9 P8's first packet would tie a self-contained library
change to P8's WPT gates.

Graph: a new `PROMISE-PG-AGENT` in a new `docs/PROMISE-AGENT-DAG.md`, opening
with an R-V4 current-state table. Its bridges edge names `PROMISE-PG-FIRST`.
At landing, `PROMISE-PG-FIRST`'s semantics and counterexamples grounds cite
it. If W7's ledger lands first, the graph is born there.

### 6.2 Breaker packet

- Contract: `test/contracts/promise-agent-q5.contract.md`. It freezes:
  - the declaration record of 3.6 and the fourteen `WF` clauses;
  - the alphabet and answers of 3.2;
  - the D46 law, the view laws, the lens and sum laws;
  - the masks of each law;
  - decision 2's instance set.
- Batteries, declared red in `test/fixtures/trust-gate/known-red.txt`:
  - `WhatwgTest/Ecma262/AgentContract.lean` (signature ascriptions,
    instance ascriptions);
  - `WhatwgTest/Ecma262/AgentLaws.lean` (law statements);
  - `WhatwgTest/Ecma262/AgentAxiomReport.lean`;
  - `WhatwgTest/WebIdl/AgentContract.lean`;
  - `WhatwgTest/Signatures/Ecma262Contract.lean`. This one includes a toy
    second signature summed with the agent into `StateT (Agent × Nat) Id`,
    the shape lean4-effect4 would write.
- Counterexample rows, registered before any implementation:

| Id | Attack | Discriminating statement |
| --- | --- | --- |
| `WS-PROM-CE-040` | `react` then store-level `resolve` enqueues nothing (D46) | finite witness of 3.3; `react_resolve_enqueues_exactly` |
| `WS-PROM-CE-041` | a forged capability (functions never stored) settles the promise, as a fallback to `Table.settle` would | `resolve` through it leaves the agent unchanged |
| `WS-PROM-CE-042` | a per-function one-shot marker: `reject` after `resolve` still settles | agent `resolve` then `reject` is inert |
| `WS-PROM-CE-043` | duplicate identifiers through the public `Table.mk` | `¬ WF` on `Table.mk [(0, c), (0, c')] 1` |
| `WS-PROM-CE-044` | `finishJob` with `[[Capability]]` *undefined* settles something (D18) | the table is unchanged and the agent is at a checkpoint |
| `WS-PROM-CE-045` | `startJob` ignores the activation (run to completion) | `startJob_running` |
| `WS-PROM-CE-046` | a separate job-serial supply (the `WS-PROM-CE-039` shape) | `startJob` sets `Active.job j.reaction`, which `triggerReactions`' `.queued r.id` names |
| `WS-PROM-CE-047` | a lens without `view (update a s) = a`, or a handler that steps twice | `interpret_handlerAt`'s hypothesis is necessary (witness); `interpret_eq_run` refutes the double step |

### 6.3 Builder slices

| Slice | Fence | Depends on | Size |
| --- | --- | --- | --- |
| B1 record, operations, step, views, D46 | `Whatwg/Ecma262/Agent.lean`; the import and docstring of `Whatwg/Ecma262.lean`; the two `Promise.Reaction`/`Capability` docstrings in `Whatwg/Ecma262/Promise.lean` | breaker packet | about 500 lines; the prototype has 360 |
| B2 invariant and lifted laws | `Whatwg/Ecma262/AgentLaws.lean` (new module, so B3 and B4 do not wait) | B1 | 900 to 1,200 lines `[H]`, from the measured `WF.settle` |
| B3 Web IDL verbs | `Whatwg/WebIdl/Agent.lean`; `Whatwg/WebIdl.lean`; two docstrings in `Whatwg/WebIdl/Promise.lean` | B1 | about 200 lines |
| B4 face | `Whatwg/Signatures.lean`, `Whatwg/Signatures/Ecma262.lean`; one `[[lean_lib]]` block and `defaultTargets` in `lakefile.toml`; one import in `Whatwg.lean`. The `strictCeilingPrefixes` entry is applied by the coordinator, as R-V7 did for the word list | B1 | about 200 lines |

Order: B1, then B2, B3 and B4 in parallel worktrees.

### 6.4 What the independent reviewer checks

- Fidelity per operation, against the sealed bytes: `op.fulfillpromise`,
  `op.rejectpromise`, `op.triggerpromisereactions`, `op.performpromisethen`,
  `op.newpromisereactionjob`, `op.createresolvingfunctions` and the Web IDL
  `op.resolve`, `op.reject`, `react`. Every departure is named, especially
  the non-thenable restriction, `held` never shrinking, and phases not
  advanced past `.queued` by `finishJob`.
- That each view theorem's right side is the landed operation, not a copy.
- That `react_resolve_enqueues` is not vacuous: `WS-PROM-CE-040`'s witness
  satisfies its hypotheses.
- That `WF.empty` holds, and that a reachable agent after a few operations
  is `WF`.
- That the face handler is exactly `step`, with no hidden state.
- That masks are labelled by the §7 rule.
- The axiom report, and the gate line with six prefixes.
- That no frozen ascription changed (statement fingerprint against the
  base).

### 6.5 Dependencies on W6, W7, W8 and W10

- W6:
  - masks as data: section 3.4's naming rule;
  - the declaration snapshot (D47): Q5's declarations can land with prose
    records and join the snapshot when it exists.
- W7: the graph format (6.1).
- W8: R-W1(e) makes W8's store unification target this record. Three
  points.
  - If W8's transition kernel is a generic `(state, op, answer, step)`
    structure, the face's contents generalize mechanically: `signature`,
    `handler`, `handlerAt`, `run` and the agreement laws are
    parametric in it. W8 should own that generic part in
    `Whatwg.Signatures.Kernel`, with the agent as its first instance. If
    W8 lands later, B4 lands the instance and W8 generalizes by "move".
  - The one-table cutover: Q4's `Config` holds an `Agent`. Its tokens
    (`startup`, `sink`, `observer`) become reactions whose handler is a
    Streams descriptor (`body := ` a Streams job kind). The heterogeneous
    token queue becomes the agent's queue, and the `phaseErase`
    workaround of Q4 amendment A4 disappears, because the job serial is
    the reaction identity.
  - What W8 needs from W9: the record, `step`, `WF`, that queue convention,
    and decision 6.
- W10:
  - the lean4-effect4 handoff (DI-30's re-ruling, DI-90's hazard) is
    cross-repository and the operator's;
  - the shared gate package should carry the strict-ceiling rule that
    `Whatwg.Signatures` joins.

### 6.6 Streams provider (question h)

lean4-effect4's stream kernel is unchanged at `efcf1ae2`: `openRow` (request
`.nat`, answer `.handle`), `pullRow` (answer `.option (.list elem)`, kind
`.async`) and `closeRow`. `[C]` A `Whatwg.Signatures.Streams` face would
have operations `getReader`, `read` and `cancel` or `releaseLock` over the
Readable configuration with the agent beneath it.

`read` answers a promise capability; the chunk arrives when its reaction
runs. The bridge to `pullRow` pairs one async `pull` with one `read` plus
the settlement of its promise. It answers `some [chunk]` or `none` at done,
under DB-04 M1.

That needs a Readable step function P8 has not built (Q4's configuration is
writable-only). So it belongs to P12 (bridges), after P8. Not this slice,
and not P8. W9's face is the template.

## 7. Decisions for the coordinator

1. **Phase.**
   - (a) Q5 promise slice before P8, own graph — recommended; cost: one more
     graph document.
   - (b) P8's first packet; cost: tied to P8's WPT gates.
   - (c) Folded into W8; cost: W8's kernel and this record freeze together,
     a larger packet.
2. **Instances on landed types.**
   - (a) Recommended: global conditional `DecidableEq` for `Reaction` and
     `Reactions`, global `Repr` for `Reactions`, `ResolvingFunctions` and
     `Active`, and a scoped `DecidableEq (Except ε α)`. Cost: a ruling
     superseding `E-29`'s "must not gain one silently" and re-dispositioning
     `WS-PROM-CE-015`.
   - (b) Everything scoped and hand-written; cost: about 60 lines of
     decision procedures, and no `DecidableEq` for consumers who do not
     open the scope.
   - (c) No `DecidableEq` on `Agent`; cost: no `decide` probes over agents,
     and lean4-effect4 compares agents propositionally only.
3. **Face placement.**
   - (a) `Whatwg.Signatures.*`, library `WhatwgSignatures`, strict prefix —
     recommended; cost: one library and one prefix.
   - (b) Inside `Whatwg.Ecma262`; cost: every data-model consumer builds
     `Effects`, and DI-90 bites.
   - (c) No face here; lean4-effect4 writes the 120 lines itself. Cost: RS-3
     is unmet here, and the laws are proved there instead.
4. **Graph.**
   - (a) New `PROMISE-PG-AGENT` document — recommended.
   - (b) A Q5 section of `docs/PROMISE-DAG.md` on `PROMISE-PG-FIRST`; cost:
     one table carries two packets' edges.
5. **Cursors.**
   - (a) Three cursors, ordered by `WF`; job serial is the reaction id —
     recommended.
   - (b) One supply; cost: no landed allocation stays an exact view.
6. **Queue payload.**
   - (a) Fixed at `Jobs.ReactionJob (Except reason value)`; Streams tokens
     become reactions with a `body` descriptor — recommended.
   - (b) An `Agent` parametrized by payload; cost: every view theorem needs a
     projection, and the landed operations no longer type-check against it.
7. **Universes.**
   - (a) Stay at `Type` — recommended; lean4-effect4 uses `.{0, 0}`.
   - (b) Generalize; cost: edits to frozen definitions, which R-W1(b)
     disfavours, for no present consumer.
8. **Mask names.**
   - (a) DB-04 masks never named `m1` or `m2` in Lean; W6 names them by
     meaning — recommended.
   - (b) Rename DB-04's masks to match `Effects`; cost: rewrites every
     docstring's mask label.
9. **`resolvedSettled` and thenables.**
   - (a) Accept the clause with a recorded `G-05` obligation to weaken it —
     recommended.
   - (b) Model "resolved but pending" now; cost: `G-04` and `G-05` enter
     this slice.
10. **lean4-effect4 handoff.** Forward to the operator that DI-30's ground
    is discharged here, and that DI-90's in-tree `Effects` would collide
    with this package's `effects` require (W10).
    - (a) Forward with W10 — recommended.
    - (b) Wait for a lean4-effect4 request.

## 8. Not checked

- No breaker or builder work. That `perform`, `callFunctions`, `startJob`,
  `finishJob` and the script operations keep `WF`, and the seven further
  clauses with their lemmas, are estimates `[H]`; `settle`, `newPromise`
  and `markHandled` were proved for the seven prototype clauses.
- No statement compared step by step against the sealed `spec.html` and
  `index.bs` beyond the anchors the landed docstrings already carry. The
  coverage candidates of 3.2 are `[H]`.
- lean4-effect4: read at one commit through one research seat and the greps
  of 2.2. No Lean file there was built, and its gate was not run against a
  `whatwg` import. Lake's behaviour with two packages providing `Effects.*`
  (DI-90) is `[H]`.
- The mask relation sentence of 3.4 is `[H]`.
- `lake exe whatwg_trustselftest`, `whatwg_vendorseal` and the full CI
  `leanchecker` step were not run with the prototypes. `lake build`, which
  runs the axiom gate, was.
- The review's counts of `private` declarations and theorems were not
  re-measured.

## Appendix A. Prototype listings

Each file elaborated as listed, under the `lake build` of section 2.1, and
was removed afterwards. They are design evidence, not a builder's starting
point that a breaker is bound by.

### A.1 `Whatwg/Ecma262/Agent.lean`

```lean
import Whatwg.Ecma262.Promise

/-!
# W9 prototype: the ECMAScript agent record and its one step function

Prototype of the W9 design seat (`docs/research/2026-10-01-w9-agent-effects-design.md`).
Uncommitted; not a landed declaration.
-/

namespace Whatwg.Ecma262.Agent

open Whatwg.Ecma262

/-! ## Instances the landed carriers lack (decision D-2 of the design) -/

/-- Core `Except` has no `DecidableEq` at this toolchain, and Batteries
derives one globally (`Batteries.Lean.Except`). This one is scoped, so a
consumer that imports both meets no second global instance. -/
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

/-- The job payload the landed operations already write. -/
abbrev Job (value reason : Type) : Type := Jobs.ReactionJob (Except reason value)

/-- The agent: the three landed stores, contained, not replaced; the
resolving-function store that holds each capability's one-shot marker; the
reaction records a settled `PerformPromiseThen` branch minted and handed to
its caller (`held`); the activation with the job it is evaluating; and the
settlement order. Three cursors: `table.next`, `reactions.next`,
`nextFunction`. A job's serial is its reaction identity. -/
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

/-! ## Operations -/

/-- `op.newpromisecapability` restricted to `%Promise%`, with the resolving
functions stored so that their one-shot marker is agent state. -/
def newPromise {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body × Promise.Capability :=
  ({ a with
      table := (Promise.newPromiseCapability a.table a.nextFunction).1,
      functions := a.functions ++
        [Promise.createResolvingFunctions a.table.next a.nextFunction],
      nextFunction := a.nextFunction + 2 },
    (Promise.newPromiseCapability a.table a.nextFunction).2)

/-- `op.fulfillpromise` / `op.rejectpromise` with `op.triggerpromisereactions`,
and the settlement recorded in order. -/
def settle {value reason body : Type} (a : Agent value reason body) (promise : Nat)
    (result : Except reason value) : Agent value reason body :=
  { a with
    table := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).1,
    reactions := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.1,
    queue := (Promise.Table.settleAndTrigger a.table a.reactions a.queue promise result).2.2,
    settlements := (Promise.Table.settleTraced a.table a.settlements promise result).2 }

/-- Call a stored resolving function selected by `pick`: one-shot through the
shared marker, then settle-and-trigger. An unknown function is inert. -/
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

/-- `Call(cap.[[Resolve]], undefined, « v »)` on the non-thenable branch
(`G-04`, `G-05` stay out): what Web IDL "resolve" performs. -/
def resolve {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (v : value) : Agent value reason body :=
  callFunctions a (fun f => f.resolve == cap.resolve) (Except.ok v)

/-- `Call(cap.[[Reject]], undefined, « r »)`: what Web IDL "reject" performs. -/
def reject {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (r : reason) : Agent value reason body :=
  callFunctions a (fun f => f.reject == cap.reject) (Except.error r)

/-- Web IDL "react" step 6: mint the result capability when `derive` is set. -/
def mintFor {value reason body : Type} (a : Agent value reason body) :
    Bool → Agent value reason body × Option Promise.Capability
  | true => ((newPromise a).1, some (newPromise a).2)
  | false => (a, none)

/-- `op.performpromisethen`, with the result capability minted first when
`derive` is set (Web IDL "react" steps 6 and 7). A missing promise answers
`none` and leaves the agent unchanged (`E-31`'s `Option`). -/
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

/-- `op.mark-a-promise-as-handled`. -/
def markHandled {value reason body : Type} (a : Agent value reason body) (promise : Nat) :
    Agent value reason body :=
  { a with table := Promise.Table.markHandled a.table promise }

/-- The reaction record a job was built from: a held record first, otherwise
the registered one in the list its argument's tag selects. -/
def reactionOf {value reason body : Type} (a : Agent value reason body)
    (job : Job value reason) : Option (Promise.Reaction body) :=
  match a.held.find? (fun r => r.id == job.reaction) with
  | some r => some r
  | none =>
      Promise.Reactions.get a.reactions
        (match job.argument with
          | .ok _ => Promise.ReactionType.fulfill
          | .error _ => Promise.ReactionType.reject) job.reaction

/-- `requirement.jobs.1`, `.2`: at a checkpoint, start the oldest job. The
answer names the job and its handler descriptor so the host can answer it. -/
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

/-- `op.newpromisereactionjob` steps 4 to 9 and `requirement.jobs.3`: the
handler's completion arrives as the host's decision; the derived capability is
settled through its stored resolving functions; the agent returns to a
checkpoint. Inert when no job is running. -/
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

/-- Script evaluation returns: the stack is empty again. -/
def leaveScript {value reason body : Type} (a : Agent value reason body) :
    Agent value reason body :=
  match a.active with
  | .script => { a with active := Jobs.Active.checkpoint }
  | _ => a

/-! ## The operation alphabet and the step function -/

/-- First-order operations. Every argument is data; no Lean function. -/
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

/-- The answer each operation returns to its caller. -/
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

/-! ## Views onto the landed store-level operations -/

/-- The table component of settle-and-trigger is `Table.settle`, on both branches. -/
theorem settleAndTrigger_table {value reason body : Type} (t : Promise.Table value reason)
    (rs : Promise.Reactions body)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) (id : Nat)
    (result : Except reason value) :
    (Promise.Table.settleAndTrigger t rs q id result).1 = Promise.Table.settle t id result := by
  unfold Promise.Table.settleAndTrigger Promise.Table.settle
  cases Promise.Table.isPending t id <;> rfl

/-- `settle` is `fulfillPromise` on its three stores. -/
theorem settle_ok_fulfillPromise {value reason body : Type} (a : Agent value reason body)
    (promise : Nat) (v : value) :
    ((settle a promise (Except.ok v)).table, (settle a promise (Except.ok v)).reactions,
        (settle a promise (Except.ok v)).queue) =
      Promise.fulfillPromise a.table a.reactions a.queue promise v := rfl

/-- `newPromise` is `WebIdl`-free `newPromiseCapability` at the function cursor. -/
theorem newPromise_capability {value reason body : Type} (a : Agent value reason body) :
    (newPromise a).2 = (Promise.newPromiseCapability a.table a.nextFunction).2 := rfl

/-- `markHandled` is `Table.markHandled`. -/
theorem markHandled_table {value reason body : Type} (a : Agent value reason body)
    (promise : Nat) : (markHandled a promise).table = Promise.Table.markHandled a.table promise :=
  rfl

/-- `startJob` agrees with the landed `Jobs.startJob` at the job's own serial. -/
theorem startJob_agree {value reason body : Type} (a : Agent value reason body)
    (job : Job value reason) (rest : List (Job value reason)) :
    a.active = Jobs.Active.checkpoint → a.queue.pending = job :: rest →
      Jobs.startJob a.active a.queue job.reaction =
        some (job, (startJob a).1.active, (startJob a).1.queue) := by
  intro hact hq
  unfold startJob Jobs.startJob Jobs.Queue.dequeue
  rw [hact, hq]
  rfl

/-! ## D46: `react` followed by `resolve` enqueues the reaction's job -/

/-- The waiting set after a registration is the old one with the new entry last. -/
theorem waitingOn_add_fulfill {body : Type} (rs : Promise.Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (cap : Option Promise.Capability) :
    Promise.Reactions.waitingOn (Promise.Reactions.add rs promise onFulfilled onRejected cap).1
        promise Promise.ReactionType.fulfill =
      Promise.Reactions.waitingOn rs promise Promise.ReactionType.fulfill ++
        [Promise.Reaction.mk rs.next promise Promise.ReactionType.fulfill onFulfilled cap
          Promise.ReactionPhase.waiting] := by
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

/-- **D46.** Web IDL "react" (with its derived capability) followed by
"resolve" on a pending promise whose resolving functions have not fired
enqueues, behind every job already queued, the jobs of the reactions already
waiting on that promise in registration order and then exactly the new
reaction's job. Mask M2: the statement observes queue order. -/
theorem react_resolve_enqueues {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value)
    (hp : a.table.get cap.promise = some Promise.State.pending)
    (hne : cap.promise ≠ a.table.next)
    (hf : a.functions.find? (fun g => g.resolve == cap.resolve) = some f)
    (hfr : f.alreadyResolved = false) (hfp : f.promise = cap.promise) :
    (resolve (perform a cap.promise (some h) none true).1 cap v).queue.pending =
      a.queue.pending ++
        ((Promise.Reactions.waitingOn a.reactions cap.promise Promise.ReactionType.fulfill).map
          (fun r => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
        [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) := by
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

/-- The FIFO-position corollary: with nothing yet waiting on the promise, the
queue gains exactly the new reaction's job, at its tail. Mask M2. -/
theorem react_resolve_enqueues_exactly {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value)
    (hp : a.table.get cap.promise = some Promise.State.pending)
    (hne : cap.promise ≠ a.table.next)
    (hf : a.functions.find? (fun g => g.resolve == cap.resolve) = some f)
    (hfr : f.alreadyResolved = false) (hfp : f.promise = cap.promise)
    (hnone : Promise.Reactions.waitingOn a.reactions cap.promise Promise.ReactionType.fulfill = []) :
    (resolve (perform a cap.promise (some h) none true).1 cap v).queue.pending =
      a.queue.pending ++ [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)] := by
  rw [react_resolve_enqueues a cap f h v hp hne hf hfr hfp, hnone]
  rfl

/-! ## Well-formedness -/

/-- The agent's invariant: identities unique and below their cursors, every
stored reference allocated, and resolved functions only on settled promises
(which holds while thenable adoption, `G-05`, stays out). -/
structure WF {value reason body : Type} (a : Agent value reason body) : Prop where
  tableNodup : (a.table.entries.map Prod.fst).Nodup
  tableBelow : ∀ e ∈ a.table.entries, e.1 < a.table.next
  functionsBelow : ∀ f ∈ a.functions, f.reject = f.resolve + 1 ∧ f.reject < a.nextFunction
  functionsAllocated : ∀ f ∈ a.functions, f.promise < a.table.next
  resolvedSettled : ∀ f ∈ a.functions, f.alreadyResolved = true →
    Promise.Table.isPending a.table f.promise = false
  reactionsBelow : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
    r.id < a.reactions.next
  queueBelow : ∀ j ∈ a.queue.pending, j.reaction < a.reactions.next

/-- The empty agent is well formed. -/
theorem WF.empty {value reason body : Type} : WF (empty : Agent value reason body) where
  tableNodup := List.nodup_nil
  tableBelow := fun _ h => nomatch h
  functionsBelow := fun _ h => nomatch h
  functionsAllocated := fun _ h => nomatch h
  resolvedSettled := fun _ h => nomatch h
  reactionsBelow := fun _ h => nomatch h
  queueBelow := fun _ h => nomatch h

/-- An allocated identity is below the table cursor, so it is never the
identity the next allocation takes. -/
theorem WF.get_lt {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    {p : Nat} {s : Promise.State value reason} (h : Promise.Table.get a.table p = some s) :
    p < a.table.next := by
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

/-- Marking handled changes no promise state, at any identity. -/
theorem markHandled_get {value reason : Type} (t : Promise.Table value reason) (p q : Nat) :
    Promise.Table.get (Promise.Table.markHandled t p) q = Promise.Table.get t q := by
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

/-- `markHandled` keeps the invariant. -/
theorem WF.markHandled {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (p : Nat) : WF (markHandled a p) := by
  have hfst : ∀ (e : Nat × Promise.Cell value reason),
      (if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e).1 = e.1 := by
    intro e
    cases (e.1 == p) <;> rfl
  refine ⟨?_, ?_, hw.functionsBelow, hw.functionsAllocated, ?_, hw.reactionsBelow, hw.queueBelow⟩
  · show ((a.table.entries.map _).map Prod.fst).Nodup
    rw [List.map_map]
    have : (Prod.fst ∘ (fun (e : Nat × Promise.Cell value reason) =>
        if e.1 == p then (e.1, Promise.Cell.mk e.2.state true) else e)) = Prod.fst := by
      funext e
      exact hfst e
    rw [this]
    exact hw.tableNodup
  · intro e he
    obtain ⟨e0, he0, hg⟩ := List.mem_map.mp he
    show e.1 < a.table.next
    rw [← hg, hfst e0]
    exact hw.tableBelow e0 he0
  · intro f hf hres
    show Promise.Table.isPending (Promise.Table.markHandled a.table p) f.promise = false
    unfold Promise.Table.isPending
    rw [markHandled_get]
    exact hw.resolvedSettled f hf hres

/-- `newPromise` keeps the invariant: the fresh identity is the table cursor,
which no stored identity reaches, and the two function identities are the
function cursor and its successor. -/
theorem WF.newPromise {value reason body : Type} {a : Agent value reason body} (hw : WF a) :
    WF (newPromise a).1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hw.reactionsBelow, hw.queueBelow⟩
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
    show f.promise < a.table.next + 1
    rcases List.mem_append.mp hf with hold | hnew
    · exact Nat.lt_succ_of_lt (hw.functionsAllocated f hold)
    · rw [List.mem_singleton.mp hnew]
      exact Nat.lt_succ_self _
  · intro f hf hres
    rcases List.mem_append.mp hf with hold | hnew
    · show Promise.Table.isPending (Promise.Table.fresh a.table Promise.State.pending).1
        f.promise = false
      unfold Promise.Table.isPending Promise.Table.get
      rw [Promise.Table.fresh_old a.table _ f.promise
        (Nat.ne_of_lt (hw.functionsAllocated f hold))]
      exact hw.resolvedSettled f hold hres
    · rw [List.mem_singleton.mp hnew] at hres
      cases hres

/-! ## The stored functions settle what the store-level operations settle -/

/-- **The re-description of the frozen `WebIdl.Promise.resolve`.** For a
capability this agent minted, the agent's `resolve` changes the table exactly
as `Table.settle` does: when the functions have already fired, the
well-formedness clause says the promise is settled, and `Table.settle` is the
identity there too. Mask M1. -/
theorem resolve_table {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value) (hw : WF a)
    (hf : a.functions.find? (fun g => g.resolve == cap.resolve) = some f)
    (hfp : f.promise = cap.promise) :
    (resolve a cap v).table = Promise.Table.settle a.table cap.promise (Except.ok v) := by
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

/-- **D17 at the agent.** A finishing reaction job whose record carries a
capability settles that capability's promise through the functions this
agent stored for it, with the handler's result, and returns to a checkpoint.
Mask M1. -/
theorem finishJob_settles_capability {value reason body : Type} (a : Agent value reason body)
    (job : Job value reason) (s : Nat) (r : Promise.Reaction body) (cap : Promise.Capability)
    (f : Promise.ResolvingFunctions) (decision : Except reason value)
    (hact : a.active = Jobs.Active.job s) (hrun : a.running = some job)
    (hr : reactionOf a job = some r) (hcap : r.capability = some cap)
    (hf : a.functions.find? (fun g => g.resolve == cap.resolve) = some f)
    (hfr : f.alreadyResolved = false) (hfp : f.promise = cap.promise) :
    (finishJob a decision).table =
        Promise.Table.settle a.table cap.promise
          (Promise.reactionHandlerResult r job.argument decision) ∧
      (finishJob a decision).active = Jobs.Active.checkpoint := by
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

/-- **D46 under the invariant.** The freshness side condition of
`react_resolve_enqueues` is a consequence of `WF`. Mask M2. -/
theorem react_resolve_enqueues_wf {value reason body : Type} (a : Agent value reason body)
    (cap : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value)
    (hw : WF a) (hp : a.table.get cap.promise = some Promise.State.pending)
    (hf : a.functions.find? (fun g => g.resolve == cap.resolve) = some f)
    (hfr : f.alreadyResolved = false) (hfp : f.promise = cap.promise) :
    (resolve (perform a cap.promise (some h) none true).1 cap v).queue.pending =
      a.queue.pending ++
        ((Promise.Reactions.waitingOn a.reactions cap.promise Promise.ReactionType.fulfill).map
          (fun r => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
        [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) :=
  react_resolve_enqueues a cap f h v hp (Nat.ne_of_lt (hw.get_lt hp)) hf hfr hfp

/-- `requirement.jobs.3` at the agent: while a job is being evaluated no job
starts, whatever is queued. Mask M1. -/
theorem startJob_running {value reason body : Type} (a : Agent value reason body) (s : Nat) :
    a.active = Jobs.Active.job s → startJob a = (a, none) := by
  intro h
  unfold startJob
  rw [h]

end Whatwg.Ecma262.Agent
```

### A.2 `Whatwg/WebIdl/Agent.lean`

```lean
import Whatwg.Ecma262.Agent
import Whatwg.WebIdl.Promise

/-!
# W9 prototype: the Web IDL promise verbs over the agent

Prototype of the W9 design seat (`docs/research/2026-10-01-w9-agent-effects-design.md`).
Uncommitted; not a landed declaration. Every operation is a thin wrapper over
`Whatwg.Ecma262.Agent`; the landed `Whatwg.WebIdl.Promise` operations are
their store-level views.
-/

namespace Whatwg.WebIdl.Agent

open Whatwg.Ecma262

/-- `op.a-new-promise` (347604..347946): a capability, its functions stored. -/
def newPromise {value reason body : Type} (a : Ecma262.Agent.Agent value reason body) :
    Ecma262.Agent.Agent value reason body × Promise.Capability :=
  Ecma262.Agent.newPromise a

/-- `op.resolve` (349216..349783): `Call(p.[[Resolve]], « v »)`, which settles
and triggers reactions (D46). -/
def resolve {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (p : Promise.Capability) (v : value) : Ecma262.Agent.Agent value reason body :=
  Ecma262.Agent.resolve a p v

/-- `op.reject` (349785..350073). -/
def reject {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (p : Promise.Capability) (r : reason) : Ecma262.Agent.Agent value reason body :=
  Ecma262.Agent.reject a p r

/-- `op.dfn-perform-steps-once-promise-is-settled` (350075..352408) with its
step 6 capability: the derived promise exists and is returned. -/
def react {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (p : Promise.Capability) (onFulfilled onRejected : Option body) :
    Ecma262.Agent.Agent value reason body × Option (Option Promise.Capability) :=
  Ecma262.Agent.perform a p.promise onFulfilled onRejected true

/-- `op.a-promise-resolved-with` (347948..348631), non-thenable branch. -/
def resolvedWith {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (v : value) : Ecma262.Agent.Agent value reason body × Promise.Capability :=
  (resolve (newPromise a).1 (newPromise a).2 v, (newPromise a).2)

/-- **The frozen `resolve` is the table view of this one** for a capability
the agent minted. Mask M1. `E-20` (generalize), RESOLVE. -/
theorem resolve_view {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (p : Promise.Capability) (f : Promise.ResolvingFunctions) (v : value)
    (hw : Ecma262.Agent.WF a)
    (hf : a.functions.find? (fun g => g.resolve == p.resolve) = some f)
    (hfp : f.promise = p.promise) :
    (resolve a p v).table = Whatwg.WebIdl.Promise.resolve a.table p.promise v :=
  Ecma262.Agent.resolve_table a p f v hw hf hfp

/-- **D46 at the Web IDL surface.** `react` then `resolve` enqueues the new
reaction's job behind every job already queued and every reaction already
waiting. Mask M2. -/
theorem react_resolve {value reason body : Type} (a : Ecma262.Agent.Agent value reason body)
    (p : Promise.Capability) (f : Promise.ResolvingFunctions) (h : body) (v : value)
    (hw : Ecma262.Agent.WF a) (hp : a.table.get p.promise = some Promise.State.pending)
    (hf : a.functions.find? (fun g => g.resolve == p.resolve) = some f)
    (hfr : f.alreadyResolved = false) (hfp : f.promise = p.promise) :
    (resolve (react a p (some h) none).1 p v).queue.pending =
      a.queue.pending ++
        ((Promise.Reactions.waitingOn a.reactions p.promise Promise.ReactionType.fulfill).map
          (fun r => Jobs.ReactionJob.mk r.id (Except.ok v)) ++
        [Jobs.ReactionJob.mk a.reactions.next (Except.ok v)]) :=
  Ecma262.Agent.react_resolve_enqueues_wf a p f h v hw hp hf hfr hfp

end Whatwg.WebIdl.Agent
```

### A.3 `Whatwg/Signatures/Ecma262.lean` and its root `Whatwg/Signatures.lean`

```lean
import Effects.Algebra.Sum
import Whatwg.Ecma262.Agent

/-!
# W9 prototype: the `Effects.Signature` face of the ECMAScript agent

Prototype of the W9 design seat (`docs/research/2026-10-01-w9-agent-effects-design.md`).
Uncommitted; not a landed declaration. It imports `Effects.Algebra.Sum` (and through it `Signature`, `Program`,
`Handler`, `MonadLaws`, `Laws`) and nothing else from the `effects` package.
-/

namespace Whatwg.Signatures.Ecma262

open Whatwg.Ecma262

/-- The agent's operations as an `Effects` signature, both universes `0`, the
shape lean4-effect4's own signatures have. -/
abbrev signature (value reason body : Type) : Effects.Signature.{0, 0} :=
  ⟨Agent.Op value reason body, Agent.Op.Answer⟩

/-- The canonical handler: one `Agent.step` per operation, into the agent's
state monad. -/
def handler (value reason body : Type) :
    Effects.Handler (signature value reason body) (StateT (Agent.Agent value reason body) Id) :=
  ⟨fun op a => ((Agent.step a op).2, (Agent.step a op).1)⟩

/-- The same handler at any state that contains an agent, through a view and
an update: what a consumer sums with its own handler into its own state. -/
def handlerAt {value reason body σ : Type} (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ) :
    Effects.Handler (signature value reason body) (StateT σ Id) :=
  ⟨fun op s => ((Agent.step (view s) op).2, update (Agent.step (view s) op).1 s)⟩

/-- The step-fold a program denotes: perform each operation by `Agent.step`
and continue with its answer. -/
def run {value reason body α : Type} :
    Effects.Program (signature value reason body) α → Agent.Agent value reason body →
      α × Agent.Agent value reason body
  | .pure x, a => (x, a)
  | .vis op k, a => run (k (Agent.step a op).2) (Agent.step a op).1

/-- One operation through the canonical handler is one step. -/
theorem handler_handle {value reason body : Type} (op : Agent.Op value reason body)
    (a : Agent.Agent value reason body) :
    ((handler value reason body).handle op).run a = ((Agent.step a op).2, (Agent.step a op).1) :=
  rfl

/-- The canonical handler is the lens handler at the identity lens. -/
theorem handlerAt_id {value reason body : Type} :
    handlerAt (fun a => a) (fun a _ => a) = handler value reason body := rfl

/-- **Handler–step agreement.** Interpreting any program through the canonical
handler is the step-fold `run`. Every observation of the agent (its table,
reactions, queue, settlement trace) agrees, so this holds under DB-04's M2 for
the promise layer, whose observable is the agent itself. -/
theorem interpret_eq_run {value reason body α : Type}
    (p : Effects.Program (signature value reason body) α) (a : Agent.Agent value reason body) :
    (Effects.interpret (handler value reason body) p).run a = run p a := by
  induction p generalizing a with
  | pure x => rfl
  | vis op k ih => exact ih (Agent.step a op).2 (Agent.step a op).1

/-- **Lens agreement.** Under the view-update law, the lens handler runs the
same step-fold on the viewed agent, and the update writes back exactly the
agent the fold ends with. This is what lets lean4-effect4 sum this signature
with its own into one state. -/
theorem interpret_handlerAt {value reason body σ α : Type}
    (view : σ → Agent.Agent value reason body)
    (update : Agent.Agent value reason body → σ → σ)
    (law : ∀ a s, view (update a s) = a)
    (p : Effects.Program (signature value reason body) α) (s : σ) :
    ((Effects.interpret (handlerAt view update) p).run s).1 = (run p (view s)).1 ∧
      view ((Effects.interpret (handlerAt view update) p).run s).2 = (run p (view s)).2 := by
  induction p generalizing s with
  | pure x => exact ⟨rfl, rfl⟩
  | vis op k ih =>
      have h := ih (Agent.step (view s) op).2 (update (Agent.step (view s) op).1 s)
      rw [law] at h
      exact h

/-- Performing one operation through the handler, by the `Effects` law
`interpret_perform`. -/
theorem interpret_perform_step {value reason body : Type} (op : Agent.Op value reason body)
    (a : Agent.Agent value reason body) :
    (Effects.interpret (handler value reason body)
        (Effects.Program.perform (S := signature value reason body) op)).run a =
      ((Agent.step a op).2, (Agent.step a op).1) := by
  rw [Effects.interpret_perform]
  rfl

/-- Web IDL "a promise resolved with" as a two-operation program over the
signature: allocate, then resolve through the stored resolving functions. -/
def resolvedWith {value reason body : Type} (v : value) :
    Effects.Program (signature value reason body) Promise.Capability :=
  .vis Agent.Op.newPromise (fun cap =>
    .vis (Agent.Op.resolve cap v) (fun _ => .pure cap))

/-- The program's run is the two steps. -/
theorem run_resolvedWith {value reason body : Type} (v : value)
    (a : Agent.Agent value reason body) :
    run (resolvedWith (body := body) v) a =
      ((Agent.newPromise a).2,
        Agent.resolve (Agent.newPromise a).1 (Agent.newPromise a).2 v) := rfl

/-- The provider summed with a consumer's signature `T` into the consumer's
state, the shape of lean4-effect4's `RSig` and `rHandler`. -/
def sumHandler {value reason body σ : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body) (update : Agent.Agent value reason body → σ → σ)
    (other : Effects.Handler T (StateT σ Id)) :
    Effects.Handler (Effects.Signature.sum (signature value reason body) T) (StateT σ Id) :=
  Effects.Handler.sum (handlerAt view update) other

/-- A provider program injected into the sum is interpreted by the lens
handler alone (`Effects.interpret_inl`). -/
theorem interpret_sumHandler_inl {value reason body σ α : Type} {T : Effects.Signature.{0, 0}}
    (view : σ → Agent.Agent value reason body) (update : Agent.Agent value reason body → σ → σ)
    (other : Effects.Handler T (StateT σ Id))
    (p : Effects.Program (signature value reason body) α) :
    Effects.interpret (sumHandler view update other) (Effects.Program.inl (T := T) p) =
      Effects.interpret (handlerAt view update) p :=
  Effects.interpret_inl (handlerAt view update) other p
end Whatwg.Signatures.Ecma262
```

```lean
import Whatwg.Signatures.Ecma262

/-!
# Whatwg.Signatures

W9 prototype root; uncommitted.
-/
```

### A.4 Tracked files changed for the measurement run, then restored

```diff
diff --git a/Whatwg.lean b/Whatwg.lean
index 0916a66..636f9d5 100644
--- a/Whatwg.lean
+++ b/Whatwg.lean
@@ -4,6 +4,9 @@ import Whatwg.WebIdl
 import Whatwg.Streams
 import Whatwg.Html
 import Whatwg.Url
+import Whatwg.Ecma262.Agent
+import Whatwg.WebIdl.Agent
+import Whatwg.Signatures
 
 /-!
 # Whatwg
diff --git a/WhatwgTest/Audit/AxiomGate.lean b/WhatwgTest/Audit/AxiomGate.lean
index 039d4d3..df00c2d 100644
--- a/WhatwgTest/Audit/AxiomGate.lean
+++ b/WhatwgTest/Audit/AxiomGate.lean
@@ -184,6 +184,7 @@ private def strictCeilingPrefixes : List Name :=
   , `Whatwg.Url
   , `Whatwg.Infra.Text.Utf8
   , `Whatwg.Streams
+  , `Whatwg.Signatures
   ]
 
 /-- An exact admission of one declaration under the strict ceiling to
diff --git a/lakefile.toml b/lakefile.toml
index a6cdd36..c8f52a0 100644
--- a/lakefile.toml
+++ b/lakefile.toml
@@ -5,7 +5,7 @@ keywords = ["whatwg", "streams", "infra", "verified", "lean4"]
 license = "MIT"
 readmeFile = "README.md"
 defaultTargets = ["Whatwg", "WhatwgInfra", "WhatwgEcma262", "WhatwgWebIdl",
-                  "WhatwgUrl", "WhatwgHtml", "WhatwgStreams",
+                  "WhatwgUrl", "WhatwgHtml", "WhatwgStreams", "WhatwgSignatures",
                   "WhatwgGates", "WhatwgTest",
                   "whatwg_vendorseal", "whatwg_citations", "whatwg_census",
                   "whatwg_urlinventory", "whatwg_urlcensus"]
@@ -55,6 +55,11 @@ name = "WhatwgHtml"
 roots = ["Whatwg.Html"]
 globs = ["Whatwg.Html.*"]
 
+[[lean_lib]]
+name = "WhatwgSignatures"
+roots = ["Whatwg.Signatures"]
+globs = ["Whatwg.Signatures.*"]
+
 [[lean_lib]]
 name = "WhatwgStreams"
 roots = ["Whatwg.Streams"]
```

## Appendix B. Measurement scripts

Run from the worktree root with `lake env lean <file>` after building the
modules they import. They live in the seat's scratch directory, not in the
repository.

### B.1 `EffectsAxioms.lean`

```lean
import Lean
import Effects
import Effects.Experimental

open Lean Elab Command

/- Axioms reached by every constant whose defining module is under `Effects`,
grouped by the exact axiom set. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut choice : Array Name := #[]
  let mut other : Array (Name × Array Name) := #[]
  let mut perModule : Std.HashMap Name (Nat × Nat) := {}
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`Effects).isPrefixOf m then
        total := total + 1
        let axs ← liftCoreM (Lean.collectAxioms n)
        let (t, c) := perModule.getD m (0, 0)
        if axs.contains ``Classical.choice then
          choice := choice.push n
          perModule := perModule.insert m (t + 1, c + 1)
        else
          perModule := perModule.insert m (t + 1, c)
        let extra := axs.filter (fun a => a != ``propext && a != ``Quot.sound && a != ``Classical.choice)
        if !extra.isEmpty then other := other.push (n, extra)
  logInfo m!"Effects constants: {total}; reaching Classical.choice: {choice.size}; other axioms: {other.size}"
  for (m, (t, c)) in perModule.toList do
    logInfo m!"{m}: {t} constants, {c} reach Classical.choice"
  for n in choice do
    logInfo m!"choice: {n}"
  for (n, a) in other do
    logInfo m!"other: {n} {a}"

/- The constants the W9 face would cite, one by one. -/
#eval show CommandElabM Unit from do
  let names : List Name := [``Effects.Signature, ``Effects.Signature.sum, ``Effects.Program,
    ``Effects.Program.bind, ``Effects.Program.perform, ``Effects.Program.inl, ``Effects.Program.inr,
    ``Effects.Handler, ``Effects.Handler.sum, ``Effects.interpret, ``Effects.interpret_bind,
    ``Effects.interpret_perform, ``Effects.interpret_pure, ``Effects.interpret_vis,
    ``Effects.Handler.sum_handle_inl, ``Effects.Handler.sum_handle_inr,
    ``Effects.interpret_inl, ``Effects.interpret_inr,
    ``Effects.Family, ``Effects.Family.toSignature, ``Effects.Family.perform,
    ``Effects.Family.Service, ``Effects.Family.Service.toHandler,
    ``Effects.Family.Service.traced, ``Effects.Family.Service.interpret_traced_fst,
    ``Effects.Trace.Event, ``Effects.Trace.Mask, ``Effects.Trace.Mask.m1, ``Effects.Trace.Mask.m2,
    ``Effects.Trace.project, ``Effects.Trace.project_m2, ``Effects.Trace.agree_of_agree_m2,
    ``Effects.interpret_projects_fst, ``Effects.Handler.through, ``Effects.interpret_through,
    ``Effects.Signature.Hom, ``Effects.Handler.mapHom, ``Effects.interpret_mapHom,
    ``Effects.MonadHom.stateT]
  for n in names do
    if (← getEnv).contains n then
      let axs ← liftCoreM (Lean.collectAxioms n)
      logInfo m!"{n}: {axs}"
    else
      logInfo m!"{n}: NOT FOUND"
```

### B.2 `ModuleAxioms.lean` (final form; the face under its first name)

```lean
import Lean
import Whatwg.Ecma262.Agent
import Whatwg.Effects.Ecma262
import Whatwg.WebIdl.Agent

open Lean Elab Command

/- Every constant of the prototype modules: count, over-ceiling list, and the
axioms of each named (non-internal) declaration. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let targets : List Name := [`Whatwg.Ecma262.Agent, `Whatwg.Effects.Ecma262, `Whatwg.WebIdl.Agent]
  let mut total : Nat := 0
  let mut bad : Nat := 0
  let mut perModule : Std.HashMap Name Nat := {}
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if targets.contains m then
        total := total + 1
        perModule := perModule.insert m (perModule.getD m 0 + 1)
        let axs ← liftCoreM (Lean.collectAxioms n)
        let extra := axs.filter (fun a => a != ``propext && a != ``Quot.sound)
        if !extra.isEmpty then
          bad := bad + 1
          logInfo m!"OVER CEILING: {n} {axs}"
  logInfo m!"constants: {total}; over the strict ceiling: {bad}"
  for (m, k) in perModule.toList do
    logInfo m!"{m}: {k} constants"
  let names : List Name := [``Whatwg.Ecma262.Agent.Agent, ``Whatwg.Ecma262.Agent.step,
    ``Whatwg.Ecma262.Agent.WF, ``Whatwg.Ecma262.Agent.WF.empty, ``Whatwg.Ecma262.Agent.WF.get_lt,
    ``Whatwg.Ecma262.Agent.WF.markHandled, ``Whatwg.Ecma262.Agent.WF.newPromise,
    ``Whatwg.Ecma262.Agent.markHandled_get, ``Whatwg.Ecma262.Agent.resolve_table,
    ``Whatwg.Ecma262.Agent.finishJob_settles_capability,
    ``Whatwg.Ecma262.Agent.react_resolve_enqueues, ``Whatwg.Ecma262.Agent.react_resolve_enqueues_wf,
    ``Whatwg.Ecma262.Agent.react_resolve_enqueues_exactly, ``Whatwg.Ecma262.Agent.startJob_running,
    ``Whatwg.Ecma262.Agent.startJob_agree, ``Whatwg.Ecma262.Agent.settleAndTrigger_table,
    ``Whatwg.Ecma262.Agent.waitingOn_add_fulfill, ``Whatwg.Ecma262.Agent.settle_ok_fulfillPromise,
    ``Whatwg.Ecma262.Agent.instDecidableEqAgent, ``Whatwg.Ecma262.Agent.instReprAgent,
    ``Whatwg.Effects.Ecma262.signature, ``Whatwg.Effects.Ecma262.handler,
    ``Whatwg.Effects.Ecma262.handlerAt, ``Whatwg.Effects.Ecma262.run,
    ``Whatwg.Effects.Ecma262.handler_handle, ``Whatwg.Effects.Ecma262.handlerAt_id,
    ``Whatwg.Effects.Ecma262.interpret_eq_run, ``Whatwg.Effects.Ecma262.interpret_handlerAt,
    ``Whatwg.Effects.Ecma262.interpret_perform_step, ``Whatwg.Effects.Ecma262.resolvedWith,
    ``Whatwg.Effects.Ecma262.run_resolvedWith, ``Whatwg.Effects.Ecma262.sumHandler, ``Whatwg.Effects.Ecma262.interpret_sumHandler_inl, ``Whatwg.Ecma262.Agent.instDecidableEqExcept, ``Whatwg.WebIdl.Agent.resolve_view, ``Whatwg.WebIdl.Agent.react_resolve, ``Whatwg.WebIdl.Agent.resolvedWith]
  for n in names do
    if env.contains n then
      let axs ← liftCoreM (Lean.collectAxioms n)
      logInfo m!"{n}: {axs}"
    else
      logInfo m!"{n}: NOT FOUND"
```

### B.3 `Imports.lean`

```lean
import Lean
import Whatwg.Ecma262.Agent
import Whatwg.WebIdl.Agent
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let eff := mods.filter (fun m => (`Effects).isPrefixOf m)
  let infra := mods.filter (fun m => (`Whatwg.Infra).isPrefixOf m)
  logInfo m!"modules in closure: {mods.size}; Effects modules: {eff.size}; Whatwg.Infra modules: {infra.size}"
```

### B.4 `Shadow.lean`

```lean
import Effects.Algebra.Handler
def Whatwg.Effects.Handler : Type := Nat
namespace Whatwg.Effects.Probe
#check (Effects.Handler : Type)
end Whatwg.Effects.Probe
```

### B.5 `Witness040.lean` (the `WS-PROM-CE-040` seed)

```lean
import Whatwg.Ecma262.Agent
import Whatwg.WebIdl.Agent

/-! WS-PROM-CE-040 seed witness (W9 design seat, scratch only). -/

open Whatwg.Ecma262

/-- One pending promise with its capability, from the empty agent. -/
def start : Agent.Agent Unit Nat Nat × Promise.Capability := Agent.newPromise Agent.empty

/-- Store level: `WebIdl.Promise.react`, then `WebIdl.Promise.resolve` on the
table. `resolve` takes no queue, so the queue the caller holds after `react`
is the only queue there is. -/
def storeLevelJobs : Nat :=
  match Whatwg.WebIdl.Promise.react start.1.table start.1.reactions start.1.queue
      start.2.promise (some 7) none with
  | none => 99
  | some res => res.2.2.1.pending.length

theorem storeLevel_noJob : storeLevelJobs = 0 := rfl

/-- The store-level table after `resolve` does settle the promise: the job is
what is missing, not the settlement. -/
theorem storeLevel_settled :
    (match Whatwg.WebIdl.Promise.react start.1.table start.1.reactions start.1.queue
        start.2.promise (some 7) none with
      | none => none
      | some res => Promise.Table.get (Whatwg.WebIdl.Promise.resolve res.1 start.2.promise ())
          start.2.promise) = some (Promise.State.fulfilled ()) := rfl

/-- Agent level: the same two verbs enqueue exactly the reaction's job. -/
theorem agentLevel_oneJob :
    (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.react start.1 start.2 (some 7) none).1
        start.2 ()).queue.pending =
      [Jobs.ReactionJob.mk 0 (Except.ok ())] := rfl

/-- The hypotheses of `react_resolve_enqueues_wf` hold here, so the D46 law is
not vacuous. -/
theorem hypotheses_hold :
    Agent.WF start.1 ∧
      start.1.table.get start.2.promise = some Promise.State.pending ∧
      start.1.functions.find? (fun g => g.resolve == start.2.resolve) =
        some (Promise.createResolvingFunctions 0 0) ∧
      (Promise.createResolvingFunctions 0 0).alreadyResolved = false ∧
      (Promise.createResolvingFunctions 0 0).promise = start.2.promise :=
  ⟨Agent.WF.newPromise Agent.WF.empty, rfl, rfl, rfl, rfl⟩

/-- The law's right side at this point is the one job. -/
theorem law_instance :
    (Whatwg.WebIdl.Agent.resolve (Whatwg.WebIdl.Agent.react start.1 start.2 (some 7) none).1
        start.2 ()).queue.pending =
      start.1.queue.pending ++
        ((Promise.Reactions.waitingOn start.1.reactions start.2.promise
            Promise.ReactionType.fulfill).map
          (fun r => Jobs.ReactionJob.mk r.id (Except.ok ())) ++
        [Jobs.ReactionJob.mk start.1.reactions.next (Except.ok ())]) :=
  Whatwg.WebIdl.Agent.react_resolve start.1 start.2 _ 7 () hypotheses_hold.1
    hypotheses_hold.2.1 hypotheses_hold.2.2.1 hypotheses_hold.2.2.2.1 hypotheses_hold.2.2.2.2

#print axioms storeLevel_noJob
#print axioms storeLevel_settled
#print axioms agentLevel_oneJob
#print axioms hypotheses_hold
#print axioms law_instance
```

### B.6 `WFSettle.lean`

```lean
import Whatwg.Ecma262.Agent

/-! W9 measurement: `settle` keeps the seven prototype `WF` clauses. Scratch only. -/

namespace Whatwg.Ecma262.Agent

open Whatwg.Ecma262

/-- Lookup by identity commutes with an identity-keeping map. -/
theorem find?_map_fst {α : Type} (l : List (Nat × α)) (g : Nat × α → Nat × α)
    (hg : ∀ e, (g e).1 = e.1) (q : Nat) :
    List.find? (fun e => e.1 == q) (l.map g) = (List.find? (fun e => e.1 == q) l).map g := by
  rw [List.find?_map]
  have : ((fun e : Nat × α => e.1 == q) ∘ g) = (fun e => e.1 == q) := by
    funext e
    show ((g e).1 == q) = (e.1 == q)
    rw [hg e]
  rw [this]

/-- Settling keeps the identity list and the cursor. -/
theorem settle_ids {value reason : Type} (t : Promise.Table value reason) (id : Nat)
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

/-- Settling one identity leaves every other identity's state alone. -/
theorem settle_get_other {value reason : Type} (t : Promise.Table value reason) (id q : Nat)
    (result : Except reason value) (hne : q ≠ id) :
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

/-- A promise that is not pending stays not pending. -/
theorem settle_notPending {value reason : Type} (t : Promise.Table value reason) (id q : Nat)
    (result : Except reason value) (h : Promise.Table.isPending t q = false) :
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

/-- Trigger then clear change phases only: the fulfil list keeps its
identities, whichever list was triggered. -/
theorem trigger_clear_fulfill_ids {value reason body : Type} (rs : Promise.Reactions body)
    (p : Nat) (k : Promise.ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
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

/-- The same for the reject list. -/
theorem trigger_clear_reject_ids {value reason body : Type} (rs : Promise.Reactions body)
    (p : Nat) (k : Promise.ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
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

/-- Trigger then clear consume no registration cursor. -/
theorem trigger_clear_next {value reason body : Type} (rs : Promise.Reactions body)
    (p : Nat) (k : Promise.ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).next = rs.next := by
  cases k <;> rfl

/-- Membership through an identity-keeping list. -/
theorem lt_of_ids {body : Type} (l l' : List (Promise.Reaction body)) (n : Nat)
    (h : l'.map Promise.Reaction.id = l.map Promise.Reaction.id)
    (hl : ∀ r ∈ l, r.id < n) : ∀ r ∈ l', r.id < n := by
  intro r hr
  have hm : r.id ∈ l.map Promise.Reaction.id := h ▸ List.mem_map_of_mem hr
  obtain ⟨r0, hr0, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact hl r0 hr0

/-- **`settle` keeps the seven prototype clauses.** -/
theorem WF.settle {value reason body : Type} {a : Agent value reason body} (hw : WF a)
    (p : Nat) (result : Except reason value) : WF (settle a p result) := by
  have hF : ∀ r ∈ a.reactions.fulfill, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_left _ hr))
  have hR : ∀ r ∈ a.reactions.reject, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_left _ (List.mem_append_right _ hr))
  have hH : ∀ r ∈ a.held, r.id < a.reactions.next := fun r hr =>
    hw.reactionsBelow r (List.mem_append_right _ hr)
  have hids := settle_ids a.table p result
  have htab : (Agent.settle a p result).table = Promise.Table.settle a.table p result :=
    settleAndTrigger_table a.table a.reactions a.queue p result
  refine ⟨?_, ?_, hw.functionsBelow, ?_, ?_, ?_, ?_⟩
  · rw [htab, hids.1]
    exact hw.tableNodup
  · intro e he
    rw [htab] at he
    rw [htab, hids.2]
    have hmem : e.1 ∈ (Promise.Table.settle a.table p result).entries.map Prod.fst :=
      List.mem_map_of_mem he
    rw [hids.1] at hmem
    obtain ⟨e0, he0, h0⟩ := List.mem_map.mp hmem
    rw [← h0]
    exact hw.tableBelow e0 he0
  · intro f hf
    rw [htab, hids.2]
    exact hw.functionsAllocated f hf
  · intro f hf hres
    rw [htab]
    exact settle_notPending a.table p f.promise result (hw.resolvedSettled f hf hres)
  · -- the reaction lists: either unchanged, or trigger then clear
    unfold Agent.settle Promise.Table.settleAndTrigger
    cases Promise.Table.isPending a.table p with
    | false => exact hw.reactionsBelow
    | true =>
        intro r hr
        rcases List.mem_append.mp hr with hfr | hheld
        · rcases List.mem_append.mp hfr with hful | hrej
          · exact Nat.lt_of_lt_of_eq (lt_of_ids a.reactions.fulfill _ _
              (trigger_clear_fulfill_ids _ _ _ _ _) hF r hful) (trigger_clear_next _ _ _ _ _).symm
          · exact Nat.lt_of_lt_of_eq (lt_of_ids a.reactions.reject _ _
              (trigger_clear_reject_ids _ _ _ _ _) hR r hrej) (trigger_clear_next _ _ _ _ _).symm
        · exact Nat.lt_of_lt_of_eq (hH r hheld) (trigger_clear_next _ _ _ _ _).symm
  · -- the queue: unchanged, or the old jobs then the waiting reactions' jobs
    unfold Agent.settle Promise.Table.settleAndTrigger
    cases Promise.Table.isPending a.table p with
    | false => exact hw.queueBelow
    | true =>
        intro j hj
        change j ∈ (Promise.triggerReactions a.reactions p _ result a.queue).2.pending at hj
        rw [Promise.triggerReactions_order] at hj
        rcases List.mem_append.mp hj with hold | hnew
        · exact Nat.lt_of_lt_of_eq (hw.queueBelow j hold) (trigger_clear_next _ _ _ _ _).symm
        · obtain ⟨r, hr, hjr⟩ := List.mem_map.mp hnew
          rw [← hjr]
          have hr' := (List.mem_filter.mp hr).1
          refine Nat.lt_of_lt_of_eq ?_ (trigger_clear_next _ _ _ _ _).symm
          revert hr'
          cases result with
          | ok _ => exact hF r
          | error _ => exact hR r
end Whatwg.Ecma262.Agent

#print axioms Whatwg.Ecma262.Agent.settle_ids
#print axioms Whatwg.Ecma262.Agent.settle_get_other
#print axioms Whatwg.Ecma262.Agent.settle_notPending
#print axioms Whatwg.Ecma262.Agent.trigger_clear_fulfill_ids
#print axioms Whatwg.Ecma262.Agent.WF.settle
```
