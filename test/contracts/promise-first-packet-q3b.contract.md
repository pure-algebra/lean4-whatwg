# First promise packet — fidelity addendum (slice Q3b, `PROMISE-PG-FIRST`)

Status: FROZEN / RED, Q3b addendum breaker seat, 2026-09-07, on branch
`promise/q3b-breaker`, based on `f700230` (`Q3 landing repair and ratification
R-P20`). Graph: `docs/PROMISE-DAG.md`, section "Q3b addendum".

Base packet: `test/contracts/promise-first-packet.contract.md`, frozen at
`ef960be`, landed at `7377134`, ratified by R-P18 and R-P20. **Its text is not
edited by this addendum.** This file is layered on it in the shape
`test/contracts/writable-default.contract.md` uses for the P5a "composed
lifecycle" and "exact in-flight equation" addenda: the base packet's claim
boundary, pins, masks, decisions and acceptance conditions stand, and this file
adds obligations and names, by exact ascription, the base ascriptions it
supersedes.

This addendum answers the six fidelity findings **F1–F6** of ruling **R-P20**
and the six minors that ruling lists. It is breaker-owned: statements are the
breaker's, and the Q3b builder may repair elaboration but may not weaken,
delete or replace a frozen ascription, law, mask, decision or acceptance
condition, in this file or in the base packet.

The Lean batteries are the authority on names and propositions; the Lean in
this file is a reading aid.

Read first, in this order: `COORDINATION.md` ruling R-P20 (and R-P12 to R-P18,
which still bind); the base packet in full, including its §11 corrections and
§15 builder notes; `docs/DESIGN-BASIS.md` DB-02, DB-03, DB-04, DB-07 and DB-11;
`docs/PROMISE-EXTRACTION-INVENTORY.md` rows `E-20`, `E-29`, `E-31`, `E-33`,
`E-37`, `E-47`, `E-50`, `E-51`, `E-55`, `E-56`, `E-63`, `E-71` and gaps `G-01`
to `G-11`; `test/counterexamples/promise/ATTACKS.md` in full, whose rows
`WS-PROM-CE-023` to `WS-PROM-CE-038` are seeded first and are the reason each
obligation below exists.

## 1. Claim boundary

This addendum repairs the fidelity of the first promise packet's surface to the
pinned bytes. It grants no coverage state, no host observation, no equivalence
with any engine, and no new claim about `Whatwg.Streams`.

Both censuses stay all-`absent`. Every row cited here is cited as an **anchor
for a declaration**, never as a numerator, exactly as in the base packet's §1.
`WhatwgTest/Audit/{WebIdl,Ecma262}/SpecCoverage.lean` exist on the merged tree
and are untouched; no row moves to `partial` or `green`.

Nothing here reopens DB-03: the job queue stays deterministic FIFO state inside
the configuration. F5 adds the agent's *activation* as state beside it, which
is what `requirement.jobs.1` to `requirement.jobs.3` are about; it is not a new
decision kind.

Nothing here reopens R-P18's ratification of the base packet's six decisions.
Decisions 6 to 12 stand unchanged. In particular decision 8 — two reaction
lists with `Reactions.registered` as the one-list view Streams instantiates —
is the reason F2's repair is expressible at all: with one list there would be
no "opposite-side entry" to leave `waiting`.

Explicitly still out, with their gap ids, unchanged from the base packet's
§5.2: `G-02` remainder (`HostPromiseRejectionTracker`, 2701220..2702791 — and
therefore `op.performpromisethen` step 11's third sub-step and
`op.rejectpromise` step 7), `G-04` (`IsPromise` and the value universe),
`G-05` (thenable adoption), `G-06` remainder (`op.waiting-for-all-promise`,
354881..356058, and its `[=Queue a microtask=]` step), `G-07` remainder (the
realm parameter, the Job Abstract Closure carrier, `HostMakeJobCallback`,
`HostCallJobCallback`), `G-09` remainder, `G-10` (the Completion carrier
beyond `Except`), `G-11` remainder (`then`/`catch`/`finally`, the combinators,
the `Promise` constructor, and — new here — `op.dfn-perform-steps-once-promise-is-settled`
steps 6 and 8, the `newCapability` Web IDL `react` creates and returns).

## 2. Pins

Unchanged from the base packet's §2 as amended by R-P19 (the Web IDL census is
124 rows, `rows=124`).

| Item | Value |
| --- | --- |
| ECMA-262 source | `vendor/ecma262-0248456c/spec.html`, `tc39/ecma262` `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026`, 2,978,793 bytes, SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |
| Web IDL source | `vendor/whatwg-webidl-a652053f/index.bs`, `whatwg/webidl` `a652053f1e74e4aaf647528deb174012ed6c909f`, March 2026 Review Draft, 695,845 bytes, SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` |
| ES2026 census | `generated/ecma262-census.tsv`, 77 rows, header `rows=77` |
| Web IDL census | `generated/webidl-census.tsv`, 124 rows, header `rows=124` (R-P19) |

Byte offsets are 0-based and ends are exclusive. No line number is cited
anywhere in this addendum.

One anchor is new to the lane and is not in the base packet's alias table:

| Alias | Census row | Span | Span digest |
| --- | --- | --- | --- |
| CAPFIELD | `field.promisereaction-records.Capability` | 2691475..2691802 | `67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77` |
| JOBS4 | `requirement.jobs.4` | 626486..626589 | `22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b` |

Everything else expands through `docs/PROMISE-DAG.md`'s alias table.

## 3. The batteries and their counts

| Module | `#check` | `example` | `#print axioms` | Role |
| --- | ---: | ---: | ---: | --- |
| `WhatwgTest/Ecma262/PromiseFidelityContract.lean` | 11 | 0 | 0 | the new `Whatwg.Ecma262.Promise` signatures (F1–F4, F6, minors) |
| `WhatwgTest/Ecma262/PromiseFidelityLaws.lean` | 33 | 0 | 0 | their laws, plus one Streams bridging lemma |
| `WhatwgTest/Ecma262/JobsCompleteContract.lean` | 14 | 0 | 0 | F5: 3 signatures and 11 laws |
| `WhatwgTest/WebIdl/PromiseFidelityContract.lean` | 17 | 0 | 0 | F6 and the Web IDL minors: 4 signatures and 13 laws |
| `WhatwgTest/Ecma262/PromiseFidelityAxiomReport.lean` | 0 | 0 | 57 | the receipt list |

**75 `#check` ascriptions, 0 `example`s and 57 axiom receipts.** 57 of the
ascriptions are theorem obligations (33 + 11 + 13), and the axiom report names
exactly those 57.

The 75 split as **17 signatures + 57 theorem obligations + 1 `inferInstance`
re-check**. The 17 signatures are `Reaction.capability` (a projection of the
amended `Reaction`), `SettlementTrace` (the one new type), and fifteen new
functions and predicates: `Reactions.mint`, `Reactions.clear`,
`reactionHandlerResult`, `ResolvingFunctions.callSettle`, `runReactionJob`,
`ResolvingFunctions.callResolveSelf`, `Table.settleTraced`,
`SettlementTrace.firstRejection`, `Jobs.startJob`, `Jobs.completeJob`,
`Jobs.RunToCompletion`, `Promise.waitForAllTraced`,
`Promise.newPromiseWithCapability`, `Promise.resolveThrough` and
`Promise.rejectThrough`. The `inferInstance` re-check is
`Repr (Reaction Nat)`, the `E-50` receipt; it is green today and must stay
green after `Reaction` gains its field.

The base packet's own 371 `#check`s, 13 `example`s and 125 receipts stay, with
17 of the 371 amended in place as §4 lists. The base packet's
`WhatwgTest/Ecma262/PromiseAxiomReport.lean` is **not edited**: the amendments
change statements, never names.

## 4. The amended Q3 ascriptions

Statements are breaker-owned, so every amendment below is made by this seat in
the base packet's own battery, beside the ascription it supersedes, with a
dated comment naming this addendum, the finding, the counterexample row and the
superseded text verbatim or in an abbreviated form that names what changed.
Every other Q3 ascription is byte-identical. The builder may not touch any
statement.

**Twenty-four ascriptions are amended: nineteen in their text and five by
annotation alone**, where the statement is unchanged and only the mask label or
the reading changes. Three of the nineteen (`add_id`, `add_next`, `add_paired`)
change only a `∀`-telescope. Rows `1`..`19` are the text changes and rows
`A1`..`A5` the annotations.

| # | Ascription | Battery | Kind | Finding | Why forced |
| ---: | --- | --- | --- | --- | --- |
| 1 | `Promise.Reaction.mk` | `Ecma262/PromiseContract` | signature | F4 | CAPFIELD is the record's first field and `op.newpromisereactionjob` reads it; without it the capability is stored nowhere |
| 2 | `Promise.Reactions.add` | `Ecma262/PromiseContract` | signature | F4 | `op.performpromisethen` steps 7 and 8 give both records the same `_resultCapability_` |
| 3 | `Promise.performPromiseThen` | `Ecma262/PromiseContract` | signature | F1, F2 | steps 10 and 11 append nothing, so the captured record is not reachable through `Reactions` and the operation must return it |
| 4 | `Reactions.add_id` | `Ecma262/PromiseLaws` | telescope | F4 | follows 2 |
| 5 | `Reactions.add_next` | `Ecma262/PromiseLaws` | telescope | F4 | follows 2 |
| 6 | `Reactions.add_fulfill` | `Ecma262/PromiseLaws` | statement | F4 | follows 1 and 2; this is where the capability is checkable |
| 7 | `Reactions.add_reject` | `Ecma262/PromiseLaws` | statement | F4 | as 6 |
| 8 | `Reactions.add_paired` | `Ecma262/PromiseLaws` | telescope | F4 | follows 2 |
| 9 | `Table.settleAndTrigger_pending` | `Ecma262/PromiseLaws` | statement | F3 | `op.fulfillpromise` steps 4–5 and `op.rejectpromise` steps 4–5 clear **both** lists; the base right-hand side cleared one |
| 10 | `performPromiseThen_pending` | `Ecma262/PromiseLaws` | statement | F1 | step 12 is unconditional; the base statement froze the omission |
| 11 | `performPromiseThen_fulfilled` | `Ecma262/PromiseLaws` | statement | F2 | step 10 appends to no list |
| 12 | `performPromiseThen_rejected` | `Ecma262/PromiseLaws` | statement | F2 | step 11 appends to no list |
| 13 | `WebIdl.Promise.react` | `WebIdl/PromiseContract` | signature | F1, F2 | `react` performs `PerformPromiseThen`, so it inherits step 12 and the settled branches; neither is expressible without the table and the captured record in the result |
| 14 | `WebIdl.Promise.uponFulfillment` | `WebIdl/PromiseContract` | signature | F1, F2 | follows 13 |
| 15 | `WebIdl.Promise.uponRejection` | `WebIdl/PromiseContract` | signature | F1, F2 | follows 13 |
| 16 | `WebIdl.Promise.react_pending` | `WebIdl/PromiseContract` | statement | F1, F4 | follows 13 and 2 |
| 17 | `WebIdl.Promise.react_fulfilled` | `WebIdl/PromiseContract` | statement | F1, F2 | follows 13 |
| 18 | `WebIdl.Promise.react_rejected` | `WebIdl/PromiseContract` | statement | F1, F2 | follows 13 |
| 19 | `Streams.Transform.subscribe_reactions_bridge` | `Streams/PromiseBridge` | statement | F4 | follows 2; Streams supplies `none`, a recorded `G-11` restriction |
| A1 | `Promise.triggerReactions_other_kind` | `Ecma262/PromiseLaws` | **annotation only** | F3 | the statement is true of `op.triggerpromisereactions` alone and stays frozen; the annotation forbids reading it as a law about the two callers |
| A2 | `WebIdl.Promise.waitForAll_failure` | `WebIdl/PromiseContract` | **mask M2 → M1** | F6 | R-P20: the M2 label overstates it. Argument order is neither a settlement order nor a queue order under §7's rule |
| A3 | `WebIdl.Promise.waitForAll_success` | `WebIdl/PromiseContract` | **mask M2 → M1** | F6 | the same rule applied to the same kind of statement; offered for coordinator ratification, since R-P20 names only A2 |
| A4 | `Streams.Writable.attachSink_pending_jobs` | `Streams/PromiseBridge` | **mask M2 → M1** | minor | §7's M2 list excludes it and its statement has `jobQueue s` on both sides, observing shape and not order |
| A5 | `Jobs.run_cons` | `Ecma262/JobsLaws` | **mask M2 confirmed** | minor | the implementation docstring says M2 and §7's *rule* agrees; §7's *table* of twelve is short by one and is amended to thirteen |

The Freeze receipt's per-module diagnostic table is the measurement that settles
the count in both directions: nineteen text changes across four batteries, and
five annotations of which one (`A5`, `run_cons`) is the only change in
`WhatwgTest/Ecma262/JobsLaws.lean`, which therefore stays green.

`performPromiseThen_missing`, `react_missing`, `uponFulfillment_eq` and
`uponRejection_eq` are **not** amended: their statements are byte-identical and
elaborate unchanged at the new result types, which the Freeze receipt confirms
(no diagnostic points at them).

### 4.1 The §7 mask table, amended

§7 of the base packet enumerates twelve M2 theorems plus five M2 bridging
lemmas. This addendum amends that enumeration, not the rule:

- **add** `Jobs.run_cons` (thirteen);
- **remove** `WebIdl.Promise.waitForAll_success` and
  `WebIdl.Promise.waitForAll_failure` (eleven);
- the bridging five become four: `Writable.attachSink_pending_jobs` was never
  in §7's list and its tree docstring is corrected to M1, while
  `Writable.tick_dequeue_bridge`, `Readable.runPullJob_dequeue_bridge`,
  `Transform.tick_dequeue_bridge`, `Writable.attachSink_settled_jobs` and
  `Writable.acceptAnswer_jobs` stand (§7 calls these five "three", which is a
  miscount this addendum records without changing any of the five labels);
- **add** the addendum's own M2 theorems: `Table.settleTraced_pending`,
  `SettlementTrace.firstRejection_hit`, `Writable.settlementTrace_bridge`,
  `Jobs.startJob_checkpoint`, `Jobs.startJob_queue`, `Jobs.run_one_job_per_step`,
  `Jobs.startJob_run_agree`, `Promise.waitForAllTraced_failure`,
  `Promise.waitForAllTraced_failure_pending`, and the two amended
  `performPromiseThen_fulfilled`/`_rejected` and
  `react_fulfilled`/`react_rejected`, which keep their M2 labels because their
  enqueued job is unchanged.

## 5. F5 — the recommendation

**Recommend the `Active`-threaded step, not discharge by typing.**

`requirement.jobs.3` (COMPLETE, 626357..626479) reads: "Once evaluation of a
Job starts, it must run to completion before evaluation of any other Job starts
in an agent." A discharge by typing would argue that one job is one `run` step,
that `run` has a single recursive call and it is on the tail, and that
`run_split` composes, so no second job can begin inside the first. That
argument is true of `run`, and this addendum keeps it as a theorem
(`Jobs.run_one_job_per_step`, mask M2, with `run_split` unchanged as the
composition), but it does **not** discharge the requirement, for the reason
R-P20 gives: `run` never consults the activation, and `Active.job` is produced
by no operation. A requirement about what may start *while a job is evaluating*
cannot be discharged by a function that has no notion of a job evaluating; the
argument would be about `run`'s recursion, not about the agent, and
`Active.job` would remain a constructor nothing can reach, which is the shape a
vacuous discharge takes. The base packet already states `requirement.jobs.1`
and `requirement.jobs.2` as `RunCondition` and `step_blocked` over that same
unreachable activation, so the third bullet is where the omission becomes
visible rather than where it begins.

The recommendation is therefore: `Jobs.startJob` dequeues the oldest job **and**
enters `Active.job serial` — it is the missing producer, which
`Jobs.startJob_active` states; `Jobs.completeJob` is the only route back to
`Active.checkpoint`, which `completeJob_job` and `completeJob_other` bound;
`Jobs.RunToCompletion` is the DB-05 specification half, in the same shape R-P5
requires for `hook.hostenqueuepromisejob`; `Jobs.run_to_completion` is the
realizer theorem, that in any `Active.job` activation `step` answers `none` at
every payload and every queue; and `Jobs.run_to_completion_nonvacuous` is the
receipt that the specification bites, because the activation `startJob`
produces is one in which `RunCondition` fails. The repair is conservative:
`Jobs.startJob_run_agree` says that forgetting the activation from `startJob`
at a checkpoint gives `Queue.dequeue` back exactly, so `Jobs.run_fifo`,
`Jobs.run_split`, `Jobs.hostEnqueuePromiseJob_order`,
`Writable.tick_job_fifo` and `Transform.tick_job_fifo` keep their statements
and their proofs, and `E-47` (`Writable.Control.react`, keep) stays where it
is: no second activation state is introduced. `G-08`'s remainder — a single
global configuration that threads the activation across the three components —
is P8 and stays open, and this addendum makes no claim about it.

The theorem is stated either way, as the seat instruction requires: the typed
statement is `Jobs.run_one_job_per_step` and the threaded statement is
`Jobs.run_to_completion` with `Jobs.run_to_completion_nonvacuous` beside it.
Only the second is offered as the realization of COMPLETE.

## 6. F6 — the settlement-order design

**A first-order settlement trace over the one table, related to the Streams
settlement order by a bridge, with `waitForAll` unchanged and a traced
companion beside it.**

Web IDL `wait for all` (WAITALL, 353239..354879) is not a predicate over a
final table. Its rejection handler is "1. If `rejected` is true, abort these
steps. 2. Set `rejected` to true. 3. Perform `failureSteps` given `arg`", which
fires on the first rejection **to settle**, mentions neither `fullfilledCount`
nor `total`, and therefore runs with the other promises still pending; the
success steps run only from the fulfilment handler and only when
`fullfilledCount` equals `total`, with `result[promiseIndex]` making the value
list argument-ordered. The landed `waitForAll` guards the whole answer on
`allSettled` and picks the reported reason with `List.findSome?` over the
argument list, so it answers `pending` where the text answers `failure` and it
can report a different reason than the text does. Neither divergence is
expressible over `Promise.Table`, which records what each identity settled to
and not when. The design is therefore
`Whatwg.Ecma262.Promise.SettlementTrace value reason`, an ordered list of
settled identities with their outcomes, oldest first, appended by
`Table.settleTraced`, whose first component is `Table.settle`'s table
unchanged — that equation, `Table.settleTraced_table`, is the R-P12 receipt
that this is a trace and not a shadow table, and `Table.mk`'s arity is
untouched so every Q3 ascription over `Table` stands. It is stated under mask
M2 per DB-04, because `Table.settleTraced_pending` and
`SettlementTrace.firstRejection_hit` observe the order in which settlements
happen and nothing else. Its shape is deliberately `E-71`'s
(`Whatwg.Streams.Writable.settlementTrace`, keep) lifted off the writable event
alphabet, so the bridge `Whatwg.Streams.Writable.settlementTrace_bridge`
(mask M2) needs no projection: the Streams declaration's content is unchanged
and the general first-rejection-to-settle reads off it directly; `E-63`
(`Readable.settlementTrace`, keep) is the readable counterpart and its bridge
is deferred with a stated reason, that the readable alphabet's `closed` entry
carries no promise identity and supplying one would change `Readable.Settlement`,
a `keep` row. `Promise.waitForAll` and its two law statements then keep their
signatures — `E-55` and `E-56` own the predicate half and eleven Streams call
sites reach it — their masks are corrected to M1 because argument order is
neither a settlement order nor a queue order, and
`Promise.waitForAllTraced` is the operation the pinned text describes, with
`waitForAllTraced_failure` and `waitForAllTraced_failure_pending` as the two
genuinely M2 laws and `waitForAllTraced_success` and
`waitForAll_traced_success_agree` fixing where the two forms agree.

## 7. The exact new surface

Every entry names its inventory row with reuse mode or its gap id, its census
anchor, and its mask. The Lean below is a reading aid; the batteries are the
authority.

### 7.1 `Whatwg.Ecma262.Promise` — F1, F2, F3, F4, minors, F6 trace

| Declaration | Row / gap | Anchor | Mask |
| --- | --- | --- | --- |
| `Reaction.capability : ∀ {body}, Reaction body → Option Capability` | `G-01`, `E-50` (generalize) | CAPFIELD, REACTREC | — |
| `Reactions.mint : ∀ {body}, Reactions body → Nat → ReactionType → Option body → Option Capability → Reactions body × Reaction body` | `G-01`, `E-29` (generalize) | THEN steps 7, 8, 10, 11 | — |
| `Reactions.clear : ∀ {body}, Reactions body → Nat → Reactions body` | `G-01`, `E-33` (generalize) | FULFILL steps 4–5, REJECT steps 4–5 | — |
| `reactionHandlerResult : ∀ {value reason body}, Reaction body → Except reason value → Except reason value → Except reason value` | `G-07`, `E-51` (generalize) | REACTJOB inner steps 4–5, JOBS4 | — |
| `ResolvingFunctions.callSettle : ∀ {value reason}, ResolvingFunctions → Table value reason → Except reason value → ResolvingFunctions × Table value reason` | `G-03` | RESOLVING | — |
| `runReactionJob : ∀ {value reason body}, Table value reason → ResolvingFunctions → Reaction body → Except reason value → Except reason value → ResolvingFunctions × Table value reason` | `G-07`, `G-03`, `E-51` (generalize) | REACTJOB inner steps 6–9 | — |
| `ResolvingFunctions.callResolveSelf : ∀ {value reason}, ResolvingFunctions → Table value reason → Nat → reason → Option (ResolvingFunctions × Table value reason)` | `G-03` | RESOLVING resolve steps step 4 | — |
| `SettlementTrace : Type → Type → Type` | `E-71`, `E-63` (keep), DB-04 M2 | — (a model device, no census row) | — |
| `Table.settleTraced : ∀ {value reason}, Table value reason → SettlementTrace value reason → Nat → Except reason value → Table value reason × SettlementTrace value reason` | `E-20` (generalize), `G-06` | FULFILL, REJECT | — |
| `SettlementTrace.firstRejection : ∀ {value reason}, SettlementTrace value reason → List Nat → Option reason` | `G-06`, `E-56` (generalize) | WAITALL | — |

Laws, 33, all in `WhatwgTest/Ecma262/PromiseFidelityLaws.lean`:

`Table.markHandled_marked` (M1), `performPromiseThen_handled` (M1);
`Reactions.mint_eq`, `mint_fulfill`, `mint_reject`, `mint_next`,
`mint_reaction`, `mint_capability`, `mint_no_waiting` (all M1);
`Reactions.clear_eq`, `clear_waiting`, `clear_other_promise`, `clear_next`,
`Table.settleAndTrigger_cleared` (all M1);
`reactionHandlerResult_empty`, `reactionHandlerResult_handler`,
`ResolvingFunctions.callSettle_ok`, `callSettle_error`,
`runReactionJob_no_capability`, `runReactionJob_empty_handler`,
`runReactionJob_resolve`, `runReactionJob_reject`, `runReactionJob_once`
(all M1);
`ResolvingFunctions.callResolve_disables_reject`, `callReject_disables_resolve`,
`callResolveSelf_self`, `callResolveSelf_other` (all M1);
`Table.settleTraced_table` (M1), `settleTraced_pending` (**M2**),
`settleTraced_other` (M1), `SettlementTrace.firstRejection_eq` (M1),
`firstRejection_hit` (**M2**);
`Whatwg.Streams.Writable.settlementTrace_bridge` (**M2**).

`runReactionJob` is **not** a stored computation (DB-02, WS-PROM-CE-027): the
handler stays `Option body`, a first-order descriptor, and the handler's
completion arrives as the `decision` argument, which
`reactionHandlerResult_handler` returns unexamined. The empty-handler case is
the argument itself, because `triggerReactions` already tags it `Except.ok` on
the fulfil side and `Except.error` on the reject side, so REACTJOB's
`NormalCompletion` and `ThrowCompletion` are that tag and nothing more; that is
`reactionHandlerResult_empty`. `runReactionJob` then settles the capability's
promise **through the resolving functions**, which is why it takes them rather
than minting a pair: the one-shot marker is state the configuration owns, and a
freshly minted pair would re-arm it.

### 7.2 `Whatwg.Ecma262.Jobs` — F5

| Declaration | Row / gap | Anchor | Mask |
| --- | --- | --- | --- |
| `startJob : ∀ {payload}, Active → Queue payload → Nat → Option (payload × Active × Queue payload)` | `G-08`, `E-51` (generalize), `E-47` (keep) | RUNCOND, ONEJOB, ORDER | — |
| `completeJob : Active → Active` | `G-08` | COMPLETE | — |
| `RunToCompletion : ∀ {payload}, Active → Prop` | `G-08` | COMPLETE | — |

Laws, 11, in `WhatwgTest/Ecma262/JobsCompleteContract.lean`:
`startJob_checkpoint` (**M2**), `startJob_queue` (**M2**), `startJob_blocked`
(M1), `startJob_active` (M1), `completeJob_job` (M1), `completeJob_other` (M1),
`RunToCompletion_iff` (M1), `run_to_completion` (M1),
`run_to_completion_nonvacuous` (M1), `run_one_job_per_step` (**M2**),
`startJob_run_agree` (**M2**).

### 7.3 `Whatwg.WebIdl.Promise` — F6 and the minors

| Declaration | Row / gap | Anchor | Mask |
| --- | --- | --- | --- |
| `Promise.waitForAllTraced : ∀ {value reason}, Table value reason → SettlementTrace value reason → List Nat → WaitResult value reason` | `G-06`, `E-55`, `E-56` (generalize) | WAITALL | — |
| `Promise.newPromiseWithCapability : ∀ {value reason}, Table value reason → Nat → Table value reason × Capability` | `G-03`, `E-19` (generalize) | NEWP, NEWCAP | — |
| `Promise.resolveThrough : ∀ {value reason}, ResolvingFunctions → Table value reason → value → ResolvingFunctions × Table value reason` | `G-03`, `E-20` (generalize) | RESOLVE, RESOLVING | — |
| `Promise.rejectThrough : ∀ {value reason}, ResolvingFunctions → Table value reason → reason → ResolvingFunctions × Table value reason` | `G-03`, `E-20` (generalize) | REJECTOP, RESOLVING | — |

Laws, 13, in `WhatwgTest/WebIdl/PromiseFidelityContract.lean`:
`waitForAllTraced_pending` (M1), `waitForAllTraced_success` (M1),
`waitForAllTraced_failure` (**M2**), `waitForAllTraced_failure_pending`
(**M2**), `waitForAll_traced_success_agree` (M1),
`newPromiseWithCapability_eq` (M1), `newPromise_capability_promise` (M1),
`resolveThrough_eq` (M1), `rejectThrough_eq` (M1), `resolveThrough_resolve`
(M1), `rejectThrough_reject` (M1), `react_performPromiseThen` (M1),
`react_handled` (M1).

### 7.4 The minors that add no declaration

- **The `[[AlreadyResolved]]` anachronism.** At this pin RESOLVING has no
  `[[AlreadyResolved]]` record. Step 1 creates one Record
  `{ [[Value]]: toResolve }` that both `_resolveSteps_` (step 2) and
  `_rejectSteps_` (step 4) capture, and each closure's own step 3 sets that
  shared `[[Value]]` to `~empty~` after its step 1 has tested it. The field
  keeps the name `alreadyResolved` — renaming it would break four frozen
  ascriptions for a citation defect — and the **citation** is corrected here,
  with `callResolve_disables_reject` and `callReject_disables_resolve` stating
  the sharing the name hides. WS-PROM-CE-032.
- **The §4.6 citation for `Option` handlers.** REACT steps 1 to 4 build both
  `onFulfilled` and `onRejected` unconditionally, so Web IDL `react` never
  registers an empty handler and cannot be what justifies
  `Reaction.handler : Option body`. The justification is
  `field.promisereaction-records.Handler` (2692151..2692611, "a JobCallback
  Record or `~empty~`") together with THEN steps 3 and 5, the `IsCallable`
  test. The `none` that `uponFulfillment` and `uponRejection` pass on the other
  side is a **modelling restriction recorded under `G-11`**, not the pinned
  text: the text's `react` builds a rejection handler that returns "a promise
  rejected with reason" and a fulfilment handler that returns the value, and
  neither is representable without the derived promise. `uponFulfillment_eq`
  and `uponRejection_eq` keep their statements and freeze that restriction
  where it can be seen. WS-PROM-CE-036.
- **The two divergent masks.** §4.1 above. WS-PROM-CE-037.
- **`E-50` and `E-51` cited nowhere.** Both are cited in the base packet's
  §4.4, in `docs/PROMISE-DAG.md` and in `ATTACKS.md`, and in **no** battery
  ascription, which acceptance condition 1 of the base packet requires. This
  addendum cites `E-50` on `Reaction.capability` and on the
  `inferInstance : Repr (Reaction Nat)` re-check — the new field must not force
  `DecidableEq`, or the general record stops being instantiable at
  `Transform.Job`'s payload — and `E-51` on `runReactionJob`, on
  `reactionHandlerResult` and on `Jobs.startJob`, the general "run one job"
  step whose Streams bridge the base packet deferred. WS-PROM-CE-038.
- **`op.rejectpromise`'s step numbering.** R-P20's F3 says "RejectPromise steps
  3–4". Measured from the pinned bytes both operations clear at **steps 4 and
  5**: RejectPromise is 1 assert, 2 capture, 3 set `[[PromiseResult]]`, 4 set
  `[[PromiseFulfillReactions]]`, 5 set `[[PromiseRejectReactions]]`, 6 set
  state, 7 tracker, 8 trigger, 9 return. Recorded as a measurement correction
  in the spirit of the base packet's §11; the finding itself stands unchanged.
- **`op.newpromisereactionjob`'s inner step numbering.** The Job Abstract
  Closure has nine inner steps, not eleven: 1 capability, 2 type, 3 handler,
  4 the `~empty~` branch (4a `~fulfill~` → `NormalCompletion`, 4b `~reject~` →
  assert and `ThrowCompletion`), 5 the handler branch, 6 the
  capability-`undefined` branch returning `~empty~`, 7 the assertion, 8 abrupt →
  `Call([[Reject]])`, 9 `Return ? Call([[Resolve]])`. The batteries cite these
  numbers.

## 8. Design constraints honoured

- **Additive and name-stable.** Every landed name keeps its signature except
  where §4 records a forced change, and each forced change names the exact new
  signature, the exact superseded ascription and the battery it lives in. No
  name is renamed. `Whatwg/WebIdl/Exceptions.lean` and the whole of part C are
  untouched.
- **No shadow table, no second queue (R-P12).** `Table.settleTraced_table` is
  the receipt for the first and `Jobs.startJob_run_agree` for the second:
  `startJob` is `Queue.dequeue` with the activation threaded through, not a
  second runner over a second queue. `Reactions` remains the one owner of
  reaction records; `Reactions.mint` returns the unappended one to the caller
  rather than storing it in a third list.
- **Streams unchanged in content.** `Whatwg.Streams.Writable.settlementTrace`
  and `Whatwg.Streams.Readable.settlementTrace` keep their bodies and their
  `settlementTrace_eq` receipts. The addendum's one additive Streams bridging
  lemma, `Writable.settlementTrace_bridge`, adds no field, no import beyond
  what `Whatwg/Streams/Writable/Laws.lean` already reaches, and no `@[simp]`
  attribute. No `attribute [local simp]` set changes.
- **DB-02.** Running a reaction job takes the handler's result as a decision;
  no body is stored.
- **DB-04.** Every new theorem names M1 or M2, and §4.1 amends §7's
  enumeration rather than its rule.
- **DB-07.** `waitForAllTraced_pending` is a live frontier, not a failure, and
  `Jobs.run` is still not a semantic fuel parameter.
- **R-P12.** Every ascription cites an inventory row with its reuse mode or a
  gap id, and `E-50` and `E-51` are cited in a battery for the first time.

## 9. Acceptance conditions

1. Every frozen ascription of the five Q3b batteries elaborates with no edit to
   a statement, and every one cites an inventory row `E-01`..`E-74` with its
   reuse mode or a gap id `G-01`..`G-11` with the census rows it realizes.
2. Every amended Q3 ascription of §4 elaborates as amended, and **every other
   Q3 ascription is byte-identical to `f700230`**. `git diff` over
   `WhatwgTest/Ecma262/{JobsContract,JobsLaws,PromiseAxiomReport}.lean` and
   `WhatwgTest/WebIdl/ExceptionsContract.lean` shows only the one `run_cons`
   annotation; the other three files are unchanged.
3. The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green
   before and after the builder's landing, including all 13 `example`s and all
   six `inferInstance` checks; every existing battery under
   `WhatwgTest/Streams/**` is green; no P4–P7 theorem statement, Streams
   definition body or `attribute [local simp]` set changed. The base packet's
   §9 obligations 1 to 6 all still hold.
4. A repair that turns a declared red module green by weakening a preservation
   ascription is a refusal, not a landing.
5. The two divergent mask docstrings inside `Whatwg/` are corrected:
   `Whatwg/Streams/Writable/Laws.lean`'s `attachSink_pending_jobs` becomes
   M1, and `Whatwg/Ecma262/Jobs.lean`'s `run_cons` stays M2. The two
   `waitForAll_*` docstrings in `Whatwg/WebIdl/Promise.lean` become M1.
6. All 57 receipts in `WhatwgTest/Ecma262/PromiseFidelityAxiomReport.lean` are
   inside the R-11 ceiling, and the base packet's 125 in
   `WhatwgTest/Ecma262/PromiseAxiomReport.lean` are still exactly 125 names,
   neither short nor long.
7. `Jobs.run_to_completion` is proved with `Jobs.run_to_completion_nonvacuous`
   beside it, and `Jobs.startJob_run_agree` shows the threading is
   conservative: `Jobs.run_fifo`, `Jobs.run_split`,
   `Jobs.hostEnqueuePromiseJob_order`, `Writable.tick_job_fifo`,
   `Transform.tick_job_fifo` and the three `runPullJob_*` receipts keep their
   statements **and** their proofs. `requirement.jobs.3`'s census row stays
   `absent`.
8. `Table.settleTraced_table` is proved, so no shadow table exists;
   `Whatwg.Streams.Writable.settlementTrace` and
   `Whatwg.Streams.Readable.settlementTrace` are unchanged in content.
9. Both censuses stay all-`absent`: no coverage block changes and no row goes
   `partial` or `green`. `lake exe census --standard {infra,webidl,ecma262}`
   all pass.
10. Every gap listed in §1 is still open after the landing, recorded against
    its gap id in the module docstrings.
11. `known-red.txt` is empty again, `lake --wfail build Whatwg Gates`,
    `lake build`, `lake --wfail build WhatwgTest`, `lake exe vendorseal` and
    `lake exe citations` pass, and independent review checks the inventory join
    in both directions and the sixteen counterexample rows against the
    statements named for them.

## 10. The expected declaration delta

Baseline, the Q3 landing's measured pair on the integration commit `7377134`:
**196 modules and 12973 declarations** (1477 in the Gates tooling tree). This
worktree's base `f700230` is that tree plus the Q3 landing repair, which adds
no declaration.

This addendum adds **5 test modules** (four batteries and the axiom report), so
the module count moves 196 → 201. **No implementation module is added**: all
four promise modules exist.

The authored named-declaration delta is **+73**:

| Tree | Types | Functions and predicates | Theorems | Total |
| --- | ---: | ---: | ---: | ---: |
| `Whatwg/Ecma262/Promise.lean` | 1 | 8 | 32 | 41 |
| `Whatwg/Ecma262/Jobs.lean` | 0 | 3 | 11 | 14 |
| `Whatwg/WebIdl/Promise.lean` | 0 | 4 | 13 | 17 |
| `Whatwg/Streams/**`, additive | 0 | 0 | 1 | 1 |
| **Total** | **1** | **15** | **57** | **73** |

The one type is `SettlementTrace`, an `abbrev`, which contributes no
constructors, no recursor, no `noConfusion` and no derived instance. The eight
`Ecma262/Promise.lean` functions are `Reactions.mint`, `Reactions.clear`,
`reactionHandlerResult`, `ResolvingFunctions.callSettle`, `runReactionJob`,
`ResolvingFunctions.callResolveSelf`, `Table.settleTraced` and
`SettlementTrace.firstRejection`; the three in `Ecma262/Jobs.lean` are
`startJob`, `completeJob` and `RunToCompletion`; the four in
`WebIdl/Promise.lean` are `waitForAllTraced`, `newPromiseWithCapability`,
`resolveThrough` and `rejectThrough`. The one additive Streams theorem is
`Writable.settlementTrace_bridge`.

`Reaction` gains one field, so `Reaction.capability` is **one new generated
projection** and `Reaction.mk`'s type changes; the type's other generated
constants (`Reaction.rec`, `Reaction.recOn`, the `Repr` instance) are
regenerated at the new arity and their count does not change. No other landed
type changes shape, and no new inductive or structure is declared.

The audit's `declarations` figure counts generated constants as well as
authored ones, so the exact figure is

```text
12973 + 73 + 1 (the generated projection Reaction.capability)  =  13047
```

and the landing record must publish the measured before-and-after pair together
with that arithmetic. A delta not accounted for by this table is a defect: it
means something was added that this addendum did not freeze.

## 11. Fence

Frozen breaker files, which the builder may not edit:

- `test/contracts/promise-first-packet-q3b.contract.md` and the base packet
- `WhatwgTest/Ecma262/PromiseFidelityContract.lean`,
  `PromiseFidelityLaws.lean`, `JobsCompleteContract.lean`,
  `PromiseFidelityAxiomReport.lean`
- `WhatwgTest/WebIdl/PromiseFidelityContract.lean`
- the base packet's eight batteries, including the amendments of §4
- `test/counterexamples/promise/ATTACKS.md`
- the declaration and statement rows of `docs/PROMISE-DAG.md`

Builder fence: `Whatwg/Ecma262/{Promise,Jobs}.lean`,
`Whatwg/WebIdl/Promise.lean`, the one additive bridging lemma inside
`Whatwg/Streams/Writable/Laws.lean`, the mask docstrings acceptance condition 5
names, and the `known-red.txt` entries once each battery is green.
`Whatwg/Ecma262/Promise.lean` must move `Capability` above `Reaction` so the
new field can name it; that is a declaration-order change and no signature
change, and `Whatwg/Ecma262/Jobs.lean` still imports only `Whatwg.Infra`.

This breaker edited no implementation module, no vendored byte, no generated
projection, no authored census input, no existing contract's text, and not
`test/counterexamples/REGISTER.md`, `SPEC-MANIFEST.md`, `PLAN.md`,
`COORDINATION.md`, or any document under `docs/` other than
`docs/PROMISE-DAG.md`'s new "Q3b addendum" section. Root imports and the
`known-red.txt` declarations are included with this packet; the trust
self-test checks that declaration in both directions.

## 12. Freeze receipt

Observed in this worktree at base `f700230`, Lean 4.33.1 from the unchanged
`lean-toolchain`, Windows x64, `LEAN_NUM_THREADS=1`.

`lake --wfail build Whatwg Gates` completes **164 jobs with exit code 0**: the
addendum touches no implementation module and no gate.

`lake exe vendorseal` PASS. `lake exe citations` PASS, 342 files scanned, no
line-numbered citation into a protected authored document.

`lake build WhatwgTest` fails, and the failing targets are **exactly the nine**
declared in `test/fixtures/trust-gate/known-red.txt`:

```text
✖ WhatwgTest.Ecma262.PromiseContract
✖ WhatwgTest.Ecma262.PromiseLaws
✖ WhatwgTest.Ecma262.PromiseFidelityContract
✖ WhatwgTest.Ecma262.JobsCompleteContract
✖ WhatwgTest.WebIdl.PromiseFidelityContract
✖ WhatwgTest.WebIdl.PromiseContract
✖ WhatwgTest.Ecma262.PromiseFidelityAxiomReport
✖ WhatwgTest.Ecma262.PromiseFidelityLaws
✖ WhatwgTest.Streams.PromiseBridge
```

`WhatwgTest.Ecma262.JobsContract`, `WhatwgTest.Ecma262.JobsLaws`,
`WhatwgTest.WebIdl.ExceptionsContract` and
`WhatwgTest.Ecma262.PromiseAxiomReport` all build green, which is the receipt
that the amendments changed statements and never names.

Lean's `maxErrors` is 100 and is read once per file, so the complete diagnostic
list for each module was collected separately with
`lake env lean -DmaxErrors=5000 <file>`:

| Module | Exit | Diagnostics | Classes |
| --- | ---: | ---: | --- |
| `WhatwgTest.Ecma262.PromiseFidelityContract` | 1 | 13 | 13 `lean.unknownIdentifier` |
| `WhatwgTest.Ecma262.PromiseFidelityLaws` | 1 | 78 | 68 `lean.unknownIdentifier`, 5 `lean.invalidField` (`.capability` on `Reaction`), 1 type mismatch, 2 application type mismatch, 2 invalid projection |
| `WhatwgTest.Ecma262.JobsCompleteContract` | 1 | 24 | 24 `lean.unknownIdentifier` |
| `WhatwgTest.WebIdl.PromiseFidelityContract` | 1 | 46 | 39 `lean.unknownIdentifier`, 5 invalid projection, 2 type mismatch |
| `WhatwgTest.Ecma262.PromiseFidelityAxiomReport` | 1 | 57 | 57 `lean.unknownIdentifier`, one per theorem obligation |
| `WhatwgTest.Ecma262.PromiseContract` | 1 | 3 | 3 type mismatch, one per amended signature |
| `WhatwgTest.Ecma262.PromiseLaws` | 1 | 20 | 5 `lean.unknownIdentifier` (`Reactions.mint`, `Reactions.clear`), 6 type mismatch, 2 application type mismatch, 7 function expected |
| `WhatwgTest.WebIdl.PromiseContract` | 1 | 11 | 4 `lean.unknownIdentifier`, 6 type mismatch, 1 function expected |
| `WhatwgTest.Streams.PromiseBridge` | 1 | 1 | 1 function expected (`Reactions.add` at five arguments) |

**253 diagnostics in total.** There is no parse error, no import error and no
failed instance synthesis anywhere. Every diagnostic is one of four classes and
each class has one cause:

- `lean.unknownIdentifier` and `lean.invalidField` — the addendum's declarations
  and the `Reaction.capability` field do not exist yet;
- type mismatch and application type mismatch — an amended ascription names a
  signature the landed implementation does not have (`Reaction.mk` at six
  arguments, `Reactions.add` at five, `performPromiseThen` and `react` at their
  new result types);
- function expected — the same, at an application site;
- invalid projection — the downstream consequence of a component whose type
  failed to elaborate, exactly the class the P4a, P5a and Q3 packets recorded
  as "missing-structure errors caused by missing types". No synthetic
  error-recovery term is admitted as a proof.

The 57 unknown constants of the axiom report equal, name for name, the 57
theorem ascriptions of the three law-bearing Q3b batteries, which is the
receipt that the report is neither short nor long.

**The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green.**
Its single diagnostic is at line 574, deep in the bridging half, so all 53
preservation `#check`s, all 13 `example`s and all six `inferInstance` checks
elaborate today, and acceptance condition 3 must reproduce that after the
builder's landing.

`WhatwgTest/Ecma262/PromiseFidelityContract.lean`'s
`inferInstance : Repr (Whatwg.Ecma262.Promise.Reaction Nat)` **elaborates
green** today, printing its type: that is the `E-50` receipt, and it must stay
green after `Reaction` gains its capability field.

Census cross-check performed at freeze, read-only, against the sealed bytes:
`op.performpromisethen`, `op.fulfillpromise`, `op.rejectpromise`,
`op.triggerpromisereactions`, `op.newpromisereactionjob`,
`op.createresolvingfunctions`, `record.promisereaction-records`,
`requirement.jobs.3`, `requirement.jobs.4`, `op.wait-for-all`,
`op.dfn-perform-steps-once-promise-is-settled`, `op.a-new-promise`,
`op.resolve`, `op.reject`, `op.upon-fulfillment` and `op.upon-rejection` were
read back at their frozen spans and every step number this addendum cites was
counted from those bytes. The two corrections of §7.4 are the result. No
vendored or generated byte was changed.

No `lake` command was run in the main checkout by this seat, and no Lake or
reviewer process from this freeze remains running. Every graph edge the base
packet opened stays as R-P20 left it; §"Q3b addendum" of `docs/PROMISE-DAG.md`
states which the addendum closes **on landing** and changes no landed row. This
addendum freezes what the Q3b builder must prove; it claims no implementation,
no coverage increase, no host observation and no equivalence.

## 13. Builder notes

Appended by the Q3b builder seat on branch `promise/q3b-builder`, based on
`38a806a` merged with `origin/main` (rulings R-P21 and R-P22, no conflict).
This section is the builder's; it records what the addendum did not anticipate.
It weakens, deletes and replaces nothing: no frozen ascription, law, mask,
decision or acceptance condition is changed, and all nine declared batteries
are green.

### B1 — the one ascribed type that binds a variable it does not mention

**Item.** `WhatwgTest/Ecma262/JobsCompleteContract.lean` line 73, the
`Jobs.RunToCompletion` signature ascription.

**Why the addendum did not anticipate it.** §7.2 ascribes
`RunToCompletion : ∀ {payload : Type}, Active → Prop`. `payload` appears in the
declaration's *body* — `∀ q : Queue payload, step active q = none` — and never
in its *type*, so the frozen ascription binds a variable the ascribed type does
not mention. `linter.unusedVariables` reports the binder, and ruling R-6 makes
every warning an error, so the module cannot build even though the ascription
elaborates and prints exactly the expected type. The freeze receipt could not
see this: with `RunToCompletion` unknown, elaboration stopped before the linter
ran, which is why §12 records 24 `lean.unknownIdentifier` diagnostics and
nothing else for this module. Nothing on the implementation side can reference
the binder: the ascribed type is `Active → Prop` whatever `RunToCompletion` is.

**Exact diagnostic**, on this branch against the landed implementation
(`lake env lean -DmaxErrors=100 WhatwgTest/Ecma262/JobsCompleteContract.lean`);
`lake build` reports the same text as an `error` under R-6:

```text
WhatwgTest/Ecma262/JobsCompleteContract.lean:73:5: warning: Variable name
`payload` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used
implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _payload

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```

In the same run every other ascription of the module elaborates and prints,
`RunToCompletion` itself included.

**Repair, and why it is not a weakening.** One
`set_option linter.unusedVariables false in` scoped to that single `#check`,
with a dated comment beside it. §1 of this addendum permits exactly this — "the
Q3b builder may repair elaboration but may not weaken, delete or replace a
frozen ascription, law, mask, decision or acceptance condition" — and
acceptance condition 1 asks for elaboration "with no edit to a statement". The
ascription's own text is byte-identical to the freeze and must still elaborate
at the frozen type; no statement, mask, law, decision or acceptance condition
changes, and the option's scope ends at that `#check`. The precedent in this
repository is `WhatwgTest/Audit/SpecCoverage.lean`. The alternative the linter
itself suggests — renaming the binder `_payload` — would edit the frozen text,
so it was not taken. **Offered for coordinator ratification**; a breaker-owned
rename of the binder would remove the need for the option.

### B2 — §10's arithmetic assumes no generated constant but the projection

**Item.** §10's expected figure, `12973 + 73 + 1 = 13047`. The measured pair on
this branch is **201 modules and 13079 declarations** (1477 in the Gates
tooling tree).

**Why the addendum did not anticipate it.** §10 counts "the generated
projection `Reaction.capability`" and nothing else. Lean 4 also mints, inside
the audited tree and therefore inside the audit's total, an equation lemma for
every definition a proof unfolds with `simp` or `rw`, a matcher with its case
analysis and splitter for every definition that pattern-matches on a new
scrutinee shape, and a `Repr` instance for every `deriving Repr`. The
addendum's fifteen new functions include ones that pattern-match and ones that
proofs unfold, so a delta of exactly `73 + 1` was not reachable. This is an
arithmetic gap in §10, not an extra declaration: **every authored name is
exactly the frozen list**, 73 of them, verified name for name.

**The measurement.** Constants owned by the six touched modules, dumped from
the environment at `f700230` and at this branch's head with a scratch
`#dump_decls` command over `Environment.constants`:

| | `f700230` | this branch | delta |
| --- | ---: | ---: | ---: |
| the six touched modules' constants | 1558 | 1664 | +106 |
| the audit's total | 12973 | 13079 | +106 |

**107 constants appear and 1 disappears.** The one that disappears is
`Whatwg.WebIdl.Promise.react.match_1`: `react` is now
`performPromiseThen … |>.map …` and pattern-matches on nothing, so its matcher
is gone. `12973 + 107 − 1 = 13079`.

The 107 split **74 + 33**, and the 74 are §10's table exactly:

| Tree | Types | Functions and predicates | Theorems | Total |
| --- | ---: | ---: | ---: | ---: |
| `Whatwg/Ecma262/Promise.lean` | 1 | 8 | 32 | 41 |
| `Whatwg/Ecma262/Jobs.lean` | 0 | 3 | 11 | 14 |
| `Whatwg/WebIdl/Promise.lean` | 0 | 4 | 13 | 17 |
| `Whatwg/Streams/**`, additive | 0 | 0 | 1 | 1 |
| **authored total** | **1** | **15** | **57** | **73** |
| the generated projection `Reaction.capability` | — | — | — | 1 |
| **§10's expected total** | | | | **74** |

The remaining **33** are Lean-generated and carry no content:

- **2** the `deriving Repr` on `Capability` that B3 forces:
  `instReprCapability` and `instReprCapability.repr`;
- **3** matchers and case analyses for the new pattern-matching definitions:
  `Jobs.completeJob.match_1`, `Jobs.completeJob._sparseCasesOn_1` and
  `Promise.SettlementTrace.firstRejection.match_1`;
- **12** match splitters with their equations, six raised in
  `Whatwg/Ecma262/Promise.lean` and six again in
  `Whatwg/Streams/Writable/Laws.lean`, for `List.findSome?.match_1` and
  `SettlementTrace.firstRejection.match_1` (`.eq_1`, `.eq_2` and `.splitter`
  each, all private);
- **16** equation lemmas and simp auxiliaries raised by unfolding a definition
  inside a proof: `Jobs.RunCondition.eq_1`, `Jobs.startJob.eq_1`,
  `Jobs.startJob.eq_2`, `Promise.ResolvingFunctions.callResolveSelf.eq_1`,
  `Promise.ResolvingFunctions.callSettle.eq_1`,
  `Promise.ResolvingFunctions.callSettle.eq_2`,
  `Promise.SettlementTrace.firstRejection.eq_1`,
  `Promise.Table.settleTraced.eq_1`, `Promise.reactionHandlerResult.eq_1`,
  `Promise.runReactionJob.eq_1`,
  `Promise.Reactions.clear_other_promise._simp_1_1`,
  `WebIdl.Promise.resolve.eq_1`, `WebIdl.Promise.reject.eq_1`,
  `WebIdl.Promise.resolveThrough.eq_1`, `WebIdl.Promise.rejectThrough.eq_1`,
  and `WebIdl.Promise.waitForAllTraced.eq_1`.

`2 + 3 + 12 + 16 = 33`, and `74 + 33 = 107`. No inductive, no structure and no
authored name outside §10's list was added, which is what §10's defect test is
for.

**Consequence for §10.** The arithmetic reads

```text
12973
  + 73  authored, exactly §10's table
  +  1  the generated projection Reaction.capability
  + 33  further Lean-generated constants, enumerated above
  -  1  Whatwg.WebIdl.Promise.react.match_1, no longer needed
  = 13079
```

and the module count is §10's exactly, `196 → 201`.

### B3 — `Reaction`'s `deriving Repr` forces `Repr Capability`

**Item.** `WhatwgTest/Ecma262/PromiseFidelityContract.lean`'s
`#check (inferInstance : Repr (Whatwg.Ecma262.Promise.Reaction Nat))`, §3's
`E-50` receipt.

**Why the addendum did not anticipate it.** §3 requires that re-check to stay
green after `Reaction` gains its field, and §8 requires `Reaction` to stay
`Repr`-only. `Capability` derived `DecidableEq` alone, so with the new
`capability : Option Capability` field the deriving handler cannot build
`Reaction`'s `Repr`.

**Exact diagnostic**, before the repair:

```text
Whatwg/Ecma262/Promise.lean:492:11: error(lean.synthInstanceFailed): failed to
synthesize instance of type class
  Repr (Option Capability)
```

**Repair, and why it is not a weakening.** `Capability` derives
`DecidableEq, Repr`. It is purely additive: the base packet's battery ascribes
`inferInstance : DecidableEq Capability` and that is unchanged, and `Capability`
is a triple of `Nat` identities, so `Reaction` still gains **no** `DecidableEq`
and `E-29`'s and `E-50`'s constraint holds. The two generated constants are
counted in B2. The `E-50` re-check is green.

### B4 — what the addendum predicted and this seat confirms

`Table.settleAndTrigger`'s job-queue component is byte-identical to the base
packet's, so `Table.settleAndTrigger_pending`'s M2 content is unchanged, as
§4's row 9 says. `Writable.settlementTrace`'s body is unchanged and
`settlementTrace_bridge` needed no projection: after the `abbrev` it already
*is* `SettlementTrace Unit (Boundary.Exception ε)`, which is what §6 predicted.
The ripple into `Whatwg/Streams/Transform/**` is `Reactions.add`'s fifth
argument in the base packet's own view `Transform.reactions` and in three
bridging proofs; it added and removed no constant there. Every gap §1 lists is
still open and recorded against its gap id in the module docstrings.
