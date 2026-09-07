# Promise-layer adversarial packet (`PROMISE-PG-FIRST`, slice Q3)

Breaker-authored 2026-09-07 on `promise/q3-breaker`. Contract:
`test/contracts/promise-first-packet.contract.md`. Graph:
`docs/PROMISE-DAG.md`.

Each row is a tempting implementation of the first promise packet and the
frozen statement that rejects it. The statements live in
`WhatwgTest/Ecma262/{PromiseContract,JobsContract,PromiseLaws,JobsLaws}.lean`,
`WhatwgTest/WebIdl/{PromiseContract,ExceptionsContract}.lean` and
`WhatwgTest/Streams/PromiseBridge.lean`; they are ascriptions and laws, not
finite witness modules. This packet freezes **no** executable witness module:
every attack below is discriminated by a quantified production statement, and
adding finite witnesses is separate later evidence, not a substitute for them.

The stable prefix is `WS-PROM-CE-`. The rows of
`test/counterexamples/REGISTER.md` are the coordinator's to add at integration;
this breaker does not edit the central register.

| ID | Mutant | Rejecting statement |
| --- | --- | --- |
| WS-PROM-CE-001 | collapse `PullAnswer` and `PullReturn` into `PromiseState Unit ε`, since they are isomorphic | decision 6; `Whatwg.Streams.Writable.sinkAnswer_eq`, `sinkReturn_eq`, `sinkReturnToShared_eq`, `sinkReturn_roundtrip` and the six preservation `example`s of `PromiseBridge.lean`, which must close by `rfl` |
| WS-PROM-CE-002 | apply `move` to a function, so a Streams name becomes an `abbrev` over a general function | decision 5 and inventory condition 3; the six equation-lemma `example`s of `PromiseBridge.lean` re-derive `lookupPromise_eq`, `markHandled_eq`, `Transform.lookupPromise_eq` and the three `subscriptionPromise_*` receipts by `rfl`. An `abbrev` has one equation, `f = General.f`, and `simp [f]` in the four `attribute [local simp]` sets stops rewriting |
| WS-PROM-CE-003 | give the general promise state one type parameter, fixing the value to `Unit` | `E-22`; `Whatwg.Streams.Readable.readTable` is ascribed at value `ReadResult α`, and `Whatwg.Ecma262.Promise.State : Type → Type → Type` |
| WS-PROM-CE-004 | give `Outcome` two parameters, so `Outcome.fulfilled` carries a value | `E-02`; `Whatwg.Streams.Readable.PullAnswer.fulfilled : ∀ {ε : Type}, PullAnswer ε` takes no argument, and every `.fulfilled` in `Whatwg/Streams/**` resolves against it |
| WS-PROM-CE-005 | reproduce ES2026's assertion literally, making `settle` partial or undefined on a settled promise | decision 7; `Whatwg.Ecma262.Promise.Table.settle_other` requires the identity on a non-pending cell, and `settle_assert` recovers the assertion as a side condition |
| WS-PROM-CE-006 | represent the table as a replacing map, so allocating overwrites an earlier cell | `E-13`, `E-43`; `Table.fresh_old`, `Table.fresh_eq`, and `Writable.freshPromise_bridge` |
| WS-PROM-CE-007 | reuse an identity, or advance the cursor by something other than one | `E-14`, `E-23`, decision 3; `Table.fresh_id`, `Table.fresh_next`, and the P6 `Transform.initial` and P7 run witnesses that fix concrete identities |
| WS-PROM-CE-008 | implement the job queue as a stack: prepend on enqueue, or consume the newest | `E-45`; `Whatwg.Ecma262.Jobs.Queue.enqueue_eq`, `Queue.dequeue_cons` and the general FIFO law `Queue.dequeue_fifo` |
| WS-PROM-CE-009 | run a job while a synchronous callback frame is live, or while another job is running | `G-08`; `Jobs.step_blocked`, `Jobs.RunCondition_iff`, and the three component bridges `Writable.tick_dequeue_bridge`, `Readable.runPullJob_dequeue_bridge`, `Transform.tick_dequeue_bridge`, whose hypotheses are the three Streams spellings of the empty execution-context stack |
| WS-PROM-CE-010 | let a job scheduled during a run overtake one already scheduled | `requirement.hostenqueuepromisejob.3`; `Queue.dequeue_fifo` with a nonempty `later`, `Jobs.run_fifo` and `Jobs.hostEnqueuePromiseJob_order` |
| WS-PROM-CE-011 | trigger a reaction twice, or notify out of registration order | `E-33`, `G-01`; `triggerReactions_order` (mask M2) and `triggerReactions_once` |
| WS-PROM-CE-012 | keep one undifferentiated reaction list and present it as ES2026's two | decision 8, `G-01`; `Reactions.add_fulfill`, `Reactions.add_reject`, `Reactions.add_paired`, `Reactions.registered_eq` and `Transform.reactions_registered` |
| WS-PROM-CE-013 | make `react` total, returning a value for a promise identity with no cell | `E-31`; `WebIdl.Promise.react_missing`, which keeps the Streams `Option` and records the difference from `PerformPromiseThen` rather than smoothing it |
| WS-PROM-CE-014 | run the handler immediately when `react` finds a settled promise, instead of queueing a reaction job | `E-31`, `E-37`; `react_fulfilled` and `react_rejected` (mask M2), whose right-hand sides are `Queue.enqueue` |
| WS-PROM-CE-015 | derive `DecidableEq` unconditionally on the general reaction or job record | `E-29`, `E-50`; `Transform.Reaction` and `Transform.Job` derive `Repr` only, so `inferInstance : Repr (Reaction Nat)` is ascribed and no `DecidableEq` is |
| WS-PROM-CE-016 | model Web IDL simple exceptions without an allocation identity, as the pinned text does | R-P14, `E-59`; `Exceptions.Exception.simple_eq_iff`, `Exception.identity_simple`, `Boundary.Exception.toWebIdl_injective`, and the frozen `nested_invalid_sizes_fresh_errors` witness in `Whatwg/Streams/Readable/Reentrancy.lean` |
| WS-PROM-CE-017 | re-point `Boundary.Exception` as an `abbrev` of the general exception type | `E-59` is `generalize`, not `move`; the four `Boundary.Exception` ascriptions of `PromiseBridge.lean`'s preservation half keep `.rangeError id` resolving for all 69 dependent theorems |
| WS-PROM-CE-018 | call the settled predicate `wait for all` | `E-55`, `G-06`; `AllSettled` and `waitForAll` are separate names with separate laws, and `waitForAll_success`/`waitForAll_failure` state the ordered result and the short-circuit the predicate does not have |
| WS-PROM-CE-019 | move `handled` into the cell and drop the relation to the Streams identity list | decision 9; `Writable.handled_bridge` and `Writable.markHandled_bridge` |
| WS-PROM-CE-020 | ignore `[[AlreadyResolved]]`, so a resolving function can settle its promise twice | `G-03`; `ResolvingFunctions.callResolve_alreadyResolved` and `callReject_alreadyResolved` |
| WS-PROM-CE-021 | report a later rejection instead of the first when `wait for all` short-circuits | `waitForAll_failure` (mask M2), whose hypothesis fixes every earlier identity as fulfilled |
| WS-PROM-CE-022 | give the `DOMException` name table 33 entries by adding `QuotaExceededError`, or repeat a name | R-P10; `Exceptions.Name.all_length = 32`, `Name.all_nodup`, `Name.all_complete`. At this pin `QuotaExceededError` is a derived interface (`idl.quota-exceeded-error`, 213527..213598) and the census has no `type.` row for it |

Two attacks the packet deliberately does **not** discriminate, because their
subject is out of scope and a statement about them would overclaim:

- adoption of an arbitrary thenable (`G-05`, `op.newpromiseresolvethenablejob`,
  2705599..2707541). `Transform.Completion.adopt` (`E-35`) adopts an internal
  identity and is `keep`; no statement here presents it as adoption.
- a rejection tracker reading the handled bit (`G-02`,
  `hook.host-promise-rejection-tracker`, 2701220..2702791). Nothing reads the
  bit in this packet, and `markHandled_state` says only that marking does not
  change the promise state.

Verification: the rejecting statements are checked by the six batteries' own
narrow commands, recorded in the contract's "Freeze receipt". No host was run
and no WPT case was replayed for this packet.

## Q3b fidelity addendum, 2026-09-07, branch `promise/q3b-breaker`

Appended by the Q3b addendum breaker seat, based on `f700230`. Addendum:
`test/contracts/promise-first-packet-q3b.contract.md`. The twenty-two rows
above are frozen and unchanged; these sixteen are new, one per fidelity finding
F1–F6 of ruling R-P20 and one per minor it lists. `test/counterexamples/REGISTER.md`
stays the coordinator's and is not edited here.

Every row below is `SEEDED`: the attack and the statement that must reject it
are frozen now, and the statement itself is red until the Q3b builder lands it.
Nine of them attack the landed Q3 implementation *as built* rather than a
hypothetical mutant — the mutant is what is in the tree at `f700230` — and each
of those says so. The rejecting statements live in
`WhatwgTest/Ecma262/{PromiseFidelityContract,PromiseFidelityLaws,JobsCompleteContract}.lean`
and `WhatwgTest/WebIdl/PromiseFidelityContract.lean`, plus the Q3 ascriptions
this addendum amends.

Byte offsets are 0-based, ends exclusive, into
`vendor/ecma262-0248456c/spec.html` and
`vendor/whatwg-webidl-a652053f/index.bs`. No line number is cited.

| ID | Mutant | Rejecting statement |
| --- | --- | --- |
| WS-PROM-CE-023 | set `[[PromiseIsHandled]]` only on the branches that enqueue a job, leaving a promise that was still pending when `PerformPromiseThen` ran unmarked. **This is the landed Q3 behaviour**: `performPromiseThen`'s pending branch returns `t`, and `performPromiseThen_pending` freezes the omission | F1; `op.performpromisethen` (2740635..2743669) step 12 sets `[[PromiseIsHandled]]` to *true* after the three-way branch, not inside it. `Whatwg.Ecma262.Promise.performPromiseThen_handled` (mask M1) quantifies over all three branches, `Table.markHandled_marked` supplies the cell law, and the amended `performPromiseThen_pending` marks the promise |
| WS-PROM-CE-024 | on a settled branch, append a reaction to both lists and set only the triggered side's phase, leaving the opposite-side entry in the `waiting` phase for a promise that can never trigger it again. **This is the landed Q3 behaviour** in both `performPromiseThen` and `WebIdl.Promise.react` | F2; `op.performpromisethen` steps 10 and 11 create a PromiseReaction Record and enqueue a job for it and append it to no list — only step 9's pending branch appends, and it appends both. `Reactions.mint_fulfill`, `mint_reject` (neither list changes), `mint_no_waiting` (mask M1) and the amended `performPromiseThen_fulfilled`/`_rejected` and `react_fulfilled`/`react_rejected` |
| WS-PROM-CE-025 | clear only the list that was triggered, leaving the other list's registrations on the settled promise in the `waiting` phase, and present `triggerReactions_other_kind` as the law that says so. **This is the landed Q3 behaviour**: `Table.settleAndTrigger` advances only the triggered list | F3; `op.fulfillpromise` (2695419..2696230) steps 4 and 5 and `op.rejectpromise` (2699323..2700252) steps 4 and 5 each set **both** `[[PromiseFulfillReactions]]` and `[[PromiseRejectReactions]]` to *undefined*. `Reactions.clear_waiting`, `Table.settleAndTrigger_cleared` (mask M1) and the amended `Table.settleAndTrigger_pending`. `triggerReactions_other_kind` keeps its statement — `op.triggerpromisereactions` really does not touch the other list — and gains the dated annotation that it is a law about TRIGGER alone |
| WS-PROM-CE-026 | omit `[[Capability]]` from the reaction record, so `performPromiseThen`'s capability argument is consumed by `Capability.promise` and stored nowhere and the `G-03` resolving functions settle nothing. **This is the landed Q3 behaviour** | F4; `record.promisereaction-records` (2690445..2692671) lists `[[Capability]]` first (field row 2691475..2691802), and `op.newpromisereactionjob` (2702885..2705591) reads it to resolve or reject the derived promise. `Whatwg.Ecma262.Promise.Reaction.capability`, the amended `Reaction.mk` and `Reactions.add`, `Reactions.add_capability`, `mint_capability`, and `runReactionJob_resolve`/`_reject` |
| WS-PROM-CE-027 | make the reaction job run its handler: store the handler as a Lean function, or let `runReactionJob` compute the handler's result | F4 and DB-02; `AGENTS.md`'s representation rule forbids a stored body, and `field.promisereaction-records.Handler` (2692151..2692611) is a JobCallback Record or `~empty~`, a descriptor. `Reaction.handler : Option body` stays first-order, and `reactionHandlerResult` takes the result as a decision argument: `reactionHandlerResult_handler` returns the decision unexamined and `reactionHandlerResult_empty` (mask M1) is the `~empty~` case of `op.newpromisereactionjob` inner steps 4a and 4b |
| WS-PROM-CE-028 | claim `requirement.jobs.3` from `run`'s recursion alone, with `Active.job` produced by no operation and `run` never consulting the activation. **This is the landed Q3 state**: the `semantics` edge names COMPLETE and nothing realizes it | F5; `requirement.jobs.3` (626357..626479) — "Once evaluation of a Job starts, it must run to completion before evaluation of any other Job starts in an agent". `Whatwg.Ecma262.Jobs.startJob` produces `Active.job` (`startJob_active`), `RunToCompletion` is the specification, `run_to_completion` is the realizer theorem, and `run_to_completion_nonvacuous` refuses a vacuous discharge. `startJob_run_agree` keeps `run_fifo`, `run_split` and both Streams `tick_job_fifo` corollaries unchanged |
| WS-PROM-CE-029 | require every argument promise to be settled before reporting a failure, so a rejection while a sibling is still pending answers `pending`. **This is the landed Q3 behaviour**: `waitForAll` guards on `allSettled` | F6; `op.wait-for-all` (353239..354879) sets `rejected` and performs `failureSteps` inside the rejection handler, which runs on the first rejection to settle, with no reference to `fullfilledCount` or `total`. `Whatwg.WebIdl.Promise.waitForAllTraced_failure_pending` (mask M2) fixes a sibling as pending and still requires `failure` |
| WS-PROM-CE-030 | report the first rejection in **argument** order rather than the first to settle, and label the result M2. **This is the landed Q3 behaviour**: `waitForAll` uses `List.findSome?` over `ids` | F6; the same anchor. `waitForAllTraced_failure` (mask M2) quantifies over the settlement trace, not the argument list, and its hypothesis fixes the earlier *trace* entries. `waitForAll_failure` and `waitForAll_success` keep their statements and are relabelled M1 by this addendum, because argument order is neither a settlement order nor a queue order under §7's rule |
| WS-PROM-CE-031 | carry the settlement order in a second promise table, or in a field of `Table` that changes `Table.mk`'s arity | F6 and R-P12 (no shadow table); the trace is `Whatwg.Ecma262.Promise.SettlementTrace`, a first-order list of settled identities with their outcomes, and `Table.settleTraced_table` (mask M1) requires `(settleTraced t tr id r).1 = Table.settle t id r`, so the table is the same table. `Whatwg.Streams.Writable.settlementTrace_bridge` (mask M2) relates it to `E-71`'s `Writable.settlementTrace`, whose content is unchanged |
| WS-PROM-CE-032 | give each resolving function its own `[[AlreadyResolved]]` flag, so calling `[[Resolve]]` leaves `[[Reject]]` armed | minor; at this pin `op.createresolvingfunctions` (2692679..2695411) has no `[[AlreadyResolved]]` record at all — step 1 creates one shared Record `{ [[Value]]: toResolve }` that both closures capture, and each closure's step 3 sets that shared `[[Value]]` to `~empty~`. `ResolvingFunctions.callResolve_disables_reject` and `callReject_disables_resolve` (mask M1). The field keeps the name `alreadyResolved` with the dated anachronism note; only the citation changes |
| WS-PROM-CE-033 | resolve a promise with itself and fulfil it, because the general `value` cannot be compared to a promise identity | minor; `op.createresolvingfunctions` resolve steps step 4 rejects with a newly created *TypeError* when `SameValue(resolution, promise)` is *true*. `ResolvingFunctions.callResolveSelf_self` (mask M1) states the branch, and `callResolveSelf_other` answers `none` rather than guessing, because the value universe in which a promise is one value among others is `G-04` and thenable adoption is `G-05` |
| WS-PROM-CE-034 | present `newPromise`'s `Nat` as what `op.a-new-promise` returns | minor; `op.a-new-promise` (347604..347946) step 2 returns `NewPromiseCapability(constructor)`, a PromiseCapability Record. `Whatwg.WebIdl.Promise.newPromiseWithCapability` is that form and `newPromise_capability_promise` (mask M1) exhibits the landed identity as the capability's `[[Promise]]`. `newPromise` keeps its signature: eighteen `Whatwg/Streams/**` call sites use the identity |
| WS-PROM-CE-035 | present the direct table settle as `op.resolve` or `op.reject` | minor; `op.resolve` (349216..349783) step 3 and `op.reject` (349785..350073) step 1 both `Call` the capability's `[[Resolve]]`/`[[Reject]]`, so they inherit the one-shot marker that a direct settle does not have. `Promise.resolveThrough`, `rejectThrough` and `resolveThrough_resolve`/`rejectThrough_reject` (mask M1), which state exactly when the two agree |
| WS-PROM-CE-036 | justify `Reaction.handler : Option body` by Web IDL `react` | minor; `op.dfn-perform-steps-once-promise-is-settled` (350075..352408) steps 1 to 4 build **both** `onFulfilled` and `onRejected` unconditionally, so Web IDL `react` never registers an empty handler. The `~empty~` handler comes from `op.performpromisethen` steps 3 and 5, the `IsCallable` test. The addendum corrects §4.6's citation; `uponFulfillment_eq` and `uponRejection_eq` keep their statements and the `none` they freeze is recorded as a `G-11` modelling restriction, not as the pinned text |
| WS-PROM-CE-037 | label a theorem M2 because it mentions a list, or M1 because it is easy | minor; §7's rule is that the *statement* must observe the order in which settlements happen or in which reaction jobs enter the queue. `Jobs.run_cons` observes job delivery order and stays M2, so §7's twelve become thirteen; `Whatwg.Streams.Writable.attachSink_pending_jobs` has `jobQueue s` on both sides and observes no order, so it becomes M1; `waitForAll_failure` and `waitForAll_success` observe argument order only and become M1. Each amendment is dated in the battery beside the ascription |
| WS-PROM-CE-038 | add an addendum ascription that cites neither an inventory row nor a gap id, as `E-50` and `E-51` were cited in the contract, the graph and this file but in no battery | R-P12 and acceptance condition 1; every ascription of the four Q3b batteries names an inventory row with its reuse mode or a gap id. `E-50` (`Transform.Job`, `Repr`-only) is cited on `Reaction.capability` and the `inferInstance : Repr (Reaction Nat)` re-check, because the new field must not force `DecidableEq`; `E-51` (`Transform.runJob`, generalize) is cited on `runReactionJob` and on `Jobs.startJob`, which are the general "run one job" step its bridge was deferred against |

Two attacks this addendum still deliberately does **not** discriminate, for the
same reason as the base packet: thenable adoption (`G-05`,
`op.newpromiseresolvethenablejob`, 2705599..2707541), which is why
`callResolveSelf` answers `none` off the self branch rather than adopting; and
a rejection tracker reading the handled bit (`G-02`,
`hook.host-promise-rejection-tracker`, 2701220..2702791), which is why
`performPromiseThen_handled` says only that the bit is set and never what reads
it. `op.performpromisethen`'s rejected branch also calls
`HostPromiseRejectionTracker(promise, "handle")` when the bit was *false*; that
step is `G-02` and no statement here covers it.

Verification: the rejecting statements are checked by the four Q3b batteries'
own narrow commands and by the amended Q3 ascriptions, recorded in the
addendum's "Freeze receipt". No host was run and no WPT case was replayed.

## Q4 amendment, 2026-09-07, branch `promise/q4-amend`

Appended by the Q4 amendment breaker seat, based on `promise/q4-builder` at
`746032c` merged with `origin/main`. Packet:
`test/contracts/configuration-ordering.contract.md`, its "Q4 amendment"
section. The thirty-eight rows above are frozen and unchanged; this one is new.
`test/counterexamples/REGISTER.md` stays the coordinator's and is not edited
here, so the row is `SEEDED` and its register entry is owed at landing.

The row is not hypothetical. The mutant **is the statement the Q4 packet froze
at `promise/q4-breaker` `9ae662a`**, which the first builder pass found false
and correctly refused to prove (builder note B3, contract §11.1). The rejecting
statements are the restated bridge and the new serial lemma of amendment A4.

Byte offsets are 0-based, ends exclusive, into
`vendor/ecma262-0248456c/spec.html`. No line number is cited.

| ID | Mutant | Rejecting statement |
| --- | --- | --- |
| WS-PROM-CE-039 | state the reaction half of the configuration's `notifySettled` as a plain equality of registration lists with `op.triggerpromisereactions`' result, so that the configuration's `ReactionPhase.queued` payload is claimed to be the **registration id**. **This is the Q4 packet's own frozen `notifySettled_reactions_bridge`.** The mutant erases the distinction decision 2 of the contract's §3.3 makes between the two monotone supplies, and would let a later FIFO or replay proof read a registration id where a job serial is scheduled. Witness: `c.nextJob = 7`, one registration `r` with `r.id = 0`, `r.promise = id`, `r.phase = .waiting`, and `Writable.lookupPromise c.writable id = some (.fulfilled ())`; then `(notifySettled c id).registrations = [{ r with phase := .queued 7 }]` while `(triggerReactions (reactions c) id .fulfill (.ok ()) Queue.empty).1.fulfill = [{ r with phase := .queued 0 }]`. A second, independent witness for the `Nodup` clause: two registrations sharing `id = 0` whose `promise` fields differ, one equal to `id` and one not — the configuration's fold advances both, because `setRegistrationPhase` selects by registration id alone, while `op.triggerpromisereactions`' filter `r.promise == promise && r.phase == waiting` advances one | `op.triggerpromisereactions` (2700260..2701212) and `field.promisereaction-records.Type` (2691815..2692138); contract §2.7 and decision 2 of §3.3, ratified by R-P25 ("`ReactionPhase.queued`'s payload stays the job serial in the configuration and the registration id in the landed ECMA-262 operations; Q4 keeps its two cursors"). Three statements reject it: `Whatwg.Streams.Semantics.Ordering.notifySettled_reactions_bridge` as amended, which equates the two lists **only** modulo `reactionErase` and **only** under `(c.registrations.map (·.id)).Nodup` (mask M1); `Whatwg.Streams.Semantics.Ordering.notifySettled_queued_serial`, which recovers the payload the erasure drops and ties it to the token FIFO's own supply — every triggered registration is left `.queued serial` for a `serial ≥ c.nextJob` whose `.observer` token the same notification appended to `jobQueue` (mask M2); and `Whatwg.Streams.Semantics.Ordering.phaseErase_eq`, which pins the erasure so the bridge cannot be widened back into the mutant by redefining it |

Verification: the three rejecting statements are frozen red in
`WhatwgTest/Streams/Semantics/{OrderingContract,OrderingLaws}.lean` and named
in `WhatwgTest/Streams/Semantics/OrderingAxiomReport.lean`; the second builder
pass proves them. The two witnesses above are stated, not executed: no
`WS-CONFIG` witness module exists yet, and the configuration counterexample
tranche remains the `counterexamples` edge of `docs/CONFIGURATION-DAG.md`. No
host was run and no WPT case was replayed.
