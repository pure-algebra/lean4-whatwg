# Receipts log of `PROMISE-PG-FIRST`

This log holds the history of `docs/PROMISE-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/PROMISE-DAG.md`.

## Promise-layer proof graph (`PROMISE-PG-FIRST`, slice Q3)

Moved verbatim from the freeze-time status paragraph under the title of `docs/PROMISE-DAG.md` at `325d5d5`; a current status paragraph replaces it there.

Every edge is `required-open` at this freeze except the two the packet declares
`not-applicable` with a reason. No edge closes from a compiling battery.

## Ten edges

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

| Edge | Status | Required evidence / reason |
| --- | --- | --- |
| identity | required-open | the exact ascriptions of the six batteries; the moved carriers' constructor and instance census, checked *through* the Streams `abbrev`s; the generated declaration snapshot joins every new public declaration to exactly one record above. Closes on: PSTATE, PRESULT, FULFILL, REJECT |
| construction | required-open | `Table.empty`/`.fresh` retention and cursor laws; `Queue.empty`/`.enqueue`; `newPromiseCapability`; the three Streams tables and three job lists exhibited as instances. Reachable-state and cross-owner freshness invariants stay open. Closes on: CAPREC, NEWCAP, HOSTENQ, JOBCB |
| semantics | required-open | `react`'s four branches, `triggerReactions`' order and once-only laws, `settleAndTrigger`, `performPromiseThen`'s three branches, `step`/`run` under the named run condition. The global configuration, the M2 mask projection and the bounded runner are P8 and stay open. Closes on: REACT, UPONF, UPONR, THEN, TRIGGER, REACTJOB, RUNCOND, ONEJOB, COMPLETE |
| laws | required-open | all 125 theorem ascriptions of `WhatwgTest/Ecma262/{Jobs,Promise}Laws.lean`, `WhatwgTest/WebIdl/{Promise,Exceptions}Contract.lean` and the bridging half of `WhatwgTest/Streams/PromiseBridge.lean`, each under the mask its docstring names. Closes on: ORDER, RESOLVE, REJECTOP, NEWP, RESOLVEDW, REJECTEDW, HANDLEDOP, WAITALL |
| representation | required-open | promise identities stay `Nat` with monotone cursors (decision 3); reactions and jobs are first-order descriptors, never stored bodies; the two reaction lists with their one-list view (decision 8); the handled bit as a per-cell field with its identity-list bridge (decision 9); the exception universe with allocation identity preserved (R-P14). Closes on: REACTREC, PFULFILL, PREJECT, PHANDLED, SIMPLEX, EXCOBJ |
| counterexamples | required-open | the twenty-two `WS-PROM-CE-*` rows of `test/counterexamples/promise/ATTACKS.md`, each linked to the production statement that rejects it. The central register rows are the coordinator's to add at integration; this packet does not edit `test/counterexamples/REGISTER.md` |
| bridges | required-open | the 29 bridging lemmas, plus the whole preservation half of `WhatwgTest/Streams/PromiseBridge.lean` staying green: every existing Streams name elaborates with its old type, every named `rfl` receipt still closes by `rfl`, and every derived instance is still found through the reducible `abbrev`. Host profiles and WPT settlement-order replay are P8 and stay open |
| targets | not-applicable | Q3 has no lowering and no generated code. P11 owns the TypeScript target obligation, and no declaration in this packet is reached by it |
| trust | required-open | the 125 named receipts of `WhatwgTest/Ecma262/PromiseAxiomReport.lean` inside the R-11 ceiling (`propext`, `Quot.sound`, `Classical.choice`), the exhaustive root audit, the narrow builds, the full build and every repository gate. `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the `native_decide` auxiliaries appear nowhere |
| coverage | not-applicable at this freeze, then required-open | the two censuses have no numerator module until `WhatwgTest/Audit/{WebIdl,Ecma262}/SpecCoverage.lean` exists, which the plan schedules inside Q3's builder fence and this breaker does not author. Citing a row id in a battery docstring anchors a declaration and moves no coverage state; every row named here stays `absent` at this freeze. The edge becomes `required-open` the moment a numerator module lands |

`targets` is the only permanently not-applicable edge. `coverage` is
not-applicable only because its numerator module does not exist yet; the
builder's landing must reopen it rather than inherit the label.

## Q3 landing, 2026-09-07, branch `promise/q3-builder`

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Appended by the Q3 builder seat. The declaration and statement rows above are
frozen and unchanged; this section records only which edges the landing closes,
with the theorem names that close them, and which stay open. Full commands,
results and per-move commits are in the "Q3 landing receipt" of
`docs/PROMISE-PACKAGE-PLAN.md`; the builder's exceptions are §15 of the
contract.

Nothing here closes an edge from a compiling battery alone. An edge closes only
when every item its "required evidence" column names is delivered, and the
column's own explicit deferrals ("… are P8 and stay open") are read as outside
Q3's obligation rather than as unmet.

| Edge | Status after the landing | What closed it, or what is still missing |
| --- | --- | --- |
| identity | **required-open** | The first two evidence items are delivered: the exact ascriptions of all six statement batteries elaborate (`JobsContract` 27, `JobsLaws` 20, `PromiseContract` 88, `PromiseLaws` 44, `WebIdl/PromiseContract` 33, `WebIdl/ExceptionsContract` 69), and the moved carriers' constructor and instance census is checked *through* the Streams `abbrev`s by the preservation half of `PromiseBridge` (7 constructor `#check`s and 6 `inferInstance` checks). The third is not: **this repository has no generated declaration snapshot**, so no artifact joins each new public declaration to exactly one record above. The edge stays open on that item alone. Builder note B1 records that the seven constructor ascriptions needed seven reducible aliases to elaborate at all |
| construction | **required-open** | `Table.empty_eq`, `Table.fresh_eq`, `fresh_id`, `fresh_next`, `fresh_old` (retention), `fresh_get`, `Queue.empty_eq`, `Queue.enqueue_eq`, `enqueueAll_eq` and `newPromiseCapability_eq` are proved, and the three job lists are exhibited as instances (`Writable.jobQueue_eq`, `Readable.jobQueue_eq`, `Transform.jobQueue_eq`). Two of the "three Streams tables" are exhibited (`Writable.promiseTable_eq`, `Readable.readTable_eq`); `E-22`'s operation-level generalization is deferred to Q4 with the reason the contract states — every `readPromises` update is an inline `List.map` in `Readable/DefaultController.lean` and `DefaultReader.lean`, and turning those five into `Table` calls would change a Streams definition body. Reachable-state and cross-owner freshness invariants stay open as the column already says |
| semantics | **required-open** (reopened at the landing review, ruling R-P20) | The builder's evidence stands for `react`'s four branches, `triggerReactions`, `settleAndTrigger`, `performPromiseThen`'s branches and `step`/`run` under `Jobs.RunCondition`, but `requirement.jobs.3` (COMPLETE, 626357–626479) is listed in this edge's close-on set and has no declaration or discharge-by-typing statement in `Whatwg/Ecma262/Jobs.lean`; `Active.job` is produced by no operation and `run` never consults the activation. The Q3b addendum either realizes it or states the typing discharge. Evidence as landed: `WebIdl.Promise.react_pending`, `react_fulfilled`, `react_rejected`, `react_missing` (four branches); `Promise.triggerReactions_order` (M2) and `triggerReactions_once` (M1), with `triggerReactions_other_promise` and `_other_kind`; `Table.settleAndTrigger_pending` (M2) and `_other`; `performPromiseThen_missing`, `_pending`, `_fulfilled`, `_rejected` (three branches and the partial case); `Jobs.step_checkpoint`, `step_blocked`, `run_zero`, `run_nil`, `run_cons`, `run_split` under `Jobs.RunCondition`. The global configuration, the M2 mask projection and the bounded runner are P8 and stay open, as the column states |
| laws | **closed** | All 125 theorem ascriptions are proved and named, each under the mask its block docstring gives: 20 in `Ecma262/JobsLaws`, 44 in `Ecma262/PromiseLaws`, 17 in `WebIdl/PromiseContract`, 15 in `WebIdl/ExceptionsContract`, 29 in the bridging half of `Streams/PromiseBridge`. `WhatwgTest/Ecma262/PromiseAxiomReport.lean` names exactly those 125 and no others |
| representation | **closed** | Identities stay `Nat` with monotone cursors (`Table.fresh_id`, `fresh_next`, `Reactions.add_id`, `add_next`); reactions and jobs are first-order descriptors (`Reaction.handler : Option body`, `Jobs.ReactionJob.mk : Nat → arg → …`, no stored body anywhere); the two lists with their one-list view (`Reactions.add_fulfill`, `add_reject`, `add_paired`, `registered_eq`, and `Transform.reactions_registered`); the handled bit as a per-cell field with its identity-list bridge (`Table.markHandled_eq`, `markHandled_idem`, `markHandled_state`, `Writable.handled_bridge`); the exception universe with allocation identity preserved (`Exception.simple_eq_iff`, `domException_eq_iff`, `Boundary.Exception.toWebIdl_injective`) |
| counterexamples | **required-open** | Untouched by this seat. The twenty-two `WS-PROM-CE-*` rows of `test/counterexamples/promise/ATTACKS.md` are a frozen breaker file, and `test/counterexamples/REGISTER.md` is outside the builder's fence. Linking each row to the production statement that rejects it is the reviewer's and the coordinator's |
| bridges | **closed** | All 29 bridging lemmas are proved, and the preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green: 53 `#check`s elaborate at their pre-move types, all 13 `example`s close by `intros; rfl`, and all 6 `inferInstance` checks are found through the reducible `abbrev`s. Every pre-existing battery under `WhatwgTest/Streams/**` rebuilt green. Host profiles and WPT settlement-order replay are P8 and stay open, as the column states. Three `generalize` rows keep the deferred bridges §4.4 rows 14, 15 and 16 already declare deferred with their reasons (`Transform.notify`, `Transform.settle`, `Transform.runJob`); they are not among the 29 |
| targets | not-applicable | Unchanged. Q3 lands no lowering and no generated code |
| trust | **closed** | All 125 named receipts print inside the R-11 ceiling: 59 empty, 41 `[propext]`, 20 `[propext, Quot.sound]`, 5 `[propext, Classical.choice, Quot.sound]` (`Table.fresh_get`, `Table.settle_handled`, `Table.markHandled_idem`, `WebIdl.Promise.waitForAll_success`, `Streams.Writable.settle_bridge`). The exhaustive root audit checked 192 modules and 12849 declarations on the builder branch at `795b4f8`, and 196 modules and 12973 declarations on the integration commit `7377134`, where the Q2 landing adds four audit modules and 124 declarations. `lake --wfail build Whatwg Gates` 164 jobs, `lake --wfail build WhatwgTest` 221 jobs at `795b4f8` (225 at `7377134`), `lake build` 366 jobs (374 at `7377134`), `lake exe vendorseal` PASS, `lake exe citations` PASS, and `lake exe census --standard {infra,webidl,ecma262}` PASS, all exit 0. No `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` or `native_decide` auxiliary appears anywhere, and no `sorry`, `partial` or `unsafe` survives the source trust gate |
| coverage | **required-open** (set at the landing review, ruling R-P20) | The criterion is the existence of a numerator module, not its authorship. Both `WhatwgTest/Audit/{WebIdl,Ecma262}/SpecCoverage.lean` exist on the integration commit `7377134` through the Q2 landing, and `lake exe census --standard webidl --report` and `--standard ecma262 --report` print `green 0, partial 0, absent 116` and `green 0, partial 0, absent 75`. No row moved: every Q3 declaration cites its census row as an anchor, never as a witness, and the numerators stay all-`absent` until a packet freezes witness statements against them. Only `infra` still reports "no numerator exists for this standard yet". Builder note B5 records why the Q3 seat authored neither module |

Four edges close: `laws`, `representation`, `bridges`, `trust`; `semantics` was reopened at the landing review (R-P20) and its reopening closed by the Q3b addendum (R-P24) while the edge stays required-open on its P8 deferrals.
Three stay `required-open`: `identity` (no generated declaration snapshot
exists), `construction` (`E-22`'s operations are Q4), and `counterexamples`
(the reviewer's). `targets` and `coverage` stay `not-applicable`, `coverage`
with the reason above rather than by inheritance.

No row of the clause map above is claimed whole-row green: every "residual
before whole-row green" column entry is still residual, and each is recorded
against its gap id in the module docstrings of the four implementation modules
and in the two updated roots.

## Q3b addendum, 2026-09-07, branch `promise/q3b-breaker`

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Appended by the Q3b addendum breaker seat, based on `f700230`. Contract:
`test/contracts/promise-first-packet-q3b.contract.md`. Attacks: the sixteen new
rows `WS-PROM-CE-023`..`WS-PROM-CE-038` of
`test/counterexamples/promise/ATTACKS.md`.

**Every landed row above is unchanged.** The authority-anchor table, the
declaration and existing-type records, the ten-edge table, the clause map and
the "Q3 landing" section keep their text. This section adds nothing to the
graph's inventory: it states which edges the addendum **closes on landing**,
and which it reopens or leaves as R-P20 left them. Nothing here closes an edge
at freeze; the addendum is RED and its five batteries are declared in
`test/fixtures/trust-gate/known-red.txt` together with the four base batteries
that carry an amended ascription.

The addendum answers the six fidelity findings **F1–F6** of ruling R-P20 and
the minors that ruling lists. It adds one alias to the anchor table's reading —
`CAPFIELD`, `field.promisereaction-records.Capability`, 2691475..2691802,
digest `67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77` — and
one more, `JOBS4`, `requirement.jobs.4`, 626486..626589, digest
`22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b`; both are
carried by the addendum's §2 rather than inserted above.

| Edge | Status at this freeze | What the addendum closes on landing, or leaves open |
| --- | --- | --- |
| identity | **required-open**, unchanged | Untouched. The addendum adds 17 signature ascriptions and one `inferInstance` re-check, and the edge still waits on the item R-P20 left open: this repository has no generated declaration snapshot, so no artifact joins each public declaration to exactly one record. The addendum does not supply one |
| construction | **required-open**, unchanged | Untouched by F1–F6. `E-22`'s operation-level generalization is still Q4, and reachable-state and cross-owner freshness invariants stay open, exactly as the column already says |
| semantics | **required-open**, reopened by R-P20 — **the addendum closes the reopening** | R-P20 reopened this edge because `requirement.jobs.3` (COMPLETE, 626357..626479) is in its close-on set and had no declaration and no discharge-by-typing statement. **F5 closes that item on landing**: `Jobs.startJob` is the missing producer of `Active.job` (`startJob_active`), `Jobs.RunToCompletion` is the DB-05 specification half, `Jobs.run_to_completion` is the realizer theorem, and `Jobs.run_to_completion_nonvacuous` refuses a vacuous discharge. `Jobs.startJob_run_agree` keeps the threading conservative, so `run_fifo`, `run_split` and both Streams `tick_job_fifo` corollaries stand unchanged, and `Jobs.run_one_job_per_step` states the typing half beside it. F1, F2 and F3 also touch this edge's close-on set — THEN, REACT and TRIGGER — and repair what the landed branches say about them: step 12 becomes unconditional (`performPromiseThen_handled`, `react_handled`), the settled branches append to no list (`Reactions.mint_no_waiting` and the amended branch laws), and the two settling callers clear both lists (`Reactions.clear_waiting`, `Table.settleAndTrigger_cleared`). The edge's own explicit deferrals stand: the global configuration, the M2 mask projection and the bounded runner are P8 and stay open, so the edge does not become whole-row green |
| laws | **closed**, and the addendum re-opens nothing | The 125 receipts stand. The seventeen amended statements keep their names, so `WhatwgTest/Ecma262/PromiseAxiomReport.lean` is neither short nor long, and the addendum's own 57 obligations have their own report, `WhatwgTest/Ecma262/PromiseFidelityAxiomReport.lean`. The edge closes again on landing with 182 named receipts across the two reports |
| representation | **closed**, and the addendum keeps it closed | `Reaction` gains `[[Capability]]` (CAPFIELD), which strengthens rather than weakens the column's "reactions and jobs are first-order descriptors, never stored bodies": the capability is a triple of `Nat` identities, and F4's `runReactionJob` takes the handler's completion as a **decision** (DB-02) rather than running a stored body. `E-50`'s constraint holds: `Reaction` stays `Repr`-only, and the `inferInstance : Repr (Reaction Nat)` re-check is the receipt |
| counterexamples | **required-open**, unchanged | The addendum adds sixteen rows, `WS-PROM-CE-023`..`WS-PROM-CE-038`, each linked to the statement that must reject it. Nine of them attack the landed Q3 implementation as built. `test/counterexamples/REGISTER.md` stays the coordinator's and is untouched by this seat, so the edge stays open on the same item as before |
| bridges | **closed**, and the addendum adds one | `Whatwg.Streams.Writable.settlementTrace_bridge` (mask M2) is the thirtieth bridging lemma, relating `E-71`'s writable settlement order to `Whatwg.Ecma262.Promise.SettlementTrace` with no change to `Writable.settlementTrace`'s content. `E-63`'s readable counterpart is **deferred with a stated reason**: the readable settlement alphabet's `closed` entry carries no promise identity, and supplying one would change `Readable.Settlement`, a `keep` row. The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` stays green throughout; the one amended bridging ascription is `subscribe_reactions_bridge` |
| targets | not-applicable, unchanged | Q3b lands no lowering and no generated code |
| trust | **closed**, and the addendum extends it | 57 further named receipts inside the R-11 ceiling on landing. `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the `native_decide` auxiliaries appear nowhere, and no `sorry`, `partial` or `unsafe` survives the source trust gate |
| coverage | **required-open**, unchanged | Both numerator modules exist and stay all-`absent`. Every anchor the addendum cites — CAPFIELD, JOBS4, THEN, FULFILL, REJECT, TRIGGER, REACTJOB, RESOLVING, COMPLETE, WAITALL, REACT, NEWP, RESOLVE, REJECTOP — is cited as an anchor for a declaration and never as a witness, so no row moves to `partial` or `green`. Acceptance condition 9 of the addendum requires the three census gates to confirm it |

**Which edges the addendum closes on landing.** One: the reopening of
`semantics`, through F5's realization of COMPLETE. It also delivers repairs
inside `semantics`' close-on set for THEN, REACT, TRIGGER, FULFILL and REJECT,
and one further bridge inside `bridges`, but neither edge becomes whole-row
green: `semantics` keeps its P8 deferrals and `bridges` keeps `E-63`'s deferred
readable bridge. `laws`, `representation`, `bridges` and `trust` stay closed
and reclose with more evidence; `identity`, `construction`, `counterexamples`
and `coverage` stay `required-open` on exactly the items R-P20 left them on;
`targets` stays `not-applicable`.

**The mask table.** §7 of the base packet is amended by §4.1 of the addendum,
not edited: `Jobs.run_cons` joins the M2 list, `WebIdl.Promise.waitForAll_success`
and `waitForAll_failure` leave it, `Writable.attachSink_pending_jobs`'s tree
docstring is corrected to M1, and the addendum's eleven new M2 theorems join.
No frozen statement changes for a mask correction.

## Q3b landing

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Q3b builder seat, 2026-09-07, branch `promise/q3b-builder` at `85a2d96`, based
on the frozen addendum `38a806a` merged with `origin/main` (R-P21, R-P22).
Receipt: the "Q3b landing receipt" of `docs/PROMISE-PACKAGE-PLAN.md`, which
carries every command and its result line. **Every landed row above this
section is unchanged**, the "Q3b addendum" table included: this section records
what the landing did to the edges it said it would.

| Edge | Status before | Status at the landing | Evidence, with theorem names |
| --- | --- | --- | --- |
| semantics | **required-open**, reopened by R-P20 | **the reopening is closed**; the edge stays `required-open` on its own P8 deferrals | COMPLETE has a declaration, a specification/realizer pair and a non-vacuity receipt, which is what the reopening asked for; qualified at the landing review (R-P24): `startJob` and `completeJob` are reachable only inside `Jobs.lean`'s own laws, `run` never consults the activation, and the global configuration that threads it is P8 (`G-08` remainder), so no execution the model performs today enters `Active.job`. `Jobs.startJob_active` is the producer `Active.job` lacked, `Jobs.RunToCompletion` with `Jobs.RunToCompletion_iff` is the DB-05 specification half, `Jobs.run_to_completion` is the realizer, and `Jobs.run_to_completion_nonvacuous` refuses the vacuous discharge because the activation `startJob` produces is one in which `RunCondition` fails. `Jobs.startJob_checkpoint`, `startJob_queue` and `startJob_blocked` bound the operation and `Jobs.completeJob_job`, `completeJob_other` bound the return. `Jobs.startJob_run_agree` keeps the threading conservative: `Jobs.run_fifo`, `Jobs.run_split`, `Jobs.hostEnqueuePromiseJob_order`, `Writable.tick_job_fifo`, `Transform.tick_job_fifo` and the three `runPullJob_*` receipts keep their statements **and** their proofs, byte-identical. `Jobs.run_one_job_per_step` states the typing half beside it. Inside the same close-on set, THEN and REACT are repaired by `Promise.performPromiseThen_handled` and `WebIdl.Promise.react_handled` (step 12 unconditional), by `Promise.Reactions.mint_no_waiting` with the amended `performPromiseThen_fulfilled`/`_rejected` and `react_fulfilled`/`react_rejected` (the settled branches append to no list), and TRIGGER, FULFILL and REJECT by `Promise.Reactions.clear_waiting`, `clear_other_promise` and `Table.settleAndTrigger_cleared` (both lists cleared). The global configuration, the M2 mask projection and the bounded runner are P8 and stay open, so the row is not whole-row green |
| laws | closed | **closed, with more evidence** | 182 named receipts across the two reports, all inside R-11. The addendum's 57 print 15 empty, 34 `[propext]`, 6 `[propext, Quot.sound]`, 2 `[propext, Classical.choice, Quot.sound]`; the base packet's 125 are still exactly 125 names with the Q3 landing's distribution, 59 empty, 41 `[propext]`, 20 `[propext, Quot.sound]`, 5 `[propext, Classical.choice, Quot.sound]` |
| representation | closed | **closed, and strengthened** | `Reaction` carries CAPFIELD as `Reaction.capability` and stays `Repr`-only; the `inferInstance : Repr (Reaction Nat)` re-check is green, which is the `E-50` receipt. `Promise.reactionHandlerResult_handler` returns the handler's completion unexamined, so DB-02 holds: no body is stored and none is run. `Capability` gains `deriving Repr`, forced and additive, recorded as builder note B3 |
| bridges | closed | **closed, and one bridge added** | `Whatwg.Streams.Writable.settlementTrace_bridge` (mask M2) is the thirtieth bridging lemma. `Writable.settlementTrace`'s content is unchanged and no projection was needed. `E-63`'s readable counterpart stays deferred with its stated reason. The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green and 25 of the 26 `WhatwgTest/Streams/**` batteries are byte-identical to `f700230` |
| trust | closed | **closed, and extended** | The 57 further receipts above, `lake exe trustselftest` PASS in both directions, and `known-red.txt` empty of entries again |
| counterexamples | required-open | **required-open**, unchanged | Of the sixteen rows `WS-PROM-CE-023`..`WS-PROM-CE-038`, eleven have the statement named for them landed and green and are registered `CLOSED`; five are registered `SEEDED` (R-P24): 026 names a statement `Reactions.add_capability` that exists nowhere, and the capability it stores is never read (debt D17); 033's mutant lives in the unchanged `callResolve`; 036 and 037 are documentary repairs; 038 is mechanical only through the `Repr` re-check. The register rows entered at the landing |
| identity, construction, coverage | required-open | **required-open**, unchanged | No generated declaration snapshot exists; `E-22`'s operation-level generalization is still Q4; both censuses stay all-`absent`, which the three `lake exe census` PASS lines confirm |
| targets | not-applicable | **not-applicable**, unchanged | Q3b lands no lowering and no generated code |

**Edges closed at this landing: one** — the reopening of `semantics`, through
F5's realization of COMPLETE, whose theorem is `Jobs.run_to_completion` with
`Jobs.run_to_completion_nonvacuous` beside it. **Edges reopened: none.**

**The declaration delta.** 196 → 201 modules, exactly as the addendum's §10
predicts, and 12973 → 13079 declarations. §10's expected 13047 counts the
generated projection `Reaction.capability` and no other generated constant;
the 33 further ones Lean mints — a `Repr` instance, three matchers, twelve
private match splitters and sixteen equation lemmas — are enumerated in builder
note B2 of the addendum, together with the one matcher that disappears because
`WebIdl.Promise.react` now pattern-matches on nothing. Every **authored** name
is §10's list, name for name: 1 type, 15 functions and predicates, 57 theorems.

## Q4, the DB-11 restatement, frozen 2026-09-07 on branch `promise/q4-breaker`

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Appended by the Q4 restatement breaker seat. The declaration and statement
rows above are frozen and unchanged. This section records only which edges of
`PROMISE-PG-FIRST` the Q4 restatement touches, and how. Slice Q4's own graph
is `docs/CONFIGURATION-DAG.md` (`CONFIGURATION-PG-ORDERING`); its contract is
`test/contracts/configuration-ordering.contract.md`.

Nothing here closes an edge. A frozen red battery is a statement, not
evidence.

| Edge | What Q4 touches | Effect on this graph |
| --- | --- | --- |
| identity | 15 ascriptions of `WhatwgTest/Streams/Semantics/OrderingContract.lean` name `Ecma262.Promise.Ref`, `.ReactionPhase` and `.Reaction` directly, and they elaborate. They are the first use of those three carriers by a client outside the Q3 batteries. | none: the edge stays `required-open` on the missing generated declaration snapshot. Q4 adds a second reader of the same names, not a second owner. |
| construction | Q4 lands `E-22`'s operation-level generalization, which the Q3 landing recorded as the one item still missing from this edge's "three Streams tables" evidence: `Readable.freshReadCell`, `settleReadCell` and `settleReadCells`, with `readTable_freshReadCell`, `readTable_settleReadCell` and `readTable_settleReadCells` as their bridges. | the edge stays `required-open` at this freeze; when the Q4 builder lands those three bridges, the only item left on this edge is the reachable-state and cross-owner freshness invariants the column already defers. |
| semantics | `Semantics.Ordering.activeErase` and `runCondition_iff` are the first client of `Jobs.RunCondition`, and `episodePrefix_jobQueue_eq` the first client of `Queue.enqueueAll` over a configuration. Neither realizes `requirement.jobs.3` (COMPLETE, 626357–626479), which R-P20 reopened this edge for; that stays Q3b's. | none. Q4 uses the run condition, it does not discharge COMPLETE. |
| laws | untouched. The 125 Q3 receipts stand; Q4's 82 receipts are its own, in `WhatwgTest/Streams/Semantics/OrderingAxiomReport.lean`, and belong to `CONFIGURATION-PG-ORDERING`. | none. |
| representation | the P4–P7 duplicate-prevention rows for `Readable.PromiseState`, `Writable.UnitPromise`/`SinkAnswer`/`SinkReturn`, `Writable.State.promises` and the Transform subscription adapter change from naming Streams the canonical owner to naming `Whatwg.Ecma262.Promise` the shared owner, with `E-07`..`E-12` as receipts (contract §4). This is the DB-11 sentence "at that point they become views onto the shared layer, with conversion receipts, rather than a second owner" being executed. | the edge is `closed` for Q3's own content and Q4 adds no obligation to it; the record change is `CONFIGURATION-PG-ORDERING`'s representation evidence, not a reopening of this one. |
| counterexamples | untouched. Q4 freezes no `WS-PROM-CE-*` row and does not edit `test/counterexamples/promise/ATTACKS.md` or `test/counterexamples/REGISTER.md`. | none. |
| bridges | Q4 lands the three bridges §4.4 of the Q3 contract deferred with a stated reason — rows 14 (`Transform.notify`), 15 (`Transform.settle`) and 16 (`Transform.runJob`) — as `notifyJob` and `notify_jobQueue_bridge`; `settle_table_bridge`, `settle_jobQueue_order` and `settle_waiting_once`; `runJob_writable_dequeue` and `runJob_writable_blocked`. The Q3 landing listed those three as "not among the 29". | the edge is `closed` for the 29 Q3 bridges. The three deferred rows were never counted in it, so Q4 does not reopen it; when they land, this edge's bridge set is complete for the whole `generalize` mode and the landing receipt should say so. |
| targets | untouched. | none. |
| trust | Q4's 82 receipts are inside the R-11 ceiling by its own acceptance condition 7, and no Q3 receipt changes. | none. |
| coverage | Q4 executes R-P5's Streams slot re-disposition: `slot.promise-state` and `slot.promise-is-handled` become `owned` in the *Streams* census, naming `Whatwg.Ecma262.Promise.State` and the `handled` field of its `Cell` as the model. `slot.value` stays `foreignBoundary` (gap `G-10`: no Completion carrier exists at this pin). Both re-disposed rows stay `absent`, and every Streams total is unchanged (contract §7.4, §7.5). The ES2026 and Web IDL numerators are untouched and stay all-`absent`. | none. No row of either promise census moves, and no Streams number moves. A packet that names a witness for either re-disposed row is what moves them, and it owes the numerator amendment. |

**The one thing Q4 gives this graph that is not an edge.** Q3's `E-22` was
partial by construction: only the view and its `get` law landed, because the
operations would have changed a Streams definition body. Q4 changes those five
bodies, so `Readable.State.readPromises` stops being a table with no
operations. The five equation lemmas that keep every dependent proof, the
exact new bodies and the nineteen dependent files are §5.4 of the Q4 contract.

## Q4 landing, 2026-09-07, branch `promise/q4-builder`

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Appended by the Q4 builder seat. **Every row above is unchanged**, the "Q4"
table included. This section records what the partial Q4 landing did to the
edges of `PROMISE-PG-FIRST` that its own freeze section said it would touch.
Receipt: the "Q4 landing receipt" of `docs/PROMISE-PACKAGE-PLAN.md`. Slice Q4's
own graph is `docs/CONFIGURATION-DAG.md`.

| Edge | Status before | Status at this landing | Evidence, with theorem names |
| --- | --- | --- | --- |
| construction | **required-open** on the missing `E-22` operations | **required-open**, and the item this edge named is discharged | `Readable.freshReadCell`, `settleReadCell` and `settleReadCells` landed with the five rewritten bodies, and `Readable.readTable_freshReadCell`, `readTable_settleReadCell` and `readTable_settleReadCells` are their bridges onto `Whatwg.Ecma262.Promise.Table.fresh` and `.settle`. The five equation lemmas `continuePull_settleRead_body`, `streamClose_body`, `error_body`, `beginEnqueue_settle_body` and `read_body` close definitionally, which is what keeps every dependent. The reachable-state and cross-owner freshness invariants this column already defers stay open, so the edge does not close |
| bridges | **closed** for the 29 Q3 bridges | **closed, and the three deferred rows are added** | Rows 14, 15 and 16 of §4.4 of the Q3 contract are landed: `Transform.notifyJob` with `notify_jobQueue_bridge`; `Transform.settle_table_bridge`, `settle_jobQueue_order` and `settle_waiting_once`; `Transform.runJob_writable_dequeue` and `runJob_writable_blocked`. With `E-22`'s three, the `generalize` mode's bridge set is complete for every row the Q3 contract deferred with a stated reason. `WhatwgTest/Streams/PromiseBridgeQ4.lean` is green |
| representation | closed | **closed, and the record change landed** | The P4–P7 duplicate-prevention rows for `Readable.PromiseState`, `Writable.UnitPromise`/`SinkAnswer`/`SinkReturn`, `Writable.State`'s promise slots and the Transform subscription adapter now name `Whatwg.Ecma262.Promise` the shared owner, with `E-07`..`E-12` as the receipts; the twenty ascriptions of §4.2 of the Q4 contract still elaborate, which is the acceptance condition for that change |
| identity | required-open | **required-open**, unchanged | 14 of the 15 class [R] ascriptions elaborate as the freeze predicted. The fifteenth, `Reaction.mk`, does not: it is ascribed at five explicit arguments and Q3b finding F4 gave it six. That is item B1 of §11.1 of the Q4 contract and the coordinator rules on it. No generated declaration snapshot exists, so the edge's own item is untouched |
| semantics | required-open | **required-open**, unchanged | `Semantics.Ordering.activeErase` with `runCondition_iff` is the first client of `Jobs.RunCondition`, and `episodePrefix_jobQueue_eq` the first client of `Queue.enqueueAll` over a configuration. Neither discharges anything on this edge, exactly as the freeze said |
| laws | closed | **closed**, unchanged | The 125 Q3 receipts and the 57 Q3b receipts stand, name for name. Q4's own receipts belong to `CONFIGURATION-PG-ORDERING` |
| counterexamples, targets | required-open / not-applicable | unchanged | Q4 freezes no `WS-PROM-CE-*` row and lands no lowering |
| trust | closed | **closed**, unchanged | No Q3 or Q3b receipt changed. Q4's own 79 printing receipts are inside R-11 and belong to the other graph |
| coverage | required-open | **required-open**, unchanged | R-P5's Streams re-disposition landed: `slot.promise-state` and `slot.promise-is-handled` are `owned` and still `absent`, `slot.value` stays `foreignBoundary` under gap `G-10`, no Streams number moved, and both promise censuses stay all-`absent` |

**Edges closed at this landing: none.** The `construction` edge's named
`E-22` item is discharged and the `bridges` edge's three deferred rows are
added, but both keep the deferrals their columns already record.

## Q4 landing, second pass, 2026-09-07, branch `promise/q4-builder-2`

Moved verbatim from `docs/PROMISE-DAG.md` at `325d5d5`.

Appended by the Q4 builder seat, second pass. **Every row above is unchanged**,
the first Q4 landing table included. Receipt: the "Q4 landing receipt (second
pass)" of `docs/PROMISE-PACKAGE-PLAN.md`. Slice Q4's own graph is
`docs/CONFIGURATION-DAG.md`; this section records only what the completed
landing does to `PROMISE-PG-FIRST`.

| Edge | Status before | Status at this landing | Evidence, with theorem names |
| --- | --- | --- | --- |
| identity | required-open | **required-open**, and item B1 is answered | All 15 class [R] ascriptions now elaborate. `Reaction.mk`'s ascription was re-frozen by amendment A1 under ruling R-P25 to the landed six-argument constructor with `capability : Option Capability` fifth; nothing in `Whatwg/Ecma262/Promise.lean` changed. The edge stays open on the generated declaration snapshot it already named |
| semantics | required-open | **required-open**, unchanged | `Semantics.Ordering.notifySettled_reactions_bridge` is the first statement relating this configuration's reaction half to `op.triggerpromisereactions` (2700260..2701212), modulo the Q4-owned `reactionErase` and under distinct registration identities, and `notifySettled_queued_serial` recovers the payload the erasure drops. Both are Q4-owned and belong to `CONFIGURATION-PG-ORDERING`; neither discharges anything on this edge |
| laws | closed | **closed**, unchanged | The 125 Q3 receipts and the 57 Q3b receipts stand, name for name, with the same distributions. Nothing under `Whatwg/Ecma262/` or `Whatwg/WebIdl/` was touched by this pass |
| bridges | closed | **closed**, unchanged | `WhatwgTest/Streams/PromiseBridgeQ4.lean` stayed green and byte-identical throughout |
| representation | closed | **closed**, unchanged | The four view record rows read as the first pass left them |
| construction, counterexamples, targets | unchanged | unchanged | This pass lands no `E-` operation, no `WS-PROM-CE-*` row and no lowering. `WS-PROM-CE-039`, seeded by the amendment against the packet's own false bridge, is answered by the restated bridge plus `notifySettled_queued_serial`; its `test/counterexamples/REGISTER.md` row is the coordinator's at landing |
| trust | closed | **closed**, unchanged | No Q3 or Q3b receipt changed. Q4's own 93 receipts all print inside R-11 and belong to the other graph. The trust gate's all-green control is restored: `test/fixtures/trust-gate/known-red.txt` holds no entry |
| coverage | required-open | **required-open**, unchanged | Both promise censuses stay all-`absent`, no Streams number moved, and the Q1 identity pin amendment A7 (32012 bytes, digest `247f9909…a63c`, ruling R-P26) is a disposition fact, not a coverage fact |

**Edges closed at this landing: none. Edges reopened: none.**

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/PROMISE-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/PromiseFirst.lean` and its projection `generated/graphs/PROMISE-PG-FIRST.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30, with the trust row
brought to the lane V landing of 2026-10-01 (R-V6, R-V8). Its landing records are
the Q3, Q3b and Q4 sections of the receipts log, as rulings R-P20, R-P24 and
R-P27 accepted them. Ruling R-V4 sets the rule: an edge is `required-closed`
only when every ground this document or a ruling in `COORDINATION.md` states
for keeping it open is discharged by something named in the ground cell.
Where a document and a later ruling disagree, the ruling wins and the cell
names it.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The generated declaration snapshot that joins each public declaration to exactly one declaration record below, which has no generator (debt D47). The six statement batteries' exact ascriptions and the constructor and instance census through the Streams `abbrev`s are delivered (Q3 landing), and all 15 class [R] ascriptions of the Q4 battery elaborate since amendment A1 (Q4 landing, second pass) |
| construction | `required-open` | Reachable-state and cross-owner freshness invariants. The `E-22` item is discharged by `Readable.freshReadCell`, `settleReadCell` and `settleReadCells` with the bridges `readTable_freshReadCell`, `readTable_settleReadCell` and `readTable_settleReadCells` (Q4 landing) |
| semantics | `required-open` | R-P20 reopened the edge for COMPLETE (`requirement.jobs.3`); the Q3b landing closed that reopening with `Jobs.run_to_completion` and `Jobs.run_to_completion_nonvacuous`, and R-P24 keeps the edge open: `startJob` and `completeJob` are reachable only inside the laws of `Whatwg/Ecma262/Jobs.lean` and `run` never consults the activation, so the global configuration that threads it (the `G-08` remainder), the M2 mask projection and the bounded runner stay P8 work. Debt D46 records that `WebIdl.Promise.resolve` and `reject` are `Table.settle` and trigger no reaction |
| laws | `required-closed` | 182 named receipts are proved: the 125 of `WhatwgTest/Ecma262/PromiseAxiomReport.lean` (Q3 landing, accepted by R-P20) and the 57 of `WhatwgTest/Ecma262/PromiseFidelityAxiomReport.lean` (Q3b landing, accepted by R-P24) |
| representation | `required-closed` | `Nat` identities with monotone cursors, first-order reactions and jobs, the two reaction lists with their one-list view, the per-cell handled bit with its identity-list bridge, and the exception universe with allocation identity, each by named theorems (Q3 landing, accepted by R-P20); `Reaction.capability` added and still `Repr`-only (Q3b landing); the P4 to P7 record rows name `Whatwg.Ecma262.Promise` the shared owner with receipts `E-07` to `E-12` (Q4 landing) |
| counterexamples | `required-open` | Six rows of `test/counterexamples/REGISTER.md` stand `SEEDED`: `WS-PROM-CE-015` (no witness pins the absent `DecidableEq`), `WS-PROM-CE-026` (the capability is stored and never read; debt D17), `WS-PROM-CE-033`, `WS-PROM-CE-036`, `WS-PROM-CE-037` and `WS-PROM-CE-038` (R-P24). The other 33 `WS-PROM-CE` rows are `CLOSED` |
| bridges | `required-closed` | The 29 Q3 bridging lemmas with the preservation half of `WhatwgTest/Streams/PromiseBridge.lean` green (Q3 landing, accepted by R-P20), `Writable.settlementTrace_bridge` (Q3b landing), and the bridges that rows 14 to 16 of §4.4 of the Q3 contract deferred, `notify_jobQueue_bridge`, `settle_table_bridge`, `settle_jobQueue_order`, `settle_waiting_once`, `runJob_writable_dequeue` and `runJob_writable_blocked`, with `WhatwgTest/Streams/PromiseBridgeQ4.lean` green (Q4 landing). Deferred with stated reasons, outside this edge's obligation: `E-63`'s readable settlement-trace bridge, and the host profiles and WPT settlement-order replay of P8 |
| targets | `not-applicable` | Q3, Q3b and Q4 land no lowering and no generated code; P11 owns the TypeScript target |
| trust | `required-closed` | The 182 named receipts print inside the R-11 ceiling, and `lake exe trustselftest` passed at the Q3b landing (Q3 landing, Q3b landing; R-P20, R-P24). At `325d5d5` seven of them reached `Classical.choice`: `Table.fresh_get`, `Table.settle_handled`, `Table.markHandled_idem`, `ResolvingFunctions.callResolveSelf_self`, `WebIdl.Promise.waitForAll_success`, `waitForAllTraced_success` and `Streams.Writable.settle_bridge`. Lane V repaired all seven with no statement changed (slices V1 and V5, R-V6), and since that landing the axiom gate holds `Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1) |
| coverage | `required-open` | Ruling R-P20 set the edge `required-open` because both numerator modules, `WhatwgTest/Audit/WebIdl/SpecCoverage.lean` and `WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, exist; every row of both censuses is `absent`. The later sentence of the Q3 landing section that says coverage stays `not-applicable` disagrees with R-P20, and R-P20 wins |

The ledger entry of this graph in `WhatwgTest/Ledger.lean` is projected to
`generated/graphs/PROMISE-PG-FIRST.md` by `lake exe whatwg_ledger --write`,
and `lake exe whatwg_ledger` checks that projection and the entry's
references, not this table.
