# Promise-layer proof graph (`PROMISE-PG-FIRST`, slice Q3)

Breaker-authored 2026-09-07 on `promise/q3-breaker`. Contract:
`test/contracts/promise-first-packet.contract.md`. This file owns the
declaration roles, existing-type dispositions, anchor map and graph edges of
the first packet over `Whatwg.Ecma262` and `Whatwg.WebIdl`. It owns no
coverage count, no slice ledger and no census row: `docs/PROMISE-PACKAGE-PLAN.md`
owns the slices, `docs/PROMISE-EXTRACTION-INVENTORY.md` owns the extraction
rows and gaps, and the two generated censuses own the rows.

Status: landed. Q3 is on `main` at `f700230` under ruling R-P20, the Q3b
fidelity addendum merged as `ee218c3` under R-P24, and the Q4 restatement
merged as `f4c8bad` under R-P27. No edge closes from a compiling battery.

## Current state

This table describes commit `325d5d5` on 2026-09-30. Its landing records are
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
| trust | `required-closed` | The 182 named receipts print inside the R-11 ceiling, and `lake exe trustselftest` passed at the Q3b landing (Q3 landing, Q3b landing; R-P20, R-P24). Seven of them reach `Classical.choice`, which R-11 admits: `Table.fresh_get`, `Table.settle_handled`, `Table.markHandled_idem`, `ResolvingFunctions.callResolveSelf_self`, `WebIdl.Promise.waitForAll_success` and `waitForAllTraced_success`, under repair in lane V (slice V1), and `Streams.Writable.settle_bridge`, under repair in lane V (slice V5) |
| coverage | `required-open` | Ruling R-P20 set the edge `required-open` because both numerator modules, `WhatwgTest/Audit/WebIdl/SpecCoverage.lean` and `WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, exist; every row of both censuses is `absent`. The later sentence of the Q3 landing section that says coverage stays `not-applicable` disagrees with R-P20, and R-P20 wins |

## Authority anchors

Two pinned sources. Byte offsets are 0-based, ends exclusive; no line number is
cited anywhere.

| Source | Pin | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| `vendor/ecma262-0248456c/spec.html` | `tc39/ecma262` `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026` | 2,978,793 | `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |
| `vendor/whatwg-webidl-a652053f/index.bs` | `whatwg/webidl` `a652053f1e74e4aaf647528deb174012ed6c909f`, March 2026 Review Draft | 695,845 | `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` |

Short aliases used in the declaration table expand to this table, not to a
second semantic owner. Digests are the span digests of
`generated/ecma262-census.tsv` and `generated/webidl-census.tsv`.

| Alias | Census row | Span | Span digest |
| --- | --- | --- | --- |
| PSTATE | `slot.PromiseState` | 2744957..2745252 | `b752fb3cead6b7d3063935ef7a5867b1af9f1f298b688dbe9d015540012f33fb` |
| PRESULT | `slot.PromiseResult` | 2745263..2745619 | `c0c3b1b3c19902cdec5971211ec6f5cce01d5a5696f5728c480c61013cbb9a2f` |
| PFULFILL | `slot.PromiseFulfillReactions` | 2745630..2745966 | `f13205764479117eddbc24d537a2981738b8e758dd5bd4f0d2042ce382fba3e0` |
| PREJECT | `slot.PromiseRejectReactions` | 2745977..2746311 | `d4c90d6b411a4b0359bfc0e9e75c1f9c25be373fb12d3a5bdbea60339a020f81` |
| PHANDLED | `slot.PromiseIsHandled` | 2746322..2746637 | `c5e0730a73986eb475cb399584433d21e4aadecc069e3b2d61517937d39ed652` |
| CAPREC | `record.promisecapability-records` | 2687751..2690437 | `08c37430874eb8f162eb3e84825cfecf3aae49700ec1a28e9728864e79fe83ab` |
| REACTREC | `record.promisereaction-records` | 2690445..2692671 | `d66fc8081d7a889ffbdd77b8a4828c5ad87095a72fa04b257f808dbea8816743` |
| JOBCB | `record.jobcallback-records` | 628436..630247 | `0fdda86da2a80f733a34298da2bec97f7a3c3da2cb173e0270813d63a9e85a1d` |
| FULFILL | `op.fulfillpromise` | 2695419..2696230 | `f0efa1ffede8b5b861cdb87a36f340ddbab87b2cdcd83abd7172d68e41a1c67e` |
| REJECT | `op.rejectpromise` | 2699323..2700252 | `1006df0c95f76cd0a9edadadb8f68bf85446b0e8778485cfd8b913fb169fc056` |
| TRIGGER | `op.triggerpromisereactions` | 2700260..2701212 | `ba03acae7a5640e794655f0fcb6e085859ce91eb4a8f899472ff01dc122c1839` |
| NEWCAP | `op.newpromisecapability` | 2696238..2698770 | `9d0157b63bd72c38fb0951e4d0030b46997508ca43b46c5402eb901bb4f5c1d9` |
| RESOLVING | `op.createresolvingfunctions` | 2692679..2695411 | `8227712c5eaa66d17942e1b7c13a8d6f7c29f24a03a591df81ce9868a90c8944` |
| THEN | `op.performpromisethen` | 2740635..2743669 | `ff69ee65628ebe06e4fe2717feb6013c3d3089b3fa2b034fd90c085c3fa7e2ce` |
| REACTJOB | `op.newpromisereactionjob` | 2702885..2705591 | `3225cb2f3907ae48b448c01a862587e80cd5e8b795b8ad5d610df68b5f291a7b` |
| HOSTENQ | `hook.hostenqueuepromisejob` | 633447..635836 | `2dd7ba925b7ef8424773a60bdef524789cf044e2a97d7f1796fa74acec613b93` |
| ORDER | `requirement.hostenqueuepromisejob.3` | 634739..634841 | `6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65` |
| RUNCOND | `requirement.jobs.1` | 625769..626250 | `c1afc33fed819c64bf74bbdfda723687b449fc135daaa0bb9dd9b73d0f5954e2` |
| ONEJOB | `requirement.jobs.2` | 626257..626350 | `dec0ab05daf30a7def2efe98018bbdf58750e2f762313b2b50d8184b00720ec5` |
| COMPLETE | `requirement.jobs.3` | 626357..626479 | `3cee57a0e02ed9d66b34bdaa1398995eebf32ac008eb9d493e15647bb9235378` |
| NEWP | `op.a-new-promise` | 347604..347946 | `a9c212f9448d6cfdaf262e33f33ed5104392aaec738b6e3ae22b285edc3751b3` |
| RESOLVEDW | `op.a-promise-resolved-with` | 347948..348631 | `a5b86f19962066ef9844df3f2ee2494cb78c74bae6cf6690cc8ee1b6e0b60015` |
| REJECTEDW | `op.a-promise-rejected-with` | 348633..349214 | `3f6d84e5da374f56e56aebba956939b54dbefb219a67137a37128ecce58f20f8` |
| RESOLVE | `op.resolve` | 349216..349783 | `071c11c45c5c1da04b86837e7911385b64880eaf3a013ff769676110af545cc3` |
| REJECTOP | `op.reject` | 349785..350073 | `c2edaaba6c2c29a161365819f857be96eabcf9ee573580a4687e8eec72a900ea` |
| REACT | `op.dfn-perform-steps-once-promise-is-settled` | 350075..352408 | `dd0e08ae5b8739280837b31e10f2ace6f1a7f9b20034124d7c748d450aaab383` |
| UPONF | `op.upon-fulfillment` | 352410..352816 | `81ccd0a141715f38ae30f05c97a994c4ea3fef748c6301da8f3b8e4c6c785b9d` |
| UPONR | `op.upon-rejection` | 352818..353237 | `f1e47b988febfd3652dac64ddb390db465d96a07f5b2d939cd8c62413221e7e9` |
| WAITALL | `op.wait-for-all` | 353239..354879 | `518fae182417ff76e800ed67df039a512d35b6af29ee11251b684172e703d930` |
| HANDLEDOP | `op.mark-a-promise-as-handled` | 356060..356713 | `644263e9155cf45d31167e53346f9d0e2431aedde301b440dbc92d9021b618bc` |
| SIMPLEX | `op.dfn-simple-exception` | 194433..194721 | `23597069802c1cb8d6b73ddb94125c7fed97b65815cf8e7bf7b3cdd69e1041d3` |
| EXCOBJ | `op.js-exception-objects` | 664320..664406 | `036d4e370d6f4dc68f7266889421e196ca709b894fc8ae9cfd293ae9eac124e4` |
| CREATESIMPLE | `op.to-create-a-simple-exception` | 664734..665486 | `a685c4154d0f603eb41dfcc0b4cafcb2ffcfc201d1519963d63a1008d36351de` |

The 32 base `DOMException` error names are one `type.*` row each; the contract
carries their row ids, spans and digests, and they are not aliased here.

## Declaration and existing-type records

The owner of each row is the Q3 builder after this breaker freezes it; the
breaker owns the statements. Every row's route is `PROMISE-PG-FIRST` with the
contributing edge named. Constructors, projections, derived instances and the
batteries' named theorems inherit their owning row deterministically.

Every row carries its duplicate-prevention relationship as an inventory row id
with its R-P12 reuse mode, or a gap id. A row with neither is a defect under
R-P12 and does not freeze.

| Stable declaration family | Module | Relationship and existing owner | Disposition / anchor | Edge |
| --- | --- | --- | --- | --- |
| `Ecma262.Promise.State` | `Ecma262/Promise.lean` | `E-01` move; canonical owner, `Readable.PromiseState` becomes its `abbrev` | `owned` first-order fusion of two slots; PSTATE, PRESULT | identity |
| `Ecma262.Promise.Outcome`, `.Returned` | `Ecma262/Promise.lean` | `E-02`, `E-03` move; `Readable.PullAnswer`, `Readable.PullReturn` become their `abbrev`s | `foreignBoundary` answer, `owned` shape; FULFILL, REJECT | identity |
| `Ecma262.Promise.Ref` | `Ecma262/Promise.lean` | P8a `PromiseRef`, rename only; `Ref.cell` renames `PromiseRef.local`, a Lean keyword | `owned`; no census row — a model device above `Nat` identities | representation |
| `Ecma262.Promise.Cell`, `.Table` | `Ecma262/Promise.lean` | `E-13`, `E-14`, `E-15`, `E-22`, `E-23` generalize; `Writable.State.promises`/`nextPromise`/`handled` and `Readable.State.readPromises`/`nextRead` become instances | `owned`; PSTATE, PRESULT, PHANDLED | construction |
| `Table.getCell`, `.get`, `.isPending`, `.fresh`, `.settle`, `.markHandled` | `Ecma262/Promise.lean` | `E-18`, `E-19`, `E-20`, `E-21` generalize with bridging lemmas; the Streams definitions stay `def`s so their `simp` equation lemmas survive | `owned`; FULFILL, REJECT, NEWCAP, HANDLEDOP | laws |
| `Ecma262.Promise.ReactionType`, `.ReactionPhase`, `.Reaction`, `.Reactions` | `Ecma262/Promise.lean` | `E-29`, `E-30` generalize; P8a `ObserverPhase` and `Registration` rename only; the `[[Type]]` tag is new under `G-01` | `owned`; REACTREC, PFULFILL, PREJECT | representation |
| `triggerReactions`, `Table.settleAndTrigger`, `fulfillPromise`, `rejectPromise` | `Ecma262/Promise.lean` | `E-32`, `E-33` generalize; P8a `notifySettled` rename only; the order and once-only laws are new content | `owned`; TRIGGER, FULFILL, REJECT, REACTJOB | semantics |
| `Ecma262.Promise.Capability`, `.ResolvingFunctions`, `newPromiseCapability`, `createResolvingFunctions`, `ResolvingFunctions.callResolve`/`.callReject` | `Ecma262/Promise.lean` | `G-03`, wholly absent from Streams; resolve and reject are first-order function identities, never stored bodies | `owned`; CAPREC, NEWCAP, RESOLVING | construction |
| `Ecma262.Promise.performPromiseThen` | `Ecma262/Promise.lean` | `G-11`; Streams has steps 8 to 10 twice over (`E-31`, `E-37`) with no result capability | `owned`; THEN | semantics |
| `Ecma262.Jobs.Queue` and its six operations | `Ecma262/Jobs.lean` | `E-45`, `E-48`, `E-52` generalize; the three per-component Streams lists become instances at three payloads | `owned`; HOSTENQ | construction |
| `Ecma262.Jobs.ReactionJob`, `newReactionJob` | `Ecma262/Jobs.lean` | `E-44`, `E-50` generalize; payload-polymorphic in the argument so `Jobs.lean` mentions no promise state | `owned`; REACTJOB, JOBCB | representation |
| `Ecma262.Jobs.Active`, `mayRun`, `RunCondition`, `step` | `Ecma262/Jobs.lean` | P8a `Active` rename only; `E-47` keeps `Writable.Control.react` where it is; `G-08` supplies the named condition Streams lacks | `requirement`; RUNCOND, ONEJOB, COMPLETE | semantics |
| `Ecma262.Jobs.FifoRequirement`, `run`, `hostEnqueuePromiseJob` | `Ecma262/Jobs.lean` | `E-46`, `E-49`, `E-53` generalize the realizer; `G-08` authors the specification. DB-05 pair under R-P5 | `requirement` specification with `owned` realizer; ORDER, HOSTENQ | laws |
| `WebIdl.Promise.newPromise`, `.resolvedWith`, `.rejectedWith`, `.resolve`, `.reject`, `.markAsHandled` | `WebIdl/Promise.lean` | `E-19`, `E-21` generalize; the Web IDL names over the ES2026 core | `owned`; NEWP, RESOLVEDW, REJECTEDW, RESOLVE, REJECTOP, HANDLEDOP | laws |
| `WebIdl.Promise.react`, `.uponFulfillment`, `.uponRejection` | `WebIdl/Promise.lean` | `E-31`, `E-37` generalize; P8a `register` rename only | `owned`; REACT, UPONF, UPONR | semantics |
| `WebIdl.Promise.AllSettled`, `.allSettled`, `.WaitResult`, `.waitForAll` | `WebIdl/Promise.lean` | `E-55`, `E-56` generalize the predicate; the operation and the agreement lemma are `G-06` | `owned` predicate and partial operation; WAITALL | semantics |
| `WebIdl.Exceptions.Simple`, `.Name`, `.Exception`, `createSimple` | `WebIdl/Exceptions.lean` | `E-59` generalize; `Boundary.Exception` keeps its constructors and its 69 dependents, related by an injective embedding | `owned` data; SIMPLEX, EXCOBJ, CREATESIMPLE, the 32 `type.*` name rows | representation |
| `Streams.Writable.promiseTable`, `.jobQueue`, `Streams.Readable.readTable`, `.jobQueue`, `Streams.Transform.jobQueue`, `.reactions`, `Boundary.Exception.toWebIdl`, `.ofWebIdl` | `Whatwg/Streams/**`, additive | the bridging views the `generalize` rows owe; no existing Streams definition body, theorem statement or `attribute [local simp]` set changes | `owned` views; the anchors of their targets | bridges |

Private implementation helpers may be added without changing these
signatures. A new public helper needs a record here and a theorem receipt.

## Clause map and residual obligations

| Anchors | Q3 obligations | Residual before whole-row green |
| --- | --- | --- |
| PSTATE, PRESULT | the three-tag fusion with two type parameters and its derived instances, reached through the Streams `abbrev` | the remaining three instance slots as live state in one configuration; the `[[PromiseState]]` of a promise created by user code |
| PFULFILL, PREJECT, REACTREC | the two lists, the `[[Type]]` tag, the capability field, the one-list view Streams instantiates | `[[Handler]]` as anything but a first-order descriptor; the reaction of a thenable job |
| PHANDLED | the per-cell field, its identity-list bridge, and idempotence | `HostPromiseRejectionTracker` (`hook.host-promise-rejection-tracker`, 2701220..2702791) — `G-02`, out of this packet |
| FULFILL, REJECT, TRIGGER | the guarded settle, the assertion as a side condition, the order and once-only laws | the abrupt-completion paths of the callers |
| CAPREC, NEWCAP, RESOLVING | the capability record, `NewPromiseCapability` at the intrinsic constructor, the resolving functions and `[[AlreadyResolved]]` | a non-intrinsic constructor; `Promise ( executor )`; the thenable branch (`G-05`) |
| THEN, REACT, UPONF, UPONR | steps 8 to 12 with the result capability, and the two one-sided wrappers | `then`/`catch`/`finally` and the four combinators (`G-11` remainder) |
| HOSTENQ, ORDER, RUNCOND, ONEJOB, COMPLETE | the payload-polymorphic queue, the named run condition, and the DB-05 specification/realizer pair | the realm parameter, `HostMakeJobCallback` (630253..631441) and `HostCallJobCallback` (631447..632699) — `G-07` remainder; the host microtask-checkpoint profile |
| NEWP, RESOLVEDW, REJECTEDW, RESOLVE, REJECTOP, HANDLEDOP | the six Web IDL names over the ES2026 core, with their `_eq` laws | the IDL binding layer, which stays `hostOnly` under R-P4 |
| WAITALL | the settled predicate in both forms with their agreement lemma, the ordered result list and the first-rejection short-circuit | `get a promise to wait for all` (354881..356058) and its `[=Queue a microtask=]` step — `G-06` remainder |
| SIMPLEX, EXCOBJ, CREATESIMPLE, the 32 name rows | the five simple kinds, the 32-name table as data, the identity-preserving carrier and the Streams embedding | `create a DOMException` (665488..666331), `create a DOMException derived interface` (666333..667324), `throw an exception` (667326..667543) and the six derived-interface `rule` rows — `G-09` remainder |

## Evidence ledger

The specification byte-span cross-check, the intended-red commands and their
exact diagnostics, and the immutable packet commit are recorded in the
contract's "Freeze receipt". The coordinator owns root and `known-red`
integration and may append landing receipts; it may not weaken this packet.

## Receipts

`docs/receipts/PROMISE-PG-FIRST.md` holds this graph's history, moved there
verbatim under ruling R-V4 in its original order: the freeze-time status
paragraph, the freeze-time edge table, and the sections "Q3 landing", "Q3b
addendum", "Q3b landing", "Q4, the DB-11 restatement", "Q4 landing" and "Q4
landing, second pass", each with its own edge table. This document still owns
those sections and keeps them in that log under their original headings, so a
reference to a named section of `docs/PROMISE-DAG.md`, such as the "Q3b
addendum" or "Q4" section that frozen batteries, contracts,
`test/fixtures/trust-gate/known-red.txt` and `docs/PROMISE-PACKAGE-PLAN.md`
cite, resolves there. The Q3b addendum's two further anchor aliases, CAPFIELD
and JOBS4, are carried by §2 of
`test/contracts/promise-first-packet-q3b.contract.md` and recorded in the log's
"Q3b addendum" section.
