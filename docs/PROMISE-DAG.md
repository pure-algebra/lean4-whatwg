# Promise-layer proof graph (`PROMISE-PG-FIRST`, slice Q3)

Breaker-authored 2026-09-07 on `promise/q3-breaker`. Contract:
`test/contracts/promise-first-packet.contract.md`. This file owns the
declaration roles, existing-type dispositions, anchor map and graph edges of
the first packet over `Whatwg.Ecma262` and `Whatwg.WebIdl`. It owns no
coverage count, no slice ledger and no census row: `docs/PROMISE-PACKAGE-PLAN.md`
owns the slices, `docs/PROMISE-EXTRACTION-INVENTORY.md` owns the extraction
rows and gaps, and the two generated censuses own the rows.

Every edge is `required-open` at this freeze except the two the packet declares
`not-applicable` with a reason. No edge closes from a compiling battery.

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

## Ten edges

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

## Q3 landing, 2026-09-07, branch `promise/q3-builder`

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

Five edges close: `semantics`, `laws`, `representation`, `bridges`, `trust`.
Three stay `required-open`: `identity` (no generated declaration snapshot
exists), `construction` (`E-22`'s operations are Q4), and `counterexamples`
(the reviewer's). `targets` and `coverage` stay `not-applicable`, `coverage`
with the reason above rather than by inheritance.

No row of the clause map above is claimed whole-row green: every "residual
before whole-row green" column entry is still residual, and each is recorded
against its gap id in the module docstrings of the four implementation modules
and in the two updated roots.

## Q4, the DB-11 restatement, frozen 2026-09-07 on branch `promise/q4-breaker`

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
