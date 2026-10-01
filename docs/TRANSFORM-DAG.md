# Transform proof graph (`TRANSFORM-PG-BACKPRESSURE`, P6a)

Status: P6a implementation and local-law receipt, 2026-09-05. Full P6 remains open. Contract:
`test/contracts/transform-backpressure.contract.md`.

This file owns the declaration roles, existing-type dispositions, source
anchors, and assurance edges for the first transform breadth representative.
The packet must use actual canonical readable/writable states; an isolated
backpressure Boolean model does not discharge its coupling obligation.

## Current state

This table describes commit `325d5d5` on 2026-09-30, with the trust row brought to the lane V landing of 2026-10-01 (R-V6). P6a landed on
2026-09-05 with implementation `afb57f8`, closing laws, counterexamples and
trust; full P6 stays open. Ruling R-V4 sets the rule: an edge is
`required-closed` only when every ground this document or a ruling in
`COORDINATION.md` states for keeping it open is discharged by something named
in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The generated public-declaration snapshot and its joins, which have no generator (debt D47) (P6a landing receipt) |
| construction | `required-open` | Valid ports, fresh and shared allocation, unique subscriptions, retained callback identity, trace-prefix validity and inductive reachable-state invariants; raw states can violate them (P6a landing receipt) |
| semantics | `required-open` | Full-state embeddings, global ECMAScript job order and promise adoption and registration (P6a landing receipt) |
| laws | `required-closed` | The 115 frozen local equations in `Whatwg/Streams/Transform/Laws.lean` and the three composed runs in `Runs.lean` are proved; the 118 named receipts print (P6a landing receipt) |
| representation | `required-open` | Full-state embeddings, global ECMAScript job order, promise adoption and registration, and numeric boundaries (P6a landing receipt). Since Q3, subscriptions are a view of `Whatwg.Ecma262.Promise.Reactions`, and Q4 landed the `notify`, `settle` and `runJob` bridges, which are `PROMISE-PG-FIRST` bridge evidence |
| counterexamples | `required-closed` | `WS-TRANS-CE-001` to `WS-TRANS-CE-014` are `CLOSED` in `test/counterexamples/REGISTER.md` with their linked production laws, for the exact local scope the register records (P6a landing receipt) |
| bridges | `required-open` | Full-state embeddings, global ECMAScript job order, promise adoption and registration, numeric boundaries and host relations; the four Node observations are finite host observations, compared with no Lean run (P6a landing receipt) |
| targets | `not-applicable` | This representative generates no target code; P11 owns lowering |
| trust | `required-closed` | The 118 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent implementation and proof review passed (P6a landing receipt). Four of the receipts, `freshInternal_new`, `coupled_write_read_enqueue`, `coupled_error_during_transform` and `coupled_positive_readable_capacity`, reached `Classical.choice` at `325d5d5`; slice V5 of lane V repaired them with no statement changed, and since that landing the axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1, R-V6) |
| coverage | `required-open` | The clause map and the test-side numerator witnesses; the packet adds no coverage claim (P6a landing receipt) |

## Authority anchors

Aliases expand to the sealed census at Streams commit
`b9ba9f49d95b4280be0dc2372377a006c3a91c18`. The thirteen byte spans were
independently cross-checked with system SHA-256 on 2026-09-05; all matched
the sealed census. The pinned text is the semantic owner.

| Alias | Census row | SHA-256 |
| --- | --- | --- |
| INIT | `op.initialize-transform-stream` | `597dc19c07c6724f0b47b9293e0ae511a2d33cfb18d8e583a8fb82fbafabba6f` |
| RSTART | `op.set-up-readable-stream-default-controller` | `2b2437c37f164645d5515d405886b0aa5169bda2926161244dd1891bb6275783` |
| BP | `op.transform-stream-set-backpressure` | `d137ad7abbbe3f11b932b1dc536474ca9cd6ded65f36497c15e386127c468467` |
| UNBLOCK | `op.transform-stream-unblock-write` | `1974c026dfae4d949f73629cfdb5ead20317813784b8d11e06769e023e2ba6b2` |
| PULL | `op.transform-stream-default-source-pull` | `9ab9eed9645ff3f7709a7e029231663a21e996503568e91dca277d9302c89cf6` |
| WRITE | `op.transform-stream-default-sink-write-algorithm` | `fd52d92198a29af2f7060defeeb64d596a3557966596acb0c9aca236f15a87ad` |
| PERFORM | `op.transform-stream-default-controller-perform-transform` | `8bbd594a076c0ec7653bafee9dab02f570fbc2967550c522e9a9f304bbfad08d` |
| ENQUEUE | `op.transform-stream-default-controller-enqueue` | `e0bf608500d66b48eb3a8d9755f9332aee7ba07bb9ef1434d3092cba1282eed3` |
| HASBP | `op.rs-default-controller-has-backpressure` | `8f73e15a43b7dcc8789a5dc9b5aeb67df69201de94cb347a7f6648c6da4ef34b` |
| ERROR | `op.transform-stream-error` | `e51426c943108dfee0557170123be4b9ba678840c9bce95057cd76fac6c5d52d` |
| WERROR | `op.transform-stream-error-writable-and-unblock-write` | `bf37cb6e36188d5f577361c5e94fe535b7ec87849ae954220bd344e549bae124` |
| CLEAR | `op.transform-stream-default-controller-clear-algorithms` | `5cc4daf7fecb9c7f0d0fd81536d73408fe67069b84577c875816802f2ea9e665` |
| TERMINATE | `op.transform-stream-default-controller-terminate` | `e61fa35b7b712839e193450dcab71720d5d5fbc4d2b916ad43fa0224139862c2` |

P4 and P5 canonical algorithms retain their existing authority rows. A
transform adapter relates to those owners; it does not claim the same anchor
as a second canonical operation. No mutable P5 signature is a dependency.
The frozen P5 commits and consumed surface are in the contract ledger.

## Declaration and existing-type records

The exact frozen surface is `BackpressureContract.lean`, with its stage
and composed-run statements in `BackpressureLaws.lean`. Names below are
relative to `Whatwg.Streams.Transform`, and source modules are relative to
`Whatwg/Streams/Transform`. The P6 builder owns implementations after freeze;
the independent breaker retains the statements and witnesses. Every row
routes to this graph. Constructors, projections, derived instances, and the
battery's named theorems inherit the relevant family, but still require
individual generated snapshot joins. No additional public helper may be
silently introduced; private helpers may organize an implementation.

| Stable declaration family | Module | Relationship / canonical owner | Disposition / anchors | Edge |
| --- | --- | --- | --- | --- |
| `Ports` | `Stream.lean` | canonical native port-name profile; names are not foreign-answer choices | `owned`; INIT | representation |
| `Algorithms` | `Stream.lean` | names of foreign transform/flush/cancel bodies; optional record clearing owns no active call | `foreignBoundary`; PERFORM, CLEAR | representation |
| `Completion`, `Reaction` | `Stream.lean` | derived first-order continuations; distinguish direct result, blocked reaction result, and adoption | `owned`; WRITE, PERFORM | semantics |
| `Subscription`, `subscriptionPromise`, `Job` | `Stream.lean` | captured-ID and reaction data; canonical local registration order, adapters of P4/P5 reaction queues | `owned`; BP, WRITE, PULL, PERFORM | semantics |
| `Control` | `Stream.lean` | derived synchronous foreign-call marker and deterministic continuation tags; P5 error control reused | `owned`; PERFORM, WERROR | semantics |
| `State`, `initial` | `Stream.lean` | named view embedding canonical `Readable.State` and `Writable.State`, plus transform-owned slots; initialization stages canonical P4 successful-start demand tail | `owned`; INIT, RSTART, BP, WRITE, PULL | construction |
| `Event`, `withReadable`, `withWritable` | `Stream.lean` | derived joint trace and prefix-suffix lifting of canonical component events; not the observation mask itself | `owned`; PULL, WRITE, ENQUEUE, PERFORM | representation |
| `lookupPromise`, `freshInternal`, `notify`, `subscribe`, `settle` | `Backpressure.lean` | named adapter of the P5 view of the canonical `Whatwg.Ecma262.Promise.Table`, plus exact P4/P5 answer admission; no third table/runtime. Subscriptions are a view of `Whatwg.Ecma262.Promise.Reactions` through `Transform.reactions` (`E-29`..`E-33`, generalize); the `notify`, `settle` and `runJob` bridges are §5 of `test/contracts/configuration-ordering.contract.md` | owned settlement projection; BP, WRITE, PULL, PERFORM | representation |
| `setBackpressure`, `unblockWrite` | `Backpressure.lean` | canonical transform slot algorithms on that shared-table view | `owned`; BP, UNBLOCK | laws |
| `sourcePull`, `servicePull` | `DefaultController.lean` | canonical transform source algorithm and adapter of the actual P4 pull frame/return; built-in port realization | `owned`; PULL | bridges |
| `sinkWrite`, `performTransform`, `returnTransform`, `answerTransform`, `react` | `DefaultController.lean` | canonical staged WRITE/PERFORM and foreign return/settlement boundary; actual P5 sink frame/result adapter | `owned` stages and `foreignBoundary` answers; WRITE, PERFORM | bridges |
| `read`, `enqueue` | `DefaultController.lean` | adapter of canonical P4 read/enqueue and canonical transform enqueue guard/postlude; count output profile | `owned`; ENQUEUE, HASBP, PULL | laws |
| `error`, `terminate` | `DefaultController.lean` | canonical transform algorithms delegating P4 close/error and P5 erroring control; no copied side state | `owned`; ERROR, WERROR, CLEAR, TERMINATE | laws |
| `runJob`, `externalFrontier`, `Decision`, `decide`, `tick`, `Step`, `Reaches` | new `Step.lean` | canonical local integration and finite relational composition; component jobs remain canonical; native ports cannot be foreign answers | `owned` scheduling, `foreignBoundary` body answers; all aliases | semantics |
| `OutputObservation`, `VisibleEvent`, `OrderedObservation`, `visibleEvent`, `observeOutput`, `observeOrdered` | new `Observation.lean` or `Stream.lean` | derived local candidates from canonical readable M1 and writable status/visible events; internal settlement filtering confined to this transform view | `owned`; DB-04, BP, PULL, WRITE, ENQUEUE | semantics |
| all named equations in `BackpressureLaws.lean` | owning module or new `Laws.lean`; composed proofs may use new `Runs.lean` | derived receipts of the exact owning declaration above; three composed runs include canonical component transitions | owning family's disposition / anchor | laws and bridges |

Module splitting may change only placement, not stable names or root
reachability. The shared unit outcome/answer/return types remain the exact
P4/P5 types; the packet creates no alias type or second semantic owner for
them. P3 `DyadicSize`, size strategies, queues, and shared exceptions likewise
retain their existing declaration records.

## Residual clause map

| Algorithm family | First representative | Still owned/open |
| --- | --- | --- |
| BP / UNBLOCK | captured identities, old resolution/new allocation, queue insertion order | global allocation and ECMAScript reactions |
| PULL | actual P4 frame, returned NEW cell, subscription routing, pullAgain service | setup/start, unlocked/default/BYOB alternatives and global scheduler |
| WRITE / PERFORM | actual P5 in-flight request, OLD captured wait cell, later erroring check, synchronous transform body boundary | global promise adoption, full stream lifecycle and host relation |
| ENQUEUE / HASBP | count output strategy, actual P4 enqueue and synchronous native pull, final demand computation | arbitrary size callback continuations and abrupt stored-error rethrow |
| ERROR / WERROR / TERMINATE | canonical P4 close/error and canonical P5 erroring continuation | complete flush/abort/cancel lifecycle and finishPromise identity |
| INIT / RSTART | canonical component construction, reserved-port profile, and actual P4 successful-start demand tail before external calls | constructor, full start/setup promise and initialization relation |

## Coordinator integration and module allocation (2026-09-05)

The frozen packet `03547f1feb938d65898c47b4061faeb3f4bd9edf` is integrated as
`5d95212` after P5a implementation `e4d053a52f6fc374e8657934df81d0ecc059b945`.
The coordinator declares the three known-red modules and imports the green
finite-witness module into the audited test root. Statements and witnesses
remain unchanged.

`Stream.lean` owns the frozen first-order records, component trace adapters,
subscription-ID projection, and count-profile initializer. `Backpressure.lean`
owns the shared-table allocation/settlement/subscription operations.
`DefaultController.lean` owns the actual component adapters and transformer
continuations. `Step.lean` owns the dispatcher, internal job scheduling, and
finite transition judgments. `Observation.lean` owns the frozen consumer
projections. `Laws.lean` and `Runs.lean` will hold the frozen equations and
three composed proofs. Placement does not change a stable name or semantic
owner. All required assurance edges remain open during implementation.

## Receipts

`docs/receipts/TRANSFORM-PG-BACKPRESSURE.md` holds this graph's history, moved
there verbatim under ruling R-V4: the edge table as amended at the P6a
landing, the pre-freeze review ledger, and the P6a landing receipt with its
file fence, observation boundary, verification commands, four finite Node
observations, independent review and remaining obligations. This document
still owns that receipt and its exact commands and keeps it in that log, so
references to them resolve there. The coordinator's integration and module
allocation record stays above because it carries the module placement of the
frozen names; its last sentence describes the edges during implementation, and
the table in "Current state" supersedes it.
