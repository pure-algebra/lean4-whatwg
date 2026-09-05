# Transform proof graph (`TRANSFORM-PG-BACKPRESSURE`, P6a)

Status: frozen breaker packet, 2026-09-05. Contract:
`test/contracts/transform-backpressure.contract.md`.

This file owns the declaration roles, existing-type dispositions, source
anchors, and assurance edges for the first transform breadth representative.
The packet must use actual canonical readable/writable states; an isolated
backpressure Boolean model does not discharge its coupling obligation.

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
| `lookupPromise`, `freshInternal`, `notify`, `subscribe`, `settle` | `Backpressure.lean` | named adapter of canonical P5 `lookupPromise`, `freshPromise`, `settle`, plus exact P4/P5 answer admission; no third table/runtime | owned settlement projection; BP, WRITE, PULL, PERFORM | representation |
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

## Ten edges

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact signatures and constructor census; generated public declaration joins |
| construction | required-open | post-start/count-profile constructor, fresh internal IDs, subscription uniqueness, valid native ports, reachable-state invariants |
| semantics | required-open | return/answer/reaction distinction, one ordered cross-component reaction queue, native ports hidden from foreign decisions, finite relational composition; global adoption-job embedding later |
| laws | required-open | all frozen stage equations and exact old/new identity, erroring recheck, enqueue backpressure, termination laws |
| representation | required-open | P3/P4/P5 reuse and named cell adapter preserving prior cells/IDs; no stored function or third runtime |
| counterexamples | required-open | retained WS-TRANS finite execution mutants and production repair laws; no snapshot promoted to full execution |
| bridges | required-open | exact P4 pull-frame and P5 write-frame realization laws; full profile, arithmetic and host correspondences later |
| targets | not-applicable | this representative generates no target code; P11 owns lowering |
| trust | required-open | intended-red verification, theorem receipts, full root audit/gates and independent review after implementation |
| coverage | required-open | clause map and test-side numerator witnesses; this packet adds no coverage claim |

## Residual clause map

| Algorithm family | First representative | Still owned/open |
| --- | --- | --- |
| BP / UNBLOCK | captured identities, old resolution/new allocation, queue insertion order | global allocation and ECMAScript reactions |
| PULL | actual P4 frame, returned NEW cell, subscription routing, pullAgain service | setup/start, unlocked/default/BYOB alternatives and global scheduler |
| WRITE / PERFORM | actual P5 in-flight request, OLD captured wait cell, later erroring check, synchronous transform body boundary | global promise adoption, full stream lifecycle and host relation |
| ENQUEUE / HASBP | count output strategy, actual P4 enqueue and synchronous native pull, final demand computation | arbitrary size callback continuations and abrupt stored-error rethrow |
| ERROR / WERROR / TERMINATE | canonical P4 close/error and canonical P5 erroring continuation | complete flush/abort/cancel lifecycle and finishPromise identity |
| INIT / RSTART | canonical component construction, reserved-port profile, and actual P4 successful-start demand tail before external calls | constructor, full start/setup promise and initialization relation |

## Review ledger

Preliminary independent design review accepts the named local adapter of the
P5 table without requiring a broad shared-carrier refactor. It requires prior
cell/ID retention laws, internal-ID filtering confined to the transform view,
OLD versus NEW subscriptions, deterministic reaction insertion, actual P4
pull identity routing, and no user frontier at reserved native ports. This is
design feedback, not acceptance of an exact surface or implementation.

The staged-equation review then checked the concrete cell/notification,
source/sink adapter, callback return, and error/termination equations. It
required strict saved-depth draining (undershoot has no transition), live
callback suspension behind input-size as well as transformer frames, and
actual composed canonical P4/P5 runs. It also found the positive-readable-HWM
initial-state issue: staging bare `Readable.initial` leaves capacity-driven
pull absent. The revised `initial` stages `Readable.callPullIfNeeded`, so its
native pull frame blocks external calls until serviced. `WS-TRANS-CE-014`
and a positive-capacity run retain that correction. The fourteen finite
witnesses pass with twelve axiom-free receipts and `propext` only for CE-005
and CE-014. The three composed production runs remain intended red.

Final independent review accepted the 112 interface ascriptions, 118 exact
law/receipt-name join, observation filtering, three composed runs, all thirteen
span hashes, file fence, and trust scan. The last documentation correction
clarifies that termination preserves queued output for later delivery while
writable erroring occurs immediately after the readable close operation.
Final-byte verification and immutable packet handoff are recorded in the
contract ledger; implementation and all required graph edges remain open.
