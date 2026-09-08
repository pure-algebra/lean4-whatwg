# Transform proof graph (`TRANSFORM-PG-BACKPRESSURE`, P6a)

Status: P6a implementation and local-law receipt, 2026-09-05. Full P6 remains open. Contract:
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

## Ten edges

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact signatures and constructor census; generated public declaration joins |
| construction | required-open | post-start/count-profile constructor, fresh internal IDs, subscription uniqueness, valid native ports, reachable-state invariants |
| semantics | required-open | return/answer/reaction distinction, one ordered cross-component reaction queue, native ports hidden from foreign decisions, finite relational composition; global adoption-job embedding later |
| laws | required-closed | all 115 frozen local equations and three composed statements pass; see the P6a landing receipt; global/reachable-state obligations stay on their open edges |
| representation | required-open | P3/P4/P5 reuse and named cell adapter preserving prior cells/IDs; no stored function or third runtime |
| counterexamples | required-closed | fourteen retained WS-TRANS finite mutants and linked production repair laws pass; the register records exact local scope, without promoting a snapshot to full execution |
| bridges | required-open | exact P4 pull-frame and P5 write-frame realization laws; full profile, arithmetic and host correspondences later |
| targets | not-applicable | this representative generates no target code; P11 owns lowering |
| trust | required-closed | all 118 theorem receipts, exhaustive root audit, narrow/full builds, executable gates and independent implementation/proof review pass; see the landing receipt |
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

## P6a landing receipt, 2026-09-05

### Base, packet and file fence

The implementation base is `e66876721f55f35ef09f1114a24487f57e794097`.
The head is the commit carrying this receipt; its exact hash is supplied in
the coordinator handoff. P5a landed at
`e4d053a52f6fc374e8657934df81d0ecc059b945`. The independent P6a freeze
`03547f1feb938d65898c47b4061faeb3f4bd9edf` was integrated as `5d95212`.
Breaker repair `c420aa9d5fd0433489efa3d60723ce469ea5002d`, integrated as
`e668767`, adds only the two explicit type annotations recorded in the
contract's additive elaboration ledger. No frozen proposition branch,
premise, observation or witness changed.

The production fence is the seven modules `Stream.lean`, `Backpressure.lean`,
`DefaultController.lean`, `Step.lean`, `Observation.lean`, `Laws.lean` and
`Runs.lean` under `Whatwg/Streams/Transform/`. The first five implement only
the surface frozen in the declaration-role table. `Laws.lean` exports the
115 frozen local theorem names; `Runs.lean` exports the three frozen
composed names. The production and test roots reach every new module and
all four P6 test modules.

The other changed files are `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`harness/transform/backpressure.mjs`, `test/fixtures/trust-gate/known-red.txt`,
the P6 status/repair cells in `test/counterexamples/REGISTER.md`, this graph,
`PLAN.md` and `COORDINATION.md`. No dependency, vendor or generated file
changes in this implementation slice.

All six frozen files were compared with the separate breaker worktree at
`c420aa9`; only that worktree's coordination file was dirty. The contract,
interface battery, law battery, axiom battery, finite witness module and
attack descriptions match byte-for-byte. In particular, the repaired law
battery retains SHA-256
`D939DE85318FC675E3685708DC5061FDC2E437C34DE01272D3D0FEBFC4E3BF4C`.

### Implementation and observation boundary

The count-output state embeds actual P4 readable and P5 writable states.
P5 owns the promise table and allocations; subscriptions retain the exact
old/new identity across backpressure changes. Native pull and write ports
execute the canonical component continuations. Foreign transformer returns
and eventual answers are separate decisions; coupled jobs execute in the
frozen local FIFO order and cannot run inside the suspended transform body.
Saved writable depths stage reentrant work without accepting an undershoot.

The three `Transform.Reaches` proofs construct actual `Step` derivations:

- `coupled_write_read_enqueue`: a blocked write, read demand, delivered
  output, successful transform return, exact write/ready settlement and
  old/new backpressure identities.
- `coupled_error_during_transform`: controller error during an active body,
  rejection of the component outcomes/queries with the exact reason, and
  successful return of the already-active write after algorithms clear.
- `coupled_positive_readable_capacity`: canonical successful-start native
  pull permits a write and queued output before any read.

These proofs quantify input/output values, the foreign reason where used,
and the promise seed, but fix the count profile and three finite tape shapes.
They use `Reaches.nil`/`Reaches.cons` and ordinary `simp`/`rfl`, without a
fuel-bound interpreter as the judgment. They are composed local regressions,
not arbitrary-run invariants. The output and ordered observations derive
from actual component events; their DB-04 M1/M2 embedding is still open.
The pending backpressure cell at the error-run endpoint is retained exactly;
it is not silently converted into a settled or completed global execution.

### Verification

The exclusive main verification window used the pinned Lean 4.33.1
toolchain and the following commands:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake --log-level=warning build WhatwgTest.Streams.Transform.BackpressureContract WhatwgTest.Streams.Transform.BackpressureLaws WhatwgTest.Streams.Transform.BackpressureAxiomReport WhatwgTest.Streams.Counterexamples.Transform.Backpressure
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Transform/BackpressureAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/transform/backpressure.mjs
git diff --check
```

The normal narrow build passes 71 jobs, including all 112 interface
ascriptions, all 118 theorem signatures/receipts and the fourteen retained
finite witnesses. The full build passes 287 jobs. The 118 named theorem
receipts comprise eight axiom-free proofs, 33 at `[propext]`, 73 at
`[propext, Quot.sound]`, and four at `[propext, Classical.choice, Quot.sound]`.
The last group is `freshInternal_new` and the three composed run proofs.
All are within R-11. The exhaustive root audit checks 141 modules and 10596
declarations, including 1595 in the Gates tooling tree. The known-red set
is empty again.

The vendor seal checks 206 files in five pinned trees; the citation gate,
TyXML schema/emission drift checks, and Streams/Infra census gates pass.
At base `e66876721f55f35ef09f1114a24487f57e794097` with this implementation
working tree, the report prints:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The Node fixture passes four finite observations under `node:stream/web`,
Node `v22.23.2`, Windows x64: read demand unblocks transform but does not
fulfill a write while the transform result is pending; an active transform
can return successfully after controller error; positive readable capacity
permits output before the first read; and zero/multiple outputs plus
termination retain queued chunks in order. The fixture records its exact
pins, tapes, observer assumptions and limits. It executes neither WPT nor
the reference implementation and compares no host run against a Lean run.
Its counterexample links name only the exercised behavioral projections.

### Independent review and remaining obligations

Independent review checked the core operations against their frozen
statements and source anchors, canonical component reuse, return/answer/job
staging, retained identities, saved-depth control and observation filtering.
The subsequent proof review checked the exact 118-name join, all three
composed derivations, claim scope and the host fixture. Source-anchor
corrections and a host counterexample-label correction were applied without
changing a theorem statement or proof boundary.

Only laws, counterexamples and trust close here. Identity remains open for
generated public-declaration snapshot joins. Construction remains open for
valid ports, fresh/shared allocation, unique subscriptions, retained callback
identity, trace-prefix validity and inductive reachable-state invariants.
Raw states can violate these conditions; the local equations do not assert
that every such state is a valid stream. Semantics, representation and
bridges remain open for full-state embeddings, global ECMAScript job order,
promise adoption/registration, numeric boundaries and host relations.

Full setup/start, arbitrary output-size callbacks, flush, cancel and the
complete close/abort lifecycle remain owned/open. No absent intrinsic
algorithm becomes a foreign body or a refusal. Coverage remains open for
the clause map and test-side numerator witnesses. The next P7a breadth
packet is a separate requirements/realizer shutdown fragment; it cannot
claim full pipe finalization before the missing canonical release and
cancellation operations exist.
