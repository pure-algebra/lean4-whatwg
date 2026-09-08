# Default-readable proof graph (`READABLE-PG-DEFAULT`, P4a)

Breaker-authored 2026-09-05. Contract:
`test/contracts/readable-default.contract.md`. This file owns the declaration
roles, existing-type dispositions, anchor map, and graph edges for the first
default-readable representative. It owns no coverage count.

## Authority anchors

Every row below is a byte-span SHA-256 from the sealed Streams census at
`b9ba9f49d95b4280be0dc2372377a006c3a91c18`. Short anchor aliases used in the
declaration table expand to this table, not to a second semantic owner.

| Alias | Census row | Span digest |
| --- | --- | --- |
| ENQUEUE | `op.readable-stream-default-controller-enqueue` | `469b91977f68167edd5067124cbdba64f26f7c20b36152cbbee0332dfa65db5a` |
| PULL | `op.readable-stream-default-controller-call-pull-if-needed` | `23dd19e991d0c53c342b243ab960ff7dc17a2896ced0f27da0e81be044ecb1a7` |
| DEMAND | `op.readable-stream-default-controller-should-call-pull` | `e7836bdebd70974301841f2cd2c32ca7b78aaa42c2091472a96c24b7ea40f96e` |
| GUARD | `op.readable-stream-default-controller-can-close-or-enqueue` | `1afdc468c71f87b091aa115dae9ed2dff47d270027e588e24eae05207d5960be` |
| CLEAR | `op.readable-stream-default-controller-clear-algorithms` | `d9bf13c07b08931b8a90f6f1c84a85571520bc61b32945026e84346c12763a33` |
| CLOSE | `op.readable-stream-default-controller-close` | `9b5451d952ae77d14011a47251033a7462cf7a15c3d6789d04bcf54d27b51338` |
| ERROR | `op.readable-stream-default-controller-error` | `e2ce1b47b227604cdb27367a3eacc4536e56f582717bbb9054bdccf5f72961d9` |
| DESIRED | `op.readable-stream-default-controller-get-desired-size` | `b7fd66710c69a693cd58db51730efebe9f273117e7f9814ea0b46f87317d31dc` |
| READ | `op.readable-stream-default-reader-read` | `93c0050d31600dcc8a1556d3719117b069a229775a8bb01d6a087032f54f873e` |
| DEQUEUE | `op.rs-default-controller-private-pull` | `96222db2e7a327cede9c28b85f069a32c67402812561e6a8f12fd78aab59b86d` |
| ADDREAD | `op.readable-stream-add-read-request` | `f3bcb6fb9036cba34367a498e8d60ea1d248f165cc0c2c414be30b4610dbc046` |
| FULFILL | `op.readable-stream-fulfill-read-request` | `4b08d0beab9c9af08570f4a94f832ab1a793d5c78da74020e9dd8995f1dc03c0` |
| STREAMCLOSE | `op.readable-stream-close` | `2480d783faed1cb482d1e286bccc22507ac5d2f7af7fd07bd7516c59c380ea40` |
| STREAMERROR | `op.readable-stream-error` | `55f8e6da90fb9cd5f42fc986b056450dc52ed096028a838f2a261c748d7ef8c6` |

## Declaration and existing-type records

All names below are relative to `Whatwg.Streams`. The owner of the packet is
the P4 readable builder after this breaker freezes it; the breaker owns its
statements. Constructors, projections, derived instances, and the battery's
named theorems inherit their owning row deterministically. Every inherited
declaration must still appear in the future generated declaration snapshot.
The route for every row is `READABLE-PG-DEFAULT`, with the contributing edge
named below. No separately allocated leaf graph is needed.

| Stable declaration family | Module | Relationship and existing owner | Disposition / anchor | Edge |
| --- | --- | --- | --- | --- |
| `Boundary.Exception`, `.ofRangeError`, `.toRangeError` | `Boundary/Exception.lean` | canonical shared exception reason with allocation IDs; adapter of `Data.RangeError` at a chosen ID, with identity-erasing retraction; P3-R2 | `owned` for modeled errors, `foreignBoundary` for `.foreign`; ENQUEUE, STREAMERROR | representation |
| `Readable.Size`, `Readable.sizes`, `Readable.sizePositive` | `Readable/State.lean` | named view and derived positivity test of `Data.DyadicSize` / `.sizes`; not another number carrier | `owned` exact arithmetic view under P3-R1; DESIRED | representation |
| `Readable.Status` | `Readable/State.lean` | canonical tagged projection of stream state/stored error; full-stream embedding remains open | `owned`; READ, STREAMERROR | identity |
| `Readable.ReadResult` | `Readable/State.lean` | canonical first-order chunk/done result for the default-reader projection | `owned`; FULFILL, STREAMCLOSE | identity |
| `Readable.PromiseState` | `Readable/State.lean` | view of `Whatwg.Ecma262.Promise.State α (Boundary.Exception ε)`, the canonical owner since Q3 (`E-01`, move); not ECMAScript promise objects. Conversion receipts: `Writable.unitPromise_eq`, `unitPromiseToShared_eq`, `unitPromiseFromShared_eq`, `unitPromise_roundtrip` (`E-07`, `E-08`) | `foreignBoundary` objects; owned settlement transition projection; STREAMCLOSE, STREAMERROR | representation |
| `Readable.Algorithms` | `Readable/State.lean` | names of foreign algorithms; size reuses `Data.SizeAlgorithm Nat` | `foreignBoundary`; ENQUEUE, PULL, CLEAR | representation |
| `Readable.Settlement`, `Readable.Event` | `Readable/State.lean` | canonical data recording this projection's observations; future M2 embedding required | `owned`; FULFILL, STREAMCLOSE, STREAMERROR, PULL | semantics |
| `Readable.PullContinuation`, `Readable.Frame` | `Readable/State.lean` | derived suspended size/pull continuations; store call/read IDs and chunks, never callable bodies | `owned`; ENQUEUE, PULL, DEQUEUE | representation |
| `Readable.PullAnswer`, `Readable.PullReturn` | `Readable/State.lean` | typed eventual fulfillment/rejection and distinct synchronous callback return; returned pending/settled promise controls reaction attachment | `foreignBoundary`; PULL | semantics |
| `Readable.State`, `Readable.initial` | `Readable/State.lean` | named raw projection of one default stream/controller/attached reader, after successful start; queue is `Data.Queue` | `owned`; all aliases | construction |
| `Readable.desiredSize`, `Readable.canCloseOrEnqueue`, `Readable.shouldCallPull` | `Readable/DefaultController.lean` | canonical operations on that projection | `owned`; DESIRED, GUARD, DEMAND | laws |
| `Readable.continuePull`, `Readable.callPullIfNeededWith`, `Readable.callPullIfNeeded`, `Readable.returnPull`, `Readable.acceptPullAnswer`, `Readable.reactPull`, `Readable.runPullJob` | `Readable/DefaultController.lean` | canonical staged pull scheduling, callback return, answer admission, and deterministic FIFO reaction | `owned` scheduler, `foreignBoundary` answer; PULL, DEQUEUE, ENQUEUE | semantics |
| `Readable.close`, `Readable.streamClose`, `Readable.error` | `Readable/DefaultController.lean` | canonical controller/stream algorithms and default-reader settlement expansion; no IDL wrapper claim | `owned`; CLOSE, ERROR, STREAMCLOSE, STREAMERROR | laws |
| `Readable.beginEnqueue`, `Readable.finishEnqueue`, `Readable.resumeSize` | `Readable/DefaultController.lean` | canonical staged ENQUEUE; size answers reuse `Data.SizeAnswer`; finish is the already-admitted continuation | `owned`; ENQUEUE, FULFILL | laws |
| `Readable.read` | `Readable/DefaultReader.lean` | canonical default-reader read in the fixed-reader projection | `owned`; READ, DEQUEUE, ADDREAD | laws |
| `Readable.observeM1`, `Readable.observeM2`, `Readable.settlementTrace`, `Readable.chunksOfSettlements`, `Readable.VisibleEvent`, `Readable.M2Observation` | `Readable/State.lean` | derived views of Event; local M2 carries M1 plus ordered settlements, desiredSize queries and enqueue completions; settlementTrace is one component only | `owned`; FULFILL, STREAMCLOSE, STREAMERROR, DESIRED, ENQUEUE | semantics |
| `Readable.queryDesiredSize` | `Readable/DefaultController.lean` | consumer query transition around pure desiredSize; records its result for M2 | `owned`; DESIRED | semantics |
| `Readable.Decision`, `Readable.step`, `Readable.Step`, `Readable.Steps` | `Readable/State.lean` or new `Readable/Step.lean` if needed to avoid cyclic imports | canonical first-order external decisions and finite relational composition; internal jobs are separate | `owned` calls, `foreignBoundary` answers; all aliases | semantics |

Do not add fields or declarations to the public frozen surface silently.
Private implementation helpers may be added without changing these signatures.
A new public helper must receive a record linked to its semantic owner and
appropriate theorem receipt. Module splitting to respect dependency direction
is permitted while stable names and root reachability stay fixed.

## Ten edges

| Edge | Status | Required evidence / reason |
| --- | --- | --- |
| identity | required-open | exact ascriptions and constructor census; shared reason retraction; declaration snapshot joins every public declaration |
| construction | required-open | initial state equations; state fields first-order; no false non-coexistence invariant; later reachable-state and fresh-ID invariant proofs |
| semantics | required-open | staged transitions, answer admission and FIFO internal jobs; M1/M2 projection; external step and finite relational composition; later global job/host embedding |
| laws | required-closed | every quantified equation in DefaultContract passes; see the P4a landing receipt below; full-state and global scheduling obligations remain on their separate open edges |
| representation | required-open | queue and DyadicSize reuse, SizeAnswer reuse, shared error injection/retraction, retained enqueue frames; full stream and promise embedding remains open |
| counterexamples | required-closed | seventeen retained finite witnesses and corresponding checked production laws; `WS-READ-CE-001` through `017` close for this local projection only |
| bridges | required-open | full-state projection and host profile relation, including exact arithmetic vs binary64 and promise-reaction registration; no host equivalence is asserted by P4a |
| targets | not-applicable | P4a has no lowering or generated code; P11 owns that target obligation |
| trust | required-closed | all 94 named theorem axiom receipts, exhaustive root audit, narrow tests, full build, root gates, and independent implementation review pass; see the landing receipt |
| coverage | required-open | clause map below and test-side witnesses with frozen signatures; no census row becomes green merely from this packet |

## Clause map and residual obligations

| Anchors | P4a obligations | Residual obligation before whole-row green |
| --- | --- | --- |
| GUARD, DESIRED, DEMAND | exact branch laws on the projection, including pending-read demand at HWM zero | relate the projection to unlocked/default-reader alternatives and host numeric boundary |
| ENQUEUE | initial guard, direct read bypass, deferred size, fresh-error abrupt paths, append, staged final demand; no post-size state recheck | IDL wrapper and full read-request callbacks; global reentrant operation and error-supply embedding |
| DEQUEUE, READ, ADDREAD, FULFILL | empty/nonempty FIFO branches, fresh read IDs, terminal reads, final-close-before-chunk, suspended read continuation across source pull | ownership/locking, disturbed slot, reader lifecycle, arbitrary request callbacks |
| CLOSE, CLEAR, STREAMCLOSE | closeRequested then drain; clear algorithms; closed settlement precedes read done/chunk | no-reader branch and global promise object/reaction model |
| ERROR, STREAMERROR | reset/clear; exact stored reason; closed rejection before reads; already-errored idempotence | no-reader/BYOB alternatives and promise handled bit / host objects |
| PULL | pulling/pullAgain, synchronous return vs later answer vs reaction distinction, reentrant source-call stack, return-time reaction attachment, fulfillment recheck, rejection, FIFO jobs | full host run-to-completion embedding, setup/start and global scheduler |

The independent review before freeze rejected the original atomic queued-read
postconditions: a synchronous pull can error the stream, enqueue another
chunk, or complete a nested read before the outer read's chunk steps. It also
rejected allocation-free generated error tags and a settlement-only object
named M2. CE-013 through CE-017 retain those findings. The revised packet
adds staged pull continuations, fresh generated error IDs, explicit query
events, and a local M2 value containing its M1 projection.

## Evidence ledger

Specification byte-span cross-check, green witness command, intended red
commands, and immutable packet commit are recorded after verification in
the contract's acceptance section. The coordinator owns root/known-red
integration and may append landing receipts; it may not weaken this packet.

## P4a landing receipt (coordinator, 2026-09-05)

Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`, the coordinator's
cherry-pick of the independent breaker commit
`5f8067a1bb657b6573f2d1d96dc136a427e52afd`. This receipt accompanies the
implementation commit; the coordinator handoff records its exact head.
The integration prerequisite is `319e7448cee9b958abca579e6e262377e4c760da`.

The seven source modules are `Whatwg/Streams/Boundary/Exception.lean` and
`Whatwg/Streams/Readable/{State,DefaultController,DefaultReader,Step,Laws,Reentrancy}.lean`.
Stable declarations retain the families in the table above. Module splitting
puts the twelve external-step/composition theorems in `Step`, the sixty-two
branch and projection equations in `Laws`, and the twelve quantified
regressions in `Reentrancy`. `Exception` owns six adapter/identity theorems
and `State` owns the two numeric-view theorems. All 94 are ascribed by the
frozen test battery. The local private `Except` equality deriving helper in
`State` exports no global orphan instance. Three private next-read helpers
in `Laws` support the frozen `read_nextRead` statement.

Other files in the landing fence: `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`WhatwgTest/Streams/Readable/DefaultContract.lean`,
`test/fixtures/trust-gate/known-red.txt`, `harness/readable/reentrancy.mjs`,
`test/counterexamples/REGISTER.md`, this graph, `PLAN.md`, and
`COORDINATION.md`. The frozen contract, axiom list, and seventeen independent
witness bodies are unchanged; no generated or vendor file is edited.

The sole battery repair indents the continuation argument of
`Data.Queue.empty` in `initial_eq` by two spaces. The previously absent
`State` hid that layout error during intended-red verification. The
`WhatwgTest/AGENTS.md` elaboration-repair allowance applies: no token in the
statement changes, and `git diff --ignore-all-space` for the battery is
empty. SHA-256 before the repair:
`8527abcf8d1acbd9fde0ce73308e03231421271481d30fe7d0812a8dc1d6bc3d`;
after the repair:
`d40222414247070167389468db14eaca9d4510bb76fcad63e8276201d223b2a4`.
The breaker acknowledged the repair and the independent reviewer checked it.

### Verification

All Lean commands used the pinned Lean 4.33.1 with `LEAN_NUM_THREADS=1`.
The following commands passed on the integrated implementation:

```text
lake --log-level=warning build WhatwgTest.Streams.Readable.DefaultContract WhatwgTest.Streams.Readable.DefaultAxiomReport WhatwgTest.Streams.Counterexamples.Readable.Default
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Readable/DefaultAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/readable/reentrancy.mjs
git diff --check
```

The narrow build passed 63 jobs and all 204 exact ascriptions. The default
build passed 260 jobs. The 94 named theorem receipts comprise five
axiom-free proofs, thirty-six at `[propext]`, and fifty-three at
`[propext, Quot.sound]`; none reaches `Classical.choice` or a forbidden
axiom. The exhaustive root audit checked 121 modules and 7675 declarations,
including 1595 declarations in the Gates tooling tree, under R-11.
The two now-green battery entries were removed from the known-red list.

The vendor seal checked 206 files in five pinned trees; the citation and
schema drift gates passed. Both standard census projections passed their
drift checks. Infra still has no semantic numerator. Streams' report below
was produced at base `f4394d81d59739dd1410c6cc16df17ee147d6e1f` with this
implementation working tree; its numerator inputs are unchanged:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The host command passed four finite probes for `WS-READ-CE-013` through
`016` under Node `v22.23.2`, `node:stream/web`, Windows x64. The fixture
records exact Streams/reference/WPT pins, each tape, the observed components
of M1/M2, and reaction-registration assumptions. It executes neither the
pinned reference implementation nor WPT. It proves no general host relation.

### Independent review and residual obligations

The separate reviewer checked the frozen surface, source algorithms,
reentrancy laws, trust mechanisms, and claim scope without editing production
code. It found no landing blocker: captured continuations survive terminal
reentrancy; admitted size returns do not recheck the entry guard; all live
callback frames prevent job execution; return and settlement remain separate;
and fresh generated errors retain distinct identities. The coordinator ran
the commands above; this review is not a substitute for those receipts.

Only laws, counterexamples, and trust close at this landing. Identity stays
open for the generated declaration snapshot and joins. Construction stays
open for reachable-state and fresh-ID invariants. Semantics, representation,
and bridges stay open for the full-state, shared-allocation, global-job,
promise-object, and host-profile embeddings. Coverage stays open for the
clause map and test-side numerator witnesses. Targets are not applicable to
P4a and remain P11 work. In particular `Steps` composes external decisions
only; it does not yet interleave internal jobs or prove a global run law.

The seventeen retained attacks are closed by their linked production
equations for the named local projection. This does not close full P4 or
weaken the clause-map residuals. The next implementation depends on the P5a
writable breaker freezing its own packet, while the other breadth contracts
remain required before deeper readable/writable work.
