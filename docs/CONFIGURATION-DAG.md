# Configuration ordering proof graph (`CONFIGURATION-PG-ORDERING`, P8a / slice Q4)

Status: **frozen red**, 2026-09-07, by the Q4 restatement breaker seat.
Contract: `test/contracts/configuration-ordering.contract.md`.
Base: `main` at `f700230`. Branch `promise/q4-breaker`.

This graph is the held P8a proposal graph, re-homed into this repository and
restated against the promise libraries slice Q3 landed. Its source is the
read-only draft at
`C:\Users\kokok\Dev\lean4-WHATWG-streams-configuration-breaker`
(`docs/CONFIGURATION-DAG.md` at `codex/configuration-breaker`, checkpoint
`6c44e08` plus uncommitted edits). Nothing in that worktree was modified.

The graph owns the global scheduling and local-to-configuration relations. The
existing P4/P5/P6/P7 graphs retain their declarations and algorithm ownership,
and `PROMISE-PG-FIRST` retains the promise libraries. This graph adds adapters
and obligations; it duplicates no canonical operation and closes no residual
edge of another graph by mentioning it.

## Source anchors

The semantic owner is `vendor/whatwg-streams-b9ba9f49/index.bs` at Streams
commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18`. The eleven census byte
spans below are carried over from the draft, where they were independently
rehashed against the sealed source on 2026-09-05 and all eleven matched
`generated/spec-algorithm-census.tsv`. That was a byte cross-check, not a Lean
gate run or a semantic receipt, and this seat did not re-run it.

| Alias | Census anchor | Byte interval | SHA-256 |
| --- | --- | --- | --- |
| WRITE | `op.writable-stream-default-writer-write` | `[265111,266478)` | `d2b5ad5bcd6b399fef2ab19fba5e9aa683811ed082adaff7232e68ef5e3179c4` |
| SIZE | `op.writable-stream-default-controller-get-chunk-size` | `[275369,276291)` | `20517642266cd527180b239f5ea6cc1d3b694a632bae05296560c25f945f1872` |
| ADD | `op.writable-stream-add-write-request` | `[249249,249720)` | `7b0d6cae2c0f549b7ed453ec45aa9087b6cb6855c1b11c4aa0c8a8e2a9e31959` |
| CWRITE | `op.writable-stream-default-controller-write` | `[279182,280164)` | `8d61c07286fd9969ce15072dadfb9df0d9421859aff11314496889f48dd72a84` |
| PROCESS | `op.writable-stream-default-controller-process-write` | `[277701,279180)` | `ca9fedd0d674c0ea84b8719cde61fa478c49d330335375443a18e15de996983a` |
| FINISH | `op.writable-stream-finish-in-flight-write` | `[254872,255330)` | `0154f894cbb72a0ccee1674c0ca04aa63fc6d6dee2594bfc0910bfba5cb67880` |
| ADVANCE | `op.writable-stream-default-controller-advance-queue-if-needed` | `[271219,272322)` | `ee221518afc480ddbd35c6903d9a74f22f8f4182cb7f85a1504b29283d761cbe` |
| BP | `op.writable-stream-update-backpressure` | `[259579,260455)` | `9d09e57a740c4c8b1c915b1b5383d35098200d53568e283b575b901bec70c7bf` |
| START | `op.set-up-writable-stream-default-controller` | `[266663,268928)` | `2eeec7ee3d989e7d2ef402a7ab2be535e0b659e53271fcb6818f5b4b7d94921e` |
| DEFAULTSTART | `op.set-up-writable-stream-default-controller-from-underlying-sink` | `[268930,271217)` | `73c1fc5422ff7623809f041483b4c8cf19d46589b6fd61c4a238724a54d98f64` |
| ERRORSTART | `op.writable-stream-start-erroring` | `[258600,259577)` | `601a3534cfe044f49e5c3f06da61766c84944e3e31b8e408b4da15a6cac9ecbf` |

ERRORSTART records the additional `started` guard a broader failing-start
profile needs. The restricted successful P8a prefix must prove it cannot reach
that branch; it does not implement the branch by omitting its guard.

**Promise-layer anchors, new at Q4.** The draft says "Imported ECMAScript/Web
IDL promise semantics retain their named runtime profile boundary until
separately pinned and related". They are now pinned and related. The anchors
this graph reaches into `PROMISE-PG-FIRST` are, by ES2026 byte span into
`vendor/ecma262-0248456c/spec.html` and Web IDL byte span into
`vendor/whatwg-webidl-a652053f/index.bs`:

| Alias | Anchor | Byte interval | Reached by |
| --- | --- | --- | --- |
| PSTATE | `slot.PromiseState` | `2744957..2745252` | `lookup`, `lookup_bridge` |
| PRESULT | `slot.PromiseResult` | `2745263..2745619` | as PSTATE |
| REACTREC | `record.promisereaction-records` | `2690445..2692671` | `Reaction`, `Registration`'s six ascriptions |
| RTYPE | `field.promisereaction-records.Type` | `2691815..2692138` | `Reaction.mk`'s fifth argument |
| RHANDLER | `field.promisereaction-records.Handler` | `2692151..2692611` | `Reaction.handler` |
| TRIGGER | `op.triggerpromisereactions` | `2700260..2701212` | `notifySettled`, `notifySettled_reactions_bridge` |
| HOSTENQ | `hook.hostenqueuepromisejob` | `633447..635836` | `enqueueJob`, `enqueueJob_queue_bridge` |
| ORDER | `requirement.hostenqueuepromisejob.3` | `634739..634841` | `episodePrefix_jobQueue_eq`, `step_active_jobQueue_eq` |
| RUNCOND | `requirement.jobs.1` | `625769..626250` | `activeErase`, `runCondition_iff` |
| ONEJOB | `requirement.jobs.2` | `626257..626350` | as RUNCOND |
| REACT | `op.dfn-perform-steps-once-promise-is-settled` | `350075..352408` | `register`, `register_reactions_bridge` |
| UPONF | `op.upon-fulfillment` | `352410..352816` | the one-sided handler of `register` |

The WPT block and helper paths and digests are in the contract, §3.1 and §3.2.
They are evidence anchors. DB-03 supplies the deterministic FIFO ruling, DB-04
fixes the masks, DB-11 fixes the promise-library owners. No adapter becomes a
second owner of WRITE, FINISH, PSTATE, HOSTENQ or any other anchor.

## Existing owners and proposed declaration roles

All names are provisional until the Q4 builder lands them. Future modules lie
under `Whatwg/Streams/Semantics/`; nothing below the configuration layer may
import that layer to make an adapter work.

| Proposed family | Module | Relationship / duplicate prevention | Required route |
| --- | --- | --- | --- |
| `Ecma262.Promise.Ref` (re-homed `PromiseRef`) | `Whatwg/Ecma262/Promise.lean`, landed | address view of retained canonical component promise cells; **owned by `PROMISE-PG-FIRST`, used here** | that graph's identity edge |
| `Ecma262.Promise.Reaction`, `.ReactionPhase` (re-homed `Registration`, `ObserverPhase`) | `Whatwg/Ecma262/Promise.lean`, landed | first-order reaction record and phase; **owned by `PROMISE-PG-FIRST`, used here** | that graph's representation edge |
| `Ecma262.Jobs.Queue`, `.Active`, `.RunCondition` | `Whatwg/Ecma262/Jobs.lean`, landed | payload-polymorphic FIFO and activation state; **owned by `PROMISE-PG-FIRST`, reached here through `jobQueue` and `activeErase`** | that graph's semantics edge |
| `Semantics.Ordering.Config`, `Startup`, `Active`, `Event`, `Decision` | `Configuration.lean` | separate configuration calculus embedding the actual P5 `State` and `Control`; START/ADVANCE and DB-03; `Active` carries the `Job` record five laws consume (contract §2.5) | graph construction/semantics |
| `Semantics.Ordering.JobKind`, `Job` | `Configuration.lean` | the payload of `Jobs.Queue`; `Whatwg.Ecma262.Jobs` has no general job record and `ReactionJob` is not one (contract §2.3) | graph representation |
| `Semantics.Ordering.jobQueue`, `reactions`, `activeErase` | `Configuration.lean` | the three Q4-owned views onto the landed carriers, following Q3's `Writable.jobQueue` / `Writable.promiseTable` / `Transform.reactions` pattern | graph bridges |
| `lookup`, `lookupRegistration`, `enqueueJob`, `setRegistrationPhase`, `register`, `notifySettled`, `liftWritable` | `Configuration.lean` or a narrowly named adapter module | views and adapters of P5 lookup/fresh/settle and of the landed `Table.get`, `Reactions.get`/`.setPhase`, `react` and `triggerReactions`, with exact prior-cell retention and insertion receipts | graph representation/laws |
| `WellFormed`, `Reachable`, token/mailbox correspondence | `Configuration.lean` / `Step.lean` | derived cross-component invariants, not validators accepted on arbitrary records | graph construction/laws |
| `Step`, `Reaches`, `EpisodePrefix`, `episodePrefix_jobQueue_eq` | `Step.lean`, `Runs.lean` | deterministic internal scheduler plus explicit compatible decisions; START/PROCESS/ADVANCE, ORDER and DB-03 | graph semantics/laws |
| canonical event lift, `observeLive`, `observeWptOrdering`, M1/M2 mapping | `Mask.lean` | adapters of canonical P5 events and DB-04; WPT callback logs are separate from settlement/query events | graph bridges/laws |
| `Semantics.Ordering.Source.*` | `Whatwg/Streams/Semantics/` | the independent source-occurrence, causal-prefix and erasure judgments; no mutable table, no scheduler, no `Config` field (contract §6.1) | graph bridges |
| bounded runner / frontier | `Runs.lean`, `Frontier.lean` | approximation of relational runs; DB-07, no fixed-fuel bind law and no timeout-as-divergence | graph semantics/laws |

`Readable.PromiseState`, `Writable.UnitPromise`, `SinkReturn`, `SinkJob`,
`Writable.State.promises`, `Boundary.Exception` and the P3 numeric and queue
types keep their current owners. At Q4 the first three and the `promises`
slots become **views** naming `Whatwg.Ecma262.Promise` as the shared owner,
with the conversion receipts `E-07`..`E-12`; §4 of the contract freezes the
four record-row edits. No P8 promise-outcome enum and no second table is
proposed. The P8a observer profile still has no exposed derived promise
result; that abstraction needs the CFG-WPT prefix-erasure obligation below.

## Obligations needed for the first representative

Carried over from the draft, with the Q4 restatement folded into CFG-CELLS,
CFG-TOKENS and CFG-FIFO.

| ID | Obligation and required evidence |
| --- | --- |
| CFG-START | Derive the original synchronous WPT write/registration prefix under the successful default-start gate. Pre-start ADVANCE is inert by its source guard. Prove the restricted pre-start invariant: writable status, finite nonnegative sizes, no erroring stages, only nested writes and registrations and normal returns. A broader profile also needs ERRORSTART's `started` guard. The successful-start job stages the actual canonical P5 ADVANCE. Prove exact queued-request and registration correspondence; bare post-start initialization is insufficient. |
| CFG-CELLS | Unique canonical table ids, allocation freshness, retained old cells, monotone cursors, stable owner-qualified references, and captured observer identities. Establish from admitted initialization and preserve by every reachable step. The successful fixture allocates no generated exception. **Q4:** the owner qualification lives in `Ecma262.Promise.Ref` and the cell lookup in `Ecma262.Promise.Table.get`, joined by `lookup_bridge`; `Reaction.promise`'s bare `Nat` is sound only under this obligation's registration-owner clause (contract §2.4). |
| CFG-TOKENS | A bijection between queued intrinsic tokens for each root and the ordered canonical `Writable.jobs` payloads, plus one active ownership location after dequeue. Observer registration phases are disjoint and once-only. A queued token never chooses a non-head local payload. **Q4:** the token queue is read as `Ecma262.Jobs.Queue Job` through `jobQueue`, and the registration phases as `Ecma262.Promise.ReactionPhase`; the two cursors stay unrelated (contract §2.7). |
| CFG-EFFECTS | For each wrapped P5 stage, prove the exact sequence of newly enqueued intrinsic and observer tokens at its settlement and attachment points. Relate the underlying state update to the actual `Writable.tick` / `decide`; registration and observer administration stutter on the P5 stream state. |
| CFG-STACK | Global activation ownership extends the actual P5 synchronous frames; administrative continuations and nested foreign returns drain before another job. A foreign frontier does not permit checkpoint execution. Prove stack and depth and return matching on reachable runs. **Q4:** RUNCOND and ONEJOB are reached through `activeErase` and `runCondition_iff`, not by a second activation state. |
| CFG-FIFO | Old queue tails remain before newly appended jobs; settlements queue registered handlers in registration order; registering on a settled cell queues immediately; no queued observer executes during an active episode. **Q4:** `episodePrefix_jobQueue_eq` states R-P12's `active_episode_fifo_suffix` over `Ecma262.Jobs.Queue.enqueueAll` against ORDER, and `register_reactions_bridge` and `notifySettled_reactions_bridge` carry the reaction half onto REACT and TRIGGER. The PROCESS/ADVANCE corollary is still owed. |
| CFG-RUNS | Deterministic internal steps; prefix comparability under a fixed consumed external tape and endpoint uniqueness at normalized frontiers; finite run composition; no spontaneous callback answer or script return; missing decisions and fuel are live frontiers. |
| CFG-LOCAL | After START, erase configuration-only registrations and tokens and project each intrinsic or external P5 step to the actual P5 local step or run, with observer administration as stuttering. Because P5 permits local interleavings not admitted globally, do not assert that every raw local run lifts; state the compatibility condition for the converse. |
| CFG-OBS | Lift canonical P5 settlement and query events with exact addresses and trace prefixes. Give the explicit local ordered-view relation and the profile-limited M2 mapping. Prove observer logs from their registration and execution history, not by relabelling settlements as callback runs. |
| CFG-WPT | Relate the finite first-order foreign-boundary script to the exact pinned WPT assertion prefix, including default start. Define an independent source-occurrence, binding and use certificate; checking the erased tape against itself is insufficient. Prove that the omitted derived `.then` results and the later flush, timer and assertion tail cannot affect earlier selected logs. Then execute the actual P5-backed finite witness and its scheduler mutants. **Q4:** the surface is frozen in `WhatwgTest/Streams/Semantics/OrderingSource.lean` and §6 of the contract. |
| CFG-HOST | Later run the selected original WPT under exact Node, Bun and reference profiles and relate the captured boundary and observer trace to the named model projection. A timer-based harness end and a model live stream remain different judgments; any disagreement is a profile row. |

These are proof obligations, not assumptions to insert as new axioms. Raw
records may violate them. The first representative cannot claim a global
embedding merely from the local equations or an unchanged host trace.

## Required residual embeddings for the full P8 goal

Carried over from the draft, unchanged.

P4 stores read cells separately from its unit closed cell, and its closed
settlement has no allocated `Nat` id. A global adapter needs a stable typed
address and generation view for those cells, a binding between actual pull
invocation and returned promise, and a proof that global token projection
matches `Readable.jobs`. `Readable.Steps` is external-only, so its global
internal-job extension needs an explicit relation. Full setup and start and
reachable freshness stay open. Q4's `E-22` operations
(`Readable.freshReadCell`, `settleReadCell`, `settleReadCells`) give the read
table the `fresh`/`settle` face the global adapter will need, but allocate no
identity for `Readable.State.closedPromise`: `E-24` keeps that cell by value,
and giving it an identity is a P8 change with M2 consequences.

P6 already uses actual P4/P5 states and retains a top-level coupled job queue
plus component mailboxes. A future global token must correspond to the P6
coupled job once and must not separately schedule its nested P4/P5 payloads.
The embedding must retain OLD backpressure write subscriptions, NEW
`SourcePull` return identities, adopted result routing, native port ownership
and live callback suspension. Q4 lands `Transform.notify`'s insertion receipt
and `Transform.runJob`'s dequeue receipt against the global queue (contract
§5.1 and §5.3); the ordered-effect receipt against the *global* configuration
queue is still owed.

The full configuration must not store a transform's embedded writable half
again as an independent writable root. Root ownership and slot-reference maps
need disjointness and aliasing laws. Multiple roots need shared error-supply
and transported-reason identity proofs in addition to qualified promise ids.
General read-result values, observer derived results, foreign returned
promises, cross-root promise sharing, thenables, adoption, cancellation, abort
signals and handled-state bookkeeping remain required work; gaps `G-02`,
`G-04`, `G-05` and `G-11` of `docs/PROMISE-EXTRACTION-INVENTORY.md` name the
promise-layer half of that list.

P7's requirements and realizer must embed into the same scheduler without
making finalization, pipe-promise settlement or lock release appear before its
canonical component operations exist. The complete bounded runner, all local
host profiles, complete M1/M2 mappings and the clause-level coverage join
remain P8 obligations. None becomes an exclusion from the overarching
reification.

## Ten edges

| Edge | Status | Required work |
| --- | --- | --- |
| identity | required-open | the exact declaration freeze this packet states; canonical address views; stable registration and job names; the generated declaration join. The 15 class [R] ascriptions elaborate today and are the only part delivered |
| construction | required-open | CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and inductive reachable-state preservation |
| semantics | required-open | CFG-EFFECTS, CFG-FIFO, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers |
| laws | required-open | the 54 restated law ascriptions, the 15 Q4-owned bridging receipts and the 18 deferred-generalization ascriptions, each under the mask its docstring names |
| representation | required-open | one cell and payload owner, typed references, no closures and no shadow scheduler or table; the four view record rows of contract §4.1 and their twenty elaborating ascriptions |
| counterexamples | required-open | the actual configuration witness, the stable registered scheduler mutants and the retained failing alternatives. No WS-CONFIG id is frozen by this packet; `test/counterexamples/REGISTER.md` is outside its fence |
| bridges | required-open | CFG-LOCAL, CFG-OBS, CFG-WPT, CFG-HOST and the full P4/P5/P6/P7 embeddings; the three Q4 views and the four deferred generalizations are the part this packet states |
| targets | not-applicable | this graph generates no target program; P11 owns target lowering |
| trust | required-open | independent design review, the frozen red battery (delivered), the proofs, the 82 axiom receipts inside the R-11 ceiling, and the narrow, default and gate builds |
| coverage | required-open | the exact clause and numerator joins. This packet changes no coverage state: contract §7.4 recomputes the Streams totals and every one is unchanged, and §7.6 records that no frozen number moves |

`targets` is the only permanently not-applicable edge. No edge is closed by a
compiling battery alone, and none is closed by this freeze.

## Decision record

### Carried over from the draft

The ten decisions of §3.3 of the contract are the draft's, unchanged in
content: one writable root with a global token FIFO over the canonical P5
mailbox; two separate monotone supplies for registrations and job serials; the
represented original start prefix under a one-guard startup adapter and a
proved all-successful pre-start profile; three distinct observation records
with the WPT diagnostic projection separate from DB-04 M2; a live
finite-prefix M2 result with no terminal outcome and no sink-input field; a
dedicated checkpoint dequeue that leaves the local trace unchanged; an
intrinsic/empty-control gap that admits no author decision; prefix
comparability under a fixed external word with endpoint uniqueness only at
normalized frontiers; an independently source-checked prefix-erasure
certificate; and the namespace `Whatwg.Streams.Semantics.Ordering`.

The draft's review history is carried over as history: coordinator acceptance
of the WPT candidate and the canonical-mailbox residency; the independent
review that found the ERRORSTART `started` guard; the two later correctness
conditions (the intrinsic gap admits only the deterministic finish step, and
the checkpoint sink dequeue uses a separate receipt); the live-M2 filter; the
explicit erasure of the post-O2 flush enqueue and its pending token; and the
prefix-comparability/normalized-uniqueness split. None of that closed an edge
then and none closes one now.

### Made at the Q4 restatement, 2026-09-07

1. **The re-homing is a three-way split, not the reuse table's.** 15 [R],
   19 [B], 124 [A]; contract §2.1 and §2.2. R-P13's "move for types,
   generalize for functions" is the ruling that fixes the shape.
2. **None of the reuse table's eight "direct" ascriptions is direct.**
   Contract §2.3. `Whatwg.Ecma262.Jobs` landed no general `Job` record;
   `Jobs.ReactionJob` is anchored to `op.newpromisereactionjob` and a startup
   or sink token is not a reaction job; `enqueueJob` allocates a serial and
   emits an event that `Queue.enqueue` does not; `queuedJobs` is a trace
   filter with no counterpart.
3. **`Active` stays in Streams and erases onto `Jobs.Active`.** Contract §2.5.
   Five class [A] laws consume the whole `Job` record, and one emits
   `.jobFinished job` from it; a bare serial cannot supply it.
4. **`Registration` re-homes onto `Reaction Nat`, with three stated changes.**
   Contract §2.4: `mk` gains the `[[Type]]` tag, `promise` becomes the bare
   cell under CFG-CELLS' owner clause, and `callback` becomes
   `handler : Option body`.
5. **`register` and `notifySettled` are bridged on their reaction half only.**
   Contract §2.6. The landed operations write a reaction-job queue; this
   configuration has one heterogeneous token queue, which is the whole reason
   the draft exists.
6. **`ReactionPhase.queued` carries the job serial here**, where the landed
   `react` and `performPromiseThen` write the registration id. Contract §2.7;
   Q3b-sensitive.
7. **The CFG-WPT judgments are ascribed under
   `Whatwg.Streams.Semantics.Ordering.Source` rather than declared test-side.**
   Contract §6.1, with the alternative recorded as an open decision for the
   coordinator.
8. **`slot.promise-state` and `slot.promise-is-handled` become `owned` in the
   Streams census; `slot.value` stays `foreignBoundary`.** Contract §7.
   No Streams coverage number moves.

## Evidence ledger

The specification byte-span cross-check, the intended-red commands and their
exact diagnostics, the ascription counts per battery and the immutable packet
commit are recorded in the contract's "Freeze receipt". The coordinator owns
root and `known-red` integration, the release of the configuration-breaker
hold in `COORDINATION.md`, and may append landing receipts; it may not weaken
this packet.
