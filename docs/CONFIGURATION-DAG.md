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

### Made at the Q4 amendment, 2026-09-07, branch `promise/q4-amend`

Breaker-owned, over the first builder pass. Decisions 1 to 8 above are
unchanged; 9 to 13 are added. Contract §12 carries each with its superseded
text, and every changed battery line carries its own dated comment. No edge
closes here and none reopens: the amendment states, it implements nothing.

9. **Ruling R-P25's three ascriptions are applied to the frozen batteries.**
   `Reaction.mk` at six explicit arguments with `Option Capability` fifth
   (amendment A1, builder note B1); `register_eq`'s registered entry gains
   `none` at the fifth field (A2, note B2); `register_reactions_bridge`
   projects `x.2.1` rather than `Prod.fst`, because `WebIdl.Promise.react`
   returns the table first (A3, note B4). The first builder pass had applied
   A2 and A3 in the implementation with recorded notes and stopped on A1; the
   frozen text now matches.
10. **The false reaction-half bridge is restated by erasure, not by a carried
    map.** Amendment A4, builder note B3, counterexample `WS-PROM-CE-039`.
    `notifySettled_reactions_bridge` was false as frozen — decision 6's two
    cursors put a job serial in the configuration's `ReactionPhase.queued`
    where `op.triggerpromisereactions` puts a registration id — so it is
    restated modulo the new Q4-owned `Semantics.Ordering.reactionErase`, under
    a `Nodup` hypothesis on registration ids, and the payload it drops is
    recovered exactly by the new `notifySettled_queued_serial`, which ties it
    to the token FIFO's own serial supply. The rejected alternative, a
    serial-to-id map carried by the configuration, would add a tenth field to
    the frozen nine-argument `Config.mk`, which decision 3 already refused for
    `runningJob`, and would contradict decision 2's two unrelated supplies.
    Decision 6 is unchanged and R-P25 confirms it.
11. **The CFG-WPT seam is re-frozen as 86 total first-order ascriptions.**
    Amendment A5. The frozen 28 pinned no carrier — eleven bare types, four
    `Prop`s with no checker — which is why the first pass recorded §6 not
    attempted. Added: the pinned block's digests; a `ScriptAction` carrier for
    the finite first-order boundary script with its pinned `wptScript`; the
    `Attachment` and `Certificate` constructors and the `Binding`; four `Bool`
    checkers (`sourceCheck`, `causalCheck`, `retainedFifo`, `profileCheck`)
    with their `Prop`s and the `_iff` equations that keep them from being
    widened; a `SelectedLog`/`ReferenceEvent` alphabet over attachment,
    return, settlement and FIFO enqueue/start/finish; the `referenceErase`
    map; the pinned certificate, reference and selected prefix with three
    non-vacuity receipts; and the draft's three certificate mutants with three
    rejection receipts. Seven tightenings T1 to T7 are recorded in contract
    §12.3. The ownership route of decision 7 is unchanged.
12. **`run_erases_to_reference` moves to P8.** Amendment A5, tightening T5. As
    frozen it is false, not merely hard: it quantifies over an arbitrary start
    configuration, and `Reaches c [] c` for a fabricated `c.trace` has no
    causal reference trace. With the missing `c = initial …` hypothesis its
    proof still needs `WellFormed` initialization and preservation, the
    token/mailbox correspondence, the ordered-effect receipts, the
    successful-profile progress theorem and the finite witness through the
    original start gate, none of which this packet states. Three further items
    split to P8 for the same kind of reason: the agreement of the frozen
    digests with the sealed WPT bytes (a gate, not a theorem — no first-order
    definition reads `vendor/`), the numeric chunk values of the asserted
    array (the decision alphabet is polymorphic in the chunk type), and the
    `WS-CONFIG` register rows for the three mutants. The `bridges` edge stays
    open on `CFG-WPT` for exactly the existence half.
13. **The re-disposition of decision 8 breaks a second frozen battery.**
    Amendment A7. `lake exe census --write` shortens
    `WhatwgTest/Audit/SpecCoverageRows.lean` by 20 bytes, and
    `WhatwgTest/Audit/CensusProfileIdentity.lean` — frozen by the Q1 packet
    `test/contracts/census-profile-identity.contract.md`, not by Q4 — pins that
    file at 32032 bytes and digest `d0e47fdf…`. Measured after the
    regeneration: 32012 bytes, digest
    `247f9909716c8153541174b72d96923fe766e263c07d717c95f149b38ebba63c`. The
    battery was red at `746032c` too and §11.5 did not list it. This seat
    declares it in `test/fixtures/trust-gate/known-red.txt` with the two
    replacement values and does not edit it; its owner or a coordinator ruling
    amends the pin. No Streams coverage number moves — a disposition is not a
    coverage state — so decision 8 and contract §7.4 stand.

## Q4 landing, 2026-09-07, branch `promise/q4-builder`

Appended by the Q4 builder seat. **Every row above this section is unchanged.**
No edge closes here: the landing is partial, four of the five batteries stay
declared red, and a compiling implementation is not a closed edge. Receipt: the
"Q4 landing receipt" of `docs/PROMISE-PACKAGE-PLAN.md`, which carries every
command and its result line; the four blocking items are §11.1 of the contract.

| Edge | Status before | Status at this landing | What moved |
| --- | --- | --- | --- |
| identity | required-open | **required-open**, unchanged | The 15 class [R] ascriptions elaborate against the landed `Whatwg.Ecma262` names, with the single exception of `Reaction.mk` (item B1: five arguments ascribed, six landed). No generated declaration snapshot exists, so the edge's own item is untouched |
| construction | required-open | **required-open**, unchanged | `E-22`'s three operations, five rewritten bodies and three table bridges landed, so `Readable.State.readPromises` is no longer a table without operations; CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and reachable-state preservation are untouched |
| semantics | required-open | **required-open**, unchanged | `tick`, `decide`, `takeSinkHead`, `Step`, `Reaches` and `EpisodePrefix` exist and their frozen equations are proved, and `runCondition_iff` reaches `Jobs.RunCondition` through `activeErase`. CFG-EFFECTS, CFG-FIFO's source-specific half, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers stay open |
| laws | required-open | **required-open**, and most of it delivered | 50 of the 54 restated law ascriptions and 11 of the 12 Q4-owned bridging receipts are proved; all 18 deferred-generalization ascriptions are proved. The four that are not are B1 to B4. `OrderingLaws.lean` fell from 327 diagnostics to 4 |
| representation | required-open | **required-open**, and the record change landed | The four view record rows of contract §4.1 read as frozen in `docs/READABLE-DAG.md`, `WRITABLE-DAG.md` and `TRANSFORM-DAG.md`, and the twenty ascriptions of §4.2 still elaborate. One cell owner, one payload owner, no shadow scheduler and no second table: `Writable.State.promises` read through `Writable.promiseTable` is the only outcome table the calculus touches |
| counterexamples | required-open | **required-open**, unchanged | No configuration witness, no registered scheduler mutant and no WS-CONFIG row is landed by this seat |
| bridges | required-open | **required-open**, and the Q4 halves landed | The three Q4-owned views `jobQueue`, `reactions` and `activeErase` exist with their receipts; the four deferred generalizations of contract §5 are all proved, which makes `WhatwgTest/Streams/PromiseBridgeQ4.lean` green. CFG-LOCAL, CFG-OBS, CFG-WPT, CFG-HOST and the full component embeddings stay open — CFG-WPT was not attempted at all |
| targets | not-applicable | **not-applicable**, unchanged | This landing generates no target program |
| trust | required-open | **required-open**, partially delivered | 79 of the 82 named receipts print, all inside the R-11 ceiling: 14 empty, 27 `[propext]`, 33 `[propext, Quot.sound]`, 5 `[propext, Classical.choice, Quot.sound]`. `lake exe trustselftest` passes in both directions against a four-module declared red set. Independent review is not done and the three missing receipts are B3 and the two §6 laws |
| coverage | required-open | **required-open**, unchanged | R-P5's re-disposition landed and no coverage state moved: the two rows are `owned` and still `absent`, the Streams block re-emits byte-identically, and all four census standards pass |

**Edges closed at this landing: none. Edges reopened: none.**

## Q4 amendment, 2026-09-07, branch `promise/q4-amend`

Appended by the Q4 amendment breaker seat. **Every row above this section is
unchanged**, including the landing table. No edge closes and none reopens: a
breaker amendment states, it implements nothing, and four of the five declared
batteries stay red by design. Receipt: §12.6 of
`test/contracts/configuration-ordering.contract.md`.

What the amendment changes about the edges' *required work*, without changing
any status:

| Edge | What the amendment changes about what is owed |
| --- | --- |
| identity | `Reaction.mk`'s ascription now matches the landed six-argument constructor, so all 15 class [R] ascriptions elaborate again; item B1 of the landing table is answered |
| laws | four of the 54 + 12 are answered, three by R-P25's text (A1 to A3) and one by restatement (A4). The Q4-owned receipt count rises from 12 to 15 |
| bridges | `CFG-WPT` is now split explicitly: the certificate carriers, the four checkers, the erasure and its two laws are Q4's and are stated; the existence half `run_erases_to_reference` is P8's, together with the transcription gate, the host replay and the mutants' register rows. The edge stays open on the P8 half |
| trust | 82 named receipts become 93. 79 print, all inside R-11; the 14 that do not are the names the second builder pass supplies. A fifth module, `WhatwgTest.Audit.CensusProfileIdentity`, is declared red for the reason decision 13 records, and the trust gate's all-green control stays unrestored |
| counterexamples | one row is seeded, `WS-PROM-CE-039`, against the packet's own false bridge. Its `test/counterexamples/REGISTER.md` entry is owed at landing; no `WS-CONFIG` id is frozen |

The other five edges are untouched by the amendment.

## Q4 landing, second pass, 2026-09-07, branch `promise/q4-builder-2`

Appended by the Q4 builder seat, second pass. **Every row above this section is
unchanged**, including the first landing table and the amendment table. Receipt:
the "Q4 landing receipt (second pass)" of `docs/PROMISE-PACKAGE-PLAN.md`, which
carries every command and its result line.

**No edge closes here either.** All five declared batteries are green, the 93
receipts print inside R-11 and `test/fixtures/trust-gate/known-red.txt` is
empty — and none of that closes an edge, because a compiling battery closes no
edge and this packet proves no `WellFormed`, no progress theorem and no host
relation.

| Edge | Status before | Status at this landing | What moved |
| --- | --- | --- | --- |
| identity | required-open | **required-open**, unchanged | All 15 class [R] ascriptions elaborate, item B1 answered by A1. Two Q4-owned views are added, `phaseErase` and `reactionErase`, and 86 `Source` names. No generated declaration snapshot exists, so the edge's own item is untouched |
| construction | required-open | **required-open**, unchanged | Nothing new. CFG-START, CFG-CELLS, CFG-TOKENS, CFG-STACK and reachable-state preservation stay open |
| semantics | required-open | **required-open**, unchanged | `notifySettled_queued_serial` ties a triggered registration's phase payload to the serial of the `.observer` token the same notification appended, under mask M2 — the first statement in this packet that relates the two supplies of decision 2 through the queue. CFG-EFFECTS, CFG-FIFO, CFG-RUNS, the foreign profile, the global scheduler and the live frontiers stay open |
| laws | required-open | **required-open**, and fully delivered as stated | All 54 restated law ascriptions and all 15 Q4-owned bridging receipts are proved, and all 18 deferred-generalization ascriptions were already. B1 to B4 are answered by A1 to A4. `OrderingLaws.lean` and `OrderingContract.lean` are at zero diagnostics. The edge stays open on the obligations §3.3 lists, which no law here states |
| representation | required-open | **required-open**, unchanged | The `Source` judgment adds no cell and no table: `Certificate`, `Binding` and `ReferenceEvent` are immutable source-side data, and `referenceErase` is a `List.filter`. Still one cell owner, one payload owner, no shadow scheduler and no second table |
| counterexamples | required-open | **required-open**, and three certificate mutants landed | `mutantSelectedD0`, `mutantAliasedResults` and `mutantFlushOnW0` exist with their three rejection receipts, which is what keeps `sourceCheck = fun _ => true` from satisfying every receipt above them. Their `WS-CONFIG` register rows are still owed, `test/counterexamples/REGISTER.md` being outside the fence, and `WS-PROM-CE-039`'s row is owed at landing. No configuration witness and no scheduler mutant is landed |
| bridges | required-open | **required-open**, and Q4's half of CFG-WPT landed | The whole seam is stated and proved as amendment A5 splits it: the four checkers with their `_iff` ties, the pinned certificate and reference with three non-vacuity receipts, `erasure_preserves_selected_order` on the reference side and `erases_prefix_selected_order` on the target side. The edge stays open on P8's half — `run_erases_to_reference`, the transcription gate, the host replay — and on CFG-LOCAL, CFG-OBS, CFG-HOST and the full component embeddings |
| targets | not-applicable | **not-applicable**, unchanged | This landing generates no target program |
| trust | required-open | **required-open**, and the receipt half delivered | All 93 named receipts print, all inside the R-11 ceiling: 16 with no axioms, 35 `[propext]`, 33 `[propext, Quot.sound]`, 9 `[propext, Classical.choice, Quot.sound]`. `lake exe trustselftest` passes in both directions against an **empty** declared red set, so the all-green control is restored. Independent review is still not done, and that is what the edge is now open on |
| coverage | required-open | **required-open**, unchanged | No coverage state moves. A7 amends the Q1 identity pin to 32012 bytes / `247f9909…a63c` under R-P26, which is a disposition fact, not a coverage fact; the Streams block re-emits byte-identically and all four census standards pass |

**Edges closed at this landing: none. Edges reopened: none.** What the landing
does close is the packet's own delivery list: the 158 restated ascriptions, the
15 Q4-owned receipts, the 38 `PromiseBridgeQ4` ascriptions and the 86 `Source`
ascriptions all elaborate, with no statement changed. The
configuration-breaker hold can be released on that basis; the coordinator owns
that sentence, and the "Q4 landing receipt (second pass)" of
`docs/PROMISE-PACKAGE-PLAN.md` carries it.

## Evidence ledger

The specification byte-span cross-check, the intended-red commands and their
exact diagnostics, the ascription counts per battery and the immutable packet
commit are recorded in the contract's "Freeze receipt". The coordinator owns
root and `known-red` integration, the release of the configuration-breaker
hold in `COORDINATION.md`, and may append landing receipts; it may not weaken
this packet.
