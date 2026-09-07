# Configuration promise ordering, DB-11 restated (slice Q4, `CONFIGURATION-PG-ORDERING`)

Status: **frozen red**, 2026-09-07, by the Q4 restatement breaker seat on
branch `promise/q4-breaker`, based on `main` at `f700230`.
Graph: `docs/CONFIGURATION-DAG.md`.
Red declaration: `test/fixtures/trust-gate/known-red.txt`.
Batteries: `WhatwgTest/Streams/Semantics/OrderingContract.lean` (107),
`OrderingLaws.lean` (66), `OrderingSource.lean` (28),
`OrderingAxiomReport.lean` (82 receipts), and
`WhatwgTest/Streams/PromiseBridgeQ4.lean` (38).

This contract re-homes the held P8a configuration-ordering draft into this
repository and restates it against the promise libraries slice Q3 landed. The
draft lives read-only at
`C:\Users\kokok\Dev\lean4-WHATWG-streams-configuration-breaker`
(`codex/configuration-breaker`, checkpoint `6c44e08` plus uncommitted edits):
`test/contracts/configuration-ordering.contract.md`,
`docs/CONFIGURATION-DAG.md`,
`WhatwgTest/Streams/Semantics/OrderingContract.lean` (104 `#check` on disk)
and `OrderingLaws.lean` (54). Nothing in that worktree was modified, and no
`lake`, `lean` or `lsp` was run there.

## 1. Claim boundary

This packet freezes statements. It proves nothing. It admits no declaration,
closes no graph edge, moves no coverage row, and asserts no relation to any
host. The 158 restated ascriptions and the 15 Q4-owned bridging receipts are
obligations; the WPT block supplies an assertion to replay under the authority
order of `AGENTS.md`, never a semantic owner. The identity, FIFO,
effect-order, replay, progress and independent source-prefix obligations
`PLAN.md` names remain open and are carried over unchanged in content.

Full P8 still owes readable, transform, piping, lifecycle, promise adoption,
the masks, the bounded runner, the WPT replay harness against the three local
host profiles, and the host-profile refusal rows. This lane ends where P8's
exit gate begins.

## 2. The restatement

### 2.1 It is a re-homing, not a rewrite

`docs/PROMISE-EXTRACTION-INVENTORY.md`'s P8a reuse table classifies all 158
draft ascriptions as **8 direct**, **32 rename only** and **118 Streams
adapter**. Q4 works from that table and does not re-derive it. The
arithmetic reproduces exactly: 8 direct is 6 in `OrderingContract` plus 2 in
`OrderingLaws`; 32 rename-only is `PromiseRef` (4) + `ObserverPhase` (5) +
`Registration` (6) + `Active` (5) + five operations + seven laws; 118 adapters
is 73 in `OrderingContract` plus the 45 laws the table names. Counted on disk:
104 + 54 = 158.

What the table could not know is what Q3 would land. R-P13 rules the shape of
every reuse: **move for types, generalize for functions**, because a function
that appears in an `attribute [local simp]` set loses its equation lemmas
under an `abbrev`. Applying that ruling to the P8a table gives three Q4
classes, and they are marked per block in the two batteries:

| Class | Count | What it means |
| --- | ---: | --- |
| **[R]** re-homed | 15 | the restated ascription **is** a landed `Whatwg.Ecma262` name. Elaborates today. |
| **[B]** bridged | 19 | the declaration stays in `Whatwg.Streams.Semantics.Ordering` and is joined to a landed name by one of the 15 Q4-owned receipts |
| **[A]** adapter | 124 | Streams-specific, carried over from the draft unchanged in content as well as in file |

15 + 19 + 124 = 158. Nothing in class [A] is reinterpreted.

### 2.2 The exact mapping, ascription by ascription

**Class [R] — 15, all in `OrderingContract.lean`, all green today.**

| Draft ascription | Landed name |
| --- | --- |
| `PromiseRef` | `Whatwg.Ecma262.Promise.Ref` |
| `PromiseRef.mk` | `Whatwg.Ecma262.Promise.Ref.mk` |
| `PromiseRef.owner` | `Whatwg.Ecma262.Promise.Ref.owner` |
| `PromiseRef.local` | `Whatwg.Ecma262.Promise.Ref.cell` (R-P18: `local` is a Lean 4 keyword) |
| `ObserverPhase` | `Whatwg.Ecma262.Promise.ReactionPhase` |
| `ObserverPhase.waiting` | `…ReactionPhase.waiting` |
| `ObserverPhase.queued` | `…ReactionPhase.queued` |
| `ObserverPhase.running` | `…ReactionPhase.running` |
| `ObserverPhase.done` | `…ReactionPhase.done` |
| `Registration` | `Whatwg.Ecma262.Promise.Reaction` at `body := Nat` |
| `Registration.mk` | `…Reaction.mk` (arity 4 → 5, §2.4) |
| `Registration.id` | `…Reaction.id` |
| `Registration.promise` | `…Reaction.promise` (`Ref` → `Nat`, §2.4) |
| `Registration.callback` | `…Reaction.handler` (`Nat` → `Option body`, §2.4) |
| `Registration.phase` | `…Reaction.phase` |

**Class [B] — 19, with the Q4-owned receipt that joins each.**

| Draft ascriptions | Landed target | Receipt |
| --- | --- | --- |
| `Active`, `.script`, `.intrinsic`, `.observer`, `.checkpoint` (5) | `Whatwg.Ecma262.Jobs.Active`, `requirement.jobs.1` (625769..626250) and `requirement.jobs.2` (626257..626350) | `activeErase`, `activeErase_eq`, `runCondition_iff` |
| `lookup`, `lookup_eq` (2) | `Whatwg.Ecma262.Promise.Table.get` over Q3's `Writable.promiseTable` | `lookup_bridge` |
| `lookupRegistration`, `lookupRegistration_eq` (2) | `Whatwg.Ecma262.Promise.Reactions.get` at `ReactionType.fulfill` | `reactions`, `reactions_eq`, `lookupRegistration_bridge` |
| `setRegistrationPhase`, `setRegistrationPhase_eq` (2) | `Whatwg.Ecma262.Promise.Reactions.setPhase` at `ReactionType.fulfill` | `setRegistrationPhase_bridge` |
| `enqueueJob`, `enqueueJob_eq` (2) | `Whatwg.Ecma262.Jobs.Queue.enqueue` (`hook.hostenqueuepromisejob`, 633447..635836) | `jobQueue`, `jobQueue_eq`, `enqueueJob_queue_bridge` |
| `register`, `register_eq` (2) | `Whatwg.WebIdl.Promise.react` (`op.dfn-perform-steps-once-promise-is-settled`, 350075..352408) | `register_reactions_bridge` |
| `notifySettled`, `notifySettled_eq` (2) | `Whatwg.Ecma262.Promise.triggerReactions` (`op.triggerpromisereactions`, 2700260..2701212) | `notifySettled_reactions_bridge` |
| `step_active_jobs_eq`, `episodePrefix_jobs_eq` (2) | `Whatwg.Ecma262.Jobs.Queue.enqueueAll` (`requirement.hostenqueuepromisejob.3`, 634739..634841) | `step_active_jobQueue_eq`, `episodePrefix_jobQueue_eq` |

`episodePrefix_jobs_eq` is the obligation R-P12 names `active_episode_fifo_suffix`.
R-P12 requires it stated over `Whatwg.Ecma262.Jobs.Queue`;
`episodePrefix_jobQueue_eq` is that statement, and the draft's `List` form is
retained beside it so that no class [A] law which mentions `c.jobs` has to be
restated.

**Class [A] — 124**, the table's 118 plus the six of §2.3. Every one carries
the draft's statement verbatim, up to the type substitutions of §2.4.

### 2.3 The eight "direct" ascriptions: none is direct

The reuse table calls eight ascriptions "already general; only the namespace
changes". Against what Q3 actually landed, **zero of the eight are direct**.

| Draft ascription | Table says | Q4 finding |
| --- | --- | --- |
| `Job` | direct | `Whatwg.Ecma262.Jobs` landed **no** general `Job` record. Its only job carrier is `Jobs.ReactionJob (reaction : Nat) (argument : arg)`, anchored to `op.newpromisereactionjob` (2702885..2705591) and `record.jobcallback-records` (628436..630247). A startup token and a sink token are not reaction jobs; calling them one would be a fidelity defect. `Jobs.Queue` is payload-polymorphic by decision 4 precisely so its client supplies the payload. **→ class [A].** |
| `Job.mk`, `Job.serial`, `Job.kind` | direct | as `Job`. **→ class [A].** |
| `enqueueJob` | direct | `Jobs.Queue.enqueue` is a tail append and nothing else; the draft's operation additionally allocates a serial from `nextJob`, advances that cursor and emits a `jobQueued` trace event. **→ class [B]**, bridged by `enqueueJob_queue_bridge`. |
| `enqueueJob_eq` | direct | as `enqueueJob`. **→ class [B].** |
| `queuedJobs` | direct | a filter over the configuration's own event list. `Whatwg.Ecma262.Jobs` has no counterpart at all, and none is wanted: a trace is Streams observation state. **→ class [A].** |
| `queuedJobs_eq` | direct | as `queuedJobs`. **→ class [A].** |

Consequently the honest split is **0 direct / 34 re-homed-or-bridged / 124
adapter**, not 8 / 32 / 118. The inventory's totals are not edited; this
section is the amendment, in the manner of R-P17 and R-P19.

### 2.4 The type substitutions inside class [A]

A class [A] ascription is carried over unchanged in content. Where a field or
argument *type* is one of the class [R] names, the ascription names the landed
type. That substitution is what re-homing is, and this is the exhaustive list:

1. `PromiseRef` → `Whatwg.Ecma262.Promise.Ref` in `Event.registered`,
   `Event.observerCalled`, `Decision.observe`, `lookup`,
   `decide_checkpoint_observe`, `register`, `register_eq`, `lookup_eq`.
2. `p.local` → `p.cell` wherever the field is projected (R-P18).
3. `ObserverPhase` → `Whatwg.Ecma262.Promise.ReactionPhase` in
   `setRegistrationPhase` and `setRegistrationPhase_eq`.
4. `Registration` → `Whatwg.Ecma262.Promise.Reaction Nat` in
   `Config.mk`, `Config.registrations`, `lookupRegistration`,
   `lookupRegistration_eq`, `setRegistrationPhase_eq`, `register_eq`,
   `notifySettled_eq`.

Three of those are more than a renaming, and each is stated rather than
smoothed:

- **`Reaction.mk` takes five arguments where `Registration.mk` took four.**
  The extra argument is the `[[Type]]` tag
  `field.promisereaction-records.Type` (2691815..2692138), which gap `G-01`
  records as absent from Streams and R-P18 decision 8 adopts. The restated
  `register_eq` builds `⟨id, p.cell, .fulfill, some callback, .waiting⟩`.
- **`Reaction.promise` is a bare `Nat`, not a `Ref`.** P8a has exactly one
  root; `Config.owner` carries the owner, `lookup` rejects a cross-owner
  address, and the draft's own `CellsWellFormed` already requires every
  registration owner to equal `c.owner`. The consequence is visible in one
  restated law: the draft's `notifySettled_eq` guard
  `r.promise.owner == c.owner && r.promise.local == id` becomes
  `r.promise == id`, and the owner conjunct is discharged by that invariant
  rather than restated per entry. This is what makes `notifySettled` a true
  instance of `op.triggerpromisereactions`, whose `Reactions.waitingOn` filter
  is `r.promise == promise && r.phase == waiting`.
- **`Reaction.handler` is `Option body`, not `callback : Nat`.**
  `field.promisereaction-records.Handler` (2692151..2692611) admits an empty
  handler, and Web IDL "upon fulfillment" (352410..352816) registers exactly
  one side. At `body := Nat` the fulfil entry carries `some callback` and the
  reject entry `none`, which is what `Reactions.add`'s two arguments are for.
  `Event.registered` and `Event.observerCalled` keep their bare `Nat`
  callback: they are adapters and are unchanged.

### 2.5 Where `Active` stops being a rename

`Whatwg/Ecma262/Jobs.lean`'s own docstring adopts the reuse table's reading:
"P8a rename class 'rename only': `Semantics.Ordering.Active`, with `observer`
renamed `job` and both job-carrying constructors taking a serial rather than
the whole record." The serial is the difference, and it is not a rename.

Five class [A] ascriptions consume the whole `Job` record through `Active`:
`authorFrontier_eq`, `tick_observer_empty`, `tick_intrinsic_empty`,
`decide_intrinsic_gap` and `takeSinkHead_matching`. `tick_intrinsic_empty`
emits `.jobFinished job` from it, and a bare serial cannot supply the record.
Adopting `Jobs.Active` directly would therefore force a statement change in
five of the 118, which the re-homing-not-rewrite rule forbids.

**Frozen choice.** `Semantics.Ordering.Active` stays, carrying `Job`, and
`Semantics.Ordering.activeErase : Active → Jobs.Active` is the Q4-owned
erasure onto the landed activation state, with `activeErase_eq` and
`runCondition_iff` as its receipts. The alternative — adopting `Jobs.Active`
and adding a `runningJob : Option Job` field to `Config` — changes
`Config.mk`'s arity, which is also a class [A] ascription, and is refused for
the same reason. `E-47` already fixes that `Writable.Control.react` is not a
second activation state; `activeErase` does not create a third.

### 2.6 Where the landed operations write a queue this configuration does not have

`Whatwg.WebIdl.Promise.react` and `Whatwg.Ecma262.Promise.triggerReactions`
both take and return a `Jobs.Queue (Jobs.ReactionJob (Except reason value))`.
The P8a configuration has **one heterogeneous token queue** carrying startup,
sink and observer tokens, which is the whole reason the draft exists: "Giving
all P5 jobs priority over consumer jobs produces the wrong trace."

So `register` and `notifySettled` are bridged on their **reaction half only**,
and `register_reactions_bridge` and `notifySettled_reactions_bridge` say so
explicitly. Q3 bridged `Writable.attachSink` on its job queue alone for the
same kind of reason (§4.4 row 5 of the Q3 contract: the general `react` must
not clear the close and abort algorithm slots). The queue half is carried by
`enqueueJob_queue_bridge` and the two FIFO-suffix laws instead.

### 2.7 The phase payload, and what Q3b may change

`ReactionPhase.queued (job : Nat)` and `.running (job : Nat)` are read in this
packet as carrying the **job serial**, which is the field's own name and the
draft's meaning: registration and job tickets use two unrelated monotone
supplies (`nextObserver`, `nextJob`), and `SerialsWellFormed` depends on that.
The landed `WebIdl.Promise.react` and `Ecma262.Promise.performPromiseThen`
instead write `ReactionPhase.queued rs.next`, the **registration id**, because
`Reactions` has one shared cursor. Both readings type; they are different
facts. The Q4 builder keeps the draft's two cursors and must not silently
inherit the landed operations' instantiation.

**Q3b-sensitive list.** A parallel Q3b breaker is freezing a fidelity addendum
that may change `Reaction` (gaining a `[[Capability]]` field, finding F4),
`performPromiseThen` (F1, F2), `waitForAll` (F6), and may add a settlement
trace to the general table. Each restated ascription below is marked
"Q3b-sensitive" and the Q4 builder re-checks it after Q3b lands:

| Ascription | Why |
| --- | --- |
| `Reaction`, `Reaction.mk`, `.id`, `.promise`, `.handler`, `.phase` (6, class [R]) | F4 adds a field; `mk`'s arity changes again |
| `Config.mk`, `Config.registrations` (2, class [A]) | element type `Reaction Nat` gains a field |
| `lookupRegistration`, `lookupRegistration_eq`, `setRegistrationPhase`, `setRegistrationPhase_eq` (4, class [B]) | `Reactions.get` and `.setPhase` range over `Reaction body` |
| `register`, `register_eq` (2, class [B]) | F2 changes `react`'s settled branches; F4 threads a capability |
| `notifySettled`, `notifySettled_eq` (2, class [B]) | F3 clears the non-triggered list, changing `settleAndTrigger`'s shape around `triggerReactions` |
| `reactions`, `reactions_eq`, `lookupRegistration_bridge`, `setRegistrationPhase_bridge`, `register_reactions_bridge`, `notifySettled_reactions_bridge` (6, Q4-owned) | all range over `Reactions`/`Reaction` |
| `readTable_freshReadCell`, `readTable_settleReadCell`, `readTable_settleReadCells` (3, §5) | a settlement trace on `Table.fresh`/`.settle` changes their signatures |
| `settle_table_bridge` (1, §5) | as above |

**22 Q3b-sensitive ascriptions.** Nothing here depends on `waitForAll`: the
draft has no wait-for-all ascription, and F6 touches none of the 158.

### 2.8 Two count corrections to the reuse table

- The table says "all ten `takeSinkHead_*` receipts". The draft carries
  **nine** on disk (`_matching`, `_active`, `_control`, `_empty`,
  `_not_head`, `_empty_mailbox`, `_not_sink`, `_wrong_key`,
  `_canonical_tick`); the tenth mention is `takeSinkHead` itself, in
  `OrderingContract`. The 45-law total is unaffected.
- The draft worktree's `docs/CONFIGURATION-DAG.md` records 102 and 44
  ascriptions where the modules carry 104 and 54. The re-homed graph in this
  repository records 104 and 54 and the Q4 additions beside them.

## 3. The re-homed P8a design record

Carried over from the draft, unchanged in content.

### 3.1 The selected pinned case

WPT commit `480fdfcd85d043c23875665f464c35c0043dff52`. File
`vendor/wpt-480fdfcd/streams/writable-streams/reentrant-strategy.any.js`.
Test title `writer.write() promises should resolve in the standard order`.
The complete test block is the UTF-8 byte interval `[930, 1956)` at that pin;
SHA-256 `386a437a784cb64e46681328c76fe921b755f89f9b64b891bc5ccfc377e3daf5`.
Whole-file SHA-256
`f1c493977d45b80e1acd6611dab52896f281d527fe54518d88c39dba200210aa`.
Tail dependency `vendor/wpt-480fdfcd/streams/resources/test-utils.js`,
`flushAsyncEvents`, SHA-256
`6ba682d4fa67f654de9c0d3516b6c3e0cdf1f0017085c866418cf93ced85cce7`.

The asserted array is

```text
size, 2, size, 1, size, 0,
sink.write, 0, sink.write, 1, writer.write done, 0,
sink.write, 2, writer.write done, 1, writer.write done, 2
```

The reference implementation's `PerformPromiseThen` helper describes itself as
an approximation; its extra rejection-check reactions are not normative jobs
to copy into the Lean scheduler. No WPT, reference implementation, Node or Bun
execution was performed for this packet.

**Amendment to the draft's authority note.** The draft's coordinator section
says "ECMAScript and Web IDL promise algorithms are not independently sealed
semantic sources in this repository; pinning/transcribing those algorithms is
a later authority decision". That decision has since been taken: both sources
are pinned in `SPEC-MANIFEST.md` (ECMA-262 `0248456c`, Web IDL `a652053f`),
censused at Q1/Q2, and modelled at Q3 under DB-11. The sentence is superseded;
the profile boundary it names is now the gap set `G-01`..`G-11` of the
inventory.

### 3.2 The twelve source occurrences

Byte intervals relative to the whole WPT file, hashed from their exact UTF-8
bytes. These are source-transcription inputs, not a parser proof; no expected
label list is an input to the source-use checker.

| Occurrence role | Byte interval | SHA-256 |
| --- | --- | --- |
| `sizeLog` | `[1031,1058)` | `7510676d5a833a66299d473f28840d07637bbab8eb383623a0ec8b363abc85c7` |
| `positiveGuard` | `[1065,1079)` | `28f40d8a6a6d5bc5760b907223315932de3754fb0ac9236e8b8b2a1bb55bc91a` |
| `nestedWriterCall` | `[1090,1113)` | `d5d4ed5c09faad7f8a1f676117bbc92681a954f07cc69966956085762ef28302` |
| `nestedObserverAttachment` | `[1126,1182)` | `b42c3cfa5a231120a2fb9614cd3689950fde3bf68452e74c5dffc973175ff1f5` |
| `sizeReturn` | `[1198,1211)` | `a8f98f8dcdc7e6daec5678b061ec88802a3710047b176579e46c43fa5c6fdc97` |
| `writableConstruction` | `[1236,1256)` | `b54f90618780d55c8585d0fe11be4ac0d0804d86ba83d734c672f8c97024d579` |
| `sinkLog` | `[1282,1315)` | `8e6e971e6fd96183f1b0ad0977113914cffc36d443fb7bbabc78648f62baa02e` |
| `writerAcquisition` | `[1340,1364)` | `787d79d99c9b5bf496a928aeee67188a283c0bb51b07299e2bfb5dd9a8781df2` |
| `outerWriterCall` | `[1367,1389)` | `c8246ccfffb442e273546c728cc32d214c09d4a4fa80a1eb2fe1a425154aa2b8` |
| `outerObserverAttachment` | `[1396,1444)` | `3ca2bf8cd597c7e8ba23bd001d50def47988112b1298088b37ebfb81235b967a` |
| `flushAttachment` | `[1451,1482)` | `60f507054f8c94a978e2113b5c795a7d1d726e1996c2ebe2014b9bc5a6b4d7d3` |
| `assertionCall` | `[1511,1538)` | `5614ae2f605f04d2ee884755fcc8dbedbc1dfc1faa849f4fc1da0e5cf2389e8c` |

The source-use graph is unchanged: `W0/W1/W2` are the three writer results,
`D0/D1/D2` the observers' derived results, `F` and `A` the flush and assertion
results. `D0` and `D1` have no uses; the flush callback requires completion of
`O2`; the assertion requires the flush chain; flush returns a promise and the
prefix restriction must not classify it as primitive-returning.

### 3.3 The decisions record, carried over

The draft's decisions are carried over in content and are re-affirmed here.

1. **One writable root plus a global token FIFO.** `Writable.State.promises`
   remains the sole outcome table; `Writable.jobs` remains the sole intrinsic
   payload owner, read as an ordered mailbox. No second promise table, no
   second scheduler, no copied `SinkJob` payload.
2. **Two separate monotone supplies** for registrations and job serials,
   unrelated to the promise cursor. See §2.7.
3. **The original start prefix is represented.** The narrow startup adapter
   implements `op.writable-stream-default-controller-advance-queue-if-needed`'s
   initial `started = false` return; the successful-start job stages canonical
   `.advance`. It is admitted only for the proved all-successful pre-start
   profile: finite nonnegative exact size returns, nested writes and observer
   registrations only, no controller error, close, abort, throwing size return
   or exceptional sink return. A broader profile owes
   `op.writable-stream-start-erroring`'s second `started` guard; the
   restricted prefix owes a theorem that it cannot reach that branch.
4. **Three distinct observation records**: lifted canonical settlement/query
   events; registration, enqueue and execution events; and
   `observeWptOrdering`, the diagnostic projection. The WPT diagnostic
   projection is not DB-04 M2 and does not add foreign sink calls to M2.
5. **A live finite-prefix M2 result** with no terminal outcome and no
   sink-input field. `m2Allowed` admits exactly `.settled`, `.readyRead`,
   `.closedRead` and `.desiredSizeRead`.
6. **A dedicated checkpoint dequeue.** It removes the matching global token
   and local mailbox head through the exact empty-control `Writable.tick`,
   leaves the local trace unchanged, and does not use the append-only
   `liftWritable` path.
7. **The intrinsic/empty-control gap admits no author decision**, only the
   deterministic `jobFinished` step.
8. **Prefix comparability under a fixed consumed external word**, with
   endpoint uniqueness only at normalized frontiers (`tick c = none`).
   Normalization is not completion and not promise settlement.
9. **An independently source-checked prefix-erasure certificate.** Comparing
   the erased tape with itself proves no WPT relation; the expected event
   array is not an input to the checker.
10. **The candidate namespace is `Whatwg.Streams.Semantics.Ordering`.** A
    later multi-root registry owns root-address allocation.

Everything the draft lists as still required is still required: `WellFormed`
initialization and preservation, the successful-profile progress theorem, the
ordered-effect receipts, the token/mailbox correspondence, the finite witness
through the original start gate, the scheduler mutants, and the WS-CONFIG
counterexample ids. None is claimed here.

## 4. The view conversions (P4–P7 records change from canonical to view)

### 4.1 The four record-row edits, frozen as acceptance conditions

The builder makes exactly these four edits and no other. Each is a
duplicate-prevention relationship cell; no theorem statement changes.

**`docs/READABLE-DAG.md`**, the `Readable.PromiseState` row of "Declaration and
existing-type records". Before:

> `first-order view of promise outcomes, not ECMAScript promise objects`

After:

> `view of Whatwg.Ecma262.Promise.State α (Boundary.Exception ε), the canonical owner since Q3 (E-01, move); not ECMAScript promise objects. Conversion receipts: Writable.unitPromise_eq, unitPromiseToShared_eq, unitPromiseFromShared_eq, unitPromise_roundtrip (E-07, E-08)`

**`docs/WRITABLE-DAG.md`**, the `UnitPromise`, `SinkAnswer`, `SinkReturn` row
of "Declaration dispositions". Before:

> `named views of the shared passive shapes first frozen under Readable; exact view/round-trip receipts required`

After:

> `views of Whatwg.Ecma262.Promise.State, .Outcome and .Returned, the canonical owners since Q3 (E-04..E-06, move), reached through the Readable abbrevs; the twelve exact view/round-trip receipts E-07..E-12 are the conversion theorems and stay rfl`

**`docs/WRITABLE-DAG.md`**, the `State`, promise/identity slot views row.
Before:

> `one post-start writer/controller projection; seeded cursors are views of a future shared supply`

After:

> `one post-start writer/controller projection; promises, nextPromise and handled are a view of the canonical Whatwg.Ecma262.Promise.Table Unit (Boundary.Exception ε) through Writable.promiseTable, with promiseTable_eq, lookupPromise_bridge, freshPromise_bridge, settle_bridge, markHandled_bridge and handled_bridge as its receipts (E-13..E-15, E-18..E-21, generalize)`

**`docs/TRANSFORM-DAG.md`**, the `lookupPromise`, `freshInternal`, `notify`,
`subscribe`, `settle` row. Before:

> `named adapter of canonical P5 lookupPromise, freshPromise, settle, plus exact P4/P5 answer admission; no third table/runtime`

After:

> `named adapter of the P5 view of the canonical Whatwg.Ecma262.Promise.Table, plus exact P4/P5 answer admission; no third table/runtime. Subscriptions are a view of Whatwg.Ecma262.Promise.Reactions through Transform.reactions (E-29..E-33, generalize); the notify, settle and runJob bridges are §5 of test/contracts/configuration-ordering.contract.md`

`Readable.State.readPromises` needs no separate row: it is inside the
`Readable.State` row, and `Readable.readTable` plus the §5 operations are its
receipts.

### 4.2 The battery assertion

`WhatwgTest/Streams/PromiseBridgeQ4.lean` ascribes the six conversion
functions, their twelve `_eq` and roundtrip receipts, and the two landed table
views, twenty ascriptions in all. They elaborate today, at their frozen P5
statements, and must still elaborate after the Q4 landing. A `view` record row
whose named conversion does not elaborate is a second owner, not a view, and
the landing is refused.

## 5. The four generalizations Q3 deferred

`WhatwgTest/Streams/PromiseBridgeQ4.lean`, 18 red ascriptions. R-P20 records
all four as Q4 work.

### 5.1 Row 14, `Transform.notify` (`E-32`, generalize)

Q3 §4.4 row 14 defers the bridge because "only the queueing half generalizes,
and the component dispatch stays in Streams". Q4 makes the queueing half
explicit as `Transform.notifyJob : Subscription α → PullAnswer ε → Job α ε`
and states `notify_jobQueue_bridge` over `Jobs.Queue.enqueue`. The dispatch
into `Readable.acceptPullAnswer` and `Writable.acceptAnswer` stays in Streams.
`Jobs.ReactionJob` is not the carrier: `Transform.Job` carries three component
tags of which only one is a reaction.

### 5.2 Row 15, `Transform.settle` (`E-33`, generalize)

Q3 §4.4 row 15 defers because relating the `foldlM` over the filtered
subscription list to `Table.settleAndTrigger` needs `notify`'s bridge. Three
statements close it: `settle_table_bridge` (the table half, over
`Table.settle`), `settle_jobQueue_order` (mask M2, the registration-order
enqueue, the instance of `triggerReactions_order`) and `settle_waiting_once`
(mask M1, the instance of `triggerReactions_once`).

The reaction half is deliberately **not** an equality of reaction lists.
`triggerReactions` advances a triggered registration's phase to `queued` and
keeps it; `Transform.settle` deletes it from `s.subscriptions`. Stating an
equality would be false, so the two landed laws are instantiated instead.

### 5.3 Row 16, `Transform.runJob` (`E-51`, generalize)

Q3 §4.4 row 16 defers because the `.writable` branch re-checks the mailbox
head against the token, which is the CFG-TOKENS correspondence and is
stream-specific. `runJob_writable_dequeue` and `runJob_writable_blocked` state
the generalizable half — the branch is gated by the landed
`Jobs.Queue.dequeue` over `Writable.jobQueue` — and defer the tick half to the
already-landed `Writable.tick_dequeue_bridge`.

### 5.4 `E-22`, the operation-level generalization

§4.3 of the Q3 contract defers this because it is a Streams **definition-body**
change, which the Q3 fence forbade.

**Where the five inline updates are.** `Readable.State.readPromises` is
updated by five definitions and eight syntactic sites: four `List.map`
updates in `Whatwg/Streams/Readable/DefaultController.lean` (`continuePull`'s
`.settleRead` branch, `streamClose`, `error`, `beginEnqueue`'s pending-read
branch) and four appends inside the single definition `read` in
`Whatwg/Streams/Readable/DefaultReader.lean`. The inventory's `E-22` row says
"every update is an inline `List.map` inside RC and RD"; the four `read`
updates are appends, not maps. Five definitions is the count Q3 and this
contract use.

**The three new operations**, in `Whatwg/Streams/Readable/State.lean`:

```lean
/-- `E-22` (generalize, Q4): allocate a read cell at the cursor. The Streams
instance of `Whatwg.Ecma262.Promise.Table.fresh` at value parameter
`ReadResult α`. -/
def freshReadCell {α ε : Type} (s : State α ε)
    (outcome : PromiseState (ReadResult α) ε) : State α ε × Nat :=
  ({ s with
      nextRead := s.nextRead + 1,
      readPromises := s.readPromises ++ [(s.nextRead, outcome)] },
    s.nextRead)

/-- `E-22` (generalize, Q4): overwrite one read cell. Deliberately unguarded,
exactly as the inline `List.map` updates are: the general `Table.settle` is
guarded by `isPending` and a non-pending settle is the identity (decision 7),
so the two agree only under the pending hypothesis, which is where
`Table.settle_pending` puts them. Adopting the guard here would change the
meaning of four landed Streams bodies. -/
def settleReadCell {α ε : Type} (s : State α ε) (id : Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) : State α ε :=
  { s with
    readPromises := s.readPromises.map (fun p =>
      if p.1 = id then
        (p.1, match result with | .ok v => .fulfilled v | .error e => .rejected e)
      else p) }

/-- `E-22` (generalize, Q4): overwrite every read cell whose identity is in
`ids`. The two set-shaped updates of `streamClose` and `error` are its
instances. -/
def settleReadCells {α ε : Type} (s : State α ε) (ids : List Nat)
    (result : Except (Boundary.Exception ε) (ReadResult α)) : State α ε :=
  { s with
    readPromises := s.readPromises.map (fun p =>
      if p.1 ∈ ids then
        (p.1, match result with | .ok v => .fulfilled v | .error e => .rejected e)
      else p) }
```

**The five new bodies**, in one block, replacing the inline updates:

```lean
-- Whatwg/Streams/Readable/DefaultController.lean
def continuePull (s : State α ε) : PullContinuation α → State α ε
  | .done => s
  | .settleRead id chunk =>
      { settleReadCell s id (.ok (.chunk chunk)) with
        trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
  | .returnEnqueue call =>
      { s with trace := s.trace ++ [.enqueueReturned call (.ok ())] }

def streamClose (s : State α ε) : State α ε :=
  match s.status with
  | .readable =>
      { settleReadCells s s.readRequests (.ok .done) with
        status := .closed, readRequests := [], closedPromise := .fulfilled (),
        trace := s.trace ++ [.settled (.closed (.ok ()))] ++
          s.readRequests.map (fun id => .settled (.read id (.ok .done))) }
  | _ => s

def error (s : State α ε) (e : Boundary.Exception ε) : State α ε :=
  match s.status with
  | .readable =>
      { settleReadCells s s.readRequests (.error e) with
        status := .errored e, queue := Data.resetQueue sizes s.queue,
        algorithms := none, readRequests := [], closedPromise := .rejected e,
        trace := s.trace ++ [.settled (.closed (.error e))] ++
          s.readRequests.map (fun id => .settled (.read id (.error e))) }
  | _ => s

def beginEnqueue (s : State α ε) (chunk : α) : State α ε :=
  if canCloseOrEnqueue s then
    match s.readRequests with
    | id :: rest =>
        callPullIfNeededWith
          { settleReadCell s id (.ok (.chunk chunk)) with
            readRequests := rest, nextEnqueue := s.nextEnqueue + 1,
            trace := s.trace ++ [.settled (.read id (.ok (.chunk chunk)))] }
          (.returnEnqueue s.nextEnqueue)
    | [] =>
        match s.algorithms with
        | none => s
        | some a =>
            match a.size with
            | .one =>
                finishEnqueue { s with nextEnqueue := s.nextEnqueue + 1 }
                  s.nextEnqueue chunk (.value sizes.one)
            | .foreign name =>
                { s with
                  nextEnqueue := s.nextEnqueue + 1,
                  frames := .size s.nextEnqueue chunk :: s.frames,
                  trace := s.trace ++ [.sizeCalled s.nextEnqueue name chunk] }
  else s

-- Whatwg/Streams/Readable/DefaultReader.lean
def read {α ε : Type} (s : State α ε) : State α ε :=
  match s.status with
  | .closed =>
      let (t, id) := freshReadCell s (.fulfilled .done)
      { t with trace := t.trace ++ [.settled (.read id (.ok .done))] }
  | .errored e =>
      let (t, id) := freshReadCell s (.rejected e)
      { t with trace := t.trace ++ [.settled (.read id (.error e))] }
  | .readable =>
      match Data.dequeueValue sizes s.queue with
      | none =>
          let (t, id) := freshReadCell s .pending
          callPullIfNeeded { t with readRequests := t.readRequests ++ [id] }
      | some (chunk, q) =>
          let (t, id) := freshReadCell { s with queue := q } .pending
          if s.closeRequested = true ∧ q.entries = [] then
            continuePull (streamClose { t with algorithms := none }) (.settleRead id chunk)
          else callPullIfNeededWith t (.settleRead id chunk)
```

Each is definitionally the pre-Q4 body: `freshReadCell` leaves `trace` and
`readRequests` untouched, so `t.trace = s.trace`, `t.readRequests =
s.readRequests` and `id = s.nextRead`; `settleReadCell` and `settleReadCells`
inline to the same `List.map`.

**The equation lemmas that keep every dependent proof.** Five, one per
rewritten definition, each restating the pre-Q4 body verbatim and each closing
by `rfl`: `continuePull_settleRead_body`, `streamClose_body`, `error_body`,
`beginEnqueue_settle_body`, `read_body`. A builder that cannot prove one of
them by `rfl` has changed the meaning of a Streams definition and is refused.
These are what keep `simp [continuePull]`, `simp [streamClose]` and the
`attribute [local simp]` normal forms of the four `simp`-set modules working:
decision 5 and inventory condition 3 forbid a `move` for a function in a
`simp` set, and a rewritten body is a stronger version of the same hazard.

**The three bridges onto the landed table**: `readTable_freshReadCell`
(unconditional), `readTable_settleReadCell` (under
`Table.get (readTable s) id = some .pending`) and `readTable_settleReadCells`
(under `ids.Nodup` and pointwise pendingness).

**The dependents verified by grep**, at file granularity, from
`git grep`-equivalent scans over `Whatwg/Streams/**` and `WhatwgTest/**` for
`readPromises`, `continuePull`, `streamClose`, `beginEnqueue`,
`Readable.read`, `Readable.error`, `read s` and `error s`:

| File | Names it mentions |
| --- | --- |
| `Whatwg/Streams/Readable/State.lean` | `readPromises` (4) |
| `Whatwg/Streams/Readable/DefaultController.lean` | `readPromises` (4), `continuePull` (5), `streamClose` (2), `beginEnqueue` (1), `error` (2) |
| `Whatwg/Streams/Readable/DefaultReader.lean` | `readPromises` (4), `continuePull` (1), `streamClose` (1), `read` (2) |
| `Whatwg/Streams/Readable/Laws.lean` | `readPromises` (14), `continuePull` (13), `streamClose` (8), `beginEnqueue` (10), `read` (7), `error` (4) |
| `Whatwg/Streams/Readable/Reentrancy.lean` | `continuePull` (1), `streamClose` (1), `beginEnqueue` (18), `read` (1) |
| `Whatwg/Streams/Readable/Step.lean` | `beginEnqueue` (2), `read` (2), `error` (2) |
| `Whatwg/Streams/Transform/DefaultController.lean` | `beginEnqueue` (1), `Readable.read` (1), `Readable.error` (2) |
| `Whatwg/Streams/Transform/Laws.lean` | `beginEnqueue` (2), `Readable.read` (1), `Readable.error` (2), `read s` (2), `error s` (2) |
| `Whatwg/Streams/Transform/Runs.lean` | `continuePull` (1), `streamClose` (1), `beginEnqueue` (1), `Readable.read` (1), `Readable.error` (1) |
| `Whatwg/Streams/Transform/Step.lean` | `read s` (1), `error s` (1) |
| `Whatwg/Streams/Piping/Runs.lean` | `continuePull` (1), `beginEnqueue` (5), `Readable.read` (5), `Readable.error` (1) |
| `Whatwg/Streams/Piping/Laws.lean` | `Readable.error` (5) |
| `Whatwg/Streams/Piping/Requirements.lean` | `Readable.error` (1) |
| `Whatwg/Streams/Piping/Step.lean` | `Readable.error` (1) |
| `WhatwgTest/Streams/Readable/DefaultContract.lean` | `readPromises` (11), `continuePull` (10), `streamClose` (4), `beginEnqueue` (24), `Readable.read` (17), `Readable.error` (11) |
| `WhatwgTest/Streams/Transform/BackpressureLaws.lean` | `beginEnqueue` (2), `Readable.read` (1), `Readable.error` (2) |
| `WhatwgTest/Streams/Counterexamples/Piping/Shutdown.lean` | `readPromises` (2), `beginEnqueue` (1), `Readable.read` (4), `Readable.error` (2) |
| `WhatwgTest/Streams/PromiseBridge.lean` | `readPromises` (3) |
| `WhatwgTest/Ecma262/PromiseContract.lean` | `readPromises` (2) |

Nineteen files. `Whatwg/Streams/Readable/Reentrancy.lean` is the highest risk:
its `attribute [local simp]` set names `returnPull`, `continuePull`,
`settlementTrace`, `chunksOfSettlements`, `observeM1` and
`Boundary.Exception.ofRangeError`, and `continuePull` is one of the five
rewritten bodies. `continuePull_settleRead_body` is the lemma that has to
carry it.

## 6. The CFG-WPT source and certificate seam

`WhatwgTest/Streams/Semantics/OrderingSource.lean`, 28 ascriptions.

### 6.1 The seam, and one amendment

The draft's coordinator-approved seam: breaker-owned `OrderingSource.lean`
owns the independent source/certificate judgments; a builder-owned
`WhatwgTest/Streams/Semantics/OrderingBridgeProofs.lean` may import that source
plus production to prove the bridge; the frozen source battery imports and
ascribes those bridge proofs; neither source nor bridge imports the battery,
and production imports no `WhatwgTest` module.

**Amendment.** A frozen ascription battery cannot both declare its subject and
be the red statement of it. The judgments are therefore ascribed in
`OrderingSource.lean` under the namespace
`Whatwg.Streams.Semantics.Ordering.Source` and authored by the builder under
`Whatwg/Streams/Semantics/`. The reason the seam was drawn is preserved: the
judgment carries no mutable promise table, no scheduler and no `Config` field;
it shares no cell with the runtime; the dependency direction of
`docs/ARCHITECTURE.md` is unchanged; and `OrderingBridgeProofs.lean` stays
builder-owned and outside this battery's edit fence.

**Open decision for the coordinator.** The alternative is to declare the
judgments inside `OrderingSource.lean` itself, which keeps the draft's
test-side placement but makes the module partly green from the first commit
and gives the breaker authorship of a semantic carrier. This seat recommends
the amendment above and records the alternative rather than deciding it.

### 6.2 What the surface says

`SourceChecked` is checked against source occurrences and use edges alone; the
expected event array is not an argument to it. `CausalPrefix` is a judgment
over immutable reference-trace positions and never calls `Config.tick` or
accepts `Config.Reaches` as an oracle. `ErasesPrefix` relates the two traces.
`SourceProfileCompatible` is checked against the consumed external decision
word and an explicit symbol-to-address binding.

`erasure_preserves_selected_order` is the general law: erasing `D0`, `D1` and
`D2`'s settlement, the unselected flush and assertion attachments, and the
pending flush token cannot delete or reorder a selected log before the prefix
boundary. It is proved from the no-handler and boundary conditions, never
assumed. `run_erases_to_reference` is the configuration bridge; proving a list
equal to itself satisfies neither.

Still required and not claimed: the executable certificate checker, the three
certificate mutants (a selected handler on `D0`, aliased derived results, a
flush that depends on `W0` instead of `D2`), the finite witness through the
original start gate, and the later host replay.

## 7. The Streams promise-slot re-disposition (R-P5, Q4)

R-P5 rules that the promise instance slots are `owned` in the ES2026 census
while the Streams census keeps them `foreignBoundary`, and that "these three
Streams rows become references into that library when P8 opens, at slice Q4".
This is that change.

### 7.1 The exact `census/overrides.tsv` entries

The current block, lines beginning `# ECMAScript promise and completion-record
internals.`, is replaced by:

```text
# ECMAScript promise internals. Since slice Q3 of docs/PROMISE-PACKAGE-PLAN.md
# these two slots are modelled in Lean, by Whatwg.Ecma262.Promise.State fused
# with its Cell and Table, and the Streams algorithms reach them through the
# views Writable.promiseTable and Readable.readTable. Ruling R-P5 says the
# Streams rows become references into that library when P8 opens; slice Q4 is
# that point. They stay in the denominator and stay absent until a witness is
# named in WhatwgTest/Audit/SpecCoverage.lean.
slot.promise-state	owned	modelled by Whatwg.Ecma262.Promise.State (slot.PromiseState 2744957..2745252 fused with slot.PromiseResult 2745263..2745619); reached from Streams through Writable.promiseTable and Readable.readTable (R-P5, slice Q4)
slot.promise-is-handled	owned	modelled by the handled field of Whatwg.Ecma262.Promise.Cell (slot.PromiseIsHandled 2746322..2746637); reached from Streams through Writable.promiseTable and Writable.handled_bridge (R-P5, slice Q4)

# The completion-record field stays foreignBoundary. It is not a promise slot:
# SPEC-MANIFEST.md records it as a field read off a host abrupt completion, the
# ES2026 census has no counterpart row for it (its result slot is
# [[PromiseResult]]), and gap G-10 of the extraction inventory records that no
# Completion carrier exists in Whatwg.Ecma262 at this pin. Re-dispositioning it
# would name an owner that does not exist.
slot.value	foreignBoundary	ECMAScript completion-record field read off a host abrupt completion; no Whatwg.Ecma262 counterpart at this pin (gap G-10)
```

Three rows are touched; two change disposition. The row ids, offsets and
digests are unchanged: `slot.promise-state` at 262706..262722, digest
`d4894ea72694d373cca3144868e669fa166801ad67717bccf234b4d042d67a85`;
`slot.promise-is-handled` at 47309..47329, digest
`af92d623bd559e6fa164d031baa144d48d5e0507804d6fb9b93a0bb0006b5eaa`;
`slot.value` at 93921..93930, digest
`e161dd003684ff6fdff0d4c8fae6e67eb3bc04f16a517798ff76a5c04c044bbd`.

### 7.2 Why `owned`, out of the seven dispositions

The vocabulary is `owned`, `requirement`, `foreignBoundary`, `hostOnly`,
`refused`, `evidenceOnly`, `targetOnly`. Only `owned` is supportable.

- `owned` means "modelled in Lean; must carry at least one witness before its
  coverage row can leave `absent`". Since Q3 the two slots **are** modelled in
  Lean — `Whatwg.Ecma262.Promise.State`, `.Cell`, `.Table` — and the Streams
  algorithms reach them through two landed views. The row stays in the
  denominator and stays `absent`, which is the honest record.
- `foreignBoundary` is now false. It means "a host-supplied body or host
  object whose behaviour enters only as typed decisions with a profile". The
  behaviour no longer enters only as a typed decision: under DB-03 the job
  queue that settles these cells is deterministic state in the configuration,
  and DB-11 gives that state a named home this repository owns.
- `evidenceOnly`, `refused` and `targetOnly` would remove the rows from the
  denominator. That is exactly the relabelling `docs/SPEC-COVERAGE.md`
  forbids: coverage rises by building models, not by moving rows out.
- `hostOnly` is for Web IDL conversions, brand checks and overload
  resolution. A promise state slot is none of those.
- `requirement` is for text stated as constraints rather than an algorithm,
  realized by a named algorithm. A slot row is not a requirement.

The two censuses still answer two ownership questions about two libraries.
What changes is the Streams answer: Streams does not own the slot, and it no
longer treats it as outside the model either — it names the library that does.

### 7.3 The `census/README.md` paragraph

The "Foreign internal slots" bullet is replaced by:

> - **Foreign internal slots.** Twelve `slot` rows name ECMAScript internals
>   rather than streams state: the `ArrayBuffer` and `ArrayBufferView` slots
>   the byte-stream algorithms read, and the promise and completion-record
>   fields the algorithms branch on. The manifest names ArrayBuffer detachment
>   `foreignBoundary`, and the root `AGENTS.md` representation rules put host
>   runtime objects outside stored content, so the nine `ArrayBuffer` and
>   `ArrayBufferView` rows are `foreignBoundary`. The three promise and
>   completion-record rows were the weakest of the twelve and were flagged for
>   ratification. Ruling R-P5 (2026-09-06) ratified them as they stood and
>   recorded the cross-reference: the same named slots are `owned` in the
>   ECMA-262 census, and the Streams rows become references into
>   `Whatwg.Ecma262` when P8 opens, at slice Q4 of
>   `docs/PROMISE-PACKAGE-PLAN.md`. Slice Q4 is that point.
>   `slot.promise-state` and `slot.promise-is-handled` are now `owned`: since
>   slice Q3 they are modelled by `Whatwg.Ecma262.Promise.State` and the
>   `handled` field of its `Cell`, and the Streams algorithms reach them
>   through `Writable.promiseTable` and `Readable.readTable`. They stay inside
>   the denominator and stay `absent` until a witness is named. The third row,
>   `slot.value`, stays `foreignBoundary`: it is a completion-record field read
>   off a host abrupt completion, it has no counterpart row in the ECMA-262
>   census, and gap `G-10` of `docs/PROMISE-EXTRACTION-INVENTORY.md` records
>   that no Completion carrier exists in `Whatwg.Ecma262` at this pin.

### 7.4 The expected Streams totals, recomputed by hand

The change is exactly two rows, both moving `foreignBoundary` → `owned`.
`docs/SPEC-COVERAGE.md` excludes a row from the denominator only for
`evidenceOnly`, `refused` and `targetOnly`. Neither the old nor the new
disposition is one of those, so:

| Quantity | Before | After | Why |
| --- | ---: | ---: | --- |
| census rows | 450 | 450 | no row is added, removed or re-anchored |
| excluded | 40 | 40 | neither disposition is an excluding one |
| denominator | 410 | 410 | 450 − 40 |
| green | 12 | 12 | no witness is added by this packet |
| partial | 6 | 6 | unchanged |
| absent in denominator | 392 | 392 | the two rows were `absent` and stay `absent` |
| owned-with-green | 12 | 12 | the two rows are `owned` and `absent`, so they add nothing to the green-and-owned count |

The four frozen numbers of `WhatwgTest/Audit/SpecCoverage.lean` —
`expectedRowTotal 450`, `expectedDenominator 410`, `expectedGreen 12`,
`expectedPartialCount 6`, `expectedAbsentInDenominator 392` — are therefore
**unchanged**, and §7.6 records that no battery amendment is owed.

### 7.5 The re-emitted Streams coverage block

The block `lake exe census --report` prints after the change is byte-identical
to the block it prints today:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

It is an acceptance condition that the builder pastes the block the gate
actually prints, not this one, and that the two agree.

### 7.6 The battery amendment, and why it is empty

The instruction is to amend the Streams numerator's expectations "only where a
frozen number moves, with dated reasons". No frozen number moves, so **no
amendment to `WhatwgTest/Audit/SpecCoverage.lean` is frozen here and this
packet does not edit it.**

What does change is generated, not frozen: `WhatwgTest/Audit/SpecCoverageRows.lean`
carries `⟨"slot.promise-is-handled", .foreignBoundary, .absent, []⟩` and
`⟨"slot.promise-state", .foreignBoundary, .absent, []⟩` today, and after the
change both read `.owned`. That module is written by `lake exe census --write`
and covered by the drift gate, so regenerating it is a builder action and the
gate decides it. `⟨"slot.value", .foreignBoundary, .absent, []⟩` is unchanged.

Dated reason, 2026-09-07: the disposition of a row and the coverage state of a
row are two facts with two owners. R-P5's re-disposition moves the first and
must not move the second, because no theorem was proved by moving it. If a
later packet names a witness for either row, that is when `green`,
`owned-with-green` and `absent` move, and that packet owes the amendment.

## 8. Acceptance conditions

1. All 158 restated ascriptions elaborate, joined to their class by §2.2, and
   every one of the 124 class [A] ascriptions carries the draft's statement
   unchanged up to the §2.4 substitutions. No P4–P7 theorem statement changes.
2. The 15 class [R] ascriptions still elaborate against the landed
   `Whatwg.Ecma262` names. A repair that turns a module green by weakening one
   of them is a refusal, not a landing.
3. The 15 Q4-owned bridging receipts are proved, each under the mask its
   docstring names, and `episodePrefix_jobQueue_eq` states R-P12's
   `active_episode_fifo_suffix` over `Whatwg.Ecma262.Jobs.Queue`.
4. Conversion receipts exist for all three Streams promise tables, the four
   record rows of §4.1 read as frozen there, and the twenty ascriptions of §4.2
   still elaborate.
5. The four generalizations of §5 are proved, the five `E-22` equation lemmas
   close by `rfl`, and every one of the nineteen dependent files of §5.4
   rebuilds green with no edit to a frozen statement.
6. The `census/overrides.tsv` entries and the `census/README.md` paragraph read
   as §7.1 and §7.3 freeze them; the Streams coverage block is re-emitted and
   quoted verbatim and agrees with §7.5; the four expected totals are
   unchanged.
7. The 82 receipts of `OrderingAxiomReport.lean` print inside the R-11 ceiling
   (`propext`, `Quot.sound`, `Classical.choice`). `sorryAx`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the
   `native_decide` auxiliaries appear nowhere.
8. `docs/CONFIGURATION-DAG.md` records the ten edges with no edge closed by a
   compiling battery alone, and `COORDINATION.md` records the release of the
   configuration-breaker hold. Both are the coordinator's at landing.
9. The five entries leave `test/fixtures/trust-gate/known-red.txt` only when
   their batteries are green, and the trust gate's all-green control is
   restored.

## 9. Fence

**This packet may be edited by no one but this breaker seat.** The builder's
implementation fence is:

- `Whatwg/Streams/Semantics/*.lean` — the `Ordering` configuration calculus
  and its `Source` judgment;
- `Whatwg/Streams/Readable/{State,DefaultController,DefaultReader}.lean` — the
  three `E-22` operations and the five rewritten bodies of §5.4, and nothing
  else;
- `Whatwg/Streams/{Readable,Transform}/Laws.lean` — additively, the Q4
  bridging lemmas;
- `census/overrides.tsv` and `census/README.md` — exactly §7.1 and §7.3;
- the four declaration-record rows of §4.1;
- `WhatwgTest/Streams/Semantics/OrderingBridgeProofs.lean` — new,
  builder-owned, outside this battery's edit fence;
- the regenerated `WhatwgTest/Audit/SpecCoverageRows.lean` and
  `generated/spec-algorithm-census.tsv` disposition columns, by
  `lake exe census --write`.

This breaker seat edited nothing under `Whatwg/`, `Gates/`, `census/`,
`generated/`, `vendor/`, no Streams contract or battery other than the new
`WhatwgTest/Streams/PromiseBridgeQ4.lean`, and neither
`test/counterexamples/REGISTER.md`, `SPEC-MANIFEST.md`, `PLAN.md` nor
`COORDINATION.md`. It ran no `lake`, `lean` or `lsp` in the held draft's
worktree and modified nothing there.

## 10. Freeze receipt

Frozen 2026-09-07 on branch `promise/q4-breaker`, based on `main` at
`f700230`. Toolchain `leanprover/lean4:v4.33.1`.

**Green.**

```text
lake --wfail build Whatwg Gates
Build completed successfully (164 jobs).   exit 0
```

**Red, in the declared modules only.**

```text
lake build WhatwgTest
✖ [224/230] Building WhatwgTest.Streams.Semantics.OrderingContract (705ms)
✖ [225/230] Building WhatwgTest.Streams.PromiseBridgeQ4 (900ms)
✖ [226/230] Building WhatwgTest.Streams.Semantics.OrderingLaws (925ms)
✖ [227/230] Building WhatwgTest.Streams.Semantics.OrderingSource (901ms)
✖ [228/230] Building WhatwgTest.Streams.Semantics.OrderingAxiomReport (900ms)
Some required targets logged failures:
- WhatwgTest.Streams.Semantics.OrderingContract
- WhatwgTest.Streams.PromiseBridgeQ4
- WhatwgTest.Streams.Semantics.OrderingLaws
- WhatwgTest.Streams.Semantics.OrderingSource
- WhatwgTest.Streams.Semantics.OrderingAxiomReport
error: build failed
```

Exactly the five declared modules fail, and no other module of the 230-job
test build does.

**Exact diagnostics**, from `lake env lean -DmaxErrors=5000 <file>`:

| Module | Diagnostics | Kinds |
| --- | ---: | --- |
| `WhatwgTest/Streams/Semantics/OrderingContract.lean` | 235 | 235 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Semantics/OrderingLaws.lean` | 327 | 295 `lean.unknownIdentifier`, 21 `lean.invalidDottedIdent`, 9 "`sorryAx` is not a structure", 1 "invalid `{...}` notation, expected type is not known", 1 "Invalid `⟨...⟩` notation: The expected type could not be determined" |
| `WhatwgTest/Streams/Semantics/OrderingSource.lean` | 74 | 74 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/Semantics/OrderingAxiomReport.lean` | 82 | 82 `lean.unknownIdentifier` |
| `WhatwgTest/Streams/PromiseBridgeQ4.lean` | 24 | 24 `lean.unknownIdentifier` |
| **total** | **742** | |

Every diagnostic is an unknown identifier or a direct consequence of one: an
`invalidDottedIdent` is a `.constructor` whose expected type is an unknown
`Config`, `Active` or `Startup`; "`sorryAx` is not a structure" is a
`{ c with … }` whose `c` has the error type a missing `Config` leaves behind;
the two notation diagnostics are the same for `{…}` and `⟨…⟩`. There is no
parse, import, type-mismatch or instance-synthesis failure anywhere.

**The green prefix inside a red module.** In
`WhatwgTest/Streams/Semantics/OrderingContract.lean` the first diagnostic is
at line 66, and there is none between lines 69 and 134: all fifteen class [R]
ascriptions elaborate. In `WhatwgTest/Streams/PromiseBridgeQ4.lean` the 24
diagnostics are confined to the eighteen §5 ascriptions; the twenty §4.2
ascriptions elaborate.

**Ascription counts per battery.**

| Battery | `#check` | Composition |
| --- | ---: | --- |
| `OrderingContract.lean` | 107 | 104 restated (15 [R], 11 [B], 78 [A]) + 3 Q4-owned views |
| `OrderingLaws.lean` | 66 | 54 restated (0 [R], 8 [B], 46 [A]) + 12 Q4-owned receipts |
| `OrderingSource.lean` | 28 | all new; the CFG-WPT seam |
| `PromiseBridgeQ4.lean` | 38 | 18 for the four deferred generalizations (red) + 20 view conversions (green) |
| `OrderingAxiomReport.lean` | 82 `#print axioms` | 54 + 12 + 14 + 2 |

The 158 restatement splits 15 [R] / 19 [B] / 124 [A] across the two Ordering
batteries. `OrderingContract` holds all 15 [R]; 11 [B] (`Active` and its four
constructors, plus `lookup`, `lookupRegistration`, `enqueueJob`,
`setRegistrationPhase`, `register`, `notifySettled`); and 78 [A], which is the
reuse table's 73 plus the five reclassified by §2.3 (`Job`, `Job.mk`,
`Job.serial`, `Job.kind`, `queuedJobs`). `OrderingLaws` holds 8 [B]
(`lookup_eq`, `lookupRegistration_eq`, `setRegistrationPhase_eq`,
`enqueueJob_eq`, `register_eq`, `notifySettled_eq`, `step_active_jobs_eq`,
`episodePrefix_jobs_eq`) and 46 [A], which is the table's 45 plus
`queuedJobs_eq`. 15 + (11 + 8) + (78 + 46) = 158.

No `lake exe` gate was run by this seat beyond the two builds above; the
vendor seal, citations and census gates are unchanged by a document-and-battery
freeze and are the coordinator's at landing.

## 11. Builder notes (Q4 builder seat, branch `promise/q4-builder`, 2026-09-07)

Appended by the builder as the discipline requires: for each frozen ascription
that could not be satisfied against the surface slice Q3b landed, the exact
mismatch and its diagnostic, and no silent adaptation. **The coordinator rules
on every item below.** Nothing in §1–§10 is edited.

Base: `promise/q4-breaker` at `9ae662a`, merged with the Q3b landing
`promise/q3b-builder` at `9624c4b` and with `origin/main`. Toolchain
`leanprover/lean4:v4.33.1`.

### 11.1 The four blocking items

**B1 — `Reaction.mk` is ascribed at five arguments and has six.** Q3b-sensitive
list row 1 (`Reaction`, `.mk`, …). Frozen at
`WhatwgTest/Streams/Semantics/OrderingContract.lean:108`. Finding F4 of the Q3b
fidelity addendum inserted `capability : Option Capability` (CAPFIELD,
2691475..2692138 for `Type`, 2691475..2691802 for `Capability`) between
`handler` and `phase`. Diagnostic:

```text
WhatwgTest/Streams/Semantics/OrderingContract.lean:108:7: error: Type mismatch
  @Whatwg.Ecma262.Promise.Reaction.mk
has type
  {body : Type} → Nat → Nat → ReactionType → Option body → Option Capability →
    ReactionPhase → Reaction body
but is expected to have type
  {body : Type} → Nat → Nat → ReactionType → Option body → ReactionPhase → Reaction body
```

This is the **only** remaining diagnostic in `OrderingContract.lean`; the other
234 are gone. §2.4's third bullet is what has to be re-frozen: the fifth
argument is `Option Capability`, and at this configuration it is `none`,
because a P8a registration derives no promise — `G-11`'s remainder, exactly as
`Transform.subscribe` supplies `none`. **Stopped on this item.**

**B2 — `register_eq` builds a five-field `Reaction` literal.** Frozen at
`WhatwgTest/Streams/Semantics/OrderingLaws.lean:235`, the consequence of B1 in
the law battery. Diagnostics:

```text
OrderingLaws.lean:235:51: error: Insufficient number of fields for `⟨...⟩` constructor:
  Constructor `Whatwg.Ecma262.Promise.Reaction.mk` has 6 explicit field, but only 5 were provided
OrderingLaws.lean:235:89: error: Unknown constant `Option.waiting`
```

The landed `Whatwg.Streams.Semantics.Ordering.register_eq` is the frozen
statement with `none` inserted at the capability field and nothing else
changed, and it closes by `rfl`. Its docstring carries this note. **The
adaptation is recorded, not silent; the coordinator rules whether the frozen
ascription is re-frozen to match.**

**B3 — `notifySettled_reactions_bridge` is false as frozen.** Frozen at
`WhatwgTest/Streams/Semantics/OrderingLaws.lean:545`. §2.7 of this contract
already records the two readings of `ReactionPhase.queued`'s payload and rules
that "the Q4 builder keeps the draft's two cursors and must not silently
inherit the landed operations' instantiation". Under that ruling the bridge
cannot hold: `notifySettled_eq` writes `.queued queued.2.serial`, the **job**
serial drawn from `Config.nextJob`, while `Whatwg.Ecma262.Promise.triggerReactions`
writes `.queued r.id`, the **registration** id. Decision 2 makes those two
supplies unrelated, so the two lists differ at the phase field.

Counterexample, from the decisions this packet re-affirms: take `c` with
`c.nextJob = 7`, one registration `r` with `r.id = 0`, `r.promise = id`,
`r.phase = .waiting`, and `Writable.lookupPromise c.writable id = some (.fulfilled ())`.
Then `(notifySettled c id).registrations = [{ r with phase := .queued 7 }]`
while `(triggerReactions (reactions c) id .fulfill (.ok ()) Queue.empty).1.fulfill
= [{ r with phase := .queued 0 }]`.

No replacement is authored: unlike B2 and B4 the repair changes the **content**
of the claim, not a field count or a projection, and that is the breaker's and
the coordinator's to decide. The obvious candidates are (a) state the bridge
over the phase-erased registration lists, or (b) state it under a hypothesis
that the two cursors agree at the triggered entries. `Whatwg.Streams.Semantics.Ordering.notifySettled_reactions_bridge`
therefore **does not exist**, which is one of the three remaining diagnostics of
`OrderingAxiomReport.lean`. **Stopped on this item.**

**B4 — `register_reactions_bridge` does not typecheck.** Frozen at
`WhatwgTest/Streams/Semantics/OrderingLaws.lean:540`. The left-hand side is
`(register c p callback).map reactions : Option (Reactions Nat)`; the
right-hand side closes with `.map Prod.fst` over
`Whatwg.WebIdl.Promise.react`'s result, and `react` returns
`Option (Table value reason × Reactions body × Jobs.Queue … × Option (Reaction body))`,
so `Prod.fst` projects the **table**. Diagnostic:

```text
WhatwgTest/Streams/Semantics/OrderingLaws.lean:540:8: error: Type mismatch
```

This is independent of Q3b: the same projection was wrong against the slice Q3
surface. The landed
`Whatwg.Streams.Semantics.Ordering.register_reactions_bridge` is the frozen
statement with `.map (fun x => x.2.1)` in place of `.map Prod.fst` — the
reactions component, which is what the ascription's own name and docstring say
it is — and it is proved. **The adaptation is recorded, not silent.**

### 11.2 One dependent proof of `E-22` did not survive the frozen body

Acceptance condition 5 and §5.4 say that the five equation lemmas keep every
one of the nineteen dependent files "unchanged". Eighteen of the nineteen are
byte-identical. The nineteenth is not:

`Whatwg/Streams/Readable/Laws.lean`, `read_nextRead`. Its **statement** is
unchanged and its `attribute [local simp]` neighbours are untouched, but its
tactic proof needed one edit, from `unfold read` to `rw [read_body]`. The cause
is the frozen body of `read` in §5.4, which introduces `let (t, id) := freshReadCell …`;
that pattern-`let` elaborates to a `match` on the pair, so the proof's
`split` reached the pair matcher before the `if`, and

```text
Whatwg/Streams/Readable/Laws.lean:842: Tactic `rewrite` failed:
  Did not find an occurrence of the pattern (continuePull …)
```

`read_body` is the contract's own lemma for exactly this hazard, so the repair
uses it and the proof is otherwise character-for-character the pre-Q4 one. All
five equation lemmas do close definitionally, as required. Recorded for the
coordinator; no statement changed.

### 11.3 One additive import

`Whatwg/Streams/Transform/Laws.lean` gains `import Whatwg.Streams.Writable.Laws`,
because §5.2's `settle_table_bridge` is stated over the landed
`Whatwg.Streams.Writable.settle_bridge`. The imported module declares no
instance and no global `simp` lemma, and `Whatwg/Streams/Piping/Laws.lean`
already imports it, so no dependency edge is new to `Whatwg/Streams/**`.

### 11.4 What did not land

§6, the CFG-WPT source and certificate seam, is **not attempted**. Neither
`Whatwg/Streams/Semantics/` `Source` judgments nor
`WhatwgTest/Streams/Semantics/OrderingBridgeProofs.lean` were authored.
`erasure_preserves_selected_order` and `run_erases_to_reference` are
research-scale statements — §6.2 forbids the vacuous reading explicitly, and an
honest `run_erases_to_reference` has to construct an independent causal
reference trace for every admitted run — and this seat judged that guessing at
them was worse than recording them open. `OrderingSource.lean` keeps 66 of its
74 diagnostics for that reason; the eight that cleared are the ones that name
`Config`, `Reaches`, `externalWord`, `Event` and `Decision`.

### 11.5 Measured state at the landing

| Battery | Diagnostics at the freeze | Diagnostics at this landing |
| --- | ---: | ---: |
| `WhatwgTest/Streams/Semantics/OrderingContract.lean` | 235 | **1** (B1) |
| `WhatwgTest/Streams/Semantics/OrderingLaws.lean` | 327 | **4** (B2 ×2, B3, B4) |
| `WhatwgTest/Streams/Semantics/OrderingSource.lean` | 74 | **66** (§11.4) |
| `WhatwgTest/Streams/Semantics/OrderingAxiomReport.lean` | 82 | **3** (B3 and the two §6 laws) |
| `WhatwgTest/Streams/PromiseBridgeQ4.lean` | 24 | **0 — green** |
| **total** | **742** | **74** |

79 of the 82 receipts of `OrderingAxiomReport.lean` print, and every one is
inside the R-11 ceiling: **14 empty, 27 `[propext]`, 33 `[propext, Quot.sound]`,
5 `[propext, Classical.choice, Quot.sound]`**. `sorryAx`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`, `Lean.trustCompiler` and the `native_decide` auxiliaries
appear nowhere.
