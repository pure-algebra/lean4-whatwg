# First promise packet (slice Q3, `PROMISE-PG-FIRST`)

Status: FROZEN / RED, Q3 packet breaker seat, 2026-09-07, on branch
`promise/q3-breaker`, based on `e819a9f` (`Q1 landing repair and ratification
R-P17`). Graph: `docs/PROMISE-DAG.md`, opened by this packet.

`docs/PROMISE-PACKAGE-PLAN.md` names this packet `promise-core.contract.md`;
the coordinator's seat instruction names it `promise-first-packet.contract.md`
and that name is used. The plan's file fence otherwise applies unchanged.

The Lean batteries are the authority on names and propositions; the Lean in
this file is a reading aid. The builder may repair elaboration but may not
weaken, delete or replace a frozen ascription, law, mask, decision or
acceptance condition.

Read first, in this order: `COORDINATION.md` rulings R-P12 through R-P17;
`docs/PROMISE-EXTRACTION-INVENTORY.md` in full; `docs/DESIGN-BASIS.md` DB-03,
DB-04, DB-11; `docs/PROMISE-PACKAGE-PLAN.md` sections "The extraction
inventory", "Q3" and "Q4".

## 1. Claim boundary

This packet freezes the first semantic surface of `Whatwg.Ecma262` and
`Whatwg.WebIdl`. It grants no coverage state, no host observation, no
equivalence with any engine, and no claim about `Whatwg.Streams` beyond the
preservation obligations of section 8. Every census row it cites is cited as an
**anchor for a declaration**, never as a numerator: at this freeze both
censuses are all-`absent` and stay so, and the two `SpecCoverage` numerator
modules the plan schedules inside the builder's fence do not exist yet.

Nothing here reopens DB-03: the job queue stays deterministic FIFO state inside
the configuration, and this packet gives that state a named home plus the
DB-05 specification/realizer pair R-P5 requires for
`requirement.hostenqueuepromisejob.3`.

## 2. Pins and census citations

| Item | Value |
| --- | --- |
| ECMA-262 source | `vendor/ecma262-0248456c/spec.html`, `tc39/ecma262` `0248456c758431e4bb8e5d26333ff1865123c9cd`, tag `es2026`, 2,978,793 bytes, SHA-256 `ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0` |
| Web IDL source | `vendor/whatwg-webidl-a652053f/index.bs`, `whatwg/webidl` `a652053f1e74e4aaf647528deb174012ed6c909f`, March 2026 Review Draft, 695,845 bytes, SHA-256 `3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83` |
| ES2026 census | `generated/ecma262-census.tsv`, 77 rows, header `rows=77` |
| Web IDL census | `generated/webidl-census.tsv`, 121 rows, header `rows=121` |
| Streams source | `vendor/whatwg-streams-b9ba9f49/index.bs`, unchanged by this lane |

Byte offsets are 0-based and ends are exclusive. No line number is cited
anywhere in this packet. Row ids are exactly the ids of the two generated
censuses; per R-P17 the frozen spellings
`op.dfn-perform-steps-once-promise-is-settled`, `op.waiting-for-all-promise`
and `op.mark-a-promise-as-handled` stand, and the surveys' `op.react` spelling
is not adopted. The span digests this packet quotes are the digest column of
those two files; `docs/PROMISE-DAG.md` carries the alias table.

## 3. Shape of the packet

Extraction-seeded, per R-P12, in three parts landed in this order.

- **Part A — moves and generalizations.** Every ascription cites an inventory
  row `E-01`..`E-74` with its reuse mode. Nothing in part A is designed; it
  relocates or generalizes what `Whatwg.Streams` already proves.
- **Part B — gaps.** Every ascription cites a gap id `G-01`..`G-11` and the
  census rows it realizes.
- **Part C — `Boundary.Exception`, last.** R-P14 makes it its own sub-slice,
  landed after every other move has shown the P4-P7 batteries unchanged.

An ascription that duplicates an inventoried Streams declaration without naming
its row and mode is a defect under R-P12 and the packet does not freeze.

The six batteries and their ascription counts:

| Module | `#check` | `example` | `#print axioms` | Role |
| --- | ---: | ---: | ---: | --- |
| `WhatwgTest/Ecma262/JobsContract.lean` | 27 | 0 | 0 | part A/B interface, `Whatwg.Ecma262.Jobs` |
| `WhatwgTest/Ecma262/JobsLaws.lean` | 20 | 0 | 0 | part A/B laws, `Whatwg.Ecma262.Jobs` |
| `WhatwgTest/Ecma262/PromiseContract.lean` | 88 | 0 | 0 | part A/B interface, `Whatwg.Ecma262.Promise` |
| `WhatwgTest/Ecma262/PromiseLaws.lean` | 44 | 0 | 0 | part A/B laws, `Whatwg.Ecma262.Promise` |
| `WhatwgTest/WebIdl/PromiseContract.lean` | 33 | 0 | 0 | part B interface (16) and laws (17) |
| `WhatwgTest/WebIdl/ExceptionsContract.lean` | 69 | 0 | 0 | part C interface (54) and laws (15) |
| `WhatwgTest/Streams/PromiseBridge.lean` | 90 | 13 | 0 | preservation (53 + 13) and bridging (37) |
| `WhatwgTest/Ecma262/PromiseAxiomReport.lean` | 0 | 0 | 125 | the receipt list |

371 `#check` ascriptions, 13 `example`s and 125 axiom receipts. 125 of the
ascriptions are theorem obligations, and the axiom report names exactly those
125.

## 4. Part A — the exact surface

### 4.1 The promise state carrier (`E-01`, move)

`Whatwg.Ecma262.Promise.State : Type → Type → Type`, constructors `pending`,
`fulfilled (value : value)`, `rejected (reason : reason)`, with
`deriving DecidableEq, Repr`. Two type parameters per R-P13. Anchors PSTATE
(`slot.PromiseState`, 2744957..2745252) and PRESULT (`slot.PromiseResult`,
2745263..2745619): the type is the first-order fusion of the two slots, and the
three tags are the clause's `~pending~ / ~fulfilled~ / ~rejected~`.

Streams keeps

```lean
abbrev Whatwg.Streams.Readable.PromiseState (α ε : Type) :=
  Whatwg.Ecma262.Promise.State α (Whatwg.Streams.Boundary.Exception ε)
```

The constructor and field names are the Streams ones, so every `.pending`,
`.fulfilled v` and `.rejected e` in `Whatwg/Streams/**` resolves unchanged.

Obligations, all ascribed in `PromiseBridge.lean`:

1. `Whatwg.Streams.Readable.PromiseState` still elaborates at
   `Type → Type → Type` and its three constructors at their old types.
2. `inferInstance : DecidableEq (Readable.PromiseState Unit Nat)` and
   `inferInstance : Repr (Readable.PromiseState Unit Nat)` still elaborate:
   the derived instances must be found **through** the reducible `abbrev`, or
   `decide` and the `simp` normal forms in `Whatwg/Streams/Writable/Laws.lean`
   change.
3. `Whatwg.Streams.Writable.unitPromise_eq` keeps its statement and stays
   `rfl`. The `example` re-deriving
   `Writable.UnitPromise ε = Readable.PromiseState Unit ε` by `intros; rfl`
   must close.

### 4.2 The pull and sink answer types (`E-02`, `E-03`, move; `E-04`..`E-06`)

`Whatwg.Ecma262.Promise.Outcome : Type → Type`, constructors `fulfilled` and
`rejected (reason : reason)`, `deriving DecidableEq, Repr`. Anchors FULFILL
(`op.fulfillpromise`, 2695419..2696230) and REJECT (`op.rejectpromise`,
2699323..2700252): the settled outcome a foreign callback's promise delivers,
with the value fixed to unit.

**One parameter, not two.** `Readable.PullAnswer.fulfilled` takes no argument.
A two-parameter `Outcome value reason` whose `fulfilled` carries a value would
break every `.fulfilled` use site in `Whatwg/Streams/**`, which R-P12 forbids.
The value-carrying settled outcome already exists as `Except reason value` and
is deliberately not minted a second time (duplicate prevention).

`Whatwg.Ecma262.Promise.Returned : Type → Type`, constructors `pending` and
`settled (answer : Outcome reason)`, `deriving DecidableEq, Repr`: the
`[[PromiseState]]` of a returned promise observed at callback-return time,
before any reaction runs.

Streams keeps

```lean
abbrev Whatwg.Streams.Readable.PullAnswer (ε : Type) :=
  Whatwg.Ecma262.Promise.Outcome (Whatwg.Streams.Boundary.Exception ε)
abbrev Whatwg.Streams.Readable.PullReturn (ε : Type) :=
  Whatwg.Ecma262.Promise.Returned (Whatwg.Streams.Boundary.Exception ε)
```

`E-04`, `E-05`, `E-06` are re-pointed **transitively**: the three `Writable`
abbrevs `UnitPromise`, `SinkAnswer` and `SinkReturn` keep their current text
over the three `Readable` names and are not edited, so their declaration-count
contribution is zero and `unitPromise_eq`, `sinkAnswer_eq`, `sinkReturn_eq`,
`unitPromise_roundtrip`, `sinkReturnToShared_eq` and `sinkReturn_roundtrip`
stay `rfl`. Six `example`s in `PromiseBridge.lean` re-derive exactly those
definitional equalities.

Decision 6 keeps all three carriers distinct; the isomorphisms between them are
bridging lemmas, not identifications.

### 4.3 The general promise table (`E-13`..`E-15`, `E-18`..`E-23`, generalize)

```lean
structure Whatwg.Ecma262.Promise.Cell (value reason : Type) where
  state : Whatwg.Ecma262.Promise.State value reason
  handled : Bool
  deriving DecidableEq, Repr

structure Whatwg.Ecma262.Promise.Table (value reason : Type) where
  entries : List (Nat × Whatwg.Ecma262.Promise.Cell value reason)
  next : Nat
  deriving DecidableEq, Repr
```

Identity allocation, lookup, fresh, settle and mark-handled over `Nat` ids:
`Table.empty`, `Table.getCell`, `Table.get`, `Table.isPending`, `Table.fresh`,
`Table.settle`, `Table.markHandled`. Anchors: the clause row
`clause.properties-of-promise-instances` (2744135..2746691) for the table,
PHANDLED (`slot.PromiseIsHandled`, 2746322..2746637) for the cell flag,
NEWCAP (`op.newpromisecapability`, 2696238..2698770) for `fresh`, FULFILL and
REJECT for `settle`, HANDLEDOP (`op.mark-a-promise-as-handled`,
356060..356713) for `markHandled`.

The two Streams tables are its instances. `Writable.State.promises`,
`nextPromise` and `handled` are read by the view

```lean
def Whatwg.Streams.Writable.promiseTable {α ε : Type} (s : State α ε) :
    Whatwg.Ecma262.Promise.Table Unit (Whatwg.Streams.Boundary.Exception ε)
```

and `Readable.State.readPromises` and `nextRead` by
`Whatwg.Streams.Readable.readTable`, at value parameter `ReadResult α`. That
second instance is why the general state needs two type parameters
(`E-22`, decision 1).

**`E-22` is deliberately partial in this packet.** `Readable.State.readPromises`
has no `lookup`/`fresh`/`settle` of its own: every update is an inline
`List.map` inside `Readable/DefaultController.lean` and `DefaultReader.lean`.
Turning those five inline updates into `Table` calls would change a Streams
definition body, which the Q3 fence forbids. Only the view and its `get` law
land now; the operation-level generalization of `E-22` is deferred, with that
reason, to Q4.

### 4.4 The eleven `attribute [local simp]` functions and their obligations

Decision 5 and inventory condition 3: no function named in one of the four
`attribute [local simp]` sets is a `move`. Each stays a `def` in
`Whatwg.Streams` with its body unchanged, so `simp [f]` keeps rewriting with
`f`'s own equation lemmas.

The inventory's "eleven promise-layer functions" are the eleven non-observation
names of the `Whatwg/Streams/Writable/Lifecycle.lean` set. They are listed
first; the further `generalize` rows named in the other three sets follow,
because they carry the same obligation.

| # | Function (inventory row, mode) | Bridging lemma | Exact `simp` obligation |
| ---: | --- | --- | --- |
| 1 | `Writable.lookupPromise` (`E-18`, generalize) | `Writable.lookupPromise_bridge` | body unchanged; `example` re-derives `lookupPromise s id = (s.promises.find? (fun p => p.1 == id)).map Prod.snd` by `rfl`; `Writable.lookupPromise_eq` unchanged; named in the WF, TR and PU sets |
| 2 | `Writable.freshPromise` (`E-19`, generalize) | `Writable.freshPromise_bridge`, under `s.nextPromise ∉ s.handled` | body unchanged; `freshPromise_pending`, `_fulfilled`, `_rejected` unchanged and still state the append shape verbatim; named in WF, TR, PU |
| 3 | `Writable.settle` (`E-20`, generalize) | `Writable.settle_bridge` | body unchanged; `settle_pending` and `settle_other` unchanged; named in WF, TR, PU |
| 4 | `Writable.markHandled` (`E-21`, generalize) | `Writable.markHandled_bridge`, `Writable.handled_bridge` | body unchanged; `example` re-derives `markHandled_eq`'s right-hand side by `rfl`; named in WF, TR, PU |
| 5 | `Writable.attachSink` (`E-37`, generalize) | `Writable.attachSink_settled_jobs`, `Writable.attachSink_pending_jobs` | body unchanged; the bridge is stated on the job queue alone, because `attachSink` also clears the close and abort algorithm slots and the general `react` must not; named in WF, TR, PU |
| 6 | `Writable.acceptAnswer` (`E-38`, generalize) | `Writable.acceptAnswer_jobs` | body unchanged; the `operationPhase … = some .awaiting` guard stays in Streams; named in WF, TR, PU |
| 7 | `Writable.tick` (`E-46`, generalize) | `Writable.tick_dequeue_bridge` | body unchanged; `tick_job_fifo` and `tick_no_job` unchanged and re-derivable from the bridge; named in WF, TR, PU |
| 8 | `Writable.operationPhase` (`E-36`, keep) | none | keep: no general counterpart is introduced, and `ObserverPhase` is not unified with `OperationPhase` in this packet |
| 9 | `Writable.setOperationPhase` (`E-36`, keep) | none | keep, as 8 |
| 10 | `Writable.ensureReadyRejected` (`E-42`, keep) | none | keep; it is the one place `markHandled` is applied to a fresh cell, and the general `Table.markHandled` must accept that ordering |
| 11 | `Writable.updateBackpressure` (`E-43`, keep) | none | keep; its retention property is what `Table.fresh_old` buys |
| 12 | `Transform.subscriptionPromise` (`E-30`, generalize) | `Transform.reactions_promises` | body unchanged; `example` re-derives the three constructor receipts by `rfl`; named in TR |
| 13 | `Transform.subscribe` (`E-31`, generalize) | `Transform.subscribe_reactions_bridge` (pending branch) | body unchanged; `subscribe_pending/_fulfilled/_rejected/_missing` unchanged; named in TR |
| 14 | `Transform.notify` (`E-32`, generalize) | none in this packet | body unchanged; only the queueing half generalizes, and the component dispatch stays in Streams; the bridge is deferred with that reason; named in TR |
| 15 | `Transform.settle` (`E-33`, generalize) | none in this packet | body unchanged; the general `Table.settleAndTrigger` and `triggerReactions_order` land, but relating them to the `foldlM` over the filtered subscription list needs `notify`'s bridge and is deferred; named in TR |
| 16 | `Transform.runJob` (`E-51`, generalize) | none in this packet | body unchanged; its `.writable` branch re-checks the mailbox head, which is stream-specific; named in TR |
| 17 | `Transform.tick` (`E-53`, generalize) | `Transform.tick_dequeue_bridge` | body unchanged; `tick_job_fifo` and `tick_no_job` unchanged; named in TR |
| 18 | `Readable.runPullJob` (`E-49`, generalize) | `Readable.runPullJob_dequeue_bridge` | body unchanged; `runPullJob_suspended/_empty/_cons` unchanged; named in TR |
| 19 | `Transform.lookupPromise` (`E-25`, keep) | none | keep, pure adapter; `example` re-derives `lookupPromise_eq` by `rfl`; named in TR |
| 20 | `Transform.freshInternal` (`E-26`, keep) | none | keep; its four receipts unfold `Writable.freshPromise` and `Writable.lookupPromise` inside their proofs, so those two must stay unfoldable; named in TR |
| 21 | `Piping.allWrittenSettled` (`E-56`, generalize) | `Piping.allWrittenSettled_bridge` | body unchanged; named in PU |

Rows 8 to 11 are `keep` and owe no bridging lemma; they are listed because the
inventory's eleven include them and because R-P12 makes an unnamed duplicate a
defect just as much as an unnamed move. Rows 14, 15 and 16 are `generalize`
rows whose bridge this packet defers with a stated reason, which acceptance
condition 8 of the plan requires to be visible rather than silent.

### 4.5 The payload-polymorphic job queue (`E-44`..`E-53`, generalize)

```lean
structure Whatwg.Ecma262.Jobs.Queue (payload : Type) where
  pending : List payload
  deriving DecidableEq, Repr
```

with `Queue.empty`, `Queue.enqueue` (appends at the tail), `Queue.enqueueAll`,
`Queue.oldest` and `Queue.dequeue` (dequeue-oldest). Decision 4: polymorphic,
because the three Streams queues carry `Readable.PullAnswer` (`E-48`),
`Writable.SinkJob` (`E-45`) and `Transform.Job` (`E-52`). `DecidableEq` and
`Repr` are conditional on the payload, because `SinkJob` derives both and
`Transform.Job` derives `Repr` only.

**The general FIFO law**, verbatim as frozen in
`WhatwgTest/Ecma262/JobsLaws.lean`:

```lean
theorem Whatwg.Ecma262.Jobs.Queue.dequeue_fifo :
  ∀ {payload : Type} (oldest : payload) (queued later : List payload),
    Whatwg.Ecma262.Jobs.Queue.dequeue
        (Whatwg.Ecma262.Jobs.Queue.enqueueAll
          (Whatwg.Ecma262.Jobs.Queue.mk (oldest :: queued)) later) =
      some (oldest, Whatwg.Ecma262.Jobs.Queue.mk (queued ++ later))
```

Taking `later := []` gives `Queue.dequeue_cons`, which is what both corollaries
need. Taking `later` nonempty is the ordering content of
`requirement.hostenqueuepromisejob.3` (634739..634841, digest
`6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65`): a job
scheduled after `oldest` never overtakes it.

**The two corollaries**, verbatim as they stand today in
`Whatwg/Streams/Writable/Laws.lean` and `Whatwg/Streams/Transform/Laws.lean`.
Their statements are frozen P5a and P6a theorems; this packet forbids their
change and requires that they be re-derived from the general law through the
component bridges rather than re-proved from `tick`:

```lean
theorem Whatwg.Streams.Writable.tick_job_fifo :
  ∀ {α ε : Type} (s : State α ε) (job : SinkJob α ε) (jobs : List (SinkJob α ε)),
    tick { s with control := [], jobs := job :: jobs } =
      some { s with control := [.react job], jobs := jobs }

theorem Whatwg.Streams.Transform.tick_job_fifo :
  ∀ {α β ε : Type} (s : State α β ε) (job : Job α ε) (tail : List (Job α ε)),
    s.control = [] → s.writable.control = [] → s.readable.frames = [] →
    s.jobs = job :: tail →
    tick s = runJob { s with jobs := tail } job
```

The bridges through which they are re-derived are
`Writable.tick_dequeue_bridge` and `Transform.tick_dequeue_bridge`, whose
hypotheses are the two components' own spellings of "the execution context
stack is empty". `E-46` records why this is the honest shape: the queue stage
is one branch of a twenty-branch `tick`, so the general law is
`Queue.dequeue`'s equation plus a Streams bridging lemma, not a relocation of
`tick`.

`Readable.runPullJob` is the third instance, bridged by
`Readable.runPullJob_dequeue_bridge`; its three receipts
`runPullJob_suspended`, `runPullJob_empty` and `runPullJob_cons` are the
general dequeue laws and re-derive without re-proof.

### 4.6 The reaction and registration cluster

`Whatwg.Ecma262.Promise.ReactionType` (`fulfill`, `reject`),
`ReactionPhase` (`waiting`, `queued (job : Nat)`, `running (job : Nat)`,
`done`), `Reaction (body : Type)` with fields `id`, `promise`, `kind`,
`handler : Option body`, `phase`, and `Reactions (body : Type)` with fields
`fulfill`, `reject`, `next`. Anchors REACTREC (2690445..2692671), its three
field rows (2691475..2691802, 2691815..2692138, 2692151..2692611), PFULFILL
(2745630..2745966) and PREJECT (2745977..2746311).

The P8a rename table is applied: `PromiseRef` becomes
`Whatwg.Ecma262.Promise.Ref` with `PromiseRef.local` renamed `Ref.cell`,
because `local` is a Lean 4 keyword and cannot be a field name;
`ObserverPhase` becomes `ReactionPhase` with its four constructors unchanged;
`Registration` becomes `Reaction`; `register` becomes
`Whatwg.WebIdl.Promise.react`; `notifySettled` becomes
`Whatwg.Ecma262.Promise.triggerReactions`; `Job`, `enqueueJob` and
`queuedJobs` become `Whatwg.Ecma262.Jobs.ReactionJob`,
`Whatwg.Ecma262.Jobs.Queue.enqueue` and `Queue.pending`; `Active` becomes
`Whatwg.Ecma262.Jobs.Active` with `observer` renamed `job` and both
job-carrying constructors taking a serial rather than the whole record.
`Reaction.kind` is **new content** under `G-01`, not a rename: Streams has no
`[[Type]]` tag.

`Transform.Subscription` (`E-29`) stays where it is and is read by
`Whatwg.Streams.Transform.reactions`, which builds both general lists
positionally from `State.subscriptions`, giving the paired entries one id.
`Reactions.registered` is the one-list view Streams instantiates
(decision 8), and `Transform.reactions_registered` and
`Transform.reactions_promises` are its bridging lemmas.
`Transform.subscriptionPromise` (`E-30`) is `Reaction.promise`.

`Whatwg.Ecma262.Promise.triggerReactions` is `TriggerPromiseReactions`
(TRIGGER, `op.triggerpromisereactions`, 2700260..2701212), whose entire content
is "enqueue a reaction job for each reaction, in list order". `E-33` records
that `Transform.settle` states only `settle_pending` and `settle_other`, so the
order law is **new content, not extraction**, and the packet declares it as
such:

```lean
theorem Whatwg.Ecma262.Promise.triggerReactions_order :        -- mask M2
  ∀ {value reason body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))),
    (triggerReactions rs promise kind argument q).2.pending =
      q.pending ++ (Reactions.waitingOn rs promise kind).map
        (fun r => Jobs.ReactionJob.mk r.id argument)

theorem Whatwg.Ecma262.Promise.triggerReactions_once :         -- mask M1
  ∀ …, Reactions.waitingOn (triggerReactions rs promise kind argument q).1
         promise kind = []
```

`Whatwg.WebIdl.Promise.react` is `PerformPromiseThen` steps 8 to 10 (REACT,
350075..352408), generalizing `Transform.subscribe` (`E-31`) and
`Writable.attachSink` (`E-37`), the two independently written instances of the
same case split. It keeps `E-31`'s `Option` result: a missing cell has no
transition, where `PerformPromiseThen` is total, and `react_missing` records
the difference rather than smoothing it. `uponFulfillment` and `uponRejection`
(UPONF 352410..352816, UPONR 352818..353237) are `react` with one handler
`none`, which is why `Reaction.handler` is `Option body`:
`field.promisereaction-records.Handler` admits an empty handler.

### 4.7 The two wait-for-all-shaped predicates (`E-55`, `E-56`, generalize)

`Whatwg.WebIdl.Promise.AllSettled` (`Prop`) and `allSettled` (`Bool`) over the
general table, with `allSettled_iff` as their agreement lemma. `E-56` records
that the `Prop`/`Bool` pair has no stated agreement lemma today, so that lemma
is new content. `Piping.WritesSettled` and `Piping.allWrittenSettled` are
bridged by `Piping.writesSettled_bridge` and
`Piping.allWrittenSettled_bridge`, both under the hypothesis that every link's
write has been submitted, because the Streams forms answer `false` for a link
that has not.

`E-55` warns that calling the predicate `wait for all` overclaims. The packet
therefore keeps the predicate and the operation as separate names with separate
laws; see section 5 and decision 11.

## 5. Part B — the gaps, in first-packet scope only

| Declaration | Gap | Census rows realized |
| --- | --- | --- |
| `Promise.Capability` with `promise`, `resolve`, `reject`; `newPromiseCapability` | `G-03` | `record.promisecapability-records` 2687751..2690437; `field.promisecapability-records.Promise` 2688749..2688997; `.Resolve` 2689010..2689283; `.Reject` 2689296..2689567; `op.newpromisecapability` 2696238..2698770 |
| `Promise.ResolvingFunctions`, `createResolvingFunctions`, `callResolve`, `callReject` | `G-03` | `op.createresolvingfunctions` 2692679..2695411 |
| `Promise.ReactionType`, `Reaction`, `Reactions` and their six operations | `G-01` | `record.promisereaction-records` 2690445..2692671 with its three field rows; `slot.PromiseFulfillReactions` 2745630..2745966; `slot.PromiseRejectReactions` 2745977..2746311 |
| `Promise.triggerReactions` with its order and once-only laws | `G-01` | `op.triggerpromisereactions` 2700260..2701212 |
| `Jobs.ReactionJob`, `newReactionJob` | `G-07` | `op.newpromisereactionjob` 2702885..2705591; `record.jobcallback-records` 628436..630247 |
| `Promise.performPromiseThen` with a result capability | `G-11` | `op.performpromisethen` 2740635..2743669 |
| `Jobs.Queue` as the realm-independent FIFO queue and `hostEnqueuePromiseJob` | `G-07` | `hook.hostenqueuepromisejob` 633447..635836 |
| `Jobs.RunCondition`, `Active`, `mayRun`, `step`; `FifoRequirement` and `run` | `G-08` | `requirement.jobs.1` 625769..626250; `requirement.jobs.2` 626257..626350; `requirement.jobs.3` 626357..626479; `requirement.hostenqueuepromisejob.3` 634739..634841 |
| `WebIdl.Promise.newPromise`, `resolvedWith`, `rejectedWith`, `resolve`, `reject`, `markAsHandled` | Web IDL names over the `E-19`/`E-21` core | `op.a-new-promise` 347604..347946; `op.a-promise-resolved-with` 347948..348631; `op.a-promise-rejected-with` 348633..349214; `op.resolve` 349216..349783; `op.reject` 349785..350073; `op.mark-a-promise-as-handled` 356060..356713 |
| `WebIdl.Promise.react`, `uponFulfillment`, `uponRejection` | `G-11` steps 8 to 10 with an empty handler admitted | `op.dfn-perform-steps-once-promise-is-settled` 350075..352408; `op.upon-fulfillment` 352410..352816; `op.upon-rejection` 352818..353237 |
| `WebIdl.Promise.WaitResult`, `waitForAll` | `G-06`, partially | `op.wait-for-all` 353239..354879 |

### 5.1 `HostEnqueuePromiseJob`: the run condition as a stated requirement

Under DB-03 and R-P5 the hook is a `requirement`, not a `foreignBoundary`, and
the obligation is the DB-05 shape already used for `ReadableStreamPipeTo`.

`FifoRequirement scheduled executed` is the specification over runs;
`Jobs.run` is the deterministic FIFO realizer extracted from three places
(`E-46`, `E-49`, `E-53`); `Jobs.run_fifo` is the realizer theorem, and
`Jobs.hostEnqueuePromiseJob_order` says the realizer still satisfies it when
further jobs are scheduled before the run. The `requirement.jobs.1` condition —
"no running context in the agent for which the job is scheduled and that
agent's execution context stack is empty" — is `RunCondition`, and
`Jobs.step_blocked` forbids starting a job in any other activation, which is
also `requirement.jobs.2`'s "only one Job may be actively undergoing
evaluation". `run` is not a semantic fuel parameter: `Jobs.run_split` states
that whatever it did not run is still queued, so exhaustion is a live frontier
and never a terminal outcome (DB-07).

`G-08` is closed only for the *statement* of the condition. The three Streams
spellings remain per-component hypotheses; a single global configuration that
observes the condition is P8 and stays open.

### 5.2 Explicitly out of the first packet

Each with its gap id. A later packet closes it; nothing here may be read as
covering it.

- **`G-02` remainder** — the handled-bit consumer. `HostPromiseRejectionTracker`
  (`hook.host-promise-rejection-tracker`, 2701220..2702791) is absent. Nothing
  in this packet reads the bit; `Table.markHandled_state` says only that
  marking does not change the promise state.
- **`G-04`** — `IsPromise` (`op.ispromise`, 2698778..2699315) and the value
  universe in which a promise could be one value among others.
- **`G-05`** — thenable adoption. `NewPromiseResolveThenableJob`
  (`op.newpromiseresolvethenablejob`, 2705599..2707541) and the adoption branch
  of `CreateResolvingFunctions`. `callResolve` settles with a plain value and
  never looks up a `then` method. `Transform.Completion.adopt` (`E-35`) adopts
  an internal identity and is `keep`; no ascription presents it as adoption.
- **`G-06` remainder** — `get a promise to wait for all`
  (`op.waiting-for-all-promise`, 354881..356058) and its `[=Queue a microtask=]`
  step. No ordering claim about that operation is made.
- **`G-07` remainder** — the realm parameter, the Job Abstract Closure carrier
  beyond a first-order descriptor, `HostMakeJobCallback` (630253..631441) and
  `HostCallJobCallback` (631447..632699), and the JobCallback record's
  `[[HostDefined]]` field (629941..630193).
- **`G-09` remainder** — the exception universe beyond what part C needs:
  `create a DOMException` (665488..666331), `create a DOMException derived
  interface` (666333..667324), `throw an exception` (667326..667543), the six
  `rule.domexception-derived-*` rows, `QuotaExceededError` and its
  serialization steps, and the 25 legacy `idl.domexception-*-err` code
  constants.
- **`G-10`** — the Completion carrier beyond `Except`. This packet uses
  `Except reason value` for settled outcomes and `Option` for "no transition",
  and states plainly that the two are not the same thing and that neither is a
  Completion Record. R-P9 confirms the reading; the carrier itself is Q4.
- **`G-11` remainder** — `Promise.prototype.then` / `catch` / `finally`
  (2740014..2743689, 2737067..2737453, 2737669..2740006), the four combinators
  and their `PerformPromise*` operations, `Promise ( executor )`
  (2708413..2711495), `Promise.resolve` / `reject` / `try` / `withResolvers`,
  `get Promise [%Symbol.species%]`, `GetPromiseResolve` and
  `IfAbruptRejectPromise`.
- Every inventory row in group **G** (`E-62`..`E-74`) is `keep` and belongs to
  DB-04's claim scope, not to `Whatwg.Ecma262` or `Whatwg.WebIdl`. A Q3
  ascription that re-stated one of them would be a defect; none does.

## 6. Part C — `Boundary.Exception`, landed last (R-P14)

`Whatwg.WebIdl.Exceptions.Simple` has exactly the five kinds of
`op.dfn-simple-exception` (194433..194721): `evalError` (`type.eval-error`,
194542..194576), `rangeError` (`type.range-error`, 194577..194612),
`referenceError` (`type.reference-error`, 194613..194652), `typeError`
(`type.type-error`, 194653..194687), `uriError` (`type.uri-error`,
194688..194721).

`Whatwg.WebIdl.Exceptions.Name` has exactly the 32 base `DOMException` error
names, one `type.*` row each, in specification order by ascending byte offset:

| # | Constructor | Row | Span | Digest |
| ---: | --- | --- | --- | --- |
| 1 | `indexSizeError` | `type.indexsizeerror` | 200596..200948 | `a78fab8f0aa76c8e861b409bfaedfecdfb45a4902dc41e9b0ea9dc7240a3b07c` |
| 2 | `hierarchyRequestError` | `type.hierarchyrequesterror` | 200957..201323 | `47148ba23577331f23085583db568390eb676e1e5da0eb0dbf217cf232ab2403` |
| 3 | `wrongDocumentError` | `type.wrongdocumenterror` | 201332..201674 | `d590c3a636b3e789e16529a3e72f35e5a883eb2dca6b29260e93b513f01e503c` |
| 4 | `invalidCharacterError` | `type.invalidcharactererror` | 201683..202027 | `d6ee3a99130a2233697485719c8be7fee4206a6476e98643b7b93a496f0cbc48` |
| 5 | `noModificationAllowedError` | `type.nomodificationallowederror` | 202036..202394 | `7caa02a5efd0af1a87df073e2efcda61958725d1c05581bde74dfb7d0c370783` |
| 6 | `notFoundError` | `type.notfounderror` | 202403..202709 | `4c8d7c60abde59dba7d92a596a89935c0f34e6995706afdc7805354c9d1bed41` |
| 7 | `notSupportedError` | `type.notsupportederror` | 202718..203038 | `7ef8b3a7417ef440e6cbb241c0a612d10fbad37ca6e276cdec84665a6fdba4eb` |
| 8 | `inUseAttributeError` | `type.inuseattributeerror` | 203047..203401 | `cdcb8259df8f08935d5de9972c8581d982824ce0b4f24c4e21366eb1eb587ad8` |
| 9 | `invalidStateError` | `type.invalidstateerror` | 203410..203734 | `37f9c581b7ef85e806642ab4359c5d2a8c178c985012e556c6899dd73a182110` |
| 10 | `syntaxError` | `type.syntaxerror` | 203743..204053 | `a53db98ed19f851882b83ed576f99404c39648335b82da1e835a366753532e40` |
| 11 | `invalidModificationError` | `type.invalidmodificationerror` | 204062..204423 | `39d4d1ebf79d34688ba197b09eba06ea7ce31202d870bcf887e333f6676fb800` |
| 12 | `namespaceError` | `type.namespaceerror` | 204432..204785 | `059c76bc893cbf7b23d449727a898649eadccfe1f68852c71a48c42a7b9bbec7` |
| 13 | `invalidAccessError` | `type.invalidaccesserror` | 204794..205410 | `36eb12e30a0a5172ff2e20ae8938f1857701721c16b3f5e6888c423dcbb5326a` |
| 14 | `typeMismatchError` | `type.typemismatcherror` | 205419..205776 | `0c1751de3cb145f9d78e5d1fffa55270a3a18456e32336b8db05f8aab7bc3999` |
| 15 | `securityError` | `type.securityerror` | 205785..206083 | `59c3f7350f0655d8ae23f30ad8e7c00f16f241aa12fa2cc7dac8aa21c202305c` |
| 16 | `networkError` | `type.networkerror` | 206092..206385 | `5fd5052507c74a89ef7ada1bff51a85643377976b2b1c1a42cb5faf331170402` |
| 17 | `abortError` | `type.aborterror` | 206394..206680 | `18920890af5a1bb435cd9d7215ef532f9c599e4400f56e012cf25da6b84ced66` |
| 18 | `urlMismatchError` | `type.urlmismatcherror` | 206689..207022 | `53910d07cfa4481ecde98f9aa78594b271e216a61c58e27a8a7ae7c9d127c3f5` |
| 19 | `timeoutError` | `type.timeouterror` | 207404..207696 | `24af6447be4228aa7f4ab63f6d49380fdc1ca73399af82882cb91e0926e9ee6e` |
| 20 | `invalidNodeTypeError` | `type.invalidnodetypeerror` | 207705..208100 | `4f6c50936ec7d13da070d3b5d22443da1c1a12911d3c0b455ec06901be69f01c` |
| 21 | `dataCloneError` | `type.datacloneerror` | 208109..208416 | `f4989a2f14bed893723de1a9c1bcd2f037d933bf07a5811d7ae37beae18fe49b` |
| 22 | `encodingError` | `type.encodingerror` | 208425..208646 | `09f5bb975f55e29abebae3e9d7d9ba514d815a0b707a0ee158e1252ceef52a47` |
| 23 | `notReadableError` | `type.notreadableerror` | 208655..208853 | `cb8c86f88a824b41d9caffa5e0f4159a77b97757c710acd34fc0b2f7049ff2de` |
| 24 | `unknownError` | `type.unknownerror` | 208862..209096 | `b18781b2f65d78ec81babe2c219ebb8f4e965034333e33bf909f5665689eb2ab` |
| 25 | `constraintError` | `type.constrainterror` | 209105..209369 | `2bbb3bd78064f6f703f29e3439dc75f4c25d15a9584a888621b890cc69c0ae7f` |
| 26 | `dataError` | `type.dataerror` | 209378..209560 | `1250a40d36b944ce09519ab3baab26b848091322ec10d322f89ce6e62c25cbc9` |
| 27 | `transactionInactiveError` | `type.transactioninactiveerror` | 209569..209862 | `3e7b1fcf5ac3c2dfd5eb3d90b5ea49f9c9166db31fb9fec6219c24ea6ce0291d` |
| 28 | `readOnlyError` | `type.readonlyerror` | 209871..210112 | `91d02708973dcf9c44bf5e4a8704880161e48e6705b0b57c2e2a8ff475b12a47` |
| 29 | `versionError` | `type.versionerror` | 210121..210382 | `3457c1af6ec4f7e1eb224c85b8e3067cfe3469706bf9e5c5d014962e5ba0ef47` |
| 30 | `operationError` | `type.operationerror` | 210391..210609 | `63019aafdb8dd9cecc174c10c15e970a68e941b977868c4b4a851c9c4c037cca` |
| 31 | `notAllowedError` | `type.notallowederror` | 210618..210913 | `f3382081f3f1551544d0eacad475a64b1c46eebd22c2eefbe7207f298022aa97` |
| 32 | `optOutError` | `type.optouterror` | 210922..211114 | `79525ead90cfbfd0d548f12b2d1abd9ddb13c0c6b9c053ba1a87e43f8d2b3eb5` |

The gap between rows 18 and 19 is where `QuotaExceededError` used to be; at
this pin it is a derived interface (`idl.quota-exceeded-error`,
213527..213598) and the census has no `type.` row for it, so it is **not** a
`Name` constructor. `Name.all_length = 32`, `Name.all_nodup` and
`Name.all_complete` make the table checkable in both directions.

```lean
inductive Whatwg.WebIdl.Exceptions.Exception (reason : Type) where
  | simple (kind : Simple) (id : Nat)
  | domException (name : Name) (id : Nat)
  | foreign (reason : reason)
  deriving DecidableEq, Repr
```

**Allocation identity is preserved** (R-P14). Web IDL simple exceptions carry
no identity, but the Streams constructors carry a `Nat` precisely so that two
RangeErrors created by nested size callbacks are distinguishable
(`nested_invalid_sizes_fresh_errors`, `Whatwg/Streams/Readable/Reentrancy.lean`).
`Exception.simple_eq_iff` and `Exception.domException_eq_iff` are the receipts.

**The bridging so the 69 dependents are unchanged.** `E-59` is `generalize`,
not `move`: `Whatwg.Streams.Boundary.Exception` keeps its three constructors
and its `deriving DecidableEq, Repr`, so every `.rangeError id` in the 69
dependent theorems across eight files (WL 29, TL 17, RL 11, PL 4, BE 3, RT 2,
PU 2, WF 1) resolves unchanged **by construction**. The relation to the general
type is the additive pair

```lean
def Whatwg.Streams.Boundary.Exception.toWebIdl {ε : Type} :
  Exception ε → Whatwg.WebIdl.Exceptions.Exception ε
def Whatwg.Streams.Boundary.Exception.ofWebIdl {ε : Type} :
  Whatwg.WebIdl.Exceptions.Exception ε → Option (Exception ε)
```

with `toWebIdl_rangeError`, `toWebIdl_typeError`, `toWebIdl_foreign`,
`ofWebIdl_toWebIdl`, `toWebIdl_injective` and `toWebIdl_ofRangeError`. A
`move` here would break the 69 dependents, because the general constructor
takes a kind as well as an identity; that is WS-PROM-CE-017.

## 7. The mask (DB-04)

Every theorem names one mask. The rule this packet applies is the plan's:
a theorem whose *statement* observes the order in which settlements happen or
in which reaction jobs enter the queue is **M2**; a theorem that observes only
a cell value, a branch, a table shape or a terminal result is **M1**. Each
battery docstring carries the classification per block.

**M2 — 12 theorems.**

| Theorem | Why |
| --- | --- |
| `Jobs.Queue.dequeue_cons` | delivers the oldest job, so the order is observed |
| `Jobs.Queue.dequeue_fifo` | the general FIFO law |
| `Jobs.run_fifo` | the realizer theorem for `requirement.hostenqueuepromisejob.3` |
| `Jobs.hostEnqueuePromiseJob_order` | the same under further scheduling |
| `Promise.triggerReactions_order` | reaction jobs enter the queue in registration order |
| `Promise.Table.settleAndTrigger_pending` | settle followed by the ordered trigger |
| `Promise.performPromiseThen_fulfilled`, `_rejected` | a reaction job enters the queue |
| `WebIdl.Promise.react_fulfilled`, `react_rejected` | a reaction job enters the queue |
| `WebIdl.Promise.waitForAll_success` | the result list is in argument order |
| `WebIdl.Promise.waitForAll_failure` | the *first* rejection in argument order is reported |

Three of the 29 bridging lemmas are also M2 because their right-hand sides are
`Queue.dequeue` or `Queue.enqueue`: `Writable.tick_dequeue_bridge`,
`Readable.runPullJob_dequeue_bridge`, `Transform.tick_dequeue_bridge`, plus
`Writable.attachSink_settled_jobs` and `Writable.acceptAnswer_jobs`.

**M1 — every other theorem of the 125.** In particular every law in
`WhatwgTest/WebIdl/ExceptionsContract.lean` is M1; none observes a settlement
order.

No theorem in this packet is stated under both masks, and no M1 theorem is
quoted as evidence for an ordering claim.

## 8. The axiom ceiling (R-11)

`propext`, `Quot.sound` and `Classical.choice`, for every declaration in the
four implementation modules and in the additive Streams surface.
`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and
the `native_decide` auxiliary axioms are forbidden, which forbids
`native_decide` and `bv_decide` in every proof. `sorry`, `partial` and `unsafe`
are rejected by `WhatwgTest/Audit/AxiomGate.lean`; no per-module exemption is
requested and none is needed.

`WhatwgTest/Ecma262/PromiseAxiomReport.lean` names exactly the 125 theorem
obligations and no others. A receipt that reaches `Classical.choice` is
reported as such and is inside the ceiling; an empty receipt is not required
and its absence is not a defect.

## 9. Preservation obligations

The whole of R-P12's argument is that an `abbrev` is a `@[reducible] def` and
therefore interchangeable at `rfl`. The obligations below make that checkable
rather than assumed. All of them are ascribed in the preservation half of
`WhatwgTest/Streams/PromiseBridge.lean`, which is **green today** and must stay
green.

1. Every existing Streams name the packet touches still elaborates with its old
   type: the three moved carriers and their eight constructors, the three
   `Writable` abbrevs, the twenty-one functions of section 4.4, and
   `Boundary.Exception` with its three constructors. 53 `#check` ascriptions.
2. Every named `rfl` receipt still closes by `rfl`. 13 `example`s re-derive:
   `UnitPromise ε = Readable.PromiseState Unit ε`,
   `SinkAnswer ε = Readable.PullAnswer ε`,
   `SinkReturn ε = Readable.PullReturn ε`, the three `…FromShared (…ToShared a) = a`
   roundtrips, `Writable.lookupPromise_eq`'s body, `markHandled_eq`'s body,
   `Transform.lookupPromise_eq`'s body, the three `subscriptionPromise_*`
   receipts, and `Boundary.Exception.ofRangeError_eq`.
3. Every derived instance is still found **through** the reducible abbrev:
   `DecidableEq` and `Repr` of `Readable.PromiseState Unit Nat`, `DecidableEq`
   of `Readable.PullAnswer Nat`, `Readable.PullReturn Nat`,
   `Writable.UnitPromise Nat` and `Writable.SinkJob Nat Nat`.
4. No `attribute [local simp]` set in `Readable/Reentrancy.lean`,
   `Writable/Lifecycle.lean`, `Transform/Runs.lean` or `Piping/Runs.lean`
   changes, and no function named in one of them becomes an `abbrev`.
5. No P4-P7 theorem statement and no Streams definition body changes. The
   packet's additions to `Whatwg/Streams/**` are the three re-pointed
   `abbrev`s, eight views and 29 bridging lemmas, and nothing else.
6. Every existing battery under `WhatwgTest/Streams/**` stays green, and the
   two `tick_job_fifo` corollaries and the three `runPullJob_*` receipts are
   re-derived from the general FIFO law through the three component bridges
   rather than re-proved from `tick`.

### 9.1 The expected declaration-count delta

Baseline, measured in this worktree at `e819a9f` with
`lake --wfail build WhatwgTest`: **184 modules and 12000 declarations**
(1477 in the Gates tooling tree), 213 jobs.

The packet adds **8 test modules** (the six batteries, the axiom report, and
`PromiseBridge`), so the module count moves 184 → 192. No implementation module
is added: all four promise modules already exist as declaration-free
bootstraps.

The authored named-declaration delta is **+203**, enumerated:

| Tree | Types | Functions and predicates | Theorems | Total |
| --- | ---: | ---: | ---: | ---: |
| `Whatwg/Ecma262/Jobs.lean` | 3 | 12 | 20 | 35 |
| `Whatwg/Ecma262/Promise.lean` | 12 | 22 | 44 | 78 |
| `Whatwg/WebIdl/Promise.lean` | 1 | 12 | 17 | 30 |
| `Whatwg/WebIdl/Exceptions.lean` | 3 | 5 | 15 | 23 |
| `Whatwg/Streams/**`, additive | 0 | 8 views | 29 bridging | 37 |
| **Total** | **19** | **59** | **125** | **203** |

Three existing Streams declarations change kind from `inductive` to `abbrev`
(`Readable.PromiseState`, `PullAnswer`, `PullReturn`), so their generated
constants — constructors, recursors, `noConfusion`, `toCtorIdx` and the
`deriving` instances — leave `Whatwg.Streams` and reappear verbatim under
`Whatwg.Ecma262.Promise`. They therefore contribute **zero** to the audit's
total, and the three abbrevs replace the three inductives one for one.

The audit's `declarations` figure counts generated constants as well as
authored ones, so the exact figure is

```text
12000 + 203 + (generated constants of the 19 new types)
```

and the landing record must publish the measured before-and-after pair
together with that arithmetic. A delta that is not accounted for by this table
plus the generated constants of exactly those 19 types is a defect: it means
something was added that this packet did not freeze.

## 10. The six decisions (R-P15), with recommendations

R-P15 leaves inventory decisions 6, 7, 8, 9, 11 and 12 to this breaker to
propose; the coordinator ratifies at freeze. Each is proposed here with the
inventory row cited, and each is already committed to by the frozen
ascriptions, so a different ratification is a contract change, not a builder
choice.

**D6 — collapsing `PullAnswer`/`PullReturn` into `PromiseState Unit ε`
(inventory decision 6; rows `E-02`, `E-03`, `E-04`..`E-06`).**
Recommendation: **do not collapse.** Keep three distinct carriers
(`State`, `Outcome`, `Returned`) and record the isomorphisms as bridging
lemmas. `PullAnswer` and `PullReturn` are isomorphic to `PromiseState Unit ε`
and to each other's `Option` but are not definitionally equal to them, and six
`rfl` receipts in `Whatwg/Streams/Writable/Laws.lean` depend on the current
shapes. Collapsing buys one fewer type and costs six frozen receipts and a
proof-script rewrite; the shapes also carry different meanings — a settled
outcome, a synchronous return, and a slot value — which the packet keeps
visible. WS-PROM-CE-001 is the attack.

**D7 — guard versus assertion for `settle` (inventory decision 7; row
`E-20`).** Recommendation: **the total guarded function**, with the
specification's assertion recovered as a separate side-condition lemma.
ES2026 `FulfillPromise` asserts the promise is pending; `Writable.settle`
makes a non-pending settle the identity and `settle_other` is a frozen receipt
for exactly that. `Table.settle_other` keeps that receipt derivable and
`Table.settle_assert` states, under the pending hypothesis, exactly what the
assertion guarantees. A partial or `Option`-valued settle would break
`settle_other` and would put a `none` into sixteen dependent theorems that do
not expect one. WS-PROM-CE-005 is the attack.

**D8 — one reaction list or two (inventory decision 8; row `E-29`, gap
`G-01`).** Recommendation: **two lists in `Whatwg.Ecma262.Promise`, with a
one-list view Streams instantiates.** ES2026 splits `[[PromiseFulfillReactions]]`
and `[[PromiseRejectReactions]]` and tags each reaction with `[[Type]]`;
`Transform.State.subscriptions` is one list with an answer-receiving handler.
`Reactions.add` registers both handlers under one id, so the two lists carry
the same ids in the same order (`Reactions.add_paired`), and
`Reactions.registered` — the fulfil list — is exactly the registration order
Streams records (`Transform.reactions_registered`). This gives ES2026 fidelity
without changing `Transform.Subscription`, which stays `keep`. One list would
make `[[Type]]` unrepresentable and would leave `G-01` open after a packet that
claims to close it. WS-PROM-CE-012 is the attack.

**D9 — the shape of the handled record (inventory decision 9; rows `E-15`,
`E-21`, gap `G-02`).** Recommendation: **a per-cell `handled : Bool` field in
the general table, with a bridging lemma to `id ∈ s.handled`.** Nothing reads
the bit today, so the cost of either shape is small now and large once a
rejection tracker exists; the per-cell field is what `slot.PromiseIsHandled`
says and what `HostPromiseRejectionTracker` will need. Streams keeps its
`handled : List Nat` field unchanged — changing it would touch every
`{ s with … }` update in `Writable/DefaultController.lean` — and
`Writable.handled_bridge` relates the two. WS-PROM-CE-019 is the attack.

**D10 — ownership of the wait-for-all rows (inventory decision 11; rows
`E-55`, `E-56`, gap `G-06`).** Recommendation: **land both rows in
`Whatwg.WebIdl.Promise` in this packet**, together with `wait for all` itself,
and defer `get a promise to wait for all` with a stated reason. The inventory
offers "land them with a note" or "defer both", and warns that a silent
deferral leaves two `generalize` rows with no owner. Since the seat instruction
puts `op.wait-for-all` in the packet, deferring the two rows that are its only
Streams match would be perverse: the predicate lands as `AllSettled` and
`allSettled` with the agreement lemma `E-56` lacks, the operation lands as
`waitForAll` with the ordered result and the first-rejection short-circuit
`G-06` names, and `op.waiting-for-all-promise` (354881..356058) with its
`[=Queue a microtask=]` step is the explicit remainder, out of scope in section
5.2. Calling the predicate `wait for all` would overclaim, so the two are
separate names with separate laws. WS-PROM-CE-018 is the attack.

**D11 — the timing of the Streams promise-slot re-disposition (inventory
decision 12).** Recommendation: **keep R-P5 as ruled; the re-disposition stays
at Q4.** The Q3 moves make `Readable.PromiseState` an `abbrev`, so the Streams
declaration still exists with its own owner and its census rows still describe
the Streams library; two censuses describing two libraries is the ruled
reading. Moving the re-disposition into Q3 would change the Streams
denominator inside the same slice that changes the Streams declarations, so a
regression in either would be attributable to both. Q3 lands with the Streams
census unchanged, exactly one slice changes the Streams denominator, and the
Q4 conversion receipts (`E-07`..`E-12`, already `rfl`) are what re-disposition
cites.

**D12 — a sixth decision the seat instruction folds into D6 but which the
ascriptions must answer separately: the arity of `Outcome`.** Recommendation:
**one parameter.** See section 4.2: a two-parameter outcome whose `fulfilled`
carries a value breaks every `.fulfilled` use site in `Whatwg/Streams/**`, and
the value-carrying settled outcome already exists as `Except reason value`.
This is recorded as a decision rather than an implementation detail because it
is the one place where R-P13's "two parameters" does not carry over from
`State` to its neighbours. WS-PROM-CE-004 is the attack.

Decisions 1 to 5 and 10 are already ruled by R-P13 and R-P14 and are not
reopened: two parameters on `State`, a free reason parameter, `Nat` identities
with `Ref` above them, a payload-polymorphic queue, `generalize` for every
`simp`-set function, and `Boundary.Exception` as its own sub-slice landed last.

## 11. Where this packet disagrees with the inventory

Recorded, not reopened. Each is a measurement corrected against the pinned
bytes or the generated censuses, and the packet freezes the corrected value.

| Fact | Inventory | This packet | Why |
| --- | --- | --- | --- |
| number of Web IDL simple exception kinds | "five of the seven simple exception kinds … are absent" (`E-59`, `G-09`) | **five kinds in total**, of which Streams models two, so **three** are added | `op.dfn-simple-exception` (194433..194721) lists exactly `EvalError`, `RangeError`, `ReferenceError`, `TypeError`, `URIError`, and the census has exactly five matching `type.*` rows |
| span of the exception-object definition | 664320..664612 (`E-59`) | **664320..664406**, `op.js-exception-objects` | the generated Web IDL census row |
| ES2026 record row ids | `record.promise-reaction-record`, `record.promise-capability-record`, `record.job-callback-record` (`E-29`, `E-44`, `G-03`) | `record.promisereaction-records`, `record.promisecapability-records`, `record.jobcallback-records` | R-P3 derives ids from clause ids; the generated census owns the spelling |
| ES2026 slot row ids | `slot.promise-state`, `slot.promise-result` (`E-01`) | `slot.PromiseState`, `slot.PromiseResult` | R-P3 preserves case |
| number of `generalize` functions named in an `attribute [local simp]` set | "eleven promise-layer functions" (decision 5) | **eleven** in the `Writable/Lifecycle.lean` set, of which **seven** are `generalize` and four are `keep`; **twenty-one** across all four sets, of which **fifteen** are `generalize` | section 4.4 enumerates them; the inventory's count is of one set, and the obligation applies to all four |
| `PromiseRef.local` (P8a rename-only class) | `PromiseRef.local` | `Ref.cell` | `local` is a Lean 4 keyword and cannot be a field name; the P8a draft was never elaborated, so the defect is latent there |

## 12. Acceptance conditions

1. Every frozen ascription elaborates with no edit to a statement, and every
   one cites an inventory row `E-01`..`E-74` with its reuse mode or a gap id
   `G-01`..`G-11` with the census rows it realizes. An ascription that cites
   neither, or that restates an inventoried declaration without naming its
   mode, is a defect under R-P12.
2. The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green
   before and after the builder's landing, including all 13 `example`s and all
   six `inferInstance` checks; every existing battery under
   `WhatwgTest/Streams/**` is green; no P4-P7 theorem statement, Streams
   definition body or `attribute [local simp]` set changed.
3. The root audit's module count is 192 and its declaration count is
   `12000 + 203 + g`, where `g` is the number of generated constants of the 19
   new types; the landing record publishes the measured pair and the
   arithmetic.
4. All 125 receipts in `WhatwgTest/Ecma262/PromiseAxiomReport.lean` are inside
   the R-11 ceiling; no forbidden axiom appears anywhere.
5. The general FIFO law of section 4.5 is proved, and both corollaries and the
   three `runPullJob_*` receipts are re-derived through the three component
   bridges, with their statements unchanged.
6. `Jobs.run_fifo` is proved under mask M2 as the realizer of
   `requirement.hostenqueuepromisejob.3`, with `FifoRequirement` stated as the
   specification, and its census row stays `absent`.
7. Every declaration in the four implementation modules that is not the target
   of a move or generalize row names the gap it closes; no gap row is closed
   silently, and every gap listed in section 5.2 is still open after the
   landing, recorded against its gap id.
8. Both censuses stay all-`absent`: no coverage block changes and no row goes
   `green`. The numerator modules
   `WhatwgTest/Audit/{WebIdl,Ecma262}/SpecCoverage.lean` are the builder's, and
   until one exists the `coverage` edge of `docs/PROMISE-DAG.md` stays
   `not-applicable` with the reason recorded there.
9. `known-red.txt` is empty again, `lake --wfail build Whatwg Gates`,
   `lake build`, `lake --wfail build WhatwgTest`, `lake exe vendorseal`,
   `lake exe citations` and both `lake exe census --standard …` gates pass, and
   independent review checks the inventory join in both directions.

## 13. Fence

Frozen breaker files, which the builder may not edit:

- `test/contracts/promise-first-packet.contract.md`
- `WhatwgTest/Ecma262/PromiseContract.lean`, `JobsContract.lean`,
  `PromiseLaws.lean`, `JobsLaws.lean`, `PromiseAxiomReport.lean`
- `WhatwgTest/WebIdl/PromiseContract.lean`, `ExceptionsContract.lean`
- `WhatwgTest/Streams/PromiseBridge.lean`
- `test/counterexamples/promise/ATTACKS.md`
- the declaration and statement rows of `docs/PROMISE-DAG.md`

Builder fence: `Whatwg/Ecma262/{Promise,Jobs}.lean`,
`Whatwg/WebIdl/{Promise,Exceptions}.lean`, the additive `abbrev`s, views and
bridging lemmas inside `Whatwg/Streams/**`, the two `SpecCoverage` numerator
modules, and the `known-red.txt` entries once each battery is green.
`Whatwg/Ecma262/Jobs.lean` must import only `Whatwg.Infra`;
`Whatwg/Ecma262/Promise.lean` imports it, which the root `Whatwg/Ecma262.lean`
needs no edit to accommodate.

This breaker edited no implementation module, no vendored byte, no generated
projection, no authored census input, no existing contract or battery, and not
`test/counterexamples/REGISTER.md`. Root imports and the `known-red.txt`
declarations are included with this packet, as the seat instruction requires;
the trust self-test checks that declaration in both directions.

## 14. Freeze receipt

Observed in this worktree at base `e819a9f`, Lean 4.33.1 from the unchanged
`lean-toolchain`, Windows x64.

`lake --wfail build Whatwg Gates` completes **164 jobs with exit code 0**.

`lake --wfail build WhatwgTest` at the base commit, before this packet's
modules were imported, completed **213 jobs with exit code 0** and printed

```text
Whatwg module and axiom gate: checked 184 modules and 12000 declarations
(1477 in the Gates tooling tree); semantic/test ceiling is [propext,
 Quot.sound, Classical.choice]; implementation ceiling (2 audit module(s),
 0 exact declaration(s), plus the Gates tree) additionally allows
 Classical.choice
```

That is the baseline of section 9.1.

With the packet's eight modules imported, `lake build WhatwgTest` fails, and
the failing targets are exactly the eight declared in
`test/fixtures/trust-gate/known-red.txt`. Lean's `maxErrors` is 100 and is read
once per file, so the complete diagnostic list for each module was collected
separately with `lake env lean -DmaxErrors=5000 <file>` and
`LEAN_NUM_THREADS=1`:

| Module | Exit | Diagnostics | Classes |
| --- | ---: | ---: | --- |
| `WhatwgTest.Ecma262.JobsContract` | 1 | 54 | 54 `lean.unknownIdentifier` |
| `WhatwgTest.Ecma262.JobsLaws` | 1 | 69 | 69 `lean.unknownIdentifier` |
| `WhatwgTest.Ecma262.PromiseContract` | 1 | 212 | 212 `lean.unknownIdentifier` |
| `WhatwgTest.Ecma262.PromiseLaws` | 1 | 232 | 230 `lean.unknownIdentifier`, 2 `` `sorryAx` is not a structure `` |
| `WhatwgTest.WebIdl.PromiseContract` | 1 | 149 | 149 `lean.unknownIdentifier` |
| `WhatwgTest.WebIdl.ExceptionsContract` | 1 | 145 | 145 `lean.unknownIdentifier` |
| `WhatwgTest.Streams.PromiseBridge` | 1 | 91 | 91 `lean.unknownIdentifier` |
| `WhatwgTest.Ecma262.PromiseAxiomReport` | 1 | 125 | 125 unknown constants, one per theorem obligation |

1077 diagnostics in total. There is no parse error, no import error, no type
mismatch and no failed instance synthesis anywhere. The two
`` `sorryAx` is not a structure `` errors are the downstream consequence of the
missing `ResolvingFunctions` type inside the two `{ f with alreadyResolved := true }`
updates of `callResolve_fresh` and `callReject_fresh`; they are the same class
the P4a and P5a packets recorded as "missing-structure errors caused by missing
types", and no synthetic error-recovery term is admitted as a proof.

The preservation half of `WhatwgTest/Streams/PromiseBridge.lean` is green: the
lowest line number carrying a diagnostic in that file is 371, the first line of
the bridging half, so all 53 preservation `#check`s, all 13 `example`s — every
one of which closes by `intros; rfl` — and all six `inferInstance` checks
elaborate today. That is the measurement acceptance condition 2 must reproduce
after the builder's landing.

The axiom report's 125 unknown constants equal, name for name, the 125 theorem
ascriptions of the six statement batteries, which is the receipt that the
report is neither short nor long.

Census cross-check performed at freeze, read-only, against the sealed bytes:
the five simple-exception `type.*` rows and the 32 base error-name `type.*`
rows were recounted from `generated/webidl-census.tsv` (39 `type` rows, minus
`type.idl-promise` and `type.idl-dom-exception`, minus the five simple kinds,
leaves exactly 32), and the four requirement bullets of section 5.1 were read
back from `vendor/ecma262-0248456c/spec.html` at their frozen spans. No
vendored or generated byte was changed.

No `lake` command was run in the main checkout by this seat, and no Lake or
reviewer process from this freeze remains running. All required graph edges
remain open except `targets`, which is not applicable, and `coverage`, which is
not applicable until a numerator module exists. This packet freezes what the
builder must prove; it claims no implementation, no coverage increase, no host
observation and no equivalence.
