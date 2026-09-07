# Promise extraction inventory

Status: authored 2026-09-06 by the extraction inventory seat, main checkout,
documents only. No `lake`, `lean` or `lsp` run; no `.lean` file, contract,
census input or generated projection changed.

Ruling R-P12 in `COORDINATION.md` requires that `Whatwg.Ecma262.Promise`,
`Whatwg.Ecma262.Jobs`, `Whatwg.WebIdl.Promise` and `Whatwg.WebIdl.Exceptions`
be seeded by extraction from what `Whatwg.Streams` already proves, never by
fresh design, and that this inventory exist before the Q3 breaker freezes
anything. Ruling DB-11 in `docs/DESIGN-BASIS.md` fixes the four modules'
owners and the import direction. This file is the row-by-row answer: what
Streams already has, what each declaration is in ES2026 or Web IDL terms,
where it should live, under which of R-P12's three reuse modes, how much
proof depends on it, and what exactly can break.

This file owns the inventory, the gap set, the move ordering, the P8a reuse
classification and the open decisions. It owns no plan slice, no disposition,
no census row and no Lean declaration. `docs/PROMISE-PACKAGE-PLAN.md` owns the
slices and cites this file by row id.

## Method and counting rule

The declaration set was found by the R-P12 grep

```
git grep -n -E '^(def|structure|inductive|abbrev|theorem|lemma) [A-Za-z0-9_.]*([Pp]romise|[Ss]ettle|[Jj]ob|notify|[Mm]ailbox|[Ss]ubscription)' -- 'Whatwg/Streams/**'
```

which returns 66 hits, and then widened by reading every module the ruling
names plus the three `Laws.lean`, the four `Runs`/`Reentrancy`/`Lifecycle`
composition modules, `Whatwg/Streams/Boundary/Exception.lean` and the six
`Whatwg/Streams/Semantics/*.lean` stubs. The widening adds every promise-layer
declaration whose name does not match the grep: the promise-identity supplies
(`nextPromise`, `nextRead`), the `promises`, `readPromises`, `handled`,
`internalPromises` slots, the `PullAnswer` / `PullReturn` / `SinkAnswer` /
`SinkReturn` eventual-settlement shapes, the `Event.settled` constructors and
their M1/M2 projections, `SinkJob`, `Transform.Job`, `runPullJob`, `runJob`
and the two `tick` job stages. The six `Semantics/*.lean` modules are
declaration-free stubs and contribute no row.

A **dependent theorem** is a `theorem` or `lemma` in `Whatwg/Streams/**` whose
block text — statement, proof and doc comment — mentions the name at a token
boundary. The population is 472 theorems in 14 files:

| File | theorems |
| --- | ---: |
| `Whatwg/Streams/Transform/Laws.lean` | 115 |
| `Whatwg/Streams/Writable/Laws.lean` | 109 |
| `Whatwg/Streams/Data/Queue.lean` | 64 |
| `Whatwg/Streams/Readable/Laws.lean` | 62 |
| `Whatwg/Streams/Piping/Laws.lean` | 44 |
| `Whatwg/Streams/Data/Strategy.lean` | 35 |
| `Whatwg/Streams/Readable/Reentrancy.lean` | 12 |
| `Whatwg/Streams/Readable/Step.lean` | 12 |
| `Whatwg/Streams/Boundary/Exception.lean` | 6 |
| `Whatwg/Streams/Data/DyadicSize.lean` | 4 |
| `Whatwg/Streams/Transform/Runs.lean` | 3 |
| `Whatwg/Streams/Readable/State.lean` | 2 |
| `Whatwg/Streams/Writable/Lifecycle.lean` | 2 |
| `Whatwg/Streams/Piping/Runs.lean` | 2 |

Two properties of the count are stated rather than smoothed. First, a name is
written unqualified inside its own namespace and qualified outside it, so the
per-file split disambiguates the three `settle`, the three `tick`, the two
`lookupPromise` and the two `settlementTrace`; each row states which files
carry which. Second, the count is textual, so it is an **upper bound** where a
doc comment uses the word in prose (one such artefact is flagged in row E-33)
and a **lower bound** where a theorem depends on a definition only through an
`attribute [local simp]` set without naming it. Four modules carry such sets:

| File | promise-layer names in its `attribute [local simp]` set |
| --- | --- |
| `Whatwg/Streams/Readable/Reentrancy.lean` | `returnPull`, `continuePull`, `settlementTrace`, `chunksOfSettlements`, `observeM1`, `Boundary.Exception.ofRangeError` |
| `Whatwg/Streams/Writable/Lifecycle.lean` | `tick`, `attachSink`, `acceptAnswer`, `operationPhase`, `setOperationPhase`, `lookupPromise`, `freshPromise`, `settle`, `markHandled`, `ensureReadyRejected`, `updateBackpressure`, `visibleEvents`, `observeOrdered` |
| `Whatwg/Streams/Transform/Runs.lean` | `lookupPromise`, `freshInternal`, `subscriptionPromise`, `notify`, `subscribe`, `settle`, `runJob`, `tick`, `Readable.acceptPullAnswer`, `Readable.reactPull`, `Readable.runPullJob`, `Readable.settlementTrace`, `Writable.tick`, `Writable.attachSink`, `Writable.acceptAnswer`, `Writable.lookupPromise`, `Writable.freshPromise`, `Writable.settle`, `Writable.markHandled`, `Writable.unitPromiseToShared`, `Writable.sinkAnswerFromShared` |
| `Whatwg/Streams/Piping/Runs.lean` | `allWrittenSettled`, `lookupReturn`, `Writable.tick`, `Writable.attachSink`, `Writable.acceptAnswer`, `Writable.lookupPromise`, `Writable.freshPromise`, `Writable.settle`, `Writable.markHandled`, `Writable.unitPromiseToShared`, `Writable.sinkAnswerFromShared`, `Readable.chunksOfSettlements`, `Boundary.Exception.ofRangeError` |

Those four sets are the single largest technical risk in the lane and are
treated as such in the risk column and in decision 5.

Specification citations use the census row id where the surveys propose one
and the byte span of the pinned source otherwise: ES2026 spans are into
`vendor/ecma262-0248456c/spec.html` (SHA-256
`ce7bc30174061fd8d212270b81cf6511661180c1e174f6911d10ced0581527b0`), Web IDL
spans into `vendor/whatwg-webidl-a652053f/index.bs` (SHA-256
`3c401f1eade4b56fc674e9bb86344d452f8854433bc48f0e28e354280d43dc83`). Row ids
for Web IDL operations are given in the R-P8 `algorithmNameFirst` spelling
with the current-ladder spelling beside it where the two differ.

## Reuse modes

R-P12's three modes are used exactly as the ruling defines them.

- **move** — the definition relocates to its target module and Streams keeps
  an `abbrev` at the old name, so every dependent is unchanged by definitional
  equality. Used only for types.
- **generalize** — the Streams definition becomes an instance of a general
  one, with a bridging lemma, and its theorems are re-derived from the general
  law rather than re-proved. Used for every function, slot and law.
- **keep** — stream-specific; it stays where it is. A `keep` row is still
  inventoried, because R-P12 makes an unnamed duplicate a defect: a Q3
  ascription that re-states a `keep` row is a defect just as much as one that
  re-states a `move` row.

Totals over the 74 rows below: **6 move, 28 generalize, 40 keep.**

## File legend

| Tag | Path |
| --- | --- |
| RS | `Whatwg/Streams/Readable/State.lean` |
| RC | `Whatwg/Streams/Readable/DefaultController.lean` |
| RD | `Whatwg/Streams/Readable/DefaultReader.lean` |
| RT | `Whatwg/Streams/Readable/Step.lean` |
| RL | `Whatwg/Streams/Readable/Laws.lean` |
| RE | `Whatwg/Streams/Readable/Reentrancy.lean` |
| WS | `Whatwg/Streams/Writable/Stream.lean` |
| WB | `Whatwg/Streams/Writable/Backpressure.lean` |
| WC | `Whatwg/Streams/Writable/DefaultController.lean` |
| WW | `Whatwg/Streams/Writable/DefaultWriter.lean` |
| WL | `Whatwg/Streams/Writable/Laws.lean` |
| WF | `Whatwg/Streams/Writable/Lifecycle.lean` |
| TS | `Whatwg/Streams/Transform/Stream.lean` |
| TB | `Whatwg/Streams/Transform/Backpressure.lean` |
| TC | `Whatwg/Streams/Transform/DefaultController.lean` |
| TP | `Whatwg/Streams/Transform/Step.lean` |
| TO | `Whatwg/Streams/Transform/Observation.lean` |
| TL | `Whatwg/Streams/Transform/Laws.lean` |
| TR | `Whatwg/Streams/Transform/Runs.lean` |
| PR | `Whatwg/Streams/Piping/Requirements.lean` |
| PT | `Whatwg/Streams/Piping/PipeTo.lean` |
| PS | `Whatwg/Streams/Piping/Step.lean` |
| PL | `Whatwg/Streams/Piping/Laws.lean` |
| PU | `Whatwg/Streams/Piping/Runs.lean` |
| BE | `Whatwg/Streams/Boundary/Exception.lean` |

Proposed target names (`Ecma262.Promise.State`, `Ecma262.Jobs.Queue` and the
rest) are this seat's proposals. The Q3 breaker fixes the spellings; the rows
fix the content.

## A. Promise state and outcome carriers

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-01 | `Readable.PromiseState (α ε)` (RS) | a first-order fusion of the two instance slots `[[PromiseState]]` (`slot.promise-state`, 2744957..2745252) and `[[PromiseResult]]` (`slot.promise-result`, 2745263..2745619) into one tagged value; the three tags are the clause's `~pending~ / ~fulfilled~ / ~rejected~` | `Ecma262.Promise.State` | move | 2 direct (WL, as `Readable.PromiseState`); 66 through its carriers (PL 7, PU 2, RL 10, TL 11, TR 3, WL 31, WF 2) | the general type needs a second type parameter for the reason (Streams fixes it to `Boundary.Exception ε`), so the Streams `abbrev` must be a partial application, not a rename — see decisions 1 and 2. `deriving DecidableEq, Repr` must survive as `[DecidableEq value] [DecidableEq reason]` instances found *through* the abbrev, or `decide` and the `simp` normal forms in WL change. `Writable.UnitPromise` is an `abbrev` over it and `unitPromise_eq … := rfl` (WL) is a definitional-equality receipt that must stay `rfl` |
| E-02 | `Readable.PullAnswer (ε)` (RS) | the settled outcome a foreign callback's promise delivers: the `_value_` argument of `FulfillPromise` (`sec-fulfillpromise`, 2695419..2696230) or the `_reason_` of `RejectPromise` (`sec-rejectpromise`, 2699323..2700252), with the value fixed to unit | `Ecma262.Promise.Outcome` | move | 18 (RL 4, RT 1, TL 11, WL 2) | it is the unit-valued case of a general two-parameter outcome; `Writable.SinkAnswer` is an `abbrev` over it with a `rfl` receipt (`sinkAnswer_eq`, WL). Collapsing it into E-01 is refused — see decision 6 |
| E-03 | `Readable.PullReturn (ε)` (RS) | the promise handle a foreign callback returns *before* any reaction runs: `pending`, or already settled. In ES2026 terms the `[[PromiseState]]` of the returned promise observed at return time | `Ecma262.Promise.Returned` | move | 10 (RL 2, RT 1, TL 5, WL 2) | isomorphic to `PromiseState Unit ε` but not definitionally equal; three `rfl` receipts (`sinkReturn_eq`, `sinkReturnToShared_eq`, `sinkReturn_roundtrip`, WL) depend on the current shape. Decision 6 |
| E-04 | `Writable.UnitPromise (ε)` — `abbrev` (WS) | Web IDL `Promise<undefined>`, the type every writable ready/closed/write-request cell has (`idl-promise`, 252146..252819; `hostOnly` under R-P4) | `Ecma262.Promise.State` instance | move | 7 (WL 5, PL 2) | already an `abbrev`; the move re-points it and must keep `unitPromise_eq` and `unitPromise_roundtrip` `rfl` |
| E-05 | `Writable.SinkAnswer (ε)` — `abbrev` (WS) | as E-02, at the sink boundary | `Ecma262.Promise.Outcome` instance | move | 9 (WL) | as E-04 |
| E-06 | `Writable.SinkReturn (ε)` — `abbrev` (WS) | as E-03, at the sink boundary | `Ecma262.Promise.Returned` instance | move | 8 (WL) | as E-04 |
| E-07 | `Writable.unitPromiseToShared` (WS) | identity view; no ES2026 counterpart | stays in Streams | keep | 3 (WL) + 2 (TL, qualified) | it is already the DB-11 conversion receipt Q4 asks for; after E-01 and E-04 land it must still be `rfl`. Named in the TR and PU `simp` sets |
| E-08 | `Writable.unitPromiseFromShared` (WS) | identity view | stays in Streams | keep | 3 (WL) | as E-07 |
| E-09 | `Writable.sinkAnswerToShared` (WS) | identity view | stays in Streams | keep | 3 (WL) | as E-07 |
| E-10 | `Writable.sinkAnswerFromShared` (WS) | identity view | stays in Streams | keep | 3 (WL) + 1 (TL, qualified) | named in the TR and PU `simp` sets and used inside `Transform.notify` |
| E-11 | `Writable.sinkReturnToShared` (WS) | identity view | stays in Streams | keep | 3 (WL) | as E-07 |
| E-12 | `Writable.sinkReturnFromShared` (WS) | identity view | stays in Streams | keep | 3 (WL) | as E-07 |

## B. Promise tables and identity supplies

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-13 | `Writable.State.promises : List (Nat × UnitPromise ε)` (WS) | an allocation of promise identities: one entry per promise object the writable algorithms create, keyed by the identity the model uses in place of an object reference. There is no ES2026 counterpart *slot*; the counterpart is the existence of promise objects with `[[PromiseState]]`/`[[PromiseResult]]` (`table-internal-slots-of-promise-instances`, 2744540..2746673) | `Ecma262.Promise.Table` | generalize | 5 (WL) | an association list, not a map; `freshPromise` appends and never removes, and three theorems (`freshPromise_pending/_fulfilled/_rejected`, WL) state the append shape verbatim. A general table with a different representation breaks them; a general table that is *also* `List (Nat × State …)` keeps them by `rfl` |
| E-14 | `Writable.State.nextPromise : Nat` (WS) | the promise-identity supply; ES2026 has no cursor because it has object identity | `Ecma262.Promise.Table` cursor | generalize | 4 (WL) | `Writable.initial` seeds it as `promiseSeed + 2` and P6 and P7 both rely on the exact seeded values (`Transform.initial`, `Piping` run witnesses fix ids 0..5). Any change of allocation order changes those frozen witnesses. Decision 3 |
| E-15 | `Writable.State.handled : List Nat` (WS) | `[[PromiseIsHandled]]` (slot row, 2746322..2746637) as a set of identities rather than a per-cell Boolean | `Ecma262.Promise.Table` field | generalize | 2 (WL) | nothing reads it today: it is written by `markHandled` and never consulted, so a per-cell Boolean is available at no proof cost — but it changes `State`'s field list and every `{ s with … }` update in WC. Decision 9 |
| E-16 | `Writable.State.readyPromise : Nat` (WS) | an identity reference to the writer's `[[ReadyPromise]]`; Streams-specific | stays in Streams | keep | 3 (WL) | replaced, not settled, by `updateBackpressure`; the replacement discipline is stream-specific |
| E-17 | `Writable.State.closedPromise : Nat` (WS) | identity reference to the writer's `[[ClosedPromise]]` | stays in Streams | keep | 1 (WL) | — |
| E-18 | `Writable.lookupPromise` (WS) | reading `[[PromiseState]]`/`[[PromiseResult]]` of the promise an identity names | `Ecma262.Promise.Table.get` | generalize | 30 (WL 12, WF 2, PL 7, PU 2, TL 4, TR 3) | named in all four `attribute [local simp]` sets. `lookupPromise_eq` (WL) states the `find?`/`map Prod.snd` body verbatim, and the P7 `WritesSettled` / `allWrittenSettled` predicates (E-55, E-56) are written directly over it. Name clash with `Transform.lookupPromise` (E-25) |
| E-19 | `Writable.freshPromise` (WS) | `NewPromiseCapability(%Promise%)` (`sec-newpromisecapability`, 2696238..2698770) restricted to the intrinsic constructor, followed immediately by `FulfillPromise`/`RejectPromise` when the caller supplies a settled outcome. Web IDL "a new promise" (`op.a-new-promise`, 347604..347946, 18 Streams invocations), "a promise resolved with" (`op.a-promise-resolved-with`, 347948..348631, 46) and "a promise rejected with" (`op.a-promise-rejected-with`, 348633..349214, 46) are its three call shapes | `Ecma262.Promise.Table.fresh` | generalize | 22 (WL 16, PL 2, TL 4) | it also appends a `.settled` **trace event** in two of its three branches, so the general function must either be trace-parameterized or the Streams instance must wrap it; the three `freshPromise_*` receipts fix the exact trace suffix. Named in all four `simp` sets |
| E-20 | `Writable.settle` (WS) | `FulfillPromise` (2695419..2696230) and `RejectPromise` (2699323..2700252), with the specification's *assertion* that the promise is pending replaced by a guard that makes a non-pending settle the identity. Web IDL "resolve" (`op.resolve`, 349216..349783, 35 invocations) and "reject" (`op.reject`, 349785..350073, 23) | `Ecma262.Promise.Table.settle` | generalize | 16 (WL 13, PL 2, TL 1) | the guarded-versus-asserted difference is a semantic choice the general definition must make once — decision 7. Two-way name clash: `Transform.settle` (E-33) is a *different* operation that additionally notifies subscriptions. Named in all four `simp` sets |
| E-21 | `Writable.markHandled` (WS) | Web IDL "mark as handled" (`op.mark-a-promise-as-handled`, 356060..356713), which is step-for-step "set `[[PromiseIsHandled]]` to true". R-P4 keeps it an honest uncovered denominator row because the Streams *source* invokes it 0 times — but the Streams *model* already implements it, at two call sites in WB and WC | `Ecma262.Promise.Table.markHandled` | generalize | 7 (WL 5, PL 2) | the one row in the lane where the model is ahead of the census: Q3 must not declare `mark as handled` absent from Streams. Its idempotence is stated only as `markHandled_eq` (WL), never as a law |
| E-22 | `Readable.State.readPromises : List (Nat × PromiseState (ReadResult α) ε)` (RS) | a second, independently keyed promise table, over a non-unit value type | `Ecma262.Promise.Table` at a different value parameter | generalize | 10 (RL) | proves the general table must be polymorphic in the value, not fixed to unit. It has no `lookup`/`fresh`/`settle` operations of its own: every update is an inline `List.map` inside RC and RD, so the generalization is a *refactor of five inline updates*, not a re-pointing. This is the largest hidden cost in the inventory |
| E-23 | `Readable.State.nextRead : Nat` (RS) | the read-promise identity supply | `Ecma262.Promise.Table` cursor | generalize | not separately counted; every RL read law fixes its value | P7 `RecordAllowed` requires `a.source.nextRead = b.source.nextRead` on every protocol record, so the supply is observable in a frozen P7 statement |
| E-24 | `Readable.State.closedPromise : PromiseState Unit ε` (RS) | the stream's closed promise stored **by value**, not by identity — the one promise in the model with no allocated `Nat` | stays in Streams | keep | 4 (RL) | flagged in the held P8a design as a residual: a global adapter needs an address for it. Do not give it an identity in Q3; that is a P8 change with M2 consequences |
| E-25 | `Transform.lookupPromise` (TB) | a view of the writable table through the transform state; no ES2026 counterpart | stays in Streams | keep | 13 (TL 10, TR 3) | pure adapter (`(Writable.lookupPromise …).map Writable.unitPromiseToShared`); after E-18 it must still be `rfl`-provable as `lookupPromise_eq` (TL) states |
| E-26 | `Transform.freshInternal` (TB) | allocating an internal promise nobody outside the transform observes | stays in Streams | keep | 7 (TL) | its four receipts (`freshInternal_eq/_old/_new/_identity`, TL) unfold `Writable.freshPromise` and `Writable.lookupPromise` inside their proofs, so E-18 and E-19 must leave those two unfoldable |
| E-27 | `Transform.State.internalPromises : List Nat` (TS) | the identities whose settlements the M2 projection hides; no ES2026 counterpart | stays in Streams | keep | 2 (TL) | consumed by `visibleEvent` (E-74); it is an observation-scope device, not promise state |
| E-28 | `Transform.State.backpressurePromise : Nat` (TS) | identity reference to the backpressure cell | stays in Streams | keep | 2 (TL) | — |

## C. Reactions, registration and settlement notification

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-29 | `Transform.Subscription (α)` (TS) | a PromiseReaction Record (`record.promise-reaction-record`, clause 2690445..2692671) as a first-order descriptor: the captured promise identity plus the handler tag. `State.subscriptions` is the reaction *list* that ES2026 splits into `[[PromiseFulfillReactions]]` (2745630..2745966) and `[[PromiseRejectReactions]]` (2745977..2746311) | `Ecma262.Promise.Reaction` | generalize | 6 (TL) | Streams has **one** list and a handler that receives the answer; ES2026 has two lists and a `[[Type]]` tag (2691815..2692138). Generalizing to two lists changes `subscribe`'s and `settle`'s shape, so decision 8 must be answered before this row moves. `deriving Repr` only — no `DecidableEq` — and the general type must not gain one silently, or `Transform.State` stops being `Repr`-only in the same way |
| E-30 | `Transform.subscriptionPromise` (TS) | `[[Capability]]`-side accessor: the identity captured at registration, independent of later slot replacement | `Ecma262.Promise.Reaction.promise` | generalize | 8 (TL) | three `rfl` receipts, one per constructor; a general accessor over a differently shaped reaction record loses them |
| E-31 | `Transform.subscribe` (TB) | Web IDL "react" (`op.react` under R-P8; current ladder `op.dfn-perform-steps-once-promise-is-settled`; 350075..352408; 8 direct Streams invocations and the primitive under "upon fulfillment" 352410..352816 and "upon rejection" 352818..353237), which bottoms out in `PerformPromiseThen` steps 8–10 (`sec-performpromisethen`, 2740635..2743669): pending appends the reaction, fulfilled or rejected enqueues a reaction job at once | `WebIdl.Promise.react` | generalize | 7 (TL) | the closest existing match to a Q3 deliverable anywhere in the repository, and the reason Q3 must be extraction-seeded. Its four branch receipts (`subscribe_pending/_fulfilled/_rejected/_missing`, TL) are exactly `PerformPromiseThen`'s case split. It returns `Option` because a missing cell has no transition, where `PerformPromiseThen` is total; the general operation must decide which. Named in the TR `simp` set |
| E-32 | `Transform.notify` (TB) | `NewPromiseReactionJob` (`sec-newpromisereactionjob`, 2702885..2705591) applied to one reaction, plus the `HostEnqueuePromiseJob` that follows it | `Ecma262.Promise` reaction-job creation | generalize | 6 (TL) | dispatches into the *canonical component* (`Readable.acceptPullAnswer`, `Writable.acceptAnswer`) before queueing its tag, so the general version is the queueing half only and the dispatch stays in Streams. Named in the TR `simp` set |
| E-33 | `Transform.settle` (TB) | `FulfillPromise`/`RejectPromise` followed by `TriggerPromiseReactions` (`sec-triggerpromisereactions`, 2700260..2701212), whose entire content is "enqueue a reaction job for each reaction, in list order" | `Ecma262.Promise.Table.settleAndTrigger` | generalize | 8 (TL); the RE hit reported by a bare-name scan is the word "settle" in a doc comment, not a dependency | it folds `notify` over the filtered subscription list with `foldlM` in `Option`, so its order law is where the once-only, registration-order requirement lives — but that law is **not stated today**: only `settle_pending` and `settle_other` exist. A general `TriggerPromiseReactions` with an order law is therefore new content, not extraction, and must be declared as such |
| E-34 | `Transform.Reaction (α)` (TS) | the thirteen ES2026 Abstract Closures as first-order descriptors — a tag plus the capture list the source states explicitly — which is the representation rule the Q3 plan already commits to | stays in Streams | keep | 3 (TL) | the *discipline* generalizes, the *constructors* do not: `write`, `transform` and `adopt` are transform-stream handler bodies |
| E-35 | `Transform.Completion` (TS) | resolving a promise with another promise: the adoption branch of `CreateResolvingFunctions` (`sec-createresolvingfunctions`, 2692679..2695411), restricted to an internal identity rather than an arbitrary thenable | stays in Streams | keep | 8 (TL) | it is adoption *without* the thenable job (gap G-05); a Q3 ascription must not present it as adoption |
| E-36 | `Writable.OperationPhase` (WS) | no ES2026 counterpart: the model's stand-in for "the reaction is registered" (`awaiting`) versus "its job is queued" (`queued`), because the writable half has no reaction list | stays in Streams | keep | 14 (WL) | the phase is what `acceptAnswer` and `attachSink` guard on, so if E-29's reaction list is generalized into the writable half these 14 receipts change. Keep the phase; do not unify it with `ObserverPhase` from the P8a draft in Q3 |
| E-37 | `Writable.attachSink` (WC) | `PerformPromiseThen` steps 8–10 again, at the sink boundary: a pending return registers (`.awaiting`), a settled return enqueues the job immediately | `WebIdl.Promise.react` instance | generalize | 6 (WL 4, PL 2) | second, independently written instance of the same ES2026 case split as E-31 — the strongest evidence in the inventory that one general operation exists. It also clears the algorithm slots for close and abort in the same step, which the general operation must not do. Named in the WF, TR and PU `simp` sets |
| E-38 | `Writable.acceptAnswer` (WC) | admitting a foreign settlement for an already-registered reaction: `FulfillPromise`/`RejectPromise` on the callback's promise, then `HostEnqueuePromiseJob` | `WebIdl.Promise` settle-and-react | generalize | 7 (WL 4, PL 2, TL 1) | guarded by `operationPhase … = some .awaiting`, i.e. by E-36. Named in the WF, TR and PU `simp` sets |
| E-39 | `Readable.acceptPullAnswer` (RC) | the same admission at the pull boundary | stays in Streams | keep | 4 (RL 2, RT 1, TL 1) | third instance of the same shape, but written over `pullAwaiting : Bool` rather than a phase; unifying it is a refactor with no proof saving |
| E-40 | `Readable.reactPull` (RC) | the two handlers `call pull if needed` registers, i.e. the `_onFulfilled_`/`_onRejected_` arguments of `PerformPromiseThen` as first-order bodies | stays in Streams | keep | 3 (RL) | the bodies are stream-specific (`pullAgain` bookkeeping, `error`) |
| E-41 | `Readable.State.pullAwaiting : Bool` (RS) | "a reaction is registered on the pull promise" | stays in Streams | keep | counted with E-39 | — |
| E-42 | `Writable.ensureReadyRejected` (WB) | settle-if-pending, else allocate a fresh already-rejected promise, then mark it handled — a Web IDL "a promise rejected with" (346..) plus "mark as handled" composite | stays in Streams | keep | 4 (WL) | its second branch is the only place `markHandled` is applied to a *fresh* cell; a general `markHandled` must accept that ordering |
| E-43 | `Writable.updateBackpressure` (WB) | replacing a settled ready promise with a new pending one | stays in Streams | keep | 6 (WL) | replacement never overwrites old cells; that retention property is what E-13's append-only table buys |

## D. Job queues and job records

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-44 | `Writable.SinkJob (α ε)` (WS) | a Job Abstract Closure as a first-order descriptor: the `NewPromiseReactionJob` (2702885..2705591) closure reduced to its capture list (`kind`, `request`, `answer`). The ES2026 carrier is the JobCallback Record (`record.jobcallback-records`, clause 628436..630247, fields at 629684..629930 and 629941..630193) | `Ecma262.Jobs.Job` payload instance | generalize | 3 (WL 2, TL 1) | `deriving DecidableEq, Repr` is load-bearing: `Transform.runJob` decides `first.kind = .write ∧ first.request = request`, and the P8a draft's `takeSinkHead` compares `token.kind = .sink payload.kind payload.request`. A general job record that loses `DecidableEq` breaks both |
| E-45 | `Writable.State.jobs : List (SinkJob α ε)` (WS) | the per-component FIFO job queue that realizes `HostEnqueuePromiseJob` (`hook.host-enqueue-promise-job`, clause 633447..635836), which R-P5 rules a `requirement` rather than a `foreignBoundary` | `Ecma262.Jobs.Queue` | generalize | 4 (WL, bare `jobs`) | it is a plain `List` appended at the tail and consumed at the head; the general queue must be the same `List` or `tick_job_fifo` stops being `rfl` |
| E-46 | `Writable.tick`'s empty-control job stage, with `tick_job_fifo` and `tick_no_job` (WC, WL) | the realizer of the ordering bullet at 634739..634841, digest `6c5b7796efb44a87c971febe7c06bac4a74f18154b8ccd99cf1ac693d8b4dd65` — "Jobs must run in the same order as the HostEnqueuePromiseJob invocations that scheduled them" — combined with the run condition that the execution context stack be empty (bullet at 625769..626250), modelled as `control = []` | `Ecma262.Jobs.Queue.runOldest` | generalize | 48 textual (WL 41, TL 4, PL 3) plus 4 that depend only through the WF and PU `simp` sets | the largest blast radius in the inventory. The queue is **one branch of a twenty-branch `tick`**, so this is an extraction of a branch, not a relocation of a function, and `tick_job_fifo`'s statement is an equation about the whole `tick`, not about a queue. The honest general law is `Queue.runOldest`'s equation plus a Streams bridging lemma that `tick` reduces to it when `control = []` |
| E-47 | `Writable.Control.react` (WS) | the "currently running job" marker; ES2026's "only one Job may be actively undergoing evaluation" (626257..626350) and "run to completion" (626357..626479) | stays in Streams | keep | counted under E-46 | the general activation state is the P8a draft's `Active` (row P-07); do not introduce a second one in Q3 |
| E-48 | `Readable.State.jobs : List (PullAnswer ε)` (RS) | a second FIFO job queue, whose payload is a bare settled outcome rather than a job record | `Ecma262.Jobs.Queue` at a different payload | generalize | 5 (RL 4, RT 1) | proves the general queue must be payload-polymorphic (decision 4): the three Streams queues carry `PullAnswer`, `SinkJob` and `Transform.Job` |
| E-49 | `Readable.runPullJob` (RC) | dequeue-and-run under the empty-stack condition: `s.frames = []` is the Readable spelling of "there is no running execution context" (625769..626250) | `Ecma262.Jobs.Queue.runOldest` | generalize | 4 (RL 3, TL 1) | its three receipts `runPullJob_suspended`, `runPullJob_empty` and `runPullJob_cons` (RL) are precisely the general dequeue laws and re-derive from them without re-proof. Named in the TR `simp` set |
| E-50 | `Transform.Job (α ε)` (TS) | a third job payload: coupled-component tags plus a transform reaction | `Ecma262.Jobs.Job` payload instance | generalize | 3 (TL) | `deriving Repr` only, unlike E-44; a general job record that derives `DecidableEq` unconditionally cannot be instantiated at this payload, because `Reaction` is `Repr`-only |
| E-51 | `Transform.runJob` (TP) | running one job through its owning component | `Ecma262.Jobs` run step | generalize | 5 (TL) | its `.writable` branch re-checks that the writable mailbox head matches the token; that check is the token/mailbox correspondence the P8a draft calls CFG-TOKENS and it is stream-specific. Named in the TR `simp` set |
| E-52 | `Transform.State.jobs : List (Job α ε)` (TS) | the third FIFO queue | `Ecma262.Jobs.Queue` | generalize | 7 (TL) | — |
| E-53 | `Transform.tick`'s job stage, with `tick_job_fifo` and `tick_no_job` (TP, TL) | the same ordering requirement as E-46, at the coupled level, with a three-way empty-stack guard (`control`, `writable.control`, `readable.frames` all empty) | `Ecma262.Jobs.Queue.runOldest` | generalize | 14 (TL) | the three-part guard is the clearest statement in the repository of "the execution context stack is empty", and it is stated only as a hypothesis of `tick_job_fifo`, never as a named condition. Named in the TR `simp` set |
| E-54 | `Transform.Control.settle` (TS) | a deferred settlement continuation | stays in Streams | keep | 13 with `setBackpressure` and `unblockWrite` (TL) | — |

## E. Wait-for-all-shaped predicates

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-55 | `Piping.WritesSettled` (PR) | the settlement condition of Web IDL "wait for all" (`op.wait-for-all`, 353239..354879), specialized to unit promises and stated as a `Prop` over the writable table. `wait for all` is reached from Streams exactly once, through "get a promise to wait for all" (`op.waiting-for-all-promise`, 354881..356058), in the pipe-to shutdown path | `WebIdl.Promise` settled-predicate | generalize | 4 (PL) | it is the *predicate*, not the *operation*: it returns no promise, keeps no result list and queues no microtask (gap G-06). A Q3 ascription that calls it `wait for all` overclaims |
| E-56 | `Piping.allWrittenSettled` (PT) | the `Bool` decision procedure for E-55 | `WebIdl.Promise` settled-predicate, decidable form | generalize | 4 (PL) | the `Prop`/`Bool` pair has no stated agreement lemma today; the general operation should have one, which is new content |
| E-57 | `Piping.lookupReturn` (PT) | recovering the promise identity a call returned, by searching the writable trace | stays in Streams | keep | 4 (PL) | a trace search, not a table operation; it exists because the model has no call-to-promise binding. Named in the PU `simp` set |
| E-58 | `Piping.Snapshot.abortPromise` / `State.abortPromise` (PR, PT) | the identity of the promise the abort action returned | stays in Streams | keep | 5 (PL) | — |

## F. Exceptions

| Row | Declaration (file) | ES2026 / Web IDL reading | Target | Mode | Dependents | Risk |
| --- | --- | --- | --- | --- | --- | --- |
| E-59 | `Boundary.Exception (ε)` (BE) | Web IDL simple exceptions ("create a simple exception", `op.to-create-a-simple-exception`, 664734..665486; the exception-object definition on the `js-exception-objects` heading, 664320..664612), restricted to `RangeError` and `TypeError`, each carrying an allocation identity, plus a `foreign` escape for host reasons | `WebIdl.Exceptions.Simple` | generalize | **69** (WL 29, TL 17, RL 11, PL 4, BE 3, RT 2, PU 2, WF 1) | the largest dependent set in the lane, and the row most likely to be underestimated. Web IDL simple exceptions have **no allocation identity**; the Streams constructors carry a `Nat` precisely so that two RangeErrors created by nested size callbacks are distinguishable (`nested_invalid_sizes_fresh_errors`, RE). A general Web IDL exception type without that identity cannot host this row. Five of the seven simple exception kinds and the whole `DOMException` name table are absent (gap G-09) |
| E-60 | `Boundary.Exception.ofRangeError` (BE) | embedding P3's error kind at the identity the consuming calculus allocated (ruling P3-R2) | stays in Streams | keep | 5 with `toRangeError` (BE 4, RL 1) | named in the RE and PU `simp` sets |
| E-61 | `Boundary.Exception.toRangeError` (BE) | the retraction that forgets identity | stays in Streams | keep | counted with E-60 | its three receipts are the existing-type disposition for P3's `RangeError`; they are unaffected by E-59 only if the general type keeps the two constructors definitionally |

## G. Settlement observation (DB-04 M2)

Every row in this group is `keep`. Under DB-04, M2 is "M1 plus the full order
of promise settlements observable by the consumer", and DB-04 is a repository
ruling about claim scope, not an ES2026 or Web IDL object. Nothing in this
group belongs in `Whatwg.Ecma262` or `Whatwg.WebIdl`, and a Q3 ascription that
re-states one of these rows in either library is a defect under R-P12.

| Row | Declaration (file) | Reading | Mode | Dependents |
| --- | --- | --- | --- | --- |
| E-62 | `Readable.Settlement (α ε)` (RS) | the DB-04 M2 alphabet of the readable half: the closed promise and the identified read promises | keep | 9 (RL 5, RE 2, RT 1, TL 1) |
| E-63 | `Readable.settlementTrace` (RS) | the M2 settlement-order projection | keep | 6 (RL 2, RE 4) |
| E-64 | `Readable.chunksOfSettlements` (RS) | the M1 chunk sequence read off the settlement order | keep | 3 (RL) |
| E-65 | `Readable.Event.settled` (RS) | the settlement constructor of the readable local alphabet | keep | counted with E-62 |
| E-66 | `Readable.VisibleEvent.settlement` (RS) | the consumer-visible settlement | keep | counted with E-62 |
| E-67 | `Readable.M2Observation` (RS) | the local M2 record | keep | 0 direct |
| E-68 | `Readable.observeM1` / `observeM2` (RS) | the two local mask projections | keep | 12 and 3 (RL, RE, TL, TR) |
| E-69 | `Writable.Event.settled` (WS) | settlement event keyed by request identity | keep | 3 qualified (PL 2, PU 1) |
| E-70 | `Writable.VisibleEvent.settled` (WS) | consumer-visible settlement | keep | 0 direct |
| E-71 | `Writable.settlementTrace` (WS) | the identified settlement order | keep | 2 (WL) |
| E-72 | `Writable.visibleEvents` / `observeOrdered` (WS) | the local ordered candidate view | keep | 3 and 5 (WL, WF) |
| E-73 | `Transform.VisibleEvent` (TO) | the coupled consumer alphabet | keep | 19 (TL) |
| E-74 | `Transform.visibleEvent` (TO) | the projection that hides internal settlements by identity | keep | 19 (TL) |

## Gap table — what ES2026 and Web IDL require that no Streams declaration provides

Q3's packet is "existing plus gaps and nothing else". These are the gaps. Each
row states the specification obligation, the nearest Streams declaration, and
what is actually missing.

| Gap | Obligation (anchor) | Nearest Streams row | What is missing |
| --- | --- | --- | --- |
| G-01 | reaction lists: `[[PromiseFulfillReactions]]` (2745630..2745966) and `[[PromiseRejectReactions]]` (2745977..2746311), with `PromiseReaction Record` fields `[[Capability]]` (2691475..2691802), `[[Type]]` (2691815..2692138), `[[Handler]]` (2692151..2692611) | E-29 | Streams has a single undifferentiated subscription list on the transform state only; the readable and writable halves have **no reaction list at all** and register a reaction by setting a phase (E-36) or a Boolean (E-41). No `[[Type]]` tag, no capability field |
| G-02 | the handled bit `[[PromiseIsHandled]]` (2746322..2746637) and its consumer `HostPromiseRejectionTracker` (`sec-host-promise-rejection-tracker`, clause 2701220..2702791) | E-15, E-21 | the bit exists and is set; nothing reads it, no rejection tracker exists, and there is no law relating it to anything. Partial gap, and the only row where the model is ahead of the Streams census |
| G-03 | PromiseCapability Record (`record.promise-capability-record`, clause 2687751..2690437) with `[[Promise]]` (2688749..2688997), `[[Resolve]]` (2689010..2689283), `[[Reject]]` (2689296..2689567); `NewPromiseCapability` (2696238..2698770); `CreateResolvingFunctions` (2692679..2695411) | E-19 | wholly absent. Streams allocates an identity and settles it directly; there are no resolving functions, so there is nothing that can be handed to foreign code, and `Promise ( executor )` (2708413..2711495) has no counterpart |
| G-04 | `IsPromise` (2698778..2699315) and the promise/thenable distinction | — | absent; the model has no value universe in which a promise could be one value among others |
| G-05 | thenable adoption: `NewPromiseResolveThenableJob` (2705599..2707541) and the adoption branch of `CreateResolvingFunctions` | E-35 | `Transform.Completion.adopt` adopts an **internal identity**, never an arbitrary object with a `then` method. No thenable job, no `then` lookup, no re-entrancy from adoption |
| G-06 | Web IDL `wait for all` (`op.wait-for-all`, 353239..354879) and `get a promise to wait for all` (`op.waiting-for-all-promise`, 354881..356058), including the `[=Queue a microtask=]` step the Q2 externals flag | E-55, E-56 | Streams has the settled **predicate** in two forms and nothing else: no returned promise, no ordered result list, no failure short-circuit, no microtask step |
| G-07 | a realm-independent job queue: `HostEnqueuePromiseJob ( job, realm )` (clause 633447..635836), Job Abstract Closures, and the JobCallback Record (clause 628436..630247) | E-45, E-48, E-52 | Streams has **three separate per-component job lists** and no single queue; no realm parameter, no `Job` Abstract Closure carrier, no `HostMakeJobCallback`/`HostCallJobCallback` (630253..631441, 631447..632699). The only global queue anywhere in the repository is the held P8a draft's, which is unfrozen |
| G-08 | the run condition: jobs run only "when there is no running execution context and the execution context stack is empty" (625769..626250), only one job at a time (626257..626350), each to completion (626357..626479) | E-46, E-49, E-53 | approximated per component by `frames = []`, `control = []` or the three-way transform guard, always as a hypothesis of a branch equation and never as a named requirement over runs. The DB-05 specification/realizer pair that R-P5 requires for `hook.host-enqueue-promise-job` therefore does not exist yet: the realizer is present, the specification is not |
| G-09 | the Web IDL exception universe: the remaining simple exception kinds, the base `DOMException` error names (`idl-DOMException-error-names`, 198581..211138, ruled one row per name and `owned` by R-P10), "create a DOMException" (665488..666331), "create a DOMException derived interface" (666333..667324), "throw an exception" (667326..667543) | E-59 | Streams has two kinds and a `foreign` escape. No name table, no `throw`, no `create`, no `DOMException` |
| G-10 | the completion discipline: 53 `? ` and 9 `! ` early-return prefixes across the 390 in-scope ES2026 steps, reproduced by an `Except`-shaped result under R-P9 | — | Streams uses `Except (Boundary.Exception ε) X` for settled outcomes and `Option` for "no transition"; the two are not the same thing and neither is a Completion. The carrier is admitted with the Q3 packet, so this gap is scheduled, not open-ended |
| G-11 | `PerformPromiseThen` (2740635..2743669, 29 steps) as a whole operation, and the `then`/`catch`/`finally` built-ins over it (2740014..2743689, 2737067..2737453, 2737669..2740006) | E-31, E-37 | Streams has steps 8–10 twice, specialized, with no result capability, so `react` returns nothing. Everything the derived promise makes possible — chaining, the two `upon …` wrappers' derived handles, `Promise.prototype.then`'s return value — is absent. The held P8a draft states this same restriction for its observer profile |

## Ordering of the moves

Six levels. Within a level the rows are independent and may be landed by
different seats; across levels the order is forced by what a definition
mentions.

| Level | Rows | Depends on | May proceed in parallel with |
| --- | --- | --- | --- |
| L0 | E-59 (`Boundary.Exception` → `WebIdl.Exceptions`) | nothing | L1, unless decision 2 fixes E-01's reason parameter to the Web IDL type, in which case L0 precedes L1 |
| L1 | E-01, E-02, E-03 (the three carriers) | L0 only under decision 2 | L3 |
| L2 | E-04, E-05, E-06 (the three `abbrev`s), then E-07..E-12 (their identity views, unchanged) | L1 | L3 |
| L3 | E-44, E-45, E-46, E-48, E-49, E-50, E-51, E-52, E-53 (the job queues) | nothing but the payload types, so E-48 needs E-02 and E-44 needs E-02 | L1, L2 |
| L4 | E-13..E-23 (the tables and their operations) | L1, L2 | L3 |
| L5 | E-29..E-33, E-37, E-38 (reactions and registration) | L1..L4 | — |
| L6 | E-55, E-56 (the settled predicate) | L4 | — |

**Why the P4–P7 proofs do not change.** For a `move` row the Streams name
becomes `abbrev X … := Ecma262…Y …`. An `abbrev` is a `@[reducible] def`, so
`X` and `Y` are definitionally equal and interchangeable at `rfl`: a dependent
that writes `X` elaborates to `Y`; a constructor written `.pending` is
resolved against the expected type, which unfolds to `Y`; and every P4–P7
receipt proved `by rfl` or `by intros; rfl` re-elaborates unchanged. The
existing repository already relies on exactly this: `Writable.UnitPromise` is
an `abbrev` over `Readable.PromiseState Unit ε` and `unitPromise_eq` is proved
`rfl`. Three conditions must hold for the argument to be sound, and each is a
Q3 acceptance obligation rather than an assumption:

1. the general type derives the same instances (`DecidableEq`, `Repr`) under
   the same hypotheses, and instance search finds them through the reducible
   abbrev, so `decide` and the `simp` normal forms in the four `simp`-set
   modules are unchanged;
2. the general type's constructor names are the Streams names, so
   dot-notation resolves;
3. no `move` row is applied to a **function** that appears in an
   `attribute [local simp]` set. `simp [f]` uses `f`'s equation lemmas; an
   `abbrev` over a general function has one equation, `f = General.f`, and
   unfolding it does not bring the general function's own equations into the
   set. Every such function is therefore `generalize`, not `move`: the Streams
   definition stays, its equations stay, and a bridging lemma relates it to
   the general one. That is decision 5, and it is why the mode split is 6
   move / 28 generalize rather than the reverse.

The `generalize` rows change no Streams definition body and no Streams
theorem statement; they add a general declaration and a bridging lemma, and
they re-derive the general law from the Streams instance or the reverse. The
observable effect on the tree is therefore: the root audit's declaration count
rises by the new abbrevs and bridging lemmas and by nothing else, and every
existing battery stays green with no edit to a frozen statement.

## P8a reuse table

The held draft on `codex/configuration-breaker` is at checkpoint `6c44e08`
plus uncommitted edits to `COORDINATION.md`,
`WhatwgTest/Streams/Semantics/OrderingContract.lean`,
`WhatwgTest/Streams/Semantics/OrderingLaws.lean` and
`test/contracts/configuration-ordering.contract.md`. As read on disk the two
modules carry **104** and **54** `#check` ascriptions, 158 in total; that
worktree's `docs/CONFIGURATION-DAG.md` still records the earlier tranche of
102 and 44, so the design record is four and ten ascriptions behind its own
draft. Nothing here changes those files; the classification is read-only.

| Class | Ascriptions | Contents |
| --- | ---: | --- |
| **Direct** — the statement is already general; only the namespace changes | **8** | `Job`, `Job.mk`, `Job.serial`, `Job.kind`; `enqueueJob`; `queuedJobs`; `enqueueJob_eq`; `queuedJobs_eq` |
| **Rename only** — the statement is general, the name is Streams-flavoured, and at most a payload type parameter is abstracted | **32** | `PromiseRef` and its three accessors → `Ecma262.Promise.Ref`; `ObserverPhase` and its four constructors → the reaction phase; `Registration` and its five accessors → `Ecma262.Promise.Reaction`; `Active` and its four constructors → the `Ecma262.Jobs` activation state that carries "one job at a time" (626257..626350) and "run to completion" (626357..626479); `lookup`, `lookupRegistration`, `setRegistrationPhase`, `register` (this is Web IDL `react`), `notifySettled` (this is `TriggerPromiseReactions`, 2700260..2701212), with their five `_eq` laws; and the two FIFO-suffix laws `step_active_jobs_eq` and `episodePrefix_jobs_eq`, the second of which is the `active_episode_fifo_suffix` obligation R-P12 names |
| **Streams adapter** — stays in `Whatwg.Streams.Semantics` | **118** | `Config` and its eleven ascriptions; `Decision` and its five constructors; `Startup`; `JobKind` (the Streams payload instance of the general job); `Event` and its nine constructors (six of which — `registered`, `observerCalled`, `observerReturned`, `jobQueued`, `jobStarted`, `jobFinished` — are a general reaction-and-job alphabet inside a Streams-specific type); `initial`, `liftWritable`, `preStartAllowed`, `authorFrontier`, `takeSinkHead`, `tick`, `decide`; `Step`, `Reaches`, `EpisodePrefix` and their constructors; the `m2Allowed` / `M2LivePrefix` / `observeLive` group of seven; the `stagedRequests` / `sinkMarkerCount` / `Suspensions` group of seven; `SuccessfulControl` and its eight constructors; `externalWord`, `Normalized`; and the 45 laws over those, including all ten `takeSinkHead_*` receipts and the two fixed-external-word run laws |

Two consequences for Q4. First, the DB-11 restatement is a **re-homing of 40
of 158 ascriptions and a rename of 32 of them**, not a rewrite: 118 stay where
they are, in content as well as in file. Second, the draft's `Registration` /
`ObserverPhase` / `register` / `notifySettled` cluster is the same ES2026
content as inventory rows E-29..E-33 and E-37; if Q3 lands those rows, the
draft's cluster becomes a use of the general layer rather than a second
design, and the restatement cost DB-11 accepts is paid mostly by Q3, not Q4.

## Decisions for the coordinator

1. **Type parameters of the general promise state.** Does
   `Ecma262.Promise.State` carry two parameters (value, reason), with
   `Readable.PromiseState α ε := Ecma262.Promise.State α (Boundary.Exception ε)`
   as the Streams `abbrev`? Recommended yes: E-22 already needs a non-unit
   value, and a one-parameter type cannot host both E-01 and E-22.
2. **Does `PromiseState` keep its `ε` parameter or take the Web IDL exception
   type?** ES2026 rejects with an arbitrary language value, so the reason
   should be a free parameter in `Ecma262.Promise` and `WebIdl.Exceptions`
   should be the instantiation Streams uses. Fixing the reason to the Web IDL
   type inside `Ecma262` would make L0 precede L1 and would put a Web IDL
   dependency inside a module DB-11 says imports only `Whatwg.Infra`.
3. **Do promise identities stay `Nat`?** Streams uses `Nat` with per-root
   monotone cursors (E-14, E-23) and P6 and P7 witnesses fix concrete values.
   The P8a draft adds an owner qualifier. Recommended: `Nat` stays, and
   `Ecma262.Promise.Ref` is the owner-qualified pair, with Streams continuing
   to use bare `Nat` under a single-owner view until P8.
4. **Is the general job queue polymorphic in the payload?** The three Streams
   queues carry `PullAnswer` (E-48), `SinkJob` (E-45) and `Transform.Job`
   (E-52). Recommended: yes, `Ecma262.Jobs.Queue (π : Type)`, with the FIFO
   and empty-queue laws stated over `π` and instantiated three times.
5. **Move or generalize for the functions named in `attribute [local simp]`
   sets?** Eleven promise-layer functions appear in the four sets listed
   above. Recommended: `generalize` with a bridging lemma for every one of
   them, and `move` only for types. Choosing `move` here is the single most
   likely way to turn a "no proof changes" landing into a proof-script
   rewrite in four modules.
6. **Do `PullAnswer` and `PullReturn` collapse into `PromiseState Unit ε`?**
   They are isomorphic to it and to each other's `Option`, but not
   definitionally equal, and six `rfl` receipts in WL depend on the current
   shapes. Recommended: keep all three distinct and record the isomorphisms as
   bridging lemmas.
7. **Guard or assertion for `settle`?** ES2026 `FulfillPromise` asserts the
   promise is pending; `Writable.settle` makes a non-pending settle the
   identity, and `settle_other` is a frozen receipt for exactly that. The
   general operation must pick one. Recommended: the total guarded function,
   with the assertion as a separate side-condition lemma, so E-20's receipts
   survive.
8. **One reaction list or two?** ES2026 splits fulfill and reject reactions
   (G-01); `Transform.State.subscriptions` is one list with an
   answer-receiving handler. Recommended: two lists in `Ecma262.Promise`, with
   a one-list view Streams instantiates, decided before E-29 moves.
9. **`handled` as a list of identities or a per-cell field?** Nothing reads it
   (G-02), so the cost of either is small today and large after a rejection
   tracker exists. Recommended: per-cell field in the general table, with a
   bridging lemma to `id ∈ handled`.
10. **When does `Boundary.Exception` generalize?** It has 69 dependent
    theorems in eight files and Web IDL simple exceptions carry no allocation
    identity (E-59). Recommended: schedule it as its own slice inside Q3 with
    its own breaker contract, not as a rider on the promise rows.
11. **Who owns the generalization of the settled predicate?** `wait for all`
    is not one of Q3's six operations, yet E-55 and E-56 are the only Streams
    declarations that match it. Recommended: land them in `WebIdl.Promise` as
    a predicate with an explicit note that the operation (G-06) is absent, or
    defer both rows to the P7-facing packet — but say which, because a silent
    deferral leaves two `generalize` rows with no owner.
12. **Does the Streams promise-slot re-disposition move to Q3?** R-P5 puts it
    at Q4. If the moves in L1 and L4 land in Q3, the Streams rows become
    references into `Whatwg.Ecma262` at that moment rather than at Q4.
    Recommended: keep R-P5 as ruled and let the Q3 rows land with the Streams
    census unchanged, so that exactly one slice changes the Streams
    denominator.
