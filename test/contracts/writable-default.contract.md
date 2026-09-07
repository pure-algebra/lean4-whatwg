# Default-writable representative contract (P5a)

Status: frozen base packet. Breaker: Codex, 2026-09-05.
Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`.
Graph: `WRITABLE-PG-DEFAULT`, owned by `docs/WRITABLE-DAG.md`.

This is the breadth representative for one write/close lifecycle with
backpressure, including the erroring and pending-abort transitions that can
intervene in that lifecycle. It starts after successful controller start and
acquisition of one default writer. The pinned Streams text is the semantic
owner. Source callbacks, size callbacks, and abort-signal listeners may
reenter synchronously; the packet must not freeze a non-reentrant profile.

The writer remains attached throughout this representative: release and
acquisition/reacquisition are excluded decisions with a required later
ownership-check projection. Full setup/start, Web IDL objects, arbitrary
promise reaction registration, transfer refusal, cross-calculus composition,
and global allocation/scheduling embeddings remain open. A later admission
must relate this projection to the whole stream; this packet does not claim
that a compiling representative finishes P5 or raises coverage by itself.

## Reused owners and first-order representation

`Boundary.Exception ε`, its first-order allocation IDs, and the P3 range-error
adapter remain the shared exception owner frozen by P4a. Generated errors
allocate distinct IDs; rethrowing an existing reason retains its identity.
P3 `Data.DyadicSize`, `Data.SizeClass`, `Data.Queue`, `Data.SizeAlgorithm`, and
`Data.SizeAnswer` remain the numerical, queue, strategy, and size-answer
owners. Binary64 rounding remains `DATA-FB-ROUNDING`.

The generic unit promise outcome and callback return shapes currently live
under `Readable`: P5a uses explicitly named views of
`Readable.PromiseState Unit ε`, `Readable.PullAnswer ε`, and
`Readable.PullReturn ε`, with identity/round-trip receipts. This dependency
is temporary placement of a shared value shape, not a writable-to-readable
semantic embedding. No new global promise runtime or allocation carrier is
created. The eventual move of shared shapes must preserve both frozen APIs.

Promise identities are retained in a local identity-indexed table. The
writer's ready and closed slots hold IDs into that table. Replacing the ready
slot never overwrites the old promise cell. Local natural-number cursors for
promise/error identities are seeded input views of a future shared supply;
cross-stream freshness is an explicit open embedding obligation.

Proposed public types in `Whatwg.Streams.Writable`:

* `Status ε := writable | erroring (Exception ε) | errored (Exception ε) |
  closed`; the stored error exists only in its corresponding tagged state.
* `QueueItem α := chunk α | close`; `State.queue` is the canonical
  `Data.Queue (QueueItem α) Size`. The close sentinel has size zero.
* `OperationPhase := invoking | awaiting | queued` describes callback return
  and later promise settlement. `CloseState := none | queued Nat |
  inFlight Nat OperationPhase` enforces the specification's explicit XOR
  between closeRequest and inFlightCloseRequest. In-flight write is a
  separate optional identity/phase pair: disjointness between write and
  close in flight requires a reachable-state theorem, not a raw-type claim.
* `PendingAbort ε := requested Nat (Exception ε) | alreadyErroring Nat`;
  the second case owns no reason because the specification clears it.
* `Algorithms.size` is an optional P3 `SizeAlgorithm Nat`. Sink slots are
  optional `SinkAlgorithm.fulfilled | foreign Nat` values. A default fulfilled
  algorithm is present; an absent slot means ClearAlgorithms removed it.
  Already-started callbacks retain
  their own first-order call frames.
* `State α ε` owns the writable slots, identity-indexed promise outcomes and
  handled markers, ready/closed promise IDs, the queue,
  pending write request IDs, close request, pending abort, current in-flight
  operation, abort callback phase, fresh cursors, a LIFO synchronous call
  stack, FIFO reaction jobs, and a first-order event trace.

The exact constructor surface is in `WhatwgTest/Streams/Writable/DefaultContract.lean`,
and the stage equations are in `DefaultLaws.lean`; independent review and red
receipts are recorded below. No field stores a Lean function, `Program`,
host promise, object, or closure. Data parameters and algorithm names are
related to host values only by a named later profile.

## Source requirements already established

### Write entry and size reentrancy

`WritableStreamDefaultWriterWrite` invokes GetChunkSize before its current
state/closing checks. GetChunkSize returns one if the size algorithm has been
cleared. A thrown size result calls ErrorIfNeeded with the exact reason and
returns one; the enclosing writer write then checks errored, closing/closed,
and erroring, in that order. The preceding ownership check is discharged only
by this packet's fixed-attached-writer scope, with full release behavior open.
A nested size callback may close, abort, error, or recursively write another chunk. It is
incorrect to check writable state only before the size callback, or to
enqueue a chunk admitted before reentrant close.

The pending write promise is allocated after these checks, so nested size
callbacks can allocate their write promises before the enclosing write.
ControllerWrite enqueues via P3; invalid size raises a fresh range error,
calls ErrorIfNeeded, and returns without invoking the sink. On success,
backpressure is updated only if no close is queued/in flight and status is
writable, then queue advancement is requested.

### Queue advancement and sink invocation

The specification's unstarted branch is outside this post-start snapshot.
An in-flight write prevents advancement. Erroring
advances to FinishErroring after in-flight work ends. Otherwise the first
queue item selects ProcessWrite or ProcessClose.

ProcessWrite moves the oldest write-request promise into the in-flight slot
before invoking the named sink write callback. It does not dequeue the chunk.
The callback is a synchronous reentrancy boundary; the returned promise is
not available for reaction attachment until callback return. A returned
pending promise admits a later settlement answer; a returned already-settled
promise appends its reaction job at attachment time. Both cases leave the
operation in flight until that job executes.

Write fulfillment first resolves the in-flight write promise and clears its
slot, then dequeues the chunk, then updates backpressure if still writable
and not closing, then advances the queue. Another sink callback may run
synchronously during that advancement. Rejection preserves an earlier stored
error, rejects the current write with its own rejection reason, and enters or
finishes erroring. `ready`, the current write, queued writes, and `closed`
therefore need separate settlement identities and order.

### Close and backpressure

An admitted close allocates a close request and resolves the current ready
promise immediately when backpressure is true and state is writable. It
enqueues a zero-size close sentinel. ProcessClose moves the close request in
flight and dequeues the sentinel before invoking sink close. It clears
algorithms after the synchronous callback returns and attaches reactions to
the resulting promise. Clearing them before invocation is observably wrong
under reentrancy.

A successful in-flight close resolves the close promise first. If status is
erroring, it clears the stored error and resolves a pending abort request.
It then enters closed and resolves the writer's closed promise. A failed
close rejects the close promise and pending abort with the close rejection
reason before rejection processing; any earlier stored stream error is
retained where the specification retains it.

Backpressure false-to-true allocates a fresh pending ready promise and
changes only the ready slot. True-to-false resolves the current ready promise.
No unchanged backpressure transition allocates a replacement. Closing can
resolve ready while leaving backpressure true, so pending-ready is not
equivalent to backpressure throughout the lifecycle. Erroring rejects
a pending ready cell in place or replaces an already-settled ready cell with
a new rejected cell; old references keep their original outcomes.

### Erroring, abort, and the signal boundary

ControllerError clears algorithms and starts erroring only while writable.
StartErroring stores the first reason and rejects/renews ready immediately,
but FinishErroring waits for any in-flight operation. FinishErroring resets
the queue, rejects pending writes in order, and either rejects close/closed
or starts the separately staged sink abort operation.
FinishErroring itself does not clear algorithms. It removes pendingAbort
before invoking the sink abort callback.

WritableStreamAbort first ignores already-terminal states, then signals the
controller's abort signal. The model records the first signaling argument,
not the DOM signal object's normalized reason; that normalization remains in
the abort foreign profile. First signaling runs author code synchronously;
the model records a signal-call frame and waits for an explicit return before
rechecking stream status or pendingAbortRequest. Repeated signaling does not
dispatch the same listeners again: the one-shot marker is set before entering
author code. After signal return, terminal state is checked before pending
abort reuse. An inner abort can already make the state errored; the outer
then returns a fresh fulfilled promise. Otherwise an existing pending abort
request is returned by identity. The first signal argument and a nested
abort's stored stream/sink reason can therefore differ.

If the stream was already erroring, an abort request records that fact and
its promise is eventually rejected with the existing stored reason without
calling the sink abort algorithm. Otherwise abort starts erroring with its
own reason. Sink abort runs only after any in-flight operation finishes and
after queued writes are rejected. Its synchronous callback return precedes
algorithm clearing and reaction attachment. Abort fulfillment/rejection
settles the abort promise before rejecting close/closed.

### Observations and semantics

The named local sink observation records chunks presented to foreign sink write callbacks and
the terminal state; a rejected sink write has still received its chunk.
The default fulfilled sink algorithm makes no foreign call and contributes no
chunk to this view. The view is therefore neither all admitted writes nor a
complete consumer-delivery judgment.
It is a candidate projection whose embedding into DB-04's consumer-chunk M1
remains open. The local ordered observation contains the sink observation and
the ordered visible promise settlements,
promise-reference returns, desiredSize queries, and API returns. The sink-view
projection must be available directly from the ordered observation. Pure helper
queries do not silently become observations: explicit consumer query
transitions record ready/closed identities and desiredSize results.

Synchronous callback frames are LIFO. Promise reaction jobs are FIFO internal
state and cannot execute inside a live synchronous callback frame. Callback
return and later promise settlement are distinct typed boundary decisions.
Unanswered callbacks/promises and absent jobs are live frontiers. Relational
composition belongs to the transition/finite-run face; no fixed-fuel bind
law or host equivalence is asserted. `Reaches` labels of `none` record
deterministic administrative ticks, not foreign tape choices. Consumer and
foreign decisions are admitted only with an empty control stack or a foreign
marker on top; a nested call pushes its work above that marker. `tick` cannot
cross a marker, and FIFO jobs run only once the synchronous stack is empty.

The exact signature surface has 162 entries and the stage battery has 108
quantified obligations. The 16 retained counterexamples are finite fixtures;
their corresponding production repairs are the quantified laws recorded in
`test/counterexamples/writable/ATTACKS.md` and `WS-WRITE-CE-001` through `016`.
Neither these counts nor their future compilation is a specification coverage
report or a whole-P5 completion claim.

## Verification and integration receipt

The exact signatures, stage ascriptions and 16 retained finite mutants are
physically present. The independent reviewer found no semantic blocker after
checking the 162 interface entries and 108 equations against the pinned text.
The graph carries the exact ownership map and 35 verified byte-span anchors.
Final review acknowledgment and artifact digests are in the graph's freeze ledger.
The commit carrying this packet is its identity; the full hash is reported in
the handoff. Two composed lifecycle regressions will be a separate frozen
theorem-only addendum. Stage equations alone do not satisfy that outstanding
representative-lifecycle obligation or the P5 exit criteria.

Narrow verification used the pinned toolchain directly with one thread and
`-M2048`, inheriting only main's verified library path from source/artifact
basis `5121268d3c148678bfbe501b245881631524f2e5`. Main's full build had
passed before the coordinator yielded this exclusive narrow window. In the
breaker worktree:

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Writable/Default.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/DefaultContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/DefaultLaws.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/DefaultAxiomReport.lean
```

Commands ran sequentially. Witness: exit 0; 12 axiom-free and four
`propext`-only receipts. Interface: exit 1, 392 missing production-name
diagnostics. Laws: exit 1, 615 diagnostics, comprising 478 missing names,
50 missing-structure, two missing expected tuple type, 73 missing expected
constructor type and 12 missing field/projection type consequences. Report:
exit 1, 108 missing production theorem names. No final parser, import,
type-mismatch or instance-synthesis diagnostic remained. These missing-name
failures are intended red; cascading unknown-type errors add no evidence.

The first law run also exposed 19 record-layout parser errors. Twenty
multi-line record updates were consistently indented before rerunning the
law check. Those earlier parser failures were not intended-red evidence.
Logs are at `$env:TEMP/whatwg-p5a-witness.log` and
`$env:TEMP/whatwg-p5a-Default{Contract,Laws,AxiomReport}.log`; the durable
counts and commands above are the receipt, not a dependency on temp files.

No Lake command, main-checkout write, or writable production change was made
by this breaker. The coordinator owns root imports, the host fixture, and
the three known-red entries at integration:
`WhatwgTest.Streams.Writable.DefaultContract`,
`WhatwgTest.Streams.Writable.DefaultLaws`, and
`WhatwgTest.Streams.Writable.DefaultAxiomReport`.
The builder may begin only after the reviewed packet is committed and those
red entries are declared. They are removed when the implemented battery is
green. Full build, exhaustive axiom gate and repository gates are later
integration receipts; no open graph edge is closed by this packet's freeze.

## Composed lifecycle addendum (frozen separately)

Base packet: `68fc922e4efde615fc9aecb2f3433afa99514a02`. This addendum
adds only `Writable.lifecycle_write_close` and
`Writable.lifecycle_abort_rejection` theorem obligations. It changes none
of the 162 interface signatures or 108 stage/view laws in that base.

`WhatwgTest/Streams/Writable/LifecycleContract.lean` freezes two explicit
`Reaches` derivations, with `none` labels for deterministic administrative
ticks and typed consumer/foreign decisions at their allowed frontiers.
Both start from the same fixed post-start attached-writer snapshot: HWM one,
P3 size algorithm `.one`, named foreign write/close/abort algorithms
0/1/2, and initial promise/error cursors zero.

* `lifecycle_write_close` quantifies the chunk and both data/reason types.
  It reaches a pending-write state with backpressure, retains fulfilled old
  ready ID 0 and pending current ready ID 3, then admits close, fulfills the
  write and sink close, and asserts the exact local ordered view. Close
  fulfills ready before the write answer; final close/closed settlements
  follow the write, and old/current ready identities remain accessible.
* `lifecycle_abort_rejection` quantifies both chunks and two distinct shared
  exception reasons. It reaches an in-flight first write, queued second
  write and pending abort, then accepts the first write's rejection and
  a fulfilled sink-abort return. The current write retains its incoming
  rejection reason, while ready, queued write and closed use the earlier
  abort reason; the abort promise fulfills between queued-write and closed
  rejection in the exact ordered view.

These are quantified facts about two fixed trace shapes under named local
sink-input/ordered views. They do not range over arbitrary programs or prove
the still-open DB-04 mask/global scheduler/shared supply embeddings. The
independent reviewer manually checked every tick/frontier, promise ID and
ordered event against the frozen 108 stage equations and found no correction.

The exclusive narrow command window used the same pinned toolchain and main
artifact basis `5121268d3c148678bfbe501b245881631524f2e5`:
`leanprover/lean4:v4.33.1` from the unchanged `lean-toolchain`.

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/LifecycleContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/LifecycleAxiomReport.lean
```

Both exited 1 as intended red. Contract: 50 diagnostics, with 30 missing
production names and 20 unknown-type consequences (18 constructor and two
tuple notations). Report: two missing production theorem names. No parser,
import, type-mismatch or instance-synthesis diagnostic appeared. Logs were
`$env:TEMP/whatwg-p5a-LifecycleContract.log` and
`$env:TEMP/whatwg-p5a-LifecycleAxiomReport.log`.
Only documentation comments changed after that check.

The coordinator declares
`WhatwgTest.Streams.Writable.LifecycleContract` and
`WhatwgTest.Streams.Writable.LifecycleAxiomReport` as known red before
building these production theorems. Their proof receipts, full build and
gates are implementation work; this breaker has not changed production.

## Exact in-flight equation addendum (frozen separately)

The builder's elaboration of the frozen `hasInFlight_eq` exposed a precedence
weakness in that acceptance condition. In the pinned Lean4.33.1
`Init/Notation.lean`, equality has precedence 50 and Boolean OR has precedence
30. `Init/Coe.lean` coerces decidable propositions to Bool using `decide`
and Bool to Prop using equality to true. Consequently the unparenthesized
old statement denotes `(decide (hasInFlight s = writeFlag) || closeFlag) = true`.
It imposes no restriction on the answer when closeFlag is true.

The original frozen ascription and production definition remain unchanged.
`WhatwgTest/Streams/Writable/InFlightExactContract.lean` adds only
`Whatwg.Streams.Writable.hasInFlight_exact`, whose full Boolean RHS is
parenthesized. It is the required exact slot equation for the INFLIGHT
algorithm; the earlier weaker predicate remains valid but cannot stand in
for this exact receipt. No new runtime operation or carrier is introduced.
Independent review confirmed both the pinned Lean parsing/coercions and the
Streams algorithm's test of the write/close in-flight slots.

`WS-WRITE-CE-017` retains an Init-only parse theorem and finite counterexample.
They both passed without axioms. The exact ascription and its separate axiom
report were checked sequentially:

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/InFlightExactContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Writable/InFlightExactAxiomReport.lean
```

Each exited 1 with exactly one unknown `hasInFlight_exact` diagnostic;
all existing State/field expressions elaborated. There were no cascading
type, parser or import errors. The inherited compile artifacts came from the
coordinator's P5 implementation at main base
`47a86da602f5964e7cdaf24d43a99dbb70f1e59e` plus its uncommitted writable
source snapshot, which had passed the 162 interface checks. This is compile
infrastructure, not a clean-commit/full-build claim. The inspected
`Writable/Backpressure.lean` source SHA-256 was
`d2982d85b5c8683d72e20bdce5fcdacb120ad13ee07432aedb58ce946c853918`.

The coordinator owns the two new known-red declarations and root integration:
`WhatwgTest.Streams.Writable.InFlightExactContract` and
`WhatwgTest.Streams.Writable.InFlightExactAxiomReport`.
The breaker has changed no existing frozen Lean file or production source.
