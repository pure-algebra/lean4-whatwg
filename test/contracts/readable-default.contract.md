# Default-readable representative contract (P4a)

Breaker: Codex, 2026-09-05. Base: `c1c7caa`. Graph: `READABLE-PG-DEFAULT`.
Status: frozen after independent semantic review and intended-red verification,
2026-09-05. The introducing packet commit is supplied in the coordinator handoff.

This packet fixes the first semantic default-readable lifecycle. The pinned
`vendor/whatwg-streams-b9ba9f49/index.bs` is the semantic owner; exact census
anchors and declaration dispositions are owned by `docs/READABLE-DAG.md`.
The immutable WPT corpus is `vendor/wpt-480fdfcd/streams/` at
`480fdfcd85d043c23875665f464c35c0043dff52`.

The builder must not edit this contract, the two red battery modules, or the
retained breaker witnesses. All acceptance equations are exact ascriptions
in `WhatwgTest/Streams/Readable/DefaultContract.lean`; the axiom list is
`WhatwgTest/Streams/Readable/DefaultAxiomReport.lean`.

## Semantic extent

The initial configuration is the projection immediately after a successful
start and acquisition of one default reader, before that configuration's
first demand check. Its HWM is an admitted P3 size; its underlying pull,
cancel, and foreign size algorithms are names. The packet models enqueue,
size return, read, close, error, demand, one outstanding pull, and its
fulfillment/rejection job. It includes synchronous reentrant operations while
a size call is suspended. The fixed-reader projection is a named view of the
default stream/reader/controller slots, not a second stream calculus.

This packet does not implement or refuse acquisition, release, start,
cancel, tee, async iteration, or IDL methods. Those operations remain owned
and open under full P4. Public IDL enqueue/close wrappers must later throw
TypeError on an invalid call; `beginEnqueue` and `close` here model the
abstract algorithms, whose initial guard returns normally without mutation.
Byte/BYOB remains P9. Effects algebra and the global configuration are later
views over these first-order transitions, not stored program data.

The numeric view is `Readable.Size := Data.DyadicSize` and `Readable.sizes :=
Data.DyadicSize.sizes`. It adds no numeric carrier. P3's exact arithmetic
assumptions and `DATA-FB-ROUNDING` remain: this packet does not claim binary64
rounding behavior. A chunk and a foreign reason are data parameters; callback
names and promise/request identities are natural numbers. No field stores a
Lean function, `Program`, promise object, closure, or host object.

## First-order surface

`Boundary.Exception ε` has `rangeError Nat`, `typeError Nat`, and `foreign ε`.
The natural number is a first-order allocation identity, not just an error
kind. `Exception.ofRangeError id` embeds P3 `Data.RangeError` at the chosen
identity; `Exception.toRangeError` erases identity and returns `some` precisely
for that constructor. Retraction and constructor injectivity discharge
P3-R2 without changing P3 signatures. Each newly raised range error consumes
`State.nextError`; an already-thrown reason consumes no new identity. An
enclosing invalid enqueue must allocate even after a nested call errored the
stream. Global disjointness between stream supplies remains an embedding
obligation; local fresh errors must already be distinguishable.

Within `Whatwg.Streams.Readable`:

* `Status ε` is `readable | closed | errored (Exception ε)`. Stored error
  exists only in the errored constructor.
* `ReadResult α` is `chunk α | done`.
* `PromiseState α ε` is `pending | fulfilled α | rejected (Exception ε)`.
* `Algorithms` stores `size : Data.SizeAlgorithm Nat`, `pull : Nat`, and
  `cancel : Nat`. Clearing algorithms writes `none` to the one optional
  record. A suspended frame owns an already-started invocation separately.
* `Settlement α ε` is `closed (Except (Exception ε) Unit)` or
  `read Nat (Except (Exception ε) (ReadResult α))`.
* `Event α ε` is `sizeCalled Nat Nat α`, `pullCalled Nat`,
  `enqueueReturned Nat (Except (Exception ε) Unit)`, `settled Settlement`,
  or `desiredSizeRead (Option Size)`.
  The first `sizeCalled` identity is the enqueue call; its second is the
  algorithm name. Events record operations and settlement, not execution of
  arbitrary user reactions.
* `PullContinuation α` is `done | settleRead Nat α | returnEnqueue Nat`.
  A queued read's continuation owns its already-allocated read ID and chunk.
* `Frame α` is `size Nat α | pull (PullContinuation α)`. These are the
  LIFO synchronous size/pull call frames, not promise-reaction jobs.
* `PullAnswer ε` is `fulfilled | rejected (Exception ε)`.
* `PullReturn ε` is `pending | settled (PullAnswer ε)`. Returning from a
  synchronous source callback is distinct from eventual settlement of its
  returned promise. A synchronous throw is a rejected return under the
  promise-return callback boundary, retaining the exact reason.
* `State α ε` stores status, the canonical `Data.Queue α Size`, HWM,
  `started`, `closeRequested`, `pulling`, `pullAgain`, optional algorithms,
  pending read IDs, next read ID, next enqueue ID, next error identity, the
  closed promise state, read promise states indexed by IDs, a LIFO list of frames,
  `pullAwaiting`, a FIFO list of pull-answer jobs, and the event trace.

Constructor and projection signatures are frozen by the battery. This
record is a raw first-order projection: arbitrary record literals need not
be reachable. No theorem may assume that closed/errored implies an empty
queue, or that queued chunks and pending reads cannot coexist. The pinned
reentrant algorithms invalidate both assumptions. Full reachability and
identifier uniqueness are further P4 obligations; this packet's general
transition equations state their premises and do not infer reachability
from the record's type.

## Required operation behavior

`initial algorithms hwm` has a readable stream, attached reader with pending
closed promise, empty queue/read list/job list/trace/frame stack, fresh IDs
zero, started true, all three control flags false, and the named algorithms.
It is a projection constructor, not the specification's whole setup method.

`desiredSize` returns none for errored, zero for closed, otherwise HWM minus
the queue total. `canCloseOrEnqueue` is exactly readable and not
closeRequested. `shouldCallPull` additionally requires started, then accepts
a pending read or positive desired size. Positive infinity is positive; NaN
is not. A pending read creates demand even at zero HWM.

`continuePull s k` executes the recorded continuation: do nothing, settle the
captured read with its captured chunk, or record the enclosing enqueue's
normal return. Settling a captured read does not inspect current stream
status. A synchronous source callback may have errored or closed the stream
in the meantime; its current queued read still receives the chunk.

`callPullIfNeededWith s k` runs the continuation immediately when there is
no demand. If already pulling it sets pullAgain then runs the continuation,
without invoking another source callback. Otherwise, when algorithms exist,
it sets pulling=true and pullAwaiting=false, pushes `.pull k`, and appends a
named pull invocation. It suspends before executing k. `callPullIfNeeded` is
the same operation with `.done`. The algorithm's asserted precondition
pullAgain=false applies to reachable states; malformed raw records do not
gain a host claim. With missing algorithms the raw-state extension simply
runs k. A pull callback can reenter controller or reader operations, which
may push further size frames. Matching return transitions enforce LIFO.

`returnPull` accepts only a top pull frame. It removes that frame and either
sets pullAwaiting=true for a returned pending promise, or appends the already
settled answer as a reaction job and leaves pullAwaiting=false. It then runs
the captured continuation synchronously. This is when reactions attach to
the returned promise, after invocation returns. An empty stack or top size
frame has no pull-return transition. Source bodies never enter stored state.

`acceptPullAnswer` is defined only while pullAwaiting=true, sets it false,
and appends the answer as a FIFO job. It does not execute the reaction.
`runPullJob` is defined only with no synchronous size or pull frame and at least
one job. It removes the oldest job, then executes its reaction.
Fulfillment clears pulling; if pullAgain was set it clears pullAgain and
re-evaluates demand. Rejection calls controller error; it does not invent a
pulling=false assignment absent from the specification. No unanswered call
or empty job queue is an error: these are live frontiers.

`close` first tests canCloseOrEnqueue. With a nonempty queue it only sets
closeRequested. With an empty queue it also clears algorithms and closes the
stream via `streamClose`. That abstract stream operation first fulfills the
closed promise and records that settlement,
then fulfills pending reads with done in request-list order and empties the
request list. `streamClose` itself does not clear algorithms; its controller
caller does. `error` is inert unless readable; otherwise it resets the queue,
clears algorithms, stores the exact reason, rejects the closed promise first,
then rejects pending reads in order. Existing synchronous frames and pull jobs are
retained: they are already-started computations.

`read` allocates the next read ID and marks disturbed in the later full
stream embedding (the representative has no undisturbed observation). A
closed stream immediately answers done, an errored stream rejects with the
stored reason. In a readable stream, an empty queue appends a pending request
and invokes the demand check. A nonempty queue uses P3 dequeue and allocates
the current read's pending promise before calling pull. After the last queued
chunk, if closeRequested, it clears algorithms and closes the stream before
settling that read with the chunk. Otherwise it calls the demand operation
with a `settleRead` continuation. If that invokes pull, the current read
settlement suspends until `returnPull`. Synchronous error, close, enqueue, or
a nested read can change state and settlement order before it resumes. No
unconditional final queue/status/order equation is asserted across that call.

`beginEnqueue s chunk` models the abstract enqueue operation. A failed
canCloseOrEnqueue guard returns `s`. An admitted operation allocates an
enqueue ID. A pending read is fulfilled directly, without invoking size or
changing the queue, then demand is checked with a `returnEnqueue` continuation.
An invoked pull callback must return before the enclosing enqueue returns.
Otherwise the built-in `.one` algorithm continues synchronously with P3's
one. A foreign size algorithm pushes the new frame and emits sizeCalled.
It does not append the chunk yet. Missing algorithms in a raw admitted state
are inert; reachable active states must carry algorithms.

`resumeSize` requires a top size frame, pops exactly that frame, and invokes
`finishEnqueue` with its call, chunk, and the existing P3
`SizeAnswer Size (Exception ε)`. An empty stack or top pull frame has no transition.
`finishEnqueue` has already passed the entry guard. It must not recheck
canCloseOrEnqueue or reconsider the direct-delivery branch. An admissible
size appends to the current queue, even if the callback changed status or
added a pending read. It then checks demand with a `returnEnqueue`
continuation. An inadmissible size allocates a fresh identity, increments the
supply, calls error with the embedded range error, and returns that same fresh
range error. A thrown size reason calls error with that exact reason and
returns it. Because error is inert once non-readable, a reentrant earlier
stored error is retained even when the enclosing enqueue returns another
exception.

## Observations and relational face

`settlementTrace` extracts the settlements in trace order. It is one component
of M2, not a replacement for the DB-04 mask. `VisibleEvent` contains settlement,
desiredSizeRead, and enqueueReturned; named foreign callback invocations are
internal trace events and are omitted from this consumer view.
`observeM1` returns the successful read chunk sequence and the current stream
status. Pending reads and unanswered foreign calls are live, not terminal
errors. `M2Observation` contains `m1 : List α × Status ε` and the ordered
visible events. `observeM2` populates both from state. The frozen
`observeM2_toM1` theorem projects M1 directly from that observation, without
requiring additional state. `queryDesiredSize` records the pure desiredSize
result in trace; its explicit decision is included in this packet. The P8
global promise/consumer observation embedding remains open.

`Decision` is first-order: read, enqueue, close, error, size answer, pull
callback return, later pull answer, or desiredSize query. `step` consumes
exactly one such decision; controller/read calls are
total, unmatched answers give none. `Step` is its relational graph. `Steps`
is the inductive finite-list closure with nil and cons, and its append law
is proved by induction. Pull job execution is a separate internal transition,
never a consumer choice or a tape decision. This packet does not freeze a
fixed-fuel runner or assign a bind law to one. A later configuration relation
must integrate internal job steps with external steps under the host's
run-to-completion profile. This first representative blocks internal jobs
while its synchronous size/pull frame stack is nonempty. Returning a source
callback is a foreign-boundary decision; executing
its queued promise reaction is an internal transition.

## Adversarial obligations and remaining scope

`WS-READ-CE-001` through `WS-READ-CE-017` are owned by the central register and
`test/counterexamples/readable/ATTACKS.md`. The retained finite breaker models
distinguish tempting mutants. The production battery separately requires
quantified transition laws and reentrant witnesses, so an independent toy
model passing is never presented as proof of production behavior.

No full-P4 or coverage cutover follows from this packet. Remaining work:
reader acquisition/release and lock ownership, setup/start, cancellation,
arbitrary read-request callbacks, tee, async iteration, the global FIFO job
configuration, general reachable-state invariants, a structural first-order
chunk universe and its embeddings, Effects signature view, host rounding
relation, and complete algorithm-by-algorithm coverage witnesses. The
unlocked-reader alternative is part of that extension, not a refusal.

## Acceptance and handoff

Red modules: `WhatwgTest.Streams.Readable.DefaultContract` and
`WhatwgTest.Streams.Readable.DefaultAxiomReport`. The known-red file declares
both; root imports and exhaustive audit integration belong to the coordinator.
The green finite witness module is
`WhatwgTest.Streams.Counterexamples.Readable.Default`.

Narrow commands, from the breaker worktree with `LEAN_NUM_THREADS=1`:

```text
lake env lean -DmaxErrors=10000 WhatwgTest/Streams/Readable/DefaultContract.lean
lake env lean -DmaxErrors=10000 WhatwgTest/Streams/Readable/DefaultAxiomReport.lean
lake env lean WhatwgTest/Streams/Counterexamples/Readable/Default.lean
```

The intended red failures are unknown production names and direct downstream
elaboration failures only. Import/toolchain failures are infrastructure
failures, never acceptable red evidence. The builder must turn both modules
green without weakening a statement, provide the theorem axiom receipts
inside the root's R-11 ceiling, remove the two known-red entries, and pass
the full build and all root gates. Broad verification is deliberately not run
concurrently with the coordinator's integration build.

Measured freeze evidence, 2026-09-05:

* All fourteen algorithm spans in `docs/READABLE-DAG.md` were independently
  rehashed from the sealed `index.bs` bytes with .NET SHA-256 and matched the
  census digests. No vendored or generated bytes changed.
* The independent reviewer admitted the revised equations after checking the
  pinned algorithms, synchronous pull/size reentrancy, distinct allocated
  errors, and DB-04 observations. Reviewed battery SHA-256:
  `8527abcf8d1acbd9fde0ce73308e03231421271481d30fe7d0812a8dc1d6bc3d`.
  This review was read-only source/specification analysis, not a build.
* `DefaultContract.lean` has 204 exact ascriptions, including 94 theorem
  obligations. Its corresponding axiom report names exactly those 94
  theorems. The seventeen finite breaker witnesses are separate evidence.
* The breaker's root `Whatwg.Streams.olean` was absent. The first `lake env
  lean` attempt therefore failed on an import and is explicitly excluded
  from intended-red evidence. Lake overrides inherited `LEAN_PATH` here.
  The following successful infrastructure workaround used the pinned `lean`
  executable directly, with the coordinator's already-verified artifact
  directory from commit `319e7448cee9b958abca579e6e262377e4c760da`.
  `git diff c1c7caa 319e7448 -- Whatwg/Streams.lean Whatwg/Streams` is empty.

```powershell
$env:LEAN_NUM_THREADS = '1'
$env:LEAN_PATH = 'C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Readable/DefaultContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Readable/DefaultAxiomReport.lean
lean -M2048 WhatwgTest/Streams/Counterexamples/Readable/Default.lean
```

The contract command exits 1 with 770 diagnostics: 705 unknown identifiers,
42 dotted-name errors caused by their missing expected types, three field
errors caused by missing types, and twenty missing-structure errors. There
is no parse/import error, type mismatch, or failed instance synthesis.
The axiom command exits 1 with exactly 94 unknown constants. These are
intended red; no synthetic error-recovery term is admitted as a proof.
The finite-witness command exits 0 in 1.1 seconds: sixteen receipts have no
axioms, and CE-009 uses only `propext`. No full build was run in this worktree.

The coordinator separately ran `node harness/readable/reentrancy.mjs` under
Node v22.23.2, win32 x64: CE-013/014/015/016 were observed under that host
profile. This is finite host evidence, not a theorem or simulation result.

All required graph edges remain open. The packet freezes what the builder
must prove; it does not claim production implementation, global reachability,
full P4, M2 host equivalence, or a coverage increase. The known-red entries
are included with the packet; imports into the test/audit roots and the full
trust self-test belong to the coordinator's integration change.
