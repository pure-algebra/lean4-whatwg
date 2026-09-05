# Transform backpressure representative contract (P6a)

Status: frozen breaker packet, 2026-09-05; not an implementation admission.
Breaker: Codex, 2026-09-05. Base:
`5121268d3c148678bfbe501b245881631524f2e5`.
Graph: `TRANSFORM-PG-BACKPRESSURE`, owned by `docs/TRANSFORM-DAG.md`.

The semantic owner is the pinned Streams `index.bs`. This packet fixes one
transform/backpressure representative while retaining concrete relations to
the canonical readable and writable states. It is not a substitute for the
remaining transform lifecycle or the shared configuration in P8.

## Representative extent

The initial projection is at the demand-check tail of successful readable
start, with one attached default reader and writer and the writable start
already successful. It stages canonical `Readable.callPullIfNeeded`; any
resulting native pull frame must finish before an external call is admitted.
The readable output strategy is P3's `.one`, with an
admitted exact high-water mark. The input strategy is the P5 strategy. The
transform body is a named foreign algorithm: one invocation can emit zero or
multiple chunks, reenter reads, enqueues, writes, errors, or termination,
return an unanswered promise, or reject with an exact shared exception.
Synchronous callback return and eventual settlement are separate stages.

The `.one` output strategy is the first breadth profile, approved by the
coordinator. Arbitrary output-size strategies remain owned and open; they
require cross-component LIFO size continuations and are not refused.
Setup/start, unlocked readers, writer release, transformer flush/cancel,
full close/abort/cancel lifecycle, byte streams, transfer refusal, general
host correspondence, and global promise-adoption jobs remain open. A live
unanswered callback is not a rejection or refusal.

## Existing owners and coupling seam

The coupled state embeds `Readable.State` and the independently frozen
`Writable.State`. It does not copy either queue, status alphabet,
reader/writer promises, or algorithms. Numeric data and count size reuse P3;
exception identities reuse `Boundary.Exception`. The shared unit outcome,
callback answer, and callback return are named views of P4's existing shapes.

Backpressure-change promise identities use a named adapter of the existing
P5 identity-indexed promise table and its `freshPromise`, `lookupPromise`,
and `settle` operations. The transform records its allocated internal IDs.
No third promise table or global runtime is introduced. An allocation law
must retain all prior cells, `readyPromise`, `closedPromise`, and outstanding
write identities; freshness requires the canonical table's fresh-cursor
premise. Global allocation remains an explicit embedding obligation.

`Writable.observeOrdered` continues to expose its original candidate view.
The transform's own candidate consumer view filters settlements of the
recorded internal backpressure IDs and includes the readable deliveries.
It must not call a settlement-only projection M2 or erase query results.
The later DB-04 embedding must justify cross-component reaction order and
ECMAScript adoption/assimilation jobs.

The configured P4 pull and P5 sink-write algorithm names designate owned
internal ports. They cannot be answered by arbitrary foreign decisions.
The coupling dispatcher services those ports before exposing an external
frontier. An internal pull/sink invocation is not an opportunity for user
reentrancy; only the actual transformer/size/signal body is such a boundary.

## Backpressure identities and subscriptions

The candidate exact surface is in
`WhatwgTest/Streams/Transform/BackpressureContract.lean`. Names are relative
to `Whatwg.Streams.Transform`:

* `Ports` names the internal pull, readable cancel, writable write, close,
  and abort ports. Close/cancel/abort remain reserved even though their
  lifecycle continuation is not implemented by this representative.
* `Algorithms` stores the three foreign transform/flush/cancel names.
* `Completion` is `direct | adopt resultPromise`: direct returns the
  PerformTransform reaction result to P5; adopt relates that result to the
  already allocated blocked-write reaction result.
* `Reaction α` is `write request chunk resultPromise`,
  `transform resultPromise`, or `adopt resultPromise`. It stores no function.
* `Subscription α` is `readable promise`, `writable promise request`, or
  `reaction promise reaction`. Registration order is list order.
* `Job α ε` is `readable promise`, `writable request`, or
  `reaction reaction answer`. The first two tags identify already admitted
  canonical P4/P5 jobs; they are not replacements for those job bodies.
* `Control ε` is `awaitTransform request completion writableDepth`,
  `errorWritable reason`, `waitWritable depth`, `unblock`, or
  `settle promise answer`. The await marker is an actual foreign call; the
  other tags are deterministic administrative work and not tape decisions.
* `State α β ε` embeds `Readable.State β ε`, `Writable.State α ε`, ports,
  backpressure flag/current ID, retained internal IDs, optional algorithms,
  subscriptions, jobs, control, pending transform request/result-ID pairs,
  a local controller call cursor, and a joint event trace.
* `Event α β ε` lifts canonical P4/P5 events and records named transformer
  invocation/return and the public transform enqueue result. These events
  are administrative plus observable data, not themselves a claim to M2.
* `OutputObservation β ε` contains the delivered readable chunk sequence,
  readable status, and writable status. `OrderedObservation` contains that
  output view plus `VisibleEvent` values: readable settlements and queries,
  canonical writable visible events, and public transform enqueue results.
  These are local candidates for the later DB-04 embedding, not a claim to
  global M2 or host correspondence.

`withReadable` and `withWritable` replace their canonical component and
append the component's newly added trace suffix to the joint trace. Their
trace-prefix premise is a reachable-transition invariant, not inferred from
arbitrary replacement records. `freshInternal` allocates a pending cell
through P5 and retains its new ID in `internalPromises`.

`notify` maps a readable subscription to the exact P4
`acceptPullAnswer` state plus a readable job tag, a writable subscription to
the exact P5 `acceptAnswer` state plus a writable job tag, and an ordinary
reaction subscription to its queued reaction/answer. Missing canonical
pending operations have no transition; they are not silently fabricated.
`settle` resolves/rejects a pending shared-table cell through P5, removes its
captured subscriptions, and notifies them in list order. A previously
settled cell is unchanged and its subscribers are not notified twice.

The local adoption reaction is explicit data, not an assertion that this
one relay has the same number of jobs as ECMAScript promise resolution.
That job-count/registration embedding remains open under the named global
obligation. Both the distinct reaction-result identity and eventual outcome
dependency are already mandatory here.

`visibleEvent internalIds` erases only known internal promise settlements
from the canonical writable settlement events, while retaining writer ready,
closed and desired-size queries, returned consumer promises, and external
settlements. It also retains readable settlements/desired-size queries and
public transform enqueue completion. The nested P4 abstract enqueue return
is erased because the public completion is recorded by the enclosing
transform operation. Algorithm invocations/returns and other administrative
events are erased. `observeOutput` projects actual P4 M1 delivery plus the
two side statuses; `observeOrdered` includes this output value and filters
the joint trace. The original canonical P4/P5 observation functions are
unchanged.

`setBackpressure b` asserts that the flag changes. It resolves the old
backpressure-change cell, allocates a new pending cell, updates the slot,
then updates the boolean. Resolution records reactions in the registration
order of the subscriptions to the old identity. It does not execute them.
A same-flag raw-state extension is inert and has no specification assertion
claim. `unblockWrite` applies the operation only when backpressure is true.

The subscription alphabet distinguishes the readable pull reaction from
the blocked sink-write reaction. Every subscription contains the promise
identity captured at registration. A later slot replacement cannot retarget
it. Registration on an already fulfilled cell queues the reaction; pending
registration retains the subscription. Backpressure cells are never rejected
by the admitted algorithms. Invalid raw rejected/missing cells remain outside
the construction invariant and cannot become a foreign choice.

The internal reaction order is one ordered queue of component tags. P4/P5
reaction bodies remain their canonical operations. The adapter appends a
tag when it admits the corresponding answer into that component's pending
job queue, and only runs the component body for the oldest matching tag.
This is a local explicit integration order, with a later global promise-job
embedding obligation; it does not prove ECMAScript's complete job semantics.

## Native source-pull realization

The adapter consumes an actual P4 `.pull k` frame. Under the reachable
precondition backpressure=true, it runs `setBackpressure false`, returns the
NEW slot identity, and performs `Readable.returnPull .pending`. The saved
P4 continuation `k` then runs synchronously, including a captured read's
chunk settlement. The adapter registers the P4 reaction against the NEW
identity; the OLD identity's blocked write may already have a queued job.

When that NEW identity later resolves, the adapter calls
`Readable.acceptPullAnswer .fulfilled` and queues its matching reaction tag.
Only that oldest tag may run `Readable.runPullJob`. If that reaction's
pullAgain branch invokes another native source pull, the adapter services it
before exposing an external frontier. `pullAwaiting` alone is not an identity;
the subscription is required to retain the mapping.

The exact realization equation must mention the original P4 state/frame,
the resulting `returnPull` state, old/new P5 cell outcomes, queued reactions,
and the returned identity. A Boolean snapshot is not a source-pull run.

## Native sink-write and transform realization

The adapter consumes the P5 `.awaitSink (.write request chunk)` frame at
operation phase invoking and status writable. With backpressure=true, it
captures the OLD slot identity, returns pending through P5's exact
`decide (.returnSink .pending)` transition, and subscribes a blocked-write
reaction. No transform is called synchronously in this branch.

When the captured cell resolves, the queued reaction reads the CURRENT
writable status. Erroring rejects the pending sink result with its stored
reason and does not invoke the transformer. Writable invokes
`PerformTransform` with the captured chunk. The specification's assertion
rules out closed/errored at this point on an admitted in-flight write; those
raw states do not gain an invented success branch.

With backpressure=false, `PerformTransform` invokes the named transformer
synchronously. The P5 sink invocation does not return until the transformer
callback returns. The local call frame retains the request, chunk, and
continuation mode (direct sink invocation or blocked-write reaction).
Reentrant operations must finish in LIFO order before matching this return.

A returned pending transform promise installs an awaiting state; an already
settled return queues the appropriate reaction only after return. An eventual
answer is accepted only for an awaiting matching invocation and is queued.
Fulfillment forwards the sink answer through P5's canonical `acceptAnswer`.
Rejection first errors the readable side, clears the transform algorithms,
runs P5's canonical `.errorIfNeeded reason` continuation, unblocks writes,
then forwards the same rejection to the pending P5 sink invocation. The
canonical P5 erroring law decides which stored reason survives.

`performTransform` pushes the await marker and captures the current P5
control depth. A callback return matches only that marker after all
reentrant P5 work above its saved depth has returned. The direct mode also
requires the original invoking P5 sink-write marker/request; it then returns
pending through canonical P5 `decide`. The reaction-result cell is allocated
after the callback returns. Pending returns retain the request/result pair;
settled returns queue the transform reaction. Direct mode subscribes the P5
sink to that result. Adopt mode subscribes an adoption reaction into the
older blocked-write result. Thus old and new reaction-result IDs remain
distinct even when both will eventually carry the same unit outcome.

The current external decision alphabet includes read, write, enqueue,
transform error/terminate, readable and writer desired-size queries, writer
ready/closed queries, input-size return, transform return, and eventual
transform answer. It contains no pull answer, sink answer, native-port
choice, or reaction selector. Full writer close/abort and readable cancel
decisions stay owned/open with their corresponding transform lifecycle.

`tick` prioritizes synchronous owned work and existing P5 control steps,
then the oldest coupled job when no synchronous call frame is live. A
readable job executes P4 `runPullJob` and services only a newly invoked
native pull synchronously; it does not drain further reactions. A writable
job starts the canonical P5 job, whose deterministic control steps finish
before another coupled job can run. `Step` uses `none` for this internal
tick and `some decision` for an external transition; `Reaches` composes
these finite steps. Global scheduling and full reachability proofs remain
separate graph obligations. `waitWritable` advances P5 only while the stack
is strictly deeper than its saved depth; equal depth completes that
administrative continuation, and an undershoot has no transition. It cannot
pop the original sink/size callback frame to make progress.

Three required composed `Reaches` obligations prevent the component equations
from standing in for an actual coupled execution. All start from the named
count-profile `initial`, with canonical P4/P5 state constructors and a fresh
shared-table cursor. The first executes exactly the external sequence
write, read, enqueue one output, and settled successful transform return;
it reaches actual P4 delivery and P5 write/ready fulfillment, with old/new
backpressure identities retained. The second substitutes reentrant transform
error for enqueue; the active transform still returns successfully after
algorithm clearing, the P5 write result fulfills, and the overall readable
and writable states retain the error. That second run deliberately leaves
the source-pull subscription's pending backpressure cell live: stream
termination does not imply that every internal promise settles.
The third starts with positive readable HWM and writes/enqueues/returns
without any consumer read. It checks that the staged native source pull
opens initial capacity, so the transform runs and its output remains queued.
It excludes a model that needs an unnecessary read to clear initial pressure.

## Enqueue, error, and termination

Controller enqueue first checks P4 `canCloseOrEnqueue`. Failure allocates a
fresh TypeError from the shared error supply and throws it; it does not
silently return as the P4 abstract enqueue guard does. The accepted branch
delegates to actual P4 `beginEnqueue` with the count strategy and services
any native source pull synchronously. Only after that enqueue continuation
returns does it compute `hasBackpressure := !Readable.shouldCallPull`.
If the result differs from the transform flag, the admitted result is true
and `setBackpressure true` resolves/replaces the current cell. It never
sets backpressure false in this post-enqueue branch.

`TransformStreamError` delegates readable error before writable error and
unblocking. Writable erroring is a canonical P5 control/tick sequence,
not a copied assignment to a second status field. Controller termination
first calls the canonical readable close operation (therefore queued chunks
drain), allocates a fresh TypeError, then clears/errors/unblocks the writable
side. It does not error the readable side or discard an already queued chunk.

The accepted count-size enqueue has no foreign size body and hence no
post-size failure path. The full arbitrary-size enqueue's distinct abrupt
reason versus readable stored-error rethrow remains owned/open with its
own required future attack; it cannot be silently generalized from this
representative.

## Acceptance and verification ledger

The packet contains 112 exact interface ascriptions and 118 theorem
ascriptions, including three composed canonical P4/P5 runs, with all 118
names in the axiom report. Fourteen retained finite protocol witnesses are
registered under stable WS-TRANS IDs. All thirteen source spans match the
sealed census by independent system SHA-256 cross-check. The coordinator
owns known-red/root integration after the reviewed packet lands.
The exact known-red Lake module names for that integration are:

```text
WhatwgTest.Streams.Transform.BackpressureContract
WhatwgTest.Streams.Transform.BackpressureLaws
WhatwgTest.Streams.Transform.BackpressureAxiomReport
```

The independent counterexample module is green and is not a known-red entry.
The consumed P5 interface is now frozen by breaker commit
`68fc922e4efde615fc9aecb2f3433afa99514a02`; its two composed-run theorem
additions are at `b4f8642424901ff5f4dbd527777e5734a830d5ba`. P6 may consume
those exact shapes after their production modules elaborate in main.
No mutable P5 declaration is a frozen dependency. The direct Lean checks
use the coordinator's last successfully compiled P4/P5 artifacts, including
the verified P5 `decide`, `Step`, and `Reaches` surface. Those artifacts are
an import prerequisite, not a claim that the P5 proof graph is closed.

Commands from the breaker worktree, pinned Lean 4.33.1, one process at a time:

```powershell
$env:LEAN_NUM_THREADS = '1'
$env:LEAN_PATH = 'C:/Users/kokok/Dev/lean4-WHATWG-streams/.lake/build/lib/lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Transform/Backpressure.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Transform/BackpressureContract.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Transform/BackpressureLaws.lean
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Transform/BackpressureAxiomReport.lean
git diff --check
```

The fourteen-witness command exits 0: twelve receipts have no axioms,
CE-005 and CE-014 use only `propext`. The interface command exits 1 with
267 unknown-identifier diagnostics. The laws command exits 1 with 601
diagnostics: 474 unknown identifiers, 51 dotted-notation errors, 51 field
errors, and 25 missing-structure errors caused by the absent production
types. The axiom command exits 1 with exactly 118 unknown constants. None
is a parser/import error, type mismatch, or failed instance synthesis.
Lean's missing-structure error recovery may print `sorryAx`; no recovered
term is admitted as a declaration or proof receipt.

The final frozen Lean bytes were checked sequentially on 2026-09-05 with
those same results. Output is retained locally in
`.lake/transform-witnesses.log`, `.lake/transform-interface-red.log`,
`.lake/transform-laws-red.log`, and `.lake/transform-axioms-red.log`.
The exact 118 law/report-name join, duplicate-name check, 100-column Lean
check, and `git diff --check` passed. The coordinator's direct Lean window
was returned after all four commands terminated.

The first red run exposed six record-update layout errors in the authored
draft. They were repaired by putting the first field on a new line after
`with`, without changing any expression or proposition; the corrected laws
were rerun to the diagnostic counts above. No full build ran in this
worktree, and no production, vendor, generated, known-red, or root file was
edited. Independent review accepted the exact equations, observation view,
three composed runs, source hashes, and declaration/receipt joins. Its last
documentation correction clarifies that termination errors writable while
queued readable output remains available for later delivery. The immutable
packet head is supplied in the freeze handoff. All required graph edges
and every production counterexample repair
remain open; this is a breaker packet, not a P6 implementation receipt.

## Additive elaboration repair, 2026-09-05

After the production types became available, two expressions in the frozen
law battery needed explicit type arguments. `WhatwgTest/AGENTS.md` permits
elaboration repairs without changing the attacked statement, witness, or
acceptance condition. The coordinator requested these two disambiguations:

- `returnTransform_frame`: annotate the existing match result with
  `let u : Transform.State α β ε :=`, fixing the expected type of the existing
  `.reaction` and `.transformReturned` constructors.
- `visible_readable_query`: give `Transform.Event.readable` the existing
  quantified `(β := β)` argument, fixing its otherwise unconstrained output
  parameter. The original proposition-only check warned that `β` was unused.

The file `WhatwgTest/Streams/Transform/BackpressureLaws.lean` has SHA-256:

```text
before 463B4B843F0E859098CCE28F63EF805EFE3FC8FC3519F835FDB0D5F9159F690F
after  D939DE85318FC675E3685708DC5061FDC2E437C34DE01272D3D0FEBFC4E3BF4C
```

The preimage is the battery at frozen breaker commit
`03547f1feb938d65898c47b4061faeb3f4bd9edf`. Apart from the line wrap needed for
the second annotation, these are the only battery edits. No proposition
branch, premise, conclusion, theorem name, witness, or proof body changed.

The two proposition bodies were extracted verbatim into each local scratch
file, replacing only `#check (@Transform.<name> :` with `#check (`. Both
scratch files import `Whatwg.Streams`, disable automatic implicit parameters,
and open `Whatwg.Streams`. Thus a missing theorem name cannot hide expression
elaboration errors. The checks used main's last successfully compiled
production artifacts while main was at `5d95212e5b3953ec58616b7a0c7493627fa7fcfe`
with P6 implementation work uncommitted:

```powershell
$env:LEAN_NUM_THREADS = '1'
$env:LEAN_PATH = 'C:/Users/kokok/Dev/lean4-WHATWG-streams/.lake/build/lib/lean'
lean -M2048 -DmaxErrors=10000 .lake/transform-elaboration-original.lean
lean -M2048 -DmaxErrors=10000 .lake/transform-elaboration-annotated.lean
```

The original check exited 1 with exactly the two expected dotted-constructor
errors and the unused-`β` warning. The annotated check exited 0 with no
diagnostics. Logs are `.lake/transform-elaboration-original.log` and
`.lake/transform-elaboration-annotated.log`. These checks introduce no
declarations, proof assumptions, or axiom receipts. They check proposition
elaboration only; the complete theorem battery, default build, and gates
remain coordinator integration checks. The exclusive direct Lean window
was released after both commands terminated.

Independent review accepted the two annotations and this additive ledger as
an elaboration-only repair. The 118 law/receipt-name join is unchanged with
no duplicate names; the 100-column check and `git diff --check` pass.
