# Piping proof graph (`PIPING-PG-FORWARD-SHUTDOWN`, P7a)

Status: P7a implementation and theorem receipts, 2026-09-05. Contract:
`test/contracts/piping-shutdown.contract.md`. The frozen forward-error
representative passes; full P7 and the named remaining embeddings stay open.

## Current state

This table describes commit `325d5d5` on 2026-09-30, with the trust row brought to the lane V landing of 2026-10-01 (R-V6). P7a landed on
2026-09-05 with implementation `6bb79d2`, closing laws, counterexamples and
trust; full P7 stays open. Ruling R-V4 sets the rule: an edge is
`required-closed` only when every ground this document or a ruling in
`COORDINATION.md` states for keeping it open is discharged by something named
in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The unique ownership joins of the generated declaration snapshot, which has no generator (debt D47) (P7a landing receipt) |
| construction | `required-open` | Arbitrary-start construction: arbitrary prior checkpoints, full canonical source reachability and global freshness. Admitted read inventory, returned-reference retention and reachable candidate phase invariants are proved (P7a landing receipt) |
| semantics | `required-open` | Global semantics and scheduling (P7a landing receipt). The rows of "Full P7 residual map" below still apply, among them backward error and close, forward close, the whole read pump, canonical cancellation and releases, signal actions and pipe-promise settlement |
| laws | `required-closed` | The 44 frozen stage and requirements laws in `Whatwg/Streams/Piping/Laws.lean` and the two composed runs in `Runs.lean` are proved; the 46 named receipts print (P7a landing receipt) |
| representation | `required-open` | Full component and host representations (P7a landing receipt) |
| counterexamples | `required-closed` | `WS-PIPE-CE-001` to `WS-PIPE-CE-016` are `CLOSED` in `test/counterexamples/REGISTER.md` with their named production repair laws, for the local scope the register records (P7a landing receipt) |
| bridges | `required-open` | `forwardShutdown_realizes` proves `ForwardShutdownSpec` under `observeShutdown` for every admitted finite candidate run. The full lock, release, cancel, pipe-promise, M1 and global-scheduler bridge remains; neither the finite safety theorem nor the two fixed shapes establish progress or eventual shutdown (P7a landing receipt) |
| targets | `not-applicable` | No target generation; P11 owns lowering |
| trust | `required-closed` | The 46 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent source, proof and landing review passed (P7a landing receipt). Three of the receipts, `forwardShutdown_realizes`, `lifecycle_two_writes_abort_rejection` and `lifecycle_write_rejection_retains_source`, reached `Classical.choice` at `325d5d5`; slice V5 of lane V repaired them with no statement changed, and since that landing the axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1, R-V6) |
| coverage | `required-open` | The coverage join for the full residual clause map and its numerator witnesses (P7a landing receipt) |

## Source owners

Streams commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18` owns the
requirements. The aliases below name exact sealed census rows. The breaker
rehashed all eight byte spans with system SHA-256; each matched the census.
The independent reviewer rehashed the same eight spans before the freeze at
`2f43183`. `PIPE` identifies the surrounding requirement-bearing algorithm,
not permission to identify the predicate with a particular implementation.

| Alias | Census row | SHA-256 |
| --- | --- | --- |
| PIPE | `op.readable-stream-pipe-to` | `7b96d032a18f9003d2f8fdca57be770f5c5c6799620378fa122eb26ef58f3f87` |
| DIRECT | `requirement.public-api-must-not-be-used` | `b1ef1eb74583f8e6fcda2fa8d7465227ad229093b441de58d68383acbfcb49cb` |
| BP | `requirement.backpressure-must-be-enforced` | `12719b4ed85eaa95696bf6f557f683d6f53ef8a107773e7c9b47893d760a1a22` |
| STOP | `requirement.shutdown-must-stop-activity` | `79d2935ad9000ed2b784fd9601a16e41392c1ccd06ecfa75d0a505502e668eda` |
| PROPAGATE | `requirement.error-and-close-states-must-be-propagated` | `cbb1cc0df93b6e3a817dd99ba58fa0360d8674319849a1c2faff63530b3c830d` |
| ACTION | `requirement.rs-pipe-to-shutdown-with-action` | `a9ba86da2a0c5b99f4ce54b01262cc80b3695e48f5c0fc084dfdda940d958574` |
| SHUTDOWN | `requirement.rs-pipe-to-shutdown` | `3f33415b785e880ea3c276455cd8e36b7e367866325d795c4114f461fdf02462` |
| FINALIZE | `requirement.rs-pipe-to-finalize` | `f74cef91c4476d2277fa50b7edf85419a199f791d2c45627615d9a0677a7ba5a` |

P4/P5 algorithms retain their existing authority rows. A piping adapter must
name the canonical operation it calls and cannot become a second owner of
that operation. Reference-implementation and WPT pins are in
`SPEC-MANIFEST.md`; their source reading is evidence, not a semantic owner.

## Declaration and existing-type records

The exact frozen names are relative to `Whatwg.Streams.Piping`, ascribed in
`ShutdownContract.lean`; equations and composed runs are in `ShutdownLaws.lean`
and `ShutdownRuns.lean`.
The breaker retains the statements; this exact freeze admits the builder.
Every family routes to this graph. Constructors and fields inherit their
type's role while requiring individual generated ownership joins. Derived
instances and the listed theorem receipts inherit the same owner; this does
not permit an additional exported helper to evade its declaration record.
P7's builder owns production only after freeze; the breaker retains the
exact statements and witnesses. No additional public helper is admitted by
this packet; implementation organization may use private helpers.

| Family | Proposed module | Relationship / anchor | Assurance obligation |
| --- | --- | --- | --- |
| `WriteStage`, `ReadWriteLink`, `markWrite`, `deliveredReads` | `Requirements.lean` | `requirement` view/bookkeeping over P4 delivered read IDs and P5 call/result IDs; ACTION/STOP | exact canonical settlement/return linkage, order and uniqueness |
| `ShutdownPlan` | `Requirements.lean` | `requirement` view of selected source error, sampled drain guard, and prevention flag; PROPAGATE/ACTION/SHUTDOWN | first-selection identity and stable guard |
| `Snapshot`, `ProtocolEvent`, `ProtocolRecord`, `ShutdownObservation` | `Requirements.lean` | `requirement` observation views reusing canonical P4/P5 snapshots, with no candidate phase; all aliases | read-only historical evidence, exact before/after projection, no full DB-04 M1/M2 claim |
| `WritesSettled`, `BodyDecision`, `ReadInventory`, `InitialSnapshot`, `RecordAllowed`, `ObservationChain`, `ForwardShutdownSpec` | `Requirements.lean` | canonical `requirement` predicates independent of candidate reachability; STOP/PROPAGATE/ACTION/SHUTDOWN | no-new-read through nextRead, canonical transition linkage, all-settled drain, action-only reason replacement |
| `Phase`, `State`, `initial`, `snapshot`, `emit`, `Admitted` | `PipeTo.lean` | candidate-realizer state embedding actual P4/P5 states, plus protocol and historical observation data; PIPE/ACTION/SHUTDOWN | no duplicated active queue/status/outcomes/allocator; post-read batch admission; inherited source error supply |
| `drainGuard`, `nextUnwritten`, `allWrittenSettled`, `lookupReturn` | `PipeTo.lean` | derived candidate views of P5 close/desired-size/promise/return owners and requirement links | exact Boolean-to-requirement and return-provenance laws |
| `enterForwardShutdown`, `invokeWrite`, `captureWrite`, `invokeAbort`, `captureAbort`, `requestFinalize` | `PipeTo.lean` | candidate stages adapting canonical P4/P5 intrinsic operations; ACTION/SHUTDOWN | sampled guard, first latch, actual call and result identity, missing-finalization frontier |
| `Decision`, `foreignDecision`, `stepWritable`, `externalFrontier`, `decide`, `tick`, `Step`, `Reaches` | `PipeTo.lean` or new `Step.lean` | local candidate integration, typed foreign answers and relational finite composition; PIPE | canonical jobs and true callback frontiers; no scheduler decision or writer API exposed to foreign bodies |
| `observeShutdown`, `forwardShutdown_realizes` | `PipeTo.lean` or new `Laws.lean` | candidate-to-requirement adapter/bridge under the named fragment observation | quantified trace theorem from admitted canonical component states |
| every named equation and quantified law in `ShutdownLaws.lean` | owning module or new `Laws.lean` | derived receipt inheriting its owning family and source disposition | exact laws and trust receipts; no weakening of the independent predicate |
| `lifecycle_two_writes_abort_rejection`, `lifecycle_write_rejection_retains_source` | new `Runs.lean` if needed | derived actual canonical P4 prefixes and P5 finite traces | pending write blocks, two writes retained, exact abort/action/write reason distinctions |

No pipe promise, stream-lock record, cancellation result, or release event is
invented for this fragment. Its finalization-request frontier is first-order
protocol data. Supplying the missing canonical operations and a relation to
actual completion is required before it can serve as full pipe meaning.

## Full P7 residual map

| Requirement or surface | Proposed representative | Still owned/open |
| --- | --- | --- |
| Direct intrinsic operations | actual P4/P5 adapter call sites | full API/property-interception and realm correspondence |
| Backpressure | already-read batch submissions use current canonical desired size before shutdown; owed writes ignore it during required drain | complete read pump/ready-identity loop, no needless read/write serialization, BYOB sizing belongs to P9 |
| Shutdown stops activity | no new reads, only existing read inventory written | global concurrency and pending-read fulfillment after shutdown |
| Forward error | exact source reason, preventAbort and actual P5 abort | arbitrary initial setup and full observer registration timing |
| Backward error | no implementation in first representative | canonical source cancel, preventCancel, all competing states and precedence |
| Forward close | no implementation in first representative | closeWithErrorPropagation, preventClose, source final chunk order |
| Backward close | no implementation in first representative | fresh TypeError identity, no prior chunks assertion, source cancel |
| Shutdown with action | captured destination guard, drain, action result precedence | signal action list/wait-all and other propagation actions |
| Shutdown without action | preventAbort branch and same drain guard | success branch and all other callers |
| Finalize | explicit request with exact reason | canonical writer release then reader release, signal removal, pipe promise settlement and full M1 outcome |
| AbortSignal | absent signal profile | DOM reason normalization, already-aborted startup, one-shot registration/removal and action ordering |
| Acquisition/pipeThrough | actual quiescent P4 delivered batch and fresh P5 view, with two canonical prefix/run witnesses | arbitrary prior-write checkpoints, locks, disturbance, wrapper checks, P6 endpoint embedding and full pipeThrough relation |
| Global meaning | finite relational fragment observation | fair/infinite runs, deterministic ECMAScript job embedding, DB-04 M1/M2, flagship full realizability theorem |

The residual rows are not refusals and cannot be discharged by mentioning a
type. In particular, this proposal cannot close PLAN's full P7 exit gate.

## Coordinator integration and module allocation, 2026-09-05

Packet `2f4318337b839de1cce5d12e5c1f31e594dc6222` is integrated as
`ea037259afc700909c817e4504489926d17344b2` after P6a
`afb57f8ee0d889b1b4866138e31862e0cf825fd4`. The sole register conflict
retained the verified P6 closure text and appended the frozen P7 section:
25 added lines, no existing row removed or weakened. The imported finite
witness module passes the normal 68-job narrow build. The coordinator
declares the four frozen production batteries in the known-red set.

`Requirements.lean` owns the independent snapshot/event types and predicates,
including canonical read inventory, intrinsic-transition constraints and
`ForwardShutdownSpec`. `PipeTo.lean` owns the candidate state, bookkeeping,
component adapters and admission predicate. New `Step.lean` owns the
dispatcher and relational finite derivations. New `Laws.lean` will own the
44 frozen local and quantified statements and private proof-support
invariants; these support this graph's construction/bridge edges and do not
create a second semantic owner. New `Runs.lean` will own the two frozen
composed witnesses. No stable declaration name or frozen statement changes
with module placement. All required proof-graph edges remain open during
implementation.

## Receipts

`docs/receipts/PIPING-PG-FORWARD-SHUTDOWN.md` holds this graph's history,
moved there verbatim under ruling R-V4: the first paragraph of "Source owners"
as frozen, the edge table as amended at the P7a landing, the independent
review and verification ledger of the freeze, and the P7a landing receipt with
its file fence, judgment and proof boundary, verification commands,
independent review and remaining obligations. This document still owns that
landing receipt, the exact fragment judgment and its commands, and keeps them
in that log, so references to them resolve there. The coordinator's
integration and module allocation record stays above because it carries the
module placement of the frozen names; its last sentence describes the edges
during implementation, and the table in "Current state" supersedes it.
