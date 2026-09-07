# Piping proof graph (`PIPING-PG-FORWARD-SHUTDOWN`, P7a)

Status: P7a implementation and theorem receipts, 2026-09-05. Contract:
`test/contracts/piping-shutdown.contract.md`. The frozen forward-error
representative passes; full P7 and the named remaining embeddings stay open.

## Source owners

Streams commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18` owns the
requirements. The aliases below name exact sealed census rows. The breaker
rehashed all eight byte spans with system SHA-256; each matched the census.
Independent review remains required before freeze. `PIPE` identifies the surrounding requirement-bearing algorithm,
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

## Ten edges

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact signatures, constructor census, unique ownership joins |
| construction | required-open | admitted read inventory, returned-reference retention and reachable candidate phase invariants are proved; arbitrary prior checkpoints, full canonical source reachability and global freshness remain required |
| semantics | required-open | independent requirements predicate, candidate transition meaning, deterministic local order and explicit live/finalization frontiers |
| laws | required-closed | all 44 frozen stage/requirements laws and both composed runs pass; see the P7a landing receipt; broader lifecycle and progress remain on the open edges |
| representation | required-open | actual P3/P4/P5 reuse, P6 endpoint relation where admitted, no duplicate runtime or host closures |
| counterexamples | required-closed | all sixteen retained WS-PIPE witnesses and their named production repair laws pass; the register records local scope |
| bridges | required-open | forwardShutdown_realizes proves the independent fragment judgment for every admitted finite candidate run; full lock/release/cancel/pipe promise/M1/global-scheduler bridge remains required |
| targets | not-applicable | no target generation; P11 owns lowering |
| trust | required-closed | all 46 named theorem receipts, exhaustive root audit, narrow/default builds, executable gates and independent source/proof review pass; see the P7a landing receipt |
| coverage | required-open | full residual clause map and eventual numerator witnesses; no coverage claim from this proposal |

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

## Independent review and verification ledger

The breaker read the full pinned piping requirements, the reference
candidate's pipe loop and shutdown/finalization code, and representative
forward-error WPT source. The candidate rechecks the identity of
`currentWrite` after awaiting it because an already-read chunk may have
started another write. This supports an all-read-chunks inventory
obligation; a single unchanged captured target is insufficient.

No production file is changed. No host or WPT test has been run for P7a.
The coordinator approved the representative scope and finalization boundary.

The independent reviewer read all 98 interface entries and 44 equations and
found no concrete candidate/requirements contradiction. The review confirmed
the sampled guard, source-first selection, rejected-write settlement,
canonical abort result identity and synchronous frontiers. Both quantified
run tapes were then manually traced against canonical P4/P5 equations; their
tick counts and IDs match. These are independent source reviews, not Lean
runs by the reviewer. The reviewer also independently rehashed all eight
source spans and joined 44 law plus two run names to the 46 axiom receipts.

The post-latch destination-erroring trap is retained as CE-015: actual P5
after-size and return stages create the rejected owed-write cell while the
first remains pending. Its complete reentrant callback tape is not one of
the two fixed lifecycle shapes, but its semantic obligation remains in the
unchanged quantified candidate-to-requirement theorem. CE-016 retains an
actual read on an errored source and its changed `nextRead`, matching the
requirements record's no-new-read snapshot check.

The breaker completed final direct verification under main's exclusive
window. The 16 witnesses pass within R-11; the four red files fail for
missing Piping declarations and the classified type cascades. The owning
contract's Verification and immutable-surface ledger records final source
hashes, exact commands, inherited artifact basis, log paths/digests, and
the coordinator's four known-red integration entries. All Lean processes
are terminal. Full production build/gates and the remaining graph edges
are still open.

Final independent freeze admission checked all five final source/log hash
pairs and the red classifications, with every unknown declaration belonging
to the planned Piping surface. Sixteen green witness receipts have the
exact axiom split in the contract. The final review required no further
semantic source or theorem changes. The immutable packet admits only this
local requirement/candidate pair and the two finite composed shapes;
complete canonical release/cancel, final pipe settlement, P6 endpoint/global
integration and full DB-04/P7 realization stay required-open.

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

## P7a landing receipt, 2026-09-05

### Base, packet and file fence

The implementation base is `ea037259afc700909c817e4504489926d17344b2`.
The head is the commit carrying this receipt; its exact hash belongs in the
coordinator handoff. The independent breaker freeze
`2f4318337b839de1cce5d12e5c1f31e594dc6222` was integrated at that base,
after P6a `afb57f8ee0d889b1b4866138e31862e0cf825fd4`.

The production fence is `Requirements.lean`, `PipeTo.lean`, `Step.lean`,
`Laws.lean` and `Runs.lean` under `Whatwg/Streams/Piping/`. The first
three own only the frozen requirement/candidate/transition surface;
`Laws.lean` exports the 44 frozen laws and keeps proof-support lemmas
private; `Runs.lean` exports the two frozen composed names. The other
changed files are both roots, the known-red set, P7 repair/status cells in
the counterexample register, this graph, `PLAN.md` and `COORDINATION.md`.
No P4/P5/P6 production, dependency, vendor or generated bytes changed.

The contract, four ascription/receipt modules, retained witness module and
attack descriptions have no diff from the integrated freeze. The five
source hashes in the contract's immutable-surface ledger were checked again
and match. The frozen statements, premises, tape shapes and acceptance
conditions were not edited. Both roots reach all new modules; the known-red
set is empty.

### Judgment and proof boundary

The first-order candidate reuses actual readable/writable states and the P5
promise table, IDs, control frames and jobs. It owns only read/write links,
shutdown selection, continuation state and historical protocol observations.
`ForwardShutdownSpec` independently constrains before/after records; it
does not use candidate `Phase`, `Step` or `Reaches` as its definition.

The public theorem is exactly:

```lean
Admitted s → Reaches s tape t → ForwardShutdownSpec (observeShutdown t)
```

It quantifies every finite tape and endpoint. Admission requires a quiescent
delivered-read snapshot, unique read inventory and a fresh canonical P5
initial state. It does not assert that every arbitrary readable snapshot is
reachable from initialization. The two composed theorems separately provide
actual P4 enqueue/read prefixes for their admitted starts.

The inductive support establishes three independent facts: read inventory,
canonical returned-promise references and phase-specific protocol shape.
Returned references come from actual P5 return events and retained table
keys. Existing fulfilled/rejected cells remain at the same outcome through
actual P5 steps; this supports retaining the all-settled drain obligation.
Candidate transitions then produce records satisfying the independent
requirements, and induction chains those records. The invariant does not
assume `RecordAllowed` or `ForwardShutdownSpec`.

The other quantified laws establish no new read ID, stable first selection,
and source-reason retention under `preventAbort`. Finalization only follows
the captured drain condition and the actual optional abort result. The
observation ends at `readyToFinalize`: no release, signal removal or pipe
promise is invented.

The two finite operational shapes quantify their chunks and distinct
exception reasons:

- `lifecycle_two_writes_abort_rejection`: actual P4 delivery of two reads,
  P5 writes 2 and 4, a source-error latch, both pending-write frontiers,
  successful draining, and rejected abort result 5. The requested finalization
  reason is the action rejection; source/destination error and closed result
  retain the original source reason.
- `lifecycle_write_rejection_retains_source`: actual P4 delivery and a P5
  write, source-error selection, then a distinct write rejection. With either
  prevention flag the requested finalization reason remains the source
  reason. Without prevention, canonical abort of the already-errored
  destination fulfills result 4 without invoking the sink abort body.

These proofs construct `Readable.Steps` and candidate `Reaches` derivations
with ordinary constructors, `simp` and `rfl`; they invoke the general
requirements theorem for the concatenated tapes. No fuel-bounded runner or
compiler-backed decision tactic supplies their judgments.

### Verification

Main held the exclusive verification window under Lean 4.33.1. Commands:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake --log-level=warning build WhatwgTest.Streams.Piping.ShutdownContract WhatwgTest.Streams.Piping.ShutdownLaws WhatwgTest.Streams.Piping.ShutdownRuns WhatwgTest.Streams.Piping.ShutdownAxiomReport WhatwgTest.Streams.Counterexamples.Piping.Shutdown
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Piping/ShutdownAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
lake --log-level=warning exe vendorseal
lake --log-level=warning exe citations
lake --log-level=warning exe tyxmlschema
lake --log-level=warning exe census
lake --log-level=warning exe census --report
lake --log-level=warning exe census --standard infra
git diff --check
```

The narrow build passes 75 jobs, including 98 interface ascriptions, all
46 exact theorem statements/receipts and sixteen retained finite witnesses.
The full build passes 298 jobs. The 46 production axiom receipts comprise
four axiom-free proofs, 25 at `[propext]`, fourteen at
`[propext, Quot.sound]`, and three at
`[propext, Classical.choice, Quot.sound]`. The last group is
`forwardShutdown_realizes` and the two composed runs. All are within R-11.
The exhaustive root audit checks 149 modules and 11780 declarations,
including 1595 in the Gates tooling tree.

The vendor seal checks 206 files across five pinned trees. Citations,
TyXML schema/emission drift, Streams census/emit and Infra census drift
checks pass. At base `ea037259afc700909c817e4504489926d17344b2` with this
implementation working tree, the checked report prints:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

No host, WPT or reference-implementation execution is claimed for this
implementation slice. No host-to-Lean comparison or global M1/M2 relation
was established.

### Independent review and remaining obligations

Independent source/proof review accepted the unchanged general theorem,
its noncircular invariant/record induction, and both composed run proofs.
It checked actual component transitions, return/settlement provenance,
captured guards, reason distinctions and the finalization boundary.
The coordinator owns the execution receipts above.

Final independent landing review compared the saved build, axiom, audit and
gate outputs with this receipt, rechecked all five frozen source hashes and
the zero packet diff, and accepted the local register closures and open-edge
scope. The production-root category comment was corrected to include P7a.

Identity joins, arbitrary-start construction, full component/host
representations, global semantics and scheduling, full piping bridges and
the coverage join remain required-open. The full P7 residual map above
continues to apply, including backward error/close, forward close, the
complete read pump, canonical cancellation/releases, signal actions and
pipe-promise settlement. Neither the all-finite safety theorem nor the two
fixed operational shapes establish progress or eventual shutdown.
