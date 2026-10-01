# Receipts log of `WRITABLE-PG-DEFAULT`

This log holds the history of `docs/WRITABLE-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/WRITABLE-DAG.md`.

## Default-writable proof graph (`WRITABLE-PG-DEFAULT`, P5a)

Moved verbatim from the status paragraph under the title of `docs/WRITABLE-DAG.md` at `325d5d5`; a current status paragraph replaces it there.

Status: frozen base packet, 2026-09-05. Contract:
`test/contracts/writable-default.contract.md`.
Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`.

## Ten assurance edges

Moved verbatim from `docs/WRITABLE-DAG.md` at `325d5d5`.

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact constructors/signatures, sentinel separation, shared reason/size/promise view receipts |
| construction | required-open | initial state and seeded supply laws, close-request XOR, promise identity retention and reachable cross-flight disjointness |
| semantics | required-open | explicit synchronous size/sink/signal returns, later settlements, deterministic FIFO jobs and relational finite composition |
| laws | required-closed | all 109 frozen local equations and two composed lifecycle statements pass; see the P5a landing receipt; whole-P5 and global obligations remain on their separate open edges |
| representation | required-open | P3 queue/size/answer reuse, shared exceptions, promise view dependency, first-order call stack, full-stream projection |
| counterexamples | required-closed | seventeen retained attack IDs and their linked production repair laws pass for this local projection; see the landing receipt |
| bridges | required-open | full writer/global scheduler/shared supply and host-profile embeddings; no host equivalence asserted by P5a |
| targets | not-applicable | this packet has no lowering; P11 owns target obligations |
| trust | required-closed | all 111 named theorem receipts, exhaustive root audit, narrow/full builds, executable gates and independent source review pass; see the landing receipt |
| coverage | required-open | full clause map and test-side frozen numerator witnesses; packet claims no changed coverage state |

## P5a landing receipt (coordinator, 2026-09-05)

Moved verbatim from `docs/WRITABLE-DAG.md` at `325d5d5`.

Base: `5f7cebef3c533c20ee1cc65558847fc1c1db5f46`, following the frozen
base/lifecycle/exact packets integrated as `5669062`, `47a86da`, and
`5f7cebe`. The verified P4a prerequisite is
`5121268d3c148678bfbe501b245881631524f2e5`. This receipt accompanies the
implementation commit; the coordinator handoff records its exact head.

The production fence is
`Whatwg/Streams/Writable/{Stream,Backpressure,DefaultController,DefaultWriter,Step,Laws,Lifecycle}.lean`.
The stable public declarations are exactly the families recorded above,
with the module allocation in the coordinator appendix. The seven modules
implement one post-successful-start stream with a fixed attached writer,
typed size/sink/signal returns, later sink answers, staged synchronous
continuations, retained identity-indexed promise cells, and deterministic
FIFO reaction jobs. `Reaches` composes actual external decisions and
internal ticks; unanswered callbacks remain live frontiers.

The remaining changed files are `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`test/fixtures/trust-gate/known-red.txt`, `harness/writable/reentrancy.mjs`,
the seventeen writable status/repair cells in `test/counterexamples/REGISTER.md`,
this graph, `PLAN.md`, and `COORDINATION.md`. Authored dependency records in
`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`, `docs/WHATWG-PACKAGE-PLAN.md`, and
the effects version comment in `lakefile.toml` are reconciled to the
existing lockfile and local Git objects. No dependency revision changes.
All nine frozen interface/law/receipt/witness file hashes match their
freeze ledgers. No frozen statement or witness body, generated projection,
vendored byte, or `lake-manifest.json` is edited.

### Verification

All Lean commands used Lean 4.33.1 with `LEAN_NUM_THREADS=1`:

```text
lake --log-level=warning build WhatwgTest.Streams.Writable.DefaultContract WhatwgTest.Streams.Writable.DefaultLaws WhatwgTest.Streams.Writable.DefaultAxiomReport WhatwgTest.Streams.Writable.LifecycleContract WhatwgTest.Streams.Writable.LifecycleAxiomReport WhatwgTest.Streams.Writable.InFlightExactContract WhatwgTest.Streams.Writable.InFlightExactAxiomReport WhatwgTest.Streams.Counterexamples.Writable.Default WhatwgTest.Streams.Counterexamples.Writable.InFlightPrecedence
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/DefaultAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/LifecycleAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Writable/InFlightExactAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/writable/reentrancy.mjs
git diff --check
```

The narrow build passes 72 jobs, including all 162 interface ascriptions,
109 local law signatures, the two composed signatures, and the two retained
witness modules. The full build passes 275 jobs. The 111 theorem receipts
comprise 23 axiom-free proofs, 34 at `[propext]`, 52 at
`[propext, Quot.sound]`, and the two lifecycle proofs at
`[propext, Classical.choice, Quot.sound]`. All are within R-11; none reaches
a forbidden axiom. The exhaustive root audit checks 133 modules and 9324
declarations, including 1595 in the Gates tooling tree. All seven now-green
battery modules have been removed from the known-red set.

The vendor seal checks 206 files in five pinned trees. The citation gate,
TyXML projection/emission drift checks, and Streams/Infra census gates pass.
The coverage report at the base above with this implementation working tree
prints the following unchanged numerator; these local proofs add no census
witness by themselves:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The Node fixture passes four finite observations under `node:stream/web`,
Node `v22.23.2`, Windows x64: ready replacement and close while a write is
pending; synchronous size-close reentrancy; pending-write abort reason and
settlement ordering; and successful in-flight close during erroring. The
fixture names its authority pins, tapes, reaction-registration assumptions,
and observable limits. It executes neither WPT nor the pinned reference
implementation. It establishes no general host relation or DB-04 embedding.

### Independent review and residual obligations

The separate reviewer checked the frozen equations against their source
anchors, the canonical carrier reuse, return/answer/reaction staging,
promise identity retention, and the final implementation/proof bodies.
The lifecycle proofs construct actual `Reaches.nil`/`Reaches.cons`
derivations and discharge each actual `Step` with ordinary `simp`/`rfl`;
their endpoints are inferred from those derivations. They quantify chunks
and reasons but fix the initial projection and the two tape shapes. They
are composed local regressions, not arbitrary-run invariants or host traces.

The review also checked the additive `hasInFlight_exact` correction. The
earlier unparenthesized equation remains unchanged; CE-017 demonstrates why
it cannot by itself exclude a write-only predicate. The parenthesized
whole-result equation now has its own exact checked signature and receipt.
The other sixteen retained attacks close through their linked production
equations. Independent source review found no remaining P5a landing blocker.

Only laws, counterexamples, and trust close here. Identity remains open for
generated public-declaration snapshot joins. Construction remains open for
valid initial/full-state projection, queue/request and close-sentinel
invariants, in-flight disjointness on reachable states, and shared fresh
allocation. Semantics, representation, and bridges remain open for global
call-stack/job order, ECMAScript promises and reaction registration,
full-stream/host embeddings, and DB-04 M1/M2 relations. Coverage remains open
for the clause map and test-side numerator witnesses. P11 owns targets.
Setup/start and writer acquire/release/reacquire are later full-P5 work.

The next breadth representative is the independently frozen P6a packet
`03547f1feb938d65898c47b4061faeb3f4bd9edf`, built on the P4/P5 canonical
states and shared P5 promise table. Its integration and implementation do
not close any of these remaining global obligations.

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/WRITABLE-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/WritableDefault.lean` and its projection `generated/graphs/WRITABLE-PG-DEFAULT.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30, with the trust row brought to the lane V landing of 2026-10-01 (R-V6). The P5a landing closed
laws, counterexamples and trust; full P5 stays open. Ruling R-V4 sets the
rule: an edge is `required-closed` only when every ground this document or a
ruling in `COORDINATION.md` states for keeping it open is discharged by
something named in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The generated public-declaration snapshot and its joins, which have no generator (debt D47) (P5a landing receipt) |
| construction | `required-open` | The valid initial and full-state projection, the queue/request and close-sentinel invariants, in-flight disjointness on reachable states, and shared fresh allocation. Setup/start and writer acquire/release/reacquire are later full-P5 work (P5a landing receipt) |
| semantics | `required-open` | The global call-stack and job order, ECMAScript promises and reaction registration, the full-stream and host embeddings, and the DB-04 M1/M2 relations (P5a landing receipt) |
| laws | `required-closed` | The 109 local law signatures (the 108 frozen stage/view laws and `hasInFlight_exact`) and the two composed lifecycle statements are proved in `Whatwg/Streams/Writable/Laws.lean` and `Lifecycle.lean`; the 111 named receipts print (P5a landing receipt) |
| representation | `required-open` | The global call-stack and job order, ECMAScript promises and reaction registration, the full-stream and host embeddings, and the DB-04 M1/M2 relations (P5a landing receipt). Since Q3, `UnitPromise`, `SinkAnswer`, `SinkReturn` and the promise slots of `State` are views of `Whatwg.Ecma262.Promise`, as the declaration table records |
| counterexamples | `required-closed` | `WS-WRITE-CE-001` to `WS-WRITE-CE-017` are `CLOSED` in `test/counterexamples/REGISTER.md` for this local projection, each through its linked production law (P5a landing receipt) |
| bridges | `required-open` | The full writer, global scheduler, shared supply and host-profile embeddings and the DB-04 M1/M2 relations; P5a asserts no host relation (P5a landing receipt) |
| targets | `not-applicable` | This packet has no lowering; P11 owns target obligations |
| trust | `required-closed` | The 111 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent source review passed (P5a landing receipt). Two of the receipts, `lifecycle_write_close` and `lifecycle_abort_rejection`, reached `Classical.choice` at `325d5d5`; slice V5 of lane V repaired them with no statement changed, and since that landing the axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1, R-V6) |
| coverage | `required-open` | The full clause map and the test-side numerator witnesses; the packet claims no changed coverage state (P5a landing receipt) |
