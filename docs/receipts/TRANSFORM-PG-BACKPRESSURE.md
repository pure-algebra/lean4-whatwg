# Receipts log of `TRANSFORM-PG-BACKPRESSURE`

This log holds the history of `docs/TRANSFORM-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/TRANSFORM-DAG.md`.

## Ten edges

Moved verbatim from `docs/TRANSFORM-DAG.md` at `325d5d5`.

| Edge | Status | Required evidence |
| --- | --- | --- |
| identity | required-open | exact signatures and constructor census; generated public declaration joins |
| construction | required-open | post-start/count-profile constructor, fresh internal IDs, subscription uniqueness, valid native ports, reachable-state invariants |
| semantics | required-open | return/answer/reaction distinction, one ordered cross-component reaction queue, native ports hidden from foreign decisions, finite relational composition; global adoption-job embedding later |
| laws | required-closed | all 115 frozen local equations and three composed statements pass; see the P6a landing receipt; global/reachable-state obligations stay on their open edges |
| representation | required-open | P3/P4/P5 reuse and named cell adapter preserving prior cells/IDs; no stored function or third runtime |
| counterexamples | required-closed | fourteen retained WS-TRANS finite mutants and linked production repair laws pass; the register records exact local scope, without promoting a snapshot to full execution |
| bridges | required-open | exact P4 pull-frame and P5 write-frame realization laws; full profile, arithmetic and host correspondences later |
| targets | not-applicable | this representative generates no target code; P11 owns lowering |
| trust | required-closed | all 118 theorem receipts, exhaustive root audit, narrow/full builds, executable gates and independent implementation/proof review pass; see the landing receipt |
| coverage | required-open | clause map and test-side numerator witnesses; this packet adds no coverage claim |

## Review ledger

Moved verbatim from `docs/TRANSFORM-DAG.md` at `325d5d5`.

Preliminary independent design review accepts the named local adapter of the
P5 table without requiring a broad shared-carrier refactor. It requires prior
cell/ID retention laws, internal-ID filtering confined to the transform view,
OLD versus NEW subscriptions, deterministic reaction insertion, actual P4
pull identity routing, and no user frontier at reserved native ports. This is
design feedback, not acceptance of an exact surface or implementation.

The staged-equation review then checked the concrete cell/notification,
source/sink adapter, callback return, and error/termination equations. It
required strict saved-depth draining (undershoot has no transition), live
callback suspension behind input-size as well as transformer frames, and
actual composed canonical P4/P5 runs. It also found the positive-readable-HWM
initial-state issue: staging bare `Readable.initial` leaves capacity-driven
pull absent. The revised `initial` stages `Readable.callPullIfNeeded`, so its
native pull frame blocks external calls until serviced. `WS-TRANS-CE-014`
and a positive-capacity run retain that correction. The fourteen finite
witnesses pass with twelve axiom-free receipts and `propext` only for CE-005
and CE-014. The three composed production runs remain intended red.

Final independent review accepted the 112 interface ascriptions, 118 exact
law/receipt-name join, observation filtering, three composed runs, all thirteen
span hashes, file fence, and trust scan. The last documentation correction
clarifies that termination preserves queued output for later delivery while
writable erroring occurs immediately after the readable close operation.
Final-byte verification and immutable packet handoff are recorded in the
contract ledger; implementation and all required graph edges remain open.

## P6a landing receipt, 2026-09-05

Moved verbatim from `docs/TRANSFORM-DAG.md` at `325d5d5`.

### Base, packet and file fence

The implementation base is `e66876721f55f35ef09f1114a24487f57e794097`.
The head is the commit carrying this receipt; its exact hash is supplied in
the coordinator handoff. P5a landed at
`e4d053a52f6fc374e8657934df81d0ecc059b945`. The independent P6a freeze
`03547f1feb938d65898c47b4061faeb3f4bd9edf` was integrated as `5d95212`.
Breaker repair `c420aa9d5fd0433489efa3d60723ce469ea5002d`, integrated as
`e668767`, adds only the two explicit type annotations recorded in the
contract's additive elaboration ledger. No frozen proposition branch,
premise, observation or witness changed.

The production fence is the seven modules `Stream.lean`, `Backpressure.lean`,
`DefaultController.lean`, `Step.lean`, `Observation.lean`, `Laws.lean` and
`Runs.lean` under `Whatwg/Streams/Transform/`. The first five implement only
the surface frozen in the declaration-role table. `Laws.lean` exports the
115 frozen local theorem names; `Runs.lean` exports the three frozen
composed names. The production and test roots reach every new module and
all four P6 test modules.

The other changed files are `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`harness/transform/backpressure.mjs`, `test/fixtures/trust-gate/known-red.txt`,
the P6 status/repair cells in `test/counterexamples/REGISTER.md`, this graph,
`PLAN.md` and `COORDINATION.md`. No dependency, vendor or generated file
changes in this implementation slice.

All six frozen files were compared with the separate breaker worktree at
`c420aa9`; only that worktree's coordination file was dirty. The contract,
interface battery, law battery, axiom battery, finite witness module and
attack descriptions match byte-for-byte. In particular, the repaired law
battery retains SHA-256
`D939DE85318FC675E3685708DC5061FDC2E437C34DE01272D3D0FEBFC4E3BF4C`.

### Implementation and observation boundary

The count-output state embeds actual P4 readable and P5 writable states.
P5 owns the promise table and allocations; subscriptions retain the exact
old/new identity across backpressure changes. Native pull and write ports
execute the canonical component continuations. Foreign transformer returns
and eventual answers are separate decisions; coupled jobs execute in the
frozen local FIFO order and cannot run inside the suspended transform body.
Saved writable depths stage reentrant work without accepting an undershoot.

The three `Transform.Reaches` proofs construct actual `Step` derivations:

- `coupled_write_read_enqueue`: a blocked write, read demand, delivered
  output, successful transform return, exact write/ready settlement and
  old/new backpressure identities.
- `coupled_error_during_transform`: controller error during an active body,
  rejection of the component outcomes/queries with the exact reason, and
  successful return of the already-active write after algorithms clear.
- `coupled_positive_readable_capacity`: canonical successful-start native
  pull permits a write and queued output before any read.

These proofs quantify input/output values, the foreign reason where used,
and the promise seed, but fix the count profile and three finite tape shapes.
They use `Reaches.nil`/`Reaches.cons` and ordinary `simp`/`rfl`, without a
fuel-bound interpreter as the judgment. They are composed local regressions,
not arbitrary-run invariants. The output and ordered observations derive
from actual component events; their DB-04 M1/M2 embedding is still open.
The pending backpressure cell at the error-run endpoint is retained exactly;
it is not silently converted into a settled or completed global execution.

### Verification

The exclusive main verification window used the pinned Lean 4.33.1
toolchain and the following commands:

```powershell
$env:LEAN_NUM_THREADS = '1'
lake --log-level=warning build WhatwgTest.Streams.Transform.BackpressureContract WhatwgTest.Streams.Transform.BackpressureLaws WhatwgTest.Streams.Transform.BackpressureAxiomReport WhatwgTest.Streams.Counterexamples.Transform.Backpressure
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Transform/BackpressureAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/transform/backpressure.mjs
git diff --check
```

The normal narrow build passes 71 jobs, including all 112 interface
ascriptions, all 118 theorem signatures/receipts and the fourteen retained
finite witnesses. The full build passes 287 jobs. The 118 named theorem
receipts comprise eight axiom-free proofs, 33 at `[propext]`, 73 at
`[propext, Quot.sound]`, and four at `[propext, Classical.choice, Quot.sound]`.
The last group is `freshInternal_new` and the three composed run proofs.
All are within R-11. The exhaustive root audit checks 141 modules and 10596
declarations, including 1595 in the Gates tooling tree. The known-red set
is empty again.

The vendor seal checks 206 files in five pinned trees; the citation gate,
TyXML schema/emission drift checks, and Streams/Infra census gates pass.
At base `e66876721f55f35ef09f1114a24487f57e794097` with this implementation
working tree, the report prints:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The Node fixture passes four finite observations under `node:stream/web`,
Node `v22.23.2`, Windows x64: read demand unblocks transform but does not
fulfill a write while the transform result is pending; an active transform
can return successfully after controller error; positive readable capacity
permits output before the first read; and zero/multiple outputs plus
termination retain queued chunks in order. The fixture records its exact
pins, tapes, observer assumptions and limits. It executes neither WPT nor
the reference implementation and compares no host run against a Lean run.
Its counterexample links name only the exercised behavioral projections.

### Independent review and remaining obligations

Independent review checked the core operations against their frozen
statements and source anchors, canonical component reuse, return/answer/job
staging, retained identities, saved-depth control and observation filtering.
The subsequent proof review checked the exact 118-name join, all three
composed derivations, claim scope and the host fixture. Source-anchor
corrections and a host counterexample-label correction were applied without
changing a theorem statement or proof boundary.

Only laws, counterexamples and trust close here. Identity remains open for
generated public-declaration snapshot joins. Construction remains open for
valid ports, fresh/shared allocation, unique subscriptions, retained callback
identity, trace-prefix validity and inductive reachable-state invariants.
Raw states can violate these conditions; the local equations do not assert
that every such state is a valid stream. Semantics, representation and
bridges remain open for full-state embeddings, global ECMAScript job order,
promise adoption/registration, numeric boundaries and host relations.

Full setup/start, arbitrary output-size callbacks, flush, cancel and the
complete close/abort lifecycle remain owned/open. No absent intrinsic
algorithm becomes a foreign body or a refusal. Coverage remains open for
the clause map and test-side numerator witnesses. The next P7a breadth
packet is a separate requirements/realizer shutdown fragment; it cannot
claim full pipe finalization before the missing canonical release and
cancellation operations exist.

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/TRANSFORM-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/TransformBackpressure.lean` and its projection `generated/graphs/TRANSFORM-PG-BACKPRESSURE.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30, with the trust row brought to the lane V landing of 2026-10-01 (R-V6). P6a landed on
2026-09-05 with implementation `afb57f8`, closing laws, counterexamples and
trust; full P6 stays open. Ruling R-V4 sets the rule: an edge is
`required-closed` only when every ground this document or a ruling in
`COORDINATION.md` states for keeping it open is discharged by something named
in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The generated public-declaration snapshot and its joins, which have no generator (debt D47) (P6a landing receipt) |
| construction | `required-open` | Valid ports, fresh and shared allocation, unique subscriptions, retained callback identity, trace-prefix validity and inductive reachable-state invariants; raw states can violate them (P6a landing receipt) |
| semantics | `required-open` | Full-state embeddings, global ECMAScript job order and promise adoption and registration (P6a landing receipt) |
| laws | `required-closed` | The 115 frozen local equations in `Whatwg/Streams/Transform/Laws.lean` and the three composed runs in `Runs.lean` are proved; the 118 named receipts print (P6a landing receipt) |
| representation | `required-open` | Full-state embeddings, global ECMAScript job order, promise adoption and registration, and numeric boundaries (P6a landing receipt). Since Q3, subscriptions are a view of `Whatwg.Ecma262.Promise.Reactions`, and Q4 landed the `notify`, `settle` and `runJob` bridges, which are `PROMISE-PG-FIRST` bridge evidence |
| counterexamples | `required-closed` | `WS-TRANS-CE-001` to `WS-TRANS-CE-014` are `CLOSED` in `test/counterexamples/REGISTER.md` with their linked production laws, for the exact local scope the register records (P6a landing receipt) |
| bridges | `required-open` | Full-state embeddings, global ECMAScript job order, promise adoption and registration, numeric boundaries and host relations; the four Node observations are finite host observations, compared with no Lean run (P6a landing receipt) |
| targets | `not-applicable` | This representative generates no target code; P11 owns lowering |
| trust | `required-closed` | The 118 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent implementation and proof review passed (P6a landing receipt). Four of the receipts, `freshInternal_new`, `coupled_write_read_enqueue`, `coupled_error_during_transform` and `coupled_positive_readable_capacity`, reached `Classical.choice` at `325d5d5`; slice V5 of lane V repaired them with no statement changed, and since that landing the axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception (R-V1, R-V6) |
| coverage | `required-open` | The clause map and the test-side numerator witnesses; the packet adds no coverage claim (P6a landing receipt) |
