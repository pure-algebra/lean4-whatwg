# Receipts log of `READABLE-PG-DEFAULT`

This log holds the history of `docs/READABLE-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/READABLE-DAG.md`.

## Ten edges

Moved verbatim from `docs/READABLE-DAG.md` at `325d5d5`.

| Edge | Status | Required evidence / reason |
| --- | --- | --- |
| identity | required-open | exact ascriptions and constructor census; shared reason retraction; declaration snapshot joins every public declaration |
| construction | required-open | initial state equations; state fields first-order; no false non-coexistence invariant; later reachable-state and fresh-ID invariant proofs |
| semantics | required-open | staged transitions, answer admission and FIFO internal jobs; M1/M2 projection; external step and finite relational composition; later global job/host embedding |
| laws | required-closed | every quantified equation in DefaultContract passes; see the P4a landing receipt below; full-state and global scheduling obligations remain on their separate open edges |
| representation | required-open | queue and DyadicSize reuse, SizeAnswer reuse, shared error injection/retraction, retained enqueue frames; full stream and promise embedding remains open |
| counterexamples | required-closed | seventeen retained finite witnesses and corresponding checked production laws; `WS-READ-CE-001` through `017` close for this local projection only |
| bridges | required-open | full-state projection and host profile relation, including exact arithmetic vs binary64 and promise-reaction registration; no host equivalence is asserted by P4a |
| targets | not-applicable | P4a has no lowering or generated code; P11 owns that target obligation |
| trust | required-closed | all 94 named theorem axiom receipts, exhaustive root audit, narrow tests, full build, root gates, and independent implementation review pass; see the landing receipt |
| coverage | required-open | clause map below and test-side witnesses with frozen signatures; no census row becomes green merely from this packet |

## P4a landing receipt (coordinator, 2026-09-05)

Moved verbatim from `docs/READABLE-DAG.md` at `325d5d5`.

Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`, the coordinator's
cherry-pick of the independent breaker commit
`5f8067a1bb657b6573f2d1d96dc136a427e52afd`. This receipt accompanies the
implementation commit; the coordinator handoff records its exact head.
The integration prerequisite is `319e7448cee9b958abca579e6e262377e4c760da`.

The seven source modules are `Whatwg/Streams/Boundary/Exception.lean` and
`Whatwg/Streams/Readable/{State,DefaultController,DefaultReader,Step,Laws,Reentrancy}.lean`.
Stable declarations retain the families in the table above. Module splitting
puts the twelve external-step/composition theorems in `Step`, the sixty-two
branch and projection equations in `Laws`, and the twelve quantified
regressions in `Reentrancy`. `Exception` owns six adapter/identity theorems
and `State` owns the two numeric-view theorems. All 94 are ascribed by the
frozen test battery. The local private `Except` equality deriving helper in
`State` exports no global orphan instance. Three private next-read helpers
in `Laws` support the frozen `read_nextRead` statement.

Other files in the landing fence: `Whatwg/Streams.lean`, `WhatwgTest.lean`,
`WhatwgTest/Streams/Readable/DefaultContract.lean`,
`test/fixtures/trust-gate/known-red.txt`, `harness/readable/reentrancy.mjs`,
`test/counterexamples/REGISTER.md`, this graph, `PLAN.md`, and
`COORDINATION.md`. The frozen contract, axiom list, and seventeen independent
witness bodies are unchanged; no generated or vendor file is edited.

The sole battery repair indents the continuation argument of
`Data.Queue.empty` in `initial_eq` by two spaces. The previously absent
`State` hid that layout error during intended-red verification. The
`WhatwgTest/AGENTS.md` elaboration-repair allowance applies: no token in the
statement changes, and `git diff --ignore-all-space` for the battery is
empty. SHA-256 before the repair:
`8527abcf8d1acbd9fde0ce73308e03231421271481d30fe7d0812a8dc1d6bc3d`;
after the repair:
`d40222414247070167389468db14eaca9d4510bb76fcad63e8276201d223b2a4`.
The breaker acknowledged the repair and the independent reviewer checked it.

### Verification

All Lean commands used the pinned Lean 4.33.1 with `LEAN_NUM_THREADS=1`.
The following commands passed on the integrated implementation:

```text
lake --log-level=warning build WhatwgTest.Streams.Readable.DefaultContract WhatwgTest.Streams.Readable.DefaultAxiomReport WhatwgTest.Streams.Counterexamples.Readable.Default
lake --log-level=warning build
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest/Streams/Readable/DefaultAxiomReport.lean
lake env lean C:/Users/kokok/Dev/lean4-WHATWG-streams/WhatwgTest.lean
.lake/build/bin/vendorseal.exe
.lake/build/bin/citations.exe
.lake/build/bin/tyxmlschema.exe
.lake/build/bin/census.exe
.lake/build/bin/census.exe --report
.lake/build/bin/census.exe --standard infra
node harness/readable/reentrancy.mjs
git diff --check
```

The narrow build passed 63 jobs and all 204 exact ascriptions. The default
build passed 260 jobs. The 94 named theorem receipts comprise five
axiom-free proofs, thirty-six at `[propext]`, and fifty-three at
`[propext, Quot.sound]`; none reaches `Classical.choice` or a forbidden
axiom. The exhaustive root audit checked 121 modules and 7675 declarations,
including 1595 declarations in the Gates tooling tree, under R-11.
The two now-green battery entries were removed from the known-red list.

The vendor seal checked 206 files in five pinned trees; the citation and
schema drift gates passed. Both standard census projections passed their
drift checks. Infra still has no semantic numerator. Streams' report below
was produced at base `f4394d81d59739dd1410c6cc16df17ee147d6e1f` with this
implementation working tree; its numerator inputs are unchanged:

```text
WHATWG Streams (b9ba9f49) coverage: denominator 410; owned-with-green 12/410;
green 12, partial 6, absent 392; census 450 rows, 40 excluded
partial: op.blqs-size op.byte-length-queuing-strategy-size-function op.count-queuing-strategy-size-function op.cqs-size op.is-non-negative-number slot.queue-total-size
```

The host command passed four finite probes for `WS-READ-CE-013` through
`016` under Node `v22.23.2`, `node:stream/web`, Windows x64. The fixture
records exact Streams/reference/WPT pins, each tape, the observed components
of M1/M2, and reaction-registration assumptions. It executes neither the
pinned reference implementation nor WPT. It proves no general host relation.

### Independent review and residual obligations

The separate reviewer checked the frozen surface, source algorithms,
reentrancy laws, trust mechanisms, and claim scope without editing production
code. It found no landing blocker: captured continuations survive terminal
reentrancy; admitted size returns do not recheck the entry guard; all live
callback frames prevent job execution; return and settlement remain separate;
and fresh generated errors retain distinct identities. The coordinator ran
the commands above; this review is not a substitute for those receipts.

Only laws, counterexamples, and trust close at this landing. Identity stays
open for the generated declaration snapshot and joins. Construction stays
open for reachable-state and fresh-ID invariants. Semantics, representation,
and bridges stay open for the full-state, shared-allocation, global-job,
promise-object, and host-profile embeddings. Coverage stays open for the
clause map and test-side numerator witnesses. Targets are not applicable to
P4a and remain P11 work. In particular `Steps` composes external decisions
only; it does not yet interleave internal jobs or prove a global run law.

The seventeen retained attacks are closed by their linked production
equations for the named local projection. This does not close full P4 or
weaken the clause-map residuals. The next implementation depends on the P5a
writable breaker freezing its own packet, while the other breadth contracts
remain required before deeper readable/writable work.
