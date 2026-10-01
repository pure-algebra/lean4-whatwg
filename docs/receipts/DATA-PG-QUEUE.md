# Receipts log of `DATA-PG-QUEUE`

This log holds the history of `docs/DATA-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/DATA-DAG.md`.

## Queue-with-sizes proof graph (`DATA-PG-QUEUE`, phase P3)

Moved verbatim from the status paragraph under the title of `docs/DATA-DAG.md` at `325d5d5`; a current status paragraph replaces it there.

Status: **breaker-authored 2026-09-02, awaiting the `P3-R1` ruling.** This
document owns the proof graph, the existing-type rows, and the per-row census
map for the queue-with-sizes and queuing-strategy family. It states no
coverage number: `WhatwgTest/Audit/SpecCoverage.lean` owns coverage
states and `docs/SPEC-COVERAGE.md` owns the rules.

## 5. The ten edges

Moved verbatim from `docs/DATA-DAG.md` at `325d5d5`.

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | every row in section 3 names its census row id and that row's span digest from `generated/spec-algorithm-census.tsv`, and every quoted algorithm in the contract's section 4 was read first-hand from the pinned `index.bs` bytes at the offsets the census records |
| construction | `required-open` | D0 through D8 are frozen by name and signature in `WhatwgTest/Streams/Data/QueueContract.lean`; the module that declares them does not exist yet. Closes when the builder lands the fence and the battery goes green |
| semantics | `required-open` | the four queue operations and the two extraction algorithms have frozen definitions in the contract's D4 and D6; the apex statements are `enqueueValueWithSize_error_iff_not_admissible`, `dequeueValue_cons`, `peekQueueValue_agrees_dequeueValue`, `resetQueue_eq`, `extractHighWaterMark_error_iff`, `extractSizeAlgorithm_present` |
| laws | `required-open`, and **gated on `P3-R1`** | the invariant spine is `enqueueValueWithSize_wf`, which needs no carrier hypothesis at all, together with `sizeSum_cons`, `dequeueValue_wf` and `dequeueValue_clamp_unreachable_of_exact`, which are the only three of the ninety-nine frozen theorems that carry `SizeClass.Exact`. Under option (ii) those three are not applicable and this edge closes on `enqueueValueWithSize_wf` and the remaining order, FIFO and refusal laws alone |
| representation | `required-open` | the four representation decisions are frozen and argued: `Queue.WF` as a separate decidable `Prop` rather than a field invariant; `sizeSum` as a left fold; `peekQueueValue` returning `Option α` with no `SizeClass`; the three special constants as `SizeClass` fields. Each has a counterexample row forcing it |
| counterexamples | `required-closed` | `WS-DATA-CE-001` .. `WS-DATA-CE-010`, all `SEEDED` with proved green witnesses in `WhatwgTest/Streams/Counterexamples/Data/Queue.lean`; forty-four theorems, receipts `none` or `propext`. They close when the ruled instance rejects each attack |
| bridges | `not-applicable` | this packet claims no relation to a host implementation. The pinned WPT observations constrain which statements may be written and are recorded as host observations in the contract's section 5; none is a bridge theorem. `DATA-FB-ROUNDING` is where a bridge would have to live, and it is refused for now |
| targets | `not-applicable` | no generated code. Lowering to TypeScript is `RS-5` in `docs/REIFICATION-STRATEGY.md` and is not opened by this packet |
| trust | `required-open` | the counterexample module's receipts are measured and inside the semantic ceiling; `lake exe trustselftest` passes with the declared red set matching the observed red set exactly. **Open:** the ninety-nine production receipts, which arrive with the builder in `WhatwgTest/Streams/Data/QueueAxiomReport.lean` |
| coverage | `required-open` | the per-row map in section 6 is a proposal. No coverage state changes until the builder's witnesses land and `WhatwgTest/Audit/SpecCoverage.lean` is edited under its own claim, as `docs/SPEC-COVERAGE.md` requires |

## Landing (coordinator, 2026-09-02)

Moved verbatim from `docs/DATA-DAG.md` at `325d5d5`.

The P3 builder landed the frozen surface with all 99 theorems proved and
zero edits to the battery: 447 declarations compiled from the two fenced
modules, 375 axiom-free, 70 at `[propext]`, 2 at `[propext, Quot.sound]`
(`sizeSum_append_singleton`, `enqueueValueWithSize_wf`, through core's
`List.foldl_append`). The trust self-test reports an empty declared red set.

Module allocation for the `P3-R1` instance: `Whatwg/Streams/Data/DyadicSize.lean`,
imported from the root. Twelfth existing-type row: `Whatwg.Streams.Data.DyadicSize`,
canonical carrier for `Size` at this pin, the dyadic rationals with the
exponent fixed at 1074 (`finite u` denotes `u · 2^(-1074)`; every finite
binary64 is representable; `nan`, `posInfinity`, `negInfinity` are
constructors), with `DyadicSize.classified`, `ordered`, `exact`, and
`admissible_iff`; disposition `owned`; assurance route: this graph's
representation edge. Two frozen statements carry a hypothesis their proofs do
not use (`dequeueValue_clamp_unreachable_of_exact` needs no `Classified`);
the statements are unweakened.

Edge states after landing: identity, construction, semantics, laws,
representation, counterexamples, trust, and coverage are `required-closed`
by the receipts above and the closed `WS-DATA-CE-001`..`010` rows; bridges
and targets remain `not-applicable` at this stratum. The census rows this
packet turns `green` (12) and `partial` (6) are the builder's proposal in §6
and land through the coverage numerator in a separate packet.

## Coverage landed (coordinator, 2026-09-02)

Moved verbatim from `docs/DATA-DAG.md` at `325d5d5`.

The §6 proposal landed as 12 `green` and 6 `partial`, reached step by step
from the pinned bytes by the coverage seat, with 55 witness theorems (27
axiom-free, 28 at `[propext]`). Two proposed witnesses were rejected:
`CountQueuingStrategy.make_does_not_validate` (statement identical to
`make_highWaterMark`; `make_accepts_nan` carries the content) and
`realm_identity_refused` (its statement is `congrArg` and witnesses no step;
`DATA-FB-REALM` alone carries those steps). The §3 row for `slot.queue`
attributed the value-with-size sentence to the slot span; that span is the
`[[queue]]` definition in the default controller's slot table, and the
sentence lives in the queue-with-sizes section; the state is unaffected.
The coverage edge closes. The block at this landing:
`denominator 410; owned-with-green 12/410; green 12, partial 6, absent 392;
census 450 rows, 40 excluded`.
