# Transition-kernel attacks (W8a)

Status: frozen with the W8a packet, 2026-10-01, by the W8a breaker seat on
branch `review/w8a-kernel-breaker`. Owning contract:
`test/contracts/transition-kernel.contract.md` (ruling R-W4). Witness source
is in two modules and is linked here, not reproduced:

- `WhatwgTest/Streams/Counterexamples/Kernel/Path.lean` (rows 001 to 004), red
  until slice W8a.1 lands `Whatwg.Streams.Kernel`;
- `WhatwgTest/Streams/Counterexamples/Kernel/Invariants.lean` (rows 005 and
  006), red until slice W8a.3 lands the invariants.

Both are declared in `test/fixtures/trust-gate/known-red.txt`. Each row
attacks a hypothesis or a form the packet freezes and shows, with a
kernel-checked witness, that the statement without it is false. Rows 001 and
003 use toy relations of the `Breaker` namespace and import nothing they
attack; row 002 has a toy half and a production half; row 004 is an
elaboration probe against production `Writable.Step`; rows 005 and 006 are
mutants of production operations, defined in the witness module only. None is
a host observation, and none names an observation mask: the kernel laws hold
of every one-step relation, and the invariants concern the local derivation
closures.

| ID | Attacked statement | Witness (module, names) | What it forces |
| --- | --- | --- | --- |
| `WS-KERNEL-CE-001` | `Kernel.Path.deterministic` holds of every one-step relation, so `Kernel.Deterministic` is decoration | `Path.lean`: `Breaker.anyStep` (every `Bool` steps to every `Bool` under `()`); `ce001_not_deterministic`, `ce001_two_ends` (the label list `[()]` from `false` ends at both `false` and `true`), `ce001_unconditional_false` | the hypothesis `Kernel.Deterministic step` of `Kernel.Path.deterministic`; `Kernel.graph_deterministic` is why every partial-function graph meets it |
| `WS-KERNEL-CE-002` | the fixed-external-word comparability law needs no exclusivity, so it transfers from the configuration to the local Writable machine | `Path.lean`, toy half: `Breaker.forkTick`/`forkAccept` (at `0`, `tick` goes to `1` and the decision `()` to `2`), `ce002_fork_not_exclusive`, `ce002_left` (`0 → 1 → 3`), `ce002_right` (`0 → 2 → 4`), `ce002_comparability_false` (same external word `[()]`, both ends stuck and distinct, closed with `Kernel.silent_stuck`); production half: `ce002_writable_not_exclusive : ¬ Kernel.Exclusive (@Writable.tick Unit Unit) Writable.decide` | the hypothesis `Kernel.Exclusive tick accept` of `Kernel.prefix_comparable` and `Kernel.normalized_unique`; no per-calculus exclusivity is frozen, only `Semantics.Ordering.exclusive` |
| `WS-KERNEL-CE-003` | under exclusivity two derivations with one external word end at one state, normalized or not | `Path.lean`: `Breaker.countTick`/`countAccept` (`0` ticks to `1`, no decision admitted), `ce003_exclusive`, `ce003_unnormalized_false` (`[]` ends at `0`, `[none]` at `1`), controls `ce003_start_not_normalized` and `ce003_comparable` | the two hypotheses `tick t = none` and `tick u = none` of `Kernel.normalized_unique`; the configuration's `Normalized` frontier of Decision 8 |
| `WS-KERNEL-CE-004` | the two-stage bridge can be the equation of relations `Writable.Step = Kernel.Graph (Kernel.stage Writable.tick Writable.decide)`, proved by `rfl` | `Path.lean`: the `#check_failure` of that `rfl` at an open label, under `#guard_msgs (drop info)`, with the two closed-label `rfl` controls beside it | the pointwise iff `step_iff_stage`, proved by `cases d`, for Writable, Transform, Piping and the configuration; Readable alone has the equation `step_eq_graph`, by `rfl` |
| `WS-KERNEL-CE-005` | the readable queue invariant survives a `finishEnqueue` that appends the chunk without `Data.enqueueValueWithSize` | `Invariants.lean`: `Breaker.finishEnqueueAppend`; at `readable0` (the readable machine after start, high-water mark one grid unit) `ce005_reference_wf` (production keeps `[[queueTotalSize]]` equal to the sum) and `ce005_mutant_breaks_wf` (the mutant leaves the total at zero beside one entry of one unit), both by `decide`; `ce005_mutant_breaks_step_law` | `Readable.step_queueInv` is a law of the production `finishEnqueue`, whose only queue growth is `enqueueValueWithSize` |
| `WS-KERNEL-CE-006` | registration freshness survives a `register` that reuses `nextObserver - 1` as the new identity | `Invariants.lean`: `Breaker.registerReuse`; `config1` is one production `observe` step from `initial` (`ce006_config1_step`), fresh by the frozen theorems (`ce006_config1_fresh`); `ce006_reference_ids` (production second registration: ids `[0, 1]`), `ce006_mutant_ids` (mutant: `[0, 0]`), `ce006_mutant_breaks_step_law` | `Semantics.Ordering.step_registrationsFresh`, and the cursor clause of `RegistrationsFresh` that makes freshness inductive |

## Notes on the witnesses

Row 002's production half is the design's `Writable.not_exclusive` (design
section 2.10), proved there in `StatementsProbe.lean` and copied here with its
state: the initial writable machine with one queued sink job `⟨.write, 0,
.fulfilled⟩` and an empty control stack, where `Writable.tick` moves the job
to the control stack and `Writable.decide` still admits `queryReady`. The toy
half is this seat's: it shows the conclusion of `prefix_comparable` false, not
only its hypothesis.

Row 004 records an elaboration failure, not a kernel fact. The observed
diagnostic, from `#check_failure` of the term in a scratch file against the
reinstated prototype, is `Type mismatch: rfl has type ?m = ?m but is expected
to have type Writable.Step s d t = Kernel.Graph (Kernel.stage Writable.tick
Writable.decide) s d t`. It is not pinned, because a metavariable index is in
it; the two closed-label controls in the same module use the same subterms, so
the module cannot be green while the names are unknown, and the probe cannot
pass for that reason once they exist. If a later toolchain identifies the two
matchers, the probe reports an unexpected success and the row needs a ruling;
the pointwise bridge stays true either way.

Rows 005 and 006 compute with `decide` and `rfl` on concrete states. Row 005
uses one grid unit (`Data.DyadicSize.finite 1`) rather than `Readable.sizes.one`,
which is `2 ^ 1074` units and does not reduce under `decide`.

## Command and receipts

Against the design's Route B prototype reinstated in this seat's worktree
(uncommitted, removed before the last commit):

```powershell
lake env lean WhatwgTest/Streams/Counterexamples/Kernel/Path.lean
lake env lean WhatwgTest/Streams/Counterexamples/Kernel/Invariants.lean
```

Both exited 0, and the full `lake build` with both modules imported into the
test root passed the axiom gate (section 10 of the contract). Against `main`
at `b0d35e2` both fail with unknown identifiers only, as declared.
