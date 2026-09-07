# Writable representative attacks (P5a)

Status: witnesses verified; frozen base packet. Graph: `WRITABLE-PG-DEFAULT`.
Base: `f4394d81d59739dd1410c6cc16df17ee147d6e1f`.

The executable source is `WhatwgTest/Streams/Counterexamples/Writable/Default.lean`.
Each theorem is an independent finite fixture refuting a competing transition or
observation rule. These fixtures are not another global promise runtime and do
not establish the production transition relation, global reachability, or host
behavior. The quantified repair is the corresponding exact ascription in
`WhatwgTest/Streams/Writable/DefaultLaws.lean`.

Observation scope: local sink-input and ordered writable candidate views.
The sink-input view contains foreign write invocations only. Its mapping into
DB-04 M1, and the ordered view's mapping into DB-04 M2, remain required-open.
Identity/queue/callback-marker attacks concern intermediate slots used by those
views; finite fixture equality is not an external-equivalence claim.

| ID | Lean witness | Forced quantified production law | Competing rule |
| --- | --- | --- | --- |
| `WS-WRITE-CE-001` | `ce001_reentrant_size_close` | `tick_afterSize_closing` | Size callback closes before admission. |
| `WS-WRITE-CE-002` | `ce002_thrown_size_existing_error` | `tick_afterSize_errored` | Abrupt size result yields an already stored error. |
| `WS-WRITE-CE-003` | `ce003_closing_before_erroring` | `tick_afterSize_closing` | Closing precedes erroring after size. |
| `WS-WRITE-CE-004` | `ce004_ready_identity` | `updateBackpressure_true` | Replacing ready retains older promise cells. |
| `WS-WRITE-CE-005` | `ce005_close_keeps_backpressure` | `tick_beginClose_admitted` | Close fulfills ready while backpressure remains true. |
| `WS-WRITE-CE-006` | `ce006_inflight_queue_retained` | `tick_advance_write` | In-flight write keeps its chunk and total size. |
| `WS-WRITE-CE-007` | `ce007_write_before_ready` | `tick_write_fulfilled` | Current write fulfills before ready on drainage. |
| `WS-WRITE-CE-008` | `ce008_close_clear_after_return` | `invokeSink_eq; attachSink_eq` | Sink close invocation precedes algorithm clearing. |
| `WS-WRITE-CE-009` | `ce009_abort_entry_slots` | `tick_finishErroring; invokeSink_eq; attachSink_eq` | Pending abort removal precedes invocation; clearing follows return. |
| `WS-WRITE-CE-010` | `ce010_first_stored_error` | `tick_write_rejected; tick_dealRejection` | In-flight rejection retains the earlier stored reason. |
| `WS-WRITE-CE-011` | `ce011_close_wins_erroring` | `tick_close_fulfilled` | Close success settles close, abort, closed; prior ready rejection remains. |
| `WS-WRITE-CE-012` | `ce012_signal_terminal_recheck` | `tick_afterSignal_terminal` | Post-signal terminal recheck precedes alias reuse. |
| `WS-WRITE-CE-013` | `ce013_nested_abort_identity` | `tick_beginAbort_signaled; tick_afterSignal_existing` | Signal is one-shot and live pending abort retains identity. |
| `WS-WRITE-CE-014` | `ce014_zero_size_close` | `tick_beginClose_admitted` | Close sentinel has zero size. |
| `WS-WRITE-CE-015` | `ce015_answer_admission` | `acceptAnswer_other` | Invoking/queued operations reject settlement answers. |
| `WS-WRITE-CE-016` | `ce016_jobs_wait_for_callback` | `externalFrontier_eq; tick_foreign_marker` | Reaction jobs wait behind live callback markers. |

Pinned reading aids: `vendor/wpt-480fdfcd/streams/writable-streams/reentrant-strategy.any.js`
and `aborting.any.js`. They motivated cases about nested size, pending ready
references, error reason precedence, and in-flight close/abort ordering.
No WPT or host executable was run by this breaker. The pinned specification
algorithms and the graph's byte-span anchors remain the semantic authority.

The coordinator ran `harness/writable/reentrancy.mjs` on Node v22.23.2,
win32 x64, on 2026-09-05. Its four finite host probes cover CE001,
CE004/005, CE011, and observable portions of CE009/010/013. They report fresh ready
identity with old references retained, close fulfilling current ready while
desiredSize is zero, size closing before the outer write is admitted, pending
abort identity reuse, one signal, and distinct current-write/stored abort
reasons. A pending sink close fulfilled after abort settles close, abort and
closed in that order, retains the rejected ready identity, and never calls
sink.abort. Internal backpressure, pendingAbort and algorithm slots were not
observed. The host probe is a coordinator-owned integration file and is not
copied into this breaker commit. No simulation, coverage or host-equivalence
claim follows from that finite output.

The Lean command, run sequentially in the breaker worktree, was:

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Writable/Default.lean
```

Result: exit 0, all 16 finite fixture theorems. Twelve have no axioms;
CE005, CE006, CE014 and CE015 use only `propext`. The inherited artifacts
come from main `5121268d3c148678bfbe501b245881631524f2e5` after its full
build passed. They are compile infrastructure, not writable proof evidence.
The initial witness attempt exposed alias-qualified constructors and an
unavailable decidable equality on a test result; the draft was repaired and
the command above rerun successfully. The final sentinel witness compares
the returned total-size projection. No failed elaboration is proof evidence.

The separate `LifecycleContract.lean` addendum supplements the snapshot
fixtures with two quantified fixed-trace obligations. `lifecycle_write_close`
connects retained ready identities, pending backpressure and final close
ordering. `lifecycle_abort_rejection` connects in-flight write rejection,
queued-write failure, abort completion and the earlier stored error. These
are production theorem obligations with explicit Reaches sequences; their
own intended-red commands and scope are in the contract addendum. They do
not turn the 16 finite fixtures into whole-program executions or remove any
stage law, counterexample row, or remaining global embedding obligation.

## WS-WRITE-CE-017 — equality/Boolean-OR precedence

`WhatwgTest/Streams/Counterexamples/Writable/InFlightPrecedence.lean` imports
only Init. `weakLaw_parse` confirms that `answer = writeFlag || closeFlag`
as a proposition elaborates to `(decide (answer = writeFlag) || closeFlag) = true`.
`ce017_ignored_close_passes_weak` checks all Boolean flag pairs: returning only
writeFlag satisfies that weaker predicate, but fails the parenthesized exact
equation at writeFlag false and closeFlag true. This is a finite logical
counterexample to the old acceptance condition, not a claim that production
has this defect. The inspected production definition already returns the
full disjunction. The added quantified repair is `hasInFlight_exact`.

On the coordinator-granted exclusive window, under the pinned Lean4.33.1:

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Writable/InFlightPrecedence.lean
```

Final result: exit 0; both the parse theorem and CE017 are axiom-free.
Initial draft attempts needed explicit unfolding of test-local Prop wrappers
before finite Boolean case proofs; their failed elaborations are not evidence.
The final statements are unchanged by that proof repair. No host probe or
full-stream reachability claim is involved.
