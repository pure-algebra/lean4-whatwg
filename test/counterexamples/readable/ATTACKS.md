# Default-readable adversarial packet

All witnesses are retained in
`WhatwgTest/Streams/Counterexamples/Readable/Default.lean`, namespace
`WhatwgTest.Streams.Counterexamples.Readable.Breaker`. They are finite
independent mutant discriminators, not production proofs or host results.
The production laws are the separate, frozen ascriptions in
`WhatwgTest/Streams/Readable/DefaultContract.lean`.

| ID | Witness | Mutant | Production obligation |
| --- | --- | --- | --- |
| WS-READ-CE-001 | `ce001_pending_skips_size` | call size before testing pending reads | `beginEnqueue_pending`, `pending_read_skips_size`; ENQUEUE skips size entirely on direct delivery |
| WS-READ-CE-002 | `ce002_queue_is_not_stack` | prepend instead of append | `finishEnqueue_value`, `read_queued_eq`, `fifo_close_m1_m2`; use P3 FIFO queue |
| WS-READ-CE-003 | `ce003_close_must_drain` | immediately close with chunks queued | `close_deferred`, `fifo_close_m1_m2` |
| WS-READ-CE-004 | `ce004_closed_before_last_chunk` | settle final chunk before closed promise | `read_queued_eq`, `fifo_close_m1_m2`; DEQUEUE invokes STREAMCLOSE before chunk steps |
| WS-READ-CE-005 | `ce005_zero_hwm_pending_read` | infer demand only from desired size | `shouldCallPull_iff`, `pending_read_skips_size` |
| WS-READ-CE-006 | `ce006_pull_again_coalesces` | overlap pulls when already pulling | `callPullIfNeeded_busy` |
| WS-READ-CE-007 | `ce007_fulfillment_rechecks_demand` | treat pullAgain as unconditional permission | `reactPull_fulfilled`, `callPullIfNeeded_idle` |
| WS-READ-CE-008 | `ce008_nested_size_is_lifo` | resume nested size calls FIFO | `resumeSize_size`, `reentrant_enqueue_lifo` |
| WS-READ-CE-009 | `ce009_closed_can_retain_chunk` | recheck CanCloseOrEnqueue after size returns | `finishEnqueue_value`, `reentrant_close_keeps_chunk`, `reentrant_error_keeps_chunk` |
| WS-READ-CE-010 | `ce010_read_during_size` | reconsider direct delivery after size creates a read | `reentrant_read_does_not_recheck` |
| WS-READ-CE-011 | `ce011_first_error_survives` | replace stored error with later throw/range error | `error_terminal`, `reentrant_error_then_throw`, `reentrant_error_then_invalid` |
| WS-READ-CE-012 | `ce012_answers_are_queued` | run a foreign answer immediately, bypassing queued jobs or a synchronous size frame | `acceptPullAnswer_waiting`, `runPullJob_suspended`, `runPullJob_cons` |
| WS-READ-CE-013 | `ce013_pull_error_precedes_chunk` | settle queued read before pull callback reenters and errors | `read_queued_eq`, `pull_reentrant_error_before_chunk` |
| WS-READ-CE-014 | `ce014_pull_can_change_queue` | assume queue is still the immediate dequeue result after pull returns | `pull_reentrant_enqueue_changes_queue` |
| WS-READ-CE-015 | `ce015_nested_read_overtakes` | require earlier read ID to settle before nested later read | `pull_reentrant_read_overtakes` |
| WS-READ-CE-016 | `ce016_generated_errors_are_distinct` | identify all model-generated range errors with a single tag | `Exception.rangeError_eq_iff`, `finishEnqueue_invalid`, `nested_invalid_sizes_fresh_errors` |
| WS-READ-CE-017 | `ce017_query_is_visible` | define M2 as settlements only and erase desiredSize queries | `queryDesiredSize_eq`, `queryDesiredSize_m2`, `observeM2_toM1` |

The pinned WPT `readable-streams/reentrant-strategies.any.js` contains named
cases `enqueue() inside size() should work`, `close() inside size() should
not crash`, `close request inside size() should work`, `error() inside
size() should work`, and `read() inside of size() should behave as expected`.
The same pin's `bad-strategies.any.js` distinguishes the already-stored
controller error from a size callback's later throw and later Infinity
return. These are source witnesses at the pinned corpus commit, not claims
that a host was run. `docs/READABLE-DAG.md` owns the exact specification
algorithm digests supporting the production obligations.

The coordinator's `harness/readable/reentrancy.mjs` exercises CE-013 through
CE-016 under Node v22.23.2, win32 x64. Its result is a finite host observation
under that named profile. The pinned specification remains the authority;
the independent Lean mutant witnesses and production laws remain separate.
The pull callbacks in CE-014/015 return unanswered promises intentionally;
these are live frontiers, not successful terminal runs.

M1 can hide the stranded queue after reentrant close; CE-009 therefore also
pins an internal-slot result. M2 alone does not record source invocations;
CE-001 and CE-006 additionally inspect the first-order effect trace. This
distinction prevents a weaker observation from being passed off as the
whole algorithm.

Verification command (one thread and a memory cap):

```text
lake env lean -M2048 WhatwgTest/Streams/Counterexamples/Readable/Default.lean
```

Expected: seventeen kernel-checked finite mutant discriminators within the
root R-11 ceiling. Measured axiom results are recorded in the owning contract
at freeze; an allowed `propext` dependency is not an empty receipt.
