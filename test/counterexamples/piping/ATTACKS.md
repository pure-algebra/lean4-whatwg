# P7a forward-shutdown attacks

Status: verified breaker witnesses, 2026-09-05; freeze is recorded in the
owning contract. All witness source is in
`WhatwgTest/Streams/Counterexamples/Piping/Shutdown.lean` and is linked here,
not reproduced. The finite fixtures compare prescribed competing rules;
they do not establish the production lifecycle or a host correspondence.
Cases 005, 011, 012, 015 and 016 reduce actual canonical P4/P5 operations at small
inputs/snapshots. The other cases inspect passive canonical outcomes or
finite competing choices.

The general semantic obligation is
`Piping.forwardShutdown_realizes`, under
`Piping.ForwardShutdownSpec (Piping.observeShutdown ...)`. Two quantified,
finite canonical runs are separately ascribed in `ShutdownRuns.lean`.
Release, pipe-result settlement, full DB-04 masks, arbitrary pumping and the
global scheduler remain open. No witness below closes those obligations.

| ID | Witness suffix (`ce` prefix) | Finite discriminator | Required production law combination |
| --- | --- | --- | --- |
| `WS-PIPE-CE-001` | `ce001_pending_write_blocks` | One pending canonical unit outcome gives an unsatisfied all-settled predicate. | `allWrittenSettled_iff`, `tick_eq`, `lifecycle_two_writes_abort_rejection` |
| `WS-PIPE-CE-002` | `ce002_rejected_write_settled` | A rejected canonical unit outcome satisfies settlement and fails a fulfillment-only test. | `writesSettled_iff`, `allWrittenSettled_iff`, `lifecycle_write_rejection_retains_source` |
| `WS-PIPE-CE-003` | `ce003_stale_wait_target` | A fulfilled first cell and pending second cell distinguish one target from all obligations. | `allWrittenSettled_eq`, `recordAllowed_iff`, `lifecycle_two_writes_abort_rejection` |
| `WS-PIPE-CE-004` | `ce004_duplicate_chunk_ids` | Two read IDs with equal Nat chunks remain two obligations; deduplicating values loses one. | `readInventory_iff`, `markWrite_eq`, `recordAllowed_iff` |
| `WS-PIPE-CE-005` | `ce005_queue_drops_read_history` | Actual canonical P4 enqueue/read/error leaves an empty queue but retains read ID 0 and its delivered chunk. | `deliveredReads_eq`, `readInventory_iff`, `reaches_no_new_read` |
| `WS-PIPE-CE-006` | `ce006_first_shutdown_wins` | A finite first-selection function retains reason 1 against a later reason 2. | `enterForwardShutdown_first_wins`, `reaches_selection_stable` |
| `WS-PIPE-CE-007` | `ce007_prevent_abort_still_waits` | The prevention flag changes the action while one pending write still blocks the continuation. | `tick_eq`, `recordAllowed_iff`, `lifecycle_write_rejection_retains_source` |
| `WS-PIPE-CE-008` | `ce008_write_error_no_override` | A prescribed successful-action/no-replacement snapshot retains original reason 1 instead of write reason 2. | `recordAllowed_iff`, `preventAbort_write_rejection_no_override`, `lifecycle_write_rejection_retains_source` |
| `WS-PIPE-CE-009` | `ce009_action_error_overrides` | A rejected action with reason 3 replaces original reason 1. | `recordAllowed_iff`, `tick_eq`, `lifecycle_two_writes_abort_rejection` |
| `WS-PIPE-CE-010` | `ce010_capture_drain_gate` | Writable-at-entry and later errored destination snapshots distinguish captured from dynamic gating. | `enterForwardShutdown_eq`, `recordAllowed_iff`, `tick_eq` |
| `WS-PIPE-CE-011` | `ce011_terminal_abort_fulfills` | An actual P5 beginAbort stage at a prescribed terminal destination creates a fulfilled result cell without signaling. | `invokeAbort_eq`, `recordAllowed_iff`, `lifecycle_write_rejection_retains_source` |
| `WS-PIPE-CE-012` | `ce012_callback_blocks_jobs` | An actual P5 size marker blocks its queued job; this is a prescribed stage snapshot. | `stepWritable_eq`, `externalFrontier_eq`, `tick_eq`, `imported Writable.tick` |
| `WS-PIPE-CE-013` | `ce013_forward_error_priority` | Two finite selectors over canonical P4/P5 statuses distinguish the source-first condition order. | `enterForwardShutdown_eq`, `tick_eq`, `recordAllowed_iff` |
| `WS-PIPE-CE-014` | `ce014_pending_action_is_live` | A pending canonical action outcome produces no finalization reason. | `captureAbort_eq`, `tick_eq`, `ready_frontier` |
| `WS-PIPE-CE-015` | `ce015_erroring_owed_write_keeps_wait` | At a prescribed erroring destination with a pending first write, actual P5 after-size and return stages create/return a rejected second result; both IDs remain in the wait set. The entry guard was true and the current guard is false. | `recordAllowed_iff`, `allWrittenSettled_iff`, `tick_eq`, `forwardShutdown_realizes`; canonical `Writable.tick` |
| `WS-PIPE-CE-016` | `ce016_new_read_changes_snapshot` | Actual P4 read on an errored source allocates a new rejected read ID; the canonical nextRead snapshot changes even though no chunk is delivered. | `recordAllowed_iff`, `reaches_no_new_read`, `forwardShutdown_realizes` |

All sixteen witnesses passed the final direct command below using the
coordinator's exclusive sequential window, actual Lean exit 0. Eight are
axiom-free. CE-002/010/013 use `propext`; CE-005/011/012/015/016 use
`propext` and `Quot.sound`. No witness reaches `Classical.choice` or any
forbidden axiom. No host or WPT run was performed.

```powershell
$env:LEAN_NUM_THREADS='1'
$env:LEAN_PATH='C:\Users\kokok\Dev\lean4-WHATWG-streams\.lake\build\lib\lean'
lean -M2048 -DmaxErrors=10000 WhatwgTest/Streams/Counterexamples/Piping/Shutdown.lean
```

The command ran from `C:/Users/kokok/Dev/lean4-WHATWG-streams-piping-breaker`
under pinned Lean 4.33.1, inheriting verified main artifacts at
`afb57f8ee0d889b1b4866138e31862e0cf825fd4`. This is compile infrastructure;
the witness source remains in the separate breaker checkout.
The final output is
`C:/Users/kokok/AppData/Local/Temp/whatwg-p7-witness.log`, SHA-256
`96404a1968f60aaf806d980c60aed01448c22210271bbc78f81e1087d389f7b6`.
Final source SHA-256:
`46e2d65951bc18cda10be3f0b21d41dd722b670758179160fe2b3a7663056701`.

CE-015 is a two-stage finite P5 trace at a prescribed snapshot. The general
post-latch erroring/owed-write case remains part of the unchanged quantified
`forwardShutdown_realizes` obligation. Its complete reentrant callback tape
is not asserted by this fixture or by the two chosen lifecycle shapes.
