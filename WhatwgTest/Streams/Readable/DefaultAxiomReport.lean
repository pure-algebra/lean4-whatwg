import Whatwg.Streams

/-!
Breaker-owned P4a axiom receipt list for READABLE-PG-DEFAULT.
Exactly the 94 theorem ascriptions in DefaultContract.lean.
The root R-11 ceiling applies: propext, Quot.sound, Classical.choice only.
Unknown constants are intentional until implementation; import errors are never intended red.
-/

set_option autoImplicit false

#print axioms Whatwg.Streams.Boundary.Exception.toRangeError_ofRangeError
#print axioms Whatwg.Streams.Boundary.Exception.toRangeError_typeError
#print axioms Whatwg.Streams.Boundary.Exception.toRangeError_foreign
#print axioms Whatwg.Streams.Boundary.Exception.ofRangeError_eq
#print axioms Whatwg.Streams.Readable.size_eq
#print axioms Whatwg.Streams.Readable.sizes_eq
#print axioms Whatwg.Streams.Readable.initial_eq
#print axioms Whatwg.Streams.Readable.sizePositive_eq
#print axioms Whatwg.Streams.Readable.desiredSize_readable
#print axioms Whatwg.Streams.Readable.desiredSize_closed
#print axioms Whatwg.Streams.Readable.desiredSize_errored
#print axioms Whatwg.Streams.Readable.canCloseOrEnqueue_iff
#print axioms Whatwg.Streams.Readable.shouldCallPull_iff
#print axioms Whatwg.Streams.Readable.callPullIfNeeded_idle
#print axioms Whatwg.Streams.Readable.callPullIfNeeded_busy
#print axioms Whatwg.Streams.Readable.callPullIfNeeded_start
#print axioms Whatwg.Streams.Readable.callPullIfNeeded_missing
#print axioms Whatwg.Streams.Readable.acceptPullAnswer_waiting
#print axioms Whatwg.Streams.Readable.acceptPullAnswer_unmatched
#print axioms Whatwg.Streams.Readable.reactPull_fulfilled
#print axioms Whatwg.Streams.Readable.reactPull_rejected
#print axioms Whatwg.Streams.Readable.runPullJob_suspended
#print axioms Whatwg.Streams.Readable.runPullJob_empty
#print axioms Whatwg.Streams.Readable.runPullJob_cons
#print axioms Whatwg.Streams.Readable.close_blocked
#print axioms Whatwg.Streams.Readable.close_deferred
#print axioms Whatwg.Streams.Readable.close_empty
#print axioms Whatwg.Streams.Readable.error_terminal
#print axioms Whatwg.Streams.Readable.error_readable
#print axioms Whatwg.Streams.Readable.read_closed
#print axioms Whatwg.Streams.Readable.read_errored
#print axioms Whatwg.Streams.Readable.read_empty
#print axioms Whatwg.Streams.Readable.read_nextRead
#print axioms Whatwg.Streams.Readable.beginEnqueue_blocked
#print axioms Whatwg.Streams.Readable.beginEnqueue_pending
#print axioms Whatwg.Streams.Readable.beginEnqueue_one
#print axioms Whatwg.Streams.Readable.beginEnqueue_foreign
#print axioms Whatwg.Streams.Readable.beginEnqueue_missing
#print axioms Whatwg.Streams.Readable.finishEnqueue_value
#print axioms Whatwg.Streams.Readable.finishEnqueue_invalid
#print axioms Whatwg.Streams.Readable.finishEnqueue_thrown
#print axioms Whatwg.Streams.Readable.resumeSize_empty
#print axioms Whatwg.Streams.Readable.settlementTrace_eq
#print axioms Whatwg.Streams.Readable.chunksOfSettlements_eq
#print axioms Whatwg.Streams.Readable.observeM1_eq
#print axioms Whatwg.Streams.Readable.chunksOfSettlements_append
#print axioms Whatwg.Streams.Readable.step_read
#print axioms Whatwg.Streams.Readable.step_enqueue
#print axioms Whatwg.Streams.Readable.step_close
#print axioms Whatwg.Streams.Readable.step_error
#print axioms Whatwg.Streams.Readable.step_size
#print axioms Whatwg.Streams.Readable.step_pull
#print axioms Whatwg.Streams.Readable.step_iff
#print axioms Whatwg.Streams.Readable.steps_nil_iff
#print axioms Whatwg.Streams.Readable.steps_cons_iff
#print axioms Whatwg.Streams.Readable.steps_append_iff
#print axioms Whatwg.Streams.Readable.reentrant_enqueue_lifo
#print axioms Whatwg.Streams.Readable.reentrant_close_keeps_chunk
#print axioms Whatwg.Streams.Readable.reentrant_read_does_not_recheck
#print axioms Whatwg.Streams.Readable.reentrant_error_keeps_chunk
#print axioms Whatwg.Streams.Readable.reentrant_error_then_throw
#print axioms Whatwg.Streams.Readable.reentrant_error_then_invalid
#print axioms Whatwg.Streams.Readable.fifo_close_m1_m2
#print axioms Whatwg.Streams.Readable.pending_read_skips_size
#print axioms Whatwg.Streams.Boundary.Exception.rangeError_eq_iff
#print axioms Whatwg.Streams.Boundary.Exception.typeError_eq_iff
#print axioms Whatwg.Streams.Readable.continuePull_done
#print axioms Whatwg.Streams.Readable.continuePull_read
#print axioms Whatwg.Streams.Readable.continuePull_enqueue
#print axioms Whatwg.Streams.Readable.callPullIfNeeded_eq
#print axioms Whatwg.Streams.Readable.callPullIfNeededWith_idle
#print axioms Whatwg.Streams.Readable.callPullIfNeededWith_busy
#print axioms Whatwg.Streams.Readable.callPullIfNeededWith_start
#print axioms Whatwg.Streams.Readable.callPullIfNeededWith_missing
#print axioms Whatwg.Streams.Readable.returnPull_empty
#print axioms Whatwg.Streams.Readable.returnPull_size
#print axioms Whatwg.Streams.Readable.returnPull_pending
#print axioms Whatwg.Streams.Readable.returnPull_settled
#print axioms Whatwg.Streams.Readable.streamClose_readable
#print axioms Whatwg.Streams.Readable.streamClose_terminal
#print axioms Whatwg.Streams.Readable.read_queued_eq
#print axioms Whatwg.Streams.Readable.finishEnqueue_thrown_nextError
#print axioms Whatwg.Streams.Readable.resumeSize_size
#print axioms Whatwg.Streams.Readable.resumeSize_pull
#print axioms Whatwg.Streams.Readable.pull_reentrant_error_before_chunk
#print axioms Whatwg.Streams.Readable.pull_reentrant_enqueue_changes_queue
#print axioms Whatwg.Streams.Readable.pull_reentrant_read_overtakes
#print axioms Whatwg.Streams.Readable.nested_invalid_sizes_fresh_errors
#print axioms Whatwg.Streams.Readable.queryDesiredSize_eq
#print axioms Whatwg.Streams.Readable.observeM2_eq
#print axioms Whatwg.Streams.Readable.observeM2_toM1
#print axioms Whatwg.Streams.Readable.queryDesiredSize_m2
#print axioms Whatwg.Streams.Readable.step_pullReturn
#print axioms Whatwg.Streams.Readable.step_desiredSize
