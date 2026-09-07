import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Q4 breaker theorem receipts. Freeze state, commands and results: the owning
contract's "Freeze receipt", `test/contracts/configuration-ordering.contract.md`.

82 receipts: the 54 restated P8a law ascriptions, the 12 Q4-owned bridging
receipts, the 14 theorems of `WhatwgTest/Streams/PromiseBridgeQ4.lean`, and the
2 laws of `WhatwgTest/Streams/Semantics/OrderingSource.lean`. The ceiling is
R-11: `propext`, `Quot.sound`, `Classical.choice` and nothing else. `sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the
`native_decide` auxiliaries are forbidden here as everywhere.

Red today: every constant below is unknown. The builder removes the entry from
`test/fixtures/trust-gate/known-red.txt` only when all 82 print.
-/

/-! ## The 54 restated P8a laws -/

#print axioms Whatwg.Streams.Semantics.Ordering.initial_eq
#print axioms Whatwg.Streams.Semantics.Ordering.lookup_eq
#print axioms Whatwg.Streams.Semantics.Ordering.lookupRegistration_eq
#print axioms Whatwg.Streams.Semantics.Ordering.setRegistrationPhase_eq
#print axioms Whatwg.Streams.Semantics.Ordering.enqueueJob_eq
#print axioms Whatwg.Streams.Semantics.Ordering.preStartAllowed_eq
#print axioms Whatwg.Streams.Semantics.Ordering.authorFrontier_eq
#print axioms Whatwg.Streams.Semantics.Ordering.tick_script_empty
#print axioms Whatwg.Streams.Semantics.Ordering.tick_observer_empty
#print axioms Whatwg.Streams.Semantics.Ordering.tick_intrinsic_empty
#print axioms Whatwg.Streams.Semantics.Ordering.tick_nonempty_foreign
#print axioms Whatwg.Streams.Semantics.Ordering.decide_intrinsic_gap
#print axioms Whatwg.Streams.Semantics.Ordering.decide_checkpoint_writable
#print axioms Whatwg.Streams.Semantics.Ordering.decide_checkpoint_observe
#print axioms Whatwg.Streams.Semantics.Ordering.decide_scriptReturn
#print axioms Whatwg.Streams.Semantics.Ordering.decide_scriptBegin
#print axioms Whatwg.Streams.Semantics.Ordering.step_iff
#print axioms Whatwg.Streams.Semantics.Ordering.reaches_append
#print axioms Whatwg.Streams.Semantics.Ordering.episodePrefix_reaches
#print axioms Whatwg.Streams.Semantics.Ordering.queuedJobs_eq
#print axioms Whatwg.Streams.Semantics.Ordering.m2Allowed_eq
#print axioms Whatwg.Streams.Semantics.Ordering.observeLive_writable
#print axioms Whatwg.Streams.Semantics.Ordering.observeLive_outside_profile
#print axioms Whatwg.Streams.Semantics.Ordering.register_eq
#print axioms Whatwg.Streams.Semantics.Ordering.notifySettled_eq
#print axioms Whatwg.Streams.Semantics.Ordering.liftWritable_eq
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_matching
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_active
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_control
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_empty
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_not_head
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_empty_mailbox
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_not_sink
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_wrong_key
#print axioms Whatwg.Streams.Semantics.Ordering.takeSinkHead_canonical_tick
#print axioms Whatwg.Streams.Semantics.Ordering.stagedRequests_nil
#print axioms Whatwg.Streams.Semantics.Ordering.stagedRequests_pair
#print axioms Whatwg.Streams.Semantics.Ordering.stagedRequests_other
#print axioms Whatwg.Streams.Semantics.Ordering.sinkMarkerCount_eq
#print axioms Whatwg.Streams.Semantics.Ordering.suspensions_staged_empty
#print axioms Whatwg.Streams.Semantics.Ordering.successfulControl_advance_staged_empty
#print axioms Whatwg.Streams.Semantics.Ordering.successfulControl_sink_at_most_one
#print axioms Whatwg.Streams.Semantics.Ordering.suspensions_iff
#print axioms Whatwg.Streams.Semantics.Ordering.successfulControl_iff
#print axioms Whatwg.Streams.Semantics.Ordering.externalWord_eq
#print axioms Whatwg.Streams.Semantics.Ordering.normalized_iff
#print axioms Whatwg.Streams.Semantics.Ordering.step_deterministic
#print axioms Whatwg.Streams.Semantics.Ordering.tick_decide_exclusive
#print axioms Whatwg.Streams.Semantics.Ordering.step_owner
#print axioms Whatwg.Streams.Semantics.Ordering.step_trace_extends
#print axioms Whatwg.Streams.Semantics.Ordering.step_active_jobs_eq
#print axioms Whatwg.Streams.Semantics.Ordering.episodePrefix_jobs_eq
#print axioms Whatwg.Streams.Semantics.Ordering.fixed_external_word_prefix_comparable
#print axioms Whatwg.Streams.Semantics.Ordering.fixed_external_word_normalized_unique

/-! ## The 12 Q4-owned bridging receipts -/

#print axioms Whatwg.Streams.Semantics.Ordering.jobQueue_eq
#print axioms Whatwg.Streams.Semantics.Ordering.reactions_eq
#print axioms Whatwg.Streams.Semantics.Ordering.activeErase_eq
#print axioms Whatwg.Streams.Semantics.Ordering.runCondition_iff
#print axioms Whatwg.Streams.Semantics.Ordering.lookup_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.lookupRegistration_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.setRegistrationPhase_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.enqueueJob_queue_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.register_reactions_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.notifySettled_reactions_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.step_active_jobQueue_eq
#print axioms Whatwg.Streams.Semantics.Ordering.episodePrefix_jobQueue_eq

/-! ## The 14 deferred-generalization theorems (`WhatwgTest/Streams/PromiseBridgeQ4.lean`) -/

#print axioms Whatwg.Streams.Readable.readTable_freshReadCell
#print axioms Whatwg.Streams.Readable.readTable_settleReadCell
#print axioms Whatwg.Streams.Readable.readTable_settleReadCells
#print axioms Whatwg.Streams.Readable.continuePull_settleRead_body
#print axioms Whatwg.Streams.Readable.streamClose_body
#print axioms Whatwg.Streams.Readable.error_body
#print axioms Whatwg.Streams.Readable.beginEnqueue_settle_body
#print axioms Whatwg.Streams.Readable.read_body
#print axioms Whatwg.Streams.Transform.notify_jobQueue_bridge
#print axioms Whatwg.Streams.Transform.settle_table_bridge
#print axioms Whatwg.Streams.Transform.settle_jobQueue_order
#print axioms Whatwg.Streams.Transform.settle_waiting_once
#print axioms Whatwg.Streams.Transform.runJob_writable_dequeue
#print axioms Whatwg.Streams.Transform.runJob_writable_blocked

/-! ## The 2 source/certificate laws -/

#print axioms Whatwg.Streams.Semantics.Ordering.Source.erasure_preserves_selected_order
#print axioms Whatwg.Streams.Semantics.Ordering.Source.run_erases_to_reference
