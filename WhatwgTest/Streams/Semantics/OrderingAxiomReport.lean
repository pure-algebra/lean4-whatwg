import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Q4 breaker theorem receipts. Freeze state, commands and results: the owning
contract's "Freeze receipt", `test/contracts/configuration-ordering.contract.md`.

**93 receipts** after the Q4 amendment of 2026-09-07 (82 at the freeze): the 54
restated P8a law ascriptions, the 15 Q4-owned bridging receipts, the 14
theorems of `WhatwgTest/Streams/PromiseBridgeQ4.lean`, and the 10 laws and
receipts of `WhatwgTest/Streams/Semantics/OrderingSource.lean`. The ceiling is
R-11: `propext`, `Quot.sound`, `Classical.choice` and nothing else. `sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the
`native_decide` auxiliaries are forbidden here as everywhere.

**Q4 amendment A6, 2026-09-07, breaker seat, branch `promise/q4-amend`.** The
Q4 builder reported three missing receipts (contract §11.5): the name
`notifySettled_reactions_bridge` did not exist because the frozen statement was
false (B3), and the two §6 laws were not attempted (§11.4). This amendment
reconciles the list with the names that exist after amendments A1 to A5:

- `notifySettled_reactions_bridge` stays, at its restated statement (A4), and
  three receipts join it: `phaseErase_eq`, `reactionErase_eq` and
  `notifySettled_queued_serial`. The Q4-owned bridging block therefore holds
  15 receipts, not 12.
- `Source.run_erases_to_reference` is **removed**. Amendment A5 moves it to P8
  with its reasons; a receipt for a name this packet no longer freezes would be
  a permanent red line.
- Nine source receipts join the one that remains of §6
  (`erasure_preserves_selected_order`): `erases_prefix_selected_order`, the
  target-side consequence A5 splits off, and then
  `sourceChecked_iff`, `causalPrefix_iff`, `retainedFifo_iff`,
  `erasesPrefix_iff`, `sourceProfileCompatible_iff` — the five equations that
  keep a checker from being widened into vacuity — and
  `wptCertificate_checked`, `wptReference_causal`, `wptReference_selected`,
  the three non-vacuity receipts of §K. The three mutant rejections of §L are
  `Bool` equalities on closed terms and carry no interesting axiom set, so
  they are *not* listed here; they are checked by elaboration in the battery
  itself.

82 − 1 + 3 + 9 = 93.

Red today: every constant below is unknown, or was named by an ascription this
amendment restated. The builder removes the entry from
`test/fixtures/trust-gate/known-red.txt` only when all 93 print.
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

/-! ## The 15 Q4-owned bridging receipts

Twelve at the freeze; `phaseErase_eq`, `reactionErase_eq` and
`notifySettled_queued_serial` are added by amendment A4. -/

#print axioms Whatwg.Streams.Semantics.Ordering.jobQueue_eq
#print axioms Whatwg.Streams.Semantics.Ordering.reactions_eq
#print axioms Whatwg.Streams.Semantics.Ordering.activeErase_eq
#print axioms Whatwg.Streams.Semantics.Ordering.runCondition_iff
#print axioms Whatwg.Streams.Semantics.Ordering.lookup_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.lookupRegistration_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.setRegistrationPhase_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.enqueueJob_queue_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.register_reactions_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.phaseErase_eq
#print axioms Whatwg.Streams.Semantics.Ordering.reactionErase_eq
#print axioms Whatwg.Streams.Semantics.Ordering.notifySettled_reactions_bridge
#print axioms Whatwg.Streams.Semantics.Ordering.notifySettled_queued_serial
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

/-! ## The 10 source/certificate laws and receipts

Two at the freeze. `Source.run_erases_to_reference` is removed by amendment A5,
which moves it to P8 with its reasons. The five `_iff` equations keep a checker
from being widened into vacuity; the three `wpt*` receipts are the packet's
non-vacuity evidence that the pinned certificate and reference prefix are
accepted and produce the selected-log prefix of §3.1. The three mutant
rejections of `OrderingSource.lean` §L are closed `Bool` equalities and are
checked by elaboration there, not listed here. -/

#print axioms Whatwg.Streams.Semantics.Ordering.Source.erasure_preserves_selected_order
#print axioms Whatwg.Streams.Semantics.Ordering.Source.erases_prefix_selected_order
#print axioms Whatwg.Streams.Semantics.Ordering.Source.sourceChecked_iff
#print axioms Whatwg.Streams.Semantics.Ordering.Source.causalPrefix_iff
#print axioms Whatwg.Streams.Semantics.Ordering.Source.retainedFifo_iff
#print axioms Whatwg.Streams.Semantics.Ordering.Source.erasesPrefix_iff
#print axioms Whatwg.Streams.Semantics.Ordering.Source.sourceProfileCompatible_iff
#print axioms Whatwg.Streams.Semantics.Ordering.Source.wptCertificate_checked
#print axioms Whatwg.Streams.Semantics.Ordering.Source.wptReference_causal
#print axioms Whatwg.Streams.Semantics.Ordering.Source.wptReference_selected
