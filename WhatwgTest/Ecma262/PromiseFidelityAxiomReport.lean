import Whatwg.Ecma262
import Whatwg.Streams
import Whatwg.WebIdl

/-!
Breaker-owned Q3b axiom receipt list for the fidelity addendum.
Addendum: `test/contracts/promise-first-packet-q3b.contract.md`.
Graph: `PROMISE-PG-FIRST`, `docs/PROMISE-DAG.md`, "Q3b addendum".

This module names exactly the **57** theorem obligations of the addendum and no
others: 33 in `WhatwgTest/Ecma262/PromiseFidelityLaws.lean`, 11 in
`WhatwgTest/Ecma262/JobsCompleteContract.lean` and 13 in
`WhatwgTest/WebIdl/PromiseFidelityContract.lean`. The base packet's own 125
receipts stay in `WhatwgTest/Ecma262/PromiseAxiomReport.lean`, which this
addendum does not edit: the amendments change statements, never names, so that
report is neither short nor long after the Q3b landing.

Ceiling R-11: `propext`, `Quot.sound`, `Classical.choice`. `sorryAx`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and the
`native_decide` auxiliary axioms are forbidden, which forbids `native_decide`
and `bv_decide` in every proof. A receipt that reaches `Classical.choice` is
reported as such and is inside the ceiling; an empty receipt is not required
and its absence is not a defect.

The builder must not remove a name from this list.
-/

/-! ## F1 — `op.performpromisethen` step 12 -/
#print axioms Whatwg.Ecma262.Promise.Table.markHandled_marked
#print axioms Whatwg.Ecma262.Promise.performPromiseThen_handled

/-! ## F2 — the settled branches append to no list -/
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_fulfill
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_reject
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_next
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_reaction
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_capability
#print axioms Whatwg.Ecma262.Promise.Reactions.mint_no_waiting

/-! ## F3 — `FulfillPromise` and `RejectPromise` clear both lists -/
#print axioms Whatwg.Ecma262.Promise.Reactions.clear_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.clear_waiting
#print axioms Whatwg.Ecma262.Promise.Reactions.clear_other_promise
#print axioms Whatwg.Ecma262.Promise.Reactions.clear_next
#print axioms Whatwg.Ecma262.Promise.Table.settleAndTrigger_cleared

/-! ## F4 — the capability, the handler as a decision, and the reaction job -/
#print axioms Whatwg.Ecma262.Promise.reactionHandlerResult_empty
#print axioms Whatwg.Ecma262.Promise.reactionHandlerResult_handler
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle_ok
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callSettle_error
#print axioms Whatwg.Ecma262.Promise.runReactionJob_no_capability
#print axioms Whatwg.Ecma262.Promise.runReactionJob_empty_handler
#print axioms Whatwg.Ecma262.Promise.runReactionJob_resolve
#print axioms Whatwg.Ecma262.Promise.runReactionJob_reject
#print axioms Whatwg.Ecma262.Promise.runReactionJob_once

/-! ## Minor — the shared one-shot marker and the self-resolution branch -/
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_disables_reject
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_disables_resolve
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf_self
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callResolveSelf_other

/-! ## F6 — the settlement trace and its Streams bridge -/
#print axioms Whatwg.Ecma262.Promise.Table.settleTraced_table
#print axioms Whatwg.Ecma262.Promise.Table.settleTraced_pending
#print axioms Whatwg.Ecma262.Promise.Table.settleTraced_other
#print axioms Whatwg.Ecma262.Promise.SettlementTrace.firstRejection_eq
#print axioms Whatwg.Ecma262.Promise.SettlementTrace.firstRejection_hit
#print axioms Whatwg.Streams.Writable.settlementTrace_bridge

/-! ## F5 — `requirement.jobs.3`, run to completion -/
#print axioms Whatwg.Ecma262.Jobs.startJob_checkpoint
#print axioms Whatwg.Ecma262.Jobs.startJob_queue
#print axioms Whatwg.Ecma262.Jobs.startJob_blocked
#print axioms Whatwg.Ecma262.Jobs.startJob_active
#print axioms Whatwg.Ecma262.Jobs.completeJob_job
#print axioms Whatwg.Ecma262.Jobs.completeJob_other
#print axioms Whatwg.Ecma262.Jobs.RunToCompletion_iff
#print axioms Whatwg.Ecma262.Jobs.run_to_completion
#print axioms Whatwg.Ecma262.Jobs.run_to_completion_nonvacuous
#print axioms Whatwg.Ecma262.Jobs.run_one_job_per_step
#print axioms Whatwg.Ecma262.Jobs.startJob_run_agree

/-! ## F6 and the minors at the Web IDL layer -/
#print axioms Whatwg.WebIdl.Promise.waitForAllTraced_pending
#print axioms Whatwg.WebIdl.Promise.waitForAllTraced_success
#print axioms Whatwg.WebIdl.Promise.waitForAllTraced_failure
#print axioms Whatwg.WebIdl.Promise.waitForAllTraced_failure_pending
#print axioms Whatwg.WebIdl.Promise.waitForAll_traced_success_agree
#print axioms Whatwg.WebIdl.Promise.newPromiseWithCapability_eq
#print axioms Whatwg.WebIdl.Promise.newPromise_capability_promise
#print axioms Whatwg.WebIdl.Promise.resolveThrough_eq
#print axioms Whatwg.WebIdl.Promise.rejectThrough_eq
#print axioms Whatwg.WebIdl.Promise.resolveThrough_resolve
#print axioms Whatwg.WebIdl.Promise.rejectThrough_reject
#print axioms Whatwg.WebIdl.Promise.react_performPromiseThen
#print axioms Whatwg.WebIdl.Promise.react_handled
