import Whatwg.Streams
import Whatwg.Ecma262
import Whatwg.WebIdl

/-!
Breaker-owned Q3 axiom receipt list for `PROMISE-PG-FIRST`.
Contract: `test/contracts/promise-first-packet.contract.md`.

Exactly the 125 theorem ascriptions of the packet's six statement batteries:
20 in `WhatwgTest/Ecma262/JobsLaws.lean`, 44 in
`WhatwgTest/Ecma262/PromiseLaws.lean`, 17 in
`WhatwgTest/WebIdl/PromiseContract.lean`, 15 in
`WhatwgTest/WebIdl/ExceptionsContract.lean`, and 29 in the bridging half of
`WhatwgTest/Streams/PromiseBridge.lean`. The preservation half of that module
ascribes existing Streams theorems whose receipts already belong to the P4-P7
axiom reports and are not repeated here.

The root R-11 ceiling applies: `propext`, `Quot.sound`, `Classical.choice`
only. `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`
and the `native_decide` auxiliaries appear nowhere.

Unknown constants are intentional until implementation; an import or toolchain
failure is never intended red evidence.
-/

set_option autoImplicit false

/-! ### `Whatwg.Ecma262.Jobs` — 20 -/

#print axioms Whatwg.Ecma262.Jobs.Queue.empty_eq
#print axioms Whatwg.Ecma262.Jobs.Queue.enqueue_eq
#print axioms Whatwg.Ecma262.Jobs.Queue.enqueueAll_eq
#print axioms Whatwg.Ecma262.Jobs.Queue.oldest_eq
#print axioms Whatwg.Ecma262.Jobs.Queue.dequeue_empty
#print axioms Whatwg.Ecma262.Jobs.Queue.dequeue_cons
#print axioms Whatwg.Ecma262.Jobs.Queue.dequeue_fifo
#print axioms Whatwg.Ecma262.Jobs.mayRun_iff
#print axioms Whatwg.Ecma262.Jobs.RunCondition_iff
#print axioms Whatwg.Ecma262.Jobs.step_checkpoint
#print axioms Whatwg.Ecma262.Jobs.step_blocked
#print axioms Whatwg.Ecma262.Jobs.FifoRequirement_iff
#print axioms Whatwg.Ecma262.Jobs.run_zero
#print axioms Whatwg.Ecma262.Jobs.run_nil
#print axioms Whatwg.Ecma262.Jobs.run_cons
#print axioms Whatwg.Ecma262.Jobs.run_split
#print axioms Whatwg.Ecma262.Jobs.run_fifo
#print axioms Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob_order
#print axioms Whatwg.Ecma262.Jobs.hostEnqueuePromiseJob_eq
#print axioms Whatwg.Ecma262.Jobs.newReactionJob_eq

/-! ### `Whatwg.Ecma262.Promise` — 44 -/

#print axioms Whatwg.Ecma262.Promise.Table.empty_eq
#print axioms Whatwg.Ecma262.Promise.Table.getCell_eq
#print axioms Whatwg.Ecma262.Promise.Table.get_eq
#print axioms Whatwg.Ecma262.Promise.Table.isPending_iff
#print axioms Whatwg.Ecma262.Promise.Table.fresh_eq
#print axioms Whatwg.Ecma262.Promise.Table.fresh_id
#print axioms Whatwg.Ecma262.Promise.Table.fresh_next
#print axioms Whatwg.Ecma262.Promise.Table.fresh_old
#print axioms Whatwg.Ecma262.Promise.Table.fresh_get
#print axioms Whatwg.Ecma262.Promise.Table.settle_pending
#print axioms Whatwg.Ecma262.Promise.Table.settle_other
#print axioms Whatwg.Ecma262.Promise.Table.settle_assert
#print axioms Whatwg.Ecma262.Promise.Table.settle_handled
#print axioms Whatwg.Ecma262.Promise.Table.markHandled_eq
#print axioms Whatwg.Ecma262.Promise.Table.markHandled_idem
#print axioms Whatwg.Ecma262.Promise.Table.markHandled_state
#print axioms Whatwg.Ecma262.Promise.Reactions.empty_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.get_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.add_id
#print axioms Whatwg.Ecma262.Promise.Reactions.add_next
#print axioms Whatwg.Ecma262.Promise.Reactions.add_fulfill
#print axioms Whatwg.Ecma262.Promise.Reactions.add_reject
#print axioms Whatwg.Ecma262.Promise.Reactions.setPhase_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.waitingOn_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.registered_eq
#print axioms Whatwg.Ecma262.Promise.Reactions.add_paired
#print axioms Whatwg.Ecma262.Promise.triggerReactions_order
#print axioms Whatwg.Ecma262.Promise.triggerReactions_once
#print axioms Whatwg.Ecma262.Promise.triggerReactions_other_promise
#print axioms Whatwg.Ecma262.Promise.triggerReactions_other_kind
#print axioms Whatwg.Ecma262.Promise.Table.settleAndTrigger_pending
#print axioms Whatwg.Ecma262.Promise.Table.settleAndTrigger_other
#print axioms Whatwg.Ecma262.Promise.fulfillPromise_eq
#print axioms Whatwg.Ecma262.Promise.rejectPromise_eq
#print axioms Whatwg.Ecma262.Promise.performPromiseThen_missing
#print axioms Whatwg.Ecma262.Promise.performPromiseThen_pending
#print axioms Whatwg.Ecma262.Promise.performPromiseThen_fulfilled
#print axioms Whatwg.Ecma262.Promise.performPromiseThen_rejected
#print axioms Whatwg.Ecma262.Promise.newPromiseCapability_eq
#print axioms Whatwg.Ecma262.Promise.createResolvingFunctions_eq
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_fresh
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callResolve_alreadyResolved
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_fresh
#print axioms Whatwg.Ecma262.Promise.ResolvingFunctions.callReject_alreadyResolved

/-! ### `Whatwg.WebIdl.Promise` — 17 -/

#print axioms Whatwg.WebIdl.Promise.newPromise_eq
#print axioms Whatwg.WebIdl.Promise.resolvedWith_eq
#print axioms Whatwg.WebIdl.Promise.rejectedWith_eq
#print axioms Whatwg.WebIdl.Promise.resolve_eq
#print axioms Whatwg.WebIdl.Promise.reject_eq
#print axioms Whatwg.WebIdl.Promise.markAsHandled_eq
#print axioms Whatwg.WebIdl.Promise.react_pending
#print axioms Whatwg.WebIdl.Promise.react_fulfilled
#print axioms Whatwg.WebIdl.Promise.react_rejected
#print axioms Whatwg.WebIdl.Promise.react_missing
#print axioms Whatwg.WebIdl.Promise.uponFulfillment_eq
#print axioms Whatwg.WebIdl.Promise.uponRejection_eq
#print axioms Whatwg.WebIdl.Promise.AllSettled_iff
#print axioms Whatwg.WebIdl.Promise.allSettled_iff
#print axioms Whatwg.WebIdl.Promise.waitForAll_pending
#print axioms Whatwg.WebIdl.Promise.waitForAll_success
#print axioms Whatwg.WebIdl.Promise.waitForAll_failure

/-! ### `Whatwg.WebIdl.Exceptions` — 15 -/

#print axioms Whatwg.WebIdl.Exceptions.Simple.all_length
#print axioms Whatwg.WebIdl.Exceptions.Simple.all_nodup
#print axioms Whatwg.WebIdl.Exceptions.Simple.all_complete
#print axioms Whatwg.WebIdl.Exceptions.Name.all_length
#print axioms Whatwg.WebIdl.Exceptions.Name.all_nodup
#print axioms Whatwg.WebIdl.Exceptions.Name.all_complete
#print axioms Whatwg.WebIdl.Exceptions.createSimple_eq
#print axioms Whatwg.WebIdl.Exceptions.Exception.simple_eq_iff
#print axioms Whatwg.WebIdl.Exceptions.Exception.domException_eq_iff
#print axioms Whatwg.WebIdl.Exceptions.Exception.identity_simple
#print axioms Whatwg.WebIdl.Exceptions.Exception.identity_domException
#print axioms Whatwg.WebIdl.Exceptions.Exception.identity_foreign
#print axioms Whatwg.WebIdl.Exceptions.Exception.isSimple_simple
#print axioms Whatwg.WebIdl.Exceptions.Exception.isSimple_domException
#print axioms Whatwg.WebIdl.Exceptions.Exception.isSimple_foreign

/-! ### The Streams bridging half — 29 -/

#print axioms Whatwg.Streams.Writable.promiseTable_eq
#print axioms Whatwg.Streams.Writable.lookupPromise_bridge
#print axioms Whatwg.Streams.Writable.freshPromise_bridge
#print axioms Whatwg.Streams.Writable.settle_bridge
#print axioms Whatwg.Streams.Writable.markHandled_bridge
#print axioms Whatwg.Streams.Writable.handled_bridge
#print axioms Whatwg.Streams.Readable.readTable_eq
#print axioms Whatwg.Streams.Readable.readTable_get
#print axioms Whatwg.Streams.Writable.jobQueue_eq
#print axioms Whatwg.Streams.Readable.jobQueue_eq
#print axioms Whatwg.Streams.Transform.jobQueue_eq
#print axioms Whatwg.Streams.Writable.tick_dequeue_bridge
#print axioms Whatwg.Streams.Readable.runPullJob_dequeue_bridge
#print axioms Whatwg.Streams.Transform.tick_dequeue_bridge
#print axioms Whatwg.Streams.Writable.attachSink_settled_jobs
#print axioms Whatwg.Streams.Writable.attachSink_pending_jobs
#print axioms Whatwg.Streams.Writable.acceptAnswer_jobs
#print axioms Whatwg.Streams.Transform.reactions_next
#print axioms Whatwg.Streams.Transform.reactions_registered
#print axioms Whatwg.Streams.Transform.reactions_promises
#print axioms Whatwg.Streams.Transform.subscribe_reactions_bridge
#print axioms Whatwg.Streams.Piping.allWrittenSettled_bridge
#print axioms Whatwg.Streams.Piping.writesSettled_bridge
#print axioms Whatwg.Streams.Boundary.Exception.toWebIdl_rangeError
#print axioms Whatwg.Streams.Boundary.Exception.toWebIdl_typeError
#print axioms Whatwg.Streams.Boundary.Exception.toWebIdl_foreign
#print axioms Whatwg.Streams.Boundary.Exception.ofWebIdl_toWebIdl
#print axioms Whatwg.Streams.Boundary.Exception.toWebIdl_injective
#print axioms Whatwg.Streams.Boundary.Exception.toWebIdl_ofRangeError
