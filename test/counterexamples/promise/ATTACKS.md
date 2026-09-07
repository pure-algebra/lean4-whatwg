# Promise-layer adversarial packet (`PROMISE-PG-FIRST`, slice Q3)

Breaker-authored 2026-09-07 on `promise/q3-breaker`. Contract:
`test/contracts/promise-first-packet.contract.md`. Graph:
`docs/PROMISE-DAG.md`.

Each row is a tempting implementation of the first promise packet and the
frozen statement that rejects it. The statements live in
`WhatwgTest/Ecma262/{PromiseContract,JobsContract,PromiseLaws,JobsLaws}.lean`,
`WhatwgTest/WebIdl/{PromiseContract,ExceptionsContract}.lean` and
`WhatwgTest/Streams/PromiseBridge.lean`; they are ascriptions and laws, not
finite witness modules. This packet freezes **no** executable witness module:
every attack below is discriminated by a quantified production statement, and
adding finite witnesses is separate later evidence, not a substitute for them.

The stable prefix is `WS-PROM-CE-`. The rows of
`test/counterexamples/REGISTER.md` are the coordinator's to add at integration;
this breaker does not edit the central register.

| ID | Mutant | Rejecting statement |
| --- | --- | --- |
| WS-PROM-CE-001 | collapse `PullAnswer` and `PullReturn` into `PromiseState Unit ε`, since they are isomorphic | decision 6; `Whatwg.Streams.Writable.sinkAnswer_eq`, `sinkReturn_eq`, `sinkReturnToShared_eq`, `sinkReturn_roundtrip` and the six preservation `example`s of `PromiseBridge.lean`, which must close by `rfl` |
| WS-PROM-CE-002 | apply `move` to a function, so a Streams name becomes an `abbrev` over a general function | decision 5 and inventory condition 3; the six equation-lemma `example`s of `PromiseBridge.lean` re-derive `lookupPromise_eq`, `markHandled_eq`, `Transform.lookupPromise_eq` and the three `subscriptionPromise_*` receipts by `rfl`. An `abbrev` has one equation, `f = General.f`, and `simp [f]` in the four `attribute [local simp]` sets stops rewriting |
| WS-PROM-CE-003 | give the general promise state one type parameter, fixing the value to `Unit` | `E-22`; `Whatwg.Streams.Readable.readTable` is ascribed at value `ReadResult α`, and `Whatwg.Ecma262.Promise.State : Type → Type → Type` |
| WS-PROM-CE-004 | give `Outcome` two parameters, so `Outcome.fulfilled` carries a value | `E-02`; `Whatwg.Streams.Readable.PullAnswer.fulfilled : ∀ {ε : Type}, PullAnswer ε` takes no argument, and every `.fulfilled` in `Whatwg/Streams/**` resolves against it |
| WS-PROM-CE-005 | reproduce ES2026's assertion literally, making `settle` partial or undefined on a settled promise | decision 7; `Whatwg.Ecma262.Promise.Table.settle_other` requires the identity on a non-pending cell, and `settle_assert` recovers the assertion as a side condition |
| WS-PROM-CE-006 | represent the table as a replacing map, so allocating overwrites an earlier cell | `E-13`, `E-43`; `Table.fresh_old`, `Table.fresh_eq`, and `Writable.freshPromise_bridge` |
| WS-PROM-CE-007 | reuse an identity, or advance the cursor by something other than one | `E-14`, `E-23`, decision 3; `Table.fresh_id`, `Table.fresh_next`, and the P6 `Transform.initial` and P7 run witnesses that fix concrete identities |
| WS-PROM-CE-008 | implement the job queue as a stack: prepend on enqueue, or consume the newest | `E-45`; `Whatwg.Ecma262.Jobs.Queue.enqueue_eq`, `Queue.dequeue_cons` and the general FIFO law `Queue.dequeue_fifo` |
| WS-PROM-CE-009 | run a job while a synchronous callback frame is live, or while another job is running | `G-08`; `Jobs.step_blocked`, `Jobs.RunCondition_iff`, and the three component bridges `Writable.tick_dequeue_bridge`, `Readable.runPullJob_dequeue_bridge`, `Transform.tick_dequeue_bridge`, whose hypotheses are the three Streams spellings of the empty execution-context stack |
| WS-PROM-CE-010 | let a job scheduled during a run overtake one already scheduled | `requirement.hostenqueuepromisejob.3`; `Queue.dequeue_fifo` with a nonempty `later`, `Jobs.run_fifo` and `Jobs.hostEnqueuePromiseJob_order` |
| WS-PROM-CE-011 | trigger a reaction twice, or notify out of registration order | `E-33`, `G-01`; `triggerReactions_order` (mask M2) and `triggerReactions_once` |
| WS-PROM-CE-012 | keep one undifferentiated reaction list and present it as ES2026's two | decision 8, `G-01`; `Reactions.add_fulfill`, `Reactions.add_reject`, `Reactions.add_paired`, `Reactions.registered_eq` and `Transform.reactions_registered` |
| WS-PROM-CE-013 | make `react` total, returning a value for a promise identity with no cell | `E-31`; `WebIdl.Promise.react_missing`, which keeps the Streams `Option` and records the difference from `PerformPromiseThen` rather than smoothing it |
| WS-PROM-CE-014 | run the handler immediately when `react` finds a settled promise, instead of queueing a reaction job | `E-31`, `E-37`; `react_fulfilled` and `react_rejected` (mask M2), whose right-hand sides are `Queue.enqueue` |
| WS-PROM-CE-015 | derive `DecidableEq` unconditionally on the general reaction or job record | `E-29`, `E-50`; `Transform.Reaction` and `Transform.Job` derive `Repr` only, so `inferInstance : Repr (Reaction Nat)` is ascribed and no `DecidableEq` is |
| WS-PROM-CE-016 | model Web IDL simple exceptions without an allocation identity, as the pinned text does | R-P14, `E-59`; `Exceptions.Exception.simple_eq_iff`, `Exception.identity_simple`, `Boundary.Exception.toWebIdl_injective`, and the frozen `nested_invalid_sizes_fresh_errors` witness in `Whatwg/Streams/Readable/Reentrancy.lean` |
| WS-PROM-CE-017 | re-point `Boundary.Exception` as an `abbrev` of the general exception type | `E-59` is `generalize`, not `move`; the four `Boundary.Exception` ascriptions of `PromiseBridge.lean`'s preservation half keep `.rangeError id` resolving for all 69 dependent theorems |
| WS-PROM-CE-018 | call the settled predicate `wait for all` | `E-55`, `G-06`; `AllSettled` and `waitForAll` are separate names with separate laws, and `waitForAll_success`/`waitForAll_failure` state the ordered result and the short-circuit the predicate does not have |
| WS-PROM-CE-019 | move `handled` into the cell and drop the relation to the Streams identity list | decision 9; `Writable.handled_bridge` and `Writable.markHandled_bridge` |
| WS-PROM-CE-020 | ignore `[[AlreadyResolved]]`, so a resolving function can settle its promise twice | `G-03`; `ResolvingFunctions.callResolve_alreadyResolved` and `callReject_alreadyResolved` |
| WS-PROM-CE-021 | report a later rejection instead of the first when `wait for all` short-circuits | `waitForAll_failure` (mask M2), whose hypothesis fixes every earlier identity as fulfilled |
| WS-PROM-CE-022 | give the `DOMException` name table 33 entries by adding `QuotaExceededError`, or repeat a name | R-P10; `Exceptions.Name.all_length = 32`, `Name.all_nodup`, `Name.all_complete`. At this pin `QuotaExceededError` is a derived interface (`idl.quota-exceeded-error`, 213527..213598) and the census has no `type.` row for it |

Two attacks the packet deliberately does **not** discriminate, because their
subject is out of scope and a statement about them would overclaim:

- adoption of an arbitrary thenable (`G-05`, `op.newpromiseresolvethenablejob`,
  2705599..2707541). `Transform.Completion.adopt` (`E-35`) adopts an internal
  identity and is `keep`; no statement here presents it as adoption.
- a rejection tracker reading the handled bit (`G-02`,
  `hook.host-promise-rejection-tracker`, 2701220..2702791). Nothing reads the
  bit in this packet, and `markHandled_state` says only that marking does not
  change the promise state.

Verification: the rejecting statements are checked by the six batteries' own
narrow commands, recorded in the contract's "Freeze receipt". No host was run
and no WPT case was replayed for this packet.
