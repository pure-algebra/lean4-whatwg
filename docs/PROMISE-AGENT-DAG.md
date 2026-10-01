# Promise-layer agent graph (`PROMISE-PG-AGENT`, slice Q5)

Breaker-authored 2026-10-01 on `review/w9-q5-breaker` from `b0d35e2`, under
ruling R-W3. Contract: `test/contracts/promise-agent-q5.contract.md`. Design:
`docs/research/2026-10-01-w9-agent-effects-design.md`. This file owns the
declaration roles, the existing-type dispositions, the anchor map and the
graph edges of the Q5 packet over `Whatwg.Ecma262`, `Whatwg.WebIdl` and the
new tree `Whatwg.Signatures`. It owns no coverage count, no slice ledger and
no census row: `docs/PROMISE-PACKAGE-PLAN.md` owns the slices,
`docs/PROMISE-EXTRACTION-INVENTORY.md` the extraction rows and gaps, the two
generated censuses the rows, and `docs/PROMISE-DAG.md` the graph
`PROMISE-PG-FIRST` this one bridges to.

Status: frozen and red at the breaker's head. No builder slice has landed and
no edge is closed. No edge closes from a compiling battery.

## Current state

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/PromiseAgent.lean`, rendered to
`generated/graphs/PROMISE-PG-AGENT.md` by `lake exe whatwg_ledger --write`, and
checked by `lake exe whatwg_ledger`. The table this section held before the
ledger is in `docs/receipts/PROMISE-PG-AGENT.md`.

## Authority anchors

The two pinned sources and their aliases are `docs/PROMISE-DAG.md`'s
"Authority anchors" tables, unchanged. Two clause rows are new to the lane:

| Alias | Census row | Span | Span digest |
| --- | --- | --- | --- |
| JOBS | `clause.jobs` | 624525..636548 | `871310fa2bcc46a2c06c2b0cc2e590632270246801336d7188185f0b4b3573bf` |
| PINST | `clause.properties-of-promise-instances` | 2744135..2746691 | `f3c8e70543376d039c9138e95afd153a99dd914f87398ba9208d8b76bd00aa0d` |

Byte offsets are 0-based, ends exclusive, into
`vendor/ecma262-0248456c/spec.html`; no line number is cited.

## Declaration and existing-type records

The owner of each row is the builder of the named slice after this breaker
freezes it; the breaker owns the statements. Every row's route is
`PROMISE-PG-AGENT` with the contributing edge named. Constructors,
projections, derived instances and the batteries' named theorems inherit
their owning row deterministically; the contract's §11 lists every name with
its role, census row, mask and validation class.

| Stable declaration family | Module (slice) | Relationship and existing owner | Disposition / anchor | Edge |
| --- | --- | --- | --- | --- |
| `Ecma262.Agent.Agent`, `.Job`, `.empty` | `Ecma262/Agent.lean` (B1) | new canonical carrier, `G-08` remainder and `G-03`; *contains* the landed `Promise.Table`, `Promise.Reactions` and `Jobs.Queue` (owner `PROMISE-PG-FIRST`) by value, replacing nothing | `owned`; JOBS, PINST | identity, representation |
| `Ecma262.Agent.Op`, `.Op.Answer`, `.step` | `Ecma262/Agent.lean` (B1) | new canonical alphabet and transition; first-order (DB-02) | `owned` | identity, semantics |
| `newPromise`, `settle`, `callFunctions`, `resolve`, `reject`, `mintFor`, `perform`, `markHandled`, `reactionOf`, `startJob`, `finishJob`, `enterScript`, `leaveScript` | `Ecma262/Agent.lean` (B1) | new canonical operations, each over the landed operation it calls (`newPromiseCapability`, `Table.settleAndTrigger`, `Table.settleTraced`, `performPromiseThen`, `Table.markHandled`, `reactionHandlerResult`, `Jobs.completeJob`) | `owned`; NEWCAP, RESOLVING, FULFILL, REJECT, TRIGGER, THEN, HANDLEDOP, REACTJOB, RUNCOND, ONEJOB, COMPLETE, ORDER | semantics |
| `Minted`, `WF` | `Ecma262/Agent.lean` (B1) | new invariant; `WF.settlementsCoherent` is debt D20's coherence | `owned`; CAPREC | construction |
| the views and the D46 and D17 laws | `Ecma262/Agent.lean` (B1) | bridges to `PROMISE-PG-FIRST`'s landed operations, below | `owned` | bridges, laws |
| `Le`, `Cert`, `pre`, `post`, `Implements`, `Op.started`, `runOps` and their laws | `Ecma262/AgentLaws.lean` (B2) | new; the handler-adequacy shape read from lean4-effect4 at `b9d0d19f` (below), no generic law copied | `owned` | laws, construction |
| `WebIdl.Agent.newPromise`, `resolve`, `reject`, `react`, `uponFulfillment`, `uponRejection`, `markAsHandled`, `resolvedWith`, `rejectedWith` | `WebIdl/Agent.lean` (B3) | new adapters over `Ecma262.Agent`; the landed `WebIdl.Promise` operations (owner `PROMISE-PG-FIRST`) keep their statements and become store-level views | `owned`; NEWP, RESOLVE, REJECTOP, REACT, UPONF, UPONR, HANDLEDOP, RESOLVEDW, REJECTEDW | semantics, bridges |
| `Signatures.Ecma262.signature`, `handler`, `handlerAt`, `sumHandler`, `run`, `resolvedWith` and their laws | `Signatures/Ecma262.lean` (B4) | new face over `Ecma262.Agent` and `Effects.Algebra.Sum` (`effects` v0.8.0) | `owned` adapter; no census row | targets |
| existing types gaining instances: `Promise.Reaction` (`DecidableEq`), `Promise.Reactions` (`DecidableEq`, `Repr`), `Promise.ResolvingFunctions` (`Repr`), `Jobs.Active` (`Repr`) | instances in `Ecma262/Agent.lean` (B1); types owned by `PROMISE-PG-FIRST` | `E-29` (generalize): its "must not gain one silently" is superseded by R-W3, conditionally on `body`; `E-50`'s `Repr (Reaction Nat)` receipt stays green | unchanged dispositions | representation |
| `Ecma262.Agent.instDecidableEqExcept` | `Ecma262/Agent.lean` (B1) | scoped, never global (R-W3), because Batteries declares a global `DecidableEq (Except ε α)` | helper | representation |
| `Ecma262.Agent.Coherent` with its seven clause projections; `Coherent.empty`, `.step`, `.runOps`, `.reachable` | `Ecma262/AgentInvariant.lean` (Q5b slice B5) | new invariant that `extends` `WF` (owner B1), replacing nothing (R-W1(b), R-W9); answers gaps A to F of debts D62 and D65 (contract, Addendum Q5b, Q5b.2) | `owned`; RESOLVING, FULFILL, REJECT, TRIGGER, THEN, REACTJOB, `builtin.promise-executor`, `field.promisereaction-records.Type` | construction, counterexamples |
| `Ecma262.Agent.Extends` with its two clause projections; `Extends.refl`, `.trans`, `.step` | `Ecma262/AgentInvariant.lean` (Q5b slice B5) | new order that `extends` `Le` (owner B2), replacing nothing; gap J (Q5b.3) | `owned`; RESOLVING (the one-shot marker) | laws |
| `Ecma262.Agent.postFrom` with its nine equations and `postFrom_post`; `ImplementsFrom`, `ImplementsFrom_iff`, the nine `*_implementsFrom` and `implementsFrom` | `Ecma262/AgentInvariant.lean` (Q5b slice B5) | the second adequacy judgment beside `Implements` (owner B2), over the unchanged `pre`; its post reads the starting agent (Q5b.4); gaps A, D, E and I | `owned`; the rows of the contract's §5 | laws |
| `Ecma262.Agent.callFunctions_resolve_reject`, `finishJob_abrupt`, `finishJob_normal`, `finishJob_abrupt_dropped` | `Ecma262/AgentInvariant.lean` (Q5b slice B5) | laws over `callFunctions` and `finishJob` (owner B1); gap G, and gap H as a named departure (Q5b.5) | `owned`; RESOLVING, CAPREC, REACTJOB | semantics, laws |
| `Signatures.Ecma262.interpret_sumHandler_inr` | `Signatures/Ecma262.lean` (Q5b slice B6) | new face law, the mirror of `interpret_sumHandler_inl` (owner B4); gap K (Q5b.6) | `owned` adapter law; no census row | targets |
| `Ecma262.Agent.find?_map_fst`, `getCell_settle`, `settle_get_other`, `getCell_markHandled`, `markHandled_isSome`, `getCell_fresh`, `get_fresh`, `getCell_fresh_isSome`, `getCell_isSome_of_get`, `WF.getCell_lt`, `WF.getCell_next`, `mem_waitingOn`, `eq_of_nodup_key`, `find?_unique`, `mark_fields`, `resolve_unique`, `reject_unique` | `Ecma262/AgentLaws.lean` (B2; public since ruling R-W20(c)) | helper lemmas of slice B2, published where they stand so that slice B5 copies no proof; statements and proofs unchanged; eight are facts of `Promise.Table` alone, three of lists, one of `Promise.Reactions` and one of `Promise.ResolvingFunctions` (debt D66) | helper; no census row | laws |

## Statement rows

Which battery sections carry each edge's obligations. The batteries are the
authority; the contract is the reading aid.

| Edge | Battery and section |
| --- | --- |
| identity | `WhatwgTest/Ecma262/AgentContract.lean` §§2 and 4 |
| construction | `WhatwgTest/Ecma262/AgentContract.lean` §6; `WhatwgTest/Ecma262/AgentLaws.lean` §§2, 5 and 7 |
| semantics | `WhatwgTest/Ecma262/AgentContract.lean` §§3 and 5; `WhatwgTest/WebIdl/AgentContract.lean` §§1 and 2 |
| laws | `WhatwgTest/Ecma262/AgentContract.lean` §§8 and 9; `WhatwgTest/Ecma262/AgentLaws.lean` §§1, 3, 4, 5 and 6; `WhatwgTest/WebIdl/AgentContract.lean` §4 |
| representation | `WhatwgTest/Ecma262/AgentContract.lean` §§1 and 2 |
| counterexamples | `WhatwgTest/Ecma262/AgentContract.lean` §10; `WhatwgTest/WebIdl/AgentContract.lean` §5; `WhatwgTest/Signatures/Ecma262Contract.lean` §5; and the rejecting laws of contract §15 |
| bridges | `WhatwgTest/Ecma262/AgentContract.lean` §7; `WhatwgTest/WebIdl/AgentContract.lean` §3 |
| targets | `WhatwgTest/Signatures/Ecma262Contract.lean` §§1 to 4 |
| trust | the axiom gate over the four modules once imported by the root (R-W9: no axiom-report module) |
| coverage | none in this slice |
| construction (Q5b) | `WhatwgTest/Ecma262/AgentInvariantContract.lean` §§1 and 2 (`Coherent`, its preservation and reachability), §7 (non-vacuity at reached agents) and §10 (the obstructions the two supporting clauses remove) |
| laws (Q5b) | `WhatwgTest/Ecma262/AgentInvariantContract.lean` §§3 to 6 (`Extends`, `postFrom`, `ImplementsFrom`, the job's two completions) |
| semantics (Q5b) | `WhatwgTest/Ecma262/AgentInvariantContract.lean` §6 (gap G's `[[Reject]]` route and gap H's dropped result) |
| counterexamples (Q5b) | `WhatwgTest/Ecma262/AgentInvariantContract.lean` §§8 and 9, rows `WS-PROM-CE-048` to `056` |
| targets (Q5b) | `WhatwgTest/Signatures/Ecma262SumContract.lean` §§1 and 2 |
| trust (Q5b) | the axiom gate over `Whatwg/Ecma262/AgentInvariant.lean` and the added face law once the two batteries are imported by the root (R-W9: no axiom-report module) |

## Bridges to `PROMISE-PG-FIRST`

Each row relates a landed declaration of `PROMISE-PG-FIRST` to the agent-level
statement that states it as a view (the right side is the landed operation,
not a copy) or lifts its law to the agent.

| `PROMISE-PG-FIRST` (landed) | `PROMISE-PG-AGENT` | Kind | Slice | Mask |
| --- | --- | --- | --- | --- |
| `Promise.Table.settleAndTrigger` | `settleAndTrigger_table`, `settle_eq` | view | B1 | DB-04 M1, DB-04 M2 |
| `Promise.fulfillPromise`, `rejectPromise` | `settle_ok_fulfillPromise`, `settle_error_rejectPromise` | view | B1 | DB-04 M2 |
| `Promise.Table.settleTraced` | `settle_settlements`; `settle_trace` | view; lifted (F6) | B1; B2 | DB-04 M2 |
| `Promise.newPromiseCapability` | `newPromise_capability`, `newPromise_eq` | view | B1 | DB-04 M1 |
| `Promise.Table.markHandled` | `markHandled_table`, `markHandled_get`, `markHandled_eq` | view | B1 | DB-04 M1 |
| `Jobs.startJob` | `startJob_agree` | view | B1 | DB-04 M2 |
| `Promise.performPromiseThen` | `perform_pending`, `perform_fulfilled`, `perform_rejected`; `perform_handled` (F1), `perform_settled_lists` (F2) | view; lifted | B1; B2 | DB-04 M1, DB-04 M2 |
| `Promise.Table.settleAndTrigger_cleared` | `settle_cleared` | lifted (F3) | B2 | DB-04 M1 |
| `Promise.triggerReactions_order` | `react_resolve_enqueues` and its corollaries | lifted (D46) | B1 | DB-04 M2 |
| `Promise.runReactionJob_resolve`, `_reject` | `finishJob_settles_capability`, `finishJob_capability` | lifted (D17) | B1 | DB-04 M1, DB-04 M2 |
| `Promise.runReactionJob_no_capability` | `finishJob_no_capability` | lifted (D18) | B1 | DB-04 M1 |
| `Promise.ResolvingFunctions.callResolve_disables_reject`, `callReject_disables_resolve` | `resolve_then_reject`, `reject_then_resolve` | lifted | B2 | DB-04 M1 |
| `Jobs.run_to_completion`, `Jobs.startJob_blocked` | `startJob_running`, `startJob_blocked` | lifted | B1 | DB-04 M1 |
| `Jobs.run_fifo`, `Jobs.FifoRequirement`, `hostEnqueuePromiseJob_order` | `runOps_fifo`, `runOps_fifoRequirement` | lifted | B2 | DB-04 M2 |
| `WebIdl.Promise.resolve`, `reject` | `resolve_table`, `reject_table`; `WebIdl.Agent.resolve_view`, `reject_view` | view (D46) | B1; B3 | DB-04 M1 |
| `WebIdl.Promise.newPromiseWithCapability` | `WebIdl.Agent.newPromise_view` | view | B3 | DB-04 M1 |
| `WebIdl.Promise.markAsHandled` | `WebIdl.Agent.markAsHandled_view` | view | B3 | DB-04 M1 |

Debts this graph discharges on landing, and the pointers the coordinator adds
then to `docs/PROMISE-DAG.md` (not added by this breaker):

- **D46** (`PROMISE-PG-FIRST` semantics ground: `WebIdl.Promise.resolve` and
  `reject` are `Table.settle` and trigger no reaction): `react_resolve_enqueues`
  and `resolve_table` (B1) with `WebIdl.Agent.react_resolve` and `resolve_view`
  (B3).
- **D17** (`WS-PROM-CE-026`, the capability stored and never read):
  `finishJob_settles_capability` and `WF.capabilityStored` (B1), kept by
  `WF.step` (B2).
- **D20** (no coherence of trace and table, no producer): `settle` produces the
  trace and `WF.settlementsCoherent` relates it to the table.
- **`G-08` remainder** (a global configuration that threads the activation):
  the agent threads it for the promise layer; the Streams configuration's
  cutover onto the agent is W8's.

## Adequacy correspondence

A reading of lean4-effect4's source at `b9d0d19f`
(`src/Effect4/Laws/Effects/Protocol.lean`,
`src/Effect4/Laws/Program/Typed/Adequacy.lean`), recorded as a reading and not
as a claim about that repository, its intent or its gate. Nothing was built
or run there.

| This graph | lean4-effect4 at `b9d0d19f`, as read | Note |
| --- | --- | --- |
| `Agent.WF` | `StoreTyped` | ours is identity and reference coherence over a homogeneous store; theirs is "every value fits its declared type" over a heterogeneous one |
| `Agent.Le` | `World.leHost`; the `le` of `WorldOrder` | `Le.refl`, `Le.trans` fill `WorldOrder`'s `refl`, `trans` |
| `Agent.Cert` (`Unit`) | `StoreCert op`; `Protocol.Cert` | no ghost certificate is needed here |
| `Agent.pre`, `Agent.post` | `storePre`, `storePost`; `Protocol.pre`, `Protocol.post` | `post` is read at the answering agent, as `Typed.vis` reads it |
| `Agent.Implements op` | `StoreImplements root op` | their step is partial (`∃ st' ans`); ours is total, so the existential is the step's own components |
| the nine `*_implements`, `implements` | the per-row `*_implements` | |
| `Le a (step a op).1` as a conjunct | "some later world `w'` with `w.leHost w'`" | their later world is any; ours is the stepped agent |
| `step` total; `pre` is enabledness | "steps, no frontier": `syncOpStep … = some …` | our `pre` of `resolve` and `reject` admits a fired function, where the step is inert and the post holds |
| (not here) `run_adequate` | `storeStep_typed`, iterated along a run | waits until `Protocol` is in the `effects` package (R-W3) |

Where the fit is weakest: the activation posts of `startJob` and `finishJob`
are true at the answering agent only, so `Typed.mono` cannot transport them;
facts a continuation keeps (allocated, settled, handled, minted) are upward
closed in `Le`.

## Evidence ledger

The prototype measurements, the validation class of every law and the
intended-red diagnostics are recorded in the contract's §14 and §19 ("Freeze
receipt"). The coordinator owns root and `known-red` integration and may
append landing receipts here; it may not weaken this packet.
