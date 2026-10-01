# Receipts log of `PROMISE-PG-AGENT`

This log holds the history of `docs/PROMISE-AGENT-DAG.md`. Under ruling R-W6
the ledger builder of slice B moved the block below out of that document
verbatim on 2026-10-01, from commit `5999363`, under the heading given. The
line under the heading says where the block came from and is the only line
added. The current state of every edge is the ledger entry
`WhatwgTest/Ledger/PromiseAgent.lean`, projected to
`generated/graphs/PROMISE-PG-AGENT.md`.

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/PROMISE-AGENT-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/PromiseAgent.lean` and its projection `generated/graphs/PROMISE-PG-AGENT.md` supersede it.

This table describes the breaker's head on `review/w9-q5-breaker`,
2026-10-01, before any builder slice. Ruling R-V4 sets the rule: an edge is
`required-closed` only when every ground this document or a ruling in
`COORDINATION.md` states for keeping it open is discharged by something named
in the ground cell. Where a document and a later ruling disagree, the ruling
wins and the cell names it.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The B1 battery's record, alphabet and instance ascriptions (its §§1 to 4: `Agent.Agent` with its nine projections, `Agent.Job`, `Agent.Op` with its nine constructors, `Op.Answer`, `step` and the nine `step_*` answer-type equations) are red until slice B1 lands. The generated declaration snapshot that joins each public declaration to exactly one record row below has no generator (debt D47); R-W5 names `Whatwg.Ecma262.Agent` among the first prefixes to join it |
| construction | `required-open` | `Agent.empty`, `Minted` and the fourteen clauses of `WF` (B1 battery §6) with `WF.get_lt`; `WF.empty`, `WF.step` and `WF.runOps` (B2 battery §2 and §5), which make every agent `runOps` reaches from `Agent.empty` well formed. All red until B1 and B2 land |
| semantics | `required-open` | The nine operations and their defining equations, every disabled branch included (B1 battery §§3 to 5); the Web IDL verbs and their equations (B3 battery §§1 and 2). Beyond the batteries, the independent reviewer's fidelity check per operation against the sealed bytes (the design's §6.4): `op.fulfillpromise`, `op.rejectpromise`, `op.triggerpromisereactions`, `op.performpromisethen`, `op.newpromisereactionjob`, `op.createresolvingfunctions`, and Web IDL `op.resolve`, `op.reject` and react, with every departure named (§16 of the contract) |
| laws | `required-open` | The D46 law `react_resolve_enqueues` with `_wf` and `_exactly`, `finishJob_settles_capability` and `startJob_running` (B1 battery §§8 and 9); `Le`, `Cert`, `pre`, `post`, `Implements`, the nine `*_implements` and `implements`, and the lifted laws (B2 battery §§1, 3 to 6); `WebIdl.Agent.react_resolve` (B3 battery §4). All 130 theorem obligations were proved in an uncommitted prototype (contract §14); none is landed |
| representation | `required-open` | The record contains the landed `Promise.Table`, `Promise.Reactions` and reaction-job `Jobs.Queue` by value; three cursors, the job serial is the reaction identity, the queue payload is fixed and every type is in `Type` (R-W3); the instance set of B1 battery §1, including the `#guard_msgs`-pinned refusal of a global `DecidableEq (Except ε α)`. `WS-PROM-CE-015` is re-dispositioned at the Q5 landing (R-W3) |
| counterexamples | `required-open` | Eight rows of `test/counterexamples/REGISTER.md`, `WS-PROM-CE-040` to `047`, stand `SEEDED` (contract §15); each closes when its rejecting statements are green and its finite witness elaborates |
| bridges | `required-open` | The views onto `PROMISE-PG-FIRST`'s landed operations and the lifted laws, §"Bridges to `PROMISE-PG-FIRST`" below, red until B1, B2 and B3 land |
| targets | `required-open` | The `Effects.Signature` face (B4 battery): `signature`, `handler`, `handlerAt`, `sumHandler`, `run` and the agreement laws, the Lake library `WhatwgSignatures` in `defaultTargets`, the umbrella import in `Whatwg.lean` that makes the audit root reach it, and the toy consumer sum of the battery's §4. No lowering and no generated code: P11 owns the TypeScript target |
| trust | `required-open` | Every declaration under `Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Signatures` inside `propext` and `Quot.sound`, enforced by the axiom gate with `Whatwg.Signatures` as the sixth strict prefix (the coordinator's entry at the B4 landing) and no exception; `lake env leanchecker` over the new modules; `lake exe whatwg_trustselftest` at the landing. Measured with the prototype only (contract §14: six prefixes, zero exceptions, 531 new `Whatwg` declarations, none reaching `Classical.choice`); no axiom-report module is written (R-W9) |
| coverage | `required-open` | Both numerator modules, `WhatwgTest/Audit/WebIdl/SpecCoverage.lean` and `WhatwgTest/Audit/Ecma262/SpecCoverage.lean`, exist, which is R-P20's ground for `required-open`. This slice moves no row. Six ES2026 rows are candidates for `green` once the coverage seat joins them step by step: `requirement.jobs.1`, `.2`, `.3`, `requirement.hostenqueuepromisejob.3`, `op.fulfillpromise` and `op.triggerpromisereactions` |
