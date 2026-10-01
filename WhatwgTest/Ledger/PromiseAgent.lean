import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `PROMISE-PG-AGENT`

The ten edges of `docs/PROMISE-AGENT-DAG.md`
(`test/contracts/graph-ledger.contract.md`, slice B; ruling R-W6), encoded from
that document's "Current state" table. Every status is the table's: every edge
`required-open`, as frozen at the breaker's head (ruling R-W13).

The table describes the breaker's head, before any builder slice. Ruling R-W16
landed slice Q5 after it: the four batteries are green and unedited, debt D46
is repaired, rows `WS-PROM-CE-040` to `047` are `CLOSED`, and no edge changes
status because the independent review reads the slice first. Where the table
and R-W16 disagree, the ruling wins (R-V4): what the table calls red until a
slice lands is recorded here as a ground the landing discharged, citing R-W16,
and every cell but coverage names the independent review as a remaining item.
R-W16 also recorded debts D62 and D65, what the builders found weaker than the
specification text; addendum Q5b answered both (next paragraph).

Ruling R-W21 landed addendum Q5b: the invariant `Coherent`, the order
`Extends`, the second judgment `ImplementsFrom`, the laws of the reaction
job's two completions and the face law `interpret_sumHandler_inr`. It closes
debts D62 and D65, records what Q5b leaves as debt D67, closes rows
`WS-PROM-CE-048` to `056` and changes no edge. The construction, semantics,
laws, counterexamples and targets cells cite it.

R-W3 (which adopted the graph), R-W5, R-W9, R-P20, R-W16 and R-W21 are cited
where the cells use them. R-W6 and R-W13 name the graph and change no edge;
they are acknowledged.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The agent graph of promise slice Q5 over `Whatwg.Ecma262.Agent`,
`Whatwg.WebIdl.Agent` and `Whatwg.Signatures`. -/
def promiseAgent : Graph where
  id := "PROMISE-PG-AGENT"
  document := "docs/PROMISE-AGENT-DAG.md"
  fence := [`Whatwg.Ecma262.Agent, `Whatwg.Ecma262.AgentLaws, `Whatwg.Ecma262.AgentInvariant,
    `Whatwg.WebIdl.Agent, `Whatwg.Signatures.Ecma262]
  dependsOn := ["PROMISE-PG-FIRST"]
  acknowledged := ["R-W6", "R-W13"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the generated declaration snapshot that joins each public declaration to exactly one record row of the graph document, which has no generator",
        .debt "D47",
        .named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [.modules [`WhatwgTest.Ecma262.AgentContract],
        .declarations [`Whatwg.Ecma262.Agent.Agent, `Whatwg.Ecma262.Agent.Job,
          `Whatwg.Ecma262.Agent.Op, `Whatwg.Ecma262.Agent.Op.Answer, `Whatwg.Ecma262.Agent.step],
        .ruling "R-W16", .ruling "R-W5"]
      note := "The B1 battery's record, alphabet and instance ascriptions (its §§1 to 4: `Agent.Agent` with its nine projections, `Agent.Job`, `Agent.Op` with its nine constructors, `Op.Answer`, `step` and the nine `step_*` answer-type equations) are green since slice B1 landed (R-W16). R-W5 names `Whatwg.Ecma262.Agent` among the first prefixes to join the snapshot." }
    construction := {
      status := .requiredOpen
      remaining := [.named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [
        .declarations [`Whatwg.Ecma262.Agent.empty, `Whatwg.Ecma262.Agent.Minted,
          `Whatwg.Ecma262.Agent.WF],
        .theorems [`Whatwg.Ecma262.Agent.WF.get_lt, `Whatwg.Ecma262.Agent.WF.empty,
          `Whatwg.Ecma262.Agent.WF.step, `Whatwg.Ecma262.Agent.WF.runOps],
        .modules [`WhatwgTest.Ecma262.AgentContract, `WhatwgTest.Ecma262.AgentLaws],
        .ruling "R-W16",
        .declarations [`Whatwg.Ecma262.Agent.Coherent],
        .theorems [`Whatwg.Ecma262.Agent.Coherent.empty, `Whatwg.Ecma262.Agent.Coherent.step,
          `Whatwg.Ecma262.Agent.Coherent.runOps, `Whatwg.Ecma262.Agent.Coherent.reachable],
        .modules [`WhatwgTest.Ecma262.AgentInvariantContract], .ruling "R-W21"]
      debts := ["D67"]
      note := "`Agent.empty`, `Minted` and the fourteen clauses of `WF` (B1 battery §6) with `WF.get_lt`, and `WF.empty`, `WF.step` and `WF.runOps` (B2 battery §2 and §5), which make every agent `runOps` reaches from `Agent.empty` well formed, are green since slices B1 and B2 landed (R-W16). `Coherent` extends `WF` with seven clauses, holds at `Agent.empty` and is kept by `step` for every operation, so it holds of every agent `runOps` reaches from `Agent.empty` (B5 battery §§1 and 2, R-W21). Debt D67 records two facts of reachable agents that `Coherent` does not state." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "the independent reviewer's fidelity check per operation against the sealed bytes (the design's §6.4): `op.fulfillpromise`, `op.rejectpromise`, `op.triggerpromisereactions`, `op.performpromisethen`, `op.newpromisereactionjob`, `op.createresolvingfunctions`, and Web IDL `op.resolve`, `op.reject` and react, with every departure named (§16 of the contract)",
        .named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [.modules [`Whatwg.Ecma262.Agent, `Whatwg.WebIdl.Agent,
          `WhatwgTest.Ecma262.AgentContract, `WhatwgTest.WebIdl.AgentContract],
        .ruling "R-W16",
        .theorems [`Whatwg.Ecma262.Agent.callFunctions_resolve_reject,
          `Whatwg.Ecma262.Agent.finishJob_abrupt, `Whatwg.Ecma262.Agent.finishJob_normal,
          `Whatwg.Ecma262.Agent.finishJob_abrupt_dropped],
        .ruling "R-W21"]
      debts := ["D67"]
      note := "The nine operations and their defining equations, every disabled branch included (B1 battery §§3 to 5), and the Web IDL verbs and their equations (B3 battery §§1 and 2) are green since slices B1 and B3 landed (R-W16). The four departures the Q5 contract did not name are answered by addendum Q5b (R-W21): an abrupt result goes through `[[Reject]]` (`finishJob_abrupt`, by `callFunctions_resolve_reject`), the two clauses `Coherent.jobsTyped` and `Coherent.reactionsAllocated` are stated, and the one departure the model keeps, an abrupt result dropped when `[[Capability]]` is undefined, is the theorem `finishJob_abrupt_dropped` (debt D67)." }
    laws := {
      status := .requiredOpen
      remaining := [.named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [
        .theorems [`Whatwg.Ecma262.Agent.react_resolve_enqueues,
          `Whatwg.Ecma262.Agent.react_resolve_enqueues_wf,
          `Whatwg.Ecma262.Agent.react_resolve_enqueues_exactly,
          `Whatwg.Ecma262.Agent.finishJob_settles_capability,
          `Whatwg.Ecma262.Agent.startJob_running, `Whatwg.Ecma262.Agent.implements,
          `Whatwg.WebIdl.Agent.react_resolve],
        .declarations [`Whatwg.Ecma262.Agent.Le, `Whatwg.Ecma262.Agent.Cert,
          `Whatwg.Ecma262.Agent.pre, `Whatwg.Ecma262.Agent.post,
          `Whatwg.Ecma262.Agent.Implements],
        .modules [`WhatwgTest.Ecma262.AgentContract, `WhatwgTest.Ecma262.AgentLaws,
          `WhatwgTest.WebIdl.AgentContract],
        .ruling "R-W16",
        .declarations [`Whatwg.Ecma262.Agent.Extends, `Whatwg.Ecma262.Agent.postFrom,
          `Whatwg.Ecma262.Agent.ImplementsFrom],
        .theorems [`Whatwg.Ecma262.Agent.Extends.refl, `Whatwg.Ecma262.Agent.Extends.trans,
          `Whatwg.Ecma262.Agent.Extends.step, `Whatwg.Ecma262.Agent.postFrom_post,
          `Whatwg.Ecma262.Agent.ImplementsFrom_iff, `Whatwg.Ecma262.Agent.implementsFrom],
        .modules [`WhatwgTest.Ecma262.AgentInvariantContract], .ruling "R-W21"]
      debts := ["D66"]
      note := "The D46 law `react_resolve_enqueues` with `_wf` and `_exactly`, `finishJob_settles_capability` and `startJob_running` (B1 battery §§8 and 9); `Le`, `Cert`, `pre`, `post`, `Implements`, the nine `*_implements` and `implements`, and the lifted laws (B2 battery §§1, 3 to 6); and `WebIdl.Agent.react_resolve` (B3 battery §4) are landed and green (R-W16), which repairs debt D46. Addendum Q5b (R-W21) adds the order `Extends`, the two-state post `postFrom` and the second judgment `ImplementsFrom` over the unchanged `pre`, with one theorem per operation and `implementsFrom` for all nine (B5 battery §§3 to 5); the Q5 declarations keep their text. Debt D66 records that the single-agent form of the post with a certificate is not stated." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [.ruling "R-W3", .rows ⟨"WS-PROM-CE", 15, 15⟩ .closed, .ruling "R-W18",
        .declarations [`Whatwg.Ecma262.Agent.Agent, `Whatwg.Ecma262.Promise.Table,
          `Whatwg.Ecma262.Promise.Reactions, `Whatwg.Ecma262.Jobs.Queue,
          `Whatwg.Ecma262.Agent.instDecidableEqExcept],
        .modules [`WhatwgTest.Ecma262.AgentContract], .ruling "R-W16"]
      note := "The record contains the landed `Promise.Table`, `Promise.Reactions` and reaction-job `Jobs.Queue` by value; three cursors, the job serial is the reaction identity, the queue payload is fixed and every type is in `Type` (R-W3); the instance set of B1 battery §1 includes the `#guard_msgs`-pinned refusal of a global `DecidableEq (Except ε α)`. R-W18 records `WS-PROM-CE-015` `CLOSED`, the re-disposition R-W3 owed at the Q5 landing." }
    counterexamples := {
      status := .requiredOpen
      remaining := [.named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [.rows ⟨"WS-PROM-CE", 40, 47⟩ .closed, .ruling "R-W16",
        .rows ⟨"WS-PROM-CE", 48, 56⟩ .closed, .ruling "R-W21"]
      note := "Each row closes when its rejecting statements are green and its finite witness elaborates; R-W16 records rows 040 to 047 `CLOSED` and R-W21 rows 048 to 056, the well-formed agents that `Coherent`, `Extends` and `postFrom` refuse (B5 battery §§8 and 9)." }
    bridges := {
      status := .requiredOpen
      remaining := [.named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [
        .theorems [`Whatwg.Ecma262.Agent.settleAndTrigger_table, `Whatwg.Ecma262.Agent.settle_eq,
          `Whatwg.Ecma262.Agent.settle_ok_fulfillPromise,
          `Whatwg.Ecma262.Agent.settle_error_rejectPromise,
          `Whatwg.Ecma262.Agent.settle_settlements, `Whatwg.Ecma262.Agent.settle_trace,
          `Whatwg.Ecma262.Agent.newPromise_capability, `Whatwg.Ecma262.Agent.newPromise_eq,
          `Whatwg.Ecma262.Agent.markHandled_table, `Whatwg.Ecma262.Agent.markHandled_get,
          `Whatwg.Ecma262.Agent.markHandled_eq, `Whatwg.Ecma262.Agent.startJob_agree,
          `Whatwg.Ecma262.Agent.perform_pending, `Whatwg.Ecma262.Agent.perform_fulfilled,
          `Whatwg.Ecma262.Agent.perform_rejected, `Whatwg.Ecma262.Agent.perform_handled,
          `Whatwg.Ecma262.Agent.perform_settled_lists, `Whatwg.Ecma262.Agent.settle_cleared,
          `Whatwg.Ecma262.Agent.react_resolve_enqueues,
          `Whatwg.Ecma262.Agent.finishJob_settles_capability,
          `Whatwg.Ecma262.Agent.finishJob_capability,
          `Whatwg.Ecma262.Agent.finishJob_no_capability,
          `Whatwg.Ecma262.Agent.resolve_then_reject, `Whatwg.Ecma262.Agent.reject_then_resolve,
          `Whatwg.Ecma262.Agent.startJob_running, `Whatwg.Ecma262.Agent.startJob_blocked,
          `Whatwg.Ecma262.Agent.runOps_fifo, `Whatwg.Ecma262.Agent.runOps_fifoRequirement,
          `Whatwg.Ecma262.Agent.resolve_table, `Whatwg.Ecma262.Agent.reject_table,
          `Whatwg.WebIdl.Agent.resolve_view, `Whatwg.WebIdl.Agent.reject_view,
          `Whatwg.WebIdl.Agent.newPromise_view, `Whatwg.WebIdl.Agent.markAsHandled_view],
        .ruling "R-W16"]
      note := "The views onto `PROMISE-PG-FIRST`'s landed operations and the lifted laws, the rows of the graph document's section \"Bridges to `PROMISE-PG-FIRST`\", are green since slices B1, B2 and B3 landed (R-W16)." }
    targets := {
      status := .requiredOpen
      remaining := [.named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [
        .declarations [`Whatwg.Signatures.Ecma262.signature, `Whatwg.Signatures.Ecma262.handler,
          `Whatwg.Signatures.Ecma262.handlerAt, `Whatwg.Signatures.Ecma262.sumHandler,
          `Whatwg.Signatures.Ecma262.run],
        .modules [`Whatwg.Signatures.Ecma262, `WhatwgTest.Signatures.Ecma262Contract],
        .ruling "R-W16",
        .theorems [`Whatwg.Signatures.Ecma262.interpret_sumHandler_inr],
        .modules [`WhatwgTest.Signatures.Ecma262SumContract], .ruling "R-W21"]
      note := "The `Effects.Signature` face (B4 battery) with its agreement laws, the Lake library `WhatwgSignatures` in `defaultTargets`, the umbrella import in `Whatwg.lean` that makes the audit root reach it, and the toy consumer sum of the battery's §4 are landed (R-W16). The face law `interpret_sumHandler_inr`, the consumer's half of the sum, landed with addendum Q5b (B6 battery, R-W21). No lowering and no generated code: P11 owns the TypeScript target." }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the independent review of slice Q5, before which R-W16 changes no edge"]
      grounds := [.gate .build, .gate .leanchecker, .ruling "R-W3", .ruling "R-W16",
        .ruling "R-W9", .gate .trustselftest, .ruling "R-W24"]
      note := "Every declaration under `Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Signatures` is inside `propext` and `Quot.sound`, enforced by the axiom gate with `Whatwg.Signatures` as the sixth strict prefix and no exception, and `lake env leanchecker` over the three library prefixes exits 0 (R-W16). With slice Q5 and addendum Q5b on `main`, the trust self-test passes every check against an empty declared red set and `lake exe whatwg_trustgate` prints the in-tree gate's summary line (R-W24). No axiom-report module is written (R-W9)." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "the coverage seat's step-by-step join of the six ES2026 candidates for `green`: `requirement.jobs.1`, `.2`, `.3`, `requirement.hostenqueuepromisejob.3`, `op.fulfillpromise` and `op.triggerpromisereactions`"]
      grounds := [.modules [`WhatwgTest.Audit.WebIdl.SpecCoverage, `WhatwgTest.Audit.Ecma262.SpecCoverage],
        .ruling "R-P20", .ruling "R-W16"]
      note := "Both numerator modules exist, which is R-P20's ground for `required-open`. This slice moves no row: the ES2026 and Web IDL coverage blocks are unchanged (R-W16)." } }

end WhatwgTest.Ledger
