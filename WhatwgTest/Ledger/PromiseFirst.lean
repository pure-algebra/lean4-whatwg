import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `PROMISE-PG-FIRST`

The ten edges of `docs/PROMISE-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice A; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history, among it the lane V repair of the seven receipts that reached
`Classical.choice`, stays in `docs/receipts/PROMISE-PG-FIRST.md` and the
rulings.

The trust cell's self-test is the `whatwg_trustselftest` executable: the
table still spells the name ruling R-V3(c) removed (debt D60), and the typed
`Gate` cannot. Ruling R-P20, the one ruling of `COORDINATION.md` that names
this graph (by its document path), is cited by the semantics, laws,
representation, bridges, trust and coverage cells.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The first promise packet's graph over `Whatwg.Ecma262` and `Whatwg.WebIdl`
(slices Q3, Q3b and Q4). -/
def promiseFirst : Graph where
  id := "PROMISE-PG-FIRST"
  document := "docs/PROMISE-DAG.md"
  fence := [`Whatwg.Ecma262.Promise, `Whatwg.Ecma262.Jobs, `Whatwg.WebIdl.Promise,
    `Whatwg.WebIdl.Exceptions]
  acknowledged := ["R-W16"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the generated declaration snapshot that joins each public declaration to exactly one declaration record of the graph document, which has no generator",
        .debt "D47"]
      grounds := [.receipt "Q3 landing", .receipt "Q4 landing, second pass"]
      note := "The six statement batteries' exact ascriptions and the constructor and instance census through the Streams `abbrev`s are delivered, and all 15 class [R] ascriptions of the Q4 battery elaborate since amendment A1." }
    construction := {
      status := .requiredOpen
      remaining := [.named "reachable-state and cross-owner freshness invariants"]
      grounds := [
        .declarations [`Whatwg.Streams.Readable.freshReadCell,
          `Whatwg.Streams.Readable.settleReadCell, `Whatwg.Streams.Readable.settleReadCells],
        .theorems [`Whatwg.Streams.Readable.readTable_freshReadCell,
          `Whatwg.Streams.Readable.readTable_settleReadCell,
          `Whatwg.Streams.Readable.readTable_settleReadCells],
        .receipt "Q4 landing"]
      note := "The `E-22` item is discharged by the three operations and their three bridges." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "the global configuration that threads the activation (the `G-08` remainder)",
        .named "the M2 mask projection",
        .named "the bounded runner"]
      grounds := [.ruling "R-P20", .ruling "R-P24",
        .theorems [`Whatwg.Ecma262.Jobs.run_to_completion,
          `Whatwg.Ecma262.Jobs.run_to_completion_nonvacuous],
        .receipt "Q3b landing"]
      debts := ["D46"]
      note := "COMPLETE (`requirement.jobs.3`), on which R-P20 reopened the edge, is discharged by the two theorems. R-P24 keeps the edge open: `startJob` and `completeJob` are reachable only inside the laws of `Whatwg/Ecma262/Jobs.lean` and `run` never consults the activation, so the remaining items stay P8 work." }
    laws := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Ecma262.JobsLaws 20,
        .receipts `WhatwgTest.Ecma262.PromiseLaws 44,
        .receipts `WhatwgTest.WebIdl.PromiseContract 17,
        .receipts `WhatwgTest.WebIdl.ExceptionsContract 15,
        .receipts `WhatwgTest.Streams.PromiseBridge 42,
        .receipts `WhatwgTest.Ecma262.PromiseFidelityLaws 33,
        .receipts `WhatwgTest.Ecma262.JobsCompleteContract 11,
        .receipts `WhatwgTest.WebIdl.PromiseFidelityContract 13,
        .receipt "Q3 landing", .ruling "R-P20", .receipt "Q3b landing", .ruling "R-P24"]
      note := "182 named receipts are proved: the 125 of the Q3 landing, accepted by R-P20, and the 57 of the Q3b landing, accepted by R-P24." }
    representation := {
      status := .requiredClosed
      grounds := [.receipt "Q3 landing", .ruling "R-P20", .receipt "Q3b landing",
        .receipt "Q4 landing"]
      note := "`Nat` identities with monotone cursors, first-order reactions and jobs, the two reaction lists with their one-list view, the per-cell handled bit with its identity-list bridge, and the exception universe with allocation identity, each by named theorems; `Reaction.capability` added and still `Repr`-only; the P4 to P7 record rows name `Whatwg.Ecma262.Promise` the shared owner with receipts `E-07` to `E-12`." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .rows ⟨"WS-PROM-CE", 26, 26⟩ .seeded,
        .rows ⟨"WS-PROM-CE", 33, 33⟩ .seeded, .rows ⟨"WS-PROM-CE", 36, 38⟩ .seeded]
      grounds := [
        .rows ⟨"WS-PROM-CE", 1, 25⟩ .closed, .ruling "R-W18",
        .rows ⟨"WS-PROM-CE", 27, 32⟩ .closed, .rows ⟨"WS-PROM-CE", 34, 35⟩ .closed,
        .rows ⟨"WS-PROM-CE", 39, 39⟩ .closed, .ruling "R-P24"]
      debts := ["D17"]
      note := "`WS-PROM-CE-015` is closed by R-W18: the reaction type's `DecidableEq` is conditional and by ruling R-W3; `WS-PROM-CE-026`: the capability is stored and never read (debt D17)." }
    bridges := {
      status := .requiredClosed
      grounds := [
        .modules [`WhatwgTest.Streams.PromiseBridge], .receipt "Q3 landing", .ruling "R-P20",
        .theorems [`Whatwg.Streams.Writable.settlementTrace_bridge], .receipt "Q3b landing",
        .theorems [`Whatwg.Streams.Transform.notify_jobQueue_bridge,
          `Whatwg.Streams.Transform.settle_table_bridge,
          `Whatwg.Streams.Transform.settle_jobQueue_order,
          `Whatwg.Streams.Transform.settle_waiting_once,
          `Whatwg.Streams.Transform.runJob_writable_dequeue,
          `Whatwg.Streams.Transform.runJob_writable_blocked],
        .modules [`WhatwgTest.Streams.PromiseBridgeQ4], .receipt "Q4 landing"]
      note := "The 29 Q3 bridging lemmas are proved and the preservation half of the Q3 bridge battery is green; the six `Transform` theorems are the bridges that rows 14 to 16 of §4.4 of the Q3 contract deferred. Deferred with stated reasons, outside this edge's obligation: `E-63`'s readable settlement-trace bridge, and the host profiles and WPT settlement-order replay of P8." }
    targets := {
      status := .notApplicable
      note := "Q3, Q3b and Q4 land no lowering and no generated code; P11 owns the TypeScript target." }
    trust := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Ecma262.JobsLaws 20,
        .receipts `WhatwgTest.Ecma262.PromiseLaws 44,
        .receipts `WhatwgTest.WebIdl.PromiseContract 17,
        .receipts `WhatwgTest.WebIdl.ExceptionsContract 15,
        .receipts `WhatwgTest.Streams.PromiseBridge 42,
        .receipts `WhatwgTest.Ecma262.PromiseFidelityLaws 33,
        .receipts `WhatwgTest.Ecma262.JobsCompleteContract 11,
        .receipts `WhatwgTest.WebIdl.PromiseFidelityContract 13,
        .gate .trustselftest, .receipt "Q3 landing", .receipt "Q3b landing",
        .ruling "R-P20", .ruling "R-P24", .ruling "R-V6", .ruling "R-V8", .ruling "R-V1",
        .gate .build]
      note := "The 182 named receipts are frozen inside the R-11 ceiling, and the trust self-test passed at the Q3b landing. The axiom gate holds `Whatwg.Ecma262`, `Whatwg.WebIdl` and `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "a witness for any row of the Web IDL and ECMA-262 censuses"]
      grounds := [.ruling "R-P20",
        .modules [`WhatwgTest.Audit.WebIdl.SpecCoverage, `WhatwgTest.Audit.Ecma262.SpecCoverage]]
      note := "Ruling R-P20 set the edge `required-open` because both numerator modules exist; every row of both censuses is `absent`. The later sentence of the Q3 landing section that says coverage stays `not-applicable` disagrees with R-P20, and R-P20 wins." } }

end WhatwgTest.Ledger
