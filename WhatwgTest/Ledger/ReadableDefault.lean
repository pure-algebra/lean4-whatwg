import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `READABLE-PG-DEFAULT`

The ten edges of `docs/READABLE-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history, among it the lane V repair of the two `readTable` theorems
that reached `Classical.choice`, stays in `docs/receipts/READABLE-PG-DEFAULT.md`
and the rulings.

Ruling R-W14 adds the W8a invariant `Readable.QueueInv` to the construction
edge and the two bridges onto `Kernel.Path` to the semantics edge, changes no
status, and says the ledger records them at seeding; both cells cite it. No
ruling of `COORDINATION.md` names this graph by identifier or document path,
so the entry acknowledges none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The default-readable graph of phase P4a. -/
def readableDefault : Graph where
  id := "READABLE-PG-DEFAULT"
  document := "docs/READABLE-DAG.md"
  fence := [`Whatwg.Streams.Boundary.Exception, `Whatwg.Streams.Readable.State,
    `Whatwg.Streams.Readable.DefaultController, `Whatwg.Streams.Readable.DefaultReader,
    `Whatwg.Streams.Readable.Step, `Whatwg.Streams.Readable.Laws,
    `Whatwg.Streams.Readable.Reentrancy, `Whatwg.Streams.Readable.Invariants]
  dependsOn := ["DATA-PG-QUEUE", "PROMISE-PG-FIRST"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the generated declaration snapshot and its joins to the declaration table, which has no generator",
        .debt "D47"]
      grounds := [.receipts `WhatwgTest.Streams.Readable.DefaultContract 94,
        .receipt "P4a landing receipt"]
      note := "The exact ascriptions, constructor census and shared-reason retraction landed with the 94 receipts." }
    construction := {
      status := .requiredOpen
      remaining := [.named "reachable-state and fresh-ID invariants"]
      grounds := [.receipt "P4a landing receipt", .ruling "R-W14",
        .declarations [`Whatwg.Streams.Readable.QueueInv],
        .theorems [`Whatwg.Streams.Readable.step_queueInv,
          `Whatwg.Streams.Readable.steps_queueInv,
          `Whatwg.Streams.Readable.initial_queueInv]]
      note := "`QueueInv` holds at `initial`, and every step from a state where it holds reaches a state where it holds; R-W14 adds it to this edge as a ground and changes no status." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "the full-state embedding", .named "the shared-allocation embedding",
        .named "the global-job embedding", .named "the promise-object embedding"]
      grounds := [.receipt "P4a landing receipt",
        .declarations [`Whatwg.Streams.Readable.Steps], .ruling "R-W14",
        .theorems [`Whatwg.Streams.Readable.step_eq_graph,
          `Whatwg.Streams.Readable.steps_iff_path]]
      note := "`Steps` composes external decisions only; it does not interleave internal jobs or prove a global run law. The bridges `step_eq_graph` and `steps_iff_path` onto `Kernel.Path` are grounds of this edge by R-W14, which changes no status." }
    laws := {
      status := .requiredClosed
      grounds := [.modules [`WhatwgTest.Streams.Readable.DefaultContract],
        .receipts `WhatwgTest.Streams.Readable.DefaultContract 94,
        .receipt "P4a landing receipt"]
      note := "Every quantified equation of the contract battery is proved: the 94 named theorems frozen with their axiom sets." }
    representation := {
      status := .requiredOpen
      remaining := [.named "the full-state embedding", .named "the shared-allocation embedding",
        .named "the global-job embedding", .named "the promise-object embedding",
        .named "the host-profile embedding"]
      grounds := [.receipt "P4a landing receipt",
        .declarations [`Whatwg.Streams.Readable.PromiseState, `Whatwg.Ecma262.Promise.State]]
      note := "`Readable.PromiseState` is a view of `Whatwg.Ecma262.Promise.State` (`E-01`), as the declaration table records." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-READ-CE", 1, 17⟩ .closed]
      debts := ["D50"]
      note := "The rows are closed for this local projection only. The witness module `WhatwgTest/Streams/Counterexamples/Readable/Default.lean` imports no production module, so the attack-to-statement link is stated in the register rather than checked in Lean." }
    bridges := {
      status := .requiredOpen
      remaining := [.named "the full-state projection",
        .named "the host-profile relation, including exact arithmetic against binary64 and promise-reaction registration"]
      note := "P4a asserts no host relation." }
    targets := {
      status := .notApplicable
      note := "P4a has no lowering or generated code; P11 owns that obligation." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Readable.DefaultContract 94, .gate .build,
        .receipt "P4a landing receipt",
        .theorems [`Whatwg.Streams.Readable.readTable_settleReadCell,
          `Whatwg.Streams.Readable.readTable_settleReadCells],
        .edge "CONFIGURATION-PG-ORDERING" .trust, .ruling "R-V6"]
      note := "The 94 named receipts are frozen inside the R-11 ceiling and none reaches `Classical.choice`; the exhaustive root audit, the builds, the gates and independent review passed. The two public theorems of `Whatwg/Streams/Readable/Laws.lean`, `readTable_settleReadCell` and `readTable_settleReadCells`, with the two private helpers beneath them, are Q4 receipts of `CONFIGURATION-PG-ORDERING`, and no declaration under `Whatwg.Streams` reaches `Classical.choice` (R-V6)." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the clause map of the graph document and the test-side numerator witnesses for its rows"]
      grounds := [.receipt "P4a landing receipt"] } }

end WhatwgTest.Ledger
