import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `TRANSFORM-PG-BACKPRESSURE`

The ten edges of `docs/TRANSFORM-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history, among it the lane V repair of the four receipts that reached
`Classical.choice`, stays in `docs/receipts/TRANSFORM-PG-BACKPRESSURE.md` and
the rulings.

The trust cell cites R-V8, which names this graph by its short name ("the
TRANSFORM graph") and records its trust row. Ruling R-W14 adds the two
bridges onto `Kernel.Path` to the semantics edge, changes no status, and says
the ledger records them at seeding; that cell cites it. No ruling of
`COORDINATION.md` names this graph by identifier or document path, so the
entry acknowledges none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The transform backpressure graph of phase P6a. -/
def transformBackpressure : Graph where
  id := "TRANSFORM-PG-BACKPRESSURE"
  document := "docs/TRANSFORM-DAG.md"
  fence := [`Whatwg.Streams.Transform.Stream, `Whatwg.Streams.Transform.Backpressure,
    `Whatwg.Streams.Transform.DefaultController, `Whatwg.Streams.Transform.Step,
    `Whatwg.Streams.Transform.Observation, `Whatwg.Streams.Transform.Laws,
    `Whatwg.Streams.Transform.Runs]
  dependsOn := ["DATA-PG-QUEUE", "READABLE-PG-DEFAULT", "WRITABLE-PG-DEFAULT",
    "PROMISE-PG-FIRST"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the generated public-declaration snapshot and its joins, which have no generator",
        .debt "D47"]
      grounds := [.receipt "P6a landing receipt"] }
    construction := {
      status := .requiredOpen
      remaining := [.named "valid ports", .named "fresh and shared allocation",
        .named "unique subscriptions", .named "retained callback identity",
        .named "trace-prefix validity", .named "inductive reachable-state invariants"]
      grounds := [.receipt "P6a landing receipt"]
      note := "Raw states can violate them." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "full-state embeddings", .named "global ECMAScript job order",
        .named "promise adoption and registration"]
      grounds := [.receipt "P6a landing receipt", .ruling "R-W14",
        .theorems [`Whatwg.Streams.Transform.step_iff_stage,
          `Whatwg.Streams.Transform.reaches_iff_path]]
      note := "The bridges `step_iff_stage` and `reaches_iff_path` onto `Kernel.Path` are grounds of this edge by R-W14, which changes no status." }
    laws := {
      status := .requiredClosed
      grounds := [.modules [`Whatwg.Streams.Transform.Laws, `Whatwg.Streams.Transform.Runs],
        .theorems [`Whatwg.Streams.Transform.coupled_write_read_enqueue,
          `Whatwg.Streams.Transform.coupled_error_during_transform,
          `Whatwg.Streams.Transform.coupled_positive_readable_capacity],
        .receipts `WhatwgTest.Streams.Transform.BackpressureAxiomReport 118,
        .receipt "P6a landing receipt"]
      note := "The 115 frozen local equations and the three composed runs are proved; the 118 named receipts print." }
    representation := {
      status := .requiredOpen
      remaining := [.named "full-state embeddings", .named "global ECMAScript job order",
        .named "promise adoption and registration", .named "numeric boundaries"]
      grounds := [.receipt "P6a landing receipt",
        .declarations [`Whatwg.Ecma262.Promise.Reactions, `Whatwg.Streams.Transform.reactions],
        .edge "PROMISE-PG-FIRST" .bridges]
      note := "Subscriptions are a view of `Whatwg.Ecma262.Promise.Reactions`, and the `notify`, `settle` and `runJob` bridges Q4 landed are `PROMISE-PG-FIRST` bridge evidence." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-TRANS-CE", 1, 14⟩ .closed, .receipt "P6a landing receipt"]
      note := "The rows are closed with their linked production laws, for the exact local scope the register records." }
    bridges := {
      status := .requiredOpen
      remaining := [.named "full-state embeddings", .named "global ECMAScript job order",
        .named "promise adoption and registration", .named "numeric boundaries",
        .named "host relations"]
      grounds := [.receipt "P6a landing receipt"]
      note := "The four Node observations are finite host observations, compared with no Lean run." }
    targets := {
      status := .notApplicable
      note := "This representative generates no target code; P11 owns lowering." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Transform.BackpressureAxiomReport 118,
        .gate .build, .receipt "P6a landing receipt", .ruling "R-V1", .ruling "R-V6",
        .ruling "R-V8"]
      note := "The 118 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent implementation and proof review passed. The axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the clause map and the test-side numerator witnesses"]
      grounds := [.receipt "P6a landing receipt"]
      note := "The packet adds no coverage claim." } }

end WhatwgTest.Ledger
