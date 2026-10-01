import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `WRITABLE-PG-DEFAULT`

The ten edges of `docs/WRITABLE-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history, among it the lane V repair of the two lifecycle receipts that
reached `Classical.choice`, stays in `docs/receipts/WRITABLE-PG-DEFAULT.md` and
the rulings.

The trust cell cites R-V8, which names this graph by its short name ("the
WRITABLE graph") and records its trust row. Ruling R-W14 adds the W8a
invariant `Writable.QueueInv` to the construction edge and the two bridges onto
`Kernel.Path` to the semantics edge, changes no status, and says the ledger
records them at seeding; both cells cite it. No ruling of `COORDINATION.md`
names this graph by identifier or document path, so the entry acknowledges
none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The default-writable graph of phase P5a. -/
def writableDefault : Graph where
  id := "WRITABLE-PG-DEFAULT"
  document := "docs/WRITABLE-DAG.md"
  fence := [`Whatwg.Streams.Writable.Stream, `Whatwg.Streams.Writable.Backpressure,
    `Whatwg.Streams.Writable.DefaultController, `Whatwg.Streams.Writable.DefaultWriter,
    `Whatwg.Streams.Writable.Step, `Whatwg.Streams.Writable.Laws,
    `Whatwg.Streams.Writable.Lifecycle, `Whatwg.Streams.Writable.Invariants]
  dependsOn := ["DATA-PG-QUEUE", "READABLE-PG-DEFAULT", "PROMISE-PG-FIRST"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the generated public-declaration snapshot and its joins, which have no generator",
        .debt "D47"]
      grounds := [.receipt "P5a landing receipt"] }
    construction := {
      status := .requiredOpen
      remaining := [.named "the valid initial and full-state projection",
        .named "the queue/request and close-sentinel invariants",
        .named "in-flight disjointness on reachable states",
        .named "shared fresh allocation"]
      grounds := [.receipt "P5a landing receipt", .ruling "R-W14",
        .declarations [`Whatwg.Streams.Writable.QueueInv],
        .theorems [`Whatwg.Streams.Writable.tick_queueInv,
          `Whatwg.Streams.Writable.decide_queueInv,
          `Whatwg.Streams.Writable.step_queueInv,
          `Whatwg.Streams.Writable.reaches_queueInv,
          `Whatwg.Streams.Writable.initial_queueInv]]
      note := "Setup/start and writer acquire/release/reacquire are later full-P5 work. `QueueInv` holds at `initial`, and `tick`, `decide`, every step and every run from a state where it holds reach a state where it holds; R-W14 adds it to this edge as a ground and changes no status." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "the global call-stack and job order",
        .named "ECMAScript promises and reaction registration",
        .named "the full-stream and host embeddings", .named "the DB-04 M1/M2 relations"]
      grounds := [.receipt "P5a landing receipt", .ruling "R-W14",
        .theorems [`Whatwg.Streams.Writable.step_iff_stage,
          `Whatwg.Streams.Writable.reaches_iff_path]]
      note := "The bridges `step_iff_stage` and `reaches_iff_path` onto `Kernel.Path` are grounds of this edge by R-W14, which changes no status." }
    laws := {
      status := .requiredClosed
      grounds := [.theorems [`Whatwg.Streams.Writable.hasInFlight_exact,
          `Whatwg.Streams.Writable.lifecycle_write_close,
          `Whatwg.Streams.Writable.lifecycle_abort_rejection],
        .modules [`Whatwg.Streams.Writable.Laws, `Whatwg.Streams.Writable.Lifecycle],
        .receipts `WhatwgTest.Streams.Writable.DefaultAxiomReport 108,
        .receipts `WhatwgTest.Streams.Writable.InFlightExactAxiomReport 1,
        .receipts `WhatwgTest.Streams.Writable.LifecycleAxiomReport 2,
        .receipt "P5a landing receipt"]
      note := "The 109 local law signatures (the 108 frozen stage/view laws and `hasInFlight_exact`) and the two composed lifecycle statements are proved; the 111 named receipts print." }
    representation := {
      status := .requiredOpen
      remaining := [.named "the global call-stack and job order",
        .named "ECMAScript promises and reaction registration",
        .named "the full-stream and host embeddings", .named "the DB-04 M1/M2 relations"]
      grounds := [.receipt "P5a landing receipt",
        .declarations [`Whatwg.Streams.Writable.UnitPromise, `Whatwg.Streams.Writable.SinkAnswer,
          `Whatwg.Streams.Writable.SinkReturn, `Whatwg.Streams.Writable.State],
        .modules [`Whatwg.Ecma262.Promise]]
      note := "`UnitPromise`, `SinkAnswer`, `SinkReturn` and the promise slots of `State` are views of `Whatwg.Ecma262.Promise`, as the declaration table records." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-WRITE-CE", 1, 17⟩ .closed, .receipt "P5a landing receipt"]
      note := "The rows are closed for this local projection, each through its linked production law." }
    bridges := {
      status := .requiredOpen
      remaining := [.named "the full writer embedding", .named "the global scheduler embedding",
        .named "the shared supply embedding", .named "the host-profile embedding",
        .named "the DB-04 M1/M2 relations"]
      grounds := [.receipt "P5a landing receipt"]
      note := "P5a asserts no host relation." }
    targets := {
      status := .notApplicable
      note := "This packet has no lowering; P11 owns target obligations." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Writable.DefaultAxiomReport 108,
        .receipts `WhatwgTest.Streams.Writable.InFlightExactAxiomReport 1,
        .receipts `WhatwgTest.Streams.Writable.LifecycleAxiomReport 2,
        .gate .build, .receipt "P5a landing receipt", .ruling "R-V1", .ruling "R-V6",
        .ruling "R-V8"]
      note := "The 111 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent source review passed. The axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the full clause map and the test-side numerator witnesses"]
      grounds := [.receipt "P5a landing receipt"]
      note := "The packet claims no changed coverage state." } }

end WhatwgTest.Ledger
