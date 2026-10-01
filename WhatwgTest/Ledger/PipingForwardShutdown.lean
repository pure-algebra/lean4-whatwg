import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `PIPING-PG-FORWARD-SHUTDOWN`

The ten edges of `docs/PIPING-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history, among it the lane V repair of the three receipts that reached
`Classical.choice`, stays in `docs/receipts/PIPING-PG-FORWARD-SHUTDOWN.md` and
the rulings.

The trust cell cites R-V8, which names this graph by its short name ("the
PIPING graph") and records its trust row. Ruling R-W14 adds the two bridges
onto `Kernel.Path` to the semantics edge, changes no status, and says the
ledger records them at seeding; that cell cites it. No ruling of
`COORDINATION.md` names this graph by identifier or document path, so the
entry acknowledges none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The forward-error piping graph of phase P7a. -/
def pipingForwardShutdown : Graph where
  id := "PIPING-PG-FORWARD-SHUTDOWN"
  document := "docs/PIPING-DAG.md"
  fence := [`Whatwg.Streams.Piping.Requirements, `Whatwg.Streams.Piping.PipeTo,
    `Whatwg.Streams.Piping.Step, `Whatwg.Streams.Piping.Laws, `Whatwg.Streams.Piping.Runs]
  dependsOn := ["READABLE-PG-DEFAULT", "WRITABLE-PG-DEFAULT"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the unique ownership joins of the generated declaration snapshot, which has no generator",
        .debt "D47"]
      grounds := [.receipt "P7a landing receipt"] }
    construction := {
      status := .requiredOpen
      remaining := [.named "arbitrary-start construction: arbitrary prior checkpoints",
        .named "arbitrary-start construction: full canonical source reachability",
        .named "arbitrary-start construction: global freshness"]
      grounds := [.receipt "P7a landing receipt"]
      note := "Admitted read inventory, returned-reference retention and reachable candidate phase invariants are proved." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "global semantics and scheduling",
        .named "the rows of \"Full P7 residual map\" of the graph document, among them backward error and close, forward close, the whole read pump, canonical cancellation and releases, signal actions and pipe-promise settlement"]
      grounds := [.receipt "P7a landing receipt", .ruling "R-W14",
        .theorems [`Whatwg.Streams.Piping.step_iff_stage, `Whatwg.Streams.Piping.reaches_iff_path]]
      note := "The bridges `step_iff_stage` and `reaches_iff_path` onto `Kernel.Path` are grounds of this edge by R-W14, which changes no status." }
    laws := {
      status := .requiredClosed
      grounds := [.modules [`Whatwg.Streams.Piping.Laws, `Whatwg.Streams.Piping.Runs],
        .theorems [`Whatwg.Streams.Piping.lifecycle_two_writes_abort_rejection,
          `Whatwg.Streams.Piping.lifecycle_write_rejection_retains_source],
        .receipts `WhatwgTest.Streams.Piping.ShutdownAxiomReport 46,
        .receipt "P7a landing receipt"]
      note := "The 44 frozen stage and requirements laws and the two composed runs are proved; the 46 named receipts print." }
    representation := {
      status := .requiredOpen
      remaining := [.named "full component and host representations"]
      grounds := [.receipt "P7a landing receipt"] }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-PIPE-CE", 1, 16⟩ .closed, .receipt "P7a landing receipt"]
      note := "The rows are closed with their named production repair laws, for the local scope the register records." }
    bridges := {
      status := .requiredOpen
      remaining := [.named "the full lock, release, cancel, pipe-promise, M1 and global-scheduler bridge"]
      grounds := [.theorems [`Whatwg.Streams.Piping.forwardShutdown_realizes],
        .declarations [`Whatwg.Streams.Piping.ForwardShutdownSpec,
          `Whatwg.Streams.Piping.observeShutdown],
        .receipt "P7a landing receipt"]
      note := "`forwardShutdown_realizes` proves `ForwardShutdownSpec` under `observeShutdown` for every admitted finite candidate run; neither the finite safety theorem nor the two fixed shapes establish progress or eventual shutdown." }
    targets := {
      status := .notApplicable
      note := "No target generation; P11 owns lowering." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Piping.ShutdownAxiomReport 46, .gate .build,
        .receipt "P7a landing receipt", .ruling "R-V1", .ruling "R-V6", .ruling "R-V8"]
      note := "The 46 named receipts print inside the R-11 ceiling; the exhaustive root audit, the builds, the gates and independent source, proof and landing review passed. The axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the coverage join for the full residual clause map and its numerator witnesses"]
      grounds := [.receipt "P7a landing receipt"] } }

end WhatwgTest.Ledger
