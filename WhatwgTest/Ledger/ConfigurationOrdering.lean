import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `CONFIGURATION-PG-ORDERING`

The ten edges of `docs/CONFIGURATION-DAG.md`
(`test/contracts/graph-ledger.contract.md`, slice A; ruling R-W6), encoded
from that document's "Current state" table. Every status is the table's. Each
sentence of a cell is a ground, an open item, a recorded debt or note text;
notes hold current grounds only, and the graph's history, among it the lane V
repair of the nine receipts that reached `Classical.choice` and the close of
debt D43, stays in `docs/receipts/CONFIGURATION-PG-ORDERING.md` and the
rulings.

The trust cell's self-test is the `whatwg_trustselftest` executable: the
table still spells the name ruling R-V3(c) removed (debt D60), and the typed
`Gate` cannot. Ruling R-V8, the one ruling of `COORDINATION.md` that names
this graph by identifier, is cited by the representation and trust cells.
Ruling R-W14 adds grounds to the construction and semantics cells, with no
status change: registration-identity freshness and the kernel bridges. The
graph depends on `WRITABLE-PG-DEFAULT`, whose machine its configuration
lifts (`Whatwg.Streams.Semantics.Configuration` imports
`Whatwg.Streams.Writable.Laws`), and on `PROMISE-PG-FIRST`.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The configuration ordering graph (P8a, slice Q4). -/
def configurationOrdering : Graph where
  id := "CONFIGURATION-PG-ORDERING"
  document := "docs/CONFIGURATION-DAG.md"
  fence := [`Whatwg.Streams.Semantics.Configuration, `Whatwg.Streams.Semantics.Step,
    `Whatwg.Streams.Semantics.Runs, `Whatwg.Streams.Semantics.Source,
    `Whatwg.Streams.Semantics.Frontier, `Whatwg.Streams.Semantics.Mask,
    `Whatwg.Streams.Semantics.Invariants]
  dependsOn := ["PROMISE-PG-FIRST", "WRITABLE-PG-DEFAULT"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [.named "the generated declaration join, which has no generator",
        .debt "D47"]
      grounds := [
        .declarations [`Whatwg.Streams.Semantics.Ordering.phaseErase,
          `Whatwg.Streams.Semantics.Ordering.reactionErase],
        .receipt "Q4 landing, second pass"]
      note := "All 15 class [R] ascriptions elaborate since amendment A1; `phaseErase`, `reactionErase` and the 86 `Source` names are added." }
    construction := {
      status := .requiredOpen
      remaining := [.named "CFG-START", .named "CFG-CELLS", .named "CFG-TOKENS",
        .named "CFG-STACK", .named "inductive reachable-state preservation", .debt "D38",
        .wanted `Whatwg.Streams.Semantics.Ordering.CellsWellFormed]
      grounds := [.ruling "R-W14",
        .declarations [`Whatwg.Streams.Semantics.Ordering.RegistrationsFresh],
        .theorems [`Whatwg.Streams.Semantics.Ordering.step_registrationsFresh,
          `Whatwg.Streams.Semantics.Ordering.reaches_registrationsFresh,
          `Whatwg.Streams.Semantics.Ordering.initial_registrationsFresh,
          `Whatwg.Streams.Semantics.Ordering.reachable_registrations_nodup]]
      note := "Debt D38: the owner clause of `CellsWellFormed` holds by representation, as the `notifySettled` docstring says since R-W14; its other clauses are not yet stated (CFG-CELLS). `RegistrationsFresh` holds at `initial` and is kept by every step, which discharges the `Nodup` premise of the two `notifySettled` bridges at every configuration reachable from `initial`; R-W14 adds it to this edge as a ground and changes no status." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "CFG-EFFECTS",
        .named "CFG-FIFO (its PROCESS/ADVANCE corollary is still owed)", .named "CFG-RUNS",
        .named "the foreign profile", .named "the global scheduler", .named "the live frontiers"]
      grounds := [.receipt "Q4 landing, second pass", .ruling "R-W14",
        .theorems [`Whatwg.Streams.Semantics.Ordering.step_iff_stage,
          `Whatwg.Streams.Semantics.Ordering.reaches_iff_path,
          `Whatwg.Streams.Semantics.Ordering.episodePrefix_iff_path,
          `Whatwg.Streams.Semantics.Ordering.exclusive]]
      note := "The configuration's step and its two closures are bridged to `Whatwg.Streams.Kernel`, and its `tick` and `decide` are exclusive; R-W14 adds the bridges to this edge as grounds and changes no status." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "`WellFormed` initialization and preservation",
        .named "the successful-profile progress theorem",
        .named "the ordered-effect receipts",
        .named "the token/mailbox correspondence",
        .named "the finite witness through the original start gate"]
      grounds := [.receipts `WhatwgTest.Streams.Semantics.OrderingAxiomReport 93,
        .receipt "Q4 landing, second pass"]
      note := "All 54 restated law ascriptions, the 15 Q4-owned bridging receipts and the 18 deferred-generalization ascriptions are proved. The edge stays open on the obligations §3.3 of the contract lists and no landed law states." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "a stable typed address for the P4 read and closed cells, since `E-24` keeps `Readable.State.closedPromise` by value (\"Required residual embeddings\" of the graph document)",
        .named "the freeze-time item \"typed references\"",
        .named "the freeze-time item \"no closures\""]
      grounds := [.ruling "R-V8", .receipt "Q4 landing, second pass"]
      note := "Ruled open by R-V8: the second pass keeps the edge open and names no remaining item, so this cell names the remaining items. The landing records report one cell owner, one payload owner, no shadow scheduler, no second table, and the four view record rows of contract §4.1 with their twenty ascriptions; they say nothing of the freeze-time items \"typed references\" and \"no closures\"." }
    counterexamples := {
      status := .requiredOpen
      remaining := [.named "the actual configuration witness",
        .named "the stable registered scheduler mutants",
        .named "the retained failing alternatives",
        .named "the `WS-CONFIG` register rows of the three certificate mutants `mutantSelectedD0`, `mutantAliasedResults` and `mutantFlushOnW0`",
        .debt "D39"]
      grounds := [.rows ⟨"WS-PROM-CE", 39, 39⟩ .closed, .ruling "R-P27"] }
    bridges := {
      status := .requiredOpen
      remaining := [
        .wanted `Whatwg.Streams.Semantics.Ordering.run_erases_to_reference,
        .named "the transcription gate to the sealed WPT bytes", .debt "D35",
        .named "the host replay", .named "CFG-LOCAL", .named "CFG-OBS",
        .named "CFG-HOST", .named "the full P4/P5/P6/P7 embeddings"]
      debts := ["D34", "D36", "D37"]
      note := "The P8 half of CFG-WPT is the existence half `run_erases_to_reference`, the transcription gate and the host replay. Debts D34, D36 and D37 are recorded against the CFG-WPT seam." }
    targets := {
      status := .notApplicable
      note := "This graph generates no target program; P11 owns target lowering." }
    trust := {
      status := .requiredClosed
      grounds := [.ruling "R-P27", .receipts `WhatwgTest.Streams.Semantics.OrderingAxiomReport 93,
        .gate .trustselftest, .receipt "Q4 landing, second pass", .ruling "R-V1", .ruling "R-V6",
        .ruling "R-V8", .gate .build]
      note := "The graph document held the edge open on independent review alone; ruling R-P27 records that review of `1d400b4` as done, so the edge closes on R-P27. The 93 named receipts print inside the R-11 ceiling and the trust self-test passes against an empty declared red set. The axiom gate holds `Whatwg.Streams` to `propext` and `Quot.sound` with no exception." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the exact clause and numerator joins"]
      grounds := [.receipt "Q4 landing, second pass"]
      note := "The R-P5 re-disposition of `slot.promise-state` and `slot.promise-is-handled` to `owned` moved no coverage state." } }

end WhatwgTest.Ledger
