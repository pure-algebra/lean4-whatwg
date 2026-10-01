import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `DATA-PG-QUEUE`

The ten edges of `docs/DATA-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice A; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history stays in `docs/receipts/DATA-PG-QUEUE.md`.

References are single-backtick names, so this module imports no production
module: `lake exe whatwg_ledger` resolves every name, count, heading, ruling,
register row and debt against the built environment and the authored files.
No ruling of `COORDINATION.md` names this graph by identifier or document
path, so the entry acknowledges none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The queue-with-sizes and queuing-strategy graph of phase P3. -/
def dataQueue : Graph where
  id := "DATA-PG-QUEUE"
  document := "docs/DATA-DAG.md"
  fence := [`Whatwg.Streams.Data.Queue, `Whatwg.Streams.Data.Strategy,
    `Whatwg.Streams.Data.DyadicSize]
  edges := {
    identity := {
      status := .requiredClosed
      grounds := [.receipt "5. The ten edges",
        .declarations [`Whatwg.Streams.Data.DyadicSize], .receipt "Landing"]
      note := "Every row of section 3 of the graph document names its census row id and that row's span digest from `generated/spec-algorithm-census.tsv`; the twelfth row, `Whatwg.Streams.Data.DyadicSize`, is routed to the representation edge. The graph document states no generated-snapshot ground for the edge and no ruling adds one." }
    construction := {
      status := .requiredClosed
      grounds := [
        .receipts `WhatwgTest.Streams.Data.QueueAxiomReport 99,
        .modules [`Whatwg.Streams.Data.Queue, `Whatwg.Streams.Data.Strategy,
          `Whatwg.Streams.Data.DyadicSize],
        .ruling "P3-R1",
        .theorems [`Whatwg.Streams.Data.DyadicSize.classified,
          `Whatwg.Streams.Data.DyadicSize.ordered,
          `Whatwg.Streams.Data.DyadicSize.exact,
          `Whatwg.Streams.Data.DyadicSize.admissible_iff],
        .receipt "Landing"]
      note := "The 99 frozen theorems are proved with no battery edit; the D0 to D8 declarations are in the queue and strategy modules, and the `P3-R1` instance is `DyadicSize`." }
    semantics := {
      status := .requiredClosed
      grounds := [
        .theorems [`Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible,
          `Whatwg.Streams.Data.dequeueValue_cons,
          `Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue,
          `Whatwg.Streams.Data.resetQueue_eq,
          `Whatwg.Streams.Data.extractHighWaterMark_error_iff,
          `Whatwg.Streams.Data.extractSizeAlgorithm_present],
        .receipt "Landing"]
      note := "The six apex statements are among the 99 proved theorems." }
    laws := {
      status := .requiredClosed
      grounds := [
        .ruling "P3-R1",
        .theorems [`Whatwg.Streams.Data.enqueueValueWithSize_wf,
          `Whatwg.Streams.Data.sizeSum_cons,
          `Whatwg.Streams.Data.dequeueValue_wf,
          `Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact],
        .receipt "Landing"]
      note := "`P3-R1` chose option (i), the exact carrier, so the edge closes on the four laws named, all proved." }
    representation := {
      status := .requiredClosed
      grounds := [.modules [`Whatwg.Streams.Data.DyadicSize], .receipt "Landing"]
      note := "The four frozen representation decisions of the freeze, each forced by a counterexample row, and the `DyadicSize` carrier row." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"WS-DATA-CE", 1, 10⟩ .closed]
      debts := ["D50"]
      note := "The witness module `WhatwgTest/Streams/Counterexamples/Data/Queue.lean` imports no production module, so the link from each attack to the rejecting statement is stated in the register rather than checked in Lean." }
    bridges := {
      status := .notApplicable
      note := "The packet claims no relation to a host implementation. `DATA-FB-ROUNDING` is where a bridge would live, and it is refused at this stratum." }
    targets := {
      status := .notApplicable
      note := "No generated code. Lowering is `RS-5` of `docs/REIFICATION-STRATEGY.md` and P11." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Streams.Data.QueueAxiomReport 99, .gate .build,
        .receipt "Landing"]
      note := "The 99 named receipts print inside the R-11 ceiling, and the declared red set of `test/fixtures/trust-gate/known-red.txt` is empty. No declaration in `Whatwg.Streams.Data` reaches `Classical.choice` at `325d5d5`, by the census script of appendix B of `docs/research/2026-09-30-implementation-review.md`." }
    coverage := {
      status := .requiredClosed
      grounds := [.modules [`WhatwgTest.Audit.SpecCoverage], .gate (.censusReport "streams"),
        .receipt "Coverage landed"]
      note := "The section 6 rows of the graph document are in the numerator, and the coverage report prints the Streams block." } }

end WhatwgTest.Ledger
