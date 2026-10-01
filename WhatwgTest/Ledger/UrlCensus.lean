import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `URL-PG-CENSUS`

The ten edges of `docs/URL-CENSUS-DAG.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
graph's history stays in `docs/receipts/URL-PG-CENSUS.md`, with the U2a, U2b
and U2c receipts in `docs/URL-PACKAGE-PLAN.md`.

The graph is over source tooling, so its fence is the three URL tooling
modules under `WhatwgGates`. No edge is closed, and no ruling of
`COORDINATION.md` names this graph or changes one of its edges, so the entry
cites and acknowledges none.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The URL census assurance graph over the U2 source tooling. -/
def urlCensus : Graph where
  id := "URL-PG-CENSUS"
  document := "docs/URL-CENSUS-DAG.md"
  fence := [`WhatwgGates.UrlInventory, `WhatwgGates.UrlCensus, `WhatwgGates.UrlCensusInput]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the canonical declaration and assurance identity joins; the per-declaration assurance snapshot has no generator",
        .debt "D47"]
      grounds := [.gate .urlinventory, .gate .urlcensus]
      note := "`lake exe whatwg_urlinventory` checks the pin and lexical spans, and `lake exe whatwg_urlcensus` checks the six authored inputs, in-span anchors, digests, origin and owner joins and disposition resolution." }
    construction := {
      status := .requiredOpen
      remaining := [.named "the generated declaration and assurance joins", .debt "D47"]
      grounds := [.declarations [`Gates.Census.Row, `Gates.UrlCensus.SourceRow]]
      note := "U2b adapts `Gates.Census.Row` through `SourceRow`, and the two source projections are Lean-generated and drift-checked." }
    semantics := {
      status := .requiredOpen
      remaining := [.named "declaration correspondence", .named "semantic assurance"]
      note := "Independent review accounted for every candidate and reviewed each authored disposition and dependency list." }
    laws := {
      status := .requiredOpen
      remaining := [.named "numerator/denominator agreement"]
      note := "The frozen scanner, join, syntax, priority, anchor and projection probes are finite tooling receipts, not general parser laws." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "canonical-owner relationships to Infra and other standards, which need per-declaration records and checked joins"] }
    counterexamples := {
      status := .requiredOpen
      remaining := [.named "a packet of its own for coverage and declaration-join attacks"]
      grounds := [.rows ⟨"URL-INV-CE", 1, 5⟩ .closed, .rows ⟨"URL-CEN-CE", 1, 1⟩ .closed,
        .rows ⟨"URL-INP-CE", 1, 1⟩ .closed]
      note := "The retained tooling regressions are closed." }
    bridges := {
      status := .notApplicable
      note := "Source census tooling claims no host, third-party or cross-language relation; those bridges belong to the URL semantic families." }
    targets := {
      status := .notApplicable
      note := "The TSV is an inventory projection, not executable URL target code; no TypeScript lowering is introduced." }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the assurance modules of the declaration and assurance join, which do not exist yet and must enter the common module and axiom audit before cutover"]
      grounds := [.modules [`WhatwgGates.UrlInventory, `WhatwgGates.UrlCensus,
        `WhatwgGates.UrlCensusInput, `WhatwgTest.Url.InventoryContract,
        `WhatwgTest.Url.CensusContract, `WhatwgTest.Url.CensusInputContract], .gate .build]
      note := "The scanner, assignment and U2c reader and test declarations are in that audit today, with receipts in `docs/URL-PACKAGE-PLAN.md`." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "an admitted URL coverage denominator and report",
        .named "the declaration/numerator join and its gate, required under `docs/SPEC-COVERAGE.md`"] } }

end WhatwgTest.Ledger
