import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `INFRA-PG-SCALAR`

The ten edges of the graph `INFRA-PG-SCALAR` of
`docs/INFRA-SCALAR-ASSURANCE.md` (`test/contracts/graph-ledger.contract.md`,
slice B; ruling R-W6), encoded from that document's "Current state" table.
Every status is the table's. Each sentence of a cell is a ground, an open
item, a recorded debt or note text; notes hold current grounds only, and the
record's history, among it the red run at `9cf3216`, stays in
`docs/receipts/INFRA-PG-SCALAR.md`.

Five closed cells of the table (semantics, laws, representation, bridges and
trust) cite no ruling, receipts-log heading or register rows. Each is attested
here by the receipts-log section "Proof repair and receipts", which the table's
construction cell cites and which ends by closing the local constructive proof
obligations of the record's edge table. No ruling of `COORDINATION.md` names
this graph, and none is cited.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The constructive scalar/`Char` repair graph of the Infra lane. -/
def infraScalar : Graph where
  id := "INFRA-PG-SCALAR"
  document := "docs/INFRA-SCALAR-ASSURANCE.md"
  fence := [`Whatwg.Infra.Text.Scalar]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the joins of the frozen source, carrier and adapter roles to the Infra census rows and to the generated declaration snapshot, which has no generator",
        .debt "D47"]
      grounds := [.gate (.census "infra")]
      note := "The Infra definition census exists and has no numerator." }
    construction := {
      status := .requiredClosed
      grounds := [.ascriptions `WhatwgTest.Infra.ScalarConstructiveContract 9,
        .receipt "Proof repair and receipts"]
      note := "The nine frozen ascriptions pass; checked constructors and all conversion definition bodies are unchanged." }
    semantics := {
      status := .requiredClosed
      grounds := [.receipt "Proof repair and receipts"]
      note := "Independent review matched the two source spans to the canonical range and surrogate definitions and `Char.valid`, including all surrogate boundaries and U+10FFFF." }
    laws := {
      status := .requiredClosed
      grounds := [.theorems [`Whatwg.Infra.ScalarValue.ofChar_toChar,
          `Whatwg.Infra.ScalarValue.toChar_ofChar],
        .receipt "Proof repair and receipts"]
      note := "The general validity helpers and both exact inverse theorems elaborate unchanged with constructive receipts." }
    representation := {
      status := .requiredClosed
      grounds := [.receipt "Proof repair and receipts"]
      note := "Independent diff review confirmed that only two helper proof bodies changed; canonical types and runtime conversions are unchanged." }
    counterexamples := {
      status := .requiredClosed
      grounds := [.rows ⟨"INFRA-SCALAR-CE", 1, 1⟩ .closed,
        .modules [`WhatwgTest.Infra.ScalarConstructiveContract]]
      note := "All nine frozen checks pass in the common test root." }
    bridges := {
      status := .requiredClosed
      grounds := [.theorems [`Whatwg.Infra.ScalarValue.ofChar_toChar,
          `Whatwg.Infra.ScalarValue.toChar_ofChar],
        .receipt "Proof repair and receipts"]
      note := "Both inverse laws hold over the exact checked scalar and native `Char` values with the recorded axioms; this says nothing about the separate string adapters." }
    targets := {
      status := .notApplicable
      note := "No target language, generated code or host implementation is introduced." }
    trust := {
      status := .requiredClosed
      grounds := [.modules [`WhatwgTest.Infra.ScalarConstructiveContract], .gate .build,
        .receipt "Proof repair and receipts",
        .declarations [`Whatwg.Infra.JsString.ofString, `Whatwg.Infra.JsString.ofLiteral]]
      note := "All nine declarations meet `[propext, Quot.sound]`, checked by `Lean.collectAxioms` in the frozen battery at every build. `JsString.ofString` and `JsString.ofLiteral`, the two declarations of `Whatwg/Infra/Text/Scalar.lean` and `String.lean` that reached `Classical.choice` at `325d5d5`, are string adapters outside this repair fence." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "the census joins"]
      note := "No Infra or URL coverage report follows from this proof-term repair." } }

end WhatwgTest.Ledger
