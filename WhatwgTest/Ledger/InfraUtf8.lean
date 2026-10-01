import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `INFRA-PG-UTF8`

The ten edges of `docs/INFRA-UTF8-DAG.md`
(`test/contracts/graph-ledger.contract.md`, slice B; ruling R-W6), encoded from
that document's "Current state" table. Every status is the table's. Each
sentence of a cell is a ground, an open item, a recorded debt or note text;
notes hold current grounds only, and the graph's history, among it the
17 receipts that missed the R-U3 target until lane V (debt D42, closed), stays
in `docs/receipts/INFRA-PG-UTF8.md` and the rulings.

The landing record of this packet is ruling R-U4, cited by the laws,
representation, counterexamples and bridges cells. The three rulings that name
this graph are cited where they act: R-U5 by the bridges cell, R-V6 by the
representation and trust cells, R-V8 by the trust cell. The
`INFRA-UTF8-CE` attack rows live only in the packet's own register
`test/counterexamples/infra/UTF8.md` (debt D45), so the counterexamples cell
names them as an item rather than as register rows the gate could check.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The Infra UTF-8 codec graph over the Encoding Standard pin. -/
def infraUtf8 : Graph where
  id := "INFRA-PG-UTF8"
  document := "docs/INFRA-UTF8-DAG.md"
  fence := [`Whatwg.Infra.Text.Utf8]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the declaration snapshot that joins every public name, which has no generator",
        .debt "D47"]
      grounds := [.ascriptions `WhatwgTest.Infra.Utf8Contract 80]
      note := "The 80 interface ascriptions of the contract battery elaborate." }
    construction := {
      status := .requiredOpen
      remaining := [
        .named "a run-level proof of the decoder's reachable-state invariant (`bytesSeen ≤ bytesNeeded ≤ 3` and `codePoint ≤ 0x10FFFF` at every step of a run started from `initial`)"]
      grounds := [.theorems [`Whatwg.Infra.Utf8.decoderHandler_items_isScalarValue]]
      note := "The invariant is only a hypothesis of `decoderHandler_items_isScalarValue`." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "a theorem relating a run of `processQueue` to a specification of UTF-8 independent of the transcription"]
      note := "R-U4 does not address this ground." }
    laws := {
      status := .requiredClosed
      grounds := [.ascriptions `WhatwgTest.Infra.Utf8Laws 119, .ruling "R-U4"]
      note := "All 119 ascriptions of the laws battery elaborate and are proved." }
    representation := {
      status := .requiredClosed
      grounds := [.theorems [`Whatwg.Infra.IoQueue.convertFrom_convertTo,
          `Whatwg.Infra.Utf8.decodeString_eq, `Whatwg.Infra.Utf8.decodeWithoutBomString_eq,
          `Whatwg.Infra.Utf8.decodeWithoutBomOrFailString_eq, `Whatwg.Infra.Utf8.scalars_val],
        .ascriptions `WhatwgTest.Infra.Utf8Laws 119, .ruling "R-U4", .ruling "R-V6"]
      note := "The three bridges the edge names are among the 119 laws R-U4 lands: `IoQueue.convertFrom_convertTo`, the `JsString.ofCodePoints` faces `decodeString_eq`, `decodeWithoutBomString_eq` and `decodeWithoutBomOrFailString_eq`, and `Utf8.scalars_val`. The `Array`/`ByteArray` realizer of `ByteSequence` is outside this packet by the edge's own statement." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .named "`INFRA-UTF8-CE-001` to `INFRA-UTF8-CE-018`, which stand `SEEDED` in `test/counterexamples/infra/UTF8.md`",
        .debt "D45"]
      grounds := [.modules [`WhatwgTest.Infra.Counterexamples.Utf8], .ruling "R-U4"]
      debts := ["D50"]
      note := "No landing record moves the rows, and they have no row in `test/counterexamples/REGISTER.md`. The witness module `WhatwgTest/Infra/Counterexamples/Utf8.lean` imports no production module. R-U4 records the counterexample battery green." }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "obligation (2), the decode half of ASCIIDEC's agreement note (isomorphic decode and UTF-8 decode agree on ASCII bytes), which is not stated"]
      grounds := [.theorems [`Whatwg.Infra.Utf8.encode_ascii_eq_asciiEncode,
          `Whatwg.Infra.Utf8.u3Profile_encoderTape, `Whatwg.Infra.Utf8.u3Profile_decodeOrFail],
        .ruling "R-U5", .ruling "R-U4", .ruling "R-U3"]
      debts := ["D44"]
      note := "Of the three obligations, (1) is closed by `encode_ascii_eq_asciiEncode`; (3) is ruled by R-U5: R-U4's closure of the URL `encoding` obligation stands on the ground R-U3 gave it, the theorems `u3Profile_encoderTape` and `u3Profile_decodeOrFail`, and what that closure does not cover is debt D44, since no declaration constructs a `Whatwg.Url.Boundary.Utf8Encoding` from this encoder." }
    targets := {
      status := .notApplicable
      note := "This packet has no lowering and no generated code; P11 owns that obligation. The \"Implementation considerations\" section is `evidenceOnly`." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Infra.Utf8AxiomReport 119, .gate .build,
        .ruling "R-V1", .ruling "R-V6", .ruling "R-V8"]
      note := "The axiom gate holds every declaration of `Whatwg.Infra.Text.Utf8` to `propext` and `Quot.sound`, the R-U3 target and the edge's one stated ground, with no exception. Debt D42 is closed." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "an Encoding census that `docs/SPEC-COVERAGE.md` admits"]
      note := "The Encoding Standard has no census, denominator, numerator or report." } }

end WhatwgTest.Ledger
