import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `URL-PG-PERCENT`

The ten edges of `docs/URL-PERCENT-ENCODING-DAG.md`
(`test/contracts/graph-ledger.contract.md`, slice B; ruling R-W6), encoded from
that document's "Current state" table. Every status is the table's. Each
sentence of a cell is a ground, an open item, a recorded debt or note text;
notes hold current grounds only, and the graph's history stays in
`docs/receipts/URL-PG-PERCENT.md` and the rulings.

The table's "U3 landing" is the receipts-log section "Landing" of the U3
builder seat, which ruling R-U2 accepted; the closed cells cite both. The two
rulings that name this graph, R-U1 and R-U5, are cited by the representation
cell, and R-U5 also by the bridges cell. Debt D44, what R-U5 records the
`encoding` closure does not cover, is recorded against the representation and
bridges edges; the table names it beside a remaining ground there, not as one.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The URL percent-encoding graph of slice U3. -/
def urlPercent : Graph where
  id := "URL-PG-PERCENT"
  document := "docs/URL-PERCENT-ENCODING-DAG.md"
  fence := [`Whatwg.Url.Boundary, `Whatwg.Url.PercentEncoding]
  dependsOn := ["INFRA-PG-UTF8"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the per-declaration ownership record and the generated declaration snapshot join, which URL has never had and which has no generator",
        .debt "D47"]
      grounds := [.theorems [`Whatwg.Url.PercentEncoding.setOf_eq,
        `Whatwg.Url.PercentEncoding.setOf_injective]] }
    construction := {
      status := .requiredClosed
      grounds := [
        .theorems [`Whatwg.Url.PercentEncoding.c0Control_mem_iff,
          `Whatwg.Url.PercentEncoding.fragment_mem_iff, `Whatwg.Url.PercentEncoding.query_mem_iff,
          `Whatwg.Url.PercentEncoding.specialQuery_mem_iff, `Whatwg.Url.PercentEncoding.path_mem_iff,
          `Whatwg.Url.PercentEncoding.userinfo_mem_iff,
          `Whatwg.Url.PercentEncoding.component_mem_iff, `Whatwg.Url.PercentEncoding.form_mem_iff],
        .declarations [`Whatwg.Url.PercentEncoding.isHexByte, `Whatwg.Url.PercentEncoding.hexValue,
          `Whatwg.Url.PercentEncoding.upperHexDigit, `Whatwg.Url.PercentEncoding.decimalDigits,
          `Whatwg.Url.PercentEncoding.encodingAssertion, `Whatwg.Url.PercentEncoding.spaceAsPlus,
          `Whatwg.Url.PercentEncoding.isomorph],
        .receipt "Landing", .ruling "R-U2"]
      debts := ["D26"]
      note := "The eight sets are `extend`ed from the parent the census records, each membership sentence a theorem, with the four helpers and their laws and steps 1, 2 and 7.3.2. Debt D26, recorded by R-U2's review: `decimalDigits` has no base-ten denotation law, so this closure over AFTER rests on the probe value 8253." }
    semantics := {
      status := .requiredClosed
      grounds := [
        .theorems [`Whatwg.Url.PercentEncoding.percentDecodeBytes_nil,
          `Whatwg.Url.PercentEncoding.percentDecodeBytes_other,
          `Whatwg.Url.PercentEncoding.percentDecodeBytes_pair,
          `Whatwg.Url.PercentEncoding.percentDecodeBytes_malformed_pair,
          `Whatwg.Url.PercentEncoding.percentDecodeBytes_short,
          `Whatwg.Url.PercentEncoding.percentDecodeString_eq,
          `Whatwg.Url.PercentEncoding.followsUtf8Advice_iff,
          `Whatwg.Url.Boundary.EncoderTape.terminated_iff,
          `Whatwg.Url.PercentEncoding.encodeLoop_nil,
          `Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_eq],
        .receipt "Landing", .ruling "R-U2"]
      debts := ["D30", "D31"]
      note := "Percent-decode is transcribed branch by branch, the encoder answer tape is DB-02 data, and the loop and assembly laws end in `percentEncodeAfterEncoding_eq`. Debts D30 and D31 are recorded against `encodeLoop` and step 1's assertion." }
    laws := {
      status := .requiredClosed
      grounds := [.ascriptions `WhatwgTest.Url.PercentEncodingLaws 95, .receipt "Landing",
        .ruling "R-U2"]
      debts := ["D26", "D28", "D29"]
      note := "All 95 ascriptions of the laws battery are proved; thirteen are finite probes and close no clause on their own." }
    representation := {
      status := .requiredOpen
      remaining := [.named "the declaration records", .debt "D47"]
      grounds := [.ruling "R-U1", .ruling "R-U4", .ruling "R-U5"]
      debts := ["D44"]
      note := "The Encoding owner the landing waited on is ruled and landed (R-U1, R-U4); R-U5 records what that closure does not cover: no declaration constructs `Boundary.Utf8Encoding` from Infra's encoder (debt D44)." }
    counterexamples := {
      status := .requiredOpen
      remaining := [.rows ⟨"URL-PE-CE", 6, 6⟩ .seeded, .debt "D27"]
      grounds := [.rows ⟨"URL-PE-CE", 1, 5⟩ .closed, .rows ⟨"URL-PE-CE", 7, 14⟩ .closed,
        .ruling "R-U2"]
      debts := ["D50"]
      note := "`URL-PE-CE-006`'s first mutation, a fresh ISO-2022-JP encoder per code point, is unrepresentable while the encoder is a tape, and `Boundary.isStateful_iso2022jp` falsifies nothing. The witness module `WhatwgTest/Url/Counterexamples/PercentEncoding.lean` imports no production module." }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "(a) the ECMA-262 half of `encodeURIComponent`, which needs `ext.ecma262.encodeuricomponent`, outside the promise lane's census scope"]
      grounds := [.theorems [`Whatwg.Url.PercentEncoding.component_complement],
        .ruling "R-U4", .ruling "R-U5"]
      debts := ["D44"]
      note := "(a) The URL half of `encodeURIComponent` is `component_complement`. (b) The Encoding Standard's `encoding` obligation is closed (see \"The encoding obligation\" in the graph document), and debt D44 remains. WPT `url/` replay and any host profile are U9 work and are not claimed." }
    targets := {
      status := .notApplicable
      note := "U3 lowers nothing and introduces no generated-code relation; P11 owns the lowering machinery." }
    trust := {
      status := .requiredClosed
      grounds := [.receipts `WhatwgTest.Url.PercentEncodingLaws 95, .gate .build,
        .receipt "Landing", .ruling "R-U2"]
      note := "The 95 named receipts are frozen inside the R-11 ceiling and none reaches `Classical.choice`; the root audit reaches both modules and `known-red.txt` holds no U3 entry. No declaration under `Whatwg.Url` reaches `Classical.choice` at `325d5d5`, by the census script of appendix B of `docs/research/2026-09-30-implementation-review.md`." }
    coverage := {
      status := .requiredOpen
      remaining := [.named "an admitted URL denominator, numerator and report"]
      note := "`docs/SPEC-COVERAGE.md` and `docs/URL-CENSUS-DAG.md` own the rest of the join." } }

end WhatwgTest.Ledger
