# Receipts log of `URL-PG-PERCENT`

This log holds the history of `docs/URL-PERCENT-ENCODING-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/URL-PERCENT-ENCODING-DAG.md`.

## Ten edges

Moved verbatim from `docs/URL-PERCENT-ENCODING-DAG.md` at `325d5d5`.

Status values below were set at the freeze and updated at the U3 builder landing
of 2026-09-07; the "Landing" section after this table records the evidence for
every change, edge by edge, with theorem names.

| Edge | Status | Rows it must close | Required evidence / reason |
| --- | --- | --- | --- |
| identity | required-open | SET, AFTER | exact ascriptions and constructor census for the carrier, `SetName` and `setOf`; `setOf_eq` and `setOf_injective`; the per-declaration ownership record and the generated declaration snapshot join, which URL has never had |
| construction | closed 2026-09-07 | C0, FRAG, QUERY, SQUERY, PATH, USER, COMP, FORM, ENCB, DECB, AFTER | the eight sets built by `extend` from the parent the census records; the four helpers; steps 1, 2 and 7.3.2; every definition total, structural, and free of a duplicate Infra carrier |
| semantics | closed 2026-09-07 | DECB, DECS, ADVICE, AFTER | branch-by-branch transcription of percent-decode including both malformed cases; the encoder answer tape as DB-02 decision data with an unanswered tape as a live frontier; `renderAnswer`, `encodeLoop`, and the assembly; the boundary's own semantics stays out |
| laws | closed 2026-09-07 | all twenty | the 95 frozen ascriptions of `WhatwgTest/Url/PercentEncodingLaws.lean`: membership, seven strict inclusions, the three rules, the syntax/encode composition, injectivity, the four round trips on their exact domains, the composition law, and the frozen non-idempotence. Thirteen of the 95 are finite probes and close no clause on their own |
| representation | required-open | SET, DECS, U8CP, U8STR, ADVICE | every carrier reused from `Whatwg.Infra` with no copy: `Byte`, `ByteSequence`, `CodePoint`, `CodeUnit`, `JsString`, `ScalarValue`, `asciiEncode?`. The boundary records are answer shapes, not stored functions. Open until the declaration records exist and until the Encoding owner named below is settled |
| counterexamples | required-open | ENCB, DECB, USER, COMP, FORM, RQF, RURI, C0, AFTER | `URL-PE-CE-001` through `URL-PE-CE-014`. The fifteen finite mutant witnesses are green at the freeze; the edge closes only when each attacked production statement is a proved law that mechanically rejects the mutant, and when the coordinator has registered the rows centrally |
| bridges | required-open | RURI, ADVICE, DECS, U8CP, U8STR, AFTER | two named, unproved bridges. (a) ECMA-262's `encodeURIComponent`: the URL half is `component_complement`; the other half needs `ext.ecma262.encodeuricomponent`, which is outside the promise lane's census scope. (b) The Encoding Standard: `UTF-8 encode`, `UTF-8 decode without BOM or fail`, `get an encoder`, `encode or fail`, the I/O queue. See the encoding obligation below. WPT `url/` replay and any host profile are U9 and are not claimed here |
| targets | not-applicable | — | U3 lowers nothing. RS-5 gives Stratum A two realizers, but the generated TypeScript realizer and the pinned host body are U9 work and P11 owns the lowering machinery. No generated-code relation is introduced, so there is no target obligation to leave open |
| trust | closed 2026-09-07 | all twenty | the 95 named receipts of `WhatwgTest/Url/PercentEncodingAxiomReport.lean` inside the R-11 ceiling, plus the URL lane's choice-minimization objective: any receipt reaching `Classical.choice` is reported with its exact dependency path and a constructive attempt. The exhaustive root audit must reach both new modules, and the three known-red entries must be gone |
| coverage | required-open | all twenty | URL has no admitted denominator, numerator, or report at all. This packet adds none and none is inferred from a green battery. The clause map below is the U3 half of the eventual join; `docs/SPEC-COVERAGE.md` and `docs/URL-CENSUS-DAG.md` own the rest |

At the freeze: nine required-open edges and one not-applicable, with no edge closed. At the U3 builder landing of 2026-09-07: four closed (construction, semantics, laws, trust), five still required-open (identity, representation, counterexamples, bridges, coverage), one not-applicable (targets).

## The encoding obligation

Moved verbatim from `docs/URL-PERCENT-ENCODING-DAG.md` at `325d5d5`; ruling R-U5 supersedes it, and the section there now states R-U5.

The Encoding Standard is pinned (`whatwg/encoding` at `67494fce`, sealed under
`vendor/whatwg-encoding-67494fce/`, ruling R-U1 of 2026-09-07, one commit
after this packet's builder branched), but no UTF-8 core has landed, so five
operations the scoped rows call have no owner yet: `UTF-8 encode`, `UTF-8
decode without BOM or fail`, `get an encoder`, `encode or fail`, and the I/O
queue. Infra defers to Encoding for all of them; the Infra UTF-8 packet
(`INFRA-PG-UTF8`) is their owner and closes this obligation. That packet must
also discharge the two facts `Boundary.Utf8Encoding.tape` assumes by
definition (R-U2): UTF-8's `encode or fail` never fails, and it returns the
whole encoding in a single call, so step 7's loop runs exactly once. The four
round trips, `utf8PercentEncodeString_flatMap`, `_append`,
`_isAsciiString` and `followsUtf8Advice_component` all factor through those
two assumptions.

This packet does not invent an owner. It confines the gap to the `bridges` and
`representation` edges by making the boundary's answer an explicit argument
(`Boundary.Utf8Encoding`, `Boundary.EncoderTape`), so that seventeen of the
twenty rows are fully owned and only DECS, U8CP and U8STR carry an unowned half.

The contract's ratification request asks the operator to rule between pinning
the Encoding Standard now, with its UTF-8 core landing in
`Whatwg.Infra.Text.Codec` beside `isomorphicDecode` and `asciiEncode`, and
deferring to U7 or U9. Until that ruling arrives this obligation stays open and
no `utf8Encode` is declared anywhere. A URL-local UTF-8 codec would be the
convenience carrier `Whatwg/AGENTS.md` forbids and would close no edge.

## Landing (builder seat, 2026-09-07, branch `url/u3-builder`)

Moved verbatim from `docs/URL-PERCENT-ENCODING-DAG.md` at `325d5d5`.

`Whatwg/Url/Boundary.lean` and `Whatwg/Url/PercentEncoding.lean` are
implemented. No token of any ascription in the three batteries changed and no
byte of the four battery files changed; the fifteen finite mutant witnesses of
`WhatwgTest/Url/Counterexamples/PercentEncoding.lean` stayed green throughout.
The measured commands are in the "U3 landing receipt" of
`docs/URL-PACKAGE-PLAN.md`; that receipt is the only plan edit.

### Edges that close, with their evidence

| Edge | Closing evidence |
| --- | --- |
| construction | The eight sets are `extend`ed from exactly the parent the census records — `fragment`/`query` from `c0Control`, `specialQuery`/`path` from `query`, `userinfo` from `path`, `component` from `userinfo`, `form` from `component` — and each membership sentence is a theorem: `c0Control_mem_iff`, `fragment_mem_iff`, `query_mem_iff`, `specialQuery_mem_iff`, `path_mem_iff`, `userinfo_mem_iff`, `component_mem_iff`, `form_mem_iff`. The three inclusive ranges are ranges: the `userinfo`, `component` and `form` laws state them as `0x5B ≤ v ≤ 0x5D`, `0x24 ≤ v ≤ 0x26` and `0x27 ≤ v ≤ 0x29`. The four helpers land with `isHexByte_iff`, `hexValue_digit`, `hexValue_upper`, `hexValue_lower`, `upperHexDigit_isAsciiUpperHexDigit`, `decimalDigits_zero`, `decimalDigits_isAsciiDigits`, `decimalDigits_shortest`; steps 1, 2 and 7.3.2 with `encodingAssertion_iff`, `spaceAsPlus_iff`, `isomorph_val`. Totality is the root axiom gate's: no `partial`, `unsafe`, `sorry`, `native_decide` or `bv_decide` anywhere, `percentDecodeBytes` and `encodeLoop` structurally recursive on their own list argument and `decimalDigitsAux` fuel-bounded by the value it prints. No Infra carrier is redeclared. |
| semantics | Percent-decode is transcribed branch by branch and each branch is a theorem: `percentDecodeBytes_nil` (step 1), `percentDecodeBytes_other` (step 2.1), `percentDecodeBytes_pair` (step 2.3), `percentDecodeBytes_malformed_pair` and `percentDecodeBytes_short` (both readings of step 2.2), with `percentDecodeBytes_length_le`, `percentDecodeBytes_percent_le`, `percentDecodeBytes_id_of_no_percent` and `percentDecodeBytes_not_idempotent` for the note. `percentDecodeString_eq` and `followsUtf8Advice_iff` compose DECS and ADVICE with the boundary's answers and nothing else. The encoder answer is DB-02 first-order data: `Boundary.EncodeAnswer`, `Boundary.EncoderTape`, `Boundary.EncoderTape.terminated_iff`, and `encodeLoop_nil` reads an unanswered tape as a live frontier rather than an error. The loop and assembly are `renderAnswer_none`, `renderAnswer_some`, `encodeLoop_terminal`, `encodeLoop_cons`, `encodeLoop_append`, `percentEncodeAfterEncoding_eq`. No encoder or decoder body is modelled. |
| laws | All 95 ascriptions of `WhatwgTest/Url/PercentEncodingLaws.lean` elaborate and are proved: the eight membership laws, the seven inclusions (`c0Control_subset_fragment`, `c0Control_subset_query`, `query_subset_specialQuery`, `query_subset_path`, `path_subset_userinfo`, `userinfo_subset_component`, `component_subset_form`) each strict (`fragment_strict_c0Control`, `query_strict_c0Control`, `specialQuery_strict_query`, `path_strict_query`, `userinfo_strict_path`, `component_strict_userinfo`, `form_strict_component`), the three rules (`fragment_not_subset_query`, `query_not_subset_fragment`, `form_complement`, `component_complement`), the family identity (`setOf_eq`, `setOf_injective`, `setOf_includes_non_ascii`), the syntax/encode composition (`isPercentEncodedByte_iff`, `percentEncodeByte_eq`, `percentEncodeByte_upper`, `percentEncodeByte_isPercentEncodedByte`, `percentEncodeByte_injective`), the four round trips on their exact domains (`percentDecodeBytes_percentEncodeByte` unrestricted, `roundTrip_component` on every UTF-8 byte sequence, `roundTrip_form` off U+0020 with `roundTrip_form_space_fails` at its boundary, `roundTrip_query_fails`), the composition law (`utf8PercentEncodeString_flatMap`, `utf8PercentEncodeString_append`, `utf8PercentEncodeString_isAsciiString`, `utf8PercentEncodeCodePoint_eq`), and the frozen non-idempotence. Thirteen of the 95 are `_example` finite probes and close no clause on their own. |
| trust | All 95 named receipts of `WhatwgTest/Url/PercentEncodingAxiomReport.lean` print inside the R-11 ceiling, and the URL lane's choice-minimization objective is met exactly: **none reaches `Classical.choice`**. Distribution: 42 with no axioms, 29 `[propext]`, 24 `[propext, Quot.sound]`. The exhaustive root audit reaches both new modules (`lake --wfail build WhatwgTest`, 200 modules and 13584 declarations), and the three `known-red.txt` entries are removed with the packet note kept, which `lake exe trustselftest` confirms as "declared red set matches the observed red set (0 module(s))". |

### Edges that stay open, and why

| Edge | Landed half | Why it stays open |
| --- | --- | --- |
| identity | `setOf_eq` and `setOf_injective` are proved, the latter through eight separating code points; the carrier, `SetName` and `setOf` elaborate at their exact frozen signatures. | The per-declaration ownership record and the generated declaration snapshot join, which URL has never had, still do not exist. Nothing in this packet creates them. |
| representation | Every carrier is Infra's and none is copied: `Byte`, `ByteSequence`, `CodePoint`, `CodeUnit`, `JsString`, `ScalarValue`, `JsString.asciiEncode?`. The four boundary records are answer shapes with no stored function. | The declaration records above, and the Encoding owner, which is unruled. |
| counterexamples | Every attacked production statement is now a proved law. `URL-PE-CE-001` → `upperHexDigit_isAsciiUpperHexDigit`, `percentEncodeByte_upper`; `-002` → `userinfo_mem_iff`; `-003`, `-004` → `percentDecodeBytes_short`; `-005` → `spaceAsPlus_iff`; `-006` → `Boundary.isStateful_iso2022jp`, `percentEncodeAfterEncoding_example_iso2022jp` (and the absence of any per-input-split law for a stateful encoder, against `utf8PercentEncodeString_append` for UTF-8); `-007` → `fragment_not_subset_query`, `query_not_subset_fragment`; `-008` → `isHexByte_iff`, `percentDecodeBytes_example_lowercase`; `-009` → `decimalDigits_shortest`; `-010` → `renderByte_plus`; `-011` → `encodeLoop_terminal`; `-012` → `component_complement`; `-013` → `percentDecodeBytes_malformed_pair`; `-014` → `c0Control_mem_iff`, `setOf_includes_non_ascii`. The fifteen finite witnesses stay green and byte-identical. | Registered centrally at the landing (R-U2): thirteen `CLOSED`, `URL-PE-CE-006` `SEEDED` because its first mutation, a fresh ISO-2022-JP encoder per code point, is unrepresentable while the encoder is a tape and `isStateful` a two-clause function; the review found `Boundary.isStateful_iso2022jp` falsifies nothing (debt D27). The edge stays required-open on that one row |
| bridges | The URL-owned half of the ECMA-262 equivalence is `component_complement`. | Neither bridge is proved. `ext.ecma262.encodeuricomponent` is outside the promise lane's census scope, and the Encoding Standard's five operations have no owner here. See the encoding obligation above. |
| coverage | None; none is claimed. | URL has no admitted denominator, numerator, or report. A green battery is a set of theorems, not a coverage state. |
| targets | — | `not-applicable`, unchanged: U3 lowers nothing. |

The **encoding obligation stays open exactly as stated above**. The three rows
DECS, U8CP and U8STR keep their unowned UTF-8 half; no `utf8Encode` is declared
anywhere, and the packet's `Boundary.Utf8Encoding` remains an answer record.
