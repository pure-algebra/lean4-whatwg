# URL percent-encoding proof graph (`URL-PG-PERCENT`, U3)

Breaker-authored 2026-09-07 on `url/u3-breaker`. Contract:
`test/contracts/url-percent-encoding.contract.md`. This file owns the
declaration roles, existing-type dispositions, anchor map, and graph edges for
the URL lane's first semantic packet. It owns no coverage count: URL has no
admitted denominator, numerator, or report, and `docs/URL-CENSUS-DAG.md` owns
that gap.

`URL-PG-CENSUS` is a separate graph over source tooling. Nothing here closes an
edge there, and nothing there closes an edge here.

## Authority anchors

Every row below is a byte-span SHA-256 from the sealed URL census at
`whatwg/url` commit `55d6699373ba68a16ec182f34222a74ed8bc3dac`, recomputed by
this seat from `vendor/whatwg-url-55d66993/url.bs`
(`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`) and
agreeing with `generated/url-census.tsv`. Short aliases used in the tables below
expand to this table, not to a second semantic owner.

| Alias | Census row | Span | Span digest |
| --- | --- | --- | --- |
| SET | `type.percent-encode-set` | [18975,19062) | `6b3a671be020062a50e688d80880c2160e70e1cbb6803945a815eb01a6450146` |
| C0 | `op.c0-control-percent-encode-set` | [19062,19252) | `3a77558e2e7c88d0ac517498ef6adb263dd71dac33faa417dd4d32e7abaf1a5c` |
| FRAG | `op.fragment-percent-encode-set` | [19252,19458) | `3a3528a44621be42a50fadab093f846ab73089afc854d004504fc1a1c760ae01` |
| QUERY | `op.query-percent-encode-set` | [19458,19661) | `40a713dbed67f2798a5a7727a6a634b6d99ad056f00c7ec860854833167b8240` |
| SQUERY | `op.special-query-percent-encode-set` | [19816,19965) | `a02d9322f10e1431ee318f32f6c070c07e12195899e05b24a6319948cee4e05a` |
| PATH | `op.path-percent-encode-set` | [19965,20183) | `0ce861ea749f4d87b4fdf6de710212c3df69b49026b5f2f1dc604ba6470b7b06` |
| USER | `op.userinfo-percent-encode-set` | [20183,20454) | `7686bccd526d0ad6a865e9495e681b55098147b32b70fceb600f850f126146e2` |
| COMP | `op.component-percent-encode-set` | [20454,20666) | `7cea81e47e63bfddd7a94d55ce75d9e5a0cf1fdbfaa0b8c13e0d42b4933c9751` |
| FORM | `op.form-percent-encode-set` | [21163,21416) | `c544851fafc9d6063bba2624ff1be2d5465fef275e9c59d15bae5216b341bceb` |
| RQF | `rule.query-fragment-encode-set-difference` | [19661,19816) | `8d376458e9d7756629833b5fa7dc4268a48504a1e4c2b2958f594a219423cf04` |
| RFORM | `rule.form-encode-set-complement` | [21416,21624) | `4f47c51bf3405a137cfb90ddb29093e86041fdadd8af3153abf71baecc46d1a8` |
| RURI | `rule.component-encodeuricomponent-equivalence` | [20666,21163) | `4752ec9d22b43e3314668e458665a06a6e59596a7c317d27443d86335a8557bc` |
| SYNTAX | `op.percent-encoded-byte-syntax` | [16209,16325) | `e932ad60acb037010d31617a2c15a6616c5c937f85d2e4ddb518bdfb0c09742c` |
| ENCB | `op.percent-encode-byte` | [16862,17111) | `d5c3d103b8b806a4fa398339bfab0e20dea4f43afb529e034d2a1da8f46bf9b0` |
| DECB | `op.percent-decode-bytes` | [17113,18462) | `f1e84473e0f9ff75037833c851b4260b0c909f484c1c35d0e0a65686a81db556` |
| DECS | `op.percent-decode-string` | [18464,18967) | `a2de391cbe8a9820a896d3b8cbb6217e192c05549c68c42c539d3d341e6fef52` |
| ADVICE | `requirement.percent-encoded-utf8-advice` | [16325,16862) | `777bc00b17dfcbd672c9f6df93b656ab950b72c8d76ca20f0efeb0976864468c` |
| AFTER | `op.percent-encode-after-encoding` | [21624,24696) | `392c22964c6825b50102ff51e28889d05b8a65346815f8593e3229bef6a23bef` |
| U8CP | `op.utf8-percent-encode-code-point` | [24698,25071) | `c4c360f1de1b9e92e18502acd8152c9edb4763684d763476cf11a630f8995c5b` |
| U8STR | `op.utf8-percent-encode-string` | [25073,25393) | `6e03cdafd70ca4858bfbd33b56834e7cfdaf3c6566576660b81de6a43c33a7c6` |

Twenty aliases, twenty rows: 15 `op`, 3 `rule`, 1 `type`, 1 `requirement`.

The example table at [25459,27305), digest
`4fa270b4ef01f88fe9fd30b223aa39184e6b3f323c03a1978583f0a00b91aec8`, is an
authored explanation with no row. It supplies thirteen finite probes and closes
nothing.

## Declaration and existing-type records

All names are relative to `Whatwg.Url`. The route for every row is
`URL-PG-PERCENT` with the contributing edge named below. No separately allocated
leaf graph is needed. Constructors, projections, derived instances and the
batteries' named theorems inherit their owning row deterministically and must
still appear in the eventual generated declaration snapshot.

| Stable declaration family | Module | Relationship and existing owner | Disposition / anchor | Edge |
| --- | --- | --- | --- | --- |
| `Boundary.EncoderName`, `.isStateful` | `Boundary.lean` | first-order name of an Encoding Standard encoder; no encoder algorithm is modelled | `foreignBoundary`; AFTER | representation |
| `Boundary.EncodeAnswer`, `Boundary.EncoderTape`, `.terminated` | `Boundary.lean` | the answer tape of one `encode or fail` run; DB-02 decision data, never a stored function | `foreignBoundary`; AFTER | semantics |
| `Boundary.Utf8Encoding`, `.tape` | `Boundary.lean` | the Encoding owner's `UTF-8 encode` answer for one scalar value string, paired with its input | `foreignBoundary`; DECS, U8CP, U8STR | representation |
| `Boundary.Utf8DecodeOrFail` | `Boundary.lean` | the Encoding owner's `UTF-8 decode without BOM or fail` answer | `foreignBoundary`; ADVICE | representation |
| `PercentEncoding.PercentEncodeSet`, `.mem`, `.extend` | `PercentEncoding.lean` | decidable predicate over the canonical `Whatwg.Infra.CodePoint`; not a second code-point carrier | `owned`; SET | identity |
| `PercentEncoding.c0Control`, `.fragment`, `.query`, `.specialQuery`, `.path`, `.userinfo`, `.component`, `.form` | `PercentEncoding.lean` | the eight named sets, each `extend`ed from the parent the census records | `owned`; C0, FRAG, QUERY, SQUERY, PATH, USER, COMP, FORM | laws |
| `PercentEncoding.SetName`, `.setOf` | `PercentEncoding.lean` | the finite index the algorithm's own identity tests compare on; pinned by `setOf_eq`, separated by `setOf_injective` | `owned`; AFTER | identity |
| `PercentEncoding.isHexByte`, `.hexValue`, `.upperHexDigit`, `.decimalDigits` | `PercentEncoding.lean` | the hex reader, the upper-hex writer, and the base-ten writer the three algorithms name; no Infra owner exists for them | `owned`; DECB, ENCB, AFTER | construction |
| `PercentEncoding.isPercentEncodedByte` | `PercentEncoding.lean` | grammar predicate over `Whatwg.Infra.JsString`, either hex case | `owned`; SYNTAX | laws |
| `PercentEncoding.percentEncodeByte` | `PercentEncoding.lean` | the byte serializer, exact uppercase output | `owned`; ENCB | laws |
| `PercentEncoding.percentDecodeBytes` | `PercentEncoding.lean` | total decoder on `Whatwg.Infra.ByteSequence` with the two malformed branches | `owned`; DECB | laws |
| `PercentEncoding.percentDecodeString` | `PercentEncoding.lean` | the scalar-value-string decoder, over the boundary's UTF-8 answer | `owned` loop, `foreignBoundary` encoding; DECS | semantics |
| `PercentEncoding.followsUtf8Advice` | `PercentEncoding.lean` | the advice as a predicate over the boundary's decode answer; the URL half is which bytes are handed over | `requirement`; ADVICE | semantics |
| `PercentEncoding.encodingAssertion`, `.spaceAsPlus`, `.isomorph` | `PercentEncoding.lean` | steps 1, 2 and 7.3.2 | `owned`; AFTER | construction |
| `PercentEncoding.renderByte`, `.errorReference`, `.renderAnswer`, `.encodeLoop` | `PercentEncoding.lean` | steps 7.3, 7.4 and the while loop, over the answer tape | `owned`; AFTER | semantics |
| `PercentEncoding.percentEncodeAfterEncoding` | `PercentEncoding.lean` | the assembled algorithm relative to an encoder answer | `owned` loop, `foreignBoundary` encoder; AFTER | semantics |
| `PercentEncoding.utf8PercentEncodeString`, `.utf8PercentEncodeCodePoint` | `PercentEncoding.lean` | the two total UTF-8 specializations over a `Utf8Encoding` | `owned`; U8STR, U8CP | laws |

Do not add fields or declarations to the public frozen surface silently. Private
implementation helpers may be added without changing these signatures. Module
splitting to respect dependency direction is permitted while stable names and
root reachability stay fixed; `Whatwg/Url.lean` already imports both files.

## Ten edges

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

## Clause map and residual obligations

| Anchors | U3 obligations | Residual obligation before whole-row green |
| --- | --- | --- |
| SET, C0, FRAG, QUERY, SQUERY, PATH, USER, COMP, FORM | exact membership per set; seven strict inclusions; the two inclusive ranges read as ranges; every set contains every code point above U+007E | none inside U3; the consumers in U4, U5, U7 and U8 must cite these sets rather than restate them |
| RQF | both incomparability directions, U+0060 and U+0023 | none |
| RFORM | the complement is ASCII alphanumeric together with `*`, `-`, `.`, `_` | none |
| RURI | the component complement is ASCII alphanumeric together with the nine `uriMark` code points | the ECMA-262 half of the equivalence; `bridges` |
| SYNTAX, ENCB | the three-code-unit grammar in either case; the exact uppercase output; injectivity; the composition of the two rows | the U5 callers `op.url-units`, `rule.url-non-ascii-percent-encoding`, `rule.url-percent-encoded-units` and the U4 caller `rule.validation-domain-percent-encoded` |
| DECB | all four branches of step 2, the size laws, the fixed point, the non-idempotence witness, the byte round trip | the U7 caller `op.urlencoded-parser` and its plus rule |
| DECS, ADVICE | the composition with the boundary's UTF-8 answer; the URL half of the advice | the Encoding owner; the U4 caller `op.host-parser` and the U6 caller `requirement.rendering-constrained-percent-decoding`, both of which the advice names |
| AFTER | steps 1, 2, 5, 6, 7 and 8 over the answer tape; the discharged non-ASCII assertion; the space-before-set order; the shortest decimal reference; the tape-split distribution law; the live-frontier reading of an unanswered tape | `get an encoder`, `encode or fail` and the I/O queue themselves; the U5 caller `op.parser-query`, whose buffering the ISO-2022-JP statefulness explains; the U7 caller `op.urlencoded-serializer` |
| U8CP, U8STR | the collapse to a per-byte rendering with no error reference; the composition law; the two round trips and their two failure witnesses | `UTF-8 encode` itself; the five U5 and U4 callers |

## Landing (builder seat, 2026-09-07, branch `url/u3-builder`)

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

## Evidence ledger

The measured freeze evidence, the intended-red diagnostics, and the immutable
packet commit are in the contract's "Freeze receipt". The measured landing
evidence is in the "U3 landing receipt" of `docs/URL-PACKAGE-PLAN.md` and in the
"Landing" section above. The coordinator owns root and known-red integration and
may append a further landing receipt here; it may not weaken this packet.
