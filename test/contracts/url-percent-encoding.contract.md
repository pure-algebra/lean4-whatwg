# URL percent-encoding packet (U3)

Status: FROZEN / RED, independent breaker seat, 2026-09-07, on branch
`url/u3-breaker` from `main` at `7345c96`.
Graph: `URL-PG-PERCENT` (`docs/URL-PERCENT-ENCODING-DAG.md`).
Attacks: `test/counterexamples/url/PERCENT-ENCODING.md`, `URL-PE-CE-001`
through `URL-PE-CE-014`.

This packet freezes the first semantic URL slice: the `percent-encoded-bytes`
section and the eight percent-encode set definitions. It is the U3 row of
`docs/URL-PACKAGE-PLAN.md`. The builder implements
`Whatwg/Url/PercentEncoding.lean` and `Whatwg/Url/Boundary.lean`; it must not
edit this contract, the three red batteries, or the retained finite witnesses.

## Pin

The semantic owner is `vendor/whatwg-url-55d66993/url.bs` at
`whatwg/url` commit `55d6699373ba68a16ec182f34222a74ed8bc3dac`, 162,680 bytes,
SHA-256 `a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`,
independently recomputed by this seat with PowerShell
`Get-FileHash -Algorithm SHA256` and agreeing with the `input-sha256` header of
`generated/url-census.tsv`. `SPEC-MANIFEST.md` owns the pin and its section
dispositions; `docs/PROVENANCE.md` owns the fetch and cross-check.

Every citation below is a census row id of `generated/url-census.tsv` with the
row's `[byte-start,byte-end)` span. No line number is cited anywhere in this
packet.

The Encoding Standard is **not** pinned at this commit and this packet does not
pin it; see "The Encoding Standard boundary" below for the ratification request.
ECMA-262 is pinned at `0248456c758431e4bb8e5d26333ff1865123c9cd`, but its
`encodeURIComponent` is not in the promise lane's census scope, so the
component-set equivalence stays an open bridge here too.

## Scope: the twenty U3 rows

The scope is the census rows in the `percent-encoded-bytes` section together
with the encode-set definitions: the contiguous byte range [16209,25393) of the
pin, whose SHA-256 including the section heading from 16150 is
`9d0ebbddc939a5c0c6e12435d738516ef0dc0b412ea0007a0e0593acfde294ee`. Every span
digest below was recomputed by this seat from the sealed bytes with .NET
`System.Security.Cryptography.SHA256` over an explicit byte slice, and every
one agrees with the census. The `anchor-sha256` of all twenty rows was
recomputed the same way and also agrees; the anchor column is not repeated here.

Counts by kind: **15 `op`, 3 `rule`, 1 `type`, 1 `requirement`; twenty rows.**

| Kind | Census row id | Span | Bytes | Recomputed span SHA-256 |
| --- | --- | --- | --- | --- |
| `op` | op.percent-encoded-byte-syntax | [16209,16325) | 116 | `e932ad60acb037010d31617a2c15a6616c5c937f85d2e4ddb518bdfb0c09742c` |
| `requirement` | requirement.percent-encoded-utf8-advice | [16325,16862) | 537 | `777bc00b17dfcbd672c9f6df93b656ab950b72c8d76ca20f0efeb0976864468c` |
| `op` | op.percent-encode-byte | [16862,17111) | 249 | `d5c3d103b8b806a4fa398339bfab0e20dea4f43afb529e034d2a1da8f46bf9b0` |
| `op` | op.percent-decode-bytes | [17113,18462) | 1349 | `f1e84473e0f9ff75037833c851b4260b0c909f484c1c35d0e0a65686a81db556` |
| `op` | op.percent-decode-string | [18464,18967) | 503 | `a2de391cbe8a9820a896d3b8cbb6217e192c05549c68c42c539d3d341e6fef52` |
| `type` | type.percent-encode-set | [18975,19062) | 87 | `6b3a671be020062a50e688d80880c2160e70e1cbb6803945a815eb01a6450146` |
| `op` | op.c0-control-percent-encode-set | [19062,19252) | 190 | `3a77558e2e7c88d0ac517498ef6adb263dd71dac33faa417dd4d32e7abaf1a5c` |
| `op` | op.fragment-percent-encode-set | [19252,19458) | 206 | `3a3528a44621be42a50fadab093f846ab73089afc854d004504fc1a1c760ae01` |
| `op` | op.query-percent-encode-set | [19458,19661) | 203 | `40a713dbed67f2798a5a7727a6a634b6d99ad056f00c7ec860854833167b8240` |
| `rule` | rule.query-fragment-encode-set-difference | [19661,19816) | 155 | `8d376458e9d7756629833b5fa7dc4268a48504a1e4c2b2958f594a219423cf04` |
| `op` | op.special-query-percent-encode-set | [19816,19965) | 149 | `a02d9322f10e1431ee318f32f6c070c07e12195899e05b24a6319948cee4e05a` |
| `op` | op.path-percent-encode-set | [19965,20183) | 218 | `0ce861ea749f4d87b4fdf6de710212c3df69b49026b5f2f1dc604ba6470b7b06` |
| `op` | op.userinfo-percent-encode-set | [20183,20454) | 271 | `7686bccd526d0ad6a865e9495e681b55098147b32b70fceb600f850f126146e2` |
| `op` | op.component-percent-encode-set | [20454,20666) | 212 | `7cea81e47e63bfddd7a94d55ce75d9e5a0cf1fdbfaa0b8c13e0d42b4933c9751` |
| `rule` | rule.component-encodeuricomponent-equivalence | [20666,21163) | 497 | `4752ec9d22b43e3314668e458665a06a6e59596a7c317d27443d86335a8557bc` |
| `op` | op.form-percent-encode-set | [21163,21416) | 253 | `c544851fafc9d6063bba2624ff1be2d5465fef275e9c59d15bae5216b341bceb` |
| `rule` | rule.form-encode-set-complement | [21416,21624) | 208 | `4f47c51bf3405a137cfb90ddb29093e86041fdadd8af3153abf71baecc46d1a8` |
| `op` | op.percent-encode-after-encoding | [21624,24696) | 3072 | `392c22964c6825b50102ff51e28889d05b8a65346815f8593e3229bef6a23bef` |
| `op` | op.utf8-percent-encode-code-point | [24698,25071) | 373 | `c4c360f1de1b9e92e18502acd8152c9edb4763684d763476cf11a630f8995c5b` |
| `op` | op.utf8-percent-encode-string | [25073,25393) | 320 | `6e03cdafd70ca4858bfbd33b56834e7cfdaf3c6566576660b81de6a43c33a7c6` |

### Source evidence inside the scope that carries no row

The example table at [25459,27305), SHA-256
`4fa270b4ef01f88fe9fd30b223aa39184e6b3f323c03a1978583f0a00b91aec8`, is an
authored explanation in `census/url/explanations.tsv` ("Finite percent-encoding
and decoding examples for the preceding operations, including malformed escapes
and legacy encoder cases"). Its eleven rows are transcribed as the thirteen
`_example` probes of the laws battery and are labelled finite probes, never
laws. It is not a census row and it moves no coverage state.

### Consumers, named and out of scope

Seventeen further census rows depend on a scoped row and are **not** in U3. They
are listed here so the packet's boundary is explicit and so a later reviewer can
check that none of them was quietly proved:

| Consumer row | Scoped rows it depends on | Slice |
| --- | --- | --- |
| `op.host-parser` | percent-encoded-byte-syntax, percent-decode-string | U4 |
| `op.opaque-host-parser` | utf8-percent-encode-string, c0-control set | U4 |
| `op.parser-authority` | utf8-percent-encode-code-point, userinfo set | U5 |
| `op.parser-fragment` | utf8-percent-encode-code-point, fragment set | U5 |
| `op.parser-opaque-path` | utf8-percent-encode-code-point, c0-control set | U5 |
| `op.parser-path` | utf8-percent-encode-code-point, path set | U5 |
| `op.parser-query` | special-query set, query set, percent-encode-after-encoding | U5 |
| `op.set-url-username`, `op.set-url-password` | utf8-percent-encode-string, userinfo set | U5 |
| `op.url-units` | percent-encoded-byte-syntax | U5 |
| `rule.url-non-ascii-percent-encoding`, `rule.url-percent-encoded-units` | percent-encoded-byte-syntax | U5 |
| `rule.validation-domain-percent-encoded` | percent-encoded-byte-syntax | U4 |
| `op.urlencoded-parser` | percent-decode-bytes | U7 |
| `op.urlencoded-serializer` | percent-encode-after-encoding, form set | U7 |
| `rule.api-url-search-params-and-query-encoding` | form, query, special-query sets | U8 |
| `requirement.rendering-constrained-percent-decoding` | percent-decode-string | U6 |

Twenty scoped rows plus seventeen consumers is the 37 `percent`-anchored rows
`COORDINATION.md` records for this seat.

## Design

### 1. The percent-encode set carrier

`type.percent-encode-set` [18975,19062) says only "A percent-encode set is a set
of code points." The carrier is
`PercentEncodeSet := Whatwg.Infra.CodePoint → Bool`, a decidable predicate on
the canonical Infra code point (INFRA-R2's bounded natural, not `Char`, because
the C0 control set's "all code points greater than U+007E" includes surrogates).
`mem s c` is its application. No new code-point carrier is introduced.

The eight named sets are built upward by one construction,
`extend (base : PercentEncodeSet) (extra : List Nat)`, so that each text
sentence of the form "consisting of the X percent-encode set and …" becomes one
`extend` application over its parent, and the inclusion chain becomes a theorem
about `extend` rather than a fact about how someone wrote out the members:

```text
c0Control    = C0 controls, and every code point above U+007E
fragment     = extend c0Control [0x20, 0x22, 0x3C, 0x3E, 0x60]
query        = extend c0Control [0x20, 0x22, 0x23, 0x3C, 0x3E]
specialQuery = extend query     [0x27]
path         = extend query     [0x3F, 0x5E, 0x60, 0x7B, 0x7D]
userinfo     = extend path      [0x2F, 0x3A, 0x3B, 0x3D, 0x40, 0x5B, 0x5C, 0x5D, 0x7C]
component    = extend userinfo  [0x24, 0x25, 0x26, 0x2B, 0x2C]
form         = extend component [0x21, 0x27, 0x28, 0x29, 0x7E]
```

These are exactly the dependency edges the census records for the eight `op`
rows. The direct-inclusion theorems are the seven edges
c0Control ⊆ fragment, c0Control ⊆ query, query ⊆ specialQuery, query ⊆ path,
path ⊆ userinfo, userinfo ⊆ component, component ⊆ form; each is strict, with
the witness the text itself names first for that set. There is deliberately no
fragment-to-query edge: `rule.query-fragment-encode-set-difference`
[19661,19816) says the query set "cannot be defined in terms of the fragment
percent-encode set due to the omission of U+0060 (`)", and the packet freezes
the incomparability in both directions, U+0060 in fragment and not in query,
U+0023 in query and not in fragment.

Membership per set is stated exactly as the text lists it. Two inclusive ranges
are ranges and not endpoint pairs: `U+005B ([) to U+005D (]), inclusive` in the
userinfo set (which is where U+005C is smuggled in, `URL-PE-CE-002`) and
`U+0024 ($) to U+0026 (&), inclusive` in the component set. The form set's
`U+0027 (') to U+0029 RIGHT PARENTHESIS, inclusive` is a third.

Steps 1 and 2 of `op.percent-encode-after-encoding` [21624,24696) compare the
`percentEncodeSet` argument with named sets by identity, and a bare predicate
has no decidable equality. The algorithm therefore takes a finite index,
`SetName`, and `setOf` resolves it. `setOf_eq` pins the eight resolutions and
`setOf_injective` separates them; both are theorems, and the second is derivable
from the seven strictness witnesses plus the two incomparability witnesses.

### 2. Syntax, encode, decode

`op.percent-encoded-byte-syntax` [16209,16325) is a predicate on
`Whatwg.Infra.JsString`: exactly three code units, U+0025 then two **ASCII hex
digits** — either case, which `docs/URL-SOURCE-REVIEW.md` already recorded for
this span.

`op.percent-encode-byte` [16862,17111) emits "two ASCII upper hex digits". The
frozen output shape is `[0x25, upperHexDigit (value / 16), upperHexDigit (value
% 16)]`, with `upperHexDigit_isAsciiUpperHexDigit` forbidding the lower-case
mutant (`URL-PE-CE-001`) and `percentEncodeByte_injective` forbidding any
collapse. The two rows compose:
`percentEncodeByte_isPercentEncodedByte`.

`op.percent-decode-bytes` [17113,18462) is a total function on
`Whatwg.Infra.ByteSequence`, transcribed branch by branch:

- step 2.1, a byte that is not 0x25 is copied;
- step 2.3, `%` followed by two bytes in the three named ranges consumes all
  three and appends one byte;
- step 2.2 with two following bytes, a malformed escape copies **only** the `%`
  and reconsiders the two bytes (`URL-PE-CE-013`);
- step 2.2 with fewer than two following bytes, "the next two bytes … are not in
  the ranges" is vacuously satisfied, so the `%` is copied and nothing is
  dropped or truncated (`URL-PE-CE-003`, `URL-PE-CE-004`).

`op.percent-decode-string` [18464,18967) is `percentDecodeBytes` of the UTF-8
encoding of its scalar value string; the encoding is the boundary's answer, see
below.

### 3. The Encoding Standard boundary

`op.percent-encode-after-encoding` [21624,24696) calls four Encoding operations:
`getting an encoder` (step 3), the I/O queue (step 4), `encode or fail` (step
7.2), and, through its callers, `UTF-8 encode`. `census/url/externals.tsv`
already names all of them, and `docs/URL-DEPENDENCIES.md` already records that
one encoder is created once and retained across the run. None of them has an
owner in this repository: the Encoding Standard is not in `vendor/`, and Infra
explicitly defers to it (`infra.bs` says using `UTF-8 encode` "from Encoding is
encouraged" and every Infra call site carries `[[!ENCODING]]`). Infra's own
codec owns only isomorphic and ASCII conversions.

DB-02 is therefore the ruling that applies: hosts are decisions, and a
decision's answer is first-order data on a tape, never a modelled body. The
packet splits the algorithm accordingly.

`Whatwg.Url.Boundary` owns the profile:

- `EncoderName` is `utf8 | iso2022jp | other (label)`. `isStateful` is `true`
  for `iso2022jp` alone. This is the special case the pin names twice: the
  example table's `` "%1B(J\%1B(B" `` and the note inside `op.parser-query`
  [116259,118265) that the query state buffers "due to the stateful ISO-2022-JP
  encoder". A stateful encoder's answers are not a function of the input's code
  points taken independently, so no per-input-split composition law exists for
  it; `URL-PE-CE-006` freezes that as a witness rather than leaving it implicit.
- `EncodeAnswer` is one `encode or fail` answer: `output : ByteSequence` and
  `potentialError : Option Nat`, the code point value the URL text renders in
  base ten.
- `EncoderTape := List EncodeAnswer` is one run of step 7's while loop, and
  `EncoderTape.terminated` says the run ended, that is, its last answer is null.
  An unterminated or empty tape is a **live frontier**, not an error: the loop
  returns what it has, per AGENTS.md's representation rules.
- `Utf8Encoding` pairs the scalar value string with the byte sequence the
  Encoding owner returns for it; `Utf8DecodeOrFail` pairs a byte sequence with
  whether `UTF-8 decode without BOM or fail` ended as failure. Both are the
  answer shape, not a stored function.

`Whatwg.Url.PercentEncoding` then owns every step the URL text writes itself:
`encodingAssertion` (step 1), `spaceAsPlus` (step 2), `isomorph` (7.3.2),
`renderByte` (7.3.1 / 7.3.4 / 7.3.5), `errorReference` and `decimalDigits`
(7.4), `renderAnswer` (one iteration), `encodeLoop` (the loop), and
`percentEncodeAfterEncoding` (the assembly). All are total. The two UTF-8
specializations are total owned operations over a `Utf8Encoding`:
`utf8PercentEncodeString` and `utf8PercentEncodeCodePoint`. Their substantive
law is that UTF-8's non-failure collapses the loop to a per-byte rendering with
no error reference (`utf8PercentEncodeString_flatMap`), from which the
composition law `utf8PercentEncodeString_append` follows.

Step 7.3.3's assertion, "percentEncodeSet includes all non-ASCII code points",
is **discharged**, not assumed: `setOf_includes_non_ascii` proves it for all
eight named sets from the C0 control set's "all code points greater than
U+007E". It is not an assertion of ASCII compatibility of the encoding, and
`URL-PE-CE-014` attacks the mutant that drops the clause.

#### Ratification request: pin the Encoding Standard now

**Recommendation: pin it now, at U3, as a source, the way Web IDL and ECMA-262
were pinned beneath Streams by DB-11.** The reasons, in order of weight:

1. Three of the twenty scoped rows — `op.percent-decode-string`,
   `op.utf8-percent-encode-code-point`, `op.utf8-percent-encode-string` — have
   no content beyond "call UTF-8 encode and then this". Without a pin they have
   no anchored owner for the UTF-8 half, and U3 can close at most seventeen
   rows. This packet is written so that the other seventeen still close, but the
   three stay `partial` for a reason that is a repository gap, not a property of
   the URL text.
2. Deferring does not shrink the obligation, it moves it and multiplies the
   callers. U4's `op.host-parser` needs `utf8-decode-without-bom(-or-fail)`,
   U6's `requirement.rendering-constrained-percent-decoding` needs
   `utf8-decode-without-bom`, U7's `op.urlencoded-parser` and
   `op.urlencoded-serializer` need decode, encode, and `get an output encoding`.
   The same boundary is reopened four more times.
3. RS-1 already places "Encoding's UTF-8 core" in Stratum V, beneath both Infra
   and URL, and RS-D3 ranks it first. The natural home for `utf8Encode` and
   `utf8DecodeWithoutBom` once pinned is `Whatwg.Infra.Text.Codec`, beside
   `isomorphicDecode`, `asciiEncode` and `asciiDecode`, not inside `Whatwg.Url`.
   A URL-local UTF-8 codec would be exactly the convenience carrier
   `Whatwg/AGENTS.md` forbids.
4. The scope needed is small and separable: UTF-8's encoder and decoder, `get an
   encoder`, `encode or fail`, the I/O queue, and `UTF-8 decode without BOM (or
   fail)`. The legacy single-byte and multi-byte encoders, including
   ISO-2022-JP's own algorithm, stay out of scope and stay foreign-boundary
   profiles under `Whatwg.Url.Boundary`; the URL text needs only their answers.

**What the operator is asked to rule.** Pinning is outside this seat's fence:
`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`, `vendor/` and `generated/` are all
excluded from it. The ruling required is (A) pin the Encoding Standard now, add
its vendor tree and provenance rows, and place its UTF-8 core in
`Whatwg.Infra.Text.Codec`, after which the builder discharges the three rows and
this packet's `encoding` graph edge; or (B) defer to U7 or U9, in which case the
three rows stay `partial` with the boundary named exactly as frozen here and no
`utf8Encode` is invented anywhere in the meantime. This packet is buildable and
closable under either ruling; option (B) is the safe default if no ruling
arrives, and is what the DAG's `encoding` obligation records.

The component-set equivalence with ECMA-262's `encodeURIComponent`
(`rule.component-encodeuricomponent-equivalence` [20666,21163)) is a second,
independent bridge. The URL-owned half is frozen as `component_complement`: the
code points the component set leaves unencoded are exactly ASCII alphanumeric
together with the nine `uriMark` code points `-_.!~*'()`. The other half is
ECMA-262's, and no URL theorem discharges it.

## Frozen ascriptions

The Lean batteries are the authority on names and propositions; this section is
a reading aid. All three are frozen; a repair that changes a token of a
statement is a refusal, not a landing.

| Module | Ascriptions |
| --- | --- |
| `WhatwgTest/Url/PercentEncodingContract.lean` | 60 interface `#check`s: 20 under `Whatwg.Url.Boundary`, 40 under `Whatwg.Url.PercentEncoding` |
| `WhatwgTest/Url/PercentEncodingLaws.lean` | 95 theorem `#check`s: 4 under `Whatwg.Url.Boundary`, 91 under `Whatwg.Url.PercentEncoding`; 82 general laws and 13 `_example` finite probes |
| `WhatwgTest/Url/PercentEncodingAxiomReport.lean` | the same 95 names, in the same order, as `#print axioms` |
| `WhatwgTest/Url/Counterexamples/PercentEncoding.lean` | 15 finite mutant theorems for `URL-PE-CE-001`..`014`; green from the freeze |

The interface, in signature form:

```lean
-- Whatwg.Url.Boundary
EncoderName          : Type            -- utf8 | iso2022jp | other (label : JsString)
EncoderName.isStateful : EncoderName → Bool
EncodeAnswer         : Type            -- output : ByteSequence, potentialError : Option Nat
EncoderTape          : Type            -- List EncodeAnswer
EncoderTape.terminated : EncoderTape → Bool
Utf8Encoding         : Type            -- input : JsString, bytes : ByteSequence
Utf8Encoding.tape    : Utf8Encoding → EncoderTape
Utf8DecodeOrFail     : Type            -- input : ByteSequence, failed : Bool

-- Whatwg.Url.PercentEncoding
PercentEncodeSet     : Type                                    -- CodePoint → Bool
mem                  : PercentEncodeSet → CodePoint → Bool
extend               : PercentEncodeSet → List Nat → PercentEncodeSet
c0Control fragment query specialQuery path userinfo component form : PercentEncodeSet
SetName              : Type                                    -- eight constructors
setOf                : SetName → PercentEncodeSet
isHexByte            : Byte → Bool
hexValue             : Byte → Nat
upperHexDigit        : Nat → CodeUnit
decimalDigits        : Nat → JsString
isPercentEncodedByte : JsString → Bool
percentEncodeByte    : Byte → JsString
percentDecodeBytes   : ByteSequence → ByteSequence
percentDecodeString  : Boundary.Utf8Encoding → ByteSequence
followsUtf8Advice    : ByteSequence → Boundary.Utf8DecodeOrFail → Prop
encodingAssertion    : Boundary.EncoderName → SetName → Bool
spaceAsPlus          : SetName → Bool
isomorph             : Byte → CodePoint
renderByte           : Bool → PercentEncodeSet → Byte → JsString
errorReference       : Nat → JsString
renderAnswer         : Bool → PercentEncodeSet → Boundary.EncodeAnswer → JsString
encodeLoop           : Bool → PercentEncodeSet → Boundary.EncoderTape → JsString
percentEncodeAfterEncoding
                     : Boundary.EncoderName → SetName → Boundary.EncoderTape → JsString
utf8PercentEncodeString    : Boundary.Utf8Encoding → SetName → JsString
utf8PercentEncodeCodePoint : ScalarValue → Boundary.Utf8Encoding → SetName → JsString
```

Every carrier is Infra's: `Byte`, `ByteSequence`, `CodePoint`, `CodeUnit`,
`JsString`, `ScalarValue`, and `JsString.asciiEncode?` for the round trips. The
packet declares none of them and copies none of them.

## The laws, by row

| Census row | Frozen laws |
| --- | --- |
| `type.percent-encode-set` [18975,19062) | carrier and `mem`; no law of its own beyond the eight membership laws below |
| `op.c0-control-percent-encode-set` [19062,19252) | `c0Control_mem_iff`; `setOf_includes_non_ascii` rests on it |
| `op.fragment-percent-encode-set` [19252,19458) | `fragment_mem_iff`, `c0Control_subset_fragment`, `fragment_strict_c0Control` |
| `op.query-percent-encode-set` [19458,19661) | `query_mem_iff`, `c0Control_subset_query`, `query_strict_c0Control` |
| `op.special-query-percent-encode-set` [19816,19965) | `specialQuery_mem_iff`, `query_subset_specialQuery`, `specialQuery_strict_query` |
| `op.path-percent-encode-set` [19965,20183) | `path_mem_iff`, `query_subset_path`, `path_strict_query` |
| `op.userinfo-percent-encode-set` [20183,20454) | `userinfo_mem_iff`, `path_subset_userinfo`, `userinfo_strict_path` |
| `op.component-percent-encode-set` [20454,20666) | `component_mem_iff`, `userinfo_subset_component`, `component_strict_userinfo` |
| `op.form-percent-encode-set` [21163,21416) | `form_mem_iff`, `component_subset_form`, `form_strict_component` |
| `rule.query-fragment-encode-set-difference` [19661,19816) | `fragment_not_subset_query`, `query_not_subset_fragment` |
| `rule.form-encode-set-complement` [21416,21624) | `form_complement` |
| `rule.component-encodeuricomponent-equivalence` [20666,21163) | `component_complement` (URL half); the ECMA-262 half stays on the `bridges` edge |
| `op.percent-encoded-byte-syntax` [16209,16325) | `isPercentEncodedByte_iff`, `percentEncodeByte_isPercentEncodedByte` |
| `op.percent-encode-byte` [16862,17111) | `percentEncodeByte_eq`, `upperHexDigit_isAsciiUpperHexDigit`, `percentEncodeByte_upper`, `percentEncodeByte_injective`, two `_example` probes |
| `op.percent-decode-bytes` [17113,18462) | `isHexByte_iff`, `hexValue_digit/_upper/_lower`, `percentDecodeBytes_nil/_other/_pair/_malformed_pair/_short`, `percentDecodeBytes_length_le`, `_percent_le`, `_id_of_no_percent`, `_not_idempotent`, `percentDecodeBytes_percentEncodeByte`, two `_example` probes |
| `op.percent-decode-string` [18464,18967) | `percentDecodeString_eq`, one `_example` probe; the note's size claim is `_length_le` and `_percent_le` |
| `requirement.percent-encoded-utf8-advice` [16325,16862) | `followsUtf8Advice_iff`, `followsUtf8Advice_component` |
| `op.percent-encode-after-encoding` [21624,24696) | `encodingAssertion_iff`, `spaceAsPlus_iff`, `isomorph_val`, `renderByte_plus/_isomorph/_encoded`, `errorReference_eq`, `decimalDigits_zero/_isAsciiDigits/_shortest`, `renderAnswer_none/_some`, `encodeLoop_nil/_terminal/_cons/_append`, `EncoderTape.terminated_iff`, `percentEncodeAfterEncoding_eq`, `setOf_includes_non_ascii`, five `_example` probes |
| `op.utf8-percent-encode-string` [25073,25393) | `Utf8Encoding.tape_eq`, `utf8PercentEncodeString_eq`, `_flatMap`, `_append`, `_isAsciiString`, three `_example` probes |
| `op.utf8-percent-encode-code-point` [24698,25071) | `utf8PercentEncodeCodePoint_eq` |
| whole-family identity | `setOf_eq`, `setOf_injective` |
| whole-family boundary | `Boundary.isStateful_utf8`, `Boundary.isStateful_iso2022jp` |

### Round trips, on their exact stated domains

The text's own claim is the closing note of `op.percent-encode-after-encoding`
[21624,24696): only the component set and the form set encode U+0025 and "thus
give 'roundtripable data'". The packet states four things, not one:

1. `percentDecodeBytes_percentEncodeByte` — **no domain restriction**. For every
   byte, percent-decoding the ASCII encoding of its escape returns that byte.
2. `roundTrip_component` — **domain: every UTF-8 byte sequence**. The component
   set is the only named set that both encodes U+0025 and never maps U+0020 to
   `+`, so `percentDecodeBytes` of the ASCII encoding of
   `utf8PercentEncodeString e component` is `e.bytes` exactly.
3. `roundTrip_form` — **domain: byte sequences containing no 0x20**. Step 7.3.1
   maps SP to U+002B and percent-decode does not undo it; undoing it is the
   urlencoded parser's plus rule, a U7 row. `roundTrip_form_space_fails` freezes
   the exact failure at the boundary of that domain.
4. `roundTrip_query_fails` — the five parser sets do **not** round-trip: they
   leave U+0025 untouched, so `"%41"` returns as the single byte `0x41`. The
   text's own remedy, percent-encoding the `%` first, is a U5 caller's job.

### Idempotence

The text implies **no** idempotence here and this packet asserts none. It
implies the opposite, in the note at [18464,18967): percent-encoding produces
more U+0025 and percent-decoding fewer. The frozen statements are the two
monotonicity laws `percentDecodeBytes_length_le` and
`percentDecodeBytes_percent_le`, the fixed-point law
`percentDecodeBytes_id_of_no_percent`, and the explicit refutation
`percentDecodeBytes_not_idempotent` (`%2525` → `%25` → `%`). The absence of an
idempotence law is frozen, not omitted.

### Observation mask

**No mask.** DB-04 pre-registers M1 and M2 for the Streams calculus: they are a
consumer's view of chunk sequences and promise settlement order over a decision
tape. Percent encoding is a Stratum A atom (RS-2): every operation here is a
total function on Stratum V data, and `docs/SPEC-COVERAGE.md`'s green criterion
covers this case explicitly — "an equational family whose contract states no
mask records that instead, per row". This contract so records it, for all twenty
rows. The one decision in the family, the Encoding boundary's answer, is
first-order data on `Boundary.EncoderTape`, an argument of the operation, not an
observation of it. If a later URL packet needs a URL-specific projection it
allocates its own and states its relation to these equations; it does not
retrofit M1 or M2 onto them.

## Counterexample seeds

`URL-PE-CE-001` through `URL-PE-CE-014`, described in
`test/counterexamples/url/PERCENT-ENCODING.md` with executable witnesses in
`WhatwgTest/Url/Counterexamples/PercentEncoding.lean`. Each names the attack,
the mutant, and the frozen statement that must reject it. The coordinator owns
the stable rows in `test/counterexamples/REGISTER.md`; this seat does not edit
that file. Status at freeze is `SEEDED`.

## Acceptance conditions

1. Every one of the 60 interface ascriptions and 95 law ascriptions elaborates
   with no token of a statement changed. `git diff --ignore-all-space` for the
   three battery files is empty except for indentation repairs the
   `WhatwgTest/AGENTS.md` elaboration-repair allowance covers, and any such
   repair is recorded with before and after SHA-256.
2. All 95 receipts in the axiom report print inside the R-11 ceiling. The URL
   lane's choice-minimization objective applies: any receipt that reaches
   `Classical.choice` is reported with its exact dependency path and a
   constructive alternative attempted first. This family is finite, decidable,
   and structural; a receipt needing choice is a signal to look again.
3. The fifteen finite mutant witnesses stay green and unchanged.
4. `lake --wfail build Whatwg Gates` is green and `lake build` is green with the
   three known-red entries removed.
5. `lake exe vendorseal`, `lake exe citations`, `lake exe census` (all
   registered standards), `lake exe urlinventory` and `lake exe urlcensus` pass
   with every existing projection byte-identical. No file under `vendor/`,
   `generated/` or `census/` changes.
6. No declaration is added under `Whatwg/Infra/`, and no byte, code point, code
   unit, string, scalar value, or byte sequence carrier is redeclared under
   `Whatwg/Url/`.
7. Nothing in this packet is reported as coverage. URL has no admitted
   denominator, numerator, or report; `docs/SPEC-COVERAGE.md` and
   `docs/URL-CENSUS-DAG.md` own that gap and the U3 landing does not close it.
   A green battery is a set of theorems, not a coverage state.
8. `docs/URL-PERCENT-ENCODING-DAG.md`'s edges are updated only where evidence
   exists. In particular the `encoding` obligation stays open until the
   ratification above is answered.

## Expected declaration delta

`Whatwg/Url/Boundary.lean`, today declaration-free, gains four types
(`EncoderName` with three constructors, `EncodeAnswer`, `Utf8Encoding`,
`Utf8DecodeOrFail`), one abbreviation (`EncoderTape`), and three operations
(`EncoderName.isStateful`, `EncoderTape.terminated`, `Utf8Encoding.tape`), plus
the four Boundary theorems.

`Whatwg/Url/PercentEncoding.lean`, today declaration-free, gains the
`PercentEncodeSet` abbreviation, `mem`, `extend`, the eight named sets,
`SetName` with eight constructors, `setOf`, four helpers (`isHexByte`,
`hexValue`, `upperHexDigit`, `decimalDigits`), and the seventeen algorithm
operations listed above, plus the 91 PercentEncoding theorems.

That is **60 frozen non-theorem declarations and 95 frozen theorems, 155 named
public declarations in two modules**, from a starting point of zero. Derived
constructors, field projections, `DecidableEq` and `Repr` instances, and
equation lemmas inherit the owning row deterministically and must still appear
in the eventual generated declaration snapshot. Private helpers are permitted
and are not ascribed. A module split to respect dependency direction is
permitted while the stable names and root reachability stay fixed;
`Whatwg/Url.lean` already imports both files.

No declaration is added to any other tree. `WhatwgTest.lean` gains four imports
and `test/fixtures/trust-gate/known-red.txt` three entries; both are
append-only for this seat, which shares them with the concurrent promise lane.

## Freeze receipt

Branch `url/u3-breaker` from `main` at `7345c96`. Files introduced by this
packet:

- `test/contracts/url-percent-encoding.contract.md`
- `docs/URL-PERCENT-ENCODING-DAG.md`
- `test/counterexamples/url/PERCENT-ENCODING.md`
- `WhatwgTest/Url/PercentEncodingContract.lean`
- `WhatwgTest/Url/PercentEncodingLaws.lean`
- `WhatwgTest/Url/PercentEncodingAxiomReport.lean`
- `WhatwgTest/Url/Counterexamples/PercentEncoding.lean`

Shared files appended to: `WhatwgTest.lean` (four imports),
`test/fixtures/trust-gate/known-red.txt` (three entries plus its packet note),
`docs/URL-PACKAGE-PLAN.md` (the U3 packet subsection, the only plan edit). No
file under `Whatwg/`, `Gates/`, `census/`, `generated/`, `vendor/`, and no
existing URL or Streams contract, battery, `REGISTER.md`, `SPEC-MANIFEST.md`,
`PLAN.md` or `COORDINATION.md` is edited.

Measured evidence, 2026-09-07, pinned Lean 4.33.1, `LEAN_NUM_THREADS=1`:

| Command | Result |
| --- | --- |
| `Get-FileHash -Algorithm SHA256 vendor/whatwg-url-55d66993/url.bs` | `a5aa827f…3c805`, 162,680 bytes; agrees with the census header |
| Independent .NET SHA-256 over each of the twenty spans and their anchors | all forty digests agree with `generated/url-census.tsv`; no vendored or generated byte changed |
| `lake --wfail build Whatwg Gates` | PASS, 164 jobs |
| `lake env lean -DmaxErrors=5000 WhatwgTest/Url/PercentEncodingContract.lean` | exit 1, 114 diagnostics, all `Unknown identifier` |
| `lake env lean -DmaxErrors=5000 WhatwgTest/Url/PercentEncodingLaws.lean` | exit 1, 354 diagnostics, all `Unknown identifier` |
| `lake env lean -DmaxErrors=5000 WhatwgTest/Url/PercentEncodingAxiomReport.lean` | exit 1, 95 diagnostics, all `Unknown constant` |
| `lake env lean -DmaxErrors=5000 WhatwgTest/Url/Counterexamples/PercentEncoding.lean` | exit 0; all fifteen mutant witnesses pass by kernel reduction |
| `lake build WhatwgTest` | exit 1; exactly the three declared modules log failures and nothing else |

563 diagnostics over 155 distinct names, every one of them under
`Whatwg.Url.PercentEncoding` or `Whatwg.Url.Boundary`. There is no parse error,
no import error, no type mismatch, and no failed instance synthesis; the two
batteries import `Whatwg.Infra` and the declaration-free `Whatwg.Url` root, both
of which build. This is intended red. No synthetic error-recovery term is
admitted as a proof, and no full build was run in this worktree.

No graph edge of `URL-PG-PERCENT` closes at this freeze. The packet states what
the builder must prove; it claims no implementation, no coverage, no host
observation, and no property of the Encoding Standard or of ECMA-262.
