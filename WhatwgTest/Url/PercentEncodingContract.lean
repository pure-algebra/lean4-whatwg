import Whatwg.Infra
import Whatwg.Url

/-!
Breaker-owned U3 exact-signature battery for the URL percent-encoding packet.

Contract: `test/contracts/url-percent-encoding.contract.md`.
Graph: `URL-PG-PERCENT` (`docs/URL-PERCENT-ENCODING-DAG.md`).
Source: `vendor/whatwg-url-55d66993/url.bs`, SHA-256
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`. Every
declaration below cites its census row of `generated/url-census.tsv` and that
row's byte span; never a line number.

This module freezes the interface only. The propositions live in
`WhatwgTest/Url/PercentEncodingLaws.lean` and their receipts in
`WhatwgTest/Url/PercentEncodingAxiomReport.lean`. The builder must not change,
weaken, or delete an ascription here.

Both root imports are intentional. `Whatwg.Url` is a declaration-free stub tree
and `Whatwg.Infra` already owns every carrier used below, so the intended red
failures are unknown declarations under `Whatwg.Url.PercentEncoding` and
`Whatwg.Url.Boundary`, never an import or toolchain failure.

Carrier reuse (`Whatwg/AGENTS.md`): no byte, code-point, code-unit, string, or
byte-sequence carrier is declared here. `Whatwg.Infra.Byte`,
`Whatwg.Infra.ByteSequence`, `Whatwg.Infra.CodePoint`, `Whatwg.Infra.CodeUnit`,
`Whatwg.Infra.JsString`, and `Whatwg.Infra.ScalarValue` remain the canonical
owners, and the ASCII codec used by the round-trip laws is
`Whatwg.Infra.JsString.asciiEncode?`.
-/

set_option autoImplicit false


/-! ## The Encoding Standard boundary (`Whatwg.Url.Boundary`)

The Encoding Standard is not pinned at this commit, so `get an encoder`,
`encode or fail`, the I/O queue, `UTF-8 encode`, and
`UTF-8 decode without BOM or fail` have no owner in this repository. DB-02
applies: they are foreign boundaries whose answers are first-order data on a
tape, never modelled bodies. Row `op.percent-encode-after-encoding`
[21624,24696) is therefore stated relative to an encoder answer tape, and the
three rows that call UTF-8 —  `op.percent-decode-string` [18464,18967),
`op.utf8-percent-encode-code-point` [24698,25071), and
`op.utf8-percent-encode-string` [25073,25393) — are stated relative to the
supplied UTF-8 encoding of their input. -/

#check (@Whatwg.Url.Boundary.EncoderName :
  Type)

#check (@Whatwg.Url.Boundary.EncoderName.utf8 :
  Whatwg.Url.Boundary.EncoderName)

#check (@Whatwg.Url.Boundary.EncoderName.iso2022jp :
  Whatwg.Url.Boundary.EncoderName)

#check (@Whatwg.Url.Boundary.EncoderName.other :
  Whatwg.Infra.JsString → Whatwg.Url.Boundary.EncoderName)

#check (@Whatwg.Url.Boundary.EncoderName.isStateful :
  Whatwg.Url.Boundary.EncoderName → Bool)

#check (@Whatwg.Url.Boundary.EncodeAnswer :
  Type)

#check (@Whatwg.Url.Boundary.EncodeAnswer.mk :
  Whatwg.Infra.ByteSequence → Option Nat → Whatwg.Url.Boundary.EncodeAnswer)

#check (@Whatwg.Url.Boundary.EncodeAnswer.output :
  Whatwg.Url.Boundary.EncodeAnswer → Whatwg.Infra.ByteSequence)

#check (@Whatwg.Url.Boundary.EncodeAnswer.potentialError :
  Whatwg.Url.Boundary.EncodeAnswer → Option Nat)

#check (@Whatwg.Url.Boundary.EncoderTape :
  Type)

#check (@Whatwg.Url.Boundary.EncoderTape.terminated :
  Whatwg.Url.Boundary.EncoderTape → Bool)

#check (@Whatwg.Url.Boundary.Utf8Encoding :
  Type)

#check (@Whatwg.Url.Boundary.Utf8Encoding.mk :
  Whatwg.Infra.JsString → Whatwg.Infra.ByteSequence → Whatwg.Url.Boundary.Utf8Encoding)

#check (@Whatwg.Url.Boundary.Utf8Encoding.input :
  Whatwg.Url.Boundary.Utf8Encoding → Whatwg.Infra.JsString)

#check (@Whatwg.Url.Boundary.Utf8Encoding.bytes :
  Whatwg.Url.Boundary.Utf8Encoding → Whatwg.Infra.ByteSequence)

#check (@Whatwg.Url.Boundary.Utf8Encoding.tape :
  Whatwg.Url.Boundary.Utf8Encoding → Whatwg.Url.Boundary.EncoderTape)

#check (@Whatwg.Url.Boundary.Utf8DecodeOrFail :
  Type)

#check (@Whatwg.Url.Boundary.Utf8DecodeOrFail.mk :
  Whatwg.Infra.ByteSequence → Bool → Whatwg.Url.Boundary.Utf8DecodeOrFail)

#check (@Whatwg.Url.Boundary.Utf8DecodeOrFail.input :
  Whatwg.Url.Boundary.Utf8DecodeOrFail → Whatwg.Infra.ByteSequence)

#check (@Whatwg.Url.Boundary.Utf8DecodeOrFail.failed :
  Whatwg.Url.Boundary.Utf8DecodeOrFail → Bool)


/-! ## The percent-encode set carrier

Row `type.percent-encode-set` [18975,19062): "A percent-encode set is a set of
code points." The carrier is a decidable predicate on the canonical Infra code
point. `extend` is the one construction the eight named sets use, so the text's
"consisting of X and …" sentences become applications of it and the inclusion
chain becomes a theorem rather than a definition. -/

#check (@Whatwg.Url.PercentEncoding.PercentEncodeSet :
  Type)

#check (@Whatwg.Url.PercentEncoding.mem :
  Whatwg.Url.PercentEncoding.PercentEncodeSet → Whatwg.Infra.CodePoint → Bool)

#check (@Whatwg.Url.PercentEncoding.extend :
  Whatwg.Url.PercentEncoding.PercentEncodeSet → List Nat →
    Whatwg.Url.PercentEncoding.PercentEncodeSet)


/-! ## The eight named sets, in the text's own dependency order -/

#check (@Whatwg.Url.PercentEncoding.c0Control :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.fragment :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.query :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.specialQuery :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.path :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.userinfo :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.component :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)

#check (@Whatwg.Url.PercentEncoding.form :
  Whatwg.Url.PercentEncoding.PercentEncodeSet)


/-! ## The finite index the algorithm's own identity tests compare on

Steps 1 and 2 of `op.percent-encode-after-encoding` [21624,24696) compare the
`percentEncodeSet` argument with named sets. A bare predicate has no decidable
equality, so the algorithm takes the name and `setOf` resolves it. `setOf` is
pinned by `setOf_eq` and separated by `setOf_injective` in the laws battery. -/

#check (@Whatwg.Url.PercentEncoding.SetName :
  Type)

#check (@Whatwg.Url.PercentEncoding.SetName.c0Control :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.fragment :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.query :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.specialQuery :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.path :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.userinfo :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.component :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.SetName.form :
  Whatwg.Url.PercentEncoding.SetName)

#check (@Whatwg.Url.PercentEncoding.setOf :
  Whatwg.Url.PercentEncoding.SetName → Whatwg.Url.PercentEncoding.PercentEncodeSet)


/-! ## Hex and decimal helpers

`isHexByte` and `hexValue` are step 2's byte ranges and step 3.1's "decoded, and
then interpreted as a hexadecimal number" of `op.percent-decode-bytes`
[17113,18462). `upperHexDigit` is the "two ASCII upper hex digits" of
`op.percent-encode-byte` [16862,17111). `decimalDigits` is the "shortest
sequence of ASCII digits representing potentialError in base ten" of step 7.4 of
`op.percent-encode-after-encoding` [21624,24696). -/

#check (@Whatwg.Url.PercentEncoding.isHexByte :
  Whatwg.Infra.Byte → Bool)

#check (@Whatwg.Url.PercentEncoding.hexValue :
  Whatwg.Infra.Byte → Nat)

#check (@Whatwg.Url.PercentEncoding.upperHexDigit :
  Nat → Whatwg.Infra.CodeUnit)

#check (@Whatwg.Url.PercentEncoding.decimalDigits :
  Nat → Whatwg.Infra.JsString)


/-! ## Percent-encoded byte syntax, percent-encode, percent-decode -/

/-! Row `op.percent-encoded-byte-syntax` [16209,16325): "A percent-encoded byte
is a string consisting of U+0025 (%) followed by two ASCII hex digits." Either
hex case is accepted; the serializer emits upper case. -/
#check (@Whatwg.Url.PercentEncoding.isPercentEncodedByte :
  Whatwg.Infra.JsString → Bool)

/-! Row `op.percent-encode-byte` [16862,17111). -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeByte :
  Whatwg.Infra.Byte → Whatwg.Infra.JsString)

/-! Row `op.percent-decode-bytes` [17113,18462). -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes :
  Whatwg.Infra.ByteSequence → Whatwg.Infra.ByteSequence)

/-! Row `op.percent-decode-string` [18464,18967), over the boundary's UTF-8
answer for step 1's "the UTF-8 encoding of input". -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeString :
  Whatwg.Url.Boundary.Utf8Encoding → Whatwg.Infra.ByteSequence)

/-! Row `requirement.percent-encoded-utf8-advice` [16325,16862), over the
boundary's `UTF-8 decode without BOM or fail` answer. -/
#check (@Whatwg.Url.PercentEncoding.followsUtf8Advice :
  Whatwg.Infra.ByteSequence → Whatwg.Url.Boundary.Utf8DecodeOrFail → Prop)


/-! ## Percent-encode after encoding, step by step

Row `op.percent-encode-after-encoding` [21624,24696). `encodingAssertion` is
step 1, `spaceAsPlus` step 2, `isomorph` step 7.3.2, `renderByte` steps
7.3.1/7.3.4/7.3.5, `errorReference` step 7.4, `renderAnswer` one iteration of
step 7, and `encodeLoop` the whole while loop of step 7. Steps 3 and 4 —
`getting an encoder` and the I/O queue — are the boundary's, and appear only as
the answer tape. -/

#check (@Whatwg.Url.PercentEncoding.encodingAssertion :
  Whatwg.Url.Boundary.EncoderName → Whatwg.Url.PercentEncoding.SetName → Bool)

#check (@Whatwg.Url.PercentEncoding.spaceAsPlus :
  Whatwg.Url.PercentEncoding.SetName → Bool)

#check (@Whatwg.Url.PercentEncoding.isomorph :
  Whatwg.Infra.Byte → Whatwg.Infra.CodePoint)

#check (@Whatwg.Url.PercentEncoding.renderByte :
  Bool → Whatwg.Url.PercentEncoding.PercentEncodeSet → Whatwg.Infra.Byte →
    Whatwg.Infra.JsString)

#check (@Whatwg.Url.PercentEncoding.errorReference :
  Nat → Whatwg.Infra.JsString)

#check (@Whatwg.Url.PercentEncoding.renderAnswer :
  Bool → Whatwg.Url.PercentEncoding.PercentEncodeSet → Whatwg.Url.Boundary.EncodeAnswer →
    Whatwg.Infra.JsString)

#check (@Whatwg.Url.PercentEncoding.encodeLoop :
  Bool → Whatwg.Url.PercentEncoding.PercentEncodeSet → Whatwg.Url.Boundary.EncoderTape →
    Whatwg.Infra.JsString)

#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding :
  Whatwg.Url.Boundary.EncoderName → Whatwg.Url.PercentEncoding.SetName →
    Whatwg.Url.Boundary.EncoderTape → Whatwg.Infra.JsString)


/-! ## The two UTF-8 specializations -/

/-! Row `op.utf8-percent-encode-string` [25073,25393). -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString :
  Whatwg.Url.Boundary.Utf8Encoding → Whatwg.Url.PercentEncoding.SetName →
    Whatwg.Infra.JsString)

/-! Row `op.utf8-percent-encode-code-point` [24698,25071): the scalar value is
the algorithm's own argument and the encoding is the boundary's answer for
"scalarValue as a string". -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeCodePoint :
  Whatwg.Infra.ScalarValue → Whatwg.Url.Boundary.Utf8Encoding →
    Whatwg.Url.PercentEncoding.SetName → Whatwg.Infra.JsString)
