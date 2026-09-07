import Whatwg.Infra
import Whatwg.Url

/-!
Breaker-owned U3 law battery for the URL percent-encoding packet.

Contract: `test/contracts/url-percent-encoding.contract.md`.
Graph: `URL-PG-PERCENT` (`docs/URL-PERCENT-ENCODING-DAG.md`).
Interface: `WhatwgTest/Url/PercentEncodingContract.lean`.
Receipts: `WhatwgTest/Url/PercentEncodingAxiomReport.lean`.

Every proposition below is frozen by `#check (@name : proposition)` ascription
and cites its census row of `generated/url-census.tsv` with that row's byte span
into `vendor/whatwg-url-55d66993/url.bs`
(`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`).

**Observation mask.** This family is equational and names no mask. DB-04's M1
and M2 are Streams' consumer observations over decision tapes; percent encoding
is a Stratum A atom (RS-2) whose operations are total functions on Stratum V
data, so `docs/SPEC-COVERAGE.md`'s green criterion applies in its
"an equational family whose contract states no mask records that instead"
form. The one place a decision appears is the Encoding boundary, and it appears
as first-order data on `Whatwg.Url.Boundary.EncoderTape`, not as a mask.

**Evidence classes.** Names ending `_example` are finite probes transcribed from
the source's own example table [25459,27305) (SHA-256
`4fa270b4ef01f88fe9fd30b223aa39184e6b3f323c03a1978583f0a00b91aec8`), which is an
explanatory region and carries no census row of its own. A passing finite probe
is a probe, never a general law.
-/

set_option autoImplicit false


/-! ## Percent-encode set membership, exactly as the text lists it

One law per encode-set row. Each states membership as the text's own sentence:
the parent set, then the individually named code points. -/

/-! Row `op.c0-control-percent-encode-set` [19062,19252): "consisting of
C0 controls and all code points greater than U+007E (~)". -/
#check (@Whatwg.Url.PercentEncoding.c0Control_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = true ↔
      (Whatwg.Infra.CodePoint.isC0Control c = true ∨ 0x7E < c.val))

/-! Row `op.fragment-percent-encode-set` [19252,19458): "consisting of the
C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+003C (<),
U+003E (>), and U+0060 (`)". -/
#check (@Whatwg.Url.PercentEncoding.fragment_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.fragment c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = true ∨
        c.val = 0x20 ∨ c.val = 0x22 ∨ c.val = 0x3C ∨ c.val = 0x3E ∨ c.val = 0x60))

/-! Row `op.query-percent-encode-set` [19458,19661): "consisting of the
C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+0023 (#),
U+003C (<), and U+003E (>)". -/
#check (@Whatwg.Url.PercentEncoding.query_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = true ∨
        c.val = 0x20 ∨ c.val = 0x22 ∨ c.val = 0x23 ∨ c.val = 0x3C ∨ c.val = 0x3E))

/-! Row `op.special-query-percent-encode-set` [19816,19965): "consisting of the
query percent-encode set and U+0027 (')". -/
#check (@Whatwg.Url.PercentEncoding.specialQuery_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.specialQuery c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true ∨
        c.val = 0x27))

/-! Row `op.path-percent-encode-set` [19965,20183): "consisting of the query
percent-encode set and U+003F (?), U+005E (^), U+0060 (`), U+007B ({), and
U+007D (})". -/
#check (@Whatwg.Url.PercentEncoding.path_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true ∨
        c.val = 0x3F ∨ c.val = 0x5E ∨ c.val = 0x60 ∨ c.val = 0x7B ∨ c.val = 0x7D))

/-! Row `op.userinfo-percent-encode-set` [20183,20454): "consisting of the path
percent-encode set and U+002F (/), U+003A (:), U+003B (;), U+003D (=),
U+0040 (@), U+005B ([) to U+005D (]), inclusive, and U+007C (|)". -/
#check (@Whatwg.Url.PercentEncoding.userinfo_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = true ∨
        c.val = 0x2F ∨ c.val = 0x3A ∨ c.val = 0x3B ∨ c.val = 0x3D ∨ c.val = 0x40 ∨
        (0x5B ≤ c.val ∧ c.val ≤ 0x5D) ∨ c.val = 0x7C))

/-! Row `op.component-percent-encode-set` [20454,20666): "consisting of the
userinfo percent-encode set and U+0024 ($) to U+0026 (&), inclusive, U+002B (+),
and U+002C (,)". -/
#check (@Whatwg.Url.PercentEncoding.component_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = true ∨
        (0x24 ≤ c.val ∧ c.val ≤ 0x26) ∨ c.val = 0x2B ∨ c.val = 0x2C))

/-! Row `op.form-percent-encode-set` [21163,21416): "consisting of the component
percent-encode set and U+0021 (!), U+0027 (') to U+0029 RIGHT PARENTHESIS,
inclusive, and U+007E (~)". -/
#check (@Whatwg.Url.PercentEncoding.form_mem_iff :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.form c = true ↔
      (Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = true ∨
        c.val = 0x21 ∨ (0x27 ≤ c.val ∧ c.val ≤ 0x29) ∨ c.val = 0x7E))


/-! ## The seven direct inclusions the text's "consisting of" sentences force

These are theorems, not definitions: each set is `extend`ed from its parent, so
the parent's membership implies the child's. The dependency edges of the census
rows are exactly these seven. -/

#check (@Whatwg.Url.PercentEncoding.c0Control_subset_fragment :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.fragment c = true)

#check (@Whatwg.Url.PercentEncoding.c0Control_subset_query :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true)

#check (@Whatwg.Url.PercentEncoding.query_subset_specialQuery :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.specialQuery c = true)

#check (@Whatwg.Url.PercentEncoding.query_subset_path :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = true)

#check (@Whatwg.Url.PercentEncoding.path_subset_userinfo :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = true)

#check (@Whatwg.Url.PercentEncoding.userinfo_subset_component :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = true)

#check (@Whatwg.Url.PercentEncoding.component_subset_form :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = true →
      Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.form c = true)


/-! ## The seven inclusions are strict

Each named witness is a code point the text lists in the child and not in the
parent. Without these the eight sets could collapse onto one predicate and every
inclusion above would still hold. -/

#check (@Whatwg.Url.PercentEncoding.fragment_strict_c0Control :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x20 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.fragment c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = false)

#check (@Whatwg.Url.PercentEncoding.query_strict_c0Control :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x20 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.c0Control c = false)

#check (@Whatwg.Url.PercentEncoding.specialQuery_strict_query :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x27 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.specialQuery c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = false)

#check (@Whatwg.Url.PercentEncoding.path_strict_query :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x3F ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = false)

#check (@Whatwg.Url.PercentEncoding.userinfo_strict_path :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x2F ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.path c = false)

#check (@Whatwg.Url.PercentEncoding.component_strict_userinfo :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x24 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.userinfo c = false)

#check (@Whatwg.Url.PercentEncoding.form_strict_component :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x21 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.form c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = false)


/-! ## The three cross-cutting rules of the section -/

/-! Row `rule.query-fragment-encode-set-difference` [19661,19816): "The query
percent-encode set cannot be defined in terms of the fragment percent-encode set
due to the omission of U+0060 (`)." The named omission. -/
#check (@Whatwg.Url.PercentEncoding.fragment_not_subset_query :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x60 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.fragment c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = false)

/-! Row `rule.query-fragment-encode-set-difference` [19661,19816), the other
direction: the two sets are incomparable, so neither can be defined as an
extension of the other. U+0023 (#) is in query and not in fragment. -/
#check (@Whatwg.Url.PercentEncoding.query_not_subset_fragment :
  ∃ c : Whatwg.Infra.CodePoint, c.val = 0x23 ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.query c = true ∧
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.fragment c = false)

/-! Row `rule.form-encode-set-complement` [21416,21624): the form percent-encode
set "contains all code points, except the ASCII alphanumeric, U+002A (*),
U+002D (-), U+002E (.), and U+005F (_)". -/
#check (@Whatwg.Url.PercentEncoding.form_complement :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.form c = true ↔
      ¬(Whatwg.Infra.CodePoint.isAsciiAlphanumeric c = true ∨
        c.val = 0x2A ∨ c.val = 0x2D ∨ c.val = 0x2E ∨ c.val = 0x5F))

/-! Row `rule.component-encodeuricomponent-equivalence` [20666,21163), the
URL-owned half: the code points the component percent-encode set leaves
unencoded are exactly ECMA-262's `uriUnescaped`, the ASCII alphanumeric together
with the nine `uriMark` code points `-_.!~*'()`. The other half, that
`encodeURIComponent()` escapes exactly the complement of that set, is an
ECMA-262 obligation on the `bridges` edge of `URL-PG-PERCENT`
(`ext.ecma262.encodeuricomponent`); no URL theorem discharges it. -/
#check (@Whatwg.Url.PercentEncoding.component_complement :
  ∀ c : Whatwg.Infra.CodePoint,
    Whatwg.Url.PercentEncoding.mem Whatwg.Url.PercentEncoding.component c = false ↔
      (Whatwg.Infra.CodePoint.isAsciiAlphanumeric c = true ∨
        c.val = 0x2D ∨ c.val = 0x5F ∨ c.val = 0x2E ∨ c.val = 0x21 ∨ c.val = 0x7E ∨
        c.val = 0x2A ∨ c.val = 0x27 ∨ c.val = 0x28 ∨ c.val = 0x29))


/-! ## The finite index resolves to the eight named sets and separates them -/

/-! `setOf` is pinned to the eight named sets; without this the algorithm's
identity tests could resolve any name to any set. -/
#check (@Whatwg.Url.PercentEncoding.setOf_eq :
  Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.c0Control =
      Whatwg.Url.PercentEncoding.c0Control ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.fragment =
      Whatwg.Url.PercentEncoding.fragment ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.query =
      Whatwg.Url.PercentEncoding.query ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.specialQuery =
      Whatwg.Url.PercentEncoding.specialQuery ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.path =
      Whatwg.Url.PercentEncoding.path ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.userinfo =
      Whatwg.Url.PercentEncoding.userinfo ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.component =
      Whatwg.Url.PercentEncoding.component ∧
    Whatwg.Url.PercentEncoding.setOf Whatwg.Url.PercentEncoding.SetName.form =
      Whatwg.Url.PercentEncoding.form)

/-! The eight named sets are pairwise distinct. Derivable from the seven
strictness witnesses and the two incomparability witnesses above; frozen
separately because steps 1 and 2 of `op.percent-encode-after-encoding`
[21624,24696) branch on set identity. -/
#check (@Whatwg.Url.PercentEncoding.setOf_injective :
  ∀ m n : Whatwg.Url.PercentEncoding.SetName,
    Whatwg.Url.PercentEncoding.setOf m = Whatwg.Url.PercentEncoding.setOf n → m = n)

/-! Step 7.3.3 of `op.percent-encode-after-encoding` [21624,24696): "Assert:
percentEncodeSet includes all non-ASCII code points." Every named set contains
the C0 control percent-encode set, which contains every code point greater than
U+007E, so the assertion holds for all eight and is discharged, not assumed. -/
#check (@Whatwg.Url.PercentEncoding.setOf_includes_non_ascii :
  ∀ (n : Whatwg.Url.PercentEncoding.SetName) (c : Whatwg.Infra.CodePoint),
    Whatwg.Infra.CodePoint.isAscii c = false →
      Whatwg.Url.PercentEncoding.mem (Whatwg.Url.PercentEncoding.setOf n) c = true)


/-! ## Percent-encoded byte syntax and percent-encode a byte -/

/-! Row `op.percent-encoded-byte-syntax` [16209,16325): "a string consisting of
U+0025 (%) followed by two ASCII hex digits". Either case, per the text's own
`ASCII hex digit` (not `ASCII upper hex digit`). -/
#check (@Whatwg.Url.PercentEncoding.isPercentEncodedByte_iff :
  ∀ s : Whatwg.Infra.JsString,
    Whatwg.Url.PercentEncoding.isPercentEncodedByte s = true ↔
      ∃ h1 h2 : Whatwg.Infra.CodeUnit,
        s = [0x25, h1, h2] ∧
        Whatwg.Infra.CodePoint.isAsciiHexDigit (Whatwg.Infra.CodePoint.ofUnit h1) = true ∧
        Whatwg.Infra.CodePoint.isAsciiHexDigit (Whatwg.Infra.CodePoint.ofUnit h2) = true)

/-! Row `op.percent-encode-byte` [16862,17111): "a string consisting of
U+0025 (%), followed by two ASCII upper hex digits representing byte". The exact
output shape. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_eq :
  ∀ b : Whatwg.Infra.Byte,
    Whatwg.Url.PercentEncoding.percentEncodeByte b =
      [0x25,
        Whatwg.Url.PercentEncoding.upperHexDigit (Whatwg.Infra.Byte.value b / 16),
        Whatwg.Url.PercentEncoding.upperHexDigit (Whatwg.Infra.Byte.value b % 16)])

/-! `upperHexDigit` produces an ASCII **upper** hex digit for every nibble; the
mutant that emits lower case (`URL-PE-CE-001`) fails here. -/
#check (@Whatwg.Url.PercentEncoding.upperHexDigit_isAsciiUpperHexDigit :
  ∀ n : Nat, n < 16 →
    Whatwg.Infra.CodePoint.isAsciiUpperHexDigit
      (Whatwg.Infra.CodePoint.ofUnit (Whatwg.Url.PercentEncoding.upperHexDigit n)) = true)

/-! The two emitted digits are ASCII upper hex digits, stated on the output of
`percentEncodeByte` itself rather than on the helper. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_upper :
  ∀ b : Whatwg.Infra.Byte,
    List.all (List.drop 1 (Whatwg.Url.PercentEncoding.percentEncodeByte b))
      (fun u => Whatwg.Infra.CodePoint.isAsciiUpperHexDigit
        (Whatwg.Infra.CodePoint.ofUnit u)) = true)

/-! Rows `op.percent-encode-byte` [16862,17111) and
`op.percent-encoded-byte-syntax` [16209,16325) compose: what the serializer
emits is what the syntax admits. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_isPercentEncodedByte :
  ∀ b : Whatwg.Infra.Byte,
    Whatwg.Url.PercentEncoding.isPercentEncodedByte
      (Whatwg.Url.PercentEncoding.percentEncodeByte b) = true)

/-! `percent-encode` is injective on the byte: distinct bytes never share an
escape. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_injective :
  ∀ a b : Whatwg.Infra.Byte,
    Whatwg.Url.PercentEncoding.percentEncodeByte a =
      Whatwg.Url.PercentEncoding.percentEncodeByte b → a = b)


/-! ## The hex reader of percent-decode

Step 2 of `op.percent-decode-bytes` [17113,18462) names its ranges by byte
value, and step 3.1 interprets the pair "decoded, and then … as a hexadecimal
number". Both cases are accepted on input. -/

#check (@Whatwg.Url.PercentEncoding.isHexByte_iff :
  ∀ b : Whatwg.Infra.Byte,
    Whatwg.Url.PercentEncoding.isHexByte b = true ↔
      ((0x30 ≤ Whatwg.Infra.Byte.value b ∧ Whatwg.Infra.Byte.value b ≤ 0x39) ∨
        (0x41 ≤ Whatwg.Infra.Byte.value b ∧ Whatwg.Infra.Byte.value b ≤ 0x46) ∨
        (0x61 ≤ Whatwg.Infra.Byte.value b ∧ Whatwg.Infra.Byte.value b ≤ 0x66)))

#check (@Whatwg.Url.PercentEncoding.hexValue_digit :
  ∀ b : Whatwg.Infra.Byte,
    0x30 ≤ Whatwg.Infra.Byte.value b → Whatwg.Infra.Byte.value b ≤ 0x39 →
      Whatwg.Url.PercentEncoding.hexValue b = Whatwg.Infra.Byte.value b - 0x30)

#check (@Whatwg.Url.PercentEncoding.hexValue_upper :
  ∀ b : Whatwg.Infra.Byte,
    0x41 ≤ Whatwg.Infra.Byte.value b → Whatwg.Infra.Byte.value b ≤ 0x46 →
      Whatwg.Url.PercentEncoding.hexValue b = Whatwg.Infra.Byte.value b - 0x37)

#check (@Whatwg.Url.PercentEncoding.hexValue_lower :
  ∀ b : Whatwg.Infra.Byte,
    0x61 ≤ Whatwg.Infra.Byte.value b → Whatwg.Infra.Byte.value b ≤ 0x66 →
      Whatwg.Url.PercentEncoding.hexValue b = Whatwg.Infra.Byte.value b - 0x57)


/-! ## Percent-decode a byte sequence, one law per branch of the text's step 2 -/

/-! Step 1 of `op.percent-decode-bytes` [17113,18462): "Let output be an empty
byte sequence." -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_nil :
  Whatwg.Url.PercentEncoding.percentDecodeBytes [] = [])

/-! Step 2.1: "If byte is not 0x25 (%), then append byte to output." -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_other :
  ∀ (b : Whatwg.Infra.Byte) (t : Whatwg.Infra.ByteSequence), b ≠ 0x25 →
    Whatwg.Url.PercentEncoding.percentDecodeBytes (b :: t) =
      b :: Whatwg.Url.PercentEncoding.percentDecodeBytes t)

/-! Step 2.3: the well-formed escape. The pair is read as a hexadecimal number
and the next two bytes are skipped. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_pair :
  ∀ (h1 h2 : Whatwg.Infra.Byte) (t : Whatwg.Infra.ByteSequence),
    Whatwg.Url.PercentEncoding.isHexByte h1 = true →
    Whatwg.Url.PercentEncoding.isHexByte h2 = true →
      Whatwg.Url.PercentEncoding.percentDecodeBytes (0x25 :: h1 :: h2 :: t) =
        UInt8.ofNat (Whatwg.Url.PercentEncoding.hexValue h1 * 16 +
          Whatwg.Url.PercentEncoding.hexValue h2) ::
            Whatwg.Url.PercentEncoding.percentDecodeBytes t)

/-! Step 2.2 with two following bytes: "if byte is 0x25 (%) and the next two
bytes … are not in the ranges …, append byte to output". Only the `%` is
appended; the two following bytes are **not** skipped and are reconsidered.
`URL-PE-CE-013` attacks the mutant that skips them. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_malformed_pair :
  ∀ (h1 h2 : Whatwg.Infra.Byte) (t : Whatwg.Infra.ByteSequence),
    (Whatwg.Url.PercentEncoding.isHexByte h1 = false ∨
      Whatwg.Url.PercentEncoding.isHexByte h2 = false) →
      Whatwg.Url.PercentEncoding.percentDecodeBytes (0x25 :: h1 :: h2 :: t) =
        0x25 :: Whatwg.Url.PercentEncoding.percentDecodeBytes (h1 :: h2 :: t))

/-! Step 2.2 with fewer than two following bytes: a trailing `%` or `%H` has no
two bytes after it, so they are not in the ranges and the `%` is copied.
`URL-PE-CE-003` and `URL-PE-CE-004` attack the mutants that fail or truncate. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_short :
  ∀ t : Whatwg.Infra.ByteSequence, List.length t < 2 →
    Whatwg.Url.PercentEncoding.percentDecodeBytes (0x25 :: t) =
      0x25 :: Whatwg.Url.PercentEncoding.percentDecodeBytes t)


/-! ## Size and fixed-point laws of percent-decode

The section's closing note [18464,18967): "percent-encoding results in a string
with more U+0025 (%) code points than the input, and percent-decoding results in
a byte sequence with less 0x25 (%) bytes than the input." Stated as the two
monotonicity facts that hold for every input; the strict reading fails on inputs
with no escape, which the text's "in general" acknowledges. -/

#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_length_le :
  ∀ input : Whatwg.Infra.ByteSequence,
    List.length (Whatwg.Url.PercentEncoding.percentDecodeBytes input) ≤ List.length input)

#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_percent_le :
  ∀ input : Whatwg.Infra.ByteSequence,
    List.length (List.filter (fun b => b == 0x25)
        (Whatwg.Url.PercentEncoding.percentDecodeBytes input)) ≤
      List.length (List.filter (fun b => b == 0x25) input))

/-! A byte sequence with no `%` is its own percent-decoding. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_id_of_no_percent :
  ∀ input : Whatwg.Infra.ByteSequence, (0x25 : Whatwg.Infra.Byte) ∉ input →
    Whatwg.Url.PercentEncoding.percentDecodeBytes input = input)

/-! Percent-decoding is **not** idempotent, and the text does not claim it is:
`%2525` decodes to `%25`, which decodes again to `%`. The packet freezes the
absence of an idempotence law with this witness rather than omitting it. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_not_idempotent :
  Whatwg.Url.PercentEncoding.percentDecodeBytes
      (Whatwg.Url.PercentEncoding.percentDecodeBytes [0x25, 0x32, 0x35, 0x32, 0x35]) ≠
    Whatwg.Url.PercentEncoding.percentDecodeBytes [0x25, 0x32, 0x35, 0x32, 0x35])


/-! ## Percent-decode a scalar value string, and the UTF-8 advice -/

/-! Row `op.percent-decode-string` [18464,18967): "Let bytes be the UTF-8
encoding of input. Return the percent-decoding of bytes." The UTF-8 encoding is
the boundary's answer. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeString_eq :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.PercentEncoding.percentDecodeString e =
      Whatwg.Url.PercentEncoding.percentDecodeBytes
        (Whatwg.Url.Boundary.Utf8Encoding.bytes e))

/-! Row `requirement.percent-encoded-utf8-advice` [16325,16862): "It is
generally a good idea for sequences of percent-encoded bytes to be such that,
when percent-decoded and then passed to UTF-8 decode without BOM or fail, they
do not end up as failure." The URL-owned content is which byte sequence is
handed to the boundary; whether it fails is the boundary's answer. -/
#check (@Whatwg.Url.PercentEncoding.followsUtf8Advice_iff :
  ∀ (input : Whatwg.Infra.ByteSequence) (answer : Whatwg.Url.Boundary.Utf8DecodeOrFail),
    Whatwg.Url.PercentEncoding.followsUtf8Advice input answer ↔
      (Whatwg.Url.Boundary.Utf8DecodeOrFail.input answer =
          Whatwg.Url.PercentEncoding.percentDecodeBytes input ∧
        Whatwg.Url.Boundary.Utf8DecodeOrFail.failed answer = false))

/-! The one case the URL side can discharge: output of the component set
percent-decodes back to the UTF-8 bytes it came from, so the advice reduces to
the boundary's non-failure hypothesis on exactly those bytes. The `host parser`
and `URL rendering` consumers the note names are U4 and U6 rows. -/
#check (@Whatwg.Url.PercentEncoding.followsUtf8Advice_component :
  ∀ (e : Whatwg.Url.Boundary.Utf8Encoding) (input : Whatwg.Infra.ByteSequence)
    (answer : Whatwg.Url.Boundary.Utf8DecodeOrFail),
    Whatwg.Infra.JsString.asciiEncode?
        (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
          Whatwg.Url.PercentEncoding.SetName.component) = some input →
      Whatwg.Url.Boundary.Utf8DecodeOrFail.input answer =
        Whatwg.Url.Boundary.Utf8Encoding.bytes e →
      Whatwg.Url.Boundary.Utf8DecodeOrFail.failed answer = false →
        Whatwg.Url.PercentEncoding.followsUtf8Advice input answer)


/-! ## Percent-encode after encoding, step by step -/

/-! Step 1 of `op.percent-encode-after-encoding` [21624,24696): "Assert:
encoding is UTF-8 or percentEncodeSet is special-query percent-encode set or
application/x-www-form-urlencoded percent-encode set." It is not an assertion
that the encoding is ASCII-compatible. -/
#check (@Whatwg.Url.PercentEncoding.encodingAssertion_iff :
  ∀ (enc : Whatwg.Url.Boundary.EncoderName) (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Url.PercentEncoding.encodingAssertion enc n = true ↔
      (enc = Whatwg.Url.Boundary.EncoderName.utf8 ∨
        n = Whatwg.Url.PercentEncoding.SetName.specialQuery ∨
        n = Whatwg.Url.PercentEncoding.SetName.form))

/-! Step 2: "Let spaceAsPlus be true if percentEncodeSet is
application/x-www-form-urlencoded percent-encode set; otherwise false."
`URL-PE-CE-005` and `URL-PE-CE-010` attack the mutants that widen it. -/
#check (@Whatwg.Url.PercentEncoding.spaceAsPlus_iff :
  ∀ n : Whatwg.Url.PercentEncoding.SetName,
    Whatwg.Url.PercentEncoding.spaceAsPlus n = true ↔
      n = Whatwg.Url.PercentEncoding.SetName.form)

/-! Step 7.3.2: "Let isomorph be a code point whose value is byte's value." -/
#check (@Whatwg.Url.PercentEncoding.isomorph_val :
  ∀ b : Whatwg.Infra.Byte,
    (Whatwg.Url.PercentEncoding.isomorph b).val = Whatwg.Infra.Byte.value b)

/-! Step 7.3.1: "If spaceAsPlus is true and byte is 0x20 (SP), then append
U+002B (+) to output and continue." The branch is taken before the set is
consulted, so it applies even though U+0020 is in every named set. -/
#check (@Whatwg.Url.PercentEncoding.renderByte_plus :
  ∀ s : Whatwg.Url.PercentEncoding.PercentEncodeSet,
    Whatwg.Url.PercentEncoding.renderByte true s 0x20 = [0x2B])

/-! Step 7.3.4: "If isomorph is not in percentEncodeSet, then append isomorph to
output." -/
#check (@Whatwg.Url.PercentEncoding.renderByte_isomorph :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet) (b : Whatwg.Infra.Byte),
    (sp = false ∨ b ≠ 0x20) →
    Whatwg.Url.PercentEncoding.mem s (Whatwg.Url.PercentEncoding.isomorph b) = false →
      Whatwg.Url.PercentEncoding.renderByte sp s b =
        [UInt16.ofNat (Whatwg.Infra.Byte.value b)])

/-! Step 7.3.5: "Otherwise, percent-encode byte and append the result to
output." -/
#check (@Whatwg.Url.PercentEncoding.renderByte_encoded :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet) (b : Whatwg.Infra.Byte),
    (sp = false ∨ b ≠ 0x20) →
    Whatwg.Url.PercentEncoding.mem s (Whatwg.Url.PercentEncoding.isomorph b) = true →
      Whatwg.Url.PercentEncoding.renderByte sp s b =
        Whatwg.Url.PercentEncoding.percentEncodeByte b)

/-! Step 7.4: append `"%26%23"`, the shortest base-ten ASCII digits of
potentialError, and `"%3B"`. -/
#check (@Whatwg.Url.PercentEncoding.errorReference_eq :
  ∀ k : Nat,
    Whatwg.Url.PercentEncoding.errorReference k =
      ([0x25, 0x32, 0x36, 0x25, 0x32, 0x33] : Whatwg.Infra.JsString) ++
        Whatwg.Url.PercentEncoding.decimalDigits k ++
        ([0x25, 0x33, 0x42] : Whatwg.Infra.JsString))

#check (@Whatwg.Url.PercentEncoding.decimalDigits_zero :
  Whatwg.Url.PercentEncoding.decimalDigits 0 = [0x30])

#check (@Whatwg.Url.PercentEncoding.decimalDigits_isAsciiDigits :
  ∀ k : Nat,
    List.all (Whatwg.Url.PercentEncoding.decimalDigits k)
      (fun u => Whatwg.Infra.CodePoint.isAsciiDigit (Whatwg.Infra.CodePoint.ofUnit u)) = true)

/-! "shortest": no leading zero above zero. `URL-PE-CE-009` attacks a padded
mutant. -/
#check (@Whatwg.Url.PercentEncoding.decimalDigits_shortest :
  ∀ k : Nat, 0 < k → List.head? (Whatwg.Url.PercentEncoding.decimalDigits k) ≠ some 0x30)

/-! Step 7.3 over one answer, with no error. -/
#check (@Whatwg.Url.PercentEncoding.renderAnswer_none :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet)
    (a : Whatwg.Url.Boundary.EncodeAnswer),
    Whatwg.Url.Boundary.EncodeAnswer.potentialError a = none →
      Whatwg.Url.PercentEncoding.renderAnswer sp s a =
        List.flatMap (Whatwg.Url.PercentEncoding.renderByte sp s)
          (Whatwg.Url.Boundary.EncodeAnswer.output a))

/-! Steps 7.3 and 7.4 over one answer that reported an error. -/
#check (@Whatwg.Url.PercentEncoding.renderAnswer_some :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet)
    (a : Whatwg.Url.Boundary.EncodeAnswer) (k : Nat),
    Whatwg.Url.Boundary.EncodeAnswer.potentialError a = some k →
      Whatwg.Url.PercentEncoding.renderAnswer sp s a =
        List.flatMap (Whatwg.Url.PercentEncoding.renderByte sp s)
            (Whatwg.Url.Boundary.EncodeAnswer.output a) ++
          Whatwg.Url.PercentEncoding.errorReference k)

/-! An unanswered encoder decision is a live frontier, not an error: the empty
tape produces the empty string (AGENTS.md, representation rules). -/
#check (@Whatwg.Url.PercentEncoding.encodeLoop_nil :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet),
    Whatwg.Url.PercentEncoding.encodeLoop sp s [] = [])

/-! Step 7's loop condition: "While potentialError is non-null." A null answer
is the last iteration; the rest of the tape is not read. `URL-PE-CE-011` attacks
the mutant that keeps going. -/
#check (@Whatwg.Url.PercentEncoding.encodeLoop_terminal :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet)
    (a : Whatwg.Url.Boundary.EncodeAnswer) (t : Whatwg.Url.Boundary.EncoderTape),
    Whatwg.Url.Boundary.EncodeAnswer.potentialError a = none →
      Whatwg.Url.PercentEncoding.encodeLoop sp s (a :: t) =
        Whatwg.Url.PercentEncoding.renderAnswer sp s a)

#check (@Whatwg.Url.PercentEncoding.encodeLoop_cons :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet)
    (a : Whatwg.Url.Boundary.EncodeAnswer) (t : Whatwg.Url.Boundary.EncoderTape) (k : Nat),
    Whatwg.Url.Boundary.EncodeAnswer.potentialError a = some k →
      Whatwg.Url.PercentEncoding.encodeLoop sp s (a :: t) =
        Whatwg.Url.PercentEncoding.renderAnswer sp s a ++
          Whatwg.Url.PercentEncoding.encodeLoop sp s t)

/-! The loop distributes over a tape split before its terminating answer. This
is the URL-owned half of composition; whether the **encoder** distributes over a
split of the input is a boundary property, false for ISO-2022-JP. -/
#check (@Whatwg.Url.PercentEncoding.encodeLoop_append :
  ∀ (sp : Bool) (s : Whatwg.Url.PercentEncoding.PercentEncodeSet)
    (as bs : Whatwg.Url.Boundary.EncoderTape),
    List.all as (fun a => Option.isSome (Whatwg.Url.Boundary.EncodeAnswer.potentialError a))
        = true →
      Whatwg.Url.PercentEncoding.encodeLoop sp s (as ++ bs) =
        Whatwg.Url.PercentEncoding.encodeLoop sp s as ++
          Whatwg.Url.PercentEncoding.encodeLoop sp s bs)

/-! `EncoderTape.terminated` records that a tape ends in a null answer, which is
what makes the loop's result a complete run rather than a frontier. -/
#check (@Whatwg.Url.Boundary.EncoderTape.terminated_iff :
  ∀ t : Whatwg.Url.Boundary.EncoderTape,
    Whatwg.Url.Boundary.EncoderTape.terminated t = true ↔
      ∃ a : Whatwg.Url.Boundary.EncodeAnswer,
        List.getLast? t = some a ∧
          Whatwg.Url.Boundary.EncodeAnswer.potentialError a = none)

/-! Row `op.percent-encode-after-encoding` [21624,24696) assembled: steps 2, 5,
6, 7 and 8 over the boundary's tape. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_eq :
  ∀ (enc : Whatwg.Url.Boundary.EncoderName) (n : Whatwg.Url.PercentEncoding.SetName)
    (tape : Whatwg.Url.Boundary.EncoderTape),
    Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding enc n tape =
      Whatwg.Url.PercentEncoding.encodeLoop (Whatwg.Url.PercentEncoding.spaceAsPlus n)
        (Whatwg.Url.PercentEncoding.setOf n) tape)


/-! ## The two UTF-8 specializations -/

/-! UTF-8 never fails, so `encode or fail` answers once with a null error. -/
#check (@Whatwg.Url.Boundary.Utf8Encoding.tape_eq :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.tape e =
      [Whatwg.Url.Boundary.EncodeAnswer.mk (Whatwg.Url.Boundary.Utf8Encoding.bytes e) none])

/-! Row `op.utf8-percent-encode-string` [25073,25393): "return the result of
running percent-encode after encoding with UTF-8, input, and
percentEncodeSet". -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_eq :
  ∀ (e : Whatwg.Url.Boundary.Utf8Encoding) (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Url.PercentEncoding.utf8PercentEncodeString e n =
      Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
        Whatwg.Url.Boundary.EncoderName.utf8 n (Whatwg.Url.Boundary.Utf8Encoding.tape e))

/-! The UTF-8 case collapses to a per-byte rendering with no error reference. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_flatMap :
  ∀ (e : Whatwg.Url.Boundary.Utf8Encoding) (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Url.PercentEncoding.utf8PercentEncodeString e n =
      List.flatMap
        (Whatwg.Url.PercentEncoding.renderByte (Whatwg.Url.PercentEncoding.spaceAsPlus n)
          (Whatwg.Url.PercentEncoding.setOf n))
        (Whatwg.Url.Boundary.Utf8Encoding.bytes e))

/-! The composition law: the encode-then-percent-encode pipeline is a monoid
homomorphism from UTF-8 byte concatenation to string concatenation, because
UTF-8 is stateless and the rendering is per byte. `URL-PE-CE-006` witnesses that
the corresponding statement fails for a stateful encoder. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_append :
  ∀ (e f g : Whatwg.Url.Boundary.Utf8Encoding) (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Url.Boundary.Utf8Encoding.bytes g =
        Whatwg.Url.Boundary.Utf8Encoding.bytes e ++ Whatwg.Url.Boundary.Utf8Encoding.bytes f →
      Whatwg.Url.PercentEncoding.utf8PercentEncodeString g n =
        Whatwg.Url.PercentEncoding.utf8PercentEncodeString e n ++
          Whatwg.Url.PercentEncoding.utf8PercentEncodeString f n)

/-! Row `op.utf8-percent-encode-code-point` [24698,25071): the code-point form is
the string form at "scalarValue as a string". -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeCodePoint_eq :
  ∀ (sv : Whatwg.Infra.ScalarValue) (e : Whatwg.Url.Boundary.Utf8Encoding)
    (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Url.Boundary.Utf8Encoding.input e =
        Whatwg.Infra.JsString.ofCodePoints [sv.val] →
      Whatwg.Url.PercentEncoding.utf8PercentEncodeCodePoint sv e n =
        Whatwg.Url.PercentEncoding.utf8PercentEncodeString e n)

/-! Every named set contains every code point above U+007E, so the output is an
ASCII string and the round-trip laws below may use `asciiEncode?`. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_isAsciiString :
  ∀ (e : Whatwg.Url.Boundary.Utf8Encoding) (n : Whatwg.Url.PercentEncoding.SetName),
    Whatwg.Infra.JsString.isAsciiString
      (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e n) = true)


/-! ## Round trips, on their exact stated domains

The closing note of `op.percent-encode-after-encoding` [21624,24696): "Of the
possible values for the percentEncodeSet argument only two end up encoding
U+0025 (%) and thus give 'roundtripable data': component percent-encode set and
application/x-www-form-urlencoded percent-encode set. The other values … leave
U+0025 (%) untouched." -/

/-! The unconditional byte-level round trip: decoding the ASCII encoding of a
percent-encoded byte returns that byte, for every byte, with no domain
restriction. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_percentEncodeByte :
  ∀ b : Whatwg.Infra.Byte,
    Option.map Whatwg.Url.PercentEncoding.percentDecodeBytes
      (Whatwg.Infra.JsString.asciiEncode?
        (Whatwg.Url.PercentEncoding.percentEncodeByte b)) = some [b])

/-! The component set round-trips on its whole domain: every UTF-8 byte
sequence. It is the only named set that both encodes U+0025 and never maps
U+0020 to `+`. -/
#check (@Whatwg.Url.PercentEncoding.roundTrip_component :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Option.map Whatwg.Url.PercentEncoding.percentDecodeBytes
        (Whatwg.Infra.JsString.asciiEncode?
          (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
            Whatwg.Url.PercentEncoding.SetName.component)) =
      some (Whatwg.Url.Boundary.Utf8Encoding.bytes e))

/-! The form set round-trips on the strictly smaller domain of byte sequences
containing no 0x20 (SP), because step 7.3.1 maps SP to U+002B (+) and
percent-decode does not undo that. The plus rule belongs to the urlencoded
parser (`op.urlencoded-parser`, U7), not to percent-decode. -/
#check (@Whatwg.Url.PercentEncoding.roundTrip_form :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    (0x20 : Whatwg.Infra.Byte) ∉ Whatwg.Url.Boundary.Utf8Encoding.bytes e →
      Option.map Whatwg.Url.PercentEncoding.percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
              Whatwg.Url.PercentEncoding.SetName.form)) =
        some (Whatwg.Url.Boundary.Utf8Encoding.bytes e))

/-! The form set fails to round-trip at the first space: `"%20"` in, `"+"` out,
`0x2B` back. The domain restriction above is exactly needed. -/
#check (@Whatwg.Url.PercentEncoding.roundTrip_form_space_fails :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e = [0x20] →
      Option.map Whatwg.Url.PercentEncoding.percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
              Whatwg.Url.PercentEncoding.SetName.form)) = some [0x2B])

/-! The five parser sets do not round-trip: they leave U+0025 untouched, so an
input that already looks like an escape decodes to something else. Witness
`"%41"`, which returns as the single byte `0x41`. The text's own remedy is to
UTF-8 percent-encode the `%` first. -/
#check (@Whatwg.Url.PercentEncoding.roundTrip_query_fails :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e = [0x25, 0x34, 0x31] →
      Option.map Whatwg.Url.PercentEncoding.percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
              Whatwg.Url.PercentEncoding.SetName.query)) = some [0x41])


/-! ## The Encoding boundary's two frozen facts -/

#check (@Whatwg.Url.Boundary.isStateful_utf8 :
  Whatwg.Url.Boundary.EncoderName.isStateful Whatwg.Url.Boundary.EncoderName.utf8 = false)

/-! The ISO-2022-JP encoder carries state across `encode or fail` calls. This is
why `op.parser-query` [116259,118265) (U5, a consumer of this packet) encodes an
accumulated buffer rather than each code point independently, and why no
per-input-split composition law is available for it. -/
#check (@Whatwg.Url.Boundary.isStateful_iso2022jp :
  Whatwg.Url.Boundary.EncoderName.isStateful Whatwg.Url.Boundary.EncoderName.iso2022jp = true)


/-! ## Finite probes from the source's own example table [25459,27305)

Evidence class: finite probes. The region is explanatory and carries no census
row; these transcribe its eleven rows against the production names. -/

#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_example_23 :
  Whatwg.Url.PercentEncoding.percentEncodeByte 0x23 = [0x25, 0x32, 0x33])

#check (@Whatwg.Url.PercentEncoding.percentEncodeByte_example_7F :
  Whatwg.Url.PercentEncoding.percentEncodeByte 0x7F = [0x25, 0x37, 0x46])

/-! `` `%25%s%1G` `` percent-decodes to `` `%%s%1G` ``. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_example :
  Whatwg.Url.PercentEncoding.percentDecodeBytes
      [0x25, 0x32, 0x35, 0x25, 0x73, 0x25, 0x31, 0x47] =
    [0x25, 0x25, 0x73, 0x25, 0x31, 0x47])

/-! Lower-case hex is accepted on input: `` `%2e` `` decodes to 0x2E. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeBytes_example_lowercase :
  Whatwg.Url.PercentEncoding.percentDecodeBytes [0x25, 0x32, 0x65] = [0x2E])

/-! `"‽%25%2E"` percent-decodes to 0xE2 0x80 0xBD 0x25 0x2E. -/
#check (@Whatwg.Url.PercentEncoding.percentDecodeString_example :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e =
        [0xE2, 0x80, 0xBD, 0x25, 0x32, 0x35, 0x25, 0x32, 0x45] →
      Whatwg.Url.PercentEncoding.percentDecodeString e = [0xE2, 0x80, 0xBD, 0x25, 0x2E])

/-! Shift_JIS, `" "`, special-query: `"%20"`. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_space :
  ∀ lbl : Whatwg.Infra.JsString,
    Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
        (Whatwg.Url.Boundary.EncoderName.other lbl)
        Whatwg.Url.PercentEncoding.SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [0x20] none] =
      [0x25, 0x32, 0x30])

/-! Shift_JIS, `"≡"`, special-query: `"%81%DF"`. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_equiv :
  ∀ lbl : Whatwg.Infra.JsString,
    Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
        (Whatwg.Url.Boundary.EncoderName.other lbl)
        Whatwg.Url.PercentEncoding.SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [0x81, 0xDF] none] =
      [0x25, 0x38, 0x31, 0x25, 0x44, 0x46])

/-! Shift_JIS, `"‽"`, special-query: the encoder fails at U+203D and the run
emits `"%26%238253%3B"`. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_error :
  ∀ lbl : Whatwg.Infra.JsString,
    Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
        (Whatwg.Url.Boundary.EncoderName.other lbl)
        Whatwg.Url.PercentEncoding.SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [] (some 8253),
          Whatwg.Url.Boundary.EncodeAnswer.mk [] none] =
      [0x25, 0x32, 0x36, 0x25, 0x32, 0x33, 0x38, 0x32, 0x35, 0x33, 0x25, 0x33, 0x42])

/-! ISO-2022-JP, `"¥"`, special-query: `` "%1B(J\%1B(B" ``. The escape sequences
the stateful encoder emits are C0 controls and are percent-encoded; the payload
byte 0x5C is not in the special-query set and passes through as `` \ ``. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_iso2022jp :
  Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
      Whatwg.Url.Boundary.EncoderName.iso2022jp
      Whatwg.Url.PercentEncoding.SetName.specialQuery
      [Whatwg.Url.Boundary.EncodeAnswer.mk [0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42] none] =
    [0x25, 0x31, 0x42, 0x28, 0x4A, 0x5C, 0x25, 0x31, 0x42, 0x28, 0x42])

/-! Shift_JIS, `"1+1 ≡ 2%20‽"`, form set:
`"1%2B1+%81%DF+2%2520%26%238253%3B"`. Every distinguishing behaviour of the form
set appears here at once: `+` is escaped, SP becomes `+`, `%` is escaped, and
the encoder error becomes a decimal character reference. -/
#check (@Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_form :
  ∀ lbl : Whatwg.Infra.JsString,
    Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding
        (Whatwg.Url.Boundary.EncoderName.other lbl)
        Whatwg.Url.PercentEncoding.SetName.form
        [Whatwg.Url.Boundary.EncodeAnswer.mk
            [0x31, 0x2B, 0x31, 0x20, 0x81, 0xDF, 0x20, 0x32, 0x25, 0x32, 0x30] (some 8253),
          Whatwg.Url.Boundary.EncodeAnswer.mk [] none] =
      [0x31, 0x25, 0x32, 0x42, 0x31, 0x2B, 0x25, 0x38, 0x31, 0x25, 0x44, 0x46, 0x2B, 0x32,
        0x25, 0x32, 0x35, 0x32, 0x30, 0x25, 0x32, 0x36, 0x25, 0x32, 0x33, 0x38, 0x32, 0x35,
        0x33, 0x25, 0x33, 0x42])

/-! UTF-8 percent-encode U+2261 (≡) with the userinfo set: `"%E2%89%A1"`. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_equiv :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e = [0xE2, 0x89, 0xA1] →
      Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
          Whatwg.Url.PercentEncoding.SetName.userinfo =
        [0x25, 0x45, 0x32, 0x25, 0x38, 0x39, 0x25, 0x41, 0x31])

/-! UTF-8 percent-encode U+203D (‽) with the userinfo set: `"%E2%80%BD"`. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_interrobang :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e = [0xE2, 0x80, 0xBD] →
      Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
          Whatwg.Url.PercentEncoding.SetName.userinfo =
        [0x25, 0x45, 0x32, 0x25, 0x38, 0x30, 0x25, 0x42, 0x44])

/-! UTF-8 percent-encode `"Say what‽"` with the userinfo set:
`"Say%20what%E2%80%BD"`. -/
#check (@Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_say :
  ∀ e : Whatwg.Url.Boundary.Utf8Encoding,
    Whatwg.Url.Boundary.Utf8Encoding.bytes e =
        [0x53, 0x61, 0x79, 0x20, 0x77, 0x68, 0x61, 0x74, 0xE2, 0x80, 0xBD] →
      Whatwg.Url.PercentEncoding.utf8PercentEncodeString e
          Whatwg.Url.PercentEncoding.SetName.userinfo =
        [0x53, 0x61, 0x79, 0x25, 0x32, 0x30, 0x77, 0x68, 0x61, 0x74, 0x25, 0x45, 0x32,
          0x25, 0x38, 0x30, 0x25, 0x42, 0x44])
