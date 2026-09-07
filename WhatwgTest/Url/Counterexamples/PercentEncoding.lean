import Std

/-!
# Finite URL percent-encoding mutants

Independent breaker models for `URL-PE-CE-001` through `URL-PE-CE-014`.
Attack record: `test/counterexamples/url/PERCENT-ENCODING.md`.
Contract: `test/contracts/url-percent-encoding.contract.md`.
Graph: `URL-PG-PERCENT` (`docs/URL-PERCENT-ENCODING-DAG.md`).

Every model here is a toy over `List Nat`, deliberately independent of
`Whatwg.Url.PercentEncoding`. It distinguishes a named mutation from the
transcription the pinned source
(`vendor/whatwg-url-55d66993/url.bs`,
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`) requires.
The matching quantified production statements are in
`WhatwgTest/Url/PercentEncodingLaws.lean`; a passing model here proves nothing
about them. Only kernel reduction is used, and no production import is needed,
so this module is green from the moment it is committed.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.Counterexamples.PercentEncoding.Breaker

/-! ## Shared toy vocabulary -/

/-- The digit of a nibble, in upper or lower case. -/
def hexDigit (upper : Bool) (n : Nat) : Nat :=
  if n < 10 then 0x30 + n else (if upper then 0x37 else 0x57) + n

/-- `op.percent-encode-byte` [16862,17111), parameterized by the case it emits.
The source says "two ASCII upper hex digits"; only `true` transcribes it. -/
def encodeByte (upper : Bool) (b : Nat) : List Nat :=
  [0x25, hexDigit upper (b / 16), hexDigit upper (b % 16)]

/-- Step 2 of `op.percent-decode-bytes` [17113,18462): the three byte ranges,
"0x30 (0) to 0x39 (9), 0x41 (A) to 0x46 (F), and 0x61 (a) to 0x66 (f), all
inclusive". -/
def isHex (n : Nat) : Bool :=
  decide (0x30 ≤ n ∧ n ≤ 0x39) || decide (0x41 ≤ n ∧ n ≤ 0x46) || decide (0x61 ≤ n ∧ n ≤ 0x66)

/-- Mutant hex reader that forgets the lower-case range. -/
def isHexUpperOnly (n : Nat) : Bool :=
  decide (0x30 ≤ n ∧ n ≤ 0x39) || decide (0x41 ≤ n ∧ n ≤ 0x46)

/-- Step 3.1: the pair "decoded, and then interpreted as a hexadecimal number". -/
def hexVal (n : Nat) : Nat :=
  if n ≤ 0x39 then n - 0x30 else if n ≤ 0x46 then n - 0x37 else n - 0x57

/-! ## Percent-decode and its four mutants -/

/-- `op.percent-decode-bytes` [17113,18462), with the hex reader as a parameter
so that `URL-PE-CE-008` can vary only that. The three short cases are step 2.2
with fewer than two bytes after the `%`: the byte is copied and nothing is
consumed. -/
def decodeWith (hex : Nat → Bool) : List Nat → List Nat
  | [] => []
  | [b] => [b]
  | [b, c] => [b, c]
  | b :: h1 :: h2 :: t =>
    if b == 0x25 then
      if hex h1 && hex h2 then (hexVal h1 * 16 + hexVal h2) :: decodeWith hex t
      else b :: decodeWith hex (h1 :: h2 :: t)
    else b :: decodeWith hex (h1 :: h2 :: t)

/-- The transcription. -/
def decode : List Nat → List Nat := decodeWith isHex

/-- Mutant: the lower-case hex range is missing from step 2's test. -/
def decodeUpperOnly : List Nat → List Nat := decodeWith isHexUpperOnly

/-- Mutant: a `%` that begins no valid escape is dropped instead of copied. -/
def decodeDropPercent : List Nat → List Nat
  | [] => []
  | [b] => if b == 0x25 then [] else [b]
  | [b, c] => if b == 0x25 then [c] else [b, c]
  | b :: h1 :: h2 :: t =>
    if b == 0x25 then
      if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: decodeDropPercent t
      else decodeDropPercent (h1 :: h2 :: t)
    else b :: decodeDropPercent (h1 :: h2 :: t)

/-- Mutant: a `%` with fewer than two bytes after it truncates the output. -/
def decodeTruncate : List Nat → List Nat
  | [] => []
  | [b] => if b == 0x25 then [] else [b]
  | [b, c] => if b == 0x25 then [] else [b, c]
  | b :: h1 :: h2 :: t =>
    if b == 0x25 then
      if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: decodeTruncate t
      else b :: decodeTruncate (h1 :: h2 :: t)
    else b :: decodeTruncate (h1 :: h2 :: t)

/-- Mutant: a malformed escape still skips the two following bytes, as a
well-formed one does. -/
def decodeSkipTwo : List Nat → List Nat
  | [] => []
  | [b] => [b]
  | [b, c] => [b, c]
  | b :: h1 :: h2 :: t =>
    if b == 0x25 then
      if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: decodeSkipTwo t
      else b :: decodeSkipTwo t
    else b :: decodeSkipTwo (h1 :: h2 :: t)

/-! ## Encode-set membership -/

/-- `op.c0-control-percent-encode-set` [19062,19252): "C0 controls and all code
points greater than U+007E (~)". -/
def c0Control (n : Nat) : Bool := decide (n ≤ 0x1F) || decide (0x7E < n)

/-- Mutant: only the C0 controls, dropping the "greater than U+007E" clause. -/
def c0ControlNoUpper (n : Nat) : Bool := decide (n ≤ 0x1F)

/-- The code points `op.userinfo-percent-encode-set` [20183,20454) adds to the
path set: "U+002F (/), U+003A (:), U+003B (;), U+003D (=), U+0040 (@),
U+005B ([) to U+005D (]), inclusive, and U+007C (|)". -/
def userinfoExtra : List Nat := [0x2F, 0x3A, 0x3B, 0x3D, 0x40, 0x5B, 0x5C, 0x5D, 0x7C]

/-- Mutant: the inclusive `[`-to-`]` range is read as its two endpoints. -/
def userinfoExtraNoBackslash : List Nat := [0x2F, 0x3A, 0x3B, 0x3D, 0x40, 0x5B, 0x5D, 0x7C]

/-- The code points `op.query-percent-encode-set` [19458,19661) adds to the
C0 control set. -/
def queryExtra : List Nat := [0x20, 0x22, 0x23, 0x3C, 0x3E]

/-- The code points `op.fragment-percent-encode-set` [19252,19458) adds. -/
def fragmentExtra : List Nat := [0x20, 0x22, 0x3C, 0x3E, 0x60]

/-- Mutant forbidden by `rule.query-fragment-encode-set-difference`
[19661,19816): query defined as the fragment set plus U+0023. -/
def queryFromFragment : List Nat := fragmentExtra ++ [0x23]

/-- ECMA-262's `uriMark`, the nine non-alphanumeric code points
`rule.component-encodeuricomponent-equivalence` [20666,21163) requires the
component set to leave alone. -/
def uriMark : List Nat := [0x2D, 0x5F, 0x2E, 0x21, 0x7E, 0x2A, 0x27, 0x28, 0x29]

/-- Mutant: U+0029 RIGHT PARENTHESIS dropped from the unreserved marks. -/
def uriMarkNoCloseParen : List Nat := [0x2D, 0x5F, 0x2E, 0x21, 0x7E, 0x2A, 0x27, 0x28]

/-- Whether the component set escapes a byte, given the marks it leaves alone. -/
def componentEscapes (unreserved : List Nat) (b : Nat) : Bool := !unreserved.contains b

/-! ## Step 7.3 of percent-encode after encoding -/

/-- Steps 7.3.1, 7.3.4 and 7.3.5 in the source's order: the space rule is tested
first and `continue`s, so the set is not consulted for it. -/
def renderByte (spaceAsPlus inSet : Bool) (b : Nat) : List Nat :=
  if spaceAsPlus && b == 0x20 then [0x2B]
  else if inSet then encodeByte true b else [b]

/-- Mutant: the set membership test runs first, so U+0020 is escaped even under
the form set, where every named set already contains it. -/
def renderByteSetFirst (spaceAsPlus inSet : Bool) (b : Nat) : List Nat :=
  if inSet then encodeByte true b
  else if spaceAsPlus && b == 0x20 then [0x2B] else [b]

/-- Step 7.4: `"%26%23"`, the digits, `"%3B"`. -/
def errorReference (digits : List Nat) : List Nat :=
  [0x25, 0x32, 0x36, 0x25, 0x32, 0x33] ++ digits ++ [0x25, 0x33, 0x42]

/-- "the shortest sequence of ASCII digits representing potentialError in base
ten" for 8253. -/
def shortestDigits : List Nat := [0x38, 0x32, 0x35, 0x33]

/-- Mutant: a zero-padded rendering. -/
def paddedDigits : List Nat := [0x30, 0x38, 0x32, 0x35, 0x33]

/-- One `encode or fail` answer: its output bytes and, when it failed, the
already-rendered decimal digits of the offending code point. -/
abbrev Answer := List Nat × Option (List Nat)

/-- Step 7's loop condition, "While potentialError is non-null": a null answer
ends the run and the rest of the tape is not read. -/
def loop : List Answer → List Nat
  | [] => []
  | (out, none) :: _ => out
  | (out, some digits) :: t => out ++ errorReference digits ++ loop t

/-- Mutant: the loop consumes the whole tape. -/
def loopAll : List Answer → List Nat
  | [] => []
  | (out, none) :: t => out ++ loopAll t
  | (out, some digits) :: t => out ++ errorReference digits ++ loopAll t

/-! ## The stateful ISO-2022-JP encoder -/

/-- The bytes `encode or fail` returns for `"¥¥"` when one encoder is created
once and retained across the run, as step 3 of `op.percent-encode-after-encoding`
[21624,24696) requires: one shift into JIS-Roman and one shift back. -/
def iso2022jpRetained : List Nat := [0x1B, 0x28, 0x4A, 0x5C, 0x5C, 0x1B, 0x28, 0x42]

/-- Mutant: a fresh encoder per code point, which repeats the escape sequences.
`op.parser-query` [116259,118265) names this encoder as the reason its state
buffers instead of encoding code points independently. -/
def iso2022jpPerCodePoint : List Nat :=
  [0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42, 0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42]

/-- The special-query set escapes the C0 escape bytes and leaves 0x5C alone. -/
def renderSpecialQuery (bytes : List Nat) : List Nat :=
  bytes.flatMap fun b => renderByte false (c0Control b || queryExtra.contains b || b == 0x27) b

/-! ## The fourteen frozen witnesses -/

/-- `URL-PE-CE-001`. `op.percent-encode-byte` [16862,17111) says "two ASCII
upper hex digits". Lower-case output is a different string. -/
theorem ce001_upper_hex_output : encodeByte true 0xAB ≠ encodeByte false 0xAB := by
  decide +kernel

/-- `URL-PE-CE-002`. `op.userinfo-percent-encode-set` [20183,20454) lists
"U+005B ([) to U+005D (]), inclusive"; reading it as two endpoints loses
U+005C (\). -/
theorem ce002_userinfo_range_is_inclusive :
    (userinfoExtra.contains 0x5C, userinfoExtraNoBackslash.contains 0x5C) = (true, false) := by
  decide +kernel

/-- `URL-PE-CE-003`. Step 2.2 of `op.percent-decode-bytes` [17113,18462)
appends the `%` itself; it is never dropped. -/
theorem ce003_lone_percent_is_copied : decode [0x25, 0x73] ≠ decodeDropPercent [0x25, 0x73] := by
  decide +kernel

/-- `URL-PE-CE-004`. A trailing `%2` has no two bytes after it, so both are
copied and nothing is truncated. -/
theorem ce004_trailing_partial_escape : decode [0x25, 0x32] ≠ decodeTruncate [0x25, 0x32] := by
  decide +kernel

/-- `URL-PE-CE-005`. Step 2 of `op.percent-encode-after-encoding` [21624,24696)
sets `spaceAsPlus` only for the form set. Using it for the query set turns
`"%20"` into `"+"`. -/
theorem ce005_form_set_is_not_the_query_set :
    renderByte false true 0x20 ≠ renderByte true true 0x20 := by
  decide +kernel

/-- `URL-PE-CE-006`. The ISO-2022-JP encoder is stateful, so `encode or fail`
over a retained encoder differs from a per-code-point restart. -/
theorem ce006_iso2022jp_is_stateful : iso2022jpRetained ≠ iso2022jpPerCodePoint := by
  decide +kernel

/-- `URL-PE-CE-006`, second half. The retained encoder's payload byte 0x5C is
not in the special-query set, so the rendered output carries a literal `\`; the
mutant claim that a non-UTF-8 encoder's output is fully percent-encoded is
false. Compare the example table's `` "%1B(J\%1B(B" `` [25459,27305). -/
theorem ce006_iso2022jp_output_is_not_all_escaped :
    renderSpecialQuery [0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42] =
      [0x25, 0x31, 0x42, 0x28, 0x4A, 0x5C, 0x25, 0x31, 0x42, 0x28, 0x42] := by
  decide +kernel

/-- `URL-PE-CE-007`. `rule.query-fragment-encode-set-difference` [19661,19816):
the query set "cannot be defined in terms of the fragment percent-encode set due
to the omission of U+0060 (`)". -/
theorem ce007_query_omits_grave_accent :
    (queryExtra.contains 0x60, queryFromFragment.contains 0x60) = (false, true) := by
  decide +kernel

/-- `URL-PE-CE-008`. Step 2 of `op.percent-decode-bytes` [17113,18462) accepts
0x61 (a) to 0x66 (f) as well; a decoder that takes only upper case leaves `%2e`
untouched. -/
theorem ce008_decode_accepts_lower_hex :
    decode [0x25, 0x32, 0x65] ≠ decodeUpperOnly [0x25, 0x32, 0x65] := by
  decide +kernel

/-- `URL-PE-CE-009`. Step 7.4 of `op.percent-encode-after-encoding`
[21624,24696) requires "the shortest sequence of ASCII digits". -/
theorem ce009_error_reference_is_shortest :
    errorReference shortestDigits ≠ errorReference paddedDigits := by
  decide +kernel

/-- `URL-PE-CE-010`. Step 7.3.1's `continue` skips 7.3.4 and 7.3.5. Testing set
membership first would escape SP even under the form set, since every named set
contains U+0020. -/
theorem ce010_space_rule_precedes_the_set_test :
    renderByte true true 0x20 ≠ renderByteSetFirst true true 0x20 := by
  decide +kernel

/-- `URL-PE-CE-011`. Step 7's loop stops at the first null `potentialError`; a
tape read past it produces a longer string. -/
theorem ce011_loop_stops_at_the_null_answer :
    loop [([0x41], none), ([0x42], none)] ≠ loopAll [([0x41], none), ([0x42], none)] := by
  decide +kernel

/-- `URL-PE-CE-012`. `rule.component-encodeuricomponent-equivalence`
[20666,21163): dropping one `uriMark` code point makes the component set escape
a code point `encodeURIComponent()` leaves alone. -/
theorem ce012_component_leaves_every_uri_mark :
    (componentEscapes uriMark 0x29, componentEscapes uriMarkNoCloseParen 0x29) = (false, true) := by
  decide +kernel

/-- `URL-PE-CE-013`. A malformed escape does not skip the two following bytes;
in `%%41` the second `%` still begins a valid escape. -/
theorem ce013_malformed_escape_does_not_skip :
    decode [0x25, 0x25, 0x34, 0x31] ≠ decodeSkipTwo [0x25, 0x25, 0x34, 0x31] := by
  decide +kernel

/-- `URL-PE-CE-014`. `op.c0-control-percent-encode-set` [19062,19252) includes
"all code points greater than U+007E (~)"; without that clause a UTF-8 lead byte
would pass through unescaped and step 7.3.3's assertion would fail. -/
theorem ce014_c0_control_set_covers_above_tilde : c0Control 0xE2 ≠ c0ControlNoUpper 0xE2 := by
  decide +kernel

end WhatwgTest.Url.Counterexamples.PercentEncoding.Breaker
