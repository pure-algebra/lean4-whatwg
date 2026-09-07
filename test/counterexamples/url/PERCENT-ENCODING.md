# URL percent-encoding attacks (`URL-PE-CE-001` … `URL-PE-CE-014`)

Seeded by the U3 breaker seat, 2026-09-07, on `url/u3-breaker`.
Packet: `test/contracts/url-percent-encoding.contract.md`.
Graph: `docs/URL-PERCENT-ENCODING-DAG.md` (`URL-PG-PERCENT`).
Executable witnesses: `WhatwgTest/Url/Counterexamples/PercentEncoding.lean`.

Status at freeze: **`SEEDED`** for all fourteen. The coordinator owns the stable
rows in `test/counterexamples/REGISTER.md`; this seat does not edit that file.
The area token is `PE`, following the register's scheme for a standard other
than Streams: `URL-<AREA>-CE-<nnn>`, alongside the existing `URL-INV-`,
`URL-CEN-` and `URL-INP-` source-tooling rows.

Each row names the attack, the mutant a plausible implementation would produce,
and the frozen statement of `WhatwgTest/Url/PercentEncodingLaws.lean` that must
reject it. Byte spans are into `vendor/whatwg-url-55d66993/url.bs` at
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`; no line
number is cited.

The Lean witnesses are toy models over `List Nat`, deliberately independent of
the production names, and they are green from the freeze. A passing model
distinguishes a mutation; it proves nothing about the production declarations,
which is why every row also names the production statement that carries the
obligation.

## URL-PE-CE-001 — the serializer emits upper-case hex

`op.percent-encode-byte` [16862,17111) says "two ASCII **upper** hex digits".
`op.percent-encoded-byte-syntax` [16209,16325) accepts either case, so a
lower-case serializer still produces a valid percent-encoded byte and every
round-trip law still holds. Nothing catches it except a statement about the
output's case.

Mutant: nibbles rendered through `0x57 + n` rather than `0x37 + n`, so `0xAB`
becomes `"%ab"`.

Rejected by `upperHexDigit_isAsciiUpperHexDigit`, `percentEncodeByte_upper`,
`percentEncodeByte_eq`, and the two `_example` probes
`percentEncodeByte_example_23` and `_7F`.
Witness: `ce001_upper_hex_output`.

## URL-PE-CE-002 — an inclusive range is a range

`op.userinfo-percent-encode-set` [20183,20454) lists "U+005B ([) to U+005D (]),
inclusive". Read as a pair of endpoints it loses U+005C (\), which is exactly
the code point the URL parser most needs escaped in userinfo. The same shape
occurs twice more: "U+0024 ($) to U+0026 (&), inclusive" in
`op.component-percent-encode-set` [20454,20666) — dropping U+0025 there would
silently destroy the component set's round-trip property — and "U+0027 (') to
U+0029 RIGHT PARENTHESIS, inclusive" in `op.form-percent-encode-set`
[21163,21416).

Mutant: `[0x5B, 0x5D]` in place of `[0x5B, 0x5C, 0x5D]`.

Rejected by `userinfo_mem_iff`, `component_mem_iff` and `form_mem_iff`, each of
which states its range as `(lo ≤ c.val ∧ c.val ≤ hi)` rather than as a
disjunction of endpoints, and consequentially by `roundTrip_component`.
Witness: `ce002_userinfo_range_is_inclusive`.

## URL-PE-CE-003 — a lone `%` is copied, never consumed

Step 2.2 of `op.percent-decode-bytes` [17113,18462): "if byte is 0x25 (%) and
the next two bytes … are not in the ranges …, **append byte to output**". A
decoder that treats an invalid escape as garbage and drops the `%` changes the
decoded byte sequence and silently loses data.

Mutant: the malformed branch recurses without appending.

Rejected by `percentDecodeBytes_malformed_pair`, `percentDecodeBytes_short`, and
the source's own example probe `percentDecodeBytes_example`
(`` `%25%s%1G` `` → `` `%%s%1G` ``), whose output has three `%` bytes.
Witness: `ce003_lone_percent_is_copied`.

## URL-PE-CE-004 — a trailing `%2` is not an error and is not truncated

"the next two bytes after byte in input" does not exist at the end of the
sequence, so they are trivially "not in the ranges" and step 2.2 applies. A
decoder that returns failure, throws, or stops emitting at a short escape
diverges from a total function.

Mutant: the fewer-than-two-bytes branch returns the empty sequence.

Rejected by `percentDecodeBytes_short` and by `percentDecodeBytes_length_le`
read together with `percentDecodeBytes_id_of_no_percent`.
Witness: `ce004_trailing_partial_escape`.

## URL-PE-CE-005 — the form set is not the query set

Step 2 of `op.percent-encode-after-encoding` [21624,24696) sets `spaceAsPlus`
true "if percentEncodeSet is application/x-www-form-urlencoded percent-encode
set; otherwise false". Using the plus rule under any other set turns `"%20"`
into `"+"` in a URL query, which no consumer will decode back.

The converse mutation is as bad: using the query set where the form set is
required drops the plus rule and the `%`-escaping that
`rule.api-url-search-params-and-query-encoding` [150977,152303) depends on. That
consumer row is U8's, and this attack is why it must cite the sets rather than
restate them.

Mutant: `spaceAsPlus` computed from something other than set identity.

Rejected by `spaceAsPlus_iff`, `renderByte_plus`, `roundTrip_form`,
`roundTrip_form_space_fails`, and the `_example` probe
`percentEncodeAfterEncoding_example_form`.
Witness: `ce005_form_set_is_not_the_query_set`.

## URL-PE-CE-006 — the ISO-2022-JP encoder is stateful

Step 3 of `op.percent-encode-after-encoding` [21624,24696) creates **one**
encoder and step 7 reuses it across every `encode or fail` call. For ISO-2022-JP
this is observable: the encoder carries a shift state, so its answers for a
split input are not the concatenation of its answers for the parts. The pin
names this twice — the example table's
`` "%1B(J\%1B(B" `` for `"¥"` [25459,27305), and the note inside
`op.parser-query` [116259,118265) that the query state buffers "due to the
stateful ISO-2022-JP encoder". `op.parser-query` is a U5 consumer, not a U3 row,
but its buffering is only justified by this fact.

Two mutations are attacked. First, creating a fresh encoder per code point,
which repeats the `ESC ( J` / `ESC ( B` shift sequences. Second, assuming a
non-UTF-8 encoder's output is fully percent-encoded: the payload byte 0x5C is
not in the special-query set, so a literal backslash survives into the output.

Rejected by `Boundary.isStateful_iso2022jp` (with `isStateful_utf8` as the
contrast), by the domain hypothesis of `encodeLoop_append`, by the restriction
of `utf8PercentEncodeString_append` to UTF-8, and by the `_example` probe
`percentEncodeAfterEncoding_example_iso2022jp`.
Witnesses: `ce006_iso2022jp_is_stateful` and
`ce006_iso2022jp_output_is_not_all_escaped`.

## URL-PE-CE-007 — the query set is not the fragment set plus `#`

`rule.query-fragment-encode-set-difference` [19661,19816) exists precisely
because the obvious factoring is wrong: "The query percent-encode set cannot be
defined in terms of the fragment percent-encode set due to the omission of
U+0060 (`)." A refactor that shares the two definitions adds U+0060 to the query
set, so a backtick in a query is escaped where the standard leaves it alone.

Mutant: `query = fragment ∪ {U+0023}`.

Rejected by `query_mem_iff`, `fragment_not_subset_query` and
`query_not_subset_fragment`; the census's own dependency edges also make both
sets children of the C0 control set and neither a child of the other.
Witness: `ce007_query_omits_grave_accent`.

## URL-PE-CE-008 — percent-decode accepts lower-case hex

Step 2 of `op.percent-decode-bytes` [17113,18462) lists three ranges, including
"0x61 (a) to 0x66 (f)". Reusing the serializer's upper-hex predicate for the
decoder is a natural slip and makes `` `%2e` `` decode to itself.

Mutant: the decoder's hex test drops the lower-case range.

Rejected by `isHexByte_iff`, `hexValue_lower`, and the `_example` probe
`percentDecodeBytes_example_lowercase`.
Witness: `ce008_decode_accepts_lower_hex`.

## URL-PE-CE-009 — the decimal character reference is shortest and exact

Step 7.4 of `op.percent-encode-after-encoding` [21624,24696): append
`"%26%23"`, then "the shortest sequence of ASCII digits representing
potentialError in base ten", then `"%3B"`. A fixed-width or zero-padded
rendering changes the escaped `&#8253;` a legacy server would see.

Mutant: `"08253"` in place of `"8253"`.

Rejected by `errorReference_eq`, `decimalDigits_shortest`,
`decimalDigits_isAsciiDigits`, `decimalDigits_zero`, and the `_example` probe
`percentEncodeAfterEncoding_example_error`.
Witness: `ce009_error_reference_is_shortest`.

## URL-PE-CE-010 — the space rule precedes the set test

Step 7.3.1 tests `spaceAsPlus` **before** step 7.3.4 consults the set, and
`continue`s. Every named set contains U+0020, so an implementation that checks
membership first escapes SP as `"%20"` even under the form set and the plus rule
never fires.

Mutant: 7.3.4 and 7.3.5 evaluated before 7.3.1.

Rejected by `renderByte_plus` (unconditional in the set) together with
`renderByte_isomorph` and `renderByte_encoded`, whose hypotheses exclude the
`spaceAsPlus` space case, and by
`percentEncodeAfterEncoding_example_form`.
Witness: `ce010_space_rule_precedes_the_set_test`.

## URL-PE-CE-011 — the loop stops at the first null answer

Step 7's condition is "While potentialError is non-null", and step 6 seeds it
with a non-null value only so the loop is entered. A null answer is the last
iteration; anything after it on the tape is not part of this run. An
implementation that folds the whole tape appends output that the algorithm never
produces.

Mutant: the loop recurses on a null answer.

Rejected by `encodeLoop_terminal`, `encodeLoop_cons`, the hypothesis of
`encodeLoop_append`, `EncoderTape.terminated_iff`, and
`utf8PercentEncodeString_flatMap`, which is only correct because UTF-8's single
null answer ends the run.
Witness: `ce011_loop_stops_at_the_null_answer`.

## URL-PE-CE-012 — the component set leaves every `uriMark` alone

`rule.component-encodeuricomponent-equivalence` [20666,21163) says using the
component set with UTF-8 percent-encode "gives identical results to JavaScript's
`encodeURIComponent()`". That holds only because the component set's complement
is exactly ECMA-262's `uriUnescaped`: ASCII alphanumeric together with the nine
`uriMark` code points `-_.!~*'()`. Dropping any one of them, or adding a tenth,
breaks the equivalence while leaving every other law in this packet intact.

Mutant: U+0029 RIGHT PARENTHESIS moved into the component set.

Rejected by `component_complement`, and structurally by `component_mem_iff`
together with `form_mem_iff` (the form set is exactly the component set plus
`!`, `'`, `(`, `)`, `~`, so a component set that already contains `)` collapses
part of the difference) and by `form_strict_component`.
Witness: `ce012_component_leaves_every_uri_mark`.

## URL-PE-CE-013 — a malformed escape does not skip two bytes

Only step 2.3 says "Skip the next two bytes in input". Step 2.2 says nothing of
the kind, so after copying a `%` the decoder reconsiders the very next byte. In
`` `%%41` `` the second `%` begins a valid escape and the result is
`` `%A` ``; a decoder that skips gets `` `%1` ``.

Mutant: the malformed branch advances past the two examined bytes.

Rejected by `percentDecodeBytes_malformed_pair`, whose right-hand side recurses
on `h1 :: h2 :: t` and not on `t`.
Witness: `ce013_malformed_escape_does_not_skip`.

## URL-PE-CE-014 — the C0 control set covers everything above U+007E

`op.c0-control-percent-encode-set` [19062,19252) is "C0 controls **and all code
points greater than U+007E (~)**". The second clause is what makes step 7.3.3's
assertion — "percentEncodeSet includes all non-ASCII code points" — true for
every named set. Dropping it lets a UTF-8 continuation or lead byte pass through
as a raw isomorph, producing a string that is not an ASCII string and that no
round-trip law can recover.

Mutant: `c0Control = C0 controls` only.

Rejected by `c0Control_mem_iff`, `setOf_includes_non_ascii`,
`utf8PercentEncodeString_isAsciiString` (which the round-trip laws depend on),
and the `_example` probes `utf8PercentEncodeString_example_equiv`,
`_interrobang` and `_say`.
Witness: `ce014_c0_control_set_covers_above_tilde`.

## Verification and scope

Frozen before any implementation of `Whatwg/Url/PercentEncoding.lean` or
`Whatwg/Url/Boundary.lean`, both of which are declaration-free stubs at
`7345c96`. The witness module imports only `Std` and uses only kernel
reduction, so it needs no production name and is green at the freeze:

```text
lake env lean -DmaxErrors=5000 WhatwgTest/Url/Counterexamples/PercentEncoding.lean
```

exits 0. The three ascription batteries are red for unknown names only; the
contract's freeze receipt records their measured diagnostics.

The builder keeps all fifteen witnesses, imports the module in the test root
(already done by this packet), and does not add its module to
`test/fixtures/trust-gate/known-red.txt`, which lists only the three red
batteries. A row closes to `CLOSED` when its named production statements are
proved and the retained witness still distinguishes the mutant.

These finite models grant no URL semantic theorem, no coverage state, no axiom
receipt, and no property of the Encoding Standard or of ECMA-262.
