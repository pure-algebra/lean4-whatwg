# Infra UTF-8 codec attacks (`INFRA-UTF8-CE-001` … `INFRA-UTF8-CE-018`)

Seeded by the Infra UTF-8 breaker seat, 2026-09-07, on `infra/utf8-breaker`.
Packet: `test/contracts/infra-utf8.contract.md`.
Graph: `docs/INFRA-UTF8-DAG.md` (`INFRA-PG-UTF8`).
Executable witnesses: `WhatwgTest/Infra/Counterexamples/Utf8.lean`.

Status at freeze: **`SEEDED`** for all eighteen. The coordinator owns the stable
rows in `test/counterexamples/REGISTER.md`; this seat does not edit that file.
The area token is `UTF8`, following the register's scheme for a standard other
than Streams — `<STANDARD>-<AREA>-CE-<nnn>` — alongside the existing
`INFRA-SCALAR-`, `INFRA-INTEGER-` and `INFRA-TEXT-` rows.

Each row names the attack, the mutant a plausible implementation would produce,
and the frozen statement of `WhatwgTest/Infra/Utf8Laws.lean` that must reject
it. Byte spans are into `vendor/whatwg-encoding-67494fce/encoding.bs` at
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`, or into
`vendor/whatwg-infra-3f984adc/infra.bs` at
`7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb` where the
row says so. No line number is cited.

The Lean witnesses are toy models over `List Nat`, deliberately independent of
the production names, and they are green from the freeze. A passing model
distinguishes a mutation; it proves nothing about the production declarations,
which is why every row also names the production statement that carries the
obligation.

The witness module parameterizes the decoder by exactly the constants under
attack — the four boundary numbers, the restore step, the truncation count and
the "Otherwise" error — so a mutant differs from the transcription in one place
and the witness says which.

## INFRA-UTF8-CE-001 — an overlong encoding is accepted

`op.utf-8-decoder` [86515,90406), step 3, switch row "0xE0 to 0xEF", sub-step 1:
"If byte is 0xE0, then set UTF-8 lower boundary to 0xA0." A decoder that skips
that line accepts 0xE0 0x80 0x80 as U+0000. Overlong forms are the classic
filter-bypass: a security check that scans for `/` as 0x2F never sees
0xC0 0xAF, and a decoder that accepts the overlong form hands the path
traversal through. The pin's own note is explicit that this is not a choice:
"No other behavior is permitted per the Encoding Standard."

Mutant: `e0Lower := 0x80`.

Rejected by `decoderHandler_lead_three`, which states the installed lower
boundary as `if b.toNat = 0xE0 then 0xA0 else 0x80`, and by
`decodeWithoutBom_overlong_three_example`.
Witness: `ce001_overlong_accepted`.

## INFRA-UTF8-CE-002 — a surrogate code point is encoded

`op.utf-8-encoder` [90407,91744) has no step that rejects a surrogate. Steps 3
to 6 run on U+D800 as happily as on U+0800 and produce 0xED 0xA0 0x80, which the
decoder then rejects three times over. Nothing in the *algorithm* excludes
surrogates; the exclusion is step 3 of `op.process-an-item` [15509,17620),
"Assert: encoderDecoder is not an encoder instance or item is not a surrogate",
and the note of `note.hooks-for-standards` [43782,45058), "Standards are to
ensure that the input I/O queues they pass to UTF-8 encode … contain no
surrogates". An encoder typed on `CodePoint` therefore has no round trip.

Mutant: the encoder's domain is `Whatwg.Infra.CodePoint` rather than
`Whatwg.Infra.ScalarValue`.

Rejected by the *type* of `Whatwg.Infra.Utf8.encodeScalar` in
`WhatwgTest/Infra/Utf8Contract.lean` and by the `isScalarValueString`
hypothesis of `Whatwg.Infra.Utf8.encode`; the round-trip laws
`decodeWithoutBom_encodeScalars` and `decodeWithoutBom_encode` are false without
it.
Witness: `ce002_surrogate_encoded`.

## INFRA-UTF8-CE-003 — the 0xE0 second-byte lower boundary is off by one

Same switch row as CE-001, but the boundary is 0x9F instead of 0xA0. One less
than correct still admits the overlong encoding of U+07FF, 0xE0 0x9F 0xBF, which
has a two-byte form. An off-by-one is what a hand-transcribed table produces and
an all-or-nothing test never catches.

Mutant: `e0Lower := 0x9F`.

Rejected by `decoderHandler_lead_three` and
`decodeWithoutBom_overlong_three_example`, and the accepting side is pinned by
`ce003_006_boundaries_are_inclusive` so a mutant cannot pass by tightening the
boundary instead.
Witness: `ce003_e0_off_by_one`.

## INFRA-UTF8-CE-004 — the 0xED second-byte upper boundary is off by one

`op.utf-8-decoder` [86515,90406), step 3, switch row "0xE0 to 0xEF", sub-step 2:
"If byte is 0xED, then set UTF-8 upper boundary to 0x9F." That single line is
the *only* thing keeping the surrogate range out of the decoder's output. With
the boundary at 0xA0 the bytes 0xED 0xA0 0x80 decode to U+D800, and step 6.1 of
`op.process-an-item` [15509,17620) — "Assert: … result does not contain any
surrogates" — is violated. CESU-8 and modified UTF-8 both produce exactly these
bytes, so real inputs exercise it.

Mutant: `edUpper := 0xA0`.

Rejected by `decoderHandler_lead_three`,
`decoderHandler_items_isScalarValue`, `decodeWithoutBom_all_isScalarValue` and
`decodeWithoutBom_surrogate_example`; the accepting extreme U+D7FF is pinned by
`decodeWithoutBom_before_surrogates_example`.
Witness: `ce004_ed_off_by_one`.

## INFRA-UTF8-CE-005 — the 0xF0 second-byte lower boundary is off by one

Step 3, switch row "0xF0 to 0xF4", sub-step 1: "If byte is 0xF0, then set UTF-8
lower boundary to 0x90." With 0x8F the four-byte overlong encoding of U+FFFF,
0xF0 0x8F 0xBF 0xBF, is accepted.

Mutant: `f0Lower := 0x8F`.

Rejected by `decoderHandler_lead_four` and
`decodeWithoutBom_overlong_four_example`; the accepting extreme U+10000 is
pinned by `ce003_006_boundaries_are_inclusive`.
Witness: `ce005_f0_off_by_one`.

## INFRA-UTF8-CE-006 — the 0xF4 second-byte upper boundary is off by one

Step 3, switch row "0xF0 to 0xF4", sub-step 2: "If byte is 0xF4, then set UTF-8
upper boundary to 0x8F." With 0x90 the bytes 0xF4 0x90 0x80 0x80 decode to
0x110000, which is not a code point at all: `Whatwg.Infra.CodePoint` cannot hold
it, so the mutant is not merely wrong, it is unconstructible in the owned
carrier. That is the point — the boundary is what makes the decoder's result
type honest.

Mutant: `f4Upper := 0x90`.

Rejected by `decoderHandler_lead_four` and
`decodeWithoutBom_above_max_example`; the accepting extreme U+10FFFF is pinned
by `decodeWithoutBom_max_example`.
Witness: `ce006_f4_off_by_one`.

## INFRA-UTF8-CE-007 — the byte order mark is stripped twice

`op.utf-8-decode` [45059,45762) has exactly two steps before it processes the
queue: peek three bytes, and if they are 0xEF 0xBB 0xBF, read three bytes. Once.
A decoder that loops until the prefix is no longer a mark silently eats a
leading U+FEFF that is *data*, which is a real content change for a document
that begins with two marks.

Mutant: `stripBomAll`, a fixed-point strip.

Rejected by `decode_bom_once` and `decode_bom_twice_example`.
Witness: `ce007_bom_stripped_twice`.

## INFRA-UTF8-CE-008 — the byte order mark is not stripped at all

The other direction, and this one is the pinned text's own defect.
`op.io-queue-peek` [7651,8447) step 3 says "For each n in the range 1 to number,
inclusive … append ioQueue[n] to prefix". Infra's indexing is zero-based
(`infra.bs` [67159,67540): "a zero-based index into a list inside square
brackets") and Infra's "the range 1 to number, inclusive" is {1,…,number}
(`infra.bs` [82259,82581)), so the literal reading skips `ioQueue[0]`,
`peek 3` of « 0xEF, 0xBB, 0xBF » is « 0xBB, 0xBF », and step 2 of
`op.utf-8-decode` [45059,45762) never matches. `UTF-8 decode` would then be
`UTF-8 decode without BOM` and the note of `op.utf-8-decoder` [86515,90406)
about the mark having priority would describe nothing.

This is ruling request **INFRA-R15** in the contract. Both readings are frozen —
`IoQueue.peek` literal, `IoQueue.peekPrefix` zero-based — so the difference is a
theorem.

Mutant: `stripBomNever`, which is what the literal reading produces.

Rejected by `peek_eq_peekPrefix_tail`, `peek_bom_example`, `decode_bom_prefix`
and `decode_bom_only_example`.
Witness: `ce008_bom_never_stripped`.

## INFRA-UTF8-CE-009 — `UTF-8 decode without BOM` strips the mark

`op.utf-8-decode-without-bom` [45763,46180) has no step 1 and no step 2: it
processes the queue and returns. The two hooks differ in exactly the three-byte
test, and `note.hooks-for-standards` [43782,45058) says which to use where —
"For decoding, UTF-8 decode is to be used by new formats. For identifiers or
byte sequences within a format or protocol, use UTF-8 decode without BOM". An
identifier that happens to begin with U+FEFF must keep it.

Mutant: `decodeWithoutBom` implemented as `decode`.

Rejected by `decodeWithoutBom_keeps_bom_example` against
`decode_bom_only_example`.
Witness: `ce009_without_bom_keeps_the_mark`.

## INFRA-UTF8-CE-010 — the fail mode returns `some` on a malformed input

`op.utf-8-decode-without-bom-or-fail` [46181,46905) step 2: "If potentialError
is an error, then return failure." A decoder that runs the replacement mode and
returns its output unconditionally answers `some [U+FFFD, U+FFFD]` for
0xC0 0x80. The callers the pin names for this hook — RFC 6455's WebSocket close
reason and the WebAssembly JS API's custom section names — are exactly the
places where substituting U+FFFD instead of failing is a protocol violation.

Mutant: `fatal` implemented as `some ∘ replacement`.

Rejected by `decodeWithoutBomOrFail_eq_none_iff`,
`decodeWithoutBomOrFail_malformed_example` and `isWellFormed_iff`.
Witness: `ce010_fail_mode_returns_some`.

## INFRA-UTF8-CE-011 — the fail mode fails on a well-formed U+FFFD

The converse, and the reason the packet declares `Whatwg.Infra.Utf8.errorCount`
at all. "The fail mode returns none exactly when the replacement mode would emit
U+FFFD" is **false** read as a statement about the output: U+FFFD is a scalar
value, 0xEF 0xBF 0xBD is its well-formed encoding, and
`decodeWithoutBom [0xEF, 0xBF, 0xBD] = [U+FFFD]` while the fatal mode succeeds.
An implementation that decides failure by scanning the output for U+FFFD rejects
every document that legitimately contains a replacement character — which is
every document that has already been through one lossy decode.

The correct observation is the number of `error` results the run *substituted*,
which is what `errorCount` counts.

Mutant: `fatal b := if U+FFFD ∈ replacement b then none else some (replacement b)`.

Rejected by `replacement_input_example` and
`decodeWithoutBomOrFail_eq_none_iff`, whose right-hand side is
`0 < errorCount b` and not a property of the output.
Witness: `ce011_replacement_input_is_well_formed`.

## INFRA-UTF8-CE-012 — a truncated sequence emits one replacement per missing byte

`op.utf-8-decoder` [86515,90406) step 1: "If byte is end-of-queue and UTF-8
bytes needed is not 0, then set UTF-8 bytes needed to 0 and return error." One
error, once, whatever the count still outstanding. A decoder that emits one
U+FFFD per byte still needed turns the single truncated byte 0xE2 at end of
input into two replacement characters, which changes the decoded length and
therefore every offset computed from it. The pin's note ties this to Unicode's
"Best Practices for Using U+FFFD" and says no other behaviour is permitted.

Mutant: `truncPerMissingByte := true`.

Rejected by `decodeWithoutBom_truncated_one`, which is general over every proper
nonempty prefix of a scalar value's encoding, and by
`decoderHandler_endOfQueue_pending`.
Witness: `ce012_truncated_two_replacements`.

## INFRA-UTF8-CE-013 — the offending byte is consumed instead of restored

`op.utf-8-decoder` [86515,90406) step 4.2: "Restore byte to ioQueue." When a
continuation byte is out of the boundary range the decoder resets, **puts the
byte back**, and returns error; the next read sees that byte again and gives it
its own interpretation. A decoder that just drops it loses data: 0xE2 0x82 0x41
must decode to U+FFFD then U+0041, not to U+FFFD alone. This is also the reason
the restore operation exists at all, which the pin's own note calls "an internal
detail of the algorithms in this specification".

Mutant: `restoreByte := false`.

Rejected by `decoderHandler_out_of_boundary`, which names
`IoQueue.restore q b` in the returned queue, and by
`decodeWithoutBom_truncated_then_ascii_example`.
Witness: `ce013_offending_byte_restored`.

## INFRA-UTF8-CE-014 — the encoder emits a byte order mark

`op.utf-8-encoder` [90407,91744) has no step that emits a mark, and
`op.utf-8-encode` [46912,47215) has no wrapper that adds one; the pin's own
introduction [12179,13365) says the mark "not being part of the encodings
themselves". An encoder that prefixes 0xEF 0xBB 0xBF is invisible to a round
trip stated through `UTF-8 decode`, because that hook strips the mark again. It
is visible through `UTF-8 decode without BOM`, and it is visible directly in a
statement about the encoder's own output — which is why the packet freezes one.

Mutant: `encodeValueWithBom`.

Rejected by `encode_startsWith_bom_iff`, `encodeScalar_bom_iff`,
`encodeScalar_ascii` and `encodeScalar_length_one`.
Witness: `ce014_encoder_emits_bom`.

## INFRA-UTF8-CE-015 — the ISO-2022-JP profile is treated as stateless

`rule.iso-2022-jp-encoder-stateful` [123264,124113): "The ISO-2022-JP encoder is
the only encoder for which the concatenation of multiple outputs can result in
an error when run through the corresponding decoder. Encoding U+00A5 (¥) gives
0x1B 0x28 0x4A 0x5C 0x1B 0x28 0x42. Doing that twice, concatenating the results,
and then decoding yields U+00A5 U+FFFD U+00A5." `op.encode-or-fail`
[51167,53203) says the caller "will have to keep an encoder instance alive" and
"invoke it again, supplying the same encoder instance". A profile that answers
from a function of the input alone, restarting per code point, is a different
byte sequence from a retained instance's answer.

No ISO-2022-JP decoder is modelled here and none is admitted by this packet; the
witness only shows the two byte sequences differ.

Mutant: `Encoder.foreign` answering without advancing its tape.

Rejected by `Encoding.Name.isStateful_iff`,
`Encoding.encodeOrFail_foreign_advances` and
`Encoding.encodeOrFail_foreign_frontier`, and consequentially by the U3 tape law
`Whatwg.Url.Boundary.EncoderTape.terminated_iff` at its Infra owner
`Encoding.EncoderTape.terminated_iff`.
Witness: `ce015_stateful_encoder_is_not_restartable`.

## INFRA-UTF8-CE-016 — `read` removes the `end-of-queue` item

`op.io-queue-read` [6610,7078) step 2 returns `end-of-queue` and step 3 removes
`ioQueue[0]` — but step 3 is only reached when step 2 did not return. A `read`
written as a pop consumes the terminator, so the second read of an immediate
queue blocks instead of answering `end-of-queue`, and `op.process-a-queue`
[14785,15508)'s `While true` never sees its `finished` result. The whole
termination argument of the decoder rests on the terminator being idempotent.

Mutant: `readPop`.

Rejected by `IoQueue.read_endOfQueue`, whose returned queue is
`Item.endOfQueue :: rest` and not `rest`, and by `processQueue_fuel_stable`,
which is false if the loop does not terminate.
Witness: `ce016_read_keeps_end_of_queue`.

## INFRA-UTF8-CE-017 — `push` appends after the `end-of-queue` item

`op.io-queue-push` [8448,9041) step 1.2: "Otherwise, insert item before the last
item in ioQueue." A `push` that always appends puts data after the terminator,
where no reader will ever see it. `op.process-an-item` [15509,17620) step 5.1
pushes `end-of-queue` to the output and step 6.2 pushes the decoded items, so
the order matters at exactly the moment the decoder finishes.

Mutant: `pushAppend`.

Rejected by `IoQueue.push_before_endOfQueue`, `IoQueue.push_append` — which is
guarded on the last item *not* being the terminator — and
`IoQueue.push_endOfQueue_idem`.
Witness: `ce017_push_before_end_of_queue`.

## INFRA-UTF8-CE-018 — an unexpected continuation byte is dropped silently

`op.utf-8-decoder` [86515,90406) step 3, switch row "Otherwise": "Return error."
Every byte from 0x80 to 0xC1 and every byte from 0xF5 up is an error when no
sequence is in progress. A decoder that skips such a byte instead of
substituting U+FFFD shortens the output silently, which is the failure mode that
makes truncation attacks invisible.

Mutant: `errorOnStrayByte := false`.

Rejected by `decodeWithoutBom_unexpected_continuation` and
`decodeWithoutBom_invalid_lead`, both general over their byte ranges, and by
`decoderHandler_lead_error`.
Witness: `ce018_stray_byte_is_an_error`.

## Not mutants

Two theorems in the witness module are the transcription itself, kept beside the
mutants so a reader can see that `spec` is the algorithm and not one more
variant: `spec_round_trips_the_pin_example` (the pin's own 💩,
`example.io-queue-restore` [9727,9981), whose four bytes are U+1F4A9's encoding)
and `spec_four_length_shape`. `ce003_006_boundaries_are_inclusive` is the same
kind of guard: it pins the four accepting extremes U+D7FF, U+10FFFF, U+0800 and
U+10000 so that a mutant cannot satisfy CE-003 through CE-006 by tightening a
boundary instead of loosening it.
