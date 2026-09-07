import Whatwg.Infra

/-!
Breaker-owned exact-signature battery for the Infra UTF-8 codec packet.

Contract: `test/contracts/infra-utf8.contract.md`.
Graph: `INFRA-PG-UTF8` (`docs/INFRA-UTF8-DAG.md`).
Source: `vendor/whatwg-encoding-67494fce/encoding.bs`, SHA-256
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`, 144,545
bytes, pinned in `SPEC-MANIFEST.md` and `docs/PROVENANCE.md` (ruling R-U1).
The Encoding Standard has no census in this repository, so every declaration
below cites its span as a `[byte-start,byte-end)` pair into those sealed bytes
together with the span's recomputed SHA-256; the contract holds the digest
table. No line number is cited anywhere.

This module freezes the interface only. The propositions live in
`WhatwgTest/Infra/Utf8Laws.lean` and their receipts in
`WhatwgTest/Infra/Utf8AxiomReport.lean`. The builder must not change, weaken,
or delete an ascription here.

The single import is intentional. `Whatwg.Infra` already owns every carrier
used below — `Byte`, `ByteSequence`, `CodePoint`, `CodeUnit`, `JsString`,
`ScalarValue`, `replacementCharacter` — so the intended red failures are
unknown declarations under `Whatwg.Infra.Item`, `Whatwg.Infra.IoQueue`,
`Whatwg.Infra.Encoding` and `Whatwg.Infra.Utf8`, never an import or toolchain
failure.

Carrier reuse (`Whatwg/AGENTS.md`): no byte, code point, code unit, string,
scalar value or byte sequence carrier is declared by this packet. The three
carriers it does add — `Item`, `IoQueue` and the encoder profile — are the
Encoding Standard's own, and neither duplicates an Infra carrier.
-/

set_option autoImplicit false


/-! ## The I/O queue

Section `terminology` [4710,12179). "An I/O queue is a type of list with items
of a particular type (i.e., bytes or scalar values). End-of-queue is a special
item that can be present in I/O queues of any type and it signifies that there
are no more items in the queue" — `type.io-queue` [5298,6609). The carrier is
therefore `List (Item α)` and not `List α`, because `end-of-queue` is an item
of the same list, not a flag beside it.

Every ascription below writes the type parameter explicitly under `@`; the
builder may declare it implicit. -/

#check (@Whatwg.Infra.Item :
  Type → Type)

#check (@Whatwg.Infra.Item.value :
  (α : Type) → α → Whatwg.Infra.Item α)

#check (@Whatwg.Infra.Item.endOfQueue :
  (α : Type) → Whatwg.Infra.Item α)

#check (@Whatwg.Infra.IoQueue :
  Type → Type)

/-! `op.io-queue-read` [6610,7078). Step 1 "wait until its size is at least 1"
is an unanswered decision, which `AGENTS.md`'s representation rules class as a
live frontier and never as an error: `none`. Step 2 returns `end-of-queue`
*without* step 3's removal, so the read is not a pop in that case; the returned
queue is the input queue. -/
#check (@Whatwg.Infra.IoQueue.read :
  (α : Type) → Whatwg.Infra.IoQueue α → Option (Whatwg.Infra.Item α × Whatwg.Infra.IoQueue α))

/-! `op.io-queue-read-items` [7079,7650): "Perform the following step number
times … Remove end-of-queue from readItems". -/
#check (@Whatwg.Infra.IoQueue.readItems :
  (α : Type) → Whatwg.Infra.IoQueue α → Nat →
    Option (List α × Whatwg.Infra.IoQueue α))

/-! `op.io-queue-peek` [7651,8447), transcribed literally: "For each n in the
range 1 to number, inclusive: If ioQueue[n] is end-of-queue, break. Otherwise,
append ioQueue[n] to prefix." Infra's indexing syntax is zero-based
(`vendor/whatwg-infra-3f984adc/infra.bs` [67300,67450)), and Infra's "the range
1 to number, inclusive" is the set {1,…,number}, so the literal reading skips
`ioQueue[0]`. Ruling request INFRA-R15 in the contract. -/
#check (@Whatwg.Infra.IoQueue.peek :
  (α : Type) → Whatwg.Infra.IoQueue α → Nat → List α)

/-! The zero-based reading of the same step, `ioQueue[0]` through
`ioQueue[number − 1]`. This is the reading `op.utf-8-decode` [45059,45762) step
2 needs for its byte-order-mark test to be a byte-order-mark test at all, and
the one INFRA-R15 asks the operator to ratify. Both are frozen so the
difference is a theorem and not a silent choice. -/
#check (@Whatwg.Infra.IoQueue.peekPrefix :
  (α : Type) → Whatwg.Infra.IoQueue α → Nat → List α)

/-! `op.io-queue-push` [8448,9041): insert before a trailing `end-of-queue`,
append otherwise, and do nothing when both are `end-of-queue`. -/
#check (@Whatwg.Infra.IoQueue.push :
  (α : Type) → Whatwg.Infra.IoQueue α → Whatwg.Infra.Item α → Whatwg.Infra.IoQueue α)

/-! `op.io-queue-push-items` [9042,9270): "push each item in the sequence to
ioQueue, in the given order". -/
#check (@Whatwg.Infra.IoQueue.pushItems :
  (α : Type) → Whatwg.Infra.IoQueue α → List (Whatwg.Infra.Item α) →
    Whatwg.Infra.IoQueue α)

/-! `op.io-queue-restore` [9271,9726): "To restore an item other than
end-of-queue to an I/O queue, perform the list prepend operation." The
restriction is carried by the argument type `α`, which cannot be
`end-of-queue`; the assertion is discharged by typing (INFRA-R3). -/
#check (@Whatwg.Infra.IoQueue.restore :
  (α : Type) → Whatwg.Infra.IoQueue α → α → Whatwg.Infra.IoQueue α)

#check (@Whatwg.Infra.IoQueue.restoreItems :
  (α : Type) → Whatwg.Infra.IoQueue α → List α → Whatwg.Infra.IoQueue α)

/-! `op.from-io-queue-convert` [9982,10285): "return the result of reading an
indefinite number of items from ioQueue". -/
#check (@Whatwg.Infra.IoQueue.convertFrom :
  (α : Type) → Whatwg.Infra.IoQueue α → List α)

/-! `op.to-io-queue-convert` [10286,10769): "Return an I/O queue containing the
items in input, in order, followed by end-of-queue." Its step 1 assertion,
"input is not a list or it does not contain end-of-queue", is discharged by
typing: the argument is a `List α`, not a `List (Item α)`. -/
#check (@Whatwg.Infra.IoQueue.convertTo :
  (α : Type) → List α → Whatwg.Infra.IoQueue α)

/-! The decidable predicate the note of `op.io-queue-read` and the assertion of
`op.to-io-queue-convert` [10286,10769) speak about: "Immediate queues have
end-of-queue as their last item, whereas streaming queues need not have it". -/
#check (@Whatwg.Infra.IoQueue.containsEndOfQueue :
  (α : Type) → Whatwg.Infra.IoQueue α → Bool)


/-! ## Encoders, decoders and their handler results

`rule.encoders-and-decoders` [13366,14779): "A handler algorithm takes an input
I/O queue and an item, and returns finished, one or more items, error
optionally with a code point, or continue." -/

#check (@Whatwg.Infra.Encoding.HandlerResult :
  Type → Type)

#check (@Whatwg.Infra.Encoding.HandlerResult.finished :
  (α : Type) → Whatwg.Infra.Encoding.HandlerResult α)

/-! "one or more items". The nonemptiness is the text's own wording and is
carried by the laws, not by the carrier: `op.process-an-item` [15509,17620)
step 6 pushes the whole list and never inspects its length. -/
#check (@Whatwg.Infra.Encoding.HandlerResult.items :
  (α : Type) → List α → Whatwg.Infra.Encoding.HandlerResult α)

/-! "error optionally with a code point". The code point is read only by the
"html" error mode of `op.process-an-item` [15509,17620) and by step 3 of
`op.encode-or-fail` [51167,53203); the UTF-8 decoder never supplies one. -/
#check (@Whatwg.Infra.Encoding.HandlerResult.error :
  (α : Type) → Option Whatwg.Infra.CodePoint → Whatwg.Infra.Encoding.HandlerResult α)

/-! The text's `continue`. `continue` is a Lean keyword, so the constructor is
spelled `continues`; the contract records the rename. -/
#check (@Whatwg.Infra.Encoding.HandlerResult.continues :
  (α : Type) → Whatwg.Infra.Encoding.HandlerResult α)

/-! `rule.encoders-and-decoders` [13366,14779): "An error mode as used below is
`replacement` or `fatal` for a decoder". The encoder's two modes, `fatal` and
`html`, are not declared: `html` is reachable only through the legacy
`op.encode` [50170,50822) hook, which this packet does not own, and
`op.encode-or-fail` [51167,53203) fixes `fatal`. -/
#check (@Whatwg.Infra.Encoding.DecoderErrorMode :
  Type)

#check (@Whatwg.Infra.Encoding.DecoderErrorMode.replacement :
  Whatwg.Infra.Encoding.DecoderErrorMode)

#check (@Whatwg.Infra.Encoding.DecoderErrorMode.fatal :
  Whatwg.Infra.Encoding.DecoderErrorMode)


/-! ## The encoding name and the encoder profile (DB-02)

An encoding "defines a mapping from a scalar value sequence to a byte sequence
(and vice versa). Each encoding has a name, and one or more labels"
(`[12179,13365)`). This packet owns exactly one encoder, UTF-8's. Every other
name is a foreign boundary whose answers are first-order data on a tape, never
a modelled body (DB-02). The three names `get an encoder` refuses —
`op.get-an-encoder` [50829,51166) step 1, "Assert: encoding is not replacement
or UTF-16BE/LE" — are distinguished so the assertion is statable. -/

#check (@Whatwg.Infra.Encoding.Name :
  Type)

#check (@Whatwg.Infra.Encoding.Name.utf8 :
  Whatwg.Infra.Encoding.Name)

#check (@Whatwg.Infra.Encoding.Name.replacement :
  Whatwg.Infra.Encoding.Name)

#check (@Whatwg.Infra.Encoding.Name.utf16be :
  Whatwg.Infra.Encoding.Name)

#check (@Whatwg.Infra.Encoding.Name.utf16le :
  Whatwg.Infra.Encoding.Name)

/-! The one encoder the pin names as stateful; see
`rule.iso-2022-jp-encoder-stateful` [123264,124113). -/
#check (@Whatwg.Infra.Encoding.Name.iso2022jp :
  Whatwg.Infra.Encoding.Name)

/-! Any other encoding, carried by its `name` [12179,13365). -/
#check (@Whatwg.Infra.Encoding.Name.other :
  Whatwg.Infra.JsString → Whatwg.Infra.Encoding.Name)

/-! `op.get-an-encoder` [50829,51166) step 1 as a decidable predicate, and the
note of `rule.encoders-and-decoders` [13366,14779): "The replacement and
UTF-16BE/LE encodings have no encoder." -/
#check (@Whatwg.Infra.Encoding.Name.hasEncoder :
  Whatwg.Infra.Encoding.Name → Bool)

/-! Whether the encoder instance carries state across `encode or fail` calls.
`rule.iso-2022-jp-encoder-stateful` [123264,124113): "ISO-2022-JP's encoder has
an associated ISO-2022-JP encoder state which is ASCII, Roman, or jis0208,
initially ASCII", and "The ISO-2022-JP encoder is the only encoder for which
the concatenation of multiple outputs can result in an error when run through
the corresponding decoder." -/
#check (@Whatwg.Infra.Encoding.Name.isStateful :
  Whatwg.Infra.Encoding.Name → Bool)

/-! Whether this repository owns the encoder algorithm for the name, as opposed
to holding a DB-02 profile for it. Exactly `utf8` today. -/
#check (@Whatwg.Infra.Encoding.Name.isOwned :
  Whatwg.Infra.Encoding.Name → Bool)

/-! One answer of `op.encode-or-fail` [51167,53203) as its caller consumes it:
the bytes pushed into `output` during the call, and the returned value, "either
the number representing the code point that could not be encoded or null, if
there was no error". Structurally the shape
`Whatwg.Url.Boundary.EncodeAnswer` already carries on `url/u3-builder`; the
contract records that the URL copy becomes a view onto this owner. -/
#check (@Whatwg.Infra.Encoding.EncodeAnswer :
  Type)

#check (@Whatwg.Infra.Encoding.EncodeAnswer.mk :
  Whatwg.Infra.ByteSequence → Option Nat → Whatwg.Infra.Encoding.EncodeAnswer)

#check (@Whatwg.Infra.Encoding.EncodeAnswer.output :
  Whatwg.Infra.Encoding.EncodeAnswer → Whatwg.Infra.ByteSequence)

#check (@Whatwg.Infra.Encoding.EncodeAnswer.potentialError :
  Whatwg.Infra.Encoding.EncodeAnswer → Option Nat)

/-! The run of a retained foreign encoder instance: "When it returns non-null
the caller will have to invoke it again, supplying the same encoder instance
and a new output I/O queue", `op.encode-or-fail` [51167,53203). A short or
empty tape is an unanswered decision and therefore a live frontier. -/
#check (@Whatwg.Infra.Encoding.EncoderTape :
  Type)

#check (@Whatwg.Infra.Encoding.EncoderTape.terminated :
  Whatwg.Infra.Encoding.EncoderTape → Bool)

/-! The instance `op.get-an-encoder` [50829,51166) step 2 returns: "an instance
of encoding's encoder". For UTF-8 it is the owned handler and carries no state;
for every other name it is a DB-02 profile carrying the answers it will give. -/
#check (@Whatwg.Infra.Encoding.Encoder :
  Type)

#check (@Whatwg.Infra.Encoding.Encoder.utf8 :
  Whatwg.Infra.Encoding.Encoder)

#check (@Whatwg.Infra.Encoding.Encoder.foreign :
  Whatwg.Infra.Encoding.Name → Whatwg.Infra.Encoding.EncoderTape →
    Whatwg.Infra.Encoding.Encoder)

#check (@Whatwg.Infra.Encoding.Encoder.name :
  Whatwg.Infra.Encoding.Encoder → Whatwg.Infra.Encoding.Name)

/-! `op.get-an-encoder` [50829,51166) with its assertion as a hypothesis
argument (INFRA-R3), and with the assertion decided at run time. -/
#check (@Whatwg.Infra.Encoding.getAnEncoder :
  (name : Whatwg.Infra.Encoding.Name) →
    Whatwg.Infra.Encoding.Name.hasEncoder name = true → Whatwg.Infra.Encoding.Encoder)

#check (@Whatwg.Infra.Encoding.getAnEncoder? :
  Whatwg.Infra.Encoding.Name → Option Whatwg.Infra.Encoding.Encoder)

/-! `op.encode-or-fail` [51167,53203). The encoder instance is retained across
the call and returned, which is exactly what makes ISO-2022-JP's statefulness
observable. `none` is an unanswered decision on a foreign profile's exhausted
tape: a live frontier, never an error. -/
#check (@Whatwg.Infra.Encoding.encodeOrFail :
  Whatwg.Infra.Encoding.Encoder → Whatwg.Infra.IoQueue Whatwg.Infra.ScalarValue →
    Option (Whatwg.Infra.Encoding.EncodeAnswer × Whatwg.Infra.Encoding.Encoder))


/-! ## The UTF-8 decoder

`op.utf-8-decoder` [86515,90406). "UTF-8's decoder has an associated UTF-8 code
point, UTF-8 bytes seen, UTF-8 bytes needed — each a number, initially 0; UTF-8
lower boundary — a byte, initially 0x80; UTF-8 upper boundary — a byte,
initially 0xBF." -/

#check (@Whatwg.Infra.Utf8.DecoderState :
  Type)

#check (@Whatwg.Infra.Utf8.DecoderState.mk :
  Nat → Nat → Nat → Whatwg.Infra.Byte → Whatwg.Infra.Byte →
    Whatwg.Infra.Utf8.DecoderState)

#check (@Whatwg.Infra.Utf8.DecoderState.codePoint :
  Whatwg.Infra.Utf8.DecoderState → Nat)

#check (@Whatwg.Infra.Utf8.DecoderState.bytesSeen :
  Whatwg.Infra.Utf8.DecoderState → Nat)

#check (@Whatwg.Infra.Utf8.DecoderState.bytesNeeded :
  Whatwg.Infra.Utf8.DecoderState → Nat)

#check (@Whatwg.Infra.Utf8.DecoderState.lowerBoundary :
  Whatwg.Infra.Utf8.DecoderState → Whatwg.Infra.Byte)

#check (@Whatwg.Infra.Utf8.DecoderState.upperBoundary :
  Whatwg.Infra.Utf8.DecoderState → Whatwg.Infra.Byte)

#check (@Whatwg.Infra.Utf8.DecoderState.initial :
  Whatwg.Infra.Utf8.DecoderState)

/-! "UTF-8's decoder's handler, given ioQueue and byte, runs these steps",
`op.utf-8-decoder` [86515,90406), steps 1 to 11. The handler returns the
possibly-modified input queue because step 4.2 restores the byte to it. Its
item type is `CodePoint` and not `ScalarValue`: step 11 returns "a code point
whose value is codePoint", and that the value is never a surrogate is a
theorem of the boundary tables, not a typing assumption. -/
#check (@Whatwg.Infra.Utf8.decoderHandler :
  Whatwg.Infra.Utf8.DecoderState → Whatwg.Infra.IoQueue Whatwg.Infra.Byte →
    Whatwg.Infra.Item Whatwg.Infra.Byte →
      Whatwg.Infra.Encoding.HandlerResult Whatwg.Infra.CodePoint ×
        Whatwg.Infra.Utf8.DecoderState × Whatwg.Infra.IoQueue Whatwg.Infra.Byte)

/-! `op.process-an-item` [15509,17620) specialized to UTF-8's decoder: the three
assertions of steps 1 to 3 hold by construction (the mode is a
`DecoderErrorMode`, so it is never "html"; the instance is a decoder, so it is
never asked for "replacement" as an encoder; the surrogate assertion is an
encoder-side assertion), step 5 pushes `end-of-queue`, step 6 pushes the items,
and step 7 switches on the mode. -/
#check (@Whatwg.Infra.Utf8.processItem :
  Whatwg.Infra.Encoding.DecoderErrorMode → Whatwg.Infra.Utf8.DecoderState →
    Whatwg.Infra.IoQueue Whatwg.Infra.Byte → Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint →
      Whatwg.Infra.Item Whatwg.Infra.Byte →
        Whatwg.Infra.Encoding.HandlerResult Whatwg.Infra.CodePoint ×
          Whatwg.Infra.Utf8.DecoderState × Whatwg.Infra.IoQueue Whatwg.Infra.Byte ×
            Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint)

/-! `op.process-a-queue` [14785,15508): "While true: Let result be the result of
processing an item with the result of reading from input …; If result is not
continue, then return result." The `While true` is fuel-bounded exactly as
`Whatwg.Infra.ByteSequence.isPrefixLoop` is, and the first component is `none`
when the fuel runs out, which is a live frontier and never an error
(`AGENTS.md`, representation rules; DB-07). -/
#check (@Whatwg.Infra.Utf8.processQueue :
  Whatwg.Infra.Encoding.DecoderErrorMode → Whatwg.Infra.Utf8.DecoderState →
    Whatwg.Infra.IoQueue Whatwg.Infra.Byte → Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint →
      Nat →
        Option (Whatwg.Infra.Encoding.HandlerResult Whatwg.Infra.CodePoint) ×
          Whatwg.Infra.Utf8.DecoderState × Whatwg.Infra.IoQueue Whatwg.Infra.Byte ×
            Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint)

/-! The fuel that always suffices. Step 4.2 of `op.utf-8-decoder`
[86515,90406) restores a byte, so the queue's length alone is not a decreasing
measure; `2 * length + 1` is, because a restore happens only together with a
reset of `UTF-8 bytes needed` to 0 and the restored byte is then consumed by the
`bytesNeeded = 0` branch, which never restores. -/
#check (@Whatwg.Infra.Utf8.processQueueFuel :
  Whatwg.Infra.IoQueue Whatwg.Infra.Byte → Nat)


/-! ## The four hooks for standards

`note.hooks-for-standards` [43782,45058): "The algorithms defined below (UTF-8
decode, UTF-8 decode without BOM, UTF-8 decode without BOM or fail, and UTF-8
encode) are intended for usage by other standards." -/

/-! `op.utf-8-decode` [45059,45762). -/
#check (@Whatwg.Infra.Utf8.decodeQueue :
  Whatwg.Infra.IoQueue Whatwg.Infra.Byte → Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint)

/-! `op.utf-8-decode-without-bom` [45763,46180). -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomQueue :
  Whatwg.Infra.IoQueue Whatwg.Infra.Byte → Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint)

/-! `op.utf-8-decode-without-bom-or-fail` [46181,46905). "If potentialError is
an error, then return failure": `none` (INFRA-R3). -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFailQueue :
  Whatwg.Infra.IoQueue Whatwg.Infra.Byte →
    Option (Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint))

/-! The byte-sequence faces of the same three hooks, which is the form every
caller in the URL and Infra texts actually uses: `op.percent-decode-string`
of `vendor/whatwg-url-55d66993/url.bs` [18464,18967) and
`op.parse-json-bytes-to-an-infra-value` of `vendor/whatwg-infra-3f984adc/infra.bs`
[95081,95398) both hand over a byte sequence. Each is the queue form composed
with `op.to-io-queue-convert` [10286,10769) and `op.from-io-queue-convert`
[9982,10285). -/
#check (@Whatwg.Infra.Utf8.decode :
  Whatwg.Infra.ByteSequence → List Whatwg.Infra.CodePoint)

#check (@Whatwg.Infra.Utf8.decodeWithoutBom :
  Whatwg.Infra.ByteSequence → List Whatwg.Infra.CodePoint)

#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail :
  Whatwg.Infra.ByteSequence → Option (List Whatwg.Infra.CodePoint))

/-! The `JsString` faces, through `Whatwg.Infra.JsString.ofCodePoints`. -/
#check (@Whatwg.Infra.Utf8.decodeString :
  Whatwg.Infra.ByteSequence → Whatwg.Infra.JsString)

#check (@Whatwg.Infra.Utf8.decodeWithoutBomString :
  Whatwg.Infra.ByteSequence → Whatwg.Infra.JsString)

#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFailString :
  Whatwg.Infra.ByteSequence → Option Whatwg.Infra.JsString)

/-! How many `error` results the replacement-mode run of
`op.process-a-queue` [14785,15508) substituted a U+FFFD for. This is not the
number of U+FFFD in the output: U+FFFD is itself a scalar value with a
well-formed encoding, so `decodeWithoutBom [0xEF, 0xBF, 0xBD]` contains one
U+FFFD and `errorCount` of it is 0. -/
#check (@Whatwg.Infra.Utf8.errorCount :
  Whatwg.Infra.ByteSequence → Nat)

/-! Whether the byte sequence is in the image of the UTF-8 encoder, which is
what `op.utf-8-decode-without-bom-or-fail` [46181,46905) succeeds on. -/
#check (@Whatwg.Infra.Utf8.isWellFormed :
  Whatwg.Infra.ByteSequence → Bool)

/-! The byte order mark `op.utf-8-decode` [45059,45762) step 2 tests for,
"0xEF 0xBB 0xBF". -/
#check (@Whatwg.Infra.Utf8.bom :
  Whatwg.Infra.ByteSequence)


/-! ## The UTF-8 encoder

`op.utf-8-encoder` [90407,91744). The handler's first argument is
`<var ignore>unused</var>` in the pin and is therefore not a parameter here. -/

/-! Step 3's `count`, extended to the ASCII case of step 2 with the value 0, at
which the step 4 and step 5 formulas reproduce step 2's single byte. -/
#check (@Whatwg.Infra.Utf8.encoderCount :
  Whatwg.Infra.CodePoint → Nat)

/-! Step 3's `offset`, extended to the ASCII case with the value 0x00. -/
#check (@Whatwg.Infra.Utf8.encoderOffset :
  Whatwg.Infra.CodePoint → Nat)

/-! Step 5's loop: "While count is greater than 0: Set temp to codePoint >>
(6 × (count − 1)). Append to bytes 0x80 | (temp & 0x3F). Decrease count by
one." The loop is structural in `count`, which the caller supplies as
`encoderCount`, so no fuel is needed. -/
#check (@Whatwg.Infra.Utf8.encoderTail :
  Nat → Nat → Whatwg.Infra.ByteSequence)

/-! "UTF-8's encoder's handler, given unused and codePoint", steps 1 to 6. Its
item type is `ScalarValue`: step 3 of `op.process-an-item` [15509,17620)
asserts "encoderDecoder is not an encoder instance or item is not a surrogate",
and INFRA-R3 turns that assertion into the carrier, discharged by typing. -/
#check (@Whatwg.Infra.Utf8.encoderHandler :
  Whatwg.Infra.Item Whatwg.Infra.ScalarValue →
    Whatwg.Infra.Encoding.HandlerResult Whatwg.Infra.Byte)

/-! Steps 2 to 6 as a total function from one scalar value to its bytes: the
four-length shape. -/
#check (@Whatwg.Infra.Utf8.encodeScalar :
  Whatwg.Infra.ScalarValue → Whatwg.Infra.ByteSequence)

#check (@Whatwg.Infra.Utf8.encodeScalars :
  List Whatwg.Infra.ScalarValue → Whatwg.Infra.ByteSequence)

/-! `op.utf-8-encode` [46912,47215): "return the result of encoding ioQueue with
encoding UTF-8 and output", where `op.encode` [50170,50822) gets an encoder and
processes the queue. -/
#check (@Whatwg.Infra.Utf8.encodeQueue :
  Whatwg.Infra.IoQueue Whatwg.Infra.ScalarValue → Whatwg.Infra.IoQueue Whatwg.Infra.Byte)

/-! The string form. `note.hooks-for-standards` [43782,45058): "Standards are to
ensure that the input I/O queues they pass to UTF-8 encode … are effectively
I/O queues of scalar values, i.e., they contain no surrogates." That is the
hypothesis argument, in the exact shape
`Whatwg.Infra.JsString.isomorphicEncode` already uses for its own restriction
(INFRA-R3). -/
#check (@Whatwg.Infra.Utf8.encode :
  (input : Whatwg.Infra.JsString) →
    Whatwg.Infra.JsString.isScalarValueString input = true → Whatwg.Infra.ByteSequence)

/-! `encode` with its hypothesis decided at run time, in the shape
`Whatwg.Infra.JsString.isomorphicEncode?` and `asciiEncode?` already use. -/
#check (@Whatwg.Infra.Utf8.encode? :
  Whatwg.Infra.JsString → Option Whatwg.Infra.ByteSequence)

/-! The scalar values of a scalar value string, the bridge between
`Whatwg.Infra.JsString.codePoints` and the encoder's item type. -/
#check (@Whatwg.Infra.Utf8.scalars :
  (input : Whatwg.Infra.JsString) →
    Whatwg.Infra.JsString.isScalarValueString input = true →
      List Whatwg.Infra.ScalarValue)
