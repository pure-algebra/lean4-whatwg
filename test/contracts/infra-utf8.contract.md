# Infra UTF-8 codec packet

Status: FROZEN / RED, independent breaker seat, 2026-09-07, branch
`infra/utf8-breaker` from `main` at `062655a`.

This packet gives the repository its first owner of UTF-8 encode and decode.
Ruling R-U1 (`COORDINATION.md`, 2026-09-07) opened it: the URL U3 breaker found
that `Whatwg.Infra.Text.Codec` owns only isomorphic and ASCII conversions, that
`infra.bs` defers to the Encoding Standard at every UTF-8 call site, and that no
`utf8Encode` is declared anywhere in this tree. The Encoding Standard was pinned
at the U3 freeze for exactly this packet.

The Lean batteries are the authority on names and propositions; every Lean
fragment below is a reading aid.

## Pin

| Field | Value |
| --- | --- |
| Source | `whatwg/encoding` commit `67494fceee1b95bbc87b58142fcc14e48310f257`, 2025-06-16, "Review Draft Publication: June 2025" |
| Sealed at | `vendor/whatwg-encoding-67494fce/encoding.bs` |
| Size | 144,545 bytes |
| SHA-256 | `43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad` |
| Manifest row | `generated/vendor-manifest.tsv` line for that path, unchanged by this packet |
| Authority rows | `SPEC-MANIFEST.md` "WHATWG Encoding Standard source"; `docs/PROVENANCE.md` `whatwg/encoding` row |

The whole-file digest was recomputed by this seat with .NET
`System.Security.Cryptography.SHA256` over `File.ReadAllBytes` and agrees with
both the manifest and the provenance row.

The Encoding Standard has **no census** in this repository: no
`census/encoding/`, no `generated/encoding-census.tsv`, no disposition rows, no
denominator and no numerator. Nothing in this packet is reported as coverage.
Every declaration is therefore anchored by a `[byte-start,byte-end)` span into
the sealed bytes together with that span's SHA-256, so that a later Encoding
census can join them by span. No line number is cited anywhere in this packet.

## Spans, with recomputed digests

Every digest below was recomputed by this seat from the sealed bytes with .NET
`System.Security.Cryptography.SHA256` over an explicit byte slice
`bytes[start .. end-1]`. Each span begins at the opening `<` of its block or
paragraph and ends after the newline that follows its closing tag, except the
three section rows, which run heading to heading.

Row ids are this packet's, not a census generator's; a later Encoding census
that keys on `<dfn export …>` the way `census/infra/` does is expected to
produce these spans, and any disagreement is a finding against the generator or
against this table, not a silent re-anchor.

### Section `terminology` [4710,12179), SHA-256 `72597cf942fec4271566d46aee04b9a2ca34c9ad9b222ef1fe82345b6cd254bd`

| Row id | Span | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `type.io-queue` | [5298,6609) | 1311 | `9cd0d416170082e8e8107fc0fdff3197d83836c6c33fb4b80d91324d008fabab` |
| `op.io-queue-read` | [6610,7078) | 468 | `480e7b46cee256258dea5e42a8795381fde9801ad39bf6c1d429514e671dafb3` |
| `op.io-queue-read-items` | [7079,7650) | 571 | `7125981956fad8e645ab082eb3c9463ac2767a554c8adda2450b4da734d1cf89` |
| `op.io-queue-peek` | [7651,8447) | 796 | `96d14ab43ad476c0c1c6c48076acc394bef0cb8b529583490c828fb63171af66` |
| `op.io-queue-push` | [8448,9041) | 593 | `687c17a075ee9486c29d19bdd588a0a5b718dec6c3f44a10e0440da186eb6d6c` |
| `op.io-queue-push-items` | [9042,9270) | 228 | `8a88caf9ab139753f6408fc4d8d3a01e3a5fdc093dd9350d669a4f6d9dd2debc` |
| `op.io-queue-restore` | [9271,9726) | 455 | `cdacf56b375040d309d17eb17ec57aaf29961d6dbff6994e1f3480c2784b0a45` |
| `example.io-queue-restore` | [9727,9981) | 254 | `79064942cb2aa294367a8b7cc7882ddd0b21829e786de9bf99d3d2ee5bd20f3d` |
| `op.from-io-queue-convert` | [9982,10285) | 303 | `3674840845a16126bd8c21d29e9d5b9b39ced74a6004734153383eceb0f7207f` |
| `op.to-io-queue-convert` | [10286,10769) | 483 | `704fc709a7ea639bd6dde388ff31ae3143197bebeb79c3becd0d676decc5d81c` |
| `op.scalar-value-from-surrogates` | [11409,11712) | 303 | `fbcce7d096f4b5a88d8a9f37d794a019cf72b658f20249b5bb58eb884cb5baa8` |

### Section `encodings` — the encoder/decoder vocabulary

| Row id | Span | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `rule.encoders-and-decoders` | [13366,14779) | 1413 | `6d90a844904e4911440a470b8c970dbf1097b0c28d542cf90698b53dc8d01a4f` |
| `op.process-a-queue` | [14785,15508) | 723 | `4025bb2135b3f424b62c265a3e07bb0d96ae341501f758055192c71cda843ce3` |
| `op.process-an-item` | [15509,17620) | 2111 | `7131bccacd9c20cbfa60a7ca5796205787ecc0c1a79d60e28eeec3ae14d08851` |

### Section `specification-hooks` [43782,53206), SHA-256 `2134431221dfa7dde2e1136fbc6338145bbbdadb4738042b9ee57722342c704c`

| Row id | Span | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `note.hooks-for-standards` | [43782,45058) | 1276 | `276ce2d78f278df9a100ad254f482e9791a66aeee74aec41c4bc2923202952a7` |
| `op.utf-8-decode` | [45059,45762) | 703 | `4143e0ffb36daea30b24fd3e90a574a0a4e2025a7367eea4cca34aac82f9e9f4` |
| `op.utf-8-decode-without-bom` | [45763,46180) | 417 | `278a469c693ad299446bdef8ee49c069c3e6271788f7a81863e5d9a322164c9c` |
| `op.utf-8-decode-without-bom-or-fail` | [46181,46905) | 724 | `7d53beab92ccd1bb6bef68728c1a9ea7a08ed68b1af0b29f3abf33b5ed5ec426` |
| `op.utf-8-encode` | [46912,47215) | 303 | `47e428dc21403bb3b23e06ff2d32153dec5c990b1bfca3757b62acdad417711b` |
| `op.encode` | [50170,50822) | 652 | `ab4e914ee0fbbb0cda597f539213de437eb26aa72eb9e15aa7b85e7f587d46d5` |
| `op.get-an-encoder` | [50829,51166) | 337 | `8bf32b8213a61a1080768d4cafea2da6f5d413d9f60d5d88113c0a6a430c79aa` |
| `op.encode-or-fail` | [51167,53203) | 2036 | `6bdff2bb587e37dd433c7823934f880626979ea67e28d007528e252927a891c4` |

### Section `the-encoding` [86440,91744), SHA-256 `d59dfb33019c1788c06f5c1c6a75c6ce15b62ab5af06b571d582c580109383ea`

| Row id | Span | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `op.utf-8-decoder` | [86515,90406) | 3891 | `7a2f860a829aae4a0917bff78cbf4a35794f9e6edd9a77945d47300032cd3b72` |
| `op.utf-8-encoder` | [90407,91744) | 1337 | `24b9d002af18c590a3ac2166e738709d674c61fac1056a8d48a93ebc2542ce41` |

### The one legacy encoder the packet names

| Row id | Span | Bytes | SHA-256 |
| --- | --- | --- | --- |
| `rule.iso-2022-jp-encoder-stateful` | [123264,124113) | 849 | `2e8280c2ce62126c984810354cc7f0a12f3d49366c2644370f72a0a9ef78ae50` |

That row is the `<h4 id=iso-2022-jp-encoder>` heading, the note div beginning
"The ISO-2022-JP encoder is the only encoder for which the concatenation of
multiple outputs can result in an error when run through the corresponding
decoder", its U+00A5 example, and the paragraph that declares the
`ISO-2022-JP encoder state`. It is the *only* span of the legacy multi-byte
sections this packet cites, and it carries a stated property of a foreign
profile, not an owned algorithm.

### Spans deliberately not cited

`names-and-labels` [17622,32891), `output-encodings` [32892,33349), the whole
`indexes` section [33350,43781), the whole `api` section [53206,86439), and
every legacy encoding section from [91744) on except the ISO-2022-JP row above.
The labels table, the index tables, `TextDecoder`/`TextEncoder`, the streaming
interfaces and every legacy encoder are outside this packet. `get an encoding`
and `get an output encoding` are outside it too: they turn a *label* into an
encoding and are only needed by the legacy `decode`/`encode` hooks, which this
packet does not own.

## The census join

The Encoding Standard has no census, so this packet joins to the **Infra**
census instead: `generated/infra-census.tsv`, generated from
`vendor/whatwg-infra-3f984adc/infra.bs`, SHA-256
`7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`, 176 rows.
Exactly six of those rows mention UTF-8, and their spans are into `infra.bs`:

| Infra census row | Span | Span SHA-256 | What it says about UTF-8 |
| --- | --- | --- | --- |
| `op.ascii-encode` | [56961,57243) | `9bdf92ca84d3d01df7cc26632b244c820b041ed713988dd0c8d2b47c389a67b4` | "Isomorphic encode and UTF-8 encode return the same byte sequence for `input`." |
| `op.ascii-decode` | [57245,57668) | `d3945be8b1c004bd6f1cdcb8deeff780748a62ca7a60a80a7a0839a6945193aa` | "This precondition ensures that isomorphic decode and UTF-8 decode return the same string for this input." |
| `op.parse-json-bytes-to-a-java-script-value` | [92877,93268) | `b928c736863d99527f8067afb3013398c690966b0ac1b130946d9aeccb7a6aa1` | step 1 runs UTF-8 decode on the bytes |
| `op.serialize-a-java-script-value-to-json-bytes` | [93914,94316) | `b69fb4856e389e772300bec2f21c2b6b0b6afc9cbd0ac063bf8d13791224e609` | the last step runs UTF-8 encode on the string |
| `op.parse-json-bytes-to-an-infra-value` | [95081,95398) | `0c92bf476055abdf52023420c8017bb037020f134ffe2a678dd7f05d7a19e2f1` | step 1 runs UTF-8 decode on the bytes |
| `op.serialize-an-infra-value-to-json-bytes` | [97433,97831) | `8ea09a5f15ebedc2398193e74be6fc40efdb40cc8051f9aa7b6a702e3b2eb8dc` | the last step runs UTF-8 encode on the string |

Every span and digest in that table was recomputed by this seat from the sealed
`infra.bs` bytes and agrees with `generated/infra-census.tsv`; the census column
is not repeated because the recomputation *is* the check.

Two of the six are discharged by this packet. `op.ascii-encode`'s note becomes
`Whatwg.Infra.Utf8.encode_ascii_eq_asciiEncode`; `op.ascii-decode`'s note is the
decode direction and is left open by design, because `asciiDecode` is stated on
a byte sequence and `UTF-8 decode` on an I/O queue with a byte-order-mark step,
so the honest statement is about `decodeWithoutBom` and belongs with the ASCII
row's own packet. `docs/INFRA-PROOF-PLAN.md` section 4.6 wrote that the
UTF-8-agreement note "is a theorem owed jointly with the Encoding Standard,
which is not pinned; the row stays `partial` with that bridge named until
Encoding has its own pin". The pin exists; this packet supplies the encode half.

The four JSON rows stay untouched. They are the JSON packet's (I5 of
`docs/INFRA-PROOF-PLAN.md` section 7) and they now have an owner to call
instead of a boundary.

Four further mentions of UTF-8 in `infra.bs` fall outside every census row and
are prose: [22552) and [33910) in examples, [34623) in the byte-sequences
introduction ("UTF-8 encode from Encoding is encouraged. In rare circumstances
isomorphic encode might be needed"), and [44798) in the strings introduction.
The [34623) sentence is the source of the finite probe
`Whatwg.Infra.Utf8.encode_ne_isomorphicEncode_example`.

**No file under `census/` or `generated/` is edited by this packet, and no
census row changes state.** A green battery is a set of theorems, not a coverage
state.

## Design

### INFRA-R14 — the module home (ruling request)

**Decision: a new `Whatwg/Infra/Text/Utf8.lean` that *imports*
`Whatwg.Infra.Text.Codec`, with `Whatwg/Infra.lean` gaining one import line.**

R-U1 and `SPEC-MANIFEST.md` both say "the natural home is
`Whatwg.Infra.Text.Codec`". This packet reads that as naming the lane and the
library root, not the file, and asks the operator to ratify the file split. Four
reasons.

1. **One pinned source per module.** Every module under `Whatwg/Infra/` names
   exactly one authority in its docstring, and `Text/Codec.lean`'s is
   `vendor/whatwg-infra-3f984adc/infra.bs`. This packet's semantic owner is
   `vendor/whatwg-encoding-67494fce/encoding.bs`. Putting two pins in one file
   makes "which pin owns this declaration" a reading exercise; `AGENTS.md` says
   to repair the ownership map rather than let two files — or two pins — appear
   to own the same fact.
2. **The dependency arrow has to run this way.** The ASCII-agreement law needs
   `JsString.asciiEncode?` and the two adopted Codec candidates, so UTF-8
   depends on Codec. If Codec imported Utf8 instead, the agreement law would
   have to live in Codec and Codec would acquire a dependency on the Encoding
   pin — the thing reason 1 is avoiding.
3. **Size.** The decoder state machine, the I/O queue, the profile and the four
   hooks are several times the size of Codec's four conversions; folding them in
   would bury the isomorphic and ASCII conversions this repository already
   depends on.
4. **RS-1 puts it in Stratum V.** `docs/REIFICATION-STRATEGY.md` RS-1 is titled
   "Stratum V: the value universe (Infra, Web IDL, **Encoding's scalar layer**)"
   and names round trips, canonical-form injectivity and normalization
   idempotence as its theorem shapes. That is why the codec belongs under
   `Whatwg.Infra` at all rather than under a `Whatwg.Encoding` root of the kind
   DB-11 gave ECMA-262 and Web IDL. The legacy encodings, the labels table and
   the index tables are *not* Encoding's scalar layer, and they stay out.

Namespaces inside the new module, each named for what it owns:

| Namespace | Owns | Section |
| --- | --- | --- |
| `Whatwg.Infra.Item`, `Whatwg.Infra.IoQueue` | the queue carrier and its seven operations | `terminology` |
| `Whatwg.Infra.Encoding` | handler result, decoder error mode, encoding name, encoder profile, `get an encoder`, `encode or fail` | `encodings`, `specification-hooks` |
| `Whatwg.Infra.Utf8` | the decoder state machine, the encoder, and the four hooks | `the-encoding`, `specification-hooks` |

The I/O queue does **not** get its own module today. Its only consumer in this
repository is the UTF-8 codec, and a module boundary with nothing on the other
side is a boundary that has to be justified twice. The split condition is
stated: the moment a second encoding is owned, or a second standard consumes the
queue directly, `Whatwg/Infra/Text/IoQueue.lean` is separated out and the two
namespaces move unchanged.

### INFRA-R15 — `op.io-queue-peek`'s index base (ruling request)

`op.io-queue-peek` [7651,8447) step 3 reads, verbatim:

> For each `n` in the range 1 to `number`, inclusive: If `ioQueue[n]` is
> end-of-queue, break. Otherwise, append `ioQueue[n]` to `prefix`.

Infra's indexing syntax is zero-based — `vendor/whatwg-infra-3f984adc/infra.bs`
[67159,67540): "An indexing syntax can be used by providing a zero-based index
into a list inside square brackets. The index cannot be out-of-bounds" — and
Infra's `the range n to m, inclusive` [82259,82581) "creates a new ordered set
containing all of the integers from n up to and including m". So the literal
reading is indices 1 through `number`: it skips `ioQueue[0]` and reads one past
the requested count.

The two Infra spans this ruling rests on, recomputed by this seat from
`vendor/whatwg-infra-3f984adc/infra.bs`, SHA-256
`7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`:

| What | Span | Bytes | SHA-256 | Census row |
| --- | --- | --- | --- | --- |
| the list literal and indexing notation | [67159,67540) | 381 | `eca5371c663af72ff08ee1b9e767615e9f40b03ed9b97f67aa83d8e8a7cf81d5` | none; it is notational prose and carries no `<dfn>` |
| `the range n to m, inclusive` | [82259,82581) | 322 | `7f370fadc30afecce83faac905f464646fcc55e37dd411c59fd017fb877674e4` | `op.the-range` of `generated/infra-census.tsv`, whose span and digest this seat independently reproduced |

The only consumer in this packet is `op.utf-8-decode` [45059,45762) step 1,
"Let buffer be the result of peeking three bytes from ioQueue, converted to a
byte sequence", tested in step 2 against 0xEF 0xBB 0xBF. Under the literal
reading, `UTF-8 decode` never strips a byte order mark from any input, which
contradicts the note of `op.utf-8-decoder` [86515,90406) ("A byte order mark has
priority over a label … it is not part of the UTF-8 decoder algorithm, but
rather the decode and UTF-8 decode algorithms"), the note of `op.decode`
[50170,50822), and every implementation.

**Both readings are frozen**, so the difference is a theorem and not a silent
choice:

- `IoQueue.peek` is the literal transcription;
- `IoQueue.peekPrefix` is the zero-based reading;
- `IoQueue.peek_eq_peekPrefix_tail` states exactly how they differ;
- `IoQueue.peek_bom_example` is the discriminating witness;
- `Whatwg.Infra.Utf8.decodeQueue` is stated over `peekPrefix`.

The request to the operator is to ratify the zero-based reading as an editorial
defect in the pin, keeping the literal transcription as the frozen record of
what the bytes say. If the operator rules the other way, the change is one
identifier in `decodeQueue` and the four BOM laws of section 10 of the law
battery invert; nothing else in the packet moves. `INFRA-UTF8-CE-008` is the
retained witness either way.

### The I/O queue

`type.io-queue` [5298,6609): "An I/O queue is a type of list with items of a
particular type (i.e., bytes or scalar values). End-of-queue is a special item
that can be present in I/O queues of any type." The terminator is an *item of
the same list*, not a flag beside it, so the carrier is
`IoQueue α := List (Item α)` with `Item α := value α | endOfQueue`, and not
`List α` with a Bool. Three consequences the laws pin:

- `read` on the empty queue is `none`. Step 1 says "wait until its size is at
  least 1"; an unanswered decision is a live frontier under `AGENTS.md`'s
  representation rules, never an error.
- `read` on a queue whose head is `end-of-queue` returns the terminator and
  leaves it in place: step 2 returns before step 3's removal. An immediate queue
  therefore keeps answering `end-of-queue` forever, which is what makes
  `op.process-a-queue` [14785,15508)'s `While true` terminate.
  `INFRA-UTF8-CE-016`.
- `push` inserts before a trailing terminator and appends otherwise, and pushing
  `end-of-queue` onto a terminated queue does nothing, so a queue never carries
  two terminators. `INFRA-UTF8-CE-017`.

`restore` takes an `α` and not an `Item α`, so
`op.io-queue-restore` [9271,9726)'s "an item other than end-of-queue" is
discharged by typing (INFRA-R3). `convertTo` takes a `List α` for the same
reason, discharging its step 1 assertion by typing.

`op.io-queue-read-items` [7079,7650) and `op.io-queue-peek` [7651,8447) both
"wait", so both can be unanswered; `readItems` returns `Option` and `peek`
returns the prefix that exists, because `peek`'s step 1 wait is bounded by "or
ioQueue contains end-of-queue, whichever comes first" and its loop breaks at the
terminator.

`op.scalar-value-from-surrogates` [11409,11712) is transcribed as a span
citation only and gets no declaration: `Whatwg.Infra.JsString.pairValue` already
owns that arithmetic under the Infra pin, with the same formula, and
`Whatwg/AGENTS.md` forbids a second carrier or a second owner for a fact that
already has one. The contract records the duplicate so a reader does not
re-derive it.

### The encoder

`op.utf-8-encoder` [90407,91744) is a six-step handler with no state; the pin
marks its first argument `<var ignore>unused</var>`, so the transcription drops
it. The packet freezes the algorithm in three pieces and then assembles them.

Step 3's switch supplies `count` and `offset`; the packet extends both to the
ASCII case of step 2 with `count = 0` and `offset = 0x00`, at which step 4's
`(codePoint >> (6 × count)) + offset` reproduces step 2's single byte exactly
and step 5's loop is empty. That is one function rather than a special case, and
`encodeScalar_ascii` proves the two agree. Step 5's `While count is greater than
0` is structural in `count`, which the caller supplies as `encoderCount`, so no
fuel appears anywhere in the encoder. The domain is `ScalarValue` and not
`CodePoint`: step 3 of `op.process-an-item` [15509,17620) asserts
"encoderDecoder is not an encoder instance or item is not a surrogate", and
INFRA-R3's discipline turns an assertion the carrier can express into the
carrier, discharged by typing. `INFRA-UTF8-CE-002` is the retained witness that
the algorithm alone does not reject a surrogate — it happily produces
0xED 0xA0 0x80 — so the domain is the only thing that does. The string face
takes `input.isScalarValueString = true` as a hypothesis argument, in the exact
shape `JsString.isomorphicEncode` already uses, with an `Option`-returning
`encode?` beside it, exactly as `isomorphicEncode?` and `asciiEncode?` sit
beside their restricted forms; `note.hooks-for-standards` [43782,45058) is the
text that restriction transcribes ("Standards are to ensure that the input I/O
queues they pass to UTF-8 encode … contain no surrogates"). Twelve laws fix the
shape: the four length rows of step 3's switch, the membership of the length in
`[1,2,3,4]`, non-emptiness, the lead byte's four accepted ranges — which exclude
0xC0, 0xC1 and everything from 0xF5 up, the encoder half of "no overlong form
and nothing above U+10FFFF exists" — the continuation range of every later byte,
injectivity, and the byte-order-mark characterisation
`encodeScalar s = bom ↔ s.val.val = 0xFEFF`, whose string form
`encode_startsWith_bom_iff` is the law that the encoder never manufactures a
mark (`INFRA-UTF8-CE-014`).

### The decoder

`op.utf-8-decoder` [86515,90406) is a genuine state machine, and the packet
transcribes it as one: `DecoderState` carries the pin's five associated values
(`UTF-8 code point`, `UTF-8 bytes seen`, `UTF-8 bytes needed`, each a number
initially 0; `UTF-8 lower boundary`, a byte initially 0x80; `UTF-8 upper
boundary`, a byte initially 0xBF), and `decoderHandler` maps a state, the input
queue and one item to a `HandlerResult CodePoint`, the next state and the
possibly-modified queue — the queue is a result because step 4.2 restores the
byte to it, and that restore is the difference between one U+FFFD and two on a
truncated sequence followed by a valid byte (`INFRA-UTF8-CE-013`). The handler's
item type is `CodePoint` and not `ScalarValue` deliberately: step 11 returns "a
code point whose value is codePoint", and that the value is never a surrogate is
a *theorem* of the 0xED upper boundary, not a typing assumption, which is what
step 6.1 of `op.process-an-item` [15509,17620) asserts and what
`decoderHandler_items_isScalarValue` and
`decodeWithoutBom_all_isScalarValue` discharge. Twelve laws cover the handler
one numbered step or switch row at a time, including the two boundary tables
verbatim — 0xE0 installs lower 0xA0, 0xED installs upper 0x9F, 0xF0 installs
lower 0x90, 0xF4 installs upper 0x8F — each of which is separately attacked off
by one (`INFRA-UTF8-CE-003` … `006`). Above the handler, `processItem`
transcribes `op.process-an-item` [15509,17620) with the error mode as a
parameter and `processQueue` transcribes `op.process-a-queue` [14785,15508)'s
`While true` as fuel-bounded recursion in the repository's established idiom
(`Whatwg.Infra.ByteSequence.isPrefixLoop`), with `none` for exhausted fuel as a
live frontier and never an error (DB-07). The fuel `2 * length + 1` is stated
and proved sufficient: the queue's length alone is not a decreasing measure
because of the restore, but a restore happens only together with the reset of
`bytes needed` to 0, and the `bytes needed = 0` branch never restores. The three
hooks sit on top unchanged — `UTF-8 decode` peeks and conditionally reads three
bytes then processes in "replacement"; `UTF-8 decode without BOM` processes in
"replacement"; `UTF-8 decode without BOM or fail` processes in "fatal" and
returns `none` for the text's "return failure" (INFRA-R3) — each with a
byte-sequence face and a `JsString` face for the callers that actually exist.

### The boundary and profile design

`op.get-an-encoder` [50829,51166) and `op.encode-or-fail` [51167,53203) are
where DB-02 applies. `Encoding.Name` distinguishes `utf8`, the three names
`get an encoder` step 1 asserts against (`replacement`, `utf16be`, `utf16le`,
which "have no encoder" per `rule.encoders-and-decoders` [13366,14779)),
`iso2022jp`, and `other` carrying a label; `hasEncoder` is that assertion as a
decidable predicate, taken as a hypothesis argument by `getAnEncoder` and
decided at run time by `getAnEncoder?`. `Encoding.Encoder` then has exactly two
shapes: `utf8`, which is the owned handler and carries no state, and
`foreign name answers`, which is a first-order tape of `EncodeAnswer` records
(`output : ByteSequence`, `potentialError : Option Nat`) — the answer shape
`op.encode-or-fail`'s caller consumes, structurally the record
`Whatwg.Url.Boundary.EncodeAnswer` already carries on `url/u3-builder`.
`encodeOrFail` returns the answer *and the encoder*, because the pin says "the
caller will have to invoke it again, supplying the same encoder instance", and a
foreign encoder's returned instance has advanced past the answer it just gave;
that advance is the whole content of `Name.isStateful`, whose only `true` is
`iso2022jp`, justified by `rule.iso-2022-jp-encoder-stateful` [123264,124113)
("ISO-2022-JP's encoder has an associated ISO-2022-JP encoder state which is
ASCII, Roman, or jis0208, initially ASCII", and "the only encoder for which the
concatenation of multiple outputs can result in an error when run through the
corresponding decoder"), with `INFRA-UTF8-CE-015` as the retained witness that a
restarted instance and a retained one produce different bytes. An exhausted tape
answers `none`: an unanswered decision, a live frontier, never an error.
`Name.isOwned` records that exactly one name has an algorithm here and every
other is a profile, so no reader can mistake a tape for a transcription; the
`html` error mode and the legacy `op.encode` [50170,50822) hook are outside the
packet for the same reason, and `EncoderErrorMode` is therefore not declared at
all.

### The U3 tapes' UTF-8 profile

`Whatwg.Infra` cannot import `Whatwg.Url`, so the discharge is stated in Infra's
own vocabulary by two theorems:

- `Utf8.u3Profile_encoderTape` — running `encode or fail` with UTF-8's encoder
  over the whole input queue gives one answer, the whole encoding, with a null
  `potentialError`, and that one-answer tape is `terminated`. This is exactly
  what `Whatwg.Url.Boundary.Utf8Encoding.tape` and its `tape_eq` assume.
- `Utf8.u3Profile_decodeOrFail` — `UTF-8 decode without BOM or fail` fails
  exactly on the byte sequences that are not well-formed. This is exactly the
  `failed` field of `Whatwg.Url.Boundary.Utf8DecodeOrFail`, as
  `requirement.percent-encoded-utf8-advice` of
  `vendor/whatwg-url-55d66993/url.bs` [16325,16862) reads it.

Plus `Encoding.Name.isStateful_iff`, which subsumes
`Whatwg.Url.Boundary.isStateful_utf8` and `isStateful_iso2022jp`, and
`Encoding.EncoderTape.terminated_iff`, which is
`Whatwg.Url.Boundary.EncoderTape.terminated_iff` at the Infra owner.

**This packet does not close the `encoding` obligation of
`docs/URL-PERCENT-ENCODING-DAG.md`.** It supplies the theorems that discharge
it. A later URL revision turns `Whatwg.Url.Boundary.Utf8Encoding` and
`Utf8DecodeOrFail` into views onto the owned codec with conversion receipts, and
*that* revision closes the edge. Saying otherwise would be closing an edge from
a different tree's theorems.

### Observation mask

None. This family is equational. DB-04's M1 and M2 are Streams' consumer
observations over decision tapes; a codec is a Stratum V deliverable and its
theorems are round trips, canonical-form injectivity and normalization
idempotence (RS-1). `docs/SPEC-COVERAGE.md`'s green criterion applies in its
"an equational family whose contract states no mask records that instead" form.
The one decision in the packet is the foreign encoder, and it appears as
first-order data on `Encoding.EncoderTape`, not as a mask.

## The four adopted Infra candidates

`test/contracts/url-percent-encoding.contract.md` recorded four facts that "do
not exist under `Whatwg/Infra/`", each proved as a private lemma in
`Whatwg/Url/PercentEncoding.lean` with nothing under `Whatwg/Infra/` changed.
This packet adopts all four with their **exact statements**, at the homes that
contract named. It is the packet that must adopt them: the ASCII-agreement law
`encode_ascii_eq_asciiEncode` is stated through `JsString.asciiEncode?`, which
is a `dite` over `isAsciiString` wrapping a `List.pmap`, and cannot be
discharged without a computed form.

| Candidate | Home | Statement |
| --- | --- | --- |
| `JsString.codePoints_of_no_lead` | `Whatwg/Infra/Text/String.lean`, beside `codePoints` | `(∀ unit ∈ input, unit.toNat < 0xD800) → codePoints input = List.map CodePoint.ofUnit input` |
| `JsString.isAsciiString_of_units` | `Whatwg/Infra/Text/String.lean` | `(∀ unit ∈ input, unit.toNat ≤ 0x7F) → isAsciiString input = true` |
| `JsString.isomorphicEncode_eq` | `Whatwg/Infra/Text/Codec.lean`, beside `isomorphicEncode` | `isomorphicEncode input h = List.map (fun c => UInt8.ofNat c.val) (codePoints input)` |
| `JsString.asciiEncode?_eq` | `Whatwg/Infra/Text/Codec.lean`, beside `asciiEncode?` | `(∀ unit ∈ input, unit.toNat ≤ 0x7F) → asciiEncode? input = some (List.map (fun unit => UInt8.ofNat unit.toNat) input)` |

The U3 builder wrote the fourth through a private `asciiBytes` abbreviation and
the third through a private generic `pmap_eq_map_of`; the adopted public
statements inline the map, and the generic `pmap` lemma stays a private helper
wherever the builder wants it. The four are ascribed in section 2 of
`WhatwgTest/Infra/Utf8Laws.lean` and appear in the axiom report with the rest.

Adopting them makes the U3 builder's private copies redundant. Removing those
copies is **not** in this packet's fence: they are inside `Whatwg/Url/`, they
are private, and `url/u3-builder` has not landed here. The follow-up is recorded
as an obligation on the `INFRA-PG-UTF8` graph's `bridges` edge.

## Frozen ascriptions

| Module | Ascriptions |
| --- | --- |
| `WhatwgTest/Infra/Utf8Contract.lean` | **80** interface `#check`s: 15 under `Whatwg.Infra.Item` and `Whatwg.Infra.IoQueue`, 31 under `Whatwg.Infra.Encoding`, 34 under `Whatwg.Infra.Utf8` |
| `WhatwgTest/Infra/Utf8Laws.lean` | **119** theorem `#check`s: 101 general laws and 18 `_example` finite probes |
| `WhatwgTest/Infra/Utf8AxiomReport.lean` | the same 119 names, in the same order, as `#print axioms` |
| `WhatwgTest/Infra/Counterexamples/Utf8.lean` | 21 finite mutant theorems for `INFRA-UTF8-CE-001`..`018`; **green from the freeze** |

The interface, in signature form. The battery is the authority; this is a
reading aid.

```lean
-- Whatwg.Infra  (section `terminology`)
Item α               : Type            -- value α | endOfQueue
IoQueue α            : Type            -- List (Item α)
IoQueue.read         : IoQueue α → Option (Item α × IoQueue α)
IoQueue.readItems    : IoQueue α → Nat → Option (List α × IoQueue α)
IoQueue.peek         : IoQueue α → Nat → List α      -- literal, 1-based (INFRA-R15)
IoQueue.peekPrefix   : IoQueue α → Nat → List α      -- zero-based (INFRA-R15)
IoQueue.push         : IoQueue α → Item α → IoQueue α
IoQueue.pushItems    : IoQueue α → List (Item α) → IoQueue α
IoQueue.restore      : IoQueue α → α → IoQueue α
IoQueue.restoreItems : IoQueue α → List α → IoQueue α
IoQueue.convertFrom  : IoQueue α → List α
IoQueue.convertTo    : List α → IoQueue α
IoQueue.containsEndOfQueue : IoQueue α → Bool

-- Whatwg.Infra.Encoding  (sections `encodings`, `specification-hooks`)
HandlerResult α      : Type            -- finished | items (List α) | error (Option CodePoint)
                                       --   | continues
DecoderErrorMode     : Type            -- replacement | fatal
Name                 : Type            -- utf8 | replacement | utf16be | utf16le | iso2022jp
                                       --   | other (label : JsString)
Name.hasEncoder      : Name → Bool
Name.isStateful      : Name → Bool
Name.isOwned         : Name → Bool
EncodeAnswer         : Type            -- output : ByteSequence, potentialError : Option Nat
EncoderTape          : Type            -- List EncodeAnswer
EncoderTape.terminated : EncoderTape → Bool
Encoder              : Type            -- utf8 | foreign (name : Name) (answers : EncoderTape)
Encoder.name         : Encoder → Name
getAnEncoder         : (n : Name) → n.hasEncoder = true → Encoder
getAnEncoder?        : Name → Option Encoder
encodeOrFail         : Encoder → IoQueue ScalarValue → Option (EncodeAnswer × Encoder)

-- Whatwg.Infra.Utf8  (sections `the-encoding`, `specification-hooks`)
DecoderState         : Type            -- codePoint bytesSeen bytesNeeded : Nat,
                                       --   lowerBoundary upperBoundary : Byte
DecoderState.initial : DecoderState
decoderHandler       : DecoderState → IoQueue Byte → Item Byte →
                         HandlerResult CodePoint × DecoderState × IoQueue Byte
processItem          : DecoderErrorMode → DecoderState → IoQueue Byte → IoQueue CodePoint →
                         Item Byte →
                         HandlerResult CodePoint × DecoderState × IoQueue Byte ×
                           IoQueue CodePoint
processQueue         : DecoderErrorMode → DecoderState → IoQueue Byte → IoQueue CodePoint →
                         Nat →
                         Option (HandlerResult CodePoint) × DecoderState × IoQueue Byte ×
                           IoQueue CodePoint
processQueueFuel     : IoQueue Byte → Nat
decodeQueue                 : IoQueue Byte → IoQueue CodePoint
decodeWithoutBomQueue       : IoQueue Byte → IoQueue CodePoint
decodeWithoutBomOrFailQueue : IoQueue Byte → Option (IoQueue CodePoint)
decode                      : ByteSequence → List CodePoint
decodeWithoutBom            : ByteSequence → List CodePoint
decodeWithoutBomOrFail      : ByteSequence → Option (List CodePoint)
decodeString                : ByteSequence → JsString
decodeWithoutBomString      : ByteSequence → JsString
decodeWithoutBomOrFailString : ByteSequence → Option JsString
errorCount           : ByteSequence → Nat
isWellFormed         : ByteSequence → Bool
bom                  : ByteSequence
encoderCount         : CodePoint → Nat
encoderOffset        : CodePoint → Nat
encoderTail          : Nat → Nat → ByteSequence
encoderHandler       : Item ScalarValue → HandlerResult Byte
encodeScalar         : ScalarValue → ByteSequence
encodeScalars        : List ScalarValue → ByteSequence
encodeQueue          : IoQueue ScalarValue → IoQueue Byte
encode               : (input : JsString) → input.isScalarValueString = true → ByteSequence
encode?              : JsString → Option ByteSequence
scalars              : (input : JsString) → input.isScalarValueString = true →
                         List ScalarValue
```

Every carrier the packet consumes is Infra's: `Byte`, `ByteSequence`,
`CodePoint`, `CodeUnit`, `JsString`, `ScalarValue`, `replacementCharacter`,
`JsString.codePoints`, `JsString.ofCodePoints`, `JsString.isScalarValueString`,
`JsString.isAsciiString`, `JsString.asciiEncode?`,
`JsString.isomorphicEncode?`, `ByteSequence.startsWith`. None is redeclared and
none is copied.

## The laws, by section of the battery

| Battery section | Rows cited | Laws |
| --- | --- | --- |
| 1. The I/O queue | `type.io-queue`, the seven `op.io-queue-*` rows, `example.io-queue-restore` | 16 |
| 2. The adopted Infra candidates | Infra `op.isomorphic-encode`, `op.ascii-encode`, `type.ascii-string` | 4 |
| 3. The UTF-8 encoder | `op.utf-8-encoder`, `op.utf-8-encode`, `op.encode`, Infra `op.ascii-encode` | 30 |
| 4. The decoder's state machine | `op.utf-8-decoder`, `op.process-an-item` | 13 |
| 5. Processing a queue | `op.process-a-queue`, `op.process-an-item` | 5 |
| 6. The three decode hooks | the three `op.utf-8-decode*` rows | 8 |
| 7. Round trips | all of the above | 6 |
| 8. The failure set | `op.utf-8-decode-without-bom-or-fail` | 4 |
| 9. The malformed classes | `op.utf-8-decoder` | 12 |
| 10. The byte order mark | `op.utf-8-decode`, `op.utf-8-decode-without-bom` | 7 |
| 11. Get an encoder, encode or fail, profiles | `op.get-an-encoder`, `op.encode-or-fail`, `rule.iso-2022-jp-encoder-stateful` | 12 |
| 12. The U3 tapes' UTF-8 profile | the two above plus URL [16325,16862) | 2 |

The eight laws the task order named, and where each lands:

1. **Encode-then-decode round trip on scalar value strings, with the two modes
   agreeing there** — `decodeWithoutBom_encode`,
   `decodeWithoutBomOrFail_encode`, `decodeWithoutBomString_encode`,
   `decodeWithoutBom_encodeScalars`, and `decodeWithoutBomOrFail_eq_some_imp`
   for the general agreement.
2. **Decode yields scalar values only** — `decodeWithoutBom_all_isScalarValue`
   and `decode_all_isScalarValue`, stated for *every* byte sequence and not only
   for well-formed ones, plus the handler-level
   `decoderHandler_items_isScalarValue`.
3. **The four-length shape and the boundary tables** — the four
   `encodeScalar_length_*` laws, `encodeScalar_length_mem`, and
   `decoderHandler_lead_three` / `decoderHandler_lead_four`, which carry the
   E0/ED/F0/F4 second-byte ranges as equations on the installed boundaries.
4. **Replacement behaviour on each malformed class** — the general
   `decodeWithoutBom_unexpected_continuation`,
   `decodeWithoutBom_invalid_lead` and `decodeWithoutBom_truncated_one`, plus
   seven finite witnesses (overlong at each of the three lengths, surrogate,
   above U+10FFFF, truncated-then-ASCII, and the two accepted boundary
   extremes).
5. **BOM stripping exactly once** — `decode_bom_prefix`, `decode_bom_once`,
   `decode_bom_twice_example`, `decode_bom_only_example`, `decode_no_bom`,
   `decode_partial_bom_example`, `decodeWithoutBom_keeps_bom_example`.
6. **The fail mode returns none exactly when the replacement mode emits U+FFFD**
   — **as literally stated this is false, and the packet corrects it.** U+FFFD
   is itself a scalar value with a well-formed encoding, so the byte sequence
   0xEF 0xBF 0xBD decodes to `[U+FFFD]` in replacement mode and *succeeds* in
   fatal mode. The observation has to be the number of `error` results the run
   *substituted*, not the output's contents. The packet therefore declares
   `Utf8.errorCount` and freezes
   `decodeWithoutBomOrFail_eq_none_iff : decodeWithoutBomOrFail b = none ↔
   0 < errorCount b`, with `errorCount_eq_zero_iff` and `isWellFormed_iff`
   pinning the failure set as the exact complement of the encoder's image, and
   `replacement_input_example` as the discriminating witness.
   `INFRA-UTF8-CE-011` retains the attack.
7. **The encoder's output is never a BOM-prefixed sequence unless the input
   starts with U+FEFF** — `encode_startsWith_bom_iff`, with the per-scalar
   `encodeScalar_bom_iff` beneath it.
8. **No mask** — recorded above and in the battery's header.

## Counterexample seeds

`test/counterexamples/infra/UTF8.md` seeds `INFRA-UTF8-CE-001` through
`INFRA-UTF8-CE-018`, all `SEEDED`. The area token is `UTF8`, following the
register's scheme for a standard other than Streams
(`<STANDARD>-<AREA>-CE-<nnn>`), alongside the existing `INFRA-SCALAR-`,
`INFRA-INTEGER-` and `INFRA-TEXT-` rows. **The coordinator owns the stable rows
in `test/counterexamples/REGISTER.md`; this seat does not edit that file.**

The executable witnesses are in `WhatwgTest/Infra/Counterexamples/Utf8.lean`,
toy models over `List Nat` with no production import, green from the freeze.

| Id | Attack |
| --- | --- |
| 001 | an overlong encoding is accepted |
| 002 | a surrogate code point is encoded |
| 003 | the 0xE0 second-byte lower boundary is off by one |
| 004 | the 0xED second-byte upper boundary is off by one |
| 005 | the 0xF0 second-byte lower boundary is off by one |
| 006 | the 0xF4 second-byte upper boundary is off by one |
| 007 | the byte order mark is stripped twice |
| 008 | the byte order mark is not stripped at all (INFRA-R15) |
| 009 | `UTF-8 decode without BOM` strips the mark |
| 010 | the fail mode returns `some` on a malformed input |
| 011 | the fail mode fails on a well-formed U+FFFD |
| 012 | a truncated sequence emits one replacement per missing byte |
| 013 | the offending byte is consumed instead of restored |
| 014 | the encoder emits a byte order mark |
| 015 | the ISO-2022-JP profile is treated as stateless |
| 016 | `read` removes the `end-of-queue` item |
| 017 | `push` appends after the `end-of-queue` item |
| 018 | an unexpected continuation byte is dropped silently |

## Acceptance conditions

1. Every one of the 80 interface ascriptions and 119 law ascriptions elaborates
   with no token of a statement changed. `git diff --ignore-all-space` for the
   three battery files is empty except for indentation repairs the
   `WhatwgTest/AGENTS.md` elaboration-repair allowance covers, and any such
   repair is recorded with before and after SHA-256.
2. All 119 receipts in the axiom report print inside the R-11 ceiling
   (`propext`, `Quot.sound`, `Classical.choice`). The **Infra lane's stricter
   local target applies**: the target ceiling is `[propext, Quot.sound]`,
   matching `docs/INFRA-SCALAR-ASSURANCE.md` and
   `docs/INFRA-INTEGER-CONSTRUCTIVE.md`, and neither of those two families may
   regress. Any receipt that reaches `Classical.choice` is reported with its
   exact dependency path and a constructive alternative attempted first. See
   "Axiom ceiling" below.
3. The twenty-one finite mutant theorems stay green and unchanged.
4. `lake --wfail build Whatwg Gates` is green and `lake build` is green with the
   three known-red entries removed.
5. `lake exe vendorseal`, `lake exe citations`, `lake exe census` (every
   registered standard), `lake exe urlinventory` and `lake exe urlcensus` pass
   with every existing projection byte-identical. **No file under `vendor/`,
   `generated/` or `census/` changes.**
6. No carrier is redeclared. `Byte`, `ByteSequence`, `CodePoint`, `CodeUnit`,
   `JsString` and `ScalarValue` keep their owners, and nothing under
   `Whatwg/Infra/Text/{CodePoint,String,Scalar,Order,Substring,Case,Whitespace,Scan}.lean`
   changes except the two additive theorems of the adopted candidates in
   `String.lean`. `Codec.lean` changes only by the two additive theorems named
   above; no existing definition body, signature or docstring in either file
   moves.
7. Nothing in this packet is reported as coverage. Encoding has no census,
   denominator, numerator or report; the six Infra rows named in "The census
   join" keep whatever state `generated/infra-census.tsv` already gives them,
   which is `absent`.
8. `docs/INFRA-UTF8-DAG.md`'s edges are updated only where evidence exists. In
   particular the `bridges` edge stays open until the URL revision that turns
   the U3 tapes into views lands, and the `coverage` edge stays open until
   Encoding has a census.
9. INFRA-R14 and INFRA-R15 are answered by the operator before the builder's
   landing is ratified. The builder may implement against the decisions recorded
   here; a different ruling on INFRA-R15 changes one identifier in
   `decodeQueue` and inverts the four BOM laws, and a different ruling on
   INFRA-R14 moves the declarations into `Whatwg/Infra/Text/Codec.lean` without
   changing one statement.

## Expected declaration delta

`Whatwg/Infra/Text/Utf8.lean` does not exist today. It gains:

- **the queue**: `Item` with two constructors, the `IoQueue` abbreviation, and
  eleven operations;
- **the vocabulary**: `Encoding.HandlerResult` with four constructors,
  `Encoding.DecoderErrorMode` with two, `Encoding.Name` with six,
  `Encoding.EncodeAnswer` with two fields, the `Encoding.EncoderTape`
  abbreviation, `Encoding.Encoder` with two constructors, and the seven
  operations over them;
- **the codec**: `Utf8.DecoderState` with five fields, and 32 operations from
  `DecoderState.initial` to `Utf8.scalars`;
- **the laws**: 115 theorems.

`Whatwg/Infra/Text/String.lean` gains **2** theorems and
`Whatwg/Infra/Text/Codec.lean` gains **2** theorems, the adopted candidates.
`Whatwg/Infra.lean` gains **one import line and no declaration**.

That is **80 frozen non-theorem declarations and 119 frozen theorems, 199 named
public declarations**, of which 195 are in one new module and four are additive
in two existing ones, from a starting point of zero UTF-8 declarations anywhere
in the tree. Derived constructors, field projections, `DecidableEq` and `Repr`
instances and equation lemmas inherit the owning row deterministically and must
still appear in the eventual generated declaration snapshot. Private helpers are
permitted and are not ascribed; the U3 builder's private `pmap_eq_map_of` is the
expected one. A module split to respect dependency direction is permitted while
the stable names and root reachability stay fixed.

No declaration is added to any other tree. `WhatwgTest.lean` gains four imports
and `test/fixtures/trust-gate/known-red.txt` three entries plus its packet note;
both are append-only for this seat, which shares them with the concurrent
promise Q4 builder and URL U3 review.

## Axiom ceiling

Target: **`propext` and `Quot.sound` only, choice-free**, for all 119 receipts.

The packet is finite, decidable and structural: `List`, `Nat`, `UInt8`,
`UInt16` and two subtypes, with no `String` anywhere. `docs/CHOICE-REMOVAL.md`
records the one confirmed path into `Classical.choice` for stock Lean 4.33.1 —
`String.toList` → `String.Internal.toArray` → `ByteArray.isSome_utf8Decode?_iff`
→ … → `Classical.propDecidable` — and **no statement in this packet mentions
`String`**. `JsString` is `List UInt16`; `JsString.ofLiteral`, `ofString` and
`toString?`, which do reach that path, are not used by any ascription here, and
the two finite probes that would naturally have been written with a string
literal (`encode_ne_isomorphicEncode_example` and `encode_astral_example`) are
written with explicit code units for exactly that reason.

Two statements are existential and are the places to look first if a receipt
does reach choice:

- `Utf8.isWellFormed_iff`, whose right-hand side is
  `∃ ss : List ScalarValue, b = encodeScalars ss`. The witness is computable
  from `b` by the decoder, so a constructive proof exists; a `Classical.choice`
  receipt here means the builder reached for `Classical.byContradiction` on the
  negative direction rather than the decision procedure.
- `Utf8.encode_decodeWithoutBom`, which recovers the encoder input from a
  well-formed byte sequence. Same argument.

`Utf8.encodeScalar_injective` is the third candidate: injectivity proved by
case analysis on the four length rows is constructive, injectivity proved by
`Function.Injective`'s classical route is not. The packet states it as
`∀ a b, encodeScalar a = encodeScalar b → a = b` rather than through
`Function.Injective` so that no library-side classical lemma is in the
statement.

A receipt that reaches `Classical.choice` is reported with its exact
`#print axioms` output and its dependency path; it does not fail the repository
ceiling (R-11 admits it) but it does fail this packet's stated target and is
recorded as debt in the graph's `trust` edge rather than being silently
accepted.

## Freeze receipt

Branch `infra/utf8-breaker` from `main` at `062655a`. Files introduced by this
packet:

- `test/contracts/infra-utf8.contract.md`
- `docs/INFRA-UTF8-DAG.md`
- `test/counterexamples/infra/UTF8.md`
- `WhatwgTest/Infra/Utf8Contract.lean`
- `WhatwgTest/Infra/Utf8Laws.lean`
- `WhatwgTest/Infra/Utf8AxiomReport.lean`
- `WhatwgTest/Infra/Counterexamples/Utf8.lean`

Shared files appended to: `WhatwgTest.lean` (four imports, inserted inside the
existing Infra block), `test/fixtures/trust-gate/known-red.txt` (three entries
plus the packet note, CRLF endings preserved as committed),
`docs/INFRA-PROOF-PLAN.md` (the "UTF-8 packet" subsection, the only plan edit).
No file under `Whatwg/`, `Gates/`, `census/`, `generated/`, `vendor/`, and no
existing contract, battery, `REGISTER.md`, `SPEC-MANIFEST.md`, `PLAN.md` or
`COORDINATION.md` is edited.

### Measured commands

All Lean commands used the pinned Lean 4.33.1 with `LEAN_NUM_THREADS=1`.

```text
lake --wfail build Whatwg Gates          -> Build completed successfully (164 jobs)
lake build WhatwgTest.Infra.Counterexamples.Utf8
                                         -> Build completed successfully (2 jobs)
lake build WhatwgTest                    -> build failed; exactly three targets red:
                                            WhatwgTest.Infra.Utf8AxiomReport
                                            WhatwgTest.Infra.Utf8Laws
                                            WhatwgTest.Infra.Utf8Contract
lake env lean -DmaxErrors=5000 WhatwgTest/Infra/Utf8Contract.lean
                                         -> 177 diagnostics, all lean.unknownIdentifier
lake env lean -DmaxErrors=5000 WhatwgTest/Infra/Utf8Laws.lean
                                         -> 405 diagnostics, all lean.unknownIdentifier
lake env lean -DmaxErrors=5000 WhatwgTest/Infra/Utf8AxiomReport.lean
                                         -> 119 diagnostics, all lean.unknownIdentifier
                                            ("Unknown constant …")
```

There is no parse, import, type-mismatch or instance-synthesis failure in any of
the three red modules, and no diagnostic at all in the witness module. Every
span digest in this document was recomputed from the sealed bytes by this seat.
