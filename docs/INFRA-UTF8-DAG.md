# Infra UTF-8 codec proof graph (`INFRA-PG-UTF8`)

Breaker-authored 2026-09-07 on `infra/utf8-breaker`, base `062655a`. Contract:
`test/contracts/infra-utf8.contract.md`. Attacks:
`test/counterexamples/infra/UTF8.md`. This file owns the declaration roles,
existing-type dispositions, anchor map, and graph edges for the repository's
first owner of UTF-8 encode and decode. It owns no coverage count.

Ruling R-U1 (`COORDINATION.md`, 2026-09-07) opened the packet and pinned the
Encoding Standard for it. `docs/INFRA-PROOF-PLAN.md` section 5 already listed
`INFRA-PG-TEXT`, `INFRA-PG-DATA`, `INFRA-PG-BASE64` and `INFRA-PG-JSON` and
predicted that "`bridges` on `INFRA-PG-TEXT` [stays open] until Encoding is
pinned (the UTF-8 agreement note)". This is a **fifth** graph rather than a
sixth family of `INFRA-PG-TEXT`, for the same reason the declarations get their
own module: a different pinned source is the semantic owner, and a graph whose
`identity` edge spans two pins cannot say which pin an edge closed against.
`INFRA-PG-TEXT`'s `bridges` edge is closed *against* this graph by the single
theorem `Whatwg.Infra.Utf8.encode_ascii_eq_asciiEncode`; nothing else moves
between them.

## Authority anchors

Every row below is a byte-span SHA-256 recomputed by the breaker seat from
`vendor/whatwg-encoding-67494fce/encoding.bs`, SHA-256
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`, 144,545
bytes, at commit `67494fceee1b95bbc87b58142fcc14e48310f257`. The Encoding
Standard has no census in this repository, so a span is the anchor and there is
no row id to defer to; the contract's span table is the same list with the
section groupings. Short aliases used in the declaration table expand to this
table, not to a second semantic owner. No line number is cited.

| Alias | Algorithm or definition | Span | Span digest |
| --- | --- | --- | --- |
| QUEUE | I/O queue, end-of-queue | [5298,6609) | `9cd0d416170082e8e8107fc0fdff3197d83836c6c33fb4b80d91324d008fabab` |
| READ | I/O queue / read | [6610,7078) | `480e7b46cee256258dea5e42a8795381fde9801ad39bf6c1d429514e671dafb3` |
| READN | I/O queue / read items | [7079,7650) | `7125981956fad8e645ab082eb3c9463ac2767a554c8adda2450b4da734d1cf89` |
| PEEK | I/O queue / peek | [7651,8447) | `96d14ab43ad476c0c1c6c48076acc394bef0cb8b529583490c828fb63171af66` |
| PUSH | I/O queue / push | [8448,9041) | `687c17a075ee9486c29d19bdd588a0a5b718dec6c3f44a10e0440da186eb6d6c` |
| PUSHN | I/O queue / push items | [9042,9270) | `8a88caf9ab139753f6408fc4d8d3a01e3a5fdc093dd9350d669a4f6d9dd2debc` |
| RESTORE | I/O queue / restore | [9271,9726) | `cdacf56b375040d309d17eb17ec57aaf29961d6dbff6994e1f3480c2784b0a45` |
| FROMQ | from I/O queue / convert | [9982,10285) | `3674840845a16126bd8c21d29e9d5b9b39ced74a6004734153383eceb0f7207f` |
| TOQ | to I/O queue / convert | [10286,10769) | `704fc709a7ea639bd6dde388ff31ae3143197bebeb79c3becd0d676decc5d81c` |
| VOCAB | decoder, encoder, handler, error mode | [13366,14779) | `6d90a844904e4911440a470b8c970dbf1097b0c28d542cf90698b53dc8d01a4f` |
| PROCQ | process a queue | [14785,15508) | `4025bb2135b3f424b62c265a3e07bb0d96ae341501f758055192c71cda843ce3` |
| PROCI | process an item | [15509,17620) | `7131bccacd9c20cbfa60a7ca5796205787ecc0c1a79d60e28eeec3ae14d08851` |
| HOOKS | the note that names the four hooks | [43782,45058) | `276ce2d78f278df9a100ad254f482e9791a66aeee74aec41c4bc2923202952a7` |
| DECODE | UTF-8 decode | [45059,45762) | `4143e0ffb36daea30b24fd3e90a574a0a4e2025a7367eea4cca34aac82f9e9f4` |
| NOBOM | UTF-8 decode without BOM | [45763,46180) | `278a469c693ad299446bdef8ee49c069c3e6271788f7a81863e5d9a322164c9c` |
| ORFAIL | UTF-8 decode without BOM or fail | [46181,46905) | `7d53beab92ccd1bb6bef68728c1a9ea7a08ed68b1af0b29f3abf33b5ed5ec426` |
| ENCODE | UTF-8 encode | [46912,47215) | `47e428dc21403bb3b23e06ff2d32153dec5c990b1bfca3757b62acdad417711b` |
| LEGACY | encode (the legacy hook) | [50170,50822) | `ab4e914ee0fbbb0cda597f539213de437eb26aa72eb9e15aa7b85e7f587d46d5` |
| GETENC | get an encoder | [50829,51166) | `8bf32b8213a61a1080768d4cafea2da6f5d413d9f60d5d88113c0a6a430c79aa` |
| ORFAILENC | encode or fail | [51167,53203) | `6bdff2bb587e37dd433c7823934f880626979ea67e28d007528e252927a891c4` |
| DECODER | UTF-8 decoder | [86515,90406) | `7a2f860a829aae4a0917bff78cbf4a35794f9e6edd9a77945d47300032cd3b72` |
| ENCODER | UTF-8 encoder | [90407,91744) | `24b9d002af18c590a3ac2166e738709d674c61fac1056a8d48a93ebc2542ce41` |
| ISO2022 | ISO-2022-JP encoder statefulness | [123264,124113) | `2e8280c2ce62126c984810354cc7f0a12f3d49366c2644370f72a0a9ef78ae50` |

Two anchors are into the **Infra** pin,
`vendor/whatwg-infra-3f984adc/infra.bs`, SHA-256
`7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`:

| Alias | Row of `generated/infra-census.tsv` | Span | Span digest |
| --- | --- | --- | --- |
| ASCIIENC | `op.ascii-encode` | [56961,57243) | `9bdf92ca84d3d01df7cc26632b244c820b041ed713988dd0c8d2b47c389a67b4` |
| ASCIIDEC | `op.ascii-decode` | [57245,57668) | `d3945be8b1c004bd6f1cdcb8deeff780748a62ca7a60a80a7a0839a6945193aa` |

## Declaration and existing-type records

All names below are relative to `Whatwg.Infra`. The owner of the packet is the
Infra UTF-8 builder after this breaker freezes it; the breaker owns its
statements. Constructors, projections, derived instances, equation lemmas and
the battery's named theorems inherit their owning row deterministically, and
every inherited declaration must still appear in the future generated
declaration snapshot. The route for every row is `INFRA-PG-UTF8`, with the
contributing edge named below. No separately allocated leaf graph is needed:
the decoder is a state machine with transition laws, which
`docs/AGENT-ROUTING.md` puts on the graph route by itself.

| Stable declaration family | Module | Relationship and existing owner | Disposition / anchor | Edge |
| --- | --- | --- | --- | --- |
| `Item`, `.value`, `.endOfQueue`, `IoQueue` | `Text/Utf8.lean` (new) | the Encoding Standard's own container; **not** a second `ByteSequence` or `JsString`, and not Infra's `queue` convention, because `end-of-queue` is an item of the list and `restore` is a prepend the Infra queue does not have | `owned`; QUEUE | identity |
| `IoQueue.read`, `.readItems`, `.peek`, `.peekPrefix`, `.push`, `.pushItems`, `.restore`, `.restoreItems`, `.convertFrom`, `.convertTo`, `.containsEndOfQueue` | `Text/Utf8.lean` | the seven numbered algorithms of section `terminology`, transcribed step for step; `peek` and `peekPrefix` are the two readings of INFRA-R15 | `owned`; READ, READN, PEEK, PUSH, PUSHN, RESTORE, FROMQ, TOQ | construction, laws |
| `Encoding.HandlerResult`, `Encoding.DecoderErrorMode` | `Text/Utf8.lean` | the four handler answers and the decoder's two error modes; the encoder's `html` mode is not declared because the legacy `encode` hook is not owned | `owned` for the decoder modes, `foreignBoundary` for the unmodelled `html` arm; VOCAB, PROCI | identity |
| `Encoding.Name`, `.hasEncoder`, `.isStateful`, `.isOwned` | `Text/Utf8.lean` | the encoding's `name`, with the three encoder-less names distinguished so GETENC's assertion is statable; `other` carries a `JsString` label and reuses Infra's string carrier | `owned` for `utf8`, `foreignBoundary` for every other constructor; GETENC, VOCAB, ISO2022 | representation |
| `Encoding.EncodeAnswer`, `EncoderTape`, `.terminated` | `Text/Utf8.lean` | DB-02 answer shape for a retained foreign encoder; structurally the record `Whatwg.Url.Boundary.EncodeAnswer` carries on `url/u3-builder`, which becomes a view onto this owner | `foreignBoundary`; ORFAILENC | representation |
| `Encoding.Encoder`, `.name`, `getAnEncoder`, `getAnEncoder?`, `encodeOrFail` | `Text/Utf8.lean` | the instance GETENC returns and the call ORFAILENC makes; the instance is returned as well as the answer, which is what makes ISO-2022-JP's state observable | `owned` for `Encoder.utf8`, `foreignBoundary` for `Encoder.foreign`; GETENC, ORFAILENC, ISO2022 | semantics |
| `Utf8.DecoderState`, `.initial` | `Text/Utf8.lean` | the five values DECODER's `<dl>` associates with UTF-8's decoder; a first-order record, no host object | `owned`; DECODER | construction |
| `Utf8.decoderHandler` | `Text/Utf8.lean` | DECODER's eleven-step handler as one total function, returning the queue because step 4.2 restores | `owned`; DECODER | semantics |
| `Utf8.processItem`, `processQueue`, `processQueueFuel` | `Text/Utf8.lean` | PROCI and PROCQ, the second specialized to UTF-8's decoder and fuel-bounded in the `isPrefixLoop` idiom; `none` fuel is a live frontier (DB-07) | `owned`; PROCQ, PROCI | semantics |
| `Utf8.decodeQueue`, `decodeWithoutBomQueue`, `decodeWithoutBomOrFailQueue` | `Text/Utf8.lean` | the three decode hooks at the queue face | `owned`; DECODE, NOBOM, ORFAIL | laws |
| `Utf8.decode`, `decodeWithoutBom`, `decodeWithoutBomOrFail`, `decodeString`, `decodeWithoutBomString`, `decodeWithoutBomOrFailString` | `Text/Utf8.lean` | the byte-sequence and `JsString` faces every caller actually uses; derived views of the queue forms through TOQ and FROMQ, not second algorithms | `owned`; DECODE, NOBOM, ORFAIL, TOQ, FROMQ | representation, laws |
| `Utf8.errorCount`, `isWellFormed`, `bom` | `Text/Utf8.lean` | the failure-set observations ORFAIL needs; `errorCount` counts substituted errors and deliberately not U+FFFD in the output | `owned`; ORFAIL, DECODE | laws |
| `Utf8.encoderCount`, `encoderOffset`, `encoderTail`, `encoderHandler`, `encodeScalar`, `encodeScalars`, `encodeQueue`, `encode`, `encode?`, `scalars` | `Text/Utf8.lean` | ENCODER's six steps, the string form with its `isScalarValueString` hypothesis (INFRA-R3), and the queue form through LEGACY's `op.encode` at UTF-8 | `owned`; ENCODER, ENCODE, LEGACY | semantics, laws |
| `JsString.codePoints_of_no_lead`, `isAsciiString_of_units` | `Text/String.lean` (additive) | the first two Infra candidates the U3 builder proved locally; adopted with their exact statements at the home `test/contracts/url-percent-encoding.contract.md` named | `owned`; Infra `op.string-code-points`, `type.ascii-string` | laws |
| `JsString.isomorphicEncode_eq`, `asciiEncode?_eq` | `Text/Codec.lean` (additive) | the other two candidates; computed forms of two `List.pmap` definitions that are otherwise opaque to rewriting | `owned`; Infra `op.isomorphic-encode`, ASCIIENC | laws |

Do not add fields or declarations to the public frozen surface silently.
Private implementation helpers may be added without changing these signatures;
the U3 builder's `pmap_eq_map_of` is the expected one. A new public helper must
receive a record linked to its semantic owner and an appropriate theorem
receipt. Module splitting to respect dependency direction is permitted while
stable names and root reachability stay fixed, and the contract records the one
split already anticipated (`Text/IoQueue.lean`, when a second encoding is
owned).

## Ten edges

| Edge | Status | Required evidence / reason |
| --- | --- | --- |
| identity | required-open | 80 exact interface ascriptions and the constructor census in `WhatwgTest/Infra/Utf8Contract.lean`; the declaration snapshot must join every public name, and the snapshot does not exist yet |
| construction | required-open | `DecoderState.initial_eq`, the queue's `convertTo_eq` and `containsEndOfQueue_convertTo`, and the `processQueueFuel` sufficiency law; the reachable-state invariant of the decoder (`bytesSeen ≤ bytesNeeded ≤ 3` and `codePoint ≤ 0x10FFFF` at every step of a run started from `initial`) is stated only as a hypothesis of `decoderHandler_items_isScalarValue` today and owes a run-level proof |
| semantics | required-open | the thirteen handler laws, the five `processItem`/`processQueue` laws, and the encoder's `encodeScalar_eq`; the pin's `<dl class=switch>` rows are covered one at a time, but no theorem yet relates a run of `processQueue` to a *specification* of UTF-8 independent of the transcription, which is what would make the transcription checkable rather than definitional |
| laws | required-open | all 119 ascriptions of `WhatwgTest/Infra/Utf8Laws.lean` must elaborate and be proved; nothing is closed at the freeze |
| representation | required-open | the `IoQueue` ↔ `List` bridge (`convertFrom_convertTo`), the `List CodePoint` ↔ `JsString` bridge through `ofCodePoints`, and the scalar-value bridge `scalars_val`; the `Array`/`ByteArray` realizer of `ByteSequence` remains undefined repository-wide and this packet does not open it |
| counterexamples | required-open | `INFRA-UTF8-CE-001` … `018`. The twenty-one finite mutant theorems of `WhatwgTest/Infra/Counterexamples/Utf8.lean` are **green at the freeze**, but a green mutant model closes nothing: the edge closes when each row's named production statement is proved |
| bridges | required-open | three obligations. (1) `encode_ascii_eq_asciiEncode` closes the UTF-8 half of ASCIIENC's note and with it the `bridges` edge of `INFRA-PG-TEXT` that `docs/INFRA-PROOF-PLAN.md` section 4.6 left open. (2) ASCIIDEC's note (isomorphic decode and UTF-8 decode agree on ASCII bytes) is **not** stated by this packet and stays owed. (3) `u3Profile_encoderTape` and `u3Profile_decodeOrFail` discharge the U3 tapes' UTF-8 profile, but the URL revision that turns `Whatwg.Url.Boundary.Utf8Encoding` and `Utf8DecodeOrFail` into views onto this owner is a separate change in a separate tree, and until it lands the `encoding` obligation of `docs/URL-PERCENT-ENCODING-DAG.md` stays open |
| targets | not-applicable | this packet has no lowering and no generated code; P11 owns that obligation. The "Implementation considerations" section [141397,142563), SHA-256 `69780255b8ebd663b75307da96cc8e13ee00cd6972212c5327ac8013e3a07297`, describes buffer strategies for implementers and is `evidenceOnly` |
| trust | required-open | all 119 named receipts in `WhatwgTest/Infra/Utf8AxiomReport.lean`, against the R-11 ceiling and against the Infra lane's stricter local target of `[propext, Quot.sound]` (`docs/CHOICE-REMOVAL.md`, `docs/INFRA-SCALAR-ASSURANCE.md`, `docs/INFRA-INTEGER-CONSTRUCTIVE.md`). No statement in the packet mentions `String`, so the one confirmed path into `Classical.choice` for stock Lean 4.33.1 is not in scope; a receipt that reaches it is reported with its dependency path and recorded as debt here |
| coverage | required-open | the Encoding Standard has **no census, no denominator, no numerator and no report**. Nothing in this packet is coverage. The edge closes only after an Encoding census exists and `docs/SPEC-COVERAGE.md` admits it; the span table of the contract is the join key that census will use |

## Clause map and residual obligations

| Anchors | Packet obligations | Residual obligation before whole-row green |
| --- | --- | --- |
| QUEUE, READ, RESTORE | the terminator is an item; `read` does not pop it; `restore` is a prepend | `readItems` and `peek` both "wait", and the blocking semantics of a *streaming* queue — the pin's second mode, used "in parallel" — has no model here; only immediate queues are covered |
| READN, PEEK | `readItems_endOfQueue`, `peekPrefix_convertTo`, and INFRA-R15's `peek_eq_peekPrefix_tail` | the operator's answer to INFRA-R15; and `peek`'s step 1 wait condition ("size ≥ number, or contains end-of-queue, whichever comes first") is not separately stated |
| PUSH, PUSHN, FROMQ, TOQ | the three `push` branches and the container round trip | none for immediate queues |
| VOCAB, VOCAB's error modes | the four handler answers, the decoder's two modes | the encoder's `html` mode and the `&#nnn;` rendering of `op.process-an-item` step 7 are unowned; the URL lane models that rendering itself, and a later packet must relate the two or refuse |
| PROCQ, PROCI | the mode switch, the two `push` sites, the fuel bound | the assertions of steps 1 to 3 are discharged by typing, and the discharge is recorded but not itself a theorem; a reviewer must check the typing argument rather than a receipt |
| DECODER | thirteen laws, one per numbered step or switch row, including both boundary tables | the reachable-state invariant (see the `construction` edge); and the decoder's agreement with Unicode's "Best Practices for Using U+FFFD", which the pin's note asserts, is evidence about Unicode and is not restated here |
| ENCODER, ENCODE, LEGACY | the four-length shape, the lead and continuation ranges, injectivity, the BOM characterisation, and the queue form | `op.encode` [50170,50822) is transcribed only at UTF-8; the legacy hook over an arbitrary encoding, and `get an encoding` / `get an output encoding`, are unowned |
| DECODE, NOBOM, ORFAIL | BOM stripping exactly once, the two error modes, the failure set as the encoder's image complement | `op.decode` and `op.BOM sniff` — the legacy-hooks region [47217,50162), SHA-256 `d540b227f4dc36d33a7ff07efd4ca4b36aaaba644b4bfee453eaa4b853fcfd07` — are unowned: they need UTF-16BE/LE decoders, which this packet refuses to open |
| GETENC, ORFAILENC, ISO2022 | `hasEncoder`, `isStateful`, the UTF-8 answer, and the foreign tape's advance | the ISO-2022-JP *encoder* is a profile, not a transcription: its Roman-state caveat ("the caller cannot output 0x5C (\\) as it will not decode as U+005C") is prose here and no theorem constrains a caller. A standard that uses `encode or fail` with a legacy encoder gets no protection from this packet |
| ASCIIENC | `encode_ascii_eq_asciiEncode` | — |
| ASCIIDEC | none | the decode half of the Infra agreement note is owed; see the `bridges` edge |

## What this graph does not claim

The packet owns **one** encoding. The labels table, the index tables, the
single-byte and legacy multi-byte encoders and decoders, `TextDecoder`,
`TextEncoder`, `TextDecoderStream` and `TextEncoderStream` are outside it and
have no declaration. `docs/REIFICATION-STRATEGY.md` RS-3 puts the streaming
interfaces in Stratum S, where they would be a signature over this codec, not a
sixth family of it; RS-2 puts "stateless Encoding" in Stratum A. Neither is
opened here.

No host profile is involved and no observation mask is named: the family is
equational (see the contract's "Observation mask").

## Evidence ledger

Specification byte-span cross-check, green witness command, intended red
commands and the immutable packet commit are recorded in the contract's freeze
receipt. The coordinator owns root and known-red integration and may append
landing receipts; it may not weaken this packet.
