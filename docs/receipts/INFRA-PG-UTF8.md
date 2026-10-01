# Receipts log of `INFRA-PG-UTF8`

This log holds the history of `docs/INFRA-UTF8-DAG.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/INFRA-UTF8-DAG.md`.

## Ten edges

Moved verbatim from `docs/INFRA-UTF8-DAG.md` at `325d5d5`.

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
