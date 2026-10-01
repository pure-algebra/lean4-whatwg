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

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/INFRA-UTF8-DAG.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/InfraUtf8.lean` and its projection `generated/graphs/INFRA-PG-UTF8.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30, with the trust row
brought to the lane V landing of 2026-10-01 (R-V6, R-V8). Ruling R-U4 landed the
packet on `main` as `854cc68` on 2026-09-07: all 119 ascriptions of
`WhatwgTest/Infra/Utf8Laws.lean` green, the counterexample battery green, no
statement of the frozen packet changed, and the R-11 ceiling held for every
receipt, while the stricter R-U3 target was unmet for 17 receipts (debt D42,
closed by lane V).
This document carried no landing record before this table. Ruling R-V4 sets
the rule: an edge is `required-closed` only when every ground this document
or a ruling in `COORDINATION.md` states for keeping it open is discharged by
something named in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The declaration snapshot that joins every public name, which has no generator (debt D47). The 80 interface ascriptions of `WhatwgTest/Infra/Utf8Contract.lean` elaborate |
| construction | `required-open` | The decoder's reachable-state invariant (`bytesSeen ≤ bytesNeeded ≤ 3` and `codePoint ≤ 0x10FFFF` at every step of a run started from `initial`) has no run-level proof; at `325d5d5` it is still only a hypothesis of `decoderHandler_items_isScalarValue` |
| semantics | `required-open` | No theorem relates a run of `processQueue` to a specification of UTF-8 independent of the transcription; R-U4 does not address this ground |
| laws | `required-closed` | All 119 ascriptions of `WhatwgTest/Infra/Utf8Laws.lean` elaborate and are proved (R-U4) |
| representation | `required-closed` | The three bridges the edge names are among the 119 laws R-U4 lands: `IoQueue.convertFrom_convertTo`, the `JsString.ofCodePoints` faces `decodeString_eq`, `decodeWithoutBomString_eq` and `decodeWithoutBomOrFailString_eq`, and `Utf8.scalars_val`. The `Array`/`ByteArray` realizer of `ByteSequence` is outside this packet by the edge's own statement |
| counterexamples | `required-open` | `INFRA-UTF8-CE-001` to `INFRA-UTF8-CE-018` stand `SEEDED` in `test/counterexamples/infra/UTF8.md`, and no landing record moves them. They have no row in `test/counterexamples/REGISTER.md` (debt D45), and the witness module `WhatwgTest/Infra/Counterexamples/Utf8.lean` imports no production module (debt D50). R-U4 records the counterexample battery green |
| bridges | `required-open` | Of the three obligations, (1) is closed by `encode_ascii_eq_asciiEncode`; (2), the decode half of ASCIIDEC's agreement note (isomorphic decode and UTF-8 decode agree on ASCII bytes), is not stated and stays owed; (3) is ruled by R-U5: R-U4's closure of the URL `encoding` obligation stands on the ground R-U3 gave it, the theorems `u3Profile_encoderTape` and `u3Profile_decodeOrFail`, and what that closure does not cover is debt D44, since no declaration constructs a `Whatwg.Url.Boundary.Utf8Encoding` from this encoder |
| targets | `not-applicable` | This packet has no lowering and no generated code; P11 owns that obligation. The "Implementation considerations" section is `evidenceOnly` |
| trust | `required-closed` | The edge was open at `325d5d5` on one ground: the R-U3 target, `propext` and `Quot.sound` only, was unmet for 17 of the 119 receipts of `WhatwgTest/Infra/Utf8AxiomReport.lean` (debt D42). Slice V5 of lane V repaired the proofs with no statement changed, and since that landing the axiom gate holds every declaration of `Whatwg.Infra.Text.Utf8` to `propext` and `Quot.sound` with no exception (R-V1, R-V6). D42 is closed |
| coverage | `required-open` | The Encoding Standard has no census, denominator, numerator or report; the edge closes only after an Encoding census exists and `docs/SPEC-COVERAGE.md` admits it |

The URL `encoding` obligation, under ruling R-U5: R-U4's closure stands. The
two facts `Whatwg.Url.Boundary.Utf8Encoding.tape` assumes are theorems of this
owner, `Whatwg.Infra.Utf8.u3Profile_encoderTape` and
`Whatwg.Infra.Utf8.u3Profile_decodeOrFail`. No declaration constructs a
`Utf8Encoding` from this encoder, so its `bytes` field is unconstrained in every
URL operation; that gap is debt D44, owed before U5 consumes the
percent-encoding rows.
