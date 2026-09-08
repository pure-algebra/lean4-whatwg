import Whatwg.Infra

/-!
Breaker-owned axiom receipt list for `INFRA-PG-UTF8`.

Contract: `test/contracts/infra-utf8.contract.md`.
Laws: `WhatwgTest/Infra/Utf8Laws.lean`.
Graph: `docs/INFRA-UTF8-DAG.md`.

Exactly the 119 theorem ascriptions of that battery, in the same order, as
`#print axioms`.

The repository ceiling applies (ruling R-11): `propext`, `Quot.sound`,
`Classical.choice` and nothing else, with `sorryAx`, `Lean.ofReduceBool`,
`Lean.ofReduceNat`, `Lean.trustCompiler` and the `native_decide` auxiliaries
forbidden everywhere.

The Infra lane carries a stricter local target. `docs/CHOICE-REMOVAL.md`,
`docs/INFRA-SCALAR-ASSURANCE.md` and `docs/INFRA-INTEGER-CONSTRUCTIVE.md`
already hold `[propext, Quot.sound]` receipts for the scalar and integer
families, and that target is not to regress. The UTF-8 codec is finite,
decidable and structural over `List`, `Nat` and `UInt8`, so the expectation for
every receipt below is `[]`, `[propext]` or `[propext, Quot.sound]`. The
contract names the two statements where `Classical.choice` might still be
unavoidable, both through the stock `String` path
`docs/CHOICE-REMOVAL.md` documents, and neither of them mentions `String`:
`isWellFormed_iff` and `encode_decodeWithoutBom` are the two existential
statements, and an existential over a decidable finite search has a
constructive witness. A receipt here that reaches `Classical.choice` is a
signal to look again, and the builder reports its exact dependency path before
accepting it.

Unknown constants are the intended red phase. An import or toolchain failure is
never intended red.
-/

set_option autoImplicit false
#print axioms Whatwg.Infra.IoQueue.read_nil
#print axioms Whatwg.Infra.IoQueue.read_endOfQueue
#print axioms Whatwg.Infra.IoQueue.read_value
#print axioms Whatwg.Infra.IoQueue.readItems_endOfQueue
#print axioms Whatwg.Infra.IoQueue.push_append
#print axioms Whatwg.Infra.IoQueue.push_before_endOfQueue
#print axioms Whatwg.Infra.IoQueue.push_endOfQueue_idem
#print axioms Whatwg.Infra.IoQueue.restore_eq
#print axioms Whatwg.Infra.IoQueue.restoreItems_eq
#print axioms Whatwg.Infra.IoQueue.restoreItems_example
#print axioms Whatwg.Infra.IoQueue.convertTo_eq
#print axioms Whatwg.Infra.IoQueue.convertFrom_convertTo
#print axioms Whatwg.Infra.IoQueue.containsEndOfQueue_convertTo
#print axioms Whatwg.Infra.IoQueue.peekPrefix_convertTo
#print axioms Whatwg.Infra.IoQueue.peek_eq_peekPrefix_tail
#print axioms Whatwg.Infra.IoQueue.peek_bom_example
#print axioms Whatwg.Infra.JsString.codePoints_of_no_lead
#print axioms Whatwg.Infra.JsString.isAsciiString_of_units
#print axioms Whatwg.Infra.JsString.isomorphicEncode_eq
#print axioms Whatwg.Infra.JsString.asciiEncode?_eq
#print axioms Whatwg.Infra.Utf8.encoderCount_eq
#print axioms Whatwg.Infra.Utf8.encoderOffset_eq
#print axioms Whatwg.Infra.Utf8.encoderTail_zero
#print axioms Whatwg.Infra.Utf8.encoderTail_succ
#print axioms Whatwg.Infra.Utf8.encoderTail_length
#print axioms Whatwg.Infra.Utf8.encoderTail_continuation
#print axioms Whatwg.Infra.Utf8.encodeScalar_eq
#print axioms Whatwg.Infra.Utf8.encodeScalar_ascii
#print axioms Whatwg.Infra.Utf8.encodeScalar_length_one
#print axioms Whatwg.Infra.Utf8.encodeScalar_length_two
#print axioms Whatwg.Infra.Utf8.encodeScalar_length_three
#print axioms Whatwg.Infra.Utf8.encodeScalar_length_four
#print axioms Whatwg.Infra.Utf8.encodeScalar_length_mem
#print axioms Whatwg.Infra.Utf8.encodeScalar_ne_nil
#print axioms Whatwg.Infra.Utf8.encodeScalar_head_range
#print axioms Whatwg.Infra.Utf8.encodeScalar_tail_continuation
#print axioms Whatwg.Infra.Utf8.encodeScalar_injective
#print axioms Whatwg.Infra.Utf8.encodeScalar_bom_iff
#print axioms Whatwg.Infra.Utf8.bom_eq
#print axioms Whatwg.Infra.Utf8.encodeScalars_eq
#print axioms Whatwg.Infra.Utf8.encodeScalars_append
#print axioms Whatwg.Infra.Utf8.encodeQueue_convertTo
#print axioms Whatwg.Infra.Utf8.scalars_val
#print axioms Whatwg.Infra.Utf8.encode_eq
#print axioms Whatwg.Infra.Utf8.encode?_eq_some
#print axioms Whatwg.Infra.Utf8.encode?_eq_none
#print axioms Whatwg.Infra.Utf8.encode_startsWith_bom_iff
#print axioms Whatwg.Infra.Utf8.encode_ascii_eq_asciiEncode
#print axioms Whatwg.Infra.Utf8.encode_ne_isomorphicEncode_example
#print axioms Whatwg.Infra.Utf8.encode_astral_example
#print axioms Whatwg.Infra.Utf8.DecoderState.initial_eq
#print axioms Whatwg.Infra.Utf8.decoderHandler_endOfQueue_pending
#print axioms Whatwg.Infra.Utf8.decoderHandler_endOfQueue_idle
#print axioms Whatwg.Infra.Utf8.decoderHandler_ascii
#print axioms Whatwg.Infra.Utf8.decoderHandler_lead_two
#print axioms Whatwg.Infra.Utf8.decoderHandler_lead_three
#print axioms Whatwg.Infra.Utf8.decoderHandler_lead_four
#print axioms Whatwg.Infra.Utf8.decoderHandler_lead_error
#print axioms Whatwg.Infra.Utf8.decoderHandler_out_of_boundary
#print axioms Whatwg.Infra.Utf8.decoderHandler_accumulate
#print axioms Whatwg.Infra.Utf8.decoderHandler_complete
#print axioms Whatwg.Infra.Utf8.decoderHandler_error_none
#print axioms Whatwg.Infra.Utf8.decoderHandler_items_isScalarValue
#print axioms Whatwg.Infra.Utf8.processQueueFuel_eq
#print axioms Whatwg.Infra.Utf8.processQueue_fuel_stable
#print axioms Whatwg.Infra.Utf8.processItem_replacement
#print axioms Whatwg.Infra.Utf8.processItem_fatal
#print axioms Whatwg.Infra.Utf8.processItem_finished
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_eq
#print axioms Whatwg.Infra.Utf8.decode_eq
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomString_eq
#print axioms Whatwg.Infra.Utf8.decodeString_eq
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFailString_eq
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_all_isScalarValue
#print axioms Whatwg.Infra.Utf8.decode_all_isScalarValue
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_encodeScalars
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_encode
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFail_encode
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq_some_imp
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomString_encode
#print axioms Whatwg.Infra.Utf8.encode_decodeWithoutBom
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq_none_iff
#print axioms Whatwg.Infra.Utf8.errorCount_eq_zero_iff
#print axioms Whatwg.Infra.Utf8.isWellFormed_iff
#print axioms Whatwg.Infra.Utf8.replacement_input_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_unexpected_continuation
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_invalid_lead
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_truncated_one
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_truncated_then_ascii_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_overlong_two_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_overlong_three_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_overlong_four_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_surrogate_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_above_max_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_max_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_before_surrogates_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBomOrFail_malformed_example
#print axioms Whatwg.Infra.Utf8.decode_bom_prefix
#print axioms Whatwg.Infra.Utf8.decode_bom_once
#print axioms Whatwg.Infra.Utf8.decode_bom_twice_example
#print axioms Whatwg.Infra.Utf8.decode_bom_only_example
#print axioms Whatwg.Infra.Utf8.decode_no_bom
#print axioms Whatwg.Infra.Utf8.decode_partial_bom_example
#print axioms Whatwg.Infra.Utf8.decodeWithoutBom_keeps_bom_example
#print axioms Whatwg.Infra.Encoding.Name.hasEncoder_iff
#print axioms Whatwg.Infra.Encoding.Name.isStateful_iff
#print axioms Whatwg.Infra.Encoding.Name.isOwned_iff
#print axioms Whatwg.Infra.Encoding.getAnEncoder?_utf8
#print axioms Whatwg.Infra.Encoding.getAnEncoder?_eq_none
#print axioms Whatwg.Infra.Encoding.getAnEncoder?_eq_some
#print axioms Whatwg.Infra.Encoding.Encoder.name_utf8
#print axioms Whatwg.Infra.Encoding.encodeOrFail_utf8
#print axioms Whatwg.Infra.Encoding.encodeOrFail_utf8_never_errors
#print axioms Whatwg.Infra.Encoding.encodeOrFail_foreign_advances
#print axioms Whatwg.Infra.Encoding.encodeOrFail_foreign_frontier
#print axioms Whatwg.Infra.Encoding.EncoderTape.terminated_iff
#print axioms Whatwg.Infra.Utf8.u3Profile_encoderTape
#print axioms Whatwg.Infra.Utf8.u3Profile_decodeOrFail
