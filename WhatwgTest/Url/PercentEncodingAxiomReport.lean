import Whatwg.Infra
import Whatwg.Url

/-!
Breaker-owned U3 axiom receipt list for `URL-PG-PERCENT`.

Contract: `test/contracts/url-percent-encoding.contract.md`.
Laws: `WhatwgTest/Url/PercentEncodingLaws.lean`.

Exactly the 95 theorem ascriptions of that battery, in the same order. The
repository ceiling applies (ruling R-11): `propext`, `Quot.sound`,
`Classical.choice` and nothing else. The URL lane's additional
choice-minimization objective (`docs/URL-PACKAGE-PLAN.md`) asks the builder to
report the exact dependency path of any receipt that does reach
`Classical.choice` and to try a constructive proof first; percent encoding is
finite, decidable, and structural, so no receipt here is expected to need it.

Unknown constants are the intended red phase. An import or toolchain failure is
never intended red.
-/

set_option autoImplicit false

#print axioms Whatwg.Url.PercentEncoding.c0Control_mem_iff
#print axioms Whatwg.Url.PercentEncoding.fragment_mem_iff
#print axioms Whatwg.Url.PercentEncoding.query_mem_iff
#print axioms Whatwg.Url.PercentEncoding.specialQuery_mem_iff
#print axioms Whatwg.Url.PercentEncoding.path_mem_iff
#print axioms Whatwg.Url.PercentEncoding.userinfo_mem_iff
#print axioms Whatwg.Url.PercentEncoding.component_mem_iff
#print axioms Whatwg.Url.PercentEncoding.form_mem_iff
#print axioms Whatwg.Url.PercentEncoding.c0Control_subset_fragment
#print axioms Whatwg.Url.PercentEncoding.c0Control_subset_query
#print axioms Whatwg.Url.PercentEncoding.query_subset_specialQuery
#print axioms Whatwg.Url.PercentEncoding.query_subset_path
#print axioms Whatwg.Url.PercentEncoding.path_subset_userinfo
#print axioms Whatwg.Url.PercentEncoding.userinfo_subset_component
#print axioms Whatwg.Url.PercentEncoding.component_subset_form
#print axioms Whatwg.Url.PercentEncoding.fragment_strict_c0Control
#print axioms Whatwg.Url.PercentEncoding.query_strict_c0Control
#print axioms Whatwg.Url.PercentEncoding.specialQuery_strict_query
#print axioms Whatwg.Url.PercentEncoding.path_strict_query
#print axioms Whatwg.Url.PercentEncoding.userinfo_strict_path
#print axioms Whatwg.Url.PercentEncoding.component_strict_userinfo
#print axioms Whatwg.Url.PercentEncoding.form_strict_component
#print axioms Whatwg.Url.PercentEncoding.fragment_not_subset_query
#print axioms Whatwg.Url.PercentEncoding.query_not_subset_fragment
#print axioms Whatwg.Url.PercentEncoding.form_complement
#print axioms Whatwg.Url.PercentEncoding.component_complement
#print axioms Whatwg.Url.PercentEncoding.setOf_eq
#print axioms Whatwg.Url.PercentEncoding.setOf_injective
#print axioms Whatwg.Url.PercentEncoding.setOf_includes_non_ascii
#print axioms Whatwg.Url.PercentEncoding.isPercentEncodedByte_iff
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_eq
#print axioms Whatwg.Url.PercentEncoding.upperHexDigit_isAsciiUpperHexDigit
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_upper
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_isPercentEncodedByte
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_injective
#print axioms Whatwg.Url.PercentEncoding.isHexByte_iff
#print axioms Whatwg.Url.PercentEncoding.hexValue_digit
#print axioms Whatwg.Url.PercentEncoding.hexValue_upper
#print axioms Whatwg.Url.PercentEncoding.hexValue_lower
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_nil
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_other
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_pair
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_malformed_pair
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_short
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_length_le
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_percent_le
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_id_of_no_percent
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_not_idempotent
#print axioms Whatwg.Url.PercentEncoding.percentDecodeString_eq
#print axioms Whatwg.Url.PercentEncoding.followsUtf8Advice_iff
#print axioms Whatwg.Url.PercentEncoding.followsUtf8Advice_component
#print axioms Whatwg.Url.PercentEncoding.encodingAssertion_iff
#print axioms Whatwg.Url.PercentEncoding.spaceAsPlus_iff
#print axioms Whatwg.Url.PercentEncoding.isomorph_val
#print axioms Whatwg.Url.PercentEncoding.renderByte_plus
#print axioms Whatwg.Url.PercentEncoding.renderByte_isomorph
#print axioms Whatwg.Url.PercentEncoding.renderByte_encoded
#print axioms Whatwg.Url.PercentEncoding.errorReference_eq
#print axioms Whatwg.Url.PercentEncoding.decimalDigits_zero
#print axioms Whatwg.Url.PercentEncoding.decimalDigits_isAsciiDigits
#print axioms Whatwg.Url.PercentEncoding.decimalDigits_shortest
#print axioms Whatwg.Url.PercentEncoding.renderAnswer_none
#print axioms Whatwg.Url.PercentEncoding.renderAnswer_some
#print axioms Whatwg.Url.PercentEncoding.encodeLoop_nil
#print axioms Whatwg.Url.PercentEncoding.encodeLoop_terminal
#print axioms Whatwg.Url.PercentEncoding.encodeLoop_cons
#print axioms Whatwg.Url.PercentEncoding.encodeLoop_append
#print axioms Whatwg.Url.Boundary.EncoderTape.terminated_iff
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_eq
#print axioms Whatwg.Url.Boundary.Utf8Encoding.tape_eq
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_eq
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_flatMap
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_append
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeCodePoint_eq
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_isAsciiString
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_percentEncodeByte
#print axioms Whatwg.Url.PercentEncoding.roundTrip_component
#print axioms Whatwg.Url.PercentEncoding.roundTrip_form
#print axioms Whatwg.Url.PercentEncoding.roundTrip_form_space_fails
#print axioms Whatwg.Url.PercentEncoding.roundTrip_query_fails
#print axioms Whatwg.Url.Boundary.isStateful_utf8
#print axioms Whatwg.Url.Boundary.isStateful_iso2022jp
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_example_23
#print axioms Whatwg.Url.PercentEncoding.percentEncodeByte_example_7F
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_example
#print axioms Whatwg.Url.PercentEncoding.percentDecodeBytes_example_lowercase
#print axioms Whatwg.Url.PercentEncoding.percentDecodeString_example
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_space
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_equiv
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_error
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_iso2022jp
#print axioms Whatwg.Url.PercentEncoding.percentEncodeAfterEncoding_example_form
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_equiv
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_interrobang
#print axioms Whatwg.Url.PercentEncoding.utf8PercentEncodeString_example_say
