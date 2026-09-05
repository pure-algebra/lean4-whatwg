import Whatwg.Infra.Text.Scan

/-!
# WS-INFRA-CE-001: comma splitting is not strict splitting

Owner: the WS-INFRA-CE-001 row of `test/counterexamples/REGISTER.md`.
Authority: `op.split-on-commas` and `op.strictly-split` in the pinned
`generated/infra-census.tsv`. The comma loop checks for end before collecting
a token, then advances past the delimiter. The strict loop collects an
initial token and collects again after each delimiter.

These are finite kernel-checked probes of the existing Infra implementation,
not general algorithm laws or coverage witnesses. This equational family has
no observation mask or host boundary. The negative theorem retains the exact
claim superseded in the source example; no algorithm changed to satisfy it.
-/

namespace WhatwgTest.Streams.Counterexamples.Infra

open Whatwg.Infra.JsString

theorem ce001_comma_result :
    splitOnCommas (ofLiteral " a , ,b,") =
      [ofLiteral "a", ofLiteral "", ofLiteral "b"] := by decide +kernel

theorem ce001_extra_trailing_token_refuted :
    splitOnCommas (ofLiteral " a , ,b,") ≠
      [ofLiteral "a", ofLiteral "", ofLiteral "b", ofLiteral ""] := by decide +kernel

theorem ce001_comma_pair :
    splitOnCommas (ofLiteral ",,") = [ofLiteral "", ofLiteral ""] := by decide +kernel

theorem ce001_strict_control :
    strictlySplit (ofLiteral ",,") comma =
      [ofLiteral "", ofLiteral "", ofLiteral ""] := by decide +kernel

theorem ce001_whitespace_control :
    splitOnAsciiWhitespace (ofLiteral "  ") = [] := by decide +kernel

theorem ce001_empty_input_control :
    splitOnCommas (ofLiteral "") = [] ∧
      strictlySplit (ofLiteral "") comma = [ofLiteral ""] := by decide +kernel

#print axioms ce001_comma_result
#print axioms ce001_extra_trailing_token_refuted
#print axioms ce001_comma_pair
#print axioms ce001_strict_control
#print axioms ce001_whitespace_control
#print axioms ce001_empty_input_control

end WhatwgTest.Streams.Counterexamples.Infra
