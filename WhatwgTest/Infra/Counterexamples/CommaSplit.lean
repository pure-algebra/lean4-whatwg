import Whatwg.Infra.Text.Scan

/-!
# Comma-splitting counterexample INFRA-TEXT-CE-001

Breaker packet: `test/counterexamples/infra/COMMA-SPLIT.md`.
Authority: `strings`, "split on commas", in the pinned Infra source
`vendor/whatwg-infra-3f984adc/infra.bs`, byte span [62430, 63598), SHA-256
`f128d4ae1e956dda5cc54b39e8976a11c5ae9b4754aac71925741ef982717962`.

The observed value is the entire ordered list of `JsString` tokens. These
closed finite probes exercise production definitions; they establish no general
algorithm law or host claim. `decide +kernel` checks the propositions by kernel
reduction. The commands below print the actual axiom dependencies at elaboration.
-/

set_option autoImplicit false

namespace WhatwgTest.Infra.Counterexamples.CommaSplit

open Whatwg.Infra.JsString

/-- INFRA-TEXT-CE-001: the final comma advances the position past the input's last code point. -/
theorem ce001_correct_result :
    splitOnCommas (ofLiteral " a , ,b,") =
      [ofLiteral "a", ofLiteral "", ofLiteral "b"] := by
  decide +kernel

/-- INFRA-TEXT-CE-001: the exact four-token proposition from the original source example is false. -/
theorem ce001_original_result_false :
    ¬ (splitOnCommas (ofLiteral " a , ,b,") =
      [ofLiteral "a", ofLiteral "", ofLiteral "b", ofLiteral ""]) := by
  decide +kernel

/-- INFRA-TEXT-CE-001: empty input enters no iteration and produces no tokens. -/
theorem ce001_empty_input : splitOnCommas (ofLiteral "") = [] := by
  decide +kernel

#check (@ce001_correct_result :
  splitOnCommas (ofLiteral " a , ,b,") =
    [ofLiteral "a", ofLiteral "", ofLiteral "b"])

#check (@ce001_original_result_false :
  ¬ (splitOnCommas (ofLiteral " a , ,b,") =
    [ofLiteral "a", ofLiteral "", ofLiteral "b", ofLiteral ""]))

#check (@ce001_empty_input : splitOnCommas (ofLiteral "") = [])

#print axioms ce001_correct_result
#print axioms ce001_original_result_false
#print axioms ce001_empty_input

end WhatwgTest.Infra.Counterexamples.CommaSplit
