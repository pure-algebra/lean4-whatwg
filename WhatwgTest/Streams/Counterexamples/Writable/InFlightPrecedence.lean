import Init

/-!
WS-WRITE-CE-017: Boolean precedence and Prop/Bool coercion can weaken an equation.
This finite witness uses only Init and no production writable implementation.
-/

set_option autoImplicit false

namespace WhatwgTest.Streams.Counterexamples.Writable.InFlightPrecedence

private def weakLaw (answer writeInFlight closeInFlight : Bool) : Prop :=
  answer = writeInFlight || closeInFlight

private def exactLaw (answer writeInFlight closeInFlight : Bool) : Prop :=
  answer = (writeInFlight || closeInFlight)

/-- The unparenthesized syntax elaborates to this coerced Boolean disjunction. -/
theorem weakLaw_parse (answer writeInFlight closeInFlight : Bool) :
    weakLaw answer writeInFlight closeInFlight ↔
      (decide (answer = writeInFlight) || closeInFlight) = true := by
  rfl

/-- Ignoring in-flight close passes the weak law for every Boolean input. -/
theorem ce017_ignored_close_passes_weak :
    (∀ writeInFlight closeInFlight : Bool,
      weakLaw writeInFlight writeInFlight closeInFlight) ∧
    ¬ exactLaw false false true := by
  constructor
  · intro writeInFlight closeInFlight
    unfold weakLaw
    cases writeInFlight <;> cases closeInFlight <;> decide +kernel
  · unfold exactLaw
    decide +kernel

#print axioms weakLaw_parse
#print axioms ce017_ignored_close_passes_weak

end WhatwgTest.Streams.Counterexamples.Writable.InFlightPrecedence
