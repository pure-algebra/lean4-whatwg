import Whatwg.Streams

/-!
P5a additive exact in-flight equation. Graph: WRITABLE-PG-DEFAULT.
The original hasInFlight_eq ascription stays unchanged. Parentheses make this
an equality to the complete Boolean disjunction, avoiding Prop/Bool coercion.
-/

set_option autoImplicit false

-- INFLIGHT: op.writable-stream-has-operation-marked-in-flight
#check (@Whatwg.Streams.Writable.hasInFlight_exact :
  ∀ {α ε : Type} (s : Whatwg.Streams.Writable.State α ε),
    Whatwg.Streams.Writable.hasInFlight s =
      (s.inFlightWrite.isSome ||
        (match s.closeState with | .inFlight _ _ => true | _ => false)))
