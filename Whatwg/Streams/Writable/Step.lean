import Whatwg.Streams.Writable.DefaultWriter

/-!
# Writable steps and finite derivations

WRITABLE-PG-DEFAULT owns these judgments. A `none` label records deterministic
administrative work; `some` records an external decision. No fuel bound defines
meaning. The local candidate observations and global embedding obligations are
unchanged by finite composition.
-/

namespace Whatwg.Streams.Writable

/-- The graph of one external decision or deterministic internal tick. -/
def Step {α ε : Type} (s : State α ε) (d : Option (Decision α ε))
    (t : State α ε) : Prop :=
  (match d with | none => tick s | some a => decide s a) = some t

/-- Finite derivations of the local writable machine, including internal ticks. -/
inductive Reaches {α ε : Type} :
    State α ε → List (Option (Decision α ε)) → State α ε → Prop
  | nil (s : State α ε) : Reaches s [] s
  | cons {s mid t : State α ε} {d : Option (Decision α ε)}
      {ds : List (Option (Decision α ε))} :
      Step s d mid → Reaches mid ds t → Reaches s (d :: ds) t

end Whatwg.Streams.Writable
