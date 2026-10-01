import Whatwg.Streams.Writable.DefaultWriter
import Whatwg.Streams.Kernel

/-!
# Writable steps and finite derivations

WRITABLE-PG-DEFAULT owns these judgments. A `none` label records deterministic
administrative work; `some` records an external decision. No fuel bound defines
meaning. The local candidate observations and global embedding obligations are
unchanged by finite composition.

Slice W8a (packet `test/contracts/transition-kernel.contract.md`) bridges both
judgments to `Whatwg.Streams.Kernel`. The local machine is not exclusive
(`WS-KERNEL-CE-002`), so the kernel's comparability laws are not claimed here.
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

/-- Kernel bridge, WRITABLE-PG-DEFAULT semantics edge: `Step` is the graph of
the kernel's two-stage step over `tick` and `decide`, pointwise, by cases on
the label (`WS-KERNEL-CE-004`). -/
theorem step_iff_stage {α ε : Type} (s : State α ε) (d : Option (Decision α ε))
    (t : State α ε) : Step s d t ↔ Kernel.Graph (Kernel.stage tick decide) s d t := by
  cases d <;> exact Iff.rfl

/-- Kernel bridge, WRITABLE-PG-DEFAULT semantics edge: the local derivations are
the kernel's derivations of `Step`. -/
theorem reaches_iff_path {α ε : Type} {s t : State α ε} {ds : List (Option (Decision α ε))} :
    Reaches s ds t ↔ Kernel.Path Step s ds t := by
  constructor
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons first _ ih => exact .cons first ih
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons first _ ih => exact .cons first ih

end Whatwg.Streams.Writable
