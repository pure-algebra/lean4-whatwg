import Whatwg.Streams.Readable.DefaultReader
import Whatwg.Streams.Kernel

/-!
# External decisions and finite composition

Owner: `READABLE-PG-DEFAULT`, semantics edge. These are the finite external steps
of the default-readable view under its local M1/M2 observations. Internal promise
jobs are deterministic state transitions, not decisions. The global interleaving
relation and host embedding remain open; this is not a fixed-fuel denotation.

Slice W8a (packet `test/contracts/transition-kernel.contract.md`): `Step` is
`Kernel.Graph step` by definition and `Steps` is a `Kernel.Path` derivation, so the
nil, cons and append laws below are corollaries of the kernel's.
-/

namespace Whatwg.Streams.Readable

/-- Consumer/controller operations and typed foreign callback answers. -/
inductive Decision (α ε : Type) where
  | read
  | enqueue (chunk : α)
  | close
  | error (reason : Boundary.Exception ε)
  | size (answer : Data.SizeAnswer Size (Boundary.Exception ε))
  | pull (answer : PullAnswer ε)
  | pullReturn (result : PullReturn ε)
  | desiredSize

/-- Consume one external decision. Unmatched answers produce no transition. -/
def step {α ε : Type} (s : State α ε) : Decision α ε → Option (State α ε)
  | .read => some (read s)
  | .enqueue chunk => some (beginEnqueue s chunk)
  | .close => some (close s)
  | .error reason => some (error s reason)
  | .size answer => resumeSize s answer
  | .pull answer => acceptPullAnswer s answer
  | .pullReturn result => returnPull s result
  | .desiredSize => some (queryDesiredSize s)

/-- The relational graph of one external step, before global job interleaving. -/
def Step {α ε : Type} (s : State α ε) (d : Decision α ε) (t : State α ε) : Prop :=
  step s d = some t

/-- Finite external-step derivations. Composition is stated here, without a fuel bound. -/
inductive Steps {α ε : Type} : State α ε → List (Decision α ε) → State α ε → Prop
  | nil (s : State α ε) : Steps s [] s
  | cons {s mid t : State α ε} {d : Decision α ε} {ds : List (Decision α ε)} :
      Step s d mid → Steps mid ds t → Steps s (d :: ds) t

variable {α ε : Type}

/-- `op.readable-stream-default-reader-read`: the external dispatch equation, local M1/M2. -/
theorem step_read (s : State α ε) : step s .read = some (read s) := rfl

/-- `op.readable-stream-default-controller-enqueue`: external dispatch, local M1/M2. -/
theorem step_enqueue (s : State α ε) (chunk : α) :
    step s (.enqueue chunk) = some (beginEnqueue s chunk) := rfl

/-- `op.readable-stream-default-controller-close`: external dispatch, local M1/M2. -/
theorem step_close (s : State α ε) : step s .close = some (close s) := rfl

/-- `op.readable-stream-default-controller-error`: external dispatch, local M1/M2. -/
theorem step_error (s : State α ε) (e : Boundary.Exception ε) :
    step s (.error e) = some (error s e) := rfl

/-- `op.readable-stream-default-controller-enqueue`: admit its size answer, local M1/M2. -/
theorem step_size (s : State α ε) (a : Data.SizeAnswer Size (Boundary.Exception ε)) :
    step s (.size a) = resumeSize s a := rfl

/-- `op.readable-stream-default-controller-call-pull-if-needed`: eventual answer, local M1/M2. -/
theorem step_pull (s : State α ε) (a : PullAnswer ε) :
    step s (.pull a) = acceptPullAnswer s a := rfl

/-- Synchronous pull return is a separate decision from its eventual settlement. -/
theorem step_pullReturn (s : State α ε) (result : PullReturn ε) :
    step s (.pullReturn result) = returnPull s result := rfl

/-- `op.readable-stream-default-controller-get-desired-size`: record the M2 query. -/
theorem step_desiredSize (s : State α ε) :
    step s .desiredSize = some (queryDesiredSize s) := rfl

/-- The exact graph judgment for one external step under local M1/M2. -/
theorem step_iff (s t : State α ε) (d : Decision α ε) :
    Step s d t ↔ step s d = some t := Iff.rfl

/-- Kernel bridge, READABLE-PG-DEFAULT semantics edge: `Step` is the kernel's
graph of `step`, by definition. -/
theorem step_eq_graph : @Step α ε = Kernel.Graph step := rfl

/-- Kernel bridge, READABLE-PG-DEFAULT semantics edge: the finite external-step
derivations are the kernel's derivations of `Step`. -/
theorem steps_iff_path {s t : State α ε} {ds : List (Decision α ε)} :
    Steps s ds t ↔ Kernel.Path Step s ds t := by
  constructor
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons first _ ih => exact .cons first ih
  · intro h
    induction h with
    | nil s => exact .nil s
    | cons first _ ih => exact .cons first ih

/-- Empty external derivations identify their endpoints; no internal jobs are implied.
Corollary of `Kernel.Path.nil_iff` through `steps_iff_path`. -/
theorem steps_nil_iff (s t : State α ε) : Steps s [] t ↔ s = t :=
  steps_iff_path.trans Kernel.Path.nil_iff

/-- A nonempty derivation has exactly its first transition and remaining derivation.
Corollary of `Kernel.Path.cons_iff` through `steps_iff_path`. -/
theorem steps_cons_iff (s t : State α ε) (d : Decision α ε) (ds : List (Decision α ε)) :
    Steps s (d :: ds) t ↔ ∃ mid, Step s d mid ∧ Steps mid ds t :=
  steps_iff_path.trans <| Kernel.Path.cons_iff.trans <|
    exists_congr fun _ => and_congr_right fun _ => steps_iff_path.symm

/-- Finite relational composition, independent of fuel and valid under either local mask.
Corollary of `Kernel.Path.append_iff` through `steps_iff_path`. -/
theorem steps_append_iff (s t : State α ε) (left right : List (Decision α ε)) :
    Steps s (left ++ right) t ↔ ∃ mid, Steps s left mid ∧ Steps mid right t :=
  steps_iff_path.trans <| Kernel.Path.append_iff.trans <|
    exists_congr fun _ => and_congr steps_iff_path.symm steps_iff_path.symm

end Whatwg.Streams.Readable
