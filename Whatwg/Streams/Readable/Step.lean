import Whatwg.Streams.Readable.DefaultReader

/-!
# External decisions and finite composition

Owner: `READABLE-PG-DEFAULT`, semantics edge. These are the finite external steps
of the default-readable view under its local M1/M2 observations. Internal promise
jobs are deterministic state transitions, not decisions. The global interleaving
relation and host embedding remain open; this is not a fixed-fuel denotation.
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

/-- Empty external derivations identify their endpoints; no internal jobs are implied. -/
theorem steps_nil_iff (s t : State α ε) : Steps s [] t ↔ s = t := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; exact .nil s

/-- A nonempty derivation has exactly its first transition and remaining derivation. -/
theorem steps_cons_iff (s t : State α ε) (d : Decision α ε) (ds : List (Decision α ε)) :
    Steps s (d :: ds) t ↔ ∃ mid, Step s d mid ∧ Steps mid ds t := by
  constructor
  · intro h; cases h with | cons first rest => exact ⟨_, first, rest⟩
  · rintro ⟨mid, first, rest⟩; exact .cons first rest

/-- Finite relational composition, independent of fuel and valid under either local mask. -/
theorem steps_append_iff (s t : State α ε) (left right : List (Decision α ε)) :
    Steps s (left ++ right) t ↔ ∃ mid, Steps s left mid ∧ Steps mid right t := by
  induction left generalizing s with
  | nil => simp [steps_nil_iff]
  | cons d ds ih =>
      simp only [List.cons_append, steps_cons_iff, ih]
      constructor
      · rintro ⟨mid, first, endpoint, before, after⟩
        exact ⟨endpoint, ⟨mid, first, before⟩, after⟩
      · rintro ⟨endpoint, ⟨mid, first, before⟩, after⟩
        exact ⟨mid, first, endpoint, before, after⟩

end Whatwg.Streams.Readable
