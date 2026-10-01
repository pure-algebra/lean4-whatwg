import Whatwg.Streams
import WhatwgTest.Audit.Freeze

/-!
Breaker-owned W8a battery, part two: the twelve bridges that join each
calculus to the transition kernel `Whatwg.Streams.Kernel`.

Contract: `test/contracts/transition-kernel.contract.md`, section 4.
Design: `docs/research/2026-10-01-w8-transition-kernel-design.md`, section
3.2. Ruling: R-W4 (Route B: every per-calculus inductive stays).
Declared red: `test/fixtures/trust-gate/known-red.txt`.

Each bridge is a receipt on the semantics edge of its calculus graph:
READABLE-PG-DEFAULT, WRITABLE-PG-DEFAULT, TRANSFORM-PG-BACKPRESSURE,
PIPING-PG-FORWARD-SHUTDOWN and CONFIGURATION-PG-ORDERING. Every bridge between
a calculus and the kernel is an `↔` (or, for Readable's one-step relation, an
equation of relations), never a one-way implication.

The one-step bridges of the four two-stage calculi are pointwise `↔`, not
equations of relations: `Step` matches on the label inside its own body and
the elaborator does not identify that matcher with `Kernel.stage`'s at an open
label (counterexample `WS-KERNEL-CE-004`). Readable's `Step` is literally the
graph of `step`, so its bridge is the equation.

Per-calculus exclusivity is not ascribed: it is false for the local Writable
machine (`WS-KERNEL-CE-002`). Only the configuration's `Ordering.exclusive`
is, which is the existing `tick_decide_exclusive` in the kernel's form.

The builder must not change a statement in this file.
-/

set_option autoImplicit false
open Whatwg.Streams

/-! ## Readable (READABLE-PG-DEFAULT) -/

#whatwg_freeze (@Readable.step_eq_graph :
  ∀ {α ε : Type}, @Readable.Step α ε = Kernel.Graph (@Readable.step α ε)) axioms [propext, Quot.sound]

#whatwg_freeze (@Readable.steps_iff_path :
  ∀ {α ε : Type} {s t : Readable.State α ε} {ds : List (Readable.Decision α ε)},
    Readable.Steps s ds t ↔ Kernel.Path Readable.Step s ds t) axioms [propext, Quot.sound]

/-! ## Writable (WRITABLE-PG-DEFAULT) -/

#whatwg_freeze (@Writable.step_iff_stage :
  ∀ {α ε : Type} (s : Writable.State α ε) (d : Option (Writable.Decision α ε))
    (t : Writable.State α ε),
    Writable.Step s d t ↔
      Kernel.Graph (Kernel.stage (@Writable.tick α ε) (@Writable.decide α ε)) s d t) axioms [propext, Quot.sound]

#whatwg_freeze (@Writable.reaches_iff_path :
  ∀ {α ε : Type} {s t : Writable.State α ε} {ds : List (Option (Writable.Decision α ε))},
    Writable.Reaches s ds t ↔ Kernel.Path Writable.Step s ds t) axioms [propext, Quot.sound]

/-! ## Transform (TRANSFORM-PG-BACKPRESSURE) -/

#whatwg_freeze (@Transform.step_iff_stage :
  ∀ {α β ε : Type} (s : Transform.State α β ε)
    (d : Option (Transform.Decision α β ε)) (t : Transform.State α β ε),
    Transform.Step s d t ↔
      Kernel.Graph (Kernel.stage (@Transform.tick α β ε) (@Transform.decide α β ε)) s d t) axioms [propext, Quot.sound]

#whatwg_freeze (@Transform.reaches_iff_path :
  ∀ {α β ε : Type} {s t : Transform.State α β ε}
    {ds : List (Option (Transform.Decision α β ε))},
    Transform.Reaches s ds t ↔ Kernel.Path Transform.Step s ds t) axioms [propext, Quot.sound]

/-! ## Piping (PIPING-PG-FORWARD-SHUTDOWN) -/

#whatwg_freeze (@Piping.step_iff_stage :
  ∀ {α ε : Type} (s : Piping.State α ε) (d : Option (Piping.Decision α ε))
    (t : Piping.State α ε),
    Piping.Step s d t ↔
      Kernel.Graph (Kernel.stage (@Piping.tick α ε) (@Piping.decide α ε)) s d t) axioms [propext, Quot.sound]

#whatwg_freeze (@Piping.reaches_iff_path :
  ∀ {α ε : Type} {s t : Piping.State α ε} {ds : List (Option (Piping.Decision α ε))},
    Piping.Reaches s ds t ↔ Kernel.Path Piping.Step s ds t) axioms [propext, Quot.sound]

/-! ## The configuration (CONFIGURATION-PG-ORDERING) -/

#whatwg_freeze (@Semantics.Ordering.step_iff_stage :
  ∀ {α ε : Type} (s : Semantics.Ordering.Config α ε)
    (d : Option (Semantics.Ordering.Decision α ε)) (t : Semantics.Ordering.Config α ε),
    Semantics.Ordering.Step s d t ↔
      Kernel.Graph
        (Kernel.stage (@Semantics.Ordering.tick α ε) (@Semantics.Ordering.decide α ε)) s d t) axioms [propext, Quot.sound]

#whatwg_freeze (@Semantics.Ordering.reaches_iff_path :
  ∀ {α ε : Type} {s t : Semantics.Ordering.Config α ε}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.Reaches s ds t ↔ Kernel.Path Semantics.Ordering.Step s ds t) axioms [propext, Quot.sound]

-- An episode prefix is a kernel derivation of the one-step relation restricted
-- to sources that are not a checkpoint: `EpisodePrefix.cons` takes the guard
-- and the step as two hypotheses, so it stays an inductive under any route.
#whatwg_freeze (@Semantics.Ordering.episodePrefix_iff_path :
  ∀ {α ε : Type} {s t : Semantics.Ordering.Config α ε}
    {ds : List (Option (Semantics.Ordering.Decision α ε))},
    Semantics.Ordering.EpisodePrefix s ds t ↔
      Kernel.Path
        (fun (c : Semantics.Ordering.Config α ε)
            (d : Option (Semantics.Ordering.Decision α ε))
            (u : Semantics.Ordering.Config α ε) =>
          c.active ≠ Semantics.Ordering.Active.checkpoint ∧ Semantics.Ordering.Step c d u)
        s ds t) axioms [propext, Quot.sound]

-- Decision 7 of the configuration as the kernel's exclusivity; the hypothesis
-- under which the two Decision-8 laws of `Semantics/Runs.lean` become
-- corollaries of `Kernel.prefix_comparable` and `Kernel.normalized_unique`.
#whatwg_freeze (@Semantics.Ordering.exclusive :
  ∀ {α ε : Type},
    Kernel.Exclusive (@Semantics.Ordering.tick α ε) (@Semantics.Ordering.decide α ε)) axioms [propext, Quot.sound]
