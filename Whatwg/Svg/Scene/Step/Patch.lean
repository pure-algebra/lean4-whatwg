import Whatwg.Svg.Scene.Step
import Whatwg.Svg.Scene.Patch.Laws

/-!
# Whatwg.Svg.Scene.Step.Patch

Owner: the patch of a step (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A step of `Whatwg/Svg/Scene/Step.lean` holds a key, the picture before and the picture after.
Its tracks say how each thing looks on the way. This module says what a store that keeps the
old picture does to hold the new one: the patch of `Whatwg/Svg/Scene/Patch.lean` between the
two pictures of the step.

- `Step.patch s`: the patch from the step's old picture to its new one.
- `Step.apply_patch`: applied to the old picture it gives the new one, where the keys of the
  new picture are distinct.
- `Step.apply_patch_next`: the patch of a step and the patch of the step after it
  (`Step.next`), as one patch, take the first picture to the third.
- `Step.apply_patch_interrupt`: the patch of a step that interrupts another
  (`Step.interrupt`) starts from the things drawn at that moment, the things that were leaving
  too, and gives the picture asked for.
- `Step.drop_mem_patch`: the patch drops a key exactly when a thing with it is in the exit of
  the step's join. `Step.patch_of_still`: a step from a picture to itself has the empty patch.

What this module does not claim: when a store does the drops. `Step.drawn` shows the things
that leave until the step's end, so a store that draws the way drops them then and not at the
step's start; no law here orders the two.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Step

variable {α κ δ : Type} [DecidableEq κ] [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α]
  [DecidableEq α]

/-- **The patch of a step**: what a store that keeps the old picture does to hold the new
one. -/
def patch (s : Step α κ) : Patch κ α δ := diff s.key s.old s.new

/-- **The patch of a step, applied to its old picture, is its new picture**, where the keys of
the new picture are distinct. -/
theorem apply_patch (s : Step α κ) (h : Distinct s.key s.new) :
    (s.patch : Patch κ α δ).apply s.key s.old = s.new :=
  apply_diff s.key s.old h

/-- **Two steps in a row are one patch.** The patch of a step and then the patch of the step
after it take the first picture to the third. -/
theorem apply_patch_next (s : Step α κ) (newer : List α) (plan : Plan α)
    (h : Distinct s.key s.new) (hn : Distinct s.key newer) :
    ((s.patch : Patch κ α δ) ++ (s.next newer plan).patch).apply s.key s.old = newer :=
  apply_append_diff s.key s.old h hn

/-- **The patch of a step that interrupts another** starts from the things drawn at the moment
of the interruption, and gives the picture asked for. -/
theorem apply_patch_interrupt (s : Step α κ) (t : Nat) (newer : List α)
    (settle : α → Transition) (shape : α → Option (List ICubic)) (plan : Plan α)
    (hn : Distinct s.key newer) :
    ((s.interrupt t newer settle shape plan).patch : Patch κ α δ).apply s.key (s.drawn t) =
      newer :=
  apply_diff s.key (s.drawn t) hn

/-- **The patch drops a key exactly when a thing with it exits.** -/
theorem drop_mem_patch (s : Step α κ) (k : κ) :
    Patch.Op.drop k ∈ (s.patch : Patch κ α δ).ops ↔ ∃ o ∈ s.join.exit, s.key o = k :=
  drop_mem_diff s.key s.old s.new k

/-- **A step from a picture to itself has the empty patch.** -/
theorem patch_of_still (s : Step α κ) (h : s.new = s.old) :
    (s.patch : Patch κ α δ) = Patch.empty := by
  show (diff s.key s.old s.new : Patch κ α δ) = Patch.empty
  rw [h]
  exact diff_self s.key s.old

end Step

end Whatwg.Svg.Scene
