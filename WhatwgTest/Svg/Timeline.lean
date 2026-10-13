import Whatwg.Svg.Scene.Timeline

/-!
# WhatwgTest.Svg.Timeline

lean4-effect4's writing of lines, one a little after the other, on `Motion.later` of
`Whatwg/Svg/Scene/Timeline.lean`.

The consumer's sampler (`lineAt` of `tools/Tools/View/Motion.lean`, read at `6ad8f7b8d`) gives a
line that is written the part `(c.write.after (i * c.stagger)).at t`, where `i` counts the lines
written before it. The port `WhatwgTest/Html/SvgMotion.lean` leaves the lines out. Here they are
tracks: line `i` has one track that reveals it, started `i` staggers later, and the step holds
the tracks inside itself. The consumer's arithmetic is typed below as the consumer has it, for
its default numbers in per mille of its step (`write` after `300` for `300`, a stagger of `60`).

The guard is a finite evaluation over thirteen lines and every moment of a step. Thirteen is
where the stagger passes the step's end: the last lines start at the end, and are cut.
-/

namespace WhatwgTest.Svg.Timeline

open Whatwg.Svg.Scene

/-- The consumer's `write`, in per mille of its step: 180 ms and 180 ms of 600, linear. -/
def write : Transition := { delay := 300, duration := 300 }

/-- The consumer's stagger, in per mille of its step: 36 ms of 600. -/
def stagger : Nat := 60

/-- **The tracks of `n` lines that write themselves**, each a stagger after the one before:
line `i` is its one track, started `i` staggers later. -/
def written (n : Nat) : Motion Nat :=
  (List.range n).flatMap fun i => Motion.later [⟨i, .reveal 0 1000, write⟩] (i * stagger)

/-- The consumer's `Transition.at` for a linear easing: the share of the duration that has
passed, rounded down to a per mille. -/
def consumerAt (delay duration t : Nat) : Int :=
  if delay + duration ≤ t then 1000
  else if t ≤ delay then 0
  else (((t - delay) * 1000 / duration : Nat) : Int)

/-- The consumer's `Transition.after` and `within`: a delay made longer, held inside the step. -/
def consumerAfter (delay duration d : Nat) : Nat × Nat :=
  (min (delay + d) 1000, min duration (1000 - min (delay + d) 1000))

/-- The consumer's `lineAt`: how much of the `i`-th line that is written is written at `t`. -/
def consumerReveal (i t : Nat) : Int :=
  consumerAt (consumerAfter write.delay write.duration (i * stagger)).1
    (consumerAfter write.delay write.duration (i * stagger)).2 t

-- The consumer's thirteen lines at every moment of the step: the part of each that is written
-- is what the kit's tracks show, held inside the step.
#guard (List.range 13).all fun i => (List.range 1001).all fun t =>
  ((written 13).within.frame i t).part == consumerReveal i t

-- A control of the cut: the last line starts at the step's end, and without the cut it is not
-- written at the end.
#guard ((written 13).frame 12 1000).part == 0 && ((written 13).within.frame 12 1000).part == 1000

/-- The track of one line that writes itself. -/
def one : Motion Nat := [⟨0, .reveal 0 1000, write⟩]

-- A control of what the module does not claim: the cut at the step's end does not commute with
-- a later start. A track cut and then started later ends after the step.
#guard ((one.later 800).within).finish == 1000 && (one.within.later 800).finish == 1400

end WhatwgTest.Svg.Timeline
