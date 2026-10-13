import Whatwg.Svg.Scene.Frame
import Whatwg.Svg.Scene.Stage
import Whatwg.Html.Node.SvgMotion

/-!
# WhatwgTest.Html.SvgMotion

The motion of a step of lean4-effect4 on the kit's motion as data (slice S13 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-71). The step is one `Plan` since slice S14. Since slice
S15 the kit has a reader (`Whatwg/Svg/Scene/Frame.lean`) and a step in stages
(`Whatwg/Svg/Scene/Stage.lean`), and this port is on both. The consumer is read at its checkout
`707b9a01`: the sections "Easing", "Transitions" and "The choreography" of
`tools/Tools/View/Look.lean`, and the join, the layout of a moment and the end laws of
`tools/Tools/View/Motion.lean`. This module imports nothing of that package.

The kit owns the mechanism of motion, and lean4-effect4's own port is written from this file. So
the file has three kinds of thing, and says which is which.

**What a real port copies.** Four things, each short.

1. *The plan* (`plan`): one `Plan` that says what each thing of a step does. It settles
   (`plan_settles`), and it is proper where the choreography is (`plan_proper`). The motion of a
   step is `Motion.ofJoin` of the plan, held in its step (`motion`).
2. *The reader* (`sample`): `Join.drawn` says which things are drawn at a moment, and
   `Motion.frame` says what each looks like. A port writes no reader of its own. Where a kept
   thing stands at a moment is read from its frame (`kept_place`, by `Motion.frame_shift`). That
   law asks that no thing has two tracks of one property (`Motion.Single`). A port shows that
   its plan gives each thing one change for each property (`plan_single`), and the kit gives the
   rest: `motion_single` is `Motion.single_ofJoin`, held in its step by `Motion.Single.within`.
3. *The end law* (`sample_end`): at the step's end the sample is the new scene, each thing with
   a frame at rest. It follows from `Motion.ofJoin_end` and `Motion.frame_atRest`.
4. *The staged step* (`stagedPlan`, `stagedMotion`): the same things and the same changes on
   `Motion.staged`, with the consumer's two entrances as parts of a level's window and its own
   durations as caps (`Transition.atMost`). The kit's laws of a staged step are then laws of the
   port, one line each: the kept things first (`staged_kept_first`), at rest from the moment the
   new things enter (`staged_kept_rest`), level by level (`staged_levels`), the last picture
   (`staged_end`), and one track for each property (`stagedMotion_single`, which is
   `Motion.staged_single` of `stagedPlan_single`).

**What is the consumer's code, restated.** The easings and their two tables (`Ease`, `Ease.at`,
`tableAt`, `Ease.points`), the timing of a transition (`Ease.timed`), the writing of a number
(`decimal`, `Ease.css`), the choreography and its numbers (`Choreography`, `Choreography.norm`),
and the arithmetic of a step (`levels`, `slot`, `entrance`, `lateness`). They are here under the
consumer's names as the reference of the guards. `motion` is the consumer's choreography as its
sampler has it today, number for number: it is the record of what the consumer's code does. A
real port has all of this already and copies none of it.

**What the port cites from the kit.** No lemma of lists or of plans is proved here. The file
cites, each under the kit's own name:

- `Plan.Single`, `Plan.moving_single` and `Motion.single_ofJoin` of
  `Whatwg/Svg/Scene/Plan.lean`: a plan with one change for each property gives a step with one
  track for each property, where the keys of each scene are distinct;
- `Motion.Single.within` and `Motion.frame_shift` of `Whatwg/Svg/Scene/Frame.lean`: the step held
  in itself is still so, and the frame of a thing then shows the pose of its track;
- `Motion.staged_single` of `Whatwg/Svg/Scene/Stage.lean`: the same for a step in stages.

Until slice S16 this file carried seven such lemmas of its own. They are in the kit now, or the
kit's laws say more: `single_of_keys`, `single_within` and `single_of_untimed` are
`Motion.single_of_keys`, `Motion.Single.within` and `Motion.single_of_untimed`; `nodup_append_of`
is in `Whatwg/Svg/Scene/Join/Laws.lean`; and `ofJoin_single`, with its two helpers
`keys_sublist` and `map_filterMap_sublist`, gave way to `Motion.single_ofJoin`, which asks for
one change for each property and not for one change at most.

**The two steps, and what they differ in.** `motion` and `stagedMotion` move the same things by
the same changes and the same easings. They differ in when.

- *The new things* have the same delays and the same durations in both, at every number of
  levels: the staged step's shares of a window are the consumer's per cents, and the caps are
  the consumer's `min`.
- *The first stage* differs at the consumer's defaults. The consumer's kept things move for 450
  of a thousand, and its first new thing starts at 300. So its kept things are still moving when
  a new thing appears (debt D131 of `COORDINATION.md`). `Motion.staged` ends the first stage by
  the moment the new things enter: in the five-thing step the kept box moves for 300 and not for
  450. Which of the two numbers gives way is the look's to say. With the new things from 450 on
  (270 ms of the step's 600), the two steps are equal track for track, and a guard says so.
- *What the staged step buys* is the four laws above. The consumer's step has none of the first
  three: its arithmetic is inside its sampler, and no theorem is about it.

| The consumer's | Here |
| --- | --- |
| `lerp`, `lerp_end` | `mix`, `mix_end` |
| `Ease`, `Ease.at` | `Easing`, `Easing.at`, by `Ease.kit` |
| `tableAt` | `Easing.stopsAt`: `stopsAt_table` |
| `Ease.points`, `Ease.css` | `Easing.sampled`, `Easing.css`: `sampled_points` |
| `Ease.at_start`, `Ease.at_end` | `Easing.Proper`: `Ease.kit_proper` |
| `Transition` and its `at`, `within`, `after`, `per` | the kit's, under the same names |
| `Transition.at_end` | `Transition.at_done_proper` |
| `Transition.within_end`, `within_at_end`, `after_at_end` | the kit's, under the same names |
| `Join`, `join`, `join_new`, `join_old` | the kit's, for a key of any type |
| `Choreography`, `Choreography.norm` | the same, of kit transitions, by `Transition.per` |
| `placedAt`, `routeAt` | the tracks that `plan` gives the new scene, read by `Motion.frame` |
| `levels`, `slot`, `start` | `levels`, `slot`, `lateness`; staged: `Motion.slot`, `rank` |
| `drawAt`, `expandAt` | `entrance`, started later by `lateness`; staged: two parts of a window |
| `gone`, `retracting` | the plan's `leave`, and `Join.drawn` |
| `sampleLaid` | `motion`, the tracks of the step, and `sample`, their reading |
| `Laid.AtRest` | `Frame.AtRest` |
| `placedAt_end`, `routeAt_end`, `sampleLaid_end` | `motion_end`, `sample_end` |

**The easings.** Four of the seven read as the consumer's at every moment. `linear` is
`Easing.linear` (`kit_linear`, up to `1000`), `in_` is `Easing.cubicIn` (`kit_in`), and
`settle` and `spring` are the stops of the consumer's two tables (`kit_settle`, `kit_spring`):
each is a theorem. The other three differ, and a guard over every moment `0 … 1000` says by how
much; no theorem states it.

- `out` is `Easing.cubicOut`. The kit reads one less than the consumer at 990 moments, and the
  same at the others. Each rounds once: with `x` the cube of what remains, the kit rounds
  `1000 - x` down, and the consumer rounds `x` down.
- `outBack` is `Easing.backOut`. The two differ by one per mille at most, either way. The kit's
  first height is `1567` for the overshoot `1.70158`, and the consumer's formula has `2702` and
  `1702`.
- `inOut` is two cubics, and no one cubic. It is `Easing.sampled` of the consumer's formula:
  twenty-one stops with straight lines between them, which is what the consumer writes to CSS
  (`sampled_points`). Between two stops it is up to five per mille off the formula.

**How the kit differs from the consumer.**

- *A step is tracks.* The consumer's moment is a layout whose things have fields: a place, a
  growth, a part drawn. Here a step is the new scene and one track for each change, so a
  browser can draw the moments from CSS (`Motion.sheet`, `Motion.style?`). `sample` reads the
  tracks back with the kit's reader, and `fields` writes a frame in the consumer's fields for
  the guards.
- *The share of a duration.* The consumer rounds the share that has passed to a per mille and
  then reads its easing. The kit reads the easing at the share itself (`Easing.of`). On the
  consumer's default choreography the two readings differ by three per mille at most.
- *The end of an easing.* The consumer's transition reads `1000` once it is over, whatever its
  easing. The kit's reads the end of its easing, and an easing of the kit is any list of stops.
  So the end law asks that the easings be proper (`Choreography.Proper`), which the consumer's
  seven are (`Ease.kit_proper`).
- *A kept route.* The consumer draws a kept route whole at its new place from the step's
  start. Here a kept thing whose place changed has a track, so a kept route moves with its
  target. A kept thing that stands where it stood has no track.
- *A route that leaves.* The consumer's retracts toward its source. The plan here shrinks
  every thing that leaves.
- *The default easing.* A transition of the consumer eases in and out where none is named. A
  transition of the kit is then linear. No default of the choreography leaves it unnamed.

**What is not ported.** The lines of a page (`lineAt`, `sampleLines`), so `write` and `stagger`
are numbers of the choreography that no track here reads. `Ease.bezier`, the nearest cubic to
an easing: the kit writes a cubic as it is. The width and the height of a layout. In the staged
step, the choreography's own delay of a draw and of a growth, which the consumer's defaults
leave at `0`.

**What this file does not show.** That the frame at the step's end is `Frame.rest` itself: it is
at rest, and that it has no shape of a track needs a law of motions with no change of shape,
which the kit does not have yet. That the staged step is over at the step's end with no cut:
`Motion.staged_end` asks that each new thing's rank is below the number of levels, and here the
rank is a place in a sorted list, so `staged_end` cuts the step and asks nothing.

**The guards.** Each is a finite evaluation: the spread of each easing against the consumer's
formula, the timing of each default transition against the consumer's, the numbers of the
default choreography in per mille, a step of five things at three of its moments, the two steps
side by side, and the CSS of the consumer's step. The CSS is text written by rule; no browser
read it here.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/
namespace WhatwgTest.Html.SvgMotion

open Whatwg.Html
open Whatwg.Svg.Scene

/-! ## Easing -/

/-- The consumer's easings, by name. -/
inductive Ease where
  | linear | in_ | out | inOut | outBack | settle | spring
  deriving DecidableEq, Repr

/-- The consumer's critically damped spring, in per mille at every twentieth of the step. -/
def settleTable : List Int :=
  [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992, 995,
    998, 1000]

/-- The consumer's underdamped spring, in per mille at every twentieth of the step. -/
def springTable : List Int :=
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019,
    1012, 1007, 1003, 1000]

/-- The consumer's `tableAt`: a table read at `p` per mille, on the line between its two
nearest entries. -/
def tableAt (t : List Int) (p : Nat) : Int :=
  let a := t.getD (p / 50) 1000
  let b := t.getD (p / 50 + 1) 1000
  a + (b - a) * ((p % 50 : Nat) : Int) / 50

/-- The consumer's `Ease.at`, formula by formula: the reference of this port. -/
def Ease.at : Ease → Nat → Int
  | .linear, p => p
  | .in_, p => (p : Int) ^ 3 / 1000000
  | .out, p => 1000 - (1000 - (p : Int)) ^ 3 / 1000000
  | .inOut, p =>
    if p < 500 then 4 * (p : Int) ^ 3 / 1000000
    else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000
  | .outBack, p =>
    let q : Int := (p : Int) - 1000
    1000 + 2702 * q ^ 3 / 1000000000 + 1702 * q ^ 2 / 1000000
  | .settle, p => tableAt settleTable p
  | .spring, p => tableAt springTable p

/-- The consumer's `Ease.points`: the easing at every twentieth of its progress. -/
def Ease.points (e : Ease) : List Int := (List.range 21).map fun i => e.at (i * 50)

/-- The consumer's `Ease.all`. -/
def Ease.all : List Ease := [.linear, .in_, .out, .inOut, .outBack, .settle, .spring]

/-- **Each easing of the consumer as an easing of the kit.** Three are cubics that the kit
names, two are the stops of the consumer's tables, and `inOut`, which is no one cubic, is the
consumer's formula at twenty-one stops. -/
def Ease.kit : Ease → Easing
  | .linear => Easing.linear
  | .in_ => Easing.cubicIn
  | .out => Easing.cubicOut
  | .inOut => Easing.sampled (Ease.at .inOut)
  | .outBack => Easing.backOut
  | .settle => .stops settleTable
  | .spring => .stops springTable

/-- The least and the greatest of the kit's reading less the consumer's, over every moment
`0 … 1000`. -/
def Ease.spread (e : Ease) : Int × Int :=
  let ds := (List.range 1001).map fun p => e.kit.at p - e.at p
  (ds.foldl min 0, ds.foldl max 0)

/-- At how many of the moments `0 … 1000` the kit's reading is not the consumer's. -/
def Ease.misses (e : Ease) : Nat :=
  ((List.range 1001).filter fun p => e.kit.at p != e.at p).length

-- Each easing against the consumer's formula: the same at every moment for four, one less at
-- most for `out`, one either way for `outBack`, and five at most for `inOut` between its stops.
#guard Ease.all.map Ease.spread == [(0, 0), (0, 0), (-1, 0), (-5, 4), (-1, 1), (0, 0), (0, 0)]

-- At how many of the 1001 moments each differs.
#guard Ease.all.map Ease.misses == [0, 0, 990, 755, 425, 0, 0]

/-- The kit's linear easing is the consumer's, up to the end. Past `1000` the kit holds the
end, and the consumer goes on. -/
theorem kit_linear (p : Nat) (h : p ≤ 1000) : (Ease.kit .linear).at p = Ease.at .linear p := by
  rcases Nat.lt_or_ge p 1000 with hlt | hge
  · have hi : p * 1 / 1000 = 0 := by omega
    show ([0, 1000] : List Int).getD (p * 1 / 1000) 1000 +
      (([0, 1000] : List Int).getD (p * 1 / 1000 + 1) 1000 -
        ([0, 1000] : List Int).getD (p * 1 / 1000) 1000) *
        ((p * 1 - 1000 * (p * 1 / 1000) : Nat) : Int) / 1000 = (p : Int)
    rw [hi]
    show (0 : Int) + (1000 - 0) * ((p * 1 - 1000 * 0 : Nat) : Int) / 1000 = (p : Int)
    omega
  · cases Nat.le_antisymm h hge
    rfl

/-- The kit's cubic that is slow at first is the consumer's `in_`, at every progress. -/
theorem kit_in (p : Nat) : (Ease.kit .in_).at p = Ease.at .in_ p := by
  show (3 * 0 * (p : Int) * (1000 - (p : Int)) ^ 2 + 3 * 0 * (p : Int) ^ 2 * (1000 - (p : Int)) +
    1000 * (p : Int) ^ 3) / 1000000000 = (p : Int) ^ 3 / 1000000
  simp only [Int.mul_zero, Int.zero_mul, Int.zero_add]
  exact Int.mul_ediv_mul_of_pos (a := 1000) ((p : Int) ^ 3) 1000000 (by decide)

/-- **The kit's stops read a table of twenty-one values as the consumer's `tableAt` does**, at
every progress: twenty pieces of fifty per mille each. -/
theorem stopsAt_table (t : List Int) (p : Nat) (hl : t.length - 1 = 20)
    (hlast : t.getLast?.getD 0 = 1000) : Easing.stopsAt t p = tableAt t p := by
  have hi : p * 20 / 1000 = p / 50 := by omega
  have hr : ((p * 20 - 1000 * (p / 50) : Nat) : Int) = 20 * ((p % 50 : Nat) : Int) := by omega
  show t.getD (p * (t.length - 1) / 1000) (t.getLast?.getD 0) +
    (t.getD (p * (t.length - 1) / 1000 + 1) (t.getLast?.getD 0) -
      t.getD (p * (t.length - 1) / 1000) (t.getLast?.getD 0)) *
      ((p * (t.length - 1) - 1000 * (p * (t.length - 1) / 1000) : Nat) : Int) / 1000 =
    t.getD (p / 50) 1000 +
      (t.getD (p / 50 + 1) 1000 - t.getD (p / 50) 1000) * ((p % 50 : Nat) : Int) / 50
  rw [hl, hlast, hi, hr, Int.mul_left_comm]
  generalize (t.getD (p / 50 + 1) 1000 - t.getD (p / 50) 1000) * ((p % 50 : Nat) : Int) = x
  omega

/-- The kit's stops of the consumer's first table are the consumer's `settle`. -/
theorem kit_settle (p : Nat) : (Ease.kit .settle).at p = Ease.at .settle p :=
  stopsAt_table settleTable p rfl rfl

/-- The kit's stops of the consumer's second table are the consumer's `spring`. -/
theorem kit_spring (p : Nat) : (Ease.kit .spring).at p = Ease.at .spring p :=
  stopsAt_table springTable p rfl rfl

/-- The kit's sample of an easing of the consumer has the consumer's points for its stops. -/
theorem sampled_points (e : Ease) : Easing.sampled e.at = .stops e.points := by
  cases e <;> decide

/-- Every easing of the consumer is proper as an easing of the kit: the consumer's
`Ease.at_start` and `Ease.at_end`. -/
theorem Ease.kit_proper (e : Ease) : e.kit.Proper := by
  cases e <;> decide

/-- The consumer's `decimal`: a number of `10 ^ -places` units, with no trailing zero. -/
def decimal (v : Int) (places : Nat) : String :=
  let unit := 10 ^ places
  let a := v.natAbs
  let frac := toString (a % unit + unit) |>.drop 1 |>.toString
  let frac := (frac.toList.reverse.dropWhile (· == '0')).reverse
  (if v < 0 then "-" else "") ++ toString (a / unit) ++
    (if frac.isEmpty then "" else "." ++ String.ofList frac)

/-- The consumer's `Ease.css`: an easing as `linear()` of CSS at its twenty-one points. -/
def Ease.css (e : Ease) : String :=
  "linear(" ++ ", ".intercalate (e.points.map (decimal · 3)) ++ ")"

-- The kit writes the stops of an easing as the consumer writes its points.
#guard Ease.all.all fun e => (Easing.sampled e.at).css == e.css

-- What the kit writes for three of the seven: a cubic as it is, and two stops as `linear()`.
#guard (Ease.kit .out).css == "cubic-bezier(0.333333, 1, 0.666667, 1)"

#guard (Ease.kit .outBack).css == "cubic-bezier(0.333333, 1.567, 0.666667, 1)"

#guard (Ease.kit .linear).css == "linear(0, 1)"

/-! ## Transitions and the choreography -/

/-- The consumer's `Transition.at`, the reference: the easing `e` after `delay`, for
`duration`, read at the moment `t`. It rounds the share of the duration that has passed to a
per mille, and then reads the easing. -/
def Ease.timed (e : Ease) (delay duration t : Nat) : Int :=
  if delay + duration ≤ t then 1000
  else if t ≤ delay then e.at 0
  else e.at ((t - delay) * 1000 / duration)

/-- The consumer's `Choreography`: how long a step lasts, and the transition of each selection,
in milliseconds, with the consumer's defaults. -/
structure Choreography where
  /-- the length of one step, from one frame to the next -/
  step : Nat := 600
  /-- the kept things move to their new places, and settle there with weight -/
  move : Transition := { duration := 270, ease := Ease.settle.kit }
  /-- the old things shrink -/
  leave : Transition := { duration := 150, ease := Ease.in_.kit }
  /-- a new or changed line writes itself, cell by cell -/
  write : Transition := { delay := 180, duration := 180, ease := Ease.linear.kit }
  /-- the delay from one new line to the next -/
  stagger : Nat := 36
  /-- when the new parts of a graph start, after the room is made -/
  enterFrom : Nat := 180
  /-- a new route draws from its source toward its target -/
  draw : Transition := { duration := 132, ease := Ease.out.kit }
  /-- the box at its end expands out, on a spring -/
  expand : Transition := { duration := 216, ease := Ease.spring.kit }
  deriving DecidableEq, Repr

/-- The consumer's `Choreography.norm`: the choreography in per mille of its step. -/
def Choreography.norm (c : Choreography) : Choreography :=
  { step := 1000, move := c.move.per c.step, leave := c.leave.per c.step,
    write := c.write.per c.step, stagger := c.stagger * 1000 / c.step,
    enterFrom := c.enterFrom * 1000 / c.step, draw := c.draw.per c.step,
    expand := c.expand.per c.step }

/-- A choreography whose easings start at `0` and end at `1000`, for the four transitions that
a track here reads. The consumer's always do, since it has seven easings and each does. Here an
easing is any list of stops. -/
def Choreography.Proper (c : Choreography) : Prop :=
  c.move.ease.Proper ∧ c.leave.ease.Proper ∧ c.draw.ease.Proper ∧ c.expand.ease.Proper

instance (c : Choreography) : Decidable c.Proper :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A choreography in per mille of its step keeps its easings. -/
theorem Choreography.norm_proper (c : Choreography) (h : c.Proper) : c.norm.Proper := h

/-- The consumer's default choreography is proper. -/
theorem proper_default : ({} : Choreography).Proper := by decide

-- The default choreography in per mille of its step of 600 ms.
#guard ({} : Choreography).norm ==
  { step := 1000, move := { duration := 450, ease := Ease.settle.kit },
    leave := { duration := 250, ease := Ease.in_.kit },
    write := { delay := 300, duration := 300, ease := Ease.linear.kit }, stagger := 60,
    enterFrom := 300, draw := { duration := 220, ease := Ease.out.kit },
    expand := { duration := 360, ease := Ease.spring.kit } }

/-- The greatest difference, over every moment of a step, between the kit's reading of a
transition and the consumer's reading of the same delay, duration and easing. -/
def Ease.timingGap (e : Ease) (tr : Transition) : Nat :=
  ((List.range 1001).map fun t => (tr.at t - e.timed tr.delay tr.duration t).natAbs).foldl max 0

-- The default transitions, read by the kit and by the consumer: `move`, `leave`, `write`,
-- `draw` and `expand`. The kit reads its easing at the share of the duration itself.
#guard
  let c := ({} : Choreography).norm
  [Ease.settle.timingGap c.move, Ease.in_.timingGap c.leave, Ease.linear.timingGap c.write,
    Ease.out.timingGap c.draw, Ease.spring.timingGap c.expand] == [3, 0, 0, 1, 3]

/-! ## The step -/

/-- What a thing is: the consumer's `Placed` is a box, and its `Route` is a route. -/
inductive Kind where
  | box | route
  deriving DecidableEq, Repr

/-- A thing of a scene: its key, its place, and what it is. A route's place is its target's,
as the consumer's `targetY` reads it. -/
structure Thing where
  key : String
  place : IVec
  kind : Kind := .box
  deriving DecidableEq, Repr

/-- The levels of the new things, from the top: the consumer's `levels`. -/
def levels (entering : List Thing) : List Int :=
  ((entering.map fun n => n.place.y).eraseDups).mergeSort (· ≤ ·)

/-- The time that each level has: the consumer's `slot`. -/
def slot (c : Choreography) (ls : List Int) : Nat :=
  if ls.isEmpty then 0 else (1000 - c.enterFrom) / ls.length

/-- **How a new thing enters**: a route draws itself and a box grows, each for as long as its
level's slot leaves it. They are the consumer's `drawAt` and `expandAt`, before their delay. -/
def entrance (c : Choreography) (ls : List Int) (n : Thing) : Change × Transition :=
  match n.kind with
  | .route =>
    (.reveal 0 1000, { c.draw with duration := min c.draw.duration (slot c ls * 45 / 100) })
  | .box =>
    (.grow 0 1000, { c.expand with duration := min c.expand.duration (slot c ls * 60 / 100) })

/-- **How much later a new thing enters**: level by level from the top, a route at the start of
its level's slot and a box two fifths into it. It is the consumer's `start`, and the delay that
it gives `drawAt` and `expandAt`. -/
def lateness (c : Choreography) (ls : List Int) (n : Thing) : Nat :=
  c.enterFrom + ls.findIdx (· == n.place.y) * slot c ls +
    match n.kind with
    | .route => 0
    | .box => slot c ls * 40 / 100

/-- **The plan of a step**: what each thing of a join does. It is the consumer's `placedAt` and
`routeAt` over the new layout, and its `gone` and `retracting`. A kept thing moves from its old
place by `move`, where its place changed. A new route draws itself and a new box grows, each
started at its level's time. An old thing shrinks by `leave`. -/
def plan (c : Choreography) (j : Join Thing) : Plan Thing where
  kept := Plan.moving Thing.place c.move
  enter := fun n =>
    let e := entrance c (levels j.enter) n
    [(e.1, { e.2 with delay := e.2.delay + lateness c (levels j.enter) n })]
  leave := fun _ => [(.grow 1000 0, c.leave)]

/-- **The motion of a step** from an old scene to a new one, in the choreography's per mille
of its step: what the consumer's `sampleLaid` samples. -/
def motion (c : Choreography) (old new : List Thing) : Motion String :=
  (Motion.ofJoin Thing.key (join Thing.key old new)
    (plan c.norm (join Thing.key old new))).within

/-- A new thing enters by a transition of the choreography, so by a proper easing. -/
theorem entrance_proper (c : Choreography) (ls : List Int) (n : Thing) (h : c.Proper) :
    (entrance c ls n).2.ease.Proper := by
  cases n with
  | mk key place kind =>
    cases kind with
    | box => exact h.2.2.2
    | route => exact h.2.2.1

/-- A new thing enters by a change that ends at rest: a route drawn whole, a box at its whole
size. -/
theorem entrance_settles (c : Choreography) (ls : List Int) (n : Thing) :
    (entrance c ls n).1.stop.AtRest := by
  cases n with
  | mk key place kind =>
    cases kind with
    | box => exact rfl
    | route => exact rfl

/-- **The plan of a step settles**: a kept thing ends on its place, a route drawn whole and a
box at its whole size. -/
theorem plan_settles (c : Choreography) (j : Join Thing) : (plan c j).Settles :=
  ⟨Plan.moving_settles Thing.place c.move, fun n _ h =>
    List.mem_singleton.mp h ▸ entrance_settles c (levels j.enter) n⟩

/-- **The plan of a step is proper**, where the choreography is. -/
theorem plan_proper (c : Choreography) (j : Join Thing) (h : c.Proper) : (plan c j).Proper :=
  ⟨Plan.moving_proper Thing.place c.move h.1,
    fun n _ hm => List.mem_singleton.mp hm ▸ entrance_proper c (levels j.enter) n h,
    fun _ _ hm => List.mem_singleton.mp hm ▸ h.2.1⟩

/-- There is one track at most for each thing of the new scene, and none for a kept thing that
stands where it stood. -/
theorem staying_le (c : Choreography) (old new : List Thing) :
    (Motion.staying Thing.key (join Thing.key old new)
      (plan c (join Thing.key old new))).length ≤ new.length := by
  have h := Motion.length_staying_le Thing.key old new (plan c (join Thing.key old new)) 1
    (Plan.length_moving_le Thing.place c.move) (fun _ => Nat.le_refl 1)
  rw [Nat.one_mul] at h
  exact h

/-- **The end law of a step.** At the end of a step every track is at rest, or is of a thing
that the new scene does not have: a kept thing on its place, a route drawn whole, a box at its
whole size. It is the consumer's end law `sampleLaid_end` in the kit's terms, with its two steps
`placedAt_end` and `routeAt_end`; `sample_end` below states it in the consumer's own form. -/
theorem motion_end (c : Choreography) (old new : List Thing) (h : c.Proper) :
    ∀ tr ∈ motion c old new, (tr.at 1000).AtRest ∨ ∀ n ∈ new, n.key ≠ tr.key := by
  intro tr htr
  rw [motion, Motion.ofJoin_within] at htr
  rcases List.mem_append.mp htr with ha | hl
  · exact Or.inl (Motion.staying_end Thing.key _ _ (plan_settles _ _)
      (plan_proper _ _ (c.norm_proper h)) tr ha)
  · obtain ⟨tr0, h0, rfl⟩ := Motion.mem_within _ hl
    obtain ⟨_, _, _, hn⟩ := Motion.mem_leaving_key Thing.key old new _ h0
    exact Or.inr hn

/-! ## One track for each thing

`Motion.frame_shift` reads where a thing stands in a motion where no thing has two tracks of one
property (`Motion.Single`). The kit says when a step is so: its plan gives each thing one change
for each property at most (`Plan.Single`), and the keys of each scene are distinct
(`Motion.single_ofJoin`). Holding the step in itself keeps it so (`Motion.Single.within`). A
port shows `Plan.Single` of its plan, and cites the kit for the rest. -/

/-- **The plan of a step gives each thing one change for each property**: a kept thing its move
or nothing, a new thing its entrance, an old thing its leaving. -/
theorem plan_single (c : Choreography) (j : Join Thing) : (plan c j).Single :=
  ⟨Plan.moving_single Thing.place c.move,
    fun _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

/-- **No thing of a step has two tracks of one property**, where the keys of each scene are
distinct: a kept thing has its move or nothing, a new thing its entrance, an old thing its
leaving. So the frame of a thing shows the pose of each of its tracks. -/
theorem motion_single (c : Choreography) (old new : List Thing) (ho : Distinct Thing.key old)
    (hn : Distinct Thing.key new) : (motion c old new).Single :=
  (Motion.single_ofJoin Thing.key old new _ (plan_single _ _) ho hn).within

/-! ## A moment of a step -/

/-- **The scene at the moment `t` of a step**: the consumer's `sampleLaid`, by the kit's reader.
The things drawn are those of `Join.drawn`: the things that leave come first, until the step's
end, and then the things of the new scene. Each comes with its frame: what `Motion.frame` says
it looks like under the tracks of the step. -/
def sample (c : Choreography) (old new : List Thing) (t : Nat) : List (Thing × Frame) :=
  ((join Thing.key old new).drawn new t).map fun n => (n, (motion c old new).frame n.key t)

/-- A sampled thing in the consumer's fields: its key, where it stands, its growth and how much
of it is drawn. The guards read a sample so. -/
def fields (x : Thing × Frame) : String × IVec × Int × Int :=
  (x.1.key, x.1.place + x.2.shift, x.2.size, x.2.part)

/-- **Where a kept thing stands at a moment**: at the consumer's `lerp` of its old place and its
new one, at the eased progress of the move. It is the consumer's `placedAt`, read from the frame
of the thing by `Motion.frame_shift`. -/
theorem kept_place (c : Choreography) (old new : List Thing) (hs : (motion c old new).Single)
    {o n : Thing} (hu : (o, n) ∈ (join Thing.key old new).update) (hne : o.place ≠ n.place)
    (t : Nat) :
    n.place + ((motion c old new).frame n.key t).shift =
      ⟨mix o.place.x n.place.x (c.norm.move.within.at t),
        mix o.place.y n.place.y (c.norm.move.within.at t)⟩ := by
  have hc : (Change.shift (o.place - n.place) 0, c.norm.move) ∈
      Plan.moving Thing.place c.norm.move o n := by
    rw [Plan.moving_of_ne Thing.place c.norm.move hne]
    exact List.mem_singleton.mpr rfl
  have h0 : (⟨n.key, .shift (o.place - n.place) 0, c.norm.move⟩ : Track String) ∈
      Motion.ofJoin Thing.key (join Thing.key old new) (plan c.norm (join Thing.key old new)) :=
    List.mem_append_left _ ((Motion.mem_staying Thing.key _ _).mpr
      (Or.inl ⟨(o, n), hu, _, hc, rfl⟩))
  have htr : (⟨n.key, .shift (o.place - n.place) 0, c.norm.move.within⟩ : Track String) ∈
      motion c old new := List.mem_map.mpr ⟨_, h0, rfl⟩
  rw [Motion.frame_shift hs htr t]
  exact IVec.ext (mix_shift o.place.x n.place.x _).symm (mix_shift o.place.y n.place.y _).symm

/-- **The consumer's end law, `sampleLaid_end`.** A step's last moment is the next scene: the
things of the new scene and no other, each with a frame at rest, so on its place, at its whole
size and drawn whole. -/
theorem sample_end (c : Choreography) (old new : List Thing) (h : c.Proper) :
    (sample c old new 1000).map Prod.fst = new ∧ ∀ x ∈ sample c old new 1000, x.2.AtRest := by
  have e : sample c old new 1000 =
      new.map fun n => (n, (motion c old new).frame n.key 1000) :=
    congrArg (List.map _) (Join.drawn_end _ new (Nat.le_refl 1000))
  rw [e]
  refine ⟨(List.map_map.trans (List.map_congr_left fun _ _ => rfl)).trans (List.map_id new),
    fun x hx => ?_⟩
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  exact Motion.frame_atRest (Motion.ofJoin_end Thing.key old new _ (plan_settles _ _)
    (plan_proper _ _ (c.norm_proper h)) hn (Nat.le_refl 1000))

/-! ## The staged step

The same things and the same changes on `Motion.staged`. The consumer's sampler gives a new
edge the first 45 per cent of its level's slot and the box at its end the slot from 40 per cent
on, each for the choreography's own duration where that is less. Here each is a part of a
window with a cap, and the arithmetic is the kit's. -/

/-- The levels of the new things of a step, from the top. -/
def stepLevels (old new : List Thing) : List Int := levels (join Thing.key old new).enter

/-- The level of a thing in a step: the place of its row among the levels of the new things. It
is the consumer's `levels.findIdx`. -/
def rank (old new : List Thing) (n : Thing) : Nat :=
  (stepLevels old new).findIdx (· == n.place.y)

/-- How long the window of one level of a step is, in the choreography's per mille. -/
def stepSlot (c : Choreography) (old new : List Thing) : Nat :=
  Motion.slot c.norm.enterFrom (stepLevels old new).length

/-- **The plan of a staged step.** A kept thing and an old thing do what `plan` gives them. A
new route draws in the first 45 per cent of its level's window, and a new box grows from 40 per
cent on, each for the choreography's own duration at most in a window `slot` long. -/
def stagedPlan (c : Choreography) (slot : Nat) : Plan Thing where
  kept := Plan.moving Thing.place c.move
  enter := fun n =>
    match n.kind with
    | .route => [(.reveal 0 1000, ({ delay := 0, duration := 450, ease := c.draw.ease } :
        Transition).atMost c.draw.duration slot)]
    | .box => [(.grow 0 1000, ({ delay := 400, duration := 600, ease := c.expand.ease } :
        Transition).atMost c.expand.duration slot)]
  leave := fun _ => [(.grow 1000 0, c.leave)]

/-- **The staged step** from an old scene to a new one: the kept things and the old things
first, over by the moment the new things enter, and then the new things level by level. -/
def stagedMotion (c : Choreography) (old new : List Thing) : Motion String :=
  Motion.staged Thing.key (join Thing.key old new) (stagedPlan c.norm (stepSlot c old new))
    c.norm.enterFrom (stepLevels old new).length (rank old new)

/-- The first stage of the staged step, as its plan times it: the tracks of the kept things and
of the old things. -/
def stagedFirst (c : Choreography) (old new : List Thing) : Motion String :=
  Motion.firstStage Thing.key (join Thing.key old new) (stagedPlan c.norm (stepSlot c old new))

/-- The tracks of one new thing in the staged step. -/
def stagedOf (c : Choreography) (old new : List Thing) (n : Thing) : Motion String :=
  Motion.stagedOf Thing.key (stagedPlan c.norm (stepSlot c old new)) c.norm.enterFrom
    (stepLevels old new).length (rank old new) n

/-- The plan of a staged step settles, as `plan` does. -/
theorem stagedPlan_settles (c : Choreography) (slot : Nat) : (stagedPlan c slot).Settles :=
  ⟨Plan.moving_settles Thing.place c.move, fun n x h => by
    cases n with
    | mk key place kind =>
      cases kind with
      | box => exact List.mem_singleton.mp h ▸ rfl
      | route => exact List.mem_singleton.mp h ▸ rfl⟩

/-- The plan of a staged step is proper, where the choreography is. -/
theorem stagedPlan_proper (c : Choreography) (slot : Nat) (h : c.Proper) :
    (stagedPlan c slot).Proper :=
  ⟨Plan.moving_proper Thing.place c.move h.1, fun n x hm => by
    cases n with
    | mk key place kind =>
      cases kind with
      | box => exact List.mem_singleton.mp hm ▸ h.2.2.2
      | route => exact List.mem_singleton.mp hm ▸ h.2.2.1,
    fun _ _ hm => List.mem_singleton.mp hm ▸ h.2.1⟩

/-- The plan of a staged step gives each thing one change for each property, as `plan` does. -/
theorem stagedPlan_single (c : Choreography) (slot : Nat) : (stagedPlan c slot).Single :=
  ⟨Plan.moving_single Thing.place c.move, fun n => by
    cases n with
    | mk key place kind =>
      cases kind with
      | box => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
      | route => exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun _ => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩

/-- Each entrance of a staged step fits in its window: its delay and its duration are a
thousand together at most. -/
theorem stagedPlan_fits (c : Choreography) (slot : Nat) (n : Thing) :
    ∀ x ∈ (stagedPlan c slot).enter n, x.2.delay + x.2.duration ≤ 1000 := by
  intro x hx
  cases n with
  | mk key place kind =>
    cases kind with
    | box =>
      rw [List.mem_singleton.mp hx]
      show 400 + min 600 ((c.expand.duration * 1000 + (slot - 1)) / slot) ≤ 1000
      omega
    | route =>
      rw [List.mem_singleton.mp hx]
      show 0 + min 450 ((c.draw.duration * 1000 + (slot - 1)) / slot) ≤ 1000
      omega

/-- A track of the staged step is a track of its first stage, retimed, or a track of a new
thing in the window of its level. The three laws below are of these two kinds of track. -/
theorem mem_stagedMotion (c : Choreography) (old new : List Thing) {tr : Track String} :
    tr ∈ stagedMotion c old new ↔
      (∃ tr0 ∈ stagedFirst c old new,
        tr = tr0.endBy c.norm.enterFrom (stagedFirst c old new).finish) ∨
        ∃ n ∈ (join Thing.key old new).enter, tr ∈ stagedOf c old new n :=
  Motion.mem_staged Thing.key _ _ _ _ _

/-- The staged step moves the things of the step by the changes and the easings of its plan,
track for track: staging changes when a thing moves, and nothing else. -/
theorem stagedMotion_untimed (c : Choreography) (old new : List Thing) :
    (stagedMotion c old new).map Track.untimed =
      (Motion.ofJoin Thing.key (join Thing.key old new)
        (stagedPlan c.norm (stepSlot c old new))).map Track.untimed :=
  Motion.staged_untimed Thing.key _ _ _ _ _

/-- No thing of a staged step has two tracks of one property, where the keys of each scene are
distinct: the kit's reader reads the staged step as it reads the consumer's. -/
theorem stagedMotion_single (c : Choreography) (old new : List Thing)
    (ho : Distinct Thing.key old) (hn : Distinct Thing.key new) :
    (stagedMotion c old new).Single :=
  Motion.staged_single Thing.key old new _ _ _ _ (stagedPlan_single _ _) ho hn

/-- **The kept things first.** Every track of a kept thing and of an old thing is over before
any track of a new thing starts. The consumer's own step does not have this at its defaults. -/
theorem staged_kept_first (c : Choreography) (old new : List Thing) {tr0 y : Track String}
    {n : Thing} (h0 : tr0 ∈ stagedFirst c old new) (hy : y ∈ stagedOf c old new n) :
    (tr0.endBy c.norm.enterFrom (stagedFirst c old new).finish).timing.delay +
      (tr0.endBy c.norm.enterFrom (stagedFirst c old new).finish).timing.duration ≤
        y.timing.delay :=
  Motion.staged_kept_first Thing.key _ _ _ _ _ h0 hy

/-- **The kept things are at rest from the moment the new things enter**: each stands on its
place when the first new thing may appear. -/
theorem staged_kept_rest (c : Choreography) (old new : List Thing) (h : c.Proper)
    {tr0 : Track String}
    (h0 : tr0 ∈ Motion.keeping Thing.key (join Thing.key old new)
      (stagedPlan c.norm (stepSlot c old new))) {t : Nat} (ht : c.norm.enterFrom ≤ t) :
    ((tr0.endBy c.norm.enterFrom (stagedFirst c old new).finish).at t).AtRest :=
  Motion.staged_kept_rest Thing.key _ _ _ (stagedPlan_settles _ _)
    (stagedPlan_proper _ _ (c.norm_proper h)) h0 ht

/-- **Level by level.** A track of a new thing of one level is over before a track of a new
thing of a deeper level starts: nothing appears before the level above it is done. -/
theorem staged_levels (c : Choreography) (old new : List Thing) {n n' : Thing}
    (hr : rank old new n < rank old new n') {x y : Track String}
    (hx : x ∈ stagedOf c old new n) (hy : y ∈ stagedOf c old new n') :
    x.timing.delay + x.timing.duration ≤ y.timing.delay :=
  Motion.staged_levels Thing.key _ _ _ _ hr (stagedPlan_fits _ _ n) hx hy

/-- **The last picture of the staged step.** Held in its step, the staged step shows each thing
of the new scene with a frame at rest at the step's end and after. It asks nothing of the ranks
or of the number of levels. -/
theorem staged_end (c : Choreography) (old new : List Thing) (h : c.Proper) {n : Thing}
    (hn : n ∈ new) {t : Nat} (ht : 1000 ≤ t) :
    ((stagedMotion c old new).within.frame n.key t).AtRest :=
  Motion.frame_atRest (Motion.staged_within_end Thing.key old new _ _ _ _ (stagedPlan_settles _ _)
    (stagedPlan_proper _ _ (c.norm_proper h)) hn ht)

/-! ## A step of five things -/

/-- The scene before: two boxes. -/
def before : List Thing := [⟨"a", ⟨40, 20⟩, .box⟩, ⟨"b", ⟨40, 80⟩, .box⟩]

/-- The scene after: `a` has moved, `b` is gone, and two boxes on two levels have come, the
first with the route that ends at it. -/
def after : List Thing :=
  [⟨"a", ⟨100, 20⟩, .box⟩, ⟨"c", ⟨100, 140⟩, .box⟩, ⟨"a c", ⟨100, 140⟩, .route⟩,
    ⟨"d", ⟨100, 200⟩, .box⟩]

/-- The step between the two, at the consumer's defaults. -/
def fiveStep : Motion String := motion {} before after

/-- The key, the delay and the duration of each track of a motion. -/
def times (m : Motion String) : List (String × Nat × Nat) :=
  m.map fun tr => (tr.key, tr.timing.delay, tr.timing.duration)

/-- Each track of a motion, whole: its key, its change and its transition. -/
def whole (m : Motion String) : List (String × Change × Transition) :=
  m.map fun tr => (tr.key, tr.change, tr.timing)

-- One track for each thing: the kept box, the three new things, and the box that leaves.
-- Level by level from the top: the route at 300, the box at its end at 440, and the box of
-- the second level at 790, which ends with the step.
#guard times fiveStep ==
  [("a", 0, 450), ("c", 440, 210), ("a c", 300, 157), ("d", 790, 210), ("b", 0, 250)]

-- The first moment: the old scene, and the new things not yet there.
#guard (sample {} before after 0).map fields ==
  [("b", ⟨40, 80⟩, 1000, 1000), ("a", ⟨40, 20⟩, 1000, 1000), ("c", ⟨100, 140⟩, 0, 1000),
    ("a c", ⟨100, 140⟩, 1000, 0), ("d", ⟨100, 200⟩, 0, 1000)]

-- Half way: `a` has settled and `b` has shrunk, the route is drawn, its box is growing, and
-- the second level has not started.
#guard (sample {} before after 500).map fields ==
  [("b", ⟨40, 80⟩, 0, 1000), ("a", ⟨100, 20⟩, 1000, 1000), ("c", ⟨100, 140⟩, 768, 1000),
    ("a c", ⟨100, 140⟩, 1000, 1000), ("d", ⟨100, 200⟩, 0, 1000)]

-- Near the end: the box of the second level is past its size, on the spring.
#guard ((sample {} before after 900).map fields).getLast? == some ("d", ⟨100, 200⟩, 1037, 1000)

/-! ### The two steps side by side -/

-- The staged step at the consumer's defaults. The three new things have the consumer's delays
-- and durations. The first stage is over by 300, the moment the new things enter: the kept box
-- moves for 300 and the old box shrinks for 166, where the consumer has 450 and 250.
#guard times (stagedMotion {} before after) ==
  [("a", 0, 300), ("c", 440, 210), ("a c", 300, 157), ("d", 790, 210), ("b", 0, 166)]

-- The tracks of the three new things are the consumer's, whole: key, change, delay, duration
-- and easing.
#guard
  let isNew (x : String × Change × Transition) := x.1 != "a" && x.1 != "b"
  (whole (stagedMotion {} before after)).filter isNew == (whole fiveStep).filter isNew

-- With the new things from 270 ms of the step's 600, the consumer's first stage is over when
-- they enter, and the two steps are equal track for track. The second scene has one level,
-- where the consumer's own durations are the shorter and the caps are what make the two agree.
#guard [after, [⟨"a", ⟨100, 20⟩, .box⟩, ⟨"c", ⟨100, 140⟩, .box⟩, ⟨"a c", ⟨100, 140⟩, .route⟩]].all
  fun new =>
    let c : Choreography := { enterFrom := 270 }
    whole (stagedMotion c before new) == whole (motion c before new)

-- The reader reads the staged step as it reads the consumer's. At the moment 300 the first new
-- thing starts. In the consumer's step the kept box then stands three units short of its
-- place, and in the staged step it is at rest on it.
#guard ((motion {} before after).frame "a" 300).shift == ⟨-3, 0⟩
#guard ((stagedMotion {} before after).frame "a" 300).AtRest
/-! ## The step as CSS -/

-- The style sheet: one `@keyframes` rule for each track, in the order of the tracks.
#guard Motion.sheet fiveStep ==
  "@keyframes m0 { from { translate: -60px 0px } to { translate: 0px 0px } }\n" ++
  "@keyframes m1 { from { scale: 0 } to { scale: 1 } }\n" ++
  "@keyframes m2 { from { stroke-dashoffset: 1000 } to { stroke-dashoffset: 0 } }\n" ++
  "@keyframes m3 { from { scale: 0 } to { scale: 1 } }\n" ++
  "@keyframes m4 { from { scale: 1 } to { scale: 0 } }"

-- The new route, in a step of 600 ms: its animation, and the one dash that it is drawn by.
-- Its duration is 157 thousandths of the step, and is written exactly.
#guard Motion.style? fiveStep "a c" 600 ==
  some ("animation: m2 94.2ms cubic-bezier(0.333333, 1, 0.666667, 1) 180ms both;" ++
    " stroke-dasharray: 1000;")

-- The box that leaves: it shrinks about its middle.
#guard Motion.style? fiveStep "b" 600 ==
  some ("animation: m4 150ms cubic-bezier(0.333333, 0, 0.666667, 0) 0ms both;" ++
    " transform-box: fill-box; transform-origin: center;")

-- The box of the second level: the spring as `linear()`, started at 474 ms.
#guard Motion.style? fiveStep "d" 600 ==
  some ("animation: m3 126ms linear(0, 0.059, 0.195, 0.363, 0.531, 0.681, 0.804, 0.898, " ++
    "0.964, 1.007, 1.032, 1.043, 1.045, 1.041, 1.034, 1.026, 1.019, 1.012, 1.007, 1.003, 1) " ++
    "474ms both; transform-box: fill-box; transform-origin: center;")

-- A key with no track has no style.
#guard Motion.style? fiveStep "z" 600 == none

end WhatwgTest.Html.SvgMotion
