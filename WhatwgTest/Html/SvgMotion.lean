import Whatwg.Svg.Scene.Plan
import Whatwg.Html.Node.SvgMotion

/-!
# WhatwgTest.Html.SvgMotion

The motion of a step of lean4-effect4 on the motion as data of the kit (slice S13 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-71). The consumer is read at its checkout `707b9a01`:
the sections "Easing", "Transitions" and "The choreography" of `tools/Tools/View/Look.lean`,
and the join, the layout of a moment and the end laws of `tools/Tools/View/Motion.lean`. This
module imports nothing of that package. It restates the consumer's easings (`Ease`) and its
choreography (`Choreography`) under the consumer's names, and copies the consumer's formulas
(`Ease.at`, `tableAt`, `Ease.timed`, `decimal`, `Ease.css`) as the reference of the guards.

**What the kit carries.** The consumer wrote for itself a mix of two values, seven easings, a
transition with its timing, a join by key, and a sample of a step with its end law. All of it
is now in the kit, in whole numbers and under the strict ceiling as the consumer has it:
`Whatwg/Svg/Scene/Join.lean`, `Whatwg/Svg/Scene/Motion.lean` and `Whatwg/Svg/Scene/Plan.lean`,
with their laws. What is here is what the consumer brings: its two tables, its seven names, its
default numbers, the levels of a layout, the things of a scene, and one `Plan` that says what
each thing of a step does.

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
| `placedAt`, `routeAt` | the tracks that `plan` gives the things of the new scene; `Seen.under` |
| `levels`, `slot`, `start` | `levels`, `slot`, `lateness` |
| `drawAt`, `expandAt` | `entrance`, started later by `lateness`, in the plan's `enter` |
| `gone`, `retracting` | the plan's `leave`, and `Join.drawn` |
| `sampleLaid` | `motion`, the tracks of the step, and `sample`, their reading |
| `Laid.AtRest` | `Pose.AtRest`, and `Thing.still` |
| `placedAt_end`, `routeAt_end`, `sampleLaid_end` | `motion_end`, `sample_end` |

**The laws.** The consumer's end law is `sampleLaid_end`: the layout at a step's end is the
next frame's. A step here is one `Plan` of the kit (`plan`). It settles (`plan_settles`), and it
is proper where the choreography is (`plan_proper`). The kit's laws of a plan then give the two
statements. At the end every track is at rest, or is of a thing that the new scene does not
have (`motion_end`, by `Motion.staying_end` and `Motion.mem_leaving_key`). The scene read at the
end is the new scene (`sample_end`, by `Motion.ofJoin_end` and `Join.drawn_end`). A kept thing
under its track stands where the consumer's `lerp` puts it (`under_shift`, by `mix_shift`).

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

**How it differs from the consumer.**

- *A step is tracks.* The consumer's moment is a layout whose things have fields: a place, a
  growth, a part drawn. Here a step is the new scene and one track for each change, so a
  browser can draw the moments from CSS (`Motion.sheet`, `Motion.style?`). `sample` reads the
  tracks back into things with fields, to state the consumer's law.
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
an easing: the kit writes a cubic as it is. The width and the height of a layout.

**The guards.** Each is a finite evaluation: the spread of each easing against the consumer's
formula, the timing of each default transition against the consumer's, the numbers of the
default choreography in per mille, a step of five things at three of its moments, and the CSS
of that step. The CSS is text written by rule; no browser read it here.

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

/-! ## A moment of a step -/

/-- A thing at a moment: the consumer's `Placed` with its `grow`, and its `Route` with its
`reveal`. -/
structure Seen where
  key : String
  place : IVec
  grow : Int := 1000
  reveal : Int := 1000
  deriving DecidableEq, Repr

/-- A thing of a still scene: at its place, at its whole size, drawn whole. -/
def Thing.still (n : Thing) : Seen := { key := n.key, place := n.place }

/-- A pose put on a thing: what the consumer's `placedAt` and `routeAt` set. -/
def Seen.under (s : Seen) : Pose → Seen
  | .shift step => { s with place := Moves.move step s.place }
  | .grow size => { s with grow := size }
  | .reveal part => { s with reveal := part }
  | _ => s

/-- **The scene at the moment `t` of a step**: the consumer's `sampleLaid`. The things drawn
are those of `Join.drawn`: the things that leave come first, until the step's end, and then the
things of the new scene. Each is drawn under the poses of its key. -/
def sample (c : Choreography) (old new : List Thing) (t : Nat) : List Seen :=
  ((join Thing.key old new).drawn new t).map fun n =>
    ((motion c old new).posesOf n.key t).foldl Seen.under n.still

/-- **A kept thing under its track stands where the consumer's `placedAt` puts it**: at the
consumer's `lerp` of its old place and its new one. -/
theorem under_shift (o n : Thing) (e : Int) :
    (n.still.under ((Change.shift (o.place - n.place) 0).at e)).place =
      ⟨mix o.place.x n.place.x e, mix o.place.y n.place.y e⟩ :=
  IVec.ext (mix_shift o.place.x n.place.x e).symm (mix_shift o.place.y n.place.y e).symm

/-- A pose at rest leaves a still thing as it is. -/
theorem under_atRest (n : Thing) (p : Pose) (h : p.AtRest) : n.still.under p = n.still := by
  cases p with
  | shift step =>
    cases (show step = 0 from h)
    exact congrArg (fun q => ({ key := n.key, place := q } : Seen)) (IVec.add_zero n.place)
  | grow size =>
    cases (show size = 1000 from h)
    rfl
  | reveal part =>
    cases (show part = 1000 from h)
    rfl
  | fade shown => rfl
  | shape segments => rfl

/-- Poses at rest leave a still thing as it is. -/
theorem foldl_under_atRest (n : Thing) :
    ∀ ps : List Pose, (∀ p ∈ ps, p.AtRest) → ps.foldl Seen.under n.still = n.still
  | [], _ => rfl
  | p :: ps, h => by
    rw [List.foldl_cons, under_atRest n p (h p List.mem_cons_self)]
    exact foldl_under_atRest n ps fun q hq => h q (List.mem_cons_of_mem p hq)

/-- **The consumer's end law, `sampleLaid_end`.** A step's last moment is the next scene: every
thing of it on its place, at its whole size and drawn whole, and no other thing. -/
theorem sample_end (c : Choreography) (old new : List Thing) (h : c.Proper) :
    sample c old new 1000 = new.map Thing.still := by
  show ((join Thing.key old new).drawn new 1000).map _ = new.map Thing.still
  rw [Join.drawn_end _ _ (Nat.le_refl 1000)]
  exact List.map_congr_left fun n hn => foldl_under_atRest n _
    (Motion.ofJoin_end Thing.key old new _ (plan_settles _ _)
      (plan_proper _ _ (c.norm_proper h)) hn (Nat.le_refl 1000))

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

-- One track for each thing: the kept box, the three new things, and the box that leaves.
-- Level by level from the top: the route at 300, the box at its end at 440, and the box of
-- the second level at 790, which ends with the step.
#guard fiveStep.map (fun tr => (tr.key, tr.timing.delay, tr.timing.duration)) ==
  [("a", 0, 450), ("c", 440, 210), ("a c", 300, 157), ("d", 790, 210), ("b", 0, 250)]

-- The first moment: the old scene, and the new things not yet there.
#guard sample {} before after 0 ==
  [⟨"b", ⟨40, 80⟩, 1000, 1000⟩, ⟨"a", ⟨40, 20⟩, 1000, 1000⟩, ⟨"c", ⟨100, 140⟩, 0, 1000⟩,
    ⟨"a c", ⟨100, 140⟩, 1000, 0⟩, ⟨"d", ⟨100, 200⟩, 0, 1000⟩]

-- Half way: `a` has settled and `b` has shrunk, the route is drawn, its box is growing, and
-- the second level has not started.
#guard sample {} before after 500 ==
  [⟨"b", ⟨40, 80⟩, 0, 1000⟩, ⟨"a", ⟨100, 20⟩, 1000, 1000⟩, ⟨"c", ⟨100, 140⟩, 768, 1000⟩,
    ⟨"a c", ⟨100, 140⟩, 1000, 1000⟩, ⟨"d", ⟨100, 200⟩, 0, 1000⟩]

-- Near the end: the box of the second level is past its size, on the spring.
#guard (sample {} before after 900).getLast? == some ⟨"d", ⟨100, 200⟩, 1037, 1000⟩

/-! ## The step as CSS -/

-- The style sheet: one `@keyframes` rule for each track, in the order of the tracks.
#guard Motion.sheet fiveStep ==
  "@keyframes m0 { from { translate: -60px 0px } to { translate: 0px 0px } }\n" ++
  "@keyframes m1 { from { scale: 0 } to { scale: 1 } }\n" ++
  "@keyframes m2 { from { stroke-dashoffset: 1000 } to { stroke-dashoffset: 0 } }\n" ++
  "@keyframes m3 { from { scale: 0 } to { scale: 1 } }\n" ++
  "@keyframes m4 { from { scale: 1 } to { scale: 0 } }"

-- The new route, in a step of 600 ms: its animation, and the one dash that it is drawn by.
#guard Motion.style? fiveStep "a c" 600 ==
  some ("animation: m2 94ms cubic-bezier(0.333333, 1, 0.666667, 1) 180ms both;" ++
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
