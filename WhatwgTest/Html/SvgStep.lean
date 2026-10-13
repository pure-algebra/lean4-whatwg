import Whatwg.Svg.Scene.Step.Laws
import WhatwgTest.Html.SvgMotion

/-!
# WhatwgTest.Html.SvgStep

Two programs that put a step together by hand, written again on `Step`
(`Whatwg/Svg/Scene/Step.lean`; slice S17 of `docs/SVG-PACKAGE-PLAN.md`). Each new value is shown
to be the old one, and each law that the old program proved or could not prove is one line.

**The rank of four boxes that is interrupted** is the data of `workshop/ResumeProbe.lean`: the
boxes `first`, `second` and `third`, the plan, and the cut at the moment `400`. That probe is a
program outside the libraries, so its data and its four motions are restated here, under its
names, as the old form. The new form is two steps, `one` and `two`: `two` is
`one.interrupt cut third`.

**The consumer's choreography** is the port `WhatwgTest/Html/SvgMotion.lean`, which this file
imports. Its `motion`, its `sample` and its `stagedMotion` are the old form. The new form is
`step` and `stagedStep`.

What a port that is written on `Step` copies from this file:

1. *The step*: one structure. `step_motion` and `step_sample` say that it is the port's motion
   and the port's sample, for every choreography and every two scenes.
2. *The laws of its plan*, each stated once: it settles, it is proper, it gives one change for
   each property (the port has these three), it changes no shape (`plan_keepsShapes`).
3. *The laws of its step*, each one line over a law of `Step`: `sample_end`, `step_single`,
   `stagedStep_single`, `staged_end`, `kept_above`.

What is new here, and was not shown before:

- `sample_end_rest`: at the step's end the sample is the new scene with every thing the still
  picture itself. The port says that it cannot show this: it needs a law of plans that change no
  shape, and that law is `Step.sample_end_rest`.
- `staged_kept_rest`: in the staged step every kept thing has a frame at rest from the moment
  the new things enter. The port has it of single tracks, and of one box at one moment as a
  guard.
- `rank_stands`: across the interruption no kept box of the rank moves, as a theorem of the two
  steps and not as a row of numbers.

How many lines the two forms take, counting code and no comment, is in the report of the slice.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/
namespace WhatwgTest.Html.SvgStep

open Whatwg.Svg.Scene
open WhatwgTest.Html.SvgMotion (Thing Choreography whole times before after stagedPlan stepSlot
  stepLevels rank stagedMotion)

namespace Rank

/-! ## A rank of four boxes, interrupted

The data of `workshop/ResumeProbe.lean`, with the widths and the gap of sixteen of
lean4-effect4's flow layout. In the first step `fiber 1` leaves and the two boxes to its right
move left to close the room. At the moment `400` a second request arrives: `fiber 0` leaves too,
and every box moves left again. -/

/-- A box of a rank: its key, its left edge and its width, in whole pixels. -/
structure Item where
  key : String
  x : Int
  w : Int
  deriving DecidableEq, Repr

/-- The first picture: four fibers in a row. -/
def first : List Item :=
  [⟨"fiber 0", 24, 120⟩, ⟨"fiber 1", 160, 160⟩, ⟨"fiber 2", 336, 216⟩, ⟨"fiber 3", 568, 120⟩]

/-- `fiber 1` has left, and the two to its right have closed the room. -/
def second : List Item := [⟨"fiber 0", 24, 120⟩, ⟨"fiber 2", 160, 216⟩, ⟨"fiber 3", 392, 120⟩]

/-- `fiber 0` has left too. -/
def third : List Item := [⟨"fiber 2", 24, 216⟩, ⟨"fiber 3", 256, 120⟩]

/-- lean4-effect4's critically damped spring. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

/-- The move of a kept box. -/
def move : Transition := { delay := 100, duration := 800, ease := settle }

/-- Where a box stands: its left edge. -/
def place (i : Item) : IVec := ⟨i.x, 0⟩

/-- The plan of a step, written as if every old thing stood still: a kept box moves, a new one
fades in, and one that leaves fades out. -/
def plan : Plan Item where
  kept := Plan.moving place move
  enter := fun _ => [(.fade 0 1000, {})]
  leave := fun _ => [(.fade 1000 0, { duration := 500, ease := Easing.cubicIn })]

/-- The moment of the interruption. -/
def cut : Nat := 400

/-- The four keys, in the order of the probe's page. -/
def keys : List String := ["fiber 0", "fiber 1", "fiber 2", "fiber 3"]

/-! ### The old form

The four values and the two readers of the probe, as it has them. The key function is written
seven times and `join` four times, and each motion is cut by hand. -/

/-- The first step. -/
def stepOne : Motion String := (Motion.ofJoin Item.key (join Item.key first second) plan).within

/-- The things drawn at the interruption: the box that is leaving, and the second picture. -/
def drawn : List Item := (join Item.key first second).drawn second cut

/-- The second step from the still picture. -/
def plain : Motion String := (Motion.ofJoin Item.key (join Item.key drawn third) plan).within

/-- The second step from where each thing is seen. -/
def resumed : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    (plan.resume (fun o => stepOne.frame o.key cut) fun _ => move)).within

/-- Where a box of the second step stands at a moment: the place it is drawn at and its shift. -/
def standsAt (m : Motion String) (t : Nat) (key : String) : Option Int :=
  let own := (third.find? fun i => i.key == key).orElse fun _ => drawn.find? fun i => i.key == key
  own.map fun i => i.x + (m.frame key t).shift.x

/-- Where a box stands at the interruption, in the first step. -/
def seenAt (key : String) : Option Int :=
  (drawn.find? fun i => i.key == key).map fun i => i.x + (stepOne.frame key cut).shift.x

/-! ### The new form -/

/-- The first step. -/
def one : Step Item String := { key := Item.key, old := first, new := second, plan := plan }

/-- The second step, from where each thing is seen at the interruption. -/
def two : Step Item String := one.interrupt cut third fun _ => move

/-- The second step from the still picture, as a viewer does that knows the pictures only. -/
def jumped : Step Item String := { one with old := one.drawn cut, new := third }

/-- Where each box that a step draws at a moment stands. -/
def stands (s : Step Item String) (t : Nat) : List (String × Int) :=
  (s.sample t).map fun x => (x.1.key, (x.2.stand (place x.1)).x)

/-! ### The new values are the old ones -/

-- The first step and the things drawn at the cut.
#guard whole one.motion == whole stepOne && one.drawn cut == drawn

-- The two second steps: resumed, and from the still picture.
#guard whole two.motion == whole resumed && whole jumped.motion == whole plain

-- The things that leave in each step, which the probe's page draws under the new picture.
#guard one.join.exit == (join Item.key first second).exit &&
  two.join.exit == (join Item.key drawn third).exit

-- The readers: where each box stands at the cut, and at the first moment of each second step.
#guard keys.map (fun k => (stands one cut).lookup k) == keys.map seenAt &&
  keys.map (fun k => (stands two 0).lookup k) == keys.map (standsAt resumed 0) &&
  keys.map (fun k => (stands jumped 0).lookup k) == keys.map (standsAt plain 0)

-- The numbers of the probe's page. At the cut the two boxes on their way stand at `201` and
-- `433`. The resumed step starts them there. The step from the still picture starts them at
-- their places in the second picture: each jumps by forty-one pixels.
#guard stands one cut == [("fiber 1", 160), ("fiber 0", 24), ("fiber 2", 201), ("fiber 3", 433)] &&
  stands two 0 == stands one cut &&
  stands jumped 0 == [("fiber 1", 160), ("fiber 0", 24), ("fiber 2", 160), ("fiber 3", 392)] &&
  stands two 1000 == [("fiber 2", 24), ("fiber 3", 256)]

-- The box that was leaving is seen at 488 thousandths of its opacity at the cut, and goes on
-- from there. From the still picture it is whole again at once.
#guard ((one.frame ⟨"fiber 1", 160, 160⟩ cut).shown, (two.frame ⟨"fiber 1", 160, 160⟩ 0).shown,
  (jumped.frame ⟨"fiber 1", 160, 160⟩ 0).shown) == (488, 488, 1000)

/-! ### The laws of the plan, each stated once -/

/-- The easing of the move starts at `0` and ends at `1000`. -/
theorem move_proper : move.ease.Proper := by decide

/-- The move reads `0` at the moment `0`: it has a delay. -/
theorem move_at_zero : move.at 0 = 0 := by decide

/-- The plan settles: a kept box ends on its place, and a new one at its whole opacity. -/
theorem plan_settles : plan.Settles :=
  ⟨Plan.moving_settles place move, fun _ _ h => by rw [List.mem_singleton.mp h]; exact rfl⟩

/-- The plan is proper: its three easings start at `0` and end at `1000`. -/
theorem plan_proper : plan.Proper :=
  ⟨Plan.moving_proper place move move_proper,
    fun _ _ h => by rw [List.mem_singleton.mp h]; decide,
    fun _ _ h => by rw [List.mem_singleton.mp h]; decide⟩

/-- The plan changes no shape. -/
theorem plan_keepsShapes : plan.KeepsShapes :=
  ⟨Plan.moving_keepsShape place move, fun _ _ h => by rw [List.mem_singleton.mp h]; decide⟩

/-- The plan is written from rest: a box that leaves fades from its whole opacity. -/
theorem plan_fromRest : plan.FromRest :=
  ⟨Plan.moving_fromRest place move,
    fun _ _ h => by rw [List.mem_singleton.mp h]; exact fun _ => rfl⟩

/-! ### The laws of the two steps -/

/-- **Across the interruption no kept box moves.** At the first moment of the second step each
kept box stands where its old box stood at the cut. It is `Step.nothing_moves` at this data: the
keys of the third picture are distinct and the move reads `0` at the moment `0`, which Lean
decides. -/
theorem rank_stands {o n : Item} (hu : (o, n) ∈ two.join.update) :
    (two.frame n 0).stand (place n) = (one.frame o cut).stand (place o) :=
  Step.nothing_moves one cut third (fun _ => move) (fun _ => none) plan (by decide) hu
    (fun c hc => by rw [Plan.mem_moving place move hc]; exact move_at_zero) move_at_zero place
    move (more := []) (List.append_nil _).symm (fun _ h => nomatch h) List.nodup_nil

/-- **The second step ends on the third picture at rest**, wherever it began: its sample at the
step's end is the two boxes of the third picture, each the still picture itself. -/
theorem two_end : two.sample 1000 = third.map fun n => (n, Frame.rest) :=
  Step.interrupt_sample_end_rest one cut third plan plan_settles plan_proper plan_keepsShapes
    (fun _ => move_proper) (Nat.le_refl 1000)

/-- **A request that arrives when the first step is over starts an ordinary step.** The step
that interrupts at the moment `1000` has the tracks of the step after the first: from the second
picture to the third. -/
theorem late_is_ordinary :
    (one.interrupt 1000 third fun _ => move).motion = (one.next third).motion :=
  Step.interrupt_of_rest one (Nat.le_refl 1000) third (fun _ => move) (fun _ => none) plan
    plan_settles plan_proper plan_keepsShapes plan_fromRest

/-- **The two boxes that close the room keep their gap at every moment of the first step.** The
second is the width of the first and the gap of the layout, 232 pixels, to its right in both
pictures, the move is one transition for both, and its easing stays in range. -/
theorem rank_gap (t : Nat) :
    ((one.frame ⟨"fiber 2", 160, 216⟩ t).stand (place ⟨"fiber 2", 160, 216⟩)).x + 232 ≤
      ((one.frame ⟨"fiber 3", 392, 120⟩ t).stand (place ⟨"fiber 3", 392, 120⟩)).x :=
  Step.leftOf one place move (by decide) (Plan.movesBy_moving place move _ _) (by decide) 232
    (o₁ := ⟨"fiber 2", 336, 216⟩) (o₂ := ⟨"fiber 3", 568, 120⟩) (by decide) (by decide)
    (by decide) (by decide) t

-- What `rank_gap` does not cover. The law is of a step that starts from the still picture. The
-- second step starts each box where it is seen, and its plan is not `Plan.moving` of one
-- transition, so no law says that the gap is kept. At the five moments read here it is: both
-- boxes are seen the same step off their places, and take one transition.
#guard ([0, 250, 500, 750, 1000].map fun t =>
  ((stands two t).lookup "fiber 3").getD 0 - ((stands two t).lookup "fiber 2").getD 0) ==
    [232, 232, 232, 232, 232]

end Rank

/-! ## The consumer's choreography

The port `WhatwgTest/Html/SvgMotion.lean` has the consumer's plan (`plan`, `stagedPlan`) and puts
its steps together by hand (`motion`, `sample`, `stagedMotion`). Here the same steps are two
values. -/

/-- **The consumer's step**: its plan is made from the join, since a new thing enters at the
time of its level among the new things. -/
def step (c : Choreography) (old new : List Thing) : Step Thing String :=
  .planned Thing.key old new (SvgMotion.plan c.norm)

/-- **The consumer's step in stages.** -/
def stagedStep (c : Choreography) (old new : List Thing) : Step Thing String :=
  { key := Thing.key, old, new, plan := stagedPlan c.norm (stepSlot c old new),
    stages := some ⟨c.norm.enterFrom, (stepLevels old new).length, rank old new⟩ }

/-- The step's tracks are the port's `motion`, for every choreography and every two scenes. -/
theorem step_motion (c : Choreography) (old new : List Thing) :
    (step c old new).motion = SvgMotion.motion c old new := rfl

/-- The step's sample is the port's `sample`. -/
theorem step_sample (c : Choreography) (old new : List Thing) (t : Nat) :
    (step c old new).sample t = SvgMotion.sample c old new t := rfl

/-- The staged step's tracks are the port's `stagedMotion`, held inside the step. -/
theorem stagedStep_motion (c : Choreography) (old new : List Thing) :
    (stagedStep c old new).motion = (stagedMotion c old new).within := rfl

-- In the step of five things the staged tracks end by the step's end, so the cut changes
-- nothing: the staged step's tracks are the port's `stagedMotion` as it is.
#guard whole (stagedStep {} before after).motion == whole (stagedMotion {} before after) &&
  times (stagedStep {} before after).motion ==
    [("a", 0, 300), ("c", 440, 210), ("a c", 300, 157), ("d", 790, 210), ("b", 0, 166)]

/-! ### The laws of the consumer's steps -/

/-- A new thing enters by a change that is not of its shape: a route is drawn, a box grows. -/
theorem entrance_keepsShape (c : Choreography) (ls : List Int) (n : Thing) :
    (SvgMotion.entrance c ls n).1.property ≠ .shape := by
  cases n with
  | mk key place kind =>
    cases kind with
    | box =>
      show (Change.grow 0 1000).property ≠ .shape
      decide
    | route =>
      show (Change.reveal 0 1000).property ≠ .shape
      decide

/-- The plan of a step changes no shape. -/
theorem plan_keepsShapes (c : Choreography) (j : Join Thing) : (SvgMotion.plan c j).KeepsShapes :=
  ⟨Plan.moving_keepsShape Thing.place c.move, fun n _ h =>
    List.mem_singleton.mp h ▸ entrance_keepsShape c (SvgMotion.levels j.enter) n⟩

/-- **The consumer's end law, `sampleLaid_end`**: the port's `sample_end`, one line on `Step`. -/
theorem sample_end (c : Choreography) (old new : List Thing) (h : c.Proper) :
    ((step c old new).sample 1000).map Prod.fst = new ∧
      ∀ x ∈ (step c old new).sample 1000, x.2.AtRest :=
  (step c old new).sample_end (SvgMotion.plan_settles _ _)
    (SvgMotion.plan_proper _ _ (c.norm_proper h)) (Nat.le_refl 1000)

/-- **A step's last moment is the next scene at rest**: each thing of the new scene is the still
picture itself. The port could not show this. -/
theorem sample_end_rest (c : Choreography) (old new : List Thing) (h : c.Proper) :
    (step c old new).sample 1000 = new.map fun n => (n, Frame.rest) :=
  (step c old new).sample_end_rest (SvgMotion.plan_settles _ _)
    (SvgMotion.plan_proper _ _ (c.norm_proper h)) (plan_keepsShapes _ _) (Nat.le_refl 1000)

/-- No thing of a step has two tracks of one property: the port's `motion_single`. -/
theorem step_single (c : Choreography) (old new : List Thing) (ho : Distinct Thing.key old)
    (hn : Distinct Thing.key new) : (step c old new).motion.Single :=
  (step c old new).single (SvgMotion.plan_single _ _) ho hn

/-- No thing of the staged step has two tracks of one property: the port's
`stagedMotion_single`, of the step as it is played. -/
theorem stagedStep_single (c : Choreography) (old new : List Thing)
    (ho : Distinct Thing.key old) (hn : Distinct Thing.key new) :
    (stagedStep c old new).motion.Single :=
  (stagedStep c old new).single (SvgMotion.stagedPlan_single _ _) ho hn

/-- The last picture of the staged step: the port's `staged_end`. -/
theorem staged_end (c : Choreography) (old new : List Thing) (h : c.Proper) {n : Thing}
    (hn : n ∈ new) {t : Nat} (ht : 1000 ≤ t) : ((stagedStep c old new).frame n t).AtRest :=
  (stagedStep c old new).frame_end (SvgMotion.stagedPlan_settles _ _)
    (SvgMotion.stagedPlan_proper _ _ (c.norm_proper h)) hn ht

/-- **In the staged step every kept thing is at rest from the moment the new things enter**: a
law of what is seen, for every two scenes. The port has it of single tracks. -/
theorem staged_kept_rest (c : Choreography) (old new : List Thing) (h : c.Proper) {o n : Thing}
    (hu : (o, n) ∈ (stagedStep c old new).join.update) {t : Nat} (ht : c.norm.enterFrom ≤ t) :
    ((stagedStep c old new).frame n t).AtRest :=
  (stagedStep c old new).kept_rest rfl (SvgMotion.stagedPlan_settles _ _)
    (SvgMotion.stagedPlan_proper _ _ (c.norm_proper h)) hu ht

/-- **Two kept things, one above the other by a gap in both scenes, are so at every moment** of
the consumer's step, where the easing of its move stays in range and the keys of the new scene
are distinct. -/
theorem kept_above (c : Choreography) (old new : List Thing) (hn : Distinct Thing.key new)
    (hb : c.move.ease.bounded = true) (g : Int) {o₁ n₁ o₂ n₂ : Thing}
    (h₁ : (o₁, n₁) ∈ (step c old new).join.update) (h₂ : (o₂, n₂) ∈ (step c old new).join.update)
    (hold : o₁.place.y + g ≤ o₂.place.y) (hnew : n₁.place.y + g ≤ n₂.place.y) (t : Nat) :
    (((step c old new).frame n₁ t).stand n₁.place).y + g ≤
      (((step c old new).frame n₂ t).stand n₂.place).y :=
  (step c old new).above Thing.place c.norm.move hn
    (Plan.movesBy_moving Thing.place c.norm.move _ _) hb g h₁ h₂ hold hnew t

/-! ### The step of five things -/

-- The sample of the step is the port's, at the three moments that the port reads.
#guard [0, 500, 900].all fun t =>
  (step {} before after).sample t == SvgMotion.sample {} before after t

/-- An order of the keys of a step: an old thing is before a new thing, and a new thing is
before a new thing of a lower row. -/
def comesFirst (old new : List Thing) (a b : String) : Bool :=
  let j := join Thing.key old new
  j.enter.any fun n => n.key == b &&
    (old.any (fun o => o.key == a) || j.enter.any fun m => m.key == a && m.place.y < n.place.y)

-- The staged step respects that order, as `Step.order` says of an order in which nothing is
-- before an old thing. The consumer's own step does not: its kept box is still moving when the
-- first new thing starts.
#guard decide ((stagedStep {} before after).motion.Respects
    fun a b => comesFirst before after a b = true) &&
  !decide ((step {} before after).motion.Respects fun a b => comesFirst before after a b = true)

-- What no order law here says: two things of one level. The route to the box `c` is still
-- drawing when the box starts to grow.
#guard !decide ((stagedStep {} before after).motion.Respects
  fun a b => (a, b) = ("a c", "c"))

end WhatwgTest.Html.SvgStep
