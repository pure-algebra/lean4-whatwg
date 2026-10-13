import Whatwg.Svg.Geometry.Spring.Resume
import Whatwg.Svg.Geometry.Spring.Follow

/-!
# WhatwgTest.Html.SvgSpringResume

A step of lean4-effect4's rank that is interrupted, resumed with the speed its boxes have (slice
S17 of `docs/SVG-PACKAGE-PLAN.md`). The data is the rank of `workshop/ResumeProbe.lean`: four
boxes with the widths and the gap of the consumer's flow layout, and the consumer's move, a delay
of 100 and a duration of 800 per mille eased by its critically damped spring. `fiber 1` leaves;
at the moment 400 `fiber 0` leaves too. This module imports nothing of the consumer's package.

**What a real port copies.** One call: `plan.springResume key place stepOne cut spring 20 800
keep` where it has `plan.resume seen settle`. `sprung` is that call.

**What the guards show**, each a finite evaluation of the kit's own reading:

- at the cut, a box of the resumed step stands where it stood, with speed or without;
- in the piece before the cut a box goes 12 to the left. Resumed at rest by the consumer's move
  it goes nothing in the next piece, for the move has a delay. Resumed at rest with no delay it
  goes 10. Resumed with its speed it goes 19: the 12 it had and the first piece of a fresh
  spring over the 136 that its place moved, which is 7.3;
- every way ends on the third picture.

**The laws at the consumer's numbers.** `sprung_end` is `Motion.springResume_end`. `apart` is
`Spring.critical_followed_gap`: the two kept boxes are 232 apart in every picture, and they are
232 apart or more at every piece, through two cuts wherever they come.

**The controls.** A thing that is not calm: with `keep` its easing leaves the range, and without
it the thing starts from rest. A thing on its target takes the spring's own easing. A spring
that swings loses a gap that three pictures have.

Every guard is a finite evaluation by the compiler, and no theorem. Every theorem of this module
depends on `propext`, `Quot.sound` and `Classical.choice` at most.
-/

namespace WhatwgTest.Html.SvgSpringResume

open Whatwg.Svg.Scene

/-- A box of a rank: its key and its left edge, in whole pixels. -/
structure Item where
  key : String
  x : Int

def first : List Item := [⟨"fiber 0", 24⟩, ⟨"fiber 1", 160⟩, ⟨"fiber 2", 336⟩, ⟨"fiber 3", 568⟩]

/-- `fiber 1` has left, and the two to its right have closed the room. -/
def second : List Item := [⟨"fiber 0", 24⟩, ⟨"fiber 2", 160⟩, ⟨"fiber 3", 392⟩]

/-- `fiber 0` has left too. -/
def third : List Item := [⟨"fiber 2", 24⟩, ⟨"fiber 3", 256⟩]

/-- The consumer's critically damped spring, as three numbers. -/
def spring : Spring := Spring.critical (69073 / 100000) (37 / 100)

/-- The consumer's move: its easing is the spring's, at twenty pieces. -/
def move : Transition := { delay := 100, duration := 800, ease := spring.easing 20 }

def place (i : Item) : IVec := ⟨i.x, 0⟩

/-- The plan of a step, written as if every old thing stood still. -/
def planWith (mv : Transition) : Plan Item where
  kept := Plan.moving place mv
  enter := fun _ => [(.fade 0 1000, {})]
  leave := fun _ => [(.fade 1000 0, { duration := 500, ease := Easing.cubicIn })]

def plan : Plan Item := planWith move

/-- The first step. -/
def stepOne : Motion String := (Motion.ofJoin Item.key (join Item.key first second) plan).within

/-- The moment of the interruption. -/
def cut : Nat := 400

/-- The things drawn at the interruption. -/
def drawn : List Item := (join Item.key first second).drawn second cut

/-- The second step from the still picture. -/
def plain : Motion String := (Motion.ofJoin Item.key (join Item.key drawn third) plan).within

/-- The second step from where each thing is seen, at rest, by a move. -/
def resumed (mv : Transition) : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    ((planWith mv).resume (fun o => stepOne.frame o.key cut) fun _ => mv)).within

/-- **The port**: the second step with the speed each thing has. -/
def sprung (keep : Bool) : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    (plan.springResume Item.key place stepOne cut spring 20 800 keep)).within

/-- Where a box of a picture stands at a moment of a step. -/
def standsIn (picture : List Item) (m : Motion String) (t : Nat) (key : String) : Option Int :=
  (picture.find? fun i => i.key == key).map fun i => i.x + (m.frame key t).shift.x

/-- Where `fiber 2` stands in a second step, at the cut and at each of the next four pieces of
40 per mille. -/
def after (m : Motion String) : List (Option Int) :=
  (List.range 5).map fun i => standsIn third m (i * 40) "fiber 2"

-- Before the cut: a piece before it and at it. The box goes 12 to the left in the piece.
#guard [360, 400].map (fun t => standsIn second stepOne t "fiber 2") = [some 213, some 201]

-- From the still picture the box jumps to 160. Resumed, it stands at 201 in every way.
#guard after plain = [some 160, some 160, some 160, some 156, some 144]
#guard after (resumed move) = [some 201, some 201, some 201, some 196, some 181]
#guard after (resumed { move with delay := 0 }) = [some 201, some 191, some 170, some 146, some 123]
#guard after (sprung true) = [some 201, some 182, some 158, some 134, some 111]

-- The box is calm, so keeping in range gives nothing up.
#guard after (sprung false) = after (sprung true)

-- The first piece of a fresh spring over the 136 that the place of the box moved.
#guard (136 : Rat) * (1 - spring.rest) = 730318640 / 100000000

-- Every way ends on the third picture, and the other kept box does as this one.
#guard [plain, resumed move, sprung true, sprung false].map
  (fun m => (standsIn third m 1000 "fiber 2", standsIn third m 1000 "fiber 3")) =
  [(some 24, some 256), (some 24, some 256), (some 24, some 256), (some 24, some 256)]
#guard (List.range 26).all fun i =>
  (standsIn third (sprung true) (i * 40) "fiber 3").map (· - 232) ==
    standsIn third (sprung true) (i * 40) "fiber 2"

/-! ## The laws at these numbers -/

/-- The response of the consumer's spring has moved by its twentieth piece. -/
theorem spring_moved : spring.response 20 ≠ 1 := by
  have a := Spring.critical_response_le (69073 / 100000) (37 / 100) (by grind) (by grind) (by grind)
    (i := 1) (j := 20) (by decide)
  have e : spring.response 1 = (1 + 37 / 100) * (69073 / 100000) := rfl
  intro h
  rw [show (Spring.critical (69073 / 100000) (37 / 100)).response 20 = spring.response 20 from rfl,
    show (Spring.critical (69073 / 100000) (37 / 100)).response 1 = spring.response 1 from rfl,
    h, e] at a
  grind

/-- The plan settles: a kept box ends on its place and a new one at its whole opacity. -/
theorem plan_settles : plan.Settles :=
  ⟨Plan.moving_settles place move, fun _ c h => by
    rw [List.mem_singleton.mp h]
    exact rfl⟩

/-- The plan is proper: each of its three easings starts at `0` and ends at `1000`. -/
theorem plan_proper : plan.Proper :=
  ⟨Plan.moving_proper place move (Spring.easing_proper spring 20 spring_moved),
    fun _ c h => by
      rw [List.mem_singleton.mp h]
      exact Easing.proper_linear,
    fun _ c h => by
      rw [List.mem_singleton.mp h]
      exact Easing.proper_cubicIn⟩

/-- **The step resumed with speed ends on the third picture**: from the step's end on each of
its boxes is drawn as the still picture has it, with `keep` or without. -/
theorem sprung_end (keep : Bool) {n : Item} (hn : n ∈ third) {u : Nat} (hu : 1000 ≤ u) :
    ((sprung keep).frame n.key u).AtRest :=
  Motion.springResume_end Item.key place stepOne cut spring 20 800 keep drawn third plan
    (fun _ => none) plan_settles plan_proper spring_moved hn hu

/-- **The two kept boxes stay 232 apart or more, wherever the cuts come.** `fiber 2` goes from
336 toward 160, then toward 24, then back toward 160, and `fiber 3` from 568 toward 392, then
toward 256, then back toward 392. They run `k` pieces to the first cut, `j` more to the second,
`l` more after it, and are read `i` pieces later. -/
theorem apart (k j l i : Nat) :
    spring.followed 336 [(160, l), (24, j), (160, k)] i + 232 ≤
      spring.followed 568 [(392, l), (256, j), (392, k)] i :=
  Spring.critical_followed_gap _ _ (by grind) (by grind) (by grind) 336 568 232 (by grind)
    [(160, 392, l), (24, 256, j), (160, 392, k)] (fun x hx => by
      rcases List.mem_cons.mp hx with e | hx
      · rw [e]
        show (160 : Rat) + 232 ≤ 392
        grind
      · rcases List.mem_cons.mp hx with e | hx
        · rw [e]
          show (24 : Rat) + 232 ≤ 256
          grind
        · rw [List.mem_singleton.mp hx]
          show (160 : Rat) + 232 ≤ 392
          grind) i

/-! ## Controls -/

-- A thing that is not calm: seen at the offset 161 and moving away from its new target. With
-- `keep` its easing starts below `0`. Without, it starts from rest, with the spring's own
-- easing.
#guard (spring.onward 20 161 (17689003 / 100000)).bounded = false
#guard spring.calmly 20 161 (17689003 / 100000) = spring.easing 20

-- A thing that stands on its target takes the spring's own easing, whatever its speed.
#guard spring.onward 20 0 5 = spring.easing 20

-- `Spring.critical_followed_gap` needs a response that never rises. The two boxes of the rank
-- move alike, so their gap is 232 on any spring. Two things whose gap is 16, then 100, then 16
-- are less than 16 apart on the consumer's spring that swings, twelve pieces after a cut at its
-- twentieth piece.
#guard ¬((Spring.under (76913 / 100000) (96435 / 100000) (25937 / 100000)).followed 0
    [(100, 0), (400, 20)] 12 + 16 ≤
  (Spring.under (76913 / 100000) (96435 / 100000) (25937 / 100000)).followed 16
    [(116, 0), (500, 20)] 12)

end WhatwgTest.Html.SvgSpringResume
