import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Scene.Resume

/-! A probe of a step that is interrupted (`Whatwg/Svg/Scene/Resume.lean`). Run it from the
repository root after `lake build`:

    lake env lean workshop/ResumeProbe.lean

It writes `docs/research/2026-10-12-motion-probe/resume.html`. No module imports this file, and
no gate reads its output.

The data is the rank of four boxes of `workshop/BetweenProbe.lean`, with the widths and the gap
of lean4-effect4's flow layout. In the first step `fiber 1` leaves and the two boxes to its right
move left to close the room. At the moment 400 of that step a second request arrives: `fiber 0`
leaves too, and every box moves left again. The page shows the moment of the interruption in two
ways:

1. the second step starts from the still picture, as a viewer does that knows the pictures only;
2. the second step resumes from where each thing is seen (`Plan.resume`).

For each way it shows two pictures that the browser computes with no script, from tracks opened
at a moment and paused: the last picture of the first step, and the first picture of the second.
Under them it prints where each box stands in the two, by the kit's own reading. The law of the
module (`Motion.nothing_moves`) says that the second way has the same places in both. -/

open Whatwg.Html
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- A box of a rank: its key, its left edge and its width, in whole pixels. -/
structure Item where
  key : String
  x : Int
  w : Int

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

def stepMs : Nat := 1600

def move : Transition := { delay := 100, duration := 800, ease := settle }

def place (i : Item) : IVec := ⟨i.x, 0⟩

/-- The plan of a step, written as if every old thing stood still: a kept box moves, a new one
fades in, and one that leaves fades out. -/
def plan : Plan Item where
  kept := Plan.moving place move
  enter := fun _ => [(.fade 0 1000, {})]
  leave := fun _ => [(.fade 1000 0, { duration := 500, ease := Easing.cubicIn })]

/-- The first step. -/
def stepOne : Motion String := (Motion.ofJoin Item.key (join Item.key first second) plan).within

/-- The moment of the interruption. -/
def cut : Nat := 400

/-- The things drawn at the interruption: the box that is leaving, and the second picture. -/
def drawn : List Item := (join Item.key first second).drawn second cut

/-- 1. The second step from the still picture. -/
def plain : Motion String := (Motion.ofJoin Item.key (join Item.key drawn third) plan).within

/-- 2. The second step from where each thing is seen. -/
def resumed : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    (plan.resume (fun o => stepOne.frame o.key cut) fun _ => move)).within

/-- Where a box of the second step stands at a moment: the place it is drawn at and its shift.
A kept box is drawn at its place in the third picture, and one that leaves at its own. -/
def standsAt (m : Motion String) (t : Nat) (key : String) : Option Int :=
  let own := (third.find? fun i => i.key == key).orElse fun _ => drawn.find? fun i => i.key == key
  own.map fun i => i.x + (m.frame key t).shift.x

/-- Where a box stands at the interruption, in the first step. -/
def seenAt (key : String) : Option Int :=
  (drawn.find? fun i => i.key == key).map fun i => i.x + (stepOne.frame key cut).shift.x

def keys : List String := ["fiber 0", "fiber 1", "fiber 2", "fiber 3"]

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb ink), .xmlSpacePreserve]

def boxNode (i : Item) (more : List (SvgAttr .g)) : SvgNode :=
  let b : Box := .ofSize ⟨i.x, 40⟩ i.w 48
  Svg.g more
    [Svg.loops (Cubic.ring b 4 1) [.fill (.rgb ink), .fillRule true],
      Svg.label ⟨(i.x : Rat) + 8, 68⟩ i.key face]

/-- A picture of a step, opened at a moment and paused or running: the things that leave, then
the things of the step's new picture. -/
def picture (m : Motion String) (stem : String) (leaving new : List Item) (opened : Nat)
    (paused : Bool) (sheet : Bool) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat 720)), .attr .height (.user (.ofNat 128)),
      .attr .viewBox (ViewBox.ofSize 720 128)]
    ((if sheet then [Svg.styleSheet (Motion.sheet m 1 stem)] else []) ++
      Svg.box (.ofSize ⟨0, 0⟩ 720 128) [.fill (.rgb ground)] ::
      (leaving ++ new).map fun i => boxNode i (Motion.attrs m i.key stepMs stem opened paused))

def places (m : Motion String) : String :=
  ", ".intercalate (keys.filterMap fun k =>
    match seenAt k, standsAt m 0 k with
    | some a, some b => some (k ++ " at " ++ toString a ++ ", then at " ++ toString b)
    | _, _ => none)

def way (title : String) (m : Motion String) (stem : String) : String :=
  let leavingOne := (join Item.key first second).exit
  let leavingTwo := (join Item.key drawn third).exit
  "<h2 style=\"font-weight:400\">" ++ title ++ "</h2>\n" ++
    "<p>The first step at the moment " ++ toString cut ++ ", and the second step at its start.</p>\n" ++
    (picture stepOne (stem ++ "s") leavingOne second cut true true).render ++ "\n" ++
    (picture m stem leavingTwo third 0 true true).render ++ "\n" ++
    "<p>Where each box stands in the two pictures, by the kit's reading: <b>" ++ places m ++
    "</b>.</p>\n"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>A step that is interrupted</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">A step that is interrupted</h1>\n" ++
    "<p>One box is leaving a rank of four and two others are closing the room, when a second " ++
    "box is asked to leave. Every picture here is computed by the browser from tracks opened at " ++
    "a moment and paused, with no script.</p>\n" ++
    way "1. The second step starts from the still picture" plain "a" ++
    way "2. The second step resumes from where each thing is seen" resumed "b" ++ "</body>\n"

#eval keys.map fun k => (k, seenAt k, standsAt plain 0 k, standsAt resumed 0 k,
  standsAt resumed 1000 k)
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/resume.html" page
