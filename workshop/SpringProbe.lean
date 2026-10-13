import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Scene.Resume
import Whatwg.Svg.Geometry.Spring.Resume

/-! A probe of a step that is interrupted and resumes with the speed its things have
(`Whatwg/Svg/Geometry/Spring/Resume.lean`). Run it from the repository root after `lake build`:

    lake env lean workshop/SpringProbe.lean

It writes `spring.html` and `spring-run.html` into `docs/research/2026-10-12-motion-probe/`, or
into the directory that the environment variable `SPRING_PROBE_OUT` names. No module imports this
file, and no gate reads its output.

The data is the rank of four boxes of `workshop/ResumeProbe.lean`. In the first step `fiber 1`
leaves and the two boxes to its right move left to close the room. At the moment 400 of that step
`fiber 0` leaves too, and every box moves left again. The move is eased by lean4-effect4's
critically damped spring, here as three numbers (`Spring.critical`), with twenty pieces over a
duration of 800: a piece is 40 per mille of the step.

The second step is made in three ways:

1. from the still picture, as a viewer does that knows the pictures only;
2. resumed from where each thing is seen, at rest (`Plan.resume` with the plan's own move);
3. resumed with the speed each thing has (`Plan.springResume`).

For each way the page shows the pictures that the browser computes with no script, from tracks
opened at a moment and paused: the cut, and each of the next four pieces. Under them it prints,
by the kit's own reading, where each kept box stands at those moments, and how far it went in
the piece before the cut and in the piece after it. `spring-run.html` plays the three ways from
the cut, one above another. -/

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

/-- lean4-effect4's critically damped spring, as three numbers. -/
def spring : Spring := Spring.critical (69073 / 100000) (37 / 100)

def pieces : Nat := 20

/-- Its easing: the consumer's table of twenty-one stops. -/
def settle : Easing := spring.easing pieces

def stepMs : Nat := 1600

def move : Transition := { delay := 100, duration := 800, ease := settle }

/-- A piece of the move, in per mille of the step. -/
def piece : Nat := move.duration / pieces

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

/-- The things drawn at the interruption: the box that is leaving, and the second picture. -/
def drawn : List Item := (join Item.key first second).drawn second cut

/-- 1. The second step from the still picture. -/
def plain : Motion String := (Motion.ofJoin Item.key (join Item.key drawn third) plan).within

/-- 2. The second step from where each thing is seen, at rest, by the plan's own move. -/
def resumed : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    (plan.resume (fun o => stepOne.frame o.key cut) fun _ => move)).within

/-- The move with no delay. -/
def moveNow : Transition := { move with delay := 0 }

/-- 2, with no delay: at rest still, and started at the cut. It is here for the numbers only. -/
def resumedNow : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    ((planWith moveNow).resume (fun o => stepOne.frame o.key cut) fun _ => moveNow)).within

/-- 3. The second step with the speed each thing has. -/
def sprung (keep : Bool) : Motion String :=
  (Motion.ofJoin Item.key (join Item.key drawn third)
    (plan.springResume Item.key place stepOne cut spring pieces move.duration keep)).within

/-- Where a box of a picture stands at a moment of a step: its place and the shift of its
frame. -/
def standsIn (picture : List Item) (m : Motion String) (t : Nat) (key : String) : Option Int :=
  (picture.find? fun i => i.key == key).map fun i => i.x + (m.frame key t).shift.x

/-- The kept boxes of the second step. -/
def kept : List String := third.map Item.key

/-- Where a kept box stands in the first step, one piece before the cut and at the cut. -/
def beforeCut (key : String) : List Int :=
  [cut - piece, cut].filterMap fun t => standsIn second stepOne t key

/-- Where a kept box stands in a second step, at the cut and at each of the next four pieces. -/
def afterCut (m : Motion String) (key : String) : List Int :=
  (List.range 5).filterMap fun i => standsIn third m (i * piece) key

/-- How far a box went between the first two places of a list. -/
def covered (l : List Int) : Int := l.getD 1 0 - l.getD 0 0

/-- The two offsets of a kept box at the cut, as `Plan.springResume` reads them, and whether the
box is calm. -/
def offsets (key : String) : Option (Rat × Rat × Bool) :=
  match drawn.find? (fun i => i.key == key), third.find? (fun i => i.key == key) with
  | some o, some n =>
    let seen := place o + (stepOne.frame key cut).shift
    let next := place o + (stepOne.frame key (cut + piece)).shift
    let x0 : Rat := (seen.x : Rat) - ((place n).x : Rat)
    let x1 : Rat := (next.x : Rat) - ((place n).x : Rat) +
      (((place n).x - (place o).x : Int) : Rat) * (1 - spring.rest)
    some (x0, x1, decide (Spring.Calm (69073 / 100000) x0 x1))
  | _, _ => none

-- The numbers, for the log: each kept box before the cut, then after it in each way.
#eval kept.map fun k => (k, beforeCut k, covered (beforeCut k))
#eval kept.map fun k => (k, "1 still", afterCut plain k, covered (afterCut plain k))
#eval kept.map fun k => (k, "2 at rest", afterCut resumed k, covered (afterCut resumed k))
#eval kept.map fun k => (k, "2 at rest, no delay", afterCut resumedNow k,
  covered (afterCut resumedNow k))
#eval kept.map fun k => (k, "3 with speed", afterCut (sprung true) k,
  covered (afterCut (sprung true) k))
#eval kept.map fun k => (k, "3 in range", afterCut (sprung false) k,
  covered (afterCut (sprung false) k))
#eval kept.map fun k => (k, (offsets k).map fun x => (x.1.floor, (1000 * x.2.1).floor, x.2.2))
#eval ((sprung true).map fun tr => (tr.key, tr.timing.ease.bounded, tr.timing.delay,
  tr.timing.duration))

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb ink), .xmlSpacePreserve]

def boxNode (i : Item) (more : List (SvgAttr .g)) : SvgNode :=
  let b : Box := .ofSize ⟨i.x, 40⟩ i.w 48
  Svg.g more
    [Svg.loops (Cubic.ring b 4 1) [.fill (.rgb ink), .fillRule .evenodd],
      Svg.label ⟨(i.x : Rat) + 8, 68⟩ i.key face]

/-- A picture of a step, opened at a moment and paused or running: the things that leave, then
the things of the step's new picture. It is drawn at half its size where `small`. -/
def picture (m : Motion String) (stem : String) (leaving new : List Item) (opened : Nat)
    (paused sheet small : Bool) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat (if small then 360 else 720))),
      .attr .height (.user (.ofNat (if small then 64 else 128))),
      .attr .viewBox (ViewBox.ofSize 720 128)]
    ((if sheet then [m.sheetNode { step := stepMs, stem := stem }] else []) ++
      Svg.box (.ofSize ⟨0, 0⟩ 720 128) [.fill (.rgb ground)] ::
      (leaving ++ new).map fun i => boxNode i (Motion.attrs m i.key { step := stepMs, stem := stem, opened := opened, paused := paused }))

def cell (s : String) : String := "<td style=\"padding:2px 12px;text-align:right\">" ++ s ++ "</td>"

def row (cells : List String) : String := "<tr>" ++ String.join (cells.map cell) ++ "</tr>\n"

/-- The numbers of a way: for each kept box, where it stands and how far it went. -/
def numbers (m : Motion String) : String :=
  "<table style=\"border-collapse:collapse;font-family:Menlo,monospace;font-size:13px\">\n" ++
    row (["box", "a piece before", "at the cut"] ++
      (List.range 5).map (fun i => "cut + " ++ toString i) ++
      ["went before", "went after"]) ++
    String.join (kept.map fun k =>
      row ([k] ++ (beforeCut k).map toString ++ (afterCut m k).map toString ++
        [toString (covered (beforeCut k)), toString (covered (afterCut m k))])) ++
    "</table>\n"

def figure (caption : String) (svg : SvgNode) : String :=
  "<figure style=\"margin:4px;display:inline-block\">" ++ svg.render ++
    "<figcaption style=\"font-size:12px\">" ++ caption ++ "</figcaption></figure>\n"

/-- A way: the first step at the cut, the second step at the cut and at the next four pieces,
and the numbers. -/
def way (title : String) (note : String) (m : Motion String) (stem : String) : String :=
  let leavingOne := (join Item.key first second).exit
  let leavingTwo := (join Item.key drawn third).exit
  "<h2 style=\"font-weight:400\">" ++ title ++ "</h2>\n<p>" ++ note ++ "</p>\n" ++
    figure ("the first step at the moment " ++ toString cut)
      (picture stepOne (stem ++ "s") leavingOne second cut true true true) ++
    String.join ((List.range 5).map fun i =>
      figure ("the second step, " ++ toString i ++ " pieces after the cut")
        (picture m stem leavingTwo third (i * piece) true (i == 0) true)) ++
    numbers m

def head (title : String) : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>" ++ title ++ "</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">" ++ title ++ "</h1>\n"

def page : String :=
  head "A step that is interrupted, and the speed of its things" ++
    "<p>One box is leaving a rank of four and two others are closing the room, when a second " ++
    "box is asked to leave. The move is a critically damped spring of twenty pieces, and a " ++
    "piece is " ++ toString piece ++ " per mille of the step. Every picture is computed by the " ++
    "browser from tracks opened at a moment and paused, with no script. The numbers are the " ++
    "kit's own reading of the same tracks: where each kept box stands a piece before the cut, " ++
    "at the cut, and at the cut and each of the next four pieces of the second step; then how " ++
    "far it went in the piece before the cut and in the piece after it.</p>\n" ++
    way "1. The second step starts from the still picture"
      "Each box jumps to its place in the second picture, and starts from there at rest."
      plain "a" ++
    way "2. The second step resumes from where each thing is seen, at rest"
      ("Nothing jumps. Each box stands for the delay of the move, " ++ toString move.delay ++
        " per mille, and then starts from rest: a box that was going fast nearly stops.")
      resumed "b" ++
    "<p>The same with no delay, so that the box starts at the cut and still from rest:</p>\n" ++
    numbers resumedNow ++
    way "3. The second step resumes with the speed each thing has"
      ("Nothing jumps, and each box goes on: in the piece after the cut it goes what it went " ++
        "in the piece before, and the first piece of a fresh spring over the way that its " ++
        "place moved.")
      (sprung true) "c" ++
    "<p>Kept in range (a thing that is not calm starts from rest):</p>\n" ++
    numbers (sprung false) ++ "</body>\n"

/-- The three ways, running from the cut, one above another. -/
def running : String :=
  let leavingTwo := (join Item.key drawn third).exit
  let one (title : String) (m : Motion String) (stem : String) : String :=
    "<h2 style=\"font-weight:400\">" ++ title ++ "</h2>\n" ++
      (picture m stem leavingTwo third 0 false true false).render ++ "\n"
  head "Three ways to go on from a cut" ++
    "<p>The three second steps play from the moment of the cut, each in a step of " ++
    toString stepMs ++ " milliseconds. Load the page again to play them again.</p>\n" ++
    one "1. From the still picture" plain "a" ++
    one "2. From where each thing is seen, at rest" resumed "b" ++
    one "3. With the speed each thing has" (sprung true) "c" ++ "</body>\n"

/-- Write the two pages. -/
def write : IO Unit := do
  let dir := (← IO.getEnv "SPRING_PROBE_OUT").getD "docs/research/2026-10-12-motion-probe"
  IO.FS.writeFile (dir ++ "/spring.html") page
  IO.FS.writeFile (dir ++ "/spring-run.html") running

#eval write
