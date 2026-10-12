import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline

/-! A probe of what holds at every moment of a step (module M1 of
`docs/research/2026-10-12-pictures-craft-modules.md`). Run it from the repository root after
`lake build`:

    lake env lean workshop/BetweenProbe.lean

It writes `docs/research/2026-10-12-motion-probe/between.html`. No module imports this file,
and no gate reads its output.

The data is a rank of four boxes of a graph of fibers, with the widths and the gap of
lean4-effect4's flow layout. One box leaves, and the two boxes to its right move left to close
the room. Both pictures have a gap of sixteen between every two neighbours. The page asks
whether every moment between them has it, for three ways of timing the same step:

1. one timing for the kept boxes, with an easing that stays in range;
2. the same easing, the farther box started first;
3. one timing, with an easing that passes its end.

Under each it prints the least gap between two neighbours over a hundred and one moments, by
the kit's own reading (`Track.at`). The law of the module says that the first never falls
below sixteen. The other two do, and each breaks one premise of the law. -/

open Whatwg.Html
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- A box of a rank: its key, its left edge and its width, in whole pixels. -/
structure Item where
  key : String
  x : Int
  w : Int

/-- The gap of the layout. -/
def gap : Int := 16

/-- The rank before: four fibers in a row. -/
def before : List Item :=
  [⟨"fiber 0", 24, 120⟩, ⟨"fiber 1", 160, 160⟩, ⟨"fiber 2", 336, 216⟩, ⟨"fiber 3", 568, 120⟩]

/-- The rank after: `fiber 1` has left, and the two to its right have closed the room. -/
def after : List Item := [⟨"fiber 0", 24, 120⟩, ⟨"fiber 2", 160, 216⟩, ⟨"fiber 3", 392, 120⟩]

/-- lean4-effect4's critically damped spring: it stays in range. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

def stepMs : Nat := 1600

/-- The tracks of the step: the box that leaves fades, and each kept box moves by the
transition that `timing` gives its key. -/
def motion (timing : String → Transition) : Motion String :=
  let j := join Item.key before after
  Motion.within
    (Motion.arriveWith Item.key (fun i => ⟨i.x, 0⟩) j (fun i => timing i.key)
        (fun _ => (.fade 0 1000, {})) ++
      j.exit.map fun o => ⟨o.key, .fade 1000 0, { duration := 250, ease := Easing.cubicIn }⟩)

/-- 1. One timing, an easing in range. -/
def together : Motion String := motion fun _ => { delay := 250, duration := 600, ease := settle }

/-- 2. The same easing, the farther box first. -/
def staggered : Motion String :=
  motion fun k =>
    { delay := if k == "fiber 3" then 150 else 400, duration := 500, ease := settle }

/-- 3. One timing, an easing that passes its end. -/
def overshot : Motion String :=
  motion fun _ => { delay := 250, duration := 600, ease := Easing.backOut }

/-- Where a kept box stands at the moment `t`: its place and the shift of its track. -/
def leftAt (m : Motion String) (t : Nat) (i : Item) : Int :=
  (m.posesOf i.key t).foldl (fun x p =>
    match p with
    | .shift s => x + s.x
    | _ => x) i.x

/-- The least gap between two neighbours of the new rank at the moment `t`. -/
def leastGapAt (m : Motion String) (t : Nat) : Int :=
  ((after.zip (after.drop 1)).map fun (a, b) => leftAt m t b - (leftAt m t a + a.w)).foldl min 1000

/-- The least gap over the moments 0, 10, …, 1000, and the first moment that has it. -/
def leastGap (m : Motion String) : Int × Nat :=
  ((List.range 101).map fun i => (leastGapAt m (10 * i), 10 * i)).foldl
    (fun best x => if x.1 < best.1 then x else best) (1000, 0)

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

/-- One panel: the rank under a motion. The sheet's names start with `stem`, so that three
panels of one page do not share a name. -/
def panel (m : Motion String) (stem : String) : SvgNode :=
  let leaving := (join Item.key before after).exit
  Svg.svg
    [.attr .width (.user (.ofNat 720)), .attr .height (.user (.ofNat 128)),
      .attr .viewBox (ViewBox.ofSize 720 128)]
    (Svg.styleSheet (Motion.sheet m 1 stem) ::
      Svg.box (.ofSize ⟨0, 0⟩ 720 128) [.fill (.rgb ground)] ::
      (after ++ leaving).map fun i => boxNode i (Motion.attrs m i.key stepMs stem))

def verdict (name : String) (m : Motion String) (stem : String) : String :=
  let (g, t) := leastGap m
  "<h2 style=\"font-weight:400\">" ++ name ++ "</h2>\n" ++ (panel m stem).render ++
    "\n<p>Least gap between two neighbours over the step: <b>" ++ toString g ++
    "</b> pixels" ++ (if g < gap then ", at the moment " ++ toString t ++ " of 1000. " ++
      "Both pictures have " ++ toString gap ++ "." else ". Both pictures have " ++ toString gap ++
      ", and so has every moment.") ++ "</p>\n"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>A gap at every moment of a step</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">A gap at every moment of a step</h1>\n" ++
    "<p>One box leaves a rank of four and the two to its right close the room. " ++
    "<button onclick=\"document.querySelectorAll('svg').forEach(s=>s.replaceWith(s.cloneNode(true)))\">" ++
    "play again</button></p>\n" ++
    verdict "1. One timing, an easing that stays in range" together "a" ++
    verdict "2. The same easing, the farther box started first" staggered "b" ++
    verdict "3. One timing, an easing that passes its end" overshot "c" ++ "</body>\n"

#eval [leastGap together, leastGap staggered, leastGap overshot]
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/between.html" page
