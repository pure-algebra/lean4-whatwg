import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Grid
import Whatwg.Svg.Scene.Cross

/-! A probe of crossings on the way (`Whatwg/Svg/Scene/Cross.lean`). Run it from the repository
root after `lake build`:

    lake env lean workshop/CrossProbe.lean

It writes `docs/research/2026-10-12-motion-probe/cross.html`. No module imports this file, and no
gate reads its output.

The data is two ranks of a graph of fibers and the straight links between them. A step moves
the ends of the links, each the straight way at one timing. The page counts the crossings at a
hundred and one moments, by the kit's own test (`crossings`), for three steps:

1. the ends spread and keep their order on both ranks;
2. the layout swaps the lower ends of two links, to take a crossing out;
3. two links change places, and their lower ends pass each other before their upper ends.

`crosses_on_way` says that the first step has the same crossings at every moment. The second
loses its crossing once and gains none. The third has no crossing before and none after, and
one on the way. -/

open Whatwg.Html
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- A link: its key, its upper end and its lower end, as abscissae in whole pixels. -/
abbrev Link : Type := String × Int × Int

/-- The heights of the two ranks. -/
def upper : Int := 36
def lower : Int := 124

/-- 1. The ends spread; the order of the upper ends and of the lower ends is kept. One crossing
before, and the same one after. -/
def spreadBefore : List Link := [("a", 80, 80), ("b", 200, 320), ("c", 320, 200), ("d", 440, 440)]
def spreadAfter : List Link := [("a", 60, 100), ("b", 180, 380), ("c", 340, 220), ("d", 460, 470)]

/-- 2. The lower ends of `b` and `c` change places: the crossing is taken out. -/
def swapAfter : List Link := [("a", 80, 80), ("b", 200, 200), ("c", 320, 320), ("d", 440, 440)]

/-- 3. Two links change places. The lower ends pass each other before the upper ends do. -/
def passBefore : List Link := [("p", 200, 200), ("q", 320, 320)]
def passAfter : List Link := [("p", 320, 400), ("q", 200, 240)]

/-- lean4-effect4's critically damped spring. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

def stepMs : Nat := 2400

def timing : Transition := { delay := 100, duration := 800, ease := settle }

/-- The links at the moment `t` of a step: each end the straight way, by the one timing. -/
def linksAt (before after : List Link) (t : Nat) : List Link :=
  (before.zip after).map fun (o, n) =>
    (n.1, mix o.2.1 n.2.1 (timing.at t), mix o.2.2 n.2.2 (timing.at t))

/-- How many crossings the links have at the moment `t`. -/
def countAt (before after : List Link) (t : Nat) : Nat :=
  (crossings (fun (_ _ : String) => true) (Cross.links upper lower (linksAt before after t))).length

/-- The count at the start, and each moment of 0, 10, …, 1000 at which the count differs from
the count ten before, with the new count. -/
def history (before after : List Link) : Nat × List (Nat × Nat) :=
  let counts := (List.range 101).map fun i => (10 * i, countAt before after (10 * i))
  (countAt before after 0,
    (counts.zip (counts.drop 1)).filterMap fun (a, b) => if a.2 = b.2 then none else some b)

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d
def boxInk : Rgb := .ofNat 0x4a4238

/-- A link as one straight segment. -/
def segment (l : Link) : List Cubic := [Cubic.line ⟨l.2.1, upper⟩ ⟨l.2.2, lower⟩]

/-- The tracks of a step: each link changes its shape, and the box at each of its ends moves,
all by the one timing. -/
def motion (before after : List Link) : Motion String :=
  (before.zip after).flatMap fun (o, n) =>
    [⟨n.1, Change.morphOf 1000 (segment o) (segment n), timing⟩,
      ⟨n.1 ++ " upper", .shift ⟨(o.2.1 - n.2.1) * 1000, 0⟩ 0, timing⟩,
      ⟨n.1 ++ " lower", .shift ⟨(o.2.2 - n.2.2) * 1000, 0⟩ 0, timing⟩]

/-- One panel: the links of the picture after, under the motion from the picture before. -/
def panel (before after : List Link) (stem : String) : SvgNode :=
  let m := motion before after
  let dot (x y : Int) (key : String) : SvgNode :=
    Svg.loops [Cubic.roundRect (.ofSize ⟨x - 18, y - 9⟩ 36 18) 4]
      ([.fill (.rgb boxInk)] ++ Motion.attrs m key { step := stepMs, stem := stem, grid := 1000 })
  Svg.svg
    [.attr .width (.user (.ofNat 540)), .attr .height (.user (.ofNat 160)),
      .attr .viewBox (ViewBox.ofSize 540 160)]
    (m.sheetNode { step := stepMs, stem := stem, grid := 1000 } ::
      Svg.box (.ofSize ⟨0, 0⟩ 540 160) [.fill (.rgb ground)] ::
      (after.map fun l =>
        Svg.cubics (segment l)
          ([.fill .none, .stroke (.rgb ink), .strokeWidth (.ofRat 2 1)] ++
            Motion.attrs m l.1 { step := stepMs, stem := stem, grid := 1000 })) ++
      after.flatMap fun l => [dot l.2.1 upper (l.1 ++ " upper"), dot l.2.2 lower (l.1 ++ " lower")])

def verdict (before after : List Link) : String :=
  let (first, changes) := history before after
  "<p>Crossings at the start: <b>" ++ toString first ++ "</b>. " ++
    (if changes.isEmpty then "The count is the same at every moment of the step."
      else "The count changes: " ++ ", ".intercalate (changes.map fun (t, c) =>
        "to <b>" ++ toString c ++ "</b> by the moment " ++ toString t) ++ ".") ++ "</p>\n"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>Crossings on the way</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">Crossings on the way</h1>\n" ++
    "<p>Straight links between two ranks, and a step that moves their ends. " ++
    "<button onclick=\"document.querySelectorAll('svg').forEach(s=>s.replaceWith(s.cloneNode(true)))\">" ++
    "play again</button></p>\n" ++
    "<h2 style=\"font-weight:400\">1. The ends spread and keep their order</h2>\n" ++
    (panel spreadBefore spreadAfter "a").render ++ "\n" ++ verdict spreadBefore spreadAfter ++
    "<h2 style=\"font-weight:400\">2. Two lower ends change places, to take the crossing out</h2>\n" ++
    (panel spreadBefore swapAfter "b").render ++ "\n" ++ verdict spreadBefore swapAfter ++
    "<h2 style=\"font-weight:400\">3. Two links change places</h2>\n" ++
    (panel passBefore passAfter "c").render ++ "\n" ++ verdict passBefore passAfter ++ "</body>\n"

#eval [history spreadBefore spreadAfter, history spreadBefore swapAfter, history passBefore passAfter]
#eval (Cross.inversions (spreadBefore.map fun l => l.2), Cross.inversions (swapAfter.map fun l => l.2))
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/cross.html" page
