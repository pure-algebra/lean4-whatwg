import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Grid
import Whatwg.Svg.Scene.Row

/-! A probe of a row whose lengths change (`Whatwg/Svg/Scene/Row.lean`). Run it from the
repository root after `lake build`:

    lake env lean workshop/RowProbe.lean

It writes `docs/research/2026-10-12-motion-probe/row.html`. No module imports this file, and no
gate reads its output.

The data is a rank of four boxes of a graph of fibers, with the gap of lean4-effect4's flow
layout. One box gets wider, as a box does when its label grows, and its neighbour gets narrower
by as much, so the rank keeps its length. Both pictures have a gap of sixteen between every two
neighbours and a rank of 664. The page asks whether every moment between them has both, for the
step made in four ways:

1. each box at its own time, the usual stagger;
2. one timing, each length mixed by itself;
3. one timing, the edges mixed (`Row.between`), with an easing that stays in range;
4. the same, with an easing that passes its end.

Under each it prints the least and the greatest gap and the least and the greatest length of the
rank over a hundred and one moments, by the kit's own reading. The laws of the module say that
the last two keep the gap at sixteen and the length at 664 at every moment. -/

open Whatwg.Html
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- The left edge of the rank. -/
def left : Int := 24

/-- The rank before: a box, a gap, a box, and so on. -/
def before : List Int := [120, 16, 160, 16, 216, 16, 120]

/-- The rank after: the second box is wider by eighty, and the third narrower by as much. -/
def after : List Int := [120, 16, 240, 16, 136, 16, 120]

def names : List String := ["fiber 0", "fiber 1", "fiber 2", "fiber 3"]

/-- The boxes of a row of spans: every other span, from the first. -/
def boxes : List (Int × Int) → List (Int × Int)
  | b :: _ :: rest => b :: boxes rest
  | rest => rest

/-- lean4-effect4's critically damped spring: it stays in range. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

def stepMs : Nat := 1600

/-- One timing for the whole rank. -/
def together (ease : Easing) : Nat → Transition := fun _ => { delay := 150, duration := 700, ease }

/-- Each box a little after the one before it. -/
def staggered : Nat → Transition := fun i => { delay := 100 + 150 * i, duration := 450, ease := settle }

/-- 1. Each box at its own time: its left edge and its width go the straight way by its own
transition. -/
def wayOwn (timing : Nat → Transition) (t : Nat) : List (Int × Int) :=
  ((boxes (Row.spans left before)).zip (boxes (Row.spans left after))).zipIdx.map fun ((o, n), i) =>
    let e := (timing i).at t
    (mix o.1 n.1 e, mix o.2 n.2 e)

/-- 2. One timing, each length mixed by itself, and the rank built from the mixed lengths. -/
def wayLengths (tr : Transition) (t : Nat) : List (Int × Int) :=
  boxes (Row.spans left ((before.zip after).map fun (w, w') => mix w w' (tr.at t)))

/-- 3 and 4. One timing, the edges mixed. -/
def wayEdges (tr : Transition) (t : Nat) : List (Int × Int) :=
  boxes (Row.between (tr.at t) left left before after)

/-- The gaps between the boxes of a rank. -/
def gapsOf (bs : List (Int × Int)) : List Int :=
  (bs.zip (bs.drop 1)).map fun (a, b) => b.1 - (a.1 + a.2)

/-- The length of a rank: from its left edge to the right edge of its last box. -/
def lengthOf (bs : List (Int × Int)) : Int :=
  match bs.getLast? with
  | some l => l.1 + l.2 - left
  | none => 0

/-- The least and the greatest gap, and the least and the greatest length, over the moments 0,
10, …, 1000. -/
def stat (way : Nat → List (Int × Int)) : (Int × Int) × (Int × Int) :=
  ((List.range 101).map fun i => way (10 * i)).foldl
    (fun acc bs =>
      let gs := gapsOf bs
      ((gs.foldl min acc.1.1, gs.foldl max acc.1.2),
        (min acc.2.1 (lengthOf bs), max acc.2.2 (lengthOf bs))))
    ((1000, -1000), (100000, 0))

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d
def boxInk : Rgb := .ofNat 0x4a4238

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb ink), .xmlSpacePreserve]

/-- The outline of a box of the rank. -/
def outline (b : Int × Int) : List Cubic := Cubic.roundRect (.ofSize ⟨b.1, 40⟩ b.2 48) 5

/-- The tracks of a step: each box changes its shape from its old outline to its new one, and its
label moves with its left edge, both by the transition that `timing` gives the box. A host that
changes a shape point by point mixes the edges. -/
def motion (timing : Nat → Transition) : Motion String :=
  ((boxes (Row.spans left before)).zip (boxes (Row.spans left after))).zipIdx.flatMap
    fun ((o, n), i) =>
      [⟨"box " ++ toString i, Change.morphOf 1000 (outline o) (outline n), timing i⟩,
        ⟨"label " ++ toString i, .shift ⟨(o.1 - n.1) * 1000, 0⟩ 0, timing i⟩]

/-- One panel: the rank under a motion. -/
def panel (m : Motion String) (stem : String) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat 720)), .attr .height (.user (.ofNat 128)),
      .attr .viewBox (ViewBox.ofSize 720 128)]
    (Svg.styleSheet (Motion.sheet m 1000 stem) ::
      Svg.box (.ofSize ⟨0, 0⟩ 720 128) [.fill (.rgb ground)] ::
      ((boxes (Row.spans left after)).zip names).zipIdx.flatMap fun ((n, name), i) =>
        [Svg.loops [outline n]
            ([.fill (.rgb boxInk)] ++ Motion.attrs m ("box " ++ toString i) stepMs stem),
          Svg.g (Motion.attrs m ("label " ++ toString i) stepMs stem)
            [Svg.label ⟨(n.1 : Rat) + 8, 68⟩ name face]])

def numbers (way : Nat → List (Int × Int)) : String :=
  let ((g0, g1), (l0, l1)) := stat way
  "<p>Over the step the gap between two neighbours runs from <b>" ++ toString g0 ++ "</b> to <b>" ++
    toString g1 ++ "</b>, and the length of the rank from <b>" ++ toString l0 ++ "</b> to <b>" ++
    toString l1 ++ "</b>. Both pictures have 16 and 664.</p>\n"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>A row whose lengths change</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">A row whose lengths change</h1>\n" ++
    "<p>The second box gets wider and the third narrower by as much. " ++
    "<button onclick=\"document.querySelectorAll('svg').forEach(s=>s.replaceWith(s.cloneNode(true)))\">" ++
    "play again</button></p>\n" ++
    "<h2 style=\"font-weight:400\">1. Each box at its own time</h2>\n" ++
    (panel (motion staggered) "a").render ++ "\n" ++ numbers (wayOwn staggered) ++
    "<h2 style=\"font-weight:400\">2. One timing, each length mixed by itself</h2>\n" ++
    numbers (wayLengths (together settle 0)) ++
    "<h2 style=\"font-weight:400\">3. One timing, the edges mixed, an easing in range</h2>\n" ++
    (panel (motion (together settle)) "c").render ++ "\n" ++ numbers (wayEdges (together settle 0)) ++
    "<h2 style=\"font-weight:400\">4. The same, with an easing that passes its end</h2>\n" ++
    (panel (motion (together Easing.backOut)) "d").render ++ "\n" ++
    numbers (wayEdges (together Easing.backOut 0)) ++ "</body>\n"

#eval [stat (wayOwn staggered), stat (wayLengths (together settle 0)),
  stat (wayEdges (together settle 0)), stat (wayEdges (together Easing.backOut 0))]
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/row.html" page
