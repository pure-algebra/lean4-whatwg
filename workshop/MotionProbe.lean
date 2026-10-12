import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Stroke

/-! A probe of motion as data (slice S12 of `docs/SVG-PACKAGE-PLAN.md`), with data like
lean4-effect4's. Run it from the repository root after `lake build`:

    lake env lean workshop/MotionProbe.lean

It writes `docs/research/2026-10-12-motion-probe/pfork.html`. No module imports this file, and
no gate reads its output.

The data is one frame of lean4-effect4's own viewer, read from
`docs/research/2026-10-10-live-graph-support/run-view/render/003.svg` of that repository: the
program `pFork`, its seven rows with their keys, and its two fibers with the fork between them.
The frame before it is that frame less the body of the fork: four rows and one fiber. The step
between the two is one picture and its tracks. A kept row moves to its new place, a new row
appears, the new fiber grows, and the fork draws itself.

The page shows the step twice: as the browser animates it from the kit's CSS, and as five
still pictures at the moments 0, 250, 500, 750 and 1000 that the kit's own reading
(`Track.at`) computes. The two must agree. -/

open Whatwg.Html
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- A row of the program: its key, its depth, its node and its type. -/
structure Row where
  key : String
  depth : Nat
  node : String
  type : String

/-- A fiber: its key, its box and its two lines. -/
structure Fiber where
  key : String
  box : Box
  lines : List String

/-- A fork: its key and its two ends. -/
structure Fork where
  key : String
  a : Vec
  b : Vec

/-- The frame of `pFork`, as lean4-effect4 draws it. -/
def rowsAfter : List Row :=
  [⟨"[]", 0, "bind", "Exit.Exit<number, never>"⟩,
    ⟨"[0]", 1, "withFiber", "Fiber.Fiber<number, never>"⟩,
    ⟨"[0 0]", 2, "fork { startImmediately := false, daemon := false, maskMode := inherit }", ""⟩,
    ⟨"[0 0 0]", 3, "bind", "number"⟩,
    ⟨"[0 0 0 0]", 4, "yieldNow 0", "void"⟩,
    ⟨"[0 0 0 1]", 4, "succeed (lit 7)", "number"⟩,
    ⟨"[1]", 1, "awaitFiber (var 0) awaitValue", "Exit.Exit<number, never>"⟩]

def fibersAfter : List Fiber :=
  [⟨"fiber 0", .ofSize ⟨72, 376⟩ 120 48, ["fiber 0", "exit: success"]⟩,
    ⟨"fiber 1", .ofSize ⟨24, 448⟩ 216 48, ["fiber 1 · forked at [0 0]", "exit: success"]⟩]

def forksAfter : List Fork := [⟨"fork 0 1", ⟨654 / 5, 424⟩, ⟨654 / 5, 448⟩⟩]

/-- The frame before: the fork has no body yet, and no second fiber. -/
def rowsBefore : List Row := rowsAfter.filter fun r => r.key.length ≤ 5

def fibersBefore : List Fiber := fibersAfter.take 1

/-! ## A frame as marks -/

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d
def rule : Rgb := .ofNat 0x45433f

/-- What a new mark does as it enters. -/
inductive Kind where
  | row | box | edge

/-- A mark: a key, a place, how it enters, and its element under attributes of motion. -/
structure Mark where
  key : String
  place : IVec
  kind : Kind
  node : ({t : Tag} → List (SvgAttr t)) → SvgNode

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb ink), .xmlSpacePreserve]

def rowMark (r : Row) (i : Nat) : Mark :=
  let y : Int := 120 + 24 * i
  { key := r.key, place := ⟨0, y⟩, kind := .row
    node := fun more => Svg.g more
      [Svg.label ⟨24, y⟩ r.key face,
        Svg.label ⟨112 + 24 * (r.depth : Rat), y⟩
          (if r.type.isEmpty then r.node else r.node ++ " : " ++ r.type) face] }

def fiberMark (f : Fiber) : Mark :=
  { key := f.key, place := ⟨f.box.x0.floor, f.box.y0.floor⟩, kind := .box
    node := fun more => Svg.g more
      (Svg.loops [Cubic.roundRect f.box 4] [.fill (.rgb ground)] ::
        Svg.loops (Cubic.ring f.box 4 1) [.fill (.rgb ink), .fillRule true] ::
        f.lines.zipIdx.map fun (s, i) =>
          Svg.label ⟨f.box.x0 + 8, f.box.y0 + 16 + 24 * (i : Rat)⟩ s face) }

/-- The width of a fork's line, and how far the noise moves each of its edges, as
lean4-effect4's look has them. -/
def forkWidth : Rat := 12 / 5

def forkNoise : Rat := 7 / 20

/-- A fork: an organic stroke along its centre line, a filled outline. It is drawn through a
mask, the centre line as a plain stroke, and the track that reveals it is on that line. The
line is as wide as the stroke at its widest (`Stroke.organic_band`) and one unit more. -/
def forkMark (f : Fork) : Mark :=
  let centre := (Curve.bumpY (1 / 2)).cubics [f.a, f.b]
  let seed := Noise.seedOf f.key
  let outline :=
    Stroke.stroke centre (Stroke.organic seed (forkWidth / 2) forkNoise 40)
      (Stroke.organic (seed + 7) (forkWidth / 2) forkNoise 40)
  { key := f.key, place := ⟨f.a.x.floor, f.a.y.floor⟩, kind := .edge
    node := fun more =>
      Svg.g []
        (Svg.revealed ("mask-" ++ f.key.replace " " "-")
          (Svg.revealLine centre (forkWidth * (1 + forkNoise) + 1) more)
          [Svg.loops [outline] [.fill (.rgb ink)]]) }

/-- The two collars of a fork, where its line leaves one box and meets the next. They appear
with the line, under a key of their own. -/
def collarMark (f : Fork) : Mark :=
  { key := f.key ++ " collars", place := ⟨f.a.x.floor, f.a.y.floor⟩, kind := .row
    node := fun more =>
      Svg.loops [Stroke.collar f.a forkWidth 6 true, Stroke.collar f.b forkWidth 6 false]
        ([.fill (.rgb ink)] ++ more) }
def frame (rows : List Row) (fibers : List Fiber) (forks : List Fork) : List Mark :=
  rows.zipIdx.map (fun (r, i) => rowMark r i) ++ fibers.map fiberMark ++ forks.map forkMark ++
    forks.map collarMark

/-! ## The step as tracks -/

/-- lean4-effect4's critically damped spring, at every twentieth of its progress. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

/-- lean4-effect4's underdamped spring. -/
def spring : Easing :=
  .stops [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026,
    1019, 1012, 1007, 1003, 1000]

/-- The length of a step, in milliseconds. -/
def stepMs : Nat := 600

/-- How a new mark enters: a row appears after the rows before it, a fork draws itself, and
the box at its end expands on a spring. -/
def enterTrack (n : Mark) (k : Nat) : Track String :=
  match n.kind with
  | .row => ⟨n.key, .fade 0 1000, .per stepMs { delay := 180 + 36 * k, duration := 180 }⟩
  | .edge => ⟨n.key, .reveal 0 1000,
      .per stepMs { delay := 180, duration := 132, ease := Easing.cubicOut }⟩
  | .box => ⟨n.key, .grow 0 1000, .per stepMs { delay := 264, duration := 216, ease := spring }⟩

/-- **The motion of a step**: the join of the two frames by key, and a track for each
selection. A kept mark moves from its old place and settles; a new one enters; an old one
fades. -/
def motion (old new : List Mark) : Motion String :=
  let j := join Mark.key old new
  let moves : Motion String :=
    j.update.map fun p =>
      ⟨p.2.key, .shift (p.1.place - p.2.place) 0, .per stepMs { duration := 270, ease := settle }⟩
  let enters : Motion String := j.enter.zipIdx.map fun (n, k) => enterTrack n k
  let exits : Motion String :=
    j.exit.map fun o =>
      ⟨o.key, .fade 1000 0, .per stepMs { duration := 150, ease := Easing.cubicIn }⟩
  Motion.within (moves ++ enters ++ exits)

/-! ## The page -/

/-- One picture: the marks under the attributes that a function of the key gives. -/
def picture (marks : List Mark) (attrs : String → ({t : Tag} → List (SvgAttr t)))
    (sheet : Option String) (width height : Nat) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat width)), .attr .height (.user (.ofNat height)),
      .attr .viewBox (ViewBox.ofSize 800 520)]
    (sheet.toList.map Svg.styleSheet ++
      [Svg.box (.ofSize ⟨0, 0⟩ 800 520) [.fill (.rgb ground)]] ++
      marks.map fun k => k.node (attrs k.key))

def before : List Mark := frame rowsBefore fibersBefore []

def after : List Mark := frame rowsAfter fibersAfter forksAfter

def step : Motion String := motion before after

/-- The marks of the step: the new frame's, and the old ones that leave. -/
def marks : List Mark := after ++ (join Mark.key before after).exit

def animated : SvgNode :=
  picture marks (fun key => Motion.attrs step key stepMs) (some (Motion.sheet step)) 800 520

def still (t : Nat) : SvgNode := picture marks (fun key => Motion.attrsAt step key t) none 400 260

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>pFork: a step as one picture and its tracks" ++
    "</title>\n<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">pFork: a step as one picture and its tracks</h1>\n" ++
    "<p>The browser animates this picture from the CSS that the kit wrote. " ++
    "<button onclick=\"const s=document.querySelector('svg');s.replaceWith(s.cloneNode(true))\">" ++
    "play again</button></p>\n" ++
    animated.render ++
    "\n<p>The same step at the moments 0, 250, 500, 750 and 1000, as the kit's own reading " ++
    "computes them, with no animation.</p>\n<div>" ++
    String.join ([0, 250, 500, 750, 1000].map fun t => (still t).render) ++ "</div>\n</body>\n"

#eval animated.okIn Whatwg.Html.Content.Ctx.flow
#eval IO.println (Motion.sheet step)
#eval step.length
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/pfork.html" page
