import Whatwg.Svg.Geometry.Arith
import Whatwg.Svg.Geometry.Pen
import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Geometry.Affine
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgKeyword
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgNest
import Whatwg.Html.Node.SvgValid
import Whatwg.Html.Print.Picture
import WhatwgTest.Html.SvgPicture

/-!
# WhatwgTest.Html.SvgKit

The picture writer of lean4-effect4's `tools/Tools/View/Output.lean` on the kit of slice S10
of `docs/SVG-PACKAGE-PLAN.md`, whole: `Dev.svg` and `svg` as typed nodes, the fold over the
calls, the proof that every picture passes the structure test, and `stepDown` of
`tools/Tools/View/Graph.lean` on the kit's curves. The consumer is read at its current
checkout, `707b9a01`. This module imports nothing of that package. It restates the device
calls and the look under the consumer's names. A box of device pixels is that of
`WhatwgTest/Html/SvgPicture.lean`, the port of the same writer onto the bare node. Since slice
S11 a cubic segment is the kit's own `Cubic`, exact: a curve is `Svg.cubics`, a shape is
`Svg.loops`, and an edge is a list of segments from the kit's `Curve`.

How it differs from that port:

- **In what it reads.** That port read a device cut down to three roles, colours as text and a
  text with no face. This one reads the consumer's: six roles, a colour as `0xRRGGBB` under
  the rule of the hue, the font of a face on every text, `cells` with its room, and a weight
  that is an integer.
- **In size.** The writer, the fold and the picture are 93 lines here and 133 there, and here
  they write the attributes of a font and the text of `cells` as well. The structure proof is
  72 lines here and 118 there.
- **In what the writer proves.** That port stated the fold and proved it: a state, a step, a
  closing of the open cuts, an invariant, and six lemmas about them. Here the fold is
  `SvgNode.nest`, and the writer proves three things. Each kind of mark passes, by one
  evaluation. A cut keeps a passing list passing, which is `Svg.okAllAt_clipped` and one
  evaluation of its clip path. Each call passes the test of a call, `Flat.okAt` (`flat_ok`):
  a case split that holds no argument, where a mark is one of those marks and a start or an
  end has no test. The marks are then `SvgNode.okAllAt_nest_of_calls`, and the picture is
  `Frame.okIn_of` and one evaluation of its attributes.

What this battery does not claim: that the picture is the one lean4-effect4 draws. No theorem
relates this writer to that package's string writer. The guards compare one sample and five
edges with texts copied by hand from a reading of its code, and the comments beside them say
where the two differ: the order of the attributes on `rect` and `path`, the spelling of a
path, one line for a line a call, `'` and `>` as they are, and a control point of an edge
that the consumer rounds down to a thousandth at each step, where the kit computes exactly and
rounds once, to the nearest thousandth, when it writes.
-/

namespace WhatwgTest.Html.SvgKit

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Svg.Value

/-- A box of whole device pixels (`Tools.View.Rect`). The kit's `Box` and `Cubic` are exact, and
a curve and a shape are of the kit's `Cubic`. -/
abbrev Rect := WhatwgTest.Html.SvgPicture.Box

/-! ## The device calls and the look, as the consumer has them -/

/-- A role of the tokens (`Tools.View.Role`). Its colour is the look's. -/
inductive Role where
  | ground | ink | rule | host | failure | resource

/-- The role's name in a class (`Role.tokenName`). -/
def Role.token : Role → String
  | .ground => "ground" | .ink => "ink" | .rule => "rule"
  | .host => "host" | .failure => "failure" | .resource => "resource"

/-- A face of the type (`Tools.View.Face`). -/
inductive Face where
  | data | name | label | title

/-- The face's name in a class (`Face.tokenName`). -/
def Face.token : Face → String
  | .data => "data" | .name => "name" | .label => "label" | .title => "title"

/-- A face's font: its families as CSS lists them (`Font.cssFamily`), its size in thousandths
of a logical pixel, its weight, and whether it is italic. -/
structure Font where
  family : String
  size : Nat
  weight : Nat
  italic : Bool

/-- What the writer reads of a look: its name, whether a role of an agent takes its hue, the
colour of each role as `0xRRGGBB`, and the font of each face. -/
structure Look where
  name : String
  hue : Bool
  palette : Role → Nat
  faces : Face → Font

/-- The colour a role is drawn in (`Look.color`): its own, or the ink for a role of an agent
with the hue off. -/
def Look.color (look : Look) (role : Role) : Rgb :=
  .ofNat (match role with
    | .host | .failure | .resource => if look.hue then look.palette role else look.palette .ink
    | _ => look.palette role)

/-- One call to the drawing device (`Tools.View.Dev`). A box, a curve and a weight are in
device pixels, a text and a cut in logical pixels, and a shape and a tone in thousandths. -/
inductive Dev where
  | fill (role : Role) (value : Nat) (box : Rect)
  | curve (role : Role) (segment : Cubic) (weight : Int)
  | cells (x base : Int) (room : Nat) (content : String)
  | text (face : Face) (x base room : Int) (content : String)
  | cut (x y w h : Int)
  | uncut
  | hit (box : Rect)
  | shape (role : Role) (value : Nat) (paths : List (List Cubic))

/-- A call with the key of the object it draws. The empty key is no key. -/
structure Keyed where
  key : String
  call : Dev

/-! ## The writer: one node for each device call -/

/-- A point in thousandths of a device pixel, as the consumer counts it. -/
def milli (p : Int × Int) : Vec := .fixed 3 p.1 p.2

/-- A tone's value as an opacity (`opacity`): thousandths, and one from a thousand up. -/
def opacity (value : Nat) : Decimal := .fixed 3 (min value 1000)

/-- A filled box. A negative size is written as zero. -/
def fillNode (look : Look) (role : Role) (value : Nat) (b : Rect) (key : String) : SvgNode :=
  Svg.rect b.x0 b.y0 (.clamp (b.x1 - b.x0)) (.clamp (b.y1 - b.y0))
    ([.className ("e4-fill-" ++ role.token), .fill (look.color role),
      .fillOpacity (opacity value)] ++ SvgAttr.dataKey? key)

/-- A stroked cubic curve. -/
def curveNode (look : Look) (role : Role) (c : Cubic) (weight : Int) (key : String) : SvgNode :=
  Svg.cubics [c]
    ([.className ("e4-stroke-" ++ role.token), .fill .none, .stroke (look.color role),
      .strokeWidth weight] ++ SvgAttr.dataKey? key)

/-- A text in a face of the look (`textAttrs`), scaled by the ratio. -/
def textNode (look : Look) (ratio : Nat) (face : Face) (x base : Int) (content key : String) :
    SvgNode :=
  Svg.text x base content
    ([.className ("e4-text e4-face-" ++ face.token), .fontFamily (look.faces face).family,
      .fontStyle (.ofItalic (look.faces face).italic), .fontWeight (look.faces face).weight,
      .fontSize (.fixed 3 (look.faces face).size), .fill (look.color .ink),
      .attr .transform [.zoom ratio], .xmlSpacePreserve] ++ SvgAttr.dataKey? key)

/-- The text of `cells` in its room: a longer one is cut, and ends in an ellipsis. -/
def shown (room : Nat) (s : String) : String :=
  if s.length ≤ room then s else (s.take (room - 1)).toString ++ "…"

/-- An invisible box that takes the pointer. -/
def hitNode (b : Rect) (key : String) : SvgNode :=
  Svg.rect b.x0 b.y0 (.clamp (b.x1 - b.x0)) (.clamp (b.y1 - b.y0))
    ([.fill .none, .pointerEvents .all] ++ SvgAttr.dataKey? key)

/-- A filled shape of several closed paths in one `d`. -/
def shapeNode (look : Look) (role : Role) (value : Nat) (paths : List (List Cubic))
    (key : String) : SvgNode :=
  Svg.loops paths
    ([.className ("e4-fill-" ++ role.token), .fillRule .evenodd, .fill (look.color role),
      .fillOpacity (opacity value)] ++ SvgAttr.dataKey? key)

/-- An open cut: the index of its call, and its box in logical pixels. -/
structure Cut where
  id : Nat
  x : Int
  y : Int
  w : Int
  h : Int

/-- A cut around the marks drawn inside it: a clip path of its box in device pixels, and the
group it clips. -/
def cutNodes (ratio : Nat) (c : Cut) (children : List SvgNode) : List SvgNode :=
  Svg.clipped ("c" ++ toString c.id)
    [Svg.rect (ratio * c.x : Int) (ratio * c.y : Int) (.clamp (ratio * c.w))
      (.clamp (ratio * c.h))] children

/-! ## The fold and the picture -/

/-- One device call with its index in the list, as a call of a flat drawing: a mark, the start
of a cut under that index, or the end of the innermost cut. -/
def flat (look : Look) (ratio : Nat) (d : Keyed × Nat) : SvgNode.Flat Cut :=
  match d.1.call with
  | .fill role value b => .leaf (fillNode look role value b d.1.key)
  | .curve role c weight => .leaf (curveNode look role c weight d.1.key)
  | .cells x base room s => .leaf (textNode look ratio .data x base (shown room s) d.1.key)
  | .text face x base _ s => .leaf (textNode look ratio face x base s d.1.key)
  | .cut x y w h => .enter ⟨d.2, x, y, w, h⟩
  | .uncut => .leave
  | .hit b => .leaf (hitNode b d.1.key)
  | .shape role value paths => .leaf (shapeNode look role value paths d.1.key)

/-- The marks of a list of device calls, in order. An end with no open cut is dropped, and a
cut with no end is closed at the end of the list. -/
def marksOf (look : Look) (ratio : Nat) (calls : List Keyed) : List SvgNode :=
  SvgNode.nest (cutNodes ratio) (calls.zipIdx.map (flat look ratio))

/-- The picture (`svg`): `W` by `H` logical pixels at a ratio, in a look. -/
def picture (look : Look) (W H ratio : Nat) (calls : List Keyed) : SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := ratio }
    [.className "e4-view", .data "look" look.name] (marksOf look ratio calls)

/-! ## The form of an edge -/

/-- The form of an edge between two ranks, as the consumer's look names it
(`Tools.View.Curve`). Each is a form of the kit's `Curve`. -/
inductive Form where
  | bumpY | linear | stepY

/-- A step down from `a` to `b`, both in thousandths, in a form (`stepDown`): cubic segments,
as the consumer's are. A `bumpY` step is the kit's `Curve.bumpY` at `reach` per mille, d3's
bump at 500: each control is that part of the drop from its end, exactly, where the consumer
rounds it down to a thousandth. A `stepY` step between two ends in one column is a straight
step, as it is in the consumer. -/
def stepDown (form : Form) (reach : Nat) (a b : Int × Int) : List Cubic :=
  match form with
  | .bumpY => (Curve.bumpY ((reach : Rat) / 1000)).cubics [milli a, milli b]
  | .linear => Curve.linear.cubics [milli a, milli b]
  | .stepY => (if a.1 = b.1 then Curve.linear else Curve.stepY).cubics [milli a, milli b]

/-! ## The structure of every picture

Each statement is at `Pos.inSvg x` for every set `x` of HTML exclusions, so the picture's
theorem holds at every HTML position that admits `svg`. -/

variable (x : Exclusions)

theorem fillNode_ok (look : Look) (role : Role) (value : Nat) (b : Rect) (key : String) :
    (fillNode look role value b key).okAt (Pos.inSvg x) = true := by
  unfold fillNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

theorem curveNode_ok (look : Look) (role : Role) (c : Cubic) (weight : Int) (key : String) :
    (curveNode look role c weight key).okAt (Pos.inSvg x) = true := by
  unfold curveNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

theorem textNode_ok (look : Look) (ratio : Nat) (face : Face) (cx base : Int)
    (content key : String) :
    (textNode look ratio face cx base content key).okAt (Pos.inSvg x) = true := by
  unfold textNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

theorem hitNode_ok (b : Rect) (key : String) : (hitNode b key).okAt (Pos.inSvg x) = true := by
  unfold hitNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

theorem shapeNode_ok (look : Look) (role : Role) (value : Nat) (paths : List (List Cubic))
    (key : String) : (shapeNode look role value paths key).okAt (Pos.inSvg x) = true := by
  unfold shapeNode SvgAttr.dataKey?
  cases key.isEmpty <;> conv => lhs; whnf

/-- A cut passes among the marks when the marks inside it do. -/
theorem cutNodes_ok (ratio : Nat) (c : Cut) (children : List SvgNode)
    (h : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    SvgNode.okAllAt (Pos.inSvg x) (cutNodes ratio c children) = true :=
  Svg.okAllAt_clipped x _ _ children (by conv => lhs; whnf) h

/-- Each call passes the test of a call: its mark passes, and a start or an end has none. -/
theorem flat_ok (look : Look) (ratio : Nat) (d : Keyed × Nat) :
    (flat look ratio d).okAt (Pos.inSvg x) = true := by
  obtain ⟨⟨key, call⟩, i⟩ := d
  cases call with
  | fill role value b => exact fillNode_ok x look role value b key
  | curve role c weight => exact curveNode_ok x look role c weight key
  | cells cx base room s => exact textNode_ok x look ratio .data cx base _ key
  | text face cx base room s => exact textNode_ok x look ratio face cx base s key
  | cut | uncut => rfl
  | hit b => exact hitNode_ok x b key
  | shape role value paths => exact shapeNode_ok x look role value paths key

/-- The marks of every list of device calls pass where the marks of a picture stand. -/
theorem marksOf_ok (look : Look) (ratio : Nat) (calls : List Keyed) :
    SvgNode.okAllAt (Pos.inSvg x) (marksOf look ratio calls) = true :=
  SvgNode.okAllAt_nest_of_calls _ _ (cutNodes_ok x ratio) _ _ (flat_ok x look ratio)

/-- The structure of every picture, at every HTML position that admits `svg`: for every look,
size, ratio and list of device calls, balanced or not. -/
theorem picture_okIn (ctx : Ctx) (hctx : ctx.admits .svg = true) (look : Look) (W H ratio : Nat)
    (calls : List Keyed) : (picture look W H ratio calls).okIn ctx = true :=
  Svg.Frame.okIn_of hctx _ (by conv => lhs; whnf) (marksOf_ok _ look ratio calls)

/-- The checker accepts the raw tree of every picture in flow content (law V8). -/
theorem picture_valid (look : Look) (W H ratio : Nat) (calls : List Keyed) :
    validIn Ctx.flow (picture look W H ratio calls).toRaw = true :=
  SvgNode.validIn_of_okIn (picture_okIn Ctx.flow (by decide +kernel) look W H ratio calls)

/-- Every value of every picture is of its grammar (law V7). -/
theorem picture_values (look : Look) (W H ratio : Nat) (calls : List Keyed) :
    valuesOk (picture look W H ratio calls).toRaw = true :=
  SvgNode.valuesOk_toRaw _

/-! ## The port beside the consumer -/

/-- The consumer's dark look, with the hue on. -/
def plain : Look where
  name := "plain"
  hue := true
  palette
    | .ground => 0x14110d | .ink => 0xf3f4f6 | .rule => 0x45433f
    | .host => 0xc0851f | .failure => 0xbd3931 | .resource => 0x359b75
  faces
    | .data => ⟨"Menlo, 'DejaVu Sans Mono', monospace", 13288, 400, false⟩
    | .name => ⟨"Georgia, Charter, serif", 15000, 400, false⟩
    | .label => ⟨"Georgia, Charter, serif", 13500, 400, true⟩
    | .title => ⟨"Georgia, Charter, serif", 20000, 400, false⟩

/-- The calls of the sample of `WhatwgTest/Html/SvgPicture.lean`, its text in a face, and then
a text of cells that is longer than its room. -/
def sample : List Keyed :=
  [⟨"n1", .fill .ground 1000 ⟨0, 0, 40, 20⟩⟩,
   ⟨"", .fill .ink 500 ⟨2, 2, 38, 18⟩⟩,
   ⟨"e<1>", .curve .ink ⟨⟨10, 20⟩, ⟨10, 30⟩, ⟨30, 30⟩, ⟨30, 40⟩⟩ 2⟩,
   ⟨"", .cut 0 0 20 10⟩,
   ⟨"n1", .text .label 4 14 12 "a<b & c"⟩,
   ⟨"", .uncut⟩,
   ⟨"n1", .hit ⟨0, 0, 40, 20⟩⟩,
   ⟨"s", .shape .host 350
     [[⟨milli (0, 0), milli (1000, 0), milli (2500, 500), milli (3005, 1000)⟩,
       ⟨milli (3005, 1000), milli (2000, 1500), milli (1000, 2000), milli (0, 0)⟩],
      [⟨milli (500, 500), milli (600, 500), milli (700, 600), milli (500, 500)⟩]]⟩,
   ⟨"n2", .cells 4 30 8 "let 'x' = 1"⟩]

-- The picture as the text of a file. `svg` of the consumer writes the same elements, with
-- the same attributes and values, and differs in this:
--   * a line for each call, where this is one line;
--   * `class` first on `rect` and `path`, where `Svg.rect` and `Svg.path` put the geometry
--     first: `<rect class="e4-fill-ground" x="0" y="0" width="40" height="20" …/>`;
--   * `d="M 10 20 C 10 30, 30 30, 30 40"`, and ` Z M ` between the two parts of the shape;
--   * `&apos;` for `'` in `font-family` and in the text of the cells, and `&gt;` for the `>`
--     of the key `e<1>`.
#guard (picture plain 40 20 2 sample).renderXmlUnchecked ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"e4-view\" data-look=\"plain\" " ++
  "width=\"40\" height=\"20\" viewBox=\"0 0 80 40\">" ++
  "<rect x=\"0\" y=\"0\" width=\"40\" height=\"20\" class=\"e4-fill-ground\" " ++
  "fill=\"#14110d\" fill-opacity=\"1\" data-key=\"n1\"/>" ++
  "<rect x=\"2\" y=\"2\" width=\"36\" height=\"16\" class=\"e4-fill-ink\" " ++
  "fill=\"#f3f4f6\" fill-opacity=\"0.5\"/>" ++
  "<path d=\"M10,20C10,30 30,30 30,40\" class=\"e4-stroke-ink\" fill=\"none\" " ++
  "stroke=\"#f3f4f6\" stroke-width=\"2\" data-key=\"e&lt;1>\"/>" ++
  "<clipPath id=\"c3\"><rect x=\"0\" y=\"0\" width=\"40\" height=\"20\"/></clipPath>" ++
  "<g clip-path=\"url(#c3)\"><text x=\"4\" y=\"14\" class=\"e4-text e4-face-label\" " ++
  "font-family=\"Georgia, Charter, serif\" font-style=\"italic\" font-weight=\"400\" " ++
  "font-size=\"13.5\" fill=\"#f3f4f6\" transform=\"scale(2)\" xml:space=\"preserve\" " ++
  "data-key=\"n1\">a&lt;b &amp; c</text></g>" ++
  "<rect x=\"0\" y=\"0\" width=\"40\" height=\"20\" fill=\"none\" pointer-events=\"all\" " ++
  "data-key=\"n1\"/>" ++
  "<path d=\"M0,0C1,0 2.5,0.5 3.005,1C2,1.5 1,2 0,0ZM0.5,0.5C0.6,0.5 0.7,0.6 0.5,0.5Z\" " ++
  "class=\"e4-fill-host\" fill-rule=\"evenodd\" fill=\"#c0851f\" fill-opacity=\"0.35\" " ++
  "data-key=\"s\"/>" ++
  "<text x=\"4\" y=\"30\" class=\"e4-text e4-face-data\" " ++
  "font-family=\"Menlo, 'DejaVu Sans Mono', monospace\" font-style=\"normal\" " ++
  "font-weight=\"400\" font-size=\"13.288\" fill=\"#f3f4f6\" transform=\"scale(2)\" " ++
  "xml:space=\"preserve\" data-key=\"n2\">let 'x'…</text></svg>"

-- One edge in each form, from (10, 20) to (30, 45.001). `stepDown` gives cubic segments, as
-- the consumer's does, and `Path.ofCubics` writes them at three places. Beside each is what
-- the consumer writes for the same numbers: `M p0 C p1, p2, p3` for each segment.

-- `bumpY`. The consumer: `M 10 20 C 10 32.5, 30 32.501, 30 45.001`. It moves each control
-- from its own end by half the drop, rounded down to a thousandth, so the two are a
-- thousandth apart. The kit's two are at the middle, exactly, and are written alike.
#guard toString (Path.ofCubics (stepDown .bumpY 500 (10000, 20000) (30000, 45001))) ==
  "M10,20C10,32.501 30,32.501 30,45.001"

-- `bumpY` to (30, 46), a whole drop. The consumer: `M 10 20 C 10 33, 30 33, 30 46`. The kit
-- writes the same numbers.
#guard toString (Path.ofCubics (stepDown .bumpY 500 (10000, 20000) (30000, 46000))) ==
  "M10,20C10,33 30,33 30,46"

-- `bumpY` at 333 per mille. The consumer: `M 10 20 C 10 28.325, 30 36.676, 30 45.001`. The
-- kit's controls are 8.325333 from their ends, exactly, and three places write the consumer's
-- numbers; six places write the product whole.
#guard toString (Path.ofCubics (stepDown .bumpY 333 (10000, 20000) (30000, 45001))) ==
  "M10,20C10,28.325 30,36.676 30,45.001"
#guard toString (Path.ofCubics (stepDown .bumpY 333 (10000, 20000) (30000, 45001)) 6) ==
  "M10,20C10,28.325333 30,36.675667 30,45.001"

-- `linear`. The consumer: `M 10 20 C 10 20, 30 45.001, 30 45.001`, a cubic with its controls
-- on its ends. The kit writes a lineto.
#guard toString (Path.ofCubics (stepDown .linear 500 (10000, 20000) (30000, 45001))) ==
  "M10,20L30,45.001"

-- `stepY`. The consumer: three paths, `M 10 20 C 10 20, 10 32.5, 10 32.5`,
-- `M 10 32.5 C 10 32.5, 30 32.5, 30 32.5` and `M 30 32.5 C 30 32.5, 30 45.001, 30 45.001`.
-- It turns at the middle rounded down; the kit's three segments are one subpath that turns at
-- the middle.
#guard toString (Path.ofCubics (stepDown .stepY 500 (10000, 20000) (30000, 45001))) ==
  "M10,20V32.501H30V45.001"

-- `stepY` between two ends in one column is one straight segment.
#guard toString (Path.ofCubics (stepDown .stepY 500 (10000, 20000) (10000, 45001))) ==
  "M10,20V45.001"

-- What the kit knows of an edge and the consumer proves by hand: its segments are a chain from
-- one end to the other, and the edge between two moved ends is the edge, moved.
example (a b : Vec) (r : Rat) : Cubic.Chained ((Curve.bumpY r).cubics [a, b]) = true :=
  Curve.chained_cubics _ _

example (c : Curve) (a b d : Vec) :
    c.cubics [a + d, b + d] = (c.cubics [a, b]).map (Cubic.move d) :=
  Curve.cubics_move c d [a, b]
end WhatwgTest.Html.SvgKit
