import Whatwg.Html.Node.Svg
import Whatwg.Html.Print.Render

/-!
# WhatwgTest.Html.SvgNode

Readers, controls and finite evaluations of the typed SVG node (slice S5 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-34): `Whatwg/Html/Node/Svg.lean`.

The trees here are built as a program builds them: from constructors, with numbers that are
variables. The picture has the elements and the attributes that lean4-effect4's picture writer
emits (`tools/Tools/View/Output.lean`, read at `707b9a01`): a root with its namespace, a
`viewBox` and a size; a filled box with a key; a stroked curve; a text; and a clipped group.

A reader applies the connector `SvgNode.valuesOk_toRaw` at a tree whose numbers are not known.
A control is a typed tree that the checker refuses: the type gives the values and not the
structure. A finite evaluation prints a closed tree.

What this battery does not claim: that a browser draws a printed tree as intended, or that a
typed tree is valid. The structure of these trees, for every number and text, is the battery
`WhatwgTest/Html/SvgValid.lean`.
-/

namespace WhatwgTest.Html.SvgNode

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Svg.Value

/-! ## The type of a value -/

-- The type of an attribute's value is a function of the element and the attribute: the
-- carrier of its kind, and text where the table gives it none.
example : AttrValue .path .d = PathData := rfl
example : AttrValue .svg .viewBox = ViewBox := rfl
example : AttrValue .g .transform = TransformList := rfl
example : AttrValue .line .x1 = Length := rfl
example : AttrValue .rect .x = Length := rfl
example : AttrValue .rect .width = AutoExtent := rfl
example : AttrValue .circle .r = Extent := rfl
example : AttrValue .rect .«class» = String := rfl

-- The place of a text is a list of lengths, and its rotation a list of numbers.
example : AttrValue .text .x = LengthList := rfl
example : AttrValue .tspan .dy = LengthList := rfl
example : AttrValue .text .rotate = NumberList := rfl
example : AttrValue .text .textLength = Extent := rfl

-- Controls of the table's key: the same name on an element that the sealed text gives no
-- value for is text.
example : AttrValue .linearGradient .x1 = String := rfl
example : AttrValue .pattern .x = String := rfl
example : AttrValue .feOffset .dx = String := rfl
example : AttrValue .textPath .textLength = String := rfl

/-! ## A picture, as a program builds it -/

/-- A filled box with a key: the numbers are the caller's. -/
def box (x y : Int) (w h : Nat) (role key : String) : SvgNode :=
  .element .rect
    [.attr .«class» ("e4-fill-" ++ role), .attr .x (.user (.ofInt x)), .attr .y (.user (.ofInt y)),
      .attr .width (.user (.ofNat w)), .attr .height (.user (.ofNat h)),
      .attr .fill "var(--ink)", .attr .fill_opacity "0.8", .data "key" key] []

/-- A stroked cubic curve, in thousandths of a unit. Each number is trimmed: no zero is
written at the end of a fraction. -/
def curve (p0 p1 p2 p3 : Int × Int) (role : String) : SvgNode :=
  let pt (p : Int × Int) : Point := ⟨(Decimal.ofScaled p.1 3).trim, (Decimal.ofScaled p.2 3).trim⟩
  .element .path
    [.attr .«class» ("e4-stroke-" ++ role),
      .attr .d (.path (.moveto false (pt p0) [] [.curveto false (pt p1, pt p2, pt p3) []])),
      .attr .fill "none", .attr .stroke "currentColor", .attr .stroke_width "1.5"] []

/-- A text at a place, scaled by the ratio. Its `x` and `y` are lists of lengths, here of one
each. -/
def label (x base : Nat) (ratio : Nat) (content : String) : SvgNode :=
  .element .text
    [.attr .x (.single (.user (.ofInt x))), .attr .y (.single (.user (.ofInt base))),
      .attr .«class» "e4-text",
      .attr .transform [.scale (.ofInt ratio) none], .attr .xml_space "preserve"]
    [.text content]

/-- A group clipped to a box, with the box's clip path before it. -/
def clipped (id : Nat) (x y : Int) (w h : Nat) (children : List SvgNode) : List SvgNode :=
  [.element .clipPath [.attr .id ("c" ++ toString id)]
      [.element .rect [.attr .x (.user (.ofInt x)), .attr .y (.user (.ofInt y)),
        .attr .width (.user (.ofNat w)), .attr .height (.user (.ofNat h))] []],
    .element .g [.attr .clip_path ("url(#c" ++ toString id ++ ")")] children]

/-- The picture: `W` by `H` units at a ratio, in a look. -/
def picture (look : String) (W H ratio : Nat) (marks : List SvgNode) : SvgNode :=
  .element .svg
    [.xmlns, .attr .«class» "e4-view", .data "look" look,
      .attr .width (.user (.ofNat W)), .attr .height (.user (.ofNat H)),
      .attr .viewBox ⟨0, 0, .ofNat (ratio * W), .ofNat (ratio * H)⟩]
    (.element .title [] [.text "A chart"] :: marks)

-- Reader of the connector (V7): every picture's values are of their grammars, whatever its
-- numbers, its texts and its marks. Nothing is evaluated.
example (look : String) (W H ratio : Nat) (marks : List SvgNode) :
    valuesOk (picture look W H ratio marks).toRaw = true :=
  SvgNode.valuesOk_toRaw _

-- The same as the absence of a refusal.
example (x y : Int) (w h : Nat) (role key : String) :
    explainValues (box x y w h role key).toRaw = none :=
  SvgNode.explainValues_toRaw _

/-- A closed picture. -/
def chart : SvgNode :=
  picture "plain" 320 200 2
    ([box 10 20 30 160 "accent" "a",
      curve (10000, 20000) (15000, 25000) (30000, 150000) (40000, 180000) "ink"] ++
      clipped 1 0 0 320 200 [label 10 195 2 "a  b"])

-- The checker accepts the raw tree of the closed picture: one run over its written names.
-- The proof of it is `SvgNode.okIn`, which reads no name (`WhatwgTest/Html/SvgValid.lean`).
#guard validIn Ctx.flow chart.toRaw

-- The printed markup: each typed value in its grammar's one spelling.
#guard Print.render chart.toRaw ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"e4-view\" data-look=\"plain\" " ++
  "width=\"320\" height=\"200\" viewBox=\"0 0 640 400\"><title>A chart</title>" ++
  "<rect class=\"e4-fill-accent\" x=\"10\" y=\"20\" width=\"30\" height=\"160\" " ++
  "fill=\"var(--ink)\" fill-opacity=\"0.8\" data-key=\"a\"></rect>" ++
  "<path class=\"e4-stroke-ink\" d=\"M10,20C15,25 30,150 40,180\" " ++
  "fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.5\"></path>" ++
  "<clipPath id=\"c1\"><rect x=\"0\" y=\"0\" width=\"320\" height=\"200\"></rect></clipPath>" ++
  "<g clip-path=\"url(#c1)\"><text x=\"10\" y=\"195\" class=\"e4-text\" " ++
  "transform=\"scale(2)\" xml:space=\"preserve\">a  b</text></g></svg>"

/-! ## The type gives the values, and the checker the structure -/

-- Control: a typed tree may put an element where the content model refuses it. Its values
-- pass by the law, and the checker refuses the tree.
example (p : PathData) :
    valuesOk (SvgNode.element .rect [] [.element .path [.attr .d p] []]).toRaw = true :=
  SvgNode.valuesOk_toRaw _
#guard !validIn Ctx.flow
  (SvgNode.element .svg [] [.element .rect [] [.element .path [] []]]).toRaw

-- Control: a typed tree may name an attribute its element does not take. `d` on `rect` has
-- the type of path data, and the checker refuses the attribute by its name.
#guard !validIn Ctx.flow
  (SvgNode.element .svg [] [.element .rect [.attr .d .none] []]).toRaw

-- Control: a name may repeat in a typed attribute list. The checker refuses it.
#guard !validIn Ctx.flow (SvgNode.element .svg [.attr .«class» "a", .attr .«class» "b"] []).toRaw

/-! ## Below an integration point -/

/-- HTML content below `foreignObject` is a raw subtree. Its premise is one evaluation of its
names: it holds no SVG value. -/
def note : SvgNode :=
  .element .svg []
    [.element .foreignObject [.attr .width 100, .attr .height 40]
      [.raw (.element "p" [("class", "note")] [.text "x"]) (by decide +kernel)]]

#guard validIn Ctx.flow note.toRaw
example : valuesOk note.toRaw = true := SvgNode.valuesOk_toRaw _

-- A nested `svg` below an integration point is a typed element again.
#guard validIn Ctx.flow
  (SvgNode.element .svg [] [.element .foreignObject [] [.element .svg [] [.element .rect [] []]]]).toRaw

/-! ## Reading a value -/

-- `readValue` reads a text as a value of an attribute's type: by the grammar where the
-- attribute has a kind, and as itself where it has none.
#guard (readValue (kindOf .line .x1) "1.5em") == some (⟨⟨15, -1⟩, .em⟩ : Length)
#guard (readValue (kindOf .line .x1) "wide") == none
#guard (readValue (kindOf .linearGradient .x1) "wide") == some "wide"

-- Reader of the retraction at the type (V1): the text of a typed value reads back.
example (p : PathData) :
    readValue (some .pathData) (valueTextOf (some .pathData) p) = some p :=
  readValue_valueTextOf (some .pathData) p

end WhatwgTest.Html.SvgNode
