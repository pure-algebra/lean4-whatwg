import Whatwg.Html.Node.SvgKit
import Whatwg.Html.Node.SvgDefs.Laws
import WhatwgTest.Html.SvgKit

/-!
# WhatwgTest.Html.SvgUseKit

The parts of the ports and of two probes that slice S17 of `docs/SVG-PACKAGE-PLAN.md` touches,
written on its additions, and one new picture. The additions are the literals of
`Whatwg/Html/Node/SvgLit.lean`, the keywords of `SvgKeyword.lean`, the definitions that are
referred to of `SvgDefs.lean` with their laws, and the one import of `SvgKit.lean`.

**The port** (`WhatwgTest/Html/SvgKit.lean`, the consumer's picture writer). Three of its marks
wrote a flag or a text where SVG has a keyword. Since this slice the port itself writes them
with the keywords (`fillRule`, `fontStyle`, `pointerEvents`), and its guards hold the markup as
it was.

**Two probes** (`workshop/MotionProbe.lean` and `workshop/TreeProbe.lean`, which no module can
import, so what they wrote is restated here beside the new form). The outer `svg`, the face of a
text, and the reveal of an edge through a mask, whose identifier each probe made from a key by
replacing characters. The reveal is written as a program of `Svg.Defs`, and a theorem says what
it writes: the mask of `Svg.revealed`, under `defs` and under a counted identifier, and its
group.

**A new picture**: the back edges of a graph, each an arc that fades in along a gradient, is
shown through a mask, and ends in an arrow head. No identifier is typed. `graph_okIn` says that
the picture passes the structure test for every list of edges, at every HTML position that
admits `svg`, and it is proved part by part with `Defs.Holds`.

**A link, a name, and the port's cuts.** A node that is a link (`nodeLink`); the picture as one
image that is read by name, its title and description under identifiers made from the stem
(`namedGraph`); and the port's own picture with each cut a clip path among the definitions of a
stem (`stemmed`), proved for every list of device calls, with the three closing laws in one.
The guards put the port's sample twice on one page: as the port writes it both pictures declare
`c3`, and under two stems they share no identifier.

What this battery does not claim: that a browser draws the new picture as its docstrings say.
The guards read the markup and the identifiers; the attributes of a gradient, a mask and a
marker are written from memory of their chapters, which are not sealed here.
-/

namespace WhatwgTest.Html.SvgUseKit

open Whatwg.Html Whatwg.Html.Content Whatwg.Svg.Value Whatwg.Svg.Scene
open Whatwg.Html.Schema (Exclusions)

/-! ## Keywords read from a text -/

-- A look read from a file holds a keyword as a text. The reader takes a keyword and refuses a
-- word that is none: the text that `.attr .stroke_linecap "Round"` would have written.
#guard (Keyword.read? "round" : Option LineCap) == some .round
#guard (Keyword.read? "Round" : Option LineCap) == none
#guard (Keyword.read? "non-scaling-stroke" : Option VectorEffect) == some .nonScalingStroke

/-! ## Two probes: the outer `svg` and the face of a text -/

/-- The outer `svg` of `workshop/MotionProbe.lean`, as the probe writes it. -/
def probeSvg (width height : Nat) (children : List SvgNode) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat width)), .attr .height (.user (.ofNat height)),
      .attr .viewBox (ViewBox.ofSize 800 520)]
    children

/-- `Svg.view` writes the probe's outer `svg`, at every size. -/
theorem view_eq_probeSvg (width height : Nat) (children : List SvgNode) :
    Svg.view width height (.ofSize 800 520) [] children = probeSvg width height children := rfl

/-- The face of a text in the probes, as they write it. -/
def probeFace : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb (.ofNat 0xf3f4f6)), .xmlSpacePreserve]

/-- The ink of the probes. A colour is a numeral of six hexadecimal digits. -/
def ink : Rgb := 0xf3f4f6

/-- The ground of the probes. -/
def ground : Rgb := 0x14110d

/-- White: what a mask shows through. -/
def white : Rgb := 0xffffff

/-- The same face with a literal for the size and a colour by its name. -/
def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize 13.288, .fill ink,
    .xmlSpacePreserve]

-- The two faces write the same four attributes.
#guard face.map SvgAttr.toPair == probeFace.map SvgAttr.toPair

/-- The size of a box: a width that a program holds as a number, and a height with a
fraction. -/
def sized (width : Nat) : List (SvgAttr .rect) :=
  [.attr .width (width : AutoExtent), .attr .height 12.5]

-- What the two sizes write, and the radius `2.5` beside the one rounded from `5 / 2`.
#guard (sized 320).map SvgAttr.toPair == [("width", "320"), ("height", "12.5")]
#guard (Svg.circle 10 10 2.5).renderXmlUnchecked ==
  (Svg.circle 10 10 (.ofRat (5 / 2))).renderXmlUnchecked

-- The text of each value, as an attribute holds it.
#guard toString (12.5 : AutoExtent) == "12.5" && toString (ViewBox.ofSize 240 160) == "0 0 240 160"
#guard toString (0x14110d : Rgb) == "#14110d" && toString (Paint.url "g-1") == "url(#g-1)"

-- Why `Rgb.toNat_ofNat_of_lt` asks for six digits: a numeral of seven is another colour's.
#guard (0x1f3f4f6 : Rgb) == (0xf3f4f6 : Rgb)

/-! ## Two probes: the reveal of an edge -/


/-- The reveal of an edge as the probes write it: `Svg.revealed`, under an identifier that the
probe makes from the edge's key. `workshop/TreeProbe.lean` takes three kinds of character out of
the key to make it. -/
def probeReveal (id : String) (centre : List Cubic) (cover : Rat) (outline : List Cubic) :
    List SvgNode :=
  Svg.revealed id (Svg.revealLine centre cover) [Svg.loops [outline] [.fill (.rgb ink)]]

/-- The same reveal as a program: the mask is a definition, and the group refers to it. -/
def reveal (centre : List Cubic) (cover : Rat) (outline : List Cubic) : Svg.Defs SvgNode := do
  let shown ← Svg.Defs.mask [Svg.revealLine centre cover]
  pure (Svg.g [.maskBy shown] [Svg.loops [outline] [.fill ink]])

/-- **What the program writes is what the probe wrote**: the probe's mask, under `defs` and
under the first identifier of the stem, and then the probe's group. No key is made into an
identifier. -/
theorem reveal_eq (stem : String) (centre : List Cubic) (cover : Rat) (outline : List Cubic) :
    Svg.withDefs stem (do let mark ← reveal centre cover outline; pure [mark]) =
      Svg.defs ((probeReveal (Svg.Defs.name stem 0) centre cover outline).take 1) ::
        (probeReveal (Svg.Defs.name stem 0) centre cover outline).drop 1 := rfl

/-! ## A new picture: the back edges of a graph -/

/-- A back edge from one point to another: an arc that fades in along a gradient from its start,
shown through a mask of its own centre line, with an arrow head at its end. The gradient and the
mask are the edge's own; the arrow head is the graph's. -/
def backEdge (head : Svg.Ref .marker) (e : Vec × Vec) : Svg.Defs SvgNode := do
  let arc := (Curve.bumpY (1 / 2)).cubics [e.1, e.2]
  let fade ← Svg.Defs.linearGradient e.1 e.2 [⟨0, ink, some 0.15⟩, ⟨1, ink, none⟩]
  let shown ← Svg.Defs.mask
    [Svg.cubics arc [.fill .none, .stroke white, .strokeWidth 6, .strokeLinecap .round]]
  pure (Svg.g [.maskBy shown]
    [Svg.cubics arc
      [.fill .none, .stroke fade, .strokeWidth 1.5, .strokeLinecap .round, .markerEnd head]])

/-- The marks of a graph's back edges under a stem: one arrow head, then each edge. -/
def marks (stem : String) (edges : List (Vec × Vec)) : List SvgNode :=
  Svg.withDefs stem do
    let head ← Svg.Defs.arrowHead 6 8 ink
    Svg.Defs.each edges (backEdge head)

/-- The picture: 240 by 160, a ground, and the back edges. -/
def graph (edges : List (Vec × Vec)) : SvgNode :=
  Svg.view 240 160 (.ofSize 240 160) []
    (Svg.box (.ofSize ⟨0, 0⟩ 240 160) [.fill ground] :: marks "g" edges)

/-- A back edge passes among the marks, and so do its two definitions, for every arrow head and
every two points. -/
theorem backEdge_holds (x : Exclusions) (head : Svg.Ref .marker) (e : Vec × Vec) :
    Svg.Defs.Holds (fun node => node.okAt (Pos.inSvg x) = true)
      (fun d => d.okAt (Pos.inSvg x) = true) (backEdge head e) :=
  Svg.Defs.Holds.bind (Svg.Defs.Holds.add (Svg.Def.linearGradient_ok x _ _ _ _ _) fun _ => trivial)
    fun _ _ =>
      Svg.Defs.Holds.bind
        (Svg.Defs.Holds.add (Svg.Def.mask_ok x _ _ _ (by conv => lhs; whnf)) fun _ => trivial)
        fun _ _ => Svg.Defs.Holds.pure (by conv => lhs; whnf)

/-- The marks of every list of back edges pass among the marks, under every stem. -/
theorem marks_ok (x : Exclusions) (stem : String) (edges : List (Vec × Vec)) :
    SvgNode.okAllAt (Pos.inSvg x) (marks stem edges) = true :=
  Svg.okAllAt_withDefs_of_holds x stem
    (Svg.Defs.Holds.bind
      (Svg.Defs.Holds.add (Svg.Def.arrowHead_ok x _ _ _ _) fun _ => trivial)
      fun head _ => fun s n =>
        ⟨(SvgNode.okAllAt_iff _ _).mpr
            ((Svg.Defs.Holds.each edges fun e _ => backEdge_holds x head e) s n).1,
          ((Svg.Defs.Holds.each edges fun e _ => backEdge_holds x head e) s n).2⟩)

/-- **The structure of the picture, for every list of edges**, at every HTML position that
admits `svg`. -/
theorem graph_okIn (ctx : Ctx) (hctx : ctx.admits .svg = true) (edges : List (Vec × Vec)) :
    (graph edges).okIn ctx = true := by
  rw [graph, Svg.view, Svg.svg, SvgNode.okIn_svg, hctx, SvgNode.okAllAt_cons, marks_ok]
  conv => lhs; whnf

/-- The checker accepts the raw tree of the picture in flow content (law V8). -/
theorem graph_valid (edges : List (Vec × Vec)) : validIn Ctx.flow (graph edges).toRaw = true :=
  SvgNode.validIn_of_okIn (graph_okIn Ctx.flow (by decide +kernel) edges)

-- The picture of one edge, as the text of a file. Three definitions under one `defs`, each
-- under the stem and its place, and each referred to by the mark that uses it.
#guard (graph [(⟨20, 20⟩, ⟨200, 140⟩)]).renderXmlUnchecked ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"240\" height=\"160\" " ++
  "viewBox=\"0 0 240 160\"><rect x=\"0\" y=\"0\" width=\"240\" height=\"160\" " ++
  "fill=\"#14110d\"/><defs><marker id=\"g-0\" markerWidth=\"6\" markerHeight=\"8\" refX=\"6\" " ++
  "refY=\"4\" orient=\"auto-start-reverse\" markerUnits=\"userSpaceOnUse\">" ++
  "<path d=\"M0,0L6,4L0,8Z\" fill=\"#f3f4f6\"/></marker>" ++
  "<linearGradient id=\"g-1\" x1=\"20\" y1=\"20\" x2=\"200\" y2=\"140\" " ++
  "gradientUnits=\"userSpaceOnUse\"><stop offset=\"0\" stop-color=\"#f3f4f6\" " ++
  "stop-opacity=\"0.15\"/><stop offset=\"1\" stop-color=\"#f3f4f6\"/></linearGradient>" ++
  "<mask id=\"g-2\" maskUnits=\"userSpaceOnUse\"><path d=\"M20,20C20,80 200,80 200,140\" " ++
  "fill=\"none\" stroke=\"#ffffff\" stroke-width=\"6\" stroke-linecap=\"round\"/></mask></defs>" ++
  "<g mask=\"url(#g-2)\"><path d=\"M20,20C20,80 200,80 200,140\" fill=\"none\" " ++
  "stroke=\"url(#g-1)\" stroke-width=\"1.5\" stroke-linecap=\"round\" " ++
  "marker-end=\"url(#g-0)\"/></g></svg>"

/-- Two edges, for the guards. -/
def two : List (Vec × Vec) := [(⟨20, 20⟩, ⟨200, 140⟩), (⟨40, 20⟩, ⟨100, 140⟩)]

-- The identifiers of a picture of two edges: five declared, six references, and the arrow head
-- referred to twice. Every reference is declared and none is declared twice.
#guard (graph two).ids == ["g-0", "g-1", "g-2", "g-3", "g-4"]
#guard (graph two).refs == ["g-2", "g-1", "g-0", "g-4", "g-3", "g-0"]
#guard (graph two).linked

-- Two pictures of one page under two stems share no identifier, and the forest of both is in
-- order.
#guard SvgNode.linkedAll (marks "a" two ++ marks "b" two)

-- Why a page gives each picture its own stem: under one stem the second picture declares the
-- identifiers of the first again, and the test refuses the page.
#guard !SvgNode.linkedAll (marks "a" two ++ marks "a" two)

-- What the test refuses in a tree with identifiers typed by hand: a reference to no
-- definition, and one identifier on two elements. The structure test passes both.
#guard !(Svg.g [.attr .mask (urlRef "nowhere")] []).linked
#guard !(Svg.g [] [Svg.clipPath "c" [], Svg.clipPath "c" []]).linked
#guard (Svg.g [] (Svg.clipped "c" [Svg.rect 0 0 4 4] [])).linked

-- The identifier of the fifth definition of a picture is the one its mark was handed, by law
-- and here by evaluation: the mask of the second edge.
#guard ((graph two).ids.getD 4 "") == Svg.Defs.name "g" 4

/-! ## A node that links to a page -/

/-- A node of a graph that links to its page: a box and its label inside an `a`. -/
def nodeLink (href : String) (b : Box) (label : String) : SvgNode :=
  Svg.link href
    [Svg.box b [.fill ground], Svg.label b.center label [.fill ink, .textAnchor .middle]]

/-- The link passes among the marks, and so in a group at any depth, for every address, box and
label. -/
theorem nodeLink_ok (x : Exclusions) (href : String) (b : Box) (label : String) :
    (nodeLink href b label).okAt (Pos.inSvg x) = true :=
  Svg.link_ok x _ _ (by conv => lhs; whnf)

-- A link in a group of a picture passes the structure test. A link that stands in a link does
-- not: the schema's `a` takes what may stand around it, but no other `a`.
#guard (Svg.svg [] [Svg.g [] [nodeLink "fiber-0.html" (.ofSize ⟨0, 0⟩ 40 20) "fiber 0"]]).okIn
  Ctx.flow
#guard !(Svg.svg [] [Svg.link "a.html" [Svg.link "b.html" []]]).okIn Ctx.flow

-- The address of a page refers to no identifier of the picture; a fragment refers to the one it
-- names.
#guard (nodeLink "fiber-0.html" (.ofSize ⟨0, 0⟩ 40 20) "fiber 0").refs == []
#guard (Svg.link "#g-0" []).refs == ["g-0"]

/-! ## The picture as one image that is read by name -/

/-- The graph as one image with a name and a description: `role="img"`, a `title` and a `desc`
under identifiers made from the stem, and the two attributes that name them. -/
def namedGraph (edges : List (Vec × Vec)) : SvgNode :=
  Svg.Frame.titled { width := 240, height := 160 } "g" "The back edges of a graph" []
    (Svg.box (.ofSize ⟨0, 0⟩ 240 160) [.fill ground] :: marks "g" edges)
    (some "Each edge fades in from its start and ends in an arrow head.")

/-- The named picture passes the structure test in flow content, for every list of edges. -/
theorem namedGraph_okIn (edges : List (Vec × Vec)) : (namedGraph edges).okIn Ctx.flow = true :=
  Svg.okIn_titled Ctx.flow (by decide +kernel) (by decide +kernel) _ _ _ (by conv => lhs; whnf)
    (by
      rw [SvgNode.okAllAt_cons, marks_ok]
      conv => lhs; whnf)

-- The identifiers of the named picture: the title's and the description's, then the places.
-- The `svg` refers to the first two, and the test of identifiers passes the whole.
#guard (namedGraph two).ids == ["g-title", "g-desc", "g-0", "g-1", "g-2", "g-3", "g-4"]
#guard (namedGraph []).refs == ["g-title", "g-desc"]
#guard (namedGraph two).linked
#guard Svg.titleId "g" == "g-title"

/-! ## The port's cuts as definitions under a stem -/

/-- The clip of a cut: its box in device pixels. It is the port's `cutNodes` without its
identifier. -/
def clipOf (ratio : Nat) (c : SvgKit.Cut) : List SvgNode :=
  [Svg.rect (ratio * c.x : Int) (ratio * c.y : Int) (.clamp (ratio * c.w)) (.clamp (ratio * c.h))]

/-- The port's marks, with each cut a clip path among the definitions of the picture's stem.
The calls are the port's own, read by its own `flat`. -/
def cutMarks (stem : String) (look : SvgKit.Look) (ratio : Nat) (calls : List SvgKit.Keyed) :
    List SvgNode :=
  Svg.withDefs stem (Svg.Defs.cuts (clipOf ratio) (calls.zipIdx.map (SvgKit.flat look ratio)))

/-- The port's picture under a stem. -/
def stemmed (stem : String) (look : SvgKit.Look) (W H ratio : Nat) (calls : List SvgKit.Keyed) :
    SvgNode :=
  Svg.Frame.svg { width := W, height := H, ratio := ratio }
    [.className "e4-view", .data "look" look.name] (cutMarks stem look ratio calls)

/-- The marks of every list of device calls pass among the marks, under every stem. The marks
are proved by the port's own `flat_ok`. -/
theorem cutMarks_ok (x : Exclusions) (stem : String) (look : SvgKit.Look) (ratio : Nat)
    (calls : List SvgKit.Keyed) :
    SvgNode.okAllAt (Pos.inSvg x) (cutMarks stem look ratio calls) = true :=
  Svg.okAllAt_withDefs_of_holds x stem
    (Svg.Defs.cuts_holds x _ _
      (fun node hn => by
        obtain ⟨d, _, hd⟩ := List.mem_map.mp hn
        have h := SvgKit.flat_ok x look ratio d
        rw [hd] at h
        exact h)
      fun c => by conv => lhs; whnf)

/-- **The three closing laws of the port's picture, in one**: its structure at every HTML
position that admits `svg`, its validity in flow content, and its values. -/
theorem stemmed_laws (stem : String) (look : SvgKit.Look) (W H ratio : Nat)
    (calls : List SvgKit.Keyed) :
    (∀ ctx : Ctx, ctx.admits .svg = true → (stemmed stem look W H ratio calls).okIn ctx = true) ∧
      validIn Ctx.flow (stemmed stem look W H ratio calls).toRaw = true ∧
      valuesOk (stemmed stem look W H ratio calls).toRaw = true :=
  Svg.Frame.picture_laws _ (by conv => lhs; whnf) fun x => cutMarks_ok x stem look ratio calls

-- The port's sample, twice on one page. As the port writes it, each picture alone is in order,
-- and the two together are not: both declare the clip path `c3`.
#guard (SvgKit.picture SvgKit.plain 40 20 2 SvgKit.sample).linked
#guard !SvgNode.linkedAll
  [SvgKit.picture SvgKit.plain 40 20 2 SvgKit.sample,
    SvgKit.picture SvgKit.plain 40 20 2 SvgKit.sample]

-- Under two stems the same two pictures are in order together: the clip path of the one is
-- `a-0` and of the other `b-0`, each referred to by its own group.
#guard SvgNode.linkedAll
  [stemmed "a" SvgKit.plain 40 20 2 SvgKit.sample, stemmed "b" SvgKit.plain 40 20 2 SvgKit.sample]
#guard (stemmed "a" SvgKit.plain 40 20 2 SvgKit.sample).ids == ["a-0"]
#guard (stemmed "a" SvgKit.plain 40 20 2 SvgKit.sample).refs == ["a-0"]

end WhatwgTest.Html.SvgUseKit
