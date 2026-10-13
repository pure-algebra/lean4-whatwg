import Whatwg.Html.Node.Combinators
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Check
import Whatwg.Html.Node.SvgFigure
-- Whatwg.Html.Node.Check and Whatwg.Html.Node.SvgFigure)

/-!
# WhatwgTest.Html.SvgFigure

Finite evaluations, readers and controls of a picture in a `figure` (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`; entry W4 of `docs/research/2026-10-12-whatwg-requests.md`, the HTML
side): `Whatwg/Html/Node/SvgFigure.lean`.

Three ways a figure is made, as lean4-effect4's site would make the figure of a plan's graph:
a closed picture, whose premises are found by evaluation; a picture with free marks, whose
premise is a law of the kit; and a picture that is data, as a raw node among the nodes of a
fold, checked with them.

What this battery does not claim: that a browser or a screen reader presents the figure as
intended. No sealed text of this repository states the rules of `role` and `aria-labelledby`:
the schema admits both on `svg`, and that is all a gate reads.
-/

namespace WhatwgTest.Html.SvgFigure

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Svg.Value

/-- A small picture written with the kit. -/
def graph : SvgNode :=
  Svg.Frame.svg { width := 120, height := 60 } [.className "plan"]
    [Svg.rect 10 10 30 20 [.fill .none], Svg.text 12 24 "claim"]

/-! ## A closed picture -/

/-- The figure of a closed picture at flow content: both premises are found by evaluation. -/
def captioned : Element .figure Ctx.flow :=
  Svg.figure "plan-graph" graph [E.txt "The plan's graph"]

-- The text: the identifier stands in the `aria-labelledby` of the picture and in the `id` of
-- the caption, from one argument.
#guard captioned.render ==
  "<figure><svg xmlns=\"http://www.w3.org/2000/svg\" class=\"plan\" width=\"120\" height=\"60\" viewBox=\"0 0 120 60\" role=\"img\" aria-labelledby=\"plan-graph\"><rect x=\"10\" y=\"10\" width=\"30\" height=\"20\" fill=\"none\"></rect><text x=\"12\" y=\"24\">claim</text></svg><figcaption id=\"plan-graph\">The plan's graph</figcaption></figure>"

-- The figure passes the checker at flow content: the checker's own run over the written names.
#guard validIn Ctx.flow captioned.toRaw

-- The figure in a page, among the children of `main`: a child like any other.
def inPage : Element .main Ctx.flow :=
  html! <main><p>"Before."</p>{E.el (Svg.figure "plan-graph" graph [E.txt "The plan's graph"])}</main>

-- A caption is flow content, and the figure takes its own attributes and another role.
def rich : Element .figure Ctx.flow :=
  Svg.figure "g2" graph [E.el (E.p [E.txt "A graph, ", E.el (E.em [E.txt "drawn"]), E.txt "."])]
    [A.a_class "wide"] "group"

#guard (rich.render.splitOn "role=\"group\" aria-labelledby=\"g2\"").length == 2

/-! ## Where the identifier is written -/

mutual

/-- The values of the attribute `name` in a tree, in document order: what a check of a whole
page reads for `id` and for `aria-labelledby` (entry W2). -/
def valuesOf (name : String) : RawNode → List String
  | .element _ attrs children =>
    (attrs.filterMap fun attr => if attr.1 == name then some attr.2 else none) ++
      valuesOfAll name children
  | _ => []

def valuesOfAll (name : String) : List RawNode → List String
  | [] => []
  | node :: rest => valuesOf name node ++ valuesOfAll name rest

end

-- The figure declares one identifier, and its picture names that one.
#guard valuesOf "id" captioned.toRaw == ["plan-graph"]
#guard valuesOf "aria-labelledby" captioned.toRaw == ["plan-graph"]

-- Reader of `Svg.figure_toRaw` and `SvgNode.toRaw_namedBy`: the two places, for every
-- identifier and every picture, with nothing evaluated.
example (id : String) (attrs : List (SvgAttr .svg)) (marks : List SvgNode)
    (content : List (Child ((Ctx.flow.child .figure).child .figcaption)))
    (h : ((SvgNode.element .svg attrs marks).namedBy id).okIn (Ctx.flow.child .figure) = true) :
    (Svg.figure id (.element .svg attrs marks) content [] "img" h).toRaw =
      .element "figure" []
        [.element "svg" (attrs.map SvgAttr.toPair ++ [("role", "img"), ("aria-labelledby", id)])
          (SvgNode.toRawAll marks),
         .element "figcaption" [("id", id)] (content.map Child.raw)] := by
  refine (Svg.figure_toRaw id _ content [] "img" h rfl (by decide)).trans ?_
  rw [Svg.figureRaw, SvgNode.toRaw_namedBy]
  rfl

/-! ## A picture with free marks -/

/-- The figure of a picture that a program draws: for every size, every identifier and every
list of marks that pass below a picture in a figure. The premise is the kit's law with the two
attributes, and one evaluation of the attribute list. -/
def drawn (width height : Nat) (id : String) (marks : List SvgNode)
    (h : SvgNode.okAllAt (Pos.belowSvg (Ctx.flow.child .figure)) marks = true) :
    Element .figure Ctx.flow :=
  Svg.figure id (Svg.Frame.svg { width := width, height := height } [.className "plan"] marks)
    [E.txt "The plan's graph"] [] "img"
    (Svg.Frame.okIn_namedBy (Ctx.admits_svg_child_figure _) _ id "img" (by conv => lhs; whnf) h)

-- Reader of `Ctx.admits_svg_child_figure`: a figure takes a picture under every ancestor, so
-- the law above asks nothing of where the figure stands.
example (ctx : Ctx) : (ctx.child .figure).admits .svg = true := Ctx.admits_svg_child_figure ctx

/-! ## A picture that is data -/

/-- A figure as a fold would yield it: a raw node among its nodes. -/
def folded (id : String) (picture : SvgNode) (words : String) : RawNode :=
  Svg.figureRaw id picture [.text words]

-- The checked admission takes it with the nodes beside it.
#guard (Child.acceptAll (ctx := Ctx.flow.child .main)
    [.element "p" [] [.text "Before."], folded "plan-graph" graph "The plan's graph"]).toOption.isSome

-- The raw figure and the typed one are one tree.
#guard folded "plan-graph" graph "The plan's graph" == captioned.toRaw

def refused {α : Type} (result : Except String α) : Option String :=
  match result with
  | .ok _ => none
  | .error words => some words

-- Control: a picture that the content model refuses is refused inside the figure, with the
-- names down to the mark. `path` is no child of `rect`.
#guard refused (Child.accept (ctx := Ctx.flow)
    (folded "g" (Svg.svg [] [.element .rect [] [.element .path [] []]]) "x")) ==
  some "/figure/svg/rect/path: <path> is not admitted here, in the content of an SVG element"

-- Control: a picture that already holds a `role` cannot take the second one.
#guard refused (Child.accept (ctx := Ctx.flow)
    (folded "g" (Svg.svg [.attr .role "img"] []) "x")) ==
  some "/figure/svg: an attribute name repeats"
example (id : String) :
    ((Svg.svg [.attr .role "img"] []).namedBy id).okIn (Ctx.flow.child .figure) = false := by
  conv => lhs; whnf

-- Control: a figure is flow content, and no phrasing content.
#guard refused (Child.accept (ctx := Ctx.phrasing) (folded "g" graph "x")) ==
  some "/figure: <figure> is not admitted here: the context is phrasing"

-- Control: the premise that the picture is an `svg` element stands. A node that is none is not
-- named, and the kit's `g` is no root.
#guard !(Svg.g [] []).isSvg && !(SvgNode.text "x").isSvg && graph.isSvg

/-! ## An attribute whose value is data -/

-- Reader of `Content.attrsOk_single`: the caption's `id` passes for every identifier, by one
-- evaluation of a test that reads no value.
example (id : String) : attrsOk .figcaption [("id", id)] = true :=
  attrsOk_single (by decide +kernel) id

-- Control: the test refuses an attribute whose value has a rule. `scope` takes keywords.
#guard !attrFree .th "scope" && attrFree .figcaption "id" && attrFree .a "href"

end WhatwgTest.Html.SvgFigure
