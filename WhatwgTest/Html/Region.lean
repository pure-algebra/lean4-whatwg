import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Check
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Node.Region

/-!
# WhatwgTest.Html.Region

The scrollable region and the figure of lean4-effect4's documents on the package's builders
(slice S17 of `docs/SVG-PACKAGE-PLAN.md`, its second round; entry W13 of
`docs/research/2026-10-12-whatwg-requests.md`): `Whatwg/Html/Node/Region.lean`. The consumer is
read at `c1faac505`: the cases `table` and `graph` of `algebra`,
`tools/Tools/Document/Html.lean`. The namespace `Theirs` restates what those two cases write.
This module imports nothing of that package.

- **The table's region is the consumer's, node for node** (`tableRegion_eq`, for every table
  and every list of headers).
- **The figure differs, and each difference is a name written once.** The consumer names the
  region with the caption's words again (`aria-label="Figure: …"`); here the region names the
  caption (`aria-labelledby`). The consumer's words stand after the figure and nothing points
  at them; here they stand in the figure, and the figure names them (`aria-describedby`). The
  figure keeps its `id` and its class.

What this battery does not claim: that a screen reader announces either form as intended. No
sealed text of this repository states the rules of `role`, `tabindex` and the `aria-`
attributes; the schema admits them, and that is all a gate reads.
-/

namespace WhatwgTest.Html.Region

open Whatwg.Html
open Whatwg.Html.Content

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-! ## The consumer's two cases, as they stand -/

namespace Theirs

/-- The region of a wide table (`algebra.table`). -/
def tableRegion (headers : List String) (table : RawNode) : RawNode :=
  el "div" [table]
    [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
     ("aria-label", "Table: " ++ ", ".intercalate headers)]

/-- A figure and its words (`algebra.graph`): the picture in a region, the caption, and after
the figure a `details` with a line for each node. -/
def graphFigure (key caption : String) (picture : RawNode) (lines : List (List RawNode)) :
    List RawNode :=
  [el "figure" [
      el "div" [picture] [("class", "scroll"), ("role", "region"), ("tabindex", "0"), ("aria-label", "Figure: " ++ caption)],
      el "figcaption" [.text caption]] [("id", key), ("class", "graph")],
   el "details" [el "summary" [.text "The figure in words"], el "ul" (lines.map fun line => el "li" line)]
     [("class", "words")]]

end Theirs

/-! ## On the package's builders -/

/-- The region of a wide table. -/
def tableRegion (headers : List String) (table : RawNode) : RawNode :=
  regionRaw (.label ("Table: " ++ ", ".intercalate headers)) [table] (some "scroll")

/-- The same node, for every table and every list of headers. -/
theorem tableRegion_eq (headers : List String) (table : RawNode) :
    tableRegion headers table = Theirs.tableRegion headers table := rfl

/-- A figure and its words: one node. -/
def graphFigure (key caption : String) (picture : RawNode) (lines : List (List RawNode)) : RawNode :=
  Region.figureRaw key [picture] [.text caption]
    (some ("The figure in words", [el "ul" (lines.map fun line => el "li" line)]))
    (some "graph") (some "scroll")

/-! ## A sample -/

/-- A small picture written with the kit, as the consumer's layout would hand one over. -/
def picture : SvgNode :=
  Svg.Frame.svg { width := 120, height := 60 } [.className "e4-view"]
    [Svg.rect 10 10 30 20 [.fill .none], Svg.text 12 24 "claim"]

def lines : List (List RawNode) :=
  [[el "a" [.text "claim"] [("href", "#claim")], .text " proved"], [.text "goal → claim"]]

def table : RawNode :=
  el "table" [el "thead" [el "tr" [el "th" [.text "Claim"] [("scope", "col")]]],
    el "tbody" [el "tr" [el "td" [.text "t"]]]]

/-- Where a block of a page stands. -/
abbrev mainCtx : Ctx := Ctx.document.below [.html, .body, .main]

-- Both forms of the figure pass the checker among the blocks of a page, with the table.
#guard (Child.checkAll? (ctx := mainCtx)
  (Theirs.tableRegion ["Claim"] table :: Theirs.graphFigure "plan" "The plan" picture.toRaw lines)).isSome
#guard (Child.checkAll? (ctx := mainCtx)
  [tableRegion ["Claim"] table, graphFigure "plan" "The plan" picture.toRaw lines]).isSome

-- The text of the package's figure: the three identifiers come from the one stem.
#guard Print.render (graphFigure "plan" "The plan" (.element "svg" [] []) [[.text "x"]]) ==
  "<figure id=\"plan\" class=\"graph\" aria-describedby=\"plan-words\"><div class=\"scroll\" role=\"region\" tabindex=\"0\" aria-labelledby=\"plan-caption\"><svg></svg></div><details id=\"plan-words\"><summary>The figure in words</summary><ul><li>x</li></ul></details><figcaption id=\"plan-caption\">The plan</figcaption></figure>"

/-! ## The typed forms -/

/-- A typed figure: the picture is a typed child of the region, and nothing else is owed. -/
def typed : Element .figure Ctx.flow :=
  Region.figure "plan" [Child.ofSvg picture] [Child.text "The plan"] (some "graph") (some "scroll")

/-- The same for every identifier, every caption and every position: no premise. -/
def anywhere {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (caption : List (Child ((ctx.child .figure).child .figcaption))) : Element .figure ctx :=
  Region.figure id content caption

-- Reader of `Region.figure_toRaw`: the typed figure is the raw one with no words.
example : typed.toRaw =
    Region.figureRaw "plan" [picture.toRaw] [.text "The plan"] none (some "graph") (some "scroll") :=
  Region.figure_toRaw "plan" _ _ _ _

#guard validIn Ctx.flow typed.toRaw

/-- A typed region placed where a `div` may stand. -/
def box (words : String) (children : List (Child (Ctx.flow.child .div))) : Child Ctx.flow :=
  Region.child (.label words) children (some "scroll")

#guard (box "Table: Claim" []).render ==
  "<div class=\"scroll\" role=\"region\" tabindex=\"0\" aria-label=\"Table: Claim\"></div>"

-- Reader of `Region.attrsOk`: the attributes are good for every name, with nothing evaluated.
example (words : String) (classes : Option String) :
    attrsOk .div (rawAttrs (Region.attrs (.label words) classes)) = true :=
  Region.attrsOk _ _

-- Reader of `Ctx.admits_div_child_figure`: a figure takes a region under every ancestor.
example (ctx : Ctx) : (ctx.child .figure).admits .div = true := Ctx.admits_div_child_figure ctx

/-! ## Controls -/

-- A region is a `div`: no phrasing content.
#guard (Child.check? (ctx := Ctx.phrasing) (regionRaw (.label "x") [])).isNone

-- The words are a `details`, which is interactive content: the figure with its words does not
-- stand inside a link, and the figure without them does.
#guard (Child.check? (ctx := Ctx.flow.child .a) (graphFigure "plan" "The plan" picture.toRaw lines)).isNone
#guard (Child.check? (ctx := Ctx.flow.child .a)
  (Region.figureRaw "plan" [picture.toRaw] [.text "The plan"])).isSome

-- What is not claimed: the content model here does not read `tabindex`, so a region inside a
-- link passes. The HTML Standard calls such an element interactive content.
#guard (Child.check? (ctx := Ctx.flow.child .a) (regionRaw (.label "x") [])).isSome

end WhatwgTest.Html.Region
