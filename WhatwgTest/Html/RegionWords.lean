import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Check
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Content.Document.Laws
import Whatwg.Html.Node.Region.Words

/-!
# WhatwgTest.Html.RegionWords

The figure of lean4-effect4's documents with its words after it, on
`Whatwg/Html/Node/Region/Words.lean` (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; what was left of
entry W13 of `docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at
`6ad8f7b8d`: the case `graph` of `algebra`, `tools/Tools/Document/Html.lean`, lines 99 to 114.
The namespace `Theirs` restates what that case writes; this module imports nothing of that
package.

The consumer keeps the caption beside the picture and puts the words after the figure. Slice
S21's `Region.figureRaw` put the words inside the figure, between the region and the caption,
which is the difference entry W13 names. `Region.withWords` and `Region.withWordsRaw` are the
consumer's placement. What still differs from its nodes is two names, each written once: the
region names the caption (`aria-labelledby`) where the consumer repeats its words
(`aria-label`), and the figure names the words (`aria-describedby`), which nothing pointed at.

What this battery does not claim: that a screen reader announces either form as intended (see
the header of `Whatwg/Html/Node/Region.lean`).
-/

namespace WhatwgTest.Html.RegionWords

open Whatwg.Html
open Whatwg.Html.Content

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

namespace Theirs

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

/-- The same two nodes, as the consumer's fold would write them: raw. -/
def graphFigure (key caption : String) (picture : RawNode) (lines : List (List RawNode)) :
    List RawNode :=
  Region.withWordsRaw key [picture] [.text caption] "The figure in words"
    [el "ul" (lines.map fun line => el "li" line)] (some "graph") (some "scroll") (some "words")

/-- Where a block of a page stands. -/
abbrev mainCtx : Ctx := Ctx.document.below [.html, .body, .main]

/-- A line of the words: where its content stands. -/
abbrev InLine : Ctx := ((((mainCtx.child .details).rebase .flow).child .ul).child .li)

/-- The same figure, typed: the picture is a typed child of the region, and each line of the
words a typed item. Nothing is checked when the program runs. -/
def typedFigure (key caption : String) (picture : Child ((mainCtx.child .figure).child .div))
    (lines : List (List (Child InLine))) : List (Child mainCtx) :=
  Region.withWords key [picture] [Child.text caption] "The figure in words"
    [E.el (E.ul (lines.map fun line => E.el (E.li line)))] (some "graph") (some "scroll") (some "words")

/-! ## A sample -/

def picture : SvgNode :=
  Svg.Frame.svg { width := 120, height := 60 } [.className "e4-view"]
    [Svg.rect 10 10 30 20 [.fill .none], Svg.text 12 24 "claim"]

def lines : List (List RawNode) :=
  [[el "a" [.text "claim"] [("href", "#claim")], .text " proved"], [.text "goal → claim"]]

def typedLines : List (List (Child InLine)) :=
  [[E.el (E.a [E.txt "claim"] [A.a_href "#claim"]), E.txt " proved"], [E.txt "goal → claim"]]

-- Both forms pass the checker among the blocks of a page.
#guard (Child.checkAll? (ctx := mainCtx) (Theirs.graphFigure "plan" "The plan" picture.toRaw lines)).isSome
#guard (Child.checkAll? (ctx := mainCtx) (graphFigure "plan" "The plan" picture.toRaw lines)).isSome

-- The text of the package's pair: the caption stands beside the picture, the words after the
-- figure, and the three identifiers come from the one stem.
#guard String.join ((graphFigure "plan" "The plan" (el "svg" []) [[.text "x"]]).map Print.render) ==
  "<figure id=\"plan\" class=\"graph\" aria-describedby=\"plan-words\"><div class=\"scroll\" role=\"region\" tabindex=\"0\" aria-labelledby=\"plan-caption\"><svg></svg></div><figcaption id=\"plan-caption\">The plan</figcaption></figure>" ++
    "<details id=\"plan-words\" class=\"words\"><summary>The figure in words</summary><ul><li>x</li></ul></details>"

-- Reader of `Region.withWords_raw`: the typed pair writes the raw one, here with the sample.
example : (typedFigure "plan" "The plan" (Child.ofSvg picture) typedLines).map Child.raw =
    Region.withWordsRaw "plan" [picture.toRaw] [.text "The plan"] "The figure in words"
      ([E.el (E.ul (typedLines.map fun line => E.el (E.li line)))].map Child.raw)
      (some "graph") (some "scroll") (some "words") :=
  Region.withWords_raw _ _ _ _ _ _ _ _ _ _

#guard (typedFigure "plan" "The plan" (Child.ofSvg picture) typedLines).map Child.raw ==
  graphFigure "plan" "The plan" picture.toRaw lines

/-- A page around some blocks, as raw nodes. -/
def pageOf (blocks : List RawNode) : RawNode :=
  el "html" [el "head" [el "title" [.text "T"]], el "body" [el "main" (el "h1" [.text "T", el "a" [.text "claim"] [("id", "claim")]] :: blocks)]]

-- Across a page, the names resolve: the region's to the caption, the figure's to the words.
#guard Document.errors (pageOf (graphFigure "plan" "The plan" picture.toRaw lines)) == []

-- Two figures under two stems share no identifier.
#guard Document.errors (pageOf (graphFigure "plan" "The plan" picture.toRaw lines ++
  graphFigure "proof" "The proof" picture.toRaw [])) == []

/-! ## Controls -/

-- The figure names its words, so the two are given together: the figure alone has a
-- reference that names nothing.
#guard (Document.errors (pageOf [Region.describedRaw "plan" [picture.toRaw] [.text "The plan"]])).map
    (·.describe) ==
  ["`aria-describedby` of `figure` names `plan-words`, and no element has that identifier: at the child path [1, 0, 1]"]

-- Two figures under one stem are refused across the page: each identifier is defined twice.
#guard (Document.errors (pageOf (graphFigure "plan" "A" picture.toRaw [] ++
  graphFigure "plan" "B" picture.toRaw []))).length == 3

-- The typed words stand wherever a `details` may: inside a link they are refused, since a
-- `details` is interactive content. The premise that is owed says so.
/--
error: could not synthesize default value for parameter 'hdetails' using tactics
---
error: <details> is not admitted here: the context is flow, excluding interactive content, a
-/
#guard_msgs in
example : List (Child (Ctx.flow.child .a)) :=
  Region.withWords "plan" [] [Child.text "The plan"] "The figure in words" []

end WhatwgTest.Html.RegionWords
