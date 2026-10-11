import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgPrint

Readers, controls and finite evaluations of the printer in the SVG namespace (slice S3d of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Html/Print/Render.lean`. Each line prints a small tree and
compares the text, or applies the round trip at a tree that holds SVG.

The serialization algorithm states its void rule and its raw-text rule of HTML elements. The
controls show each rule on both sides of the seam: in SVG it does not hold, and below an
integration point it holds again.

What this battery does not claim: that a browser parses the printed text back to the tree.
`decodeNode?` reads the printer's own output and is no HTML parser (ruling HP-8).
-/

namespace WhatwgTest.Html.SvgPrint

open Whatwg.Html
open Whatwg.Html.Print
open Whatwg.Html.Content (Ns validIn Ctx)
open WhatwgTest.Html.Svg (el picture)

/-! ## The two rules, on both sides of the seam -/

-- No SVG element is void: an element with no child has its end tag.
#guard render (el "svg" [] [el "rect"]) == "<svg><rect></rect></svg>"

-- Control: the void rule holds for an HTML element.
#guard render (el "p" [] [el "br"]) == "<p><br></p>"

-- The text of an SVG `style` is escaped. Control: the text of an HTML `style` is literal.
#guard render (el "svg" [] [el "style" [] [.text "a<b{}"]]) == "<svg><style>a&lt;b{}</style></svg>"
#guard render (el "style" [] [.text "a<b{}"]) == "<style>a<b{}</style>"

-- Below an integration point both rules hold again.
#guard render (el "svg" [] [el "foreignObject" [] [el "br", el "style" [] [.text "a<b"]]]) ==
  "<svg><foreignObject><br><style>a<b</style></foreignObject></svg>"

-- Control: the printer follows the namespace, not the checker. A `br` below `svg` is no HTML
-- element there, so it is not void, though no valid tree holds it.
#guard render (el "svg" [] [el "br"]) == "<svg><br></br></svg>"
#guard !validIn Ctx.flow (el "svg" [] [el "br"])

-- A name is written as the tree holds it: mixed case, and a colon.
#guard render (el "svg" [("viewBox", "0 0 1 1")] [el "text" [("xml:space", "preserve")] [.text "a  b"]]) ==
  "<svg viewBox=\"0 0 1 1\"><text xml:space=\"preserve\">a  b</text></svg>"

-- The state along a path: the raw-text bit is set by an HTML raw-text element alone.
#guard (PrintState.root.step "style").raw && !((PrintState.root.step "svg").step "style").raw
#guard ((PrintState.root.step "svg").step "foreignObject").ns == Ns.html

/-! ## The laws, at trees that hold SVG -/

/-- A small figure: an HTML paragraph that holds an SVG with a style, a title and a shape. -/
def figure : RawNode :=
  el "p" [("class", "fig")]
    [el "svg" [("viewBox", "0 0 10 10")]
      [el "title" [] [.text "A <chart>"], el "style" [] [.text ".a > .b { fill: red }"],
       el "g" [] [el "rect" [("x", "1")], el "foreignObject" [] [el "br"]]]]

-- The figure is in the sublanguage the decoder inverts.
example : wf figure = true := by decide

-- Reader of P1: the decoder returns the tree from its own rendering.
example : decodeNode? (weight figure) (renderChars figure) = some (figure, []) :=
  decodeNode?_render (by decide)

-- Reader of P2: the text below an SVG `style` holds no `<`.
example : '<' ∉ renderIn (PrintState.step ⟨.svg, false⟩ "style") (.text ".a > .b { a<b }") :=
  renderIn_text_no_delim_of_svg false "style" _ '<' (by decide)

-- Reader of P3: two well-formed trees that print alike are one tree.
example (other : RawNode) (hwf : wf other = true) (h : render figure = render other) :
    figure = other :=
  render_injective_of_wf (by decide) hwf h

-- Controls of `wf` in SVG: an SVG `style` may hold a `<` in its text, because it is escaped;
-- an HTML `style` may not, because it is written literally.
example : wf (el "svg" [] [el "style" [] [.text "a<b"]]) = true := by decide
example : wf (el "style" [] [.text "a<b"]) = false := by decide

-- Control: an SVG element named as an HTML void element may hold children in `wf`.
example : wf (el "svg" [] [el "br" [] [el "g"]]) = true := by decide
example : wf (el "br" [] [el "g"]) = false := by decide

/-! ## The consumer's picture -/

-- The picture is valid, well formed, and decodes back from its own rendering.
example : wf picture = true := by decide
example : decodeNode? (weight picture) (renderChars picture) = some (picture, []) :=
  decodeNode?_render (by decide)

-- A document that holds it opens with the document type and the picture's start tag.
#guard (renderDoc (el "p" [] [picture])).startsWith
  "<!DOCTYPE html><p><svg class=\"figure\" viewBox=\"0 0 320 200\""

end WhatwgTest.Html.SvgPrint