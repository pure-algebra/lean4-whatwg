import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgMarkup

Finite evaluations and controls of the meta level over SVG (slice S3e of
`docs/SVG-PACKAGE-PLAN.md`): the markup term `html!` with an `svg` subtree
(`Whatwg/Html/Syntax/Elaborator.lean`), and the tactic `admits` at a whole tree
(`Whatwg/Html/Node/Admit.lean`).

Each positive line builds a term and compares the raw tree it holds. Each control is a markup
term or a goal that is refused, with the message pinned: the message is the located refusal of
`Whatwg.Html.Content.explain`, and its text is the contract here.

What this battery does not claim: that the elaborator decides validity. It reports, and the
kernel checks each obligation again when the declaration is added.
-/

namespace WhatwgTest.Html.SvgMarkup

open Whatwg.Html
open Whatwg.Html.Content
open WhatwgTest.Html.Svg (el)

/-! ## `html!` with an SVG subtree -/

/-- A paragraph that holds a figure, as markup. Names keep their case, a dash joins a name,
and a name that is no identifier is a string literal. -/
def figure : Element .p Ctx.flow :=
  html! <p class="fig"><svg viewBox="0 0 10 10" role="img"><title>"A chart"</title><g clip-path="url(#c)"><rect x="1" y="2" width="3" height="4" /><text "xml:space"="preserve">"a  b"</text></g></svg></p>

#guard figure.toRaw ==
  el "p" [("class", "fig")]
    [el "svg" [("viewBox", "0 0 10 10"), ("role", "img")]
      [el "title" [] [.text "A chart"],
       el "g" [("clip-path", "url(#c)")]
         [el "rect" [("x", "1"), ("y", "2"), ("width", "3"), ("height", "4")],
          el "text" [("xml:space", "preserve")] [.text "a  b"]]]]

#guard validIn Ctx.flow figure.toRaw
#guard figure.render ==
  "<p class=\"fig\"><svg viewBox=\"0 0 10 10\" role=\"img\"><title>A chart</title><g clip-path=\"url(#c)\"><rect x=\"1\" y=\"2\" width=\"3\" height=\"4\"></rect><text xml:space=\"preserve\">a  b</text></g></svg></p>"

/-- An `svg` at the root is a child of its context. -/
def chart : Child Ctx.phrasing := html! <svg><rect /></svg>

#guard chart.raw == el "svg" [] [el "rect"]

/-- A spliced attribute value on an SVG element: the checker reads no SVG value. -/
def bar (x : Nat) : Child Ctx.flow := html! <svg><rect x={toString x} /></svg>

#guard (bar 7).raw == el "svg" [] [el "rect" [("x", "7")]]

/-- Attribute names that are Lean keywords, as string literals. -/
def moving : Child Ctx.flow :=
  html! <svg><rect><animate attributeName="x" "from"="0" to="9" "by"="1" "end"="2s" /></rect></svg>

#guard moving.raw ==
  el "svg" [] [el "rect" [] [el "animate"
    [("attributeName", "x"), ("from", "0"), ("to", "9"), ("by", "1"), ("end", "2s")]]]

/-- HTML again below an integration point. -/
def labelled : Child Ctx.flow :=
  html! <svg><foreignObject><div><p>"x"</p></div></foreignObject><desc>"What it shows"</desc></svg>

#guard validIn Ctx.flow labelled.raw

/-! ## Controls: the refusal, at the refused node -/

/-- error: <div>: the name is no element of this namespace -/
#guard_msgs (error) in
example : Element .p Ctx.flow := html! <p><svg><div></div></svg></p>

/-- error: <rect>: the element does not take the attribute `d` -/
#guard_msgs (error) in
example : Element .p Ctx.flow := html! <p><svg><rect d="M 0 0" /></svg></p>

/-- error: <rect>: the attribute `viewbox` is no attribute of the schema -/
#guard_msgs (error) in
example : Element .p Ctx.flow := html! <p><svg><rect viewbox="0 0 1 1" /></svg></p>

/-- error: <a>: the position does not admit the element -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><a><a></a></a></svg>

/-- error: <feDiffuseLighting>: the children do not hold a count of the element's content model -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><filter><feDiffuseLighting /></filter></svg>

/-- error: text: character data may not stand here -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg>"x"</svg>

/--
error: <svg>: the position does not admit the element (the context is only_li)
-/
#guard_msgs (error) in
example : Element .ul Ctx.flow := html! <ul><svg></svg></ul>

/--
error: <math>: the element is a foreign element whose vocabulary is not modelled (the context is phrasing)
-/
#guard_msgs (error) in
example : Element .p Ctx.flow := html! <p><math></math></p>

/-- error: html!: a spliced child is not supported inside an SVG subtree -/
#guard_msgs (error) in
example (c : Child Ctx.flow) : Child Ctx.flow := html! <svg><foreignObject>{c}</foreignObject></svg>

/-! ## `admits` at a whole tree -/

-- The tactic closes the validity of a closed tree, with SVG or without.
example : validIn Ctx.flow (el "p" [] [el "svg" [] [el "rect"]]) = true := by admits
example : validAll Ctx.flow [el "p", el "svg" [] [el "g"]] = true := by admits

/-- error: <div> at path [0, 1]: the name is no element of this namespace -/
#guard_msgs (error) in
example : validIn Ctx.flow (el "p" [] [el "svg" [] [el "rect", el "div"]]) = true := by admits

/-- error: <rect> at path [0]: the attribute `nope` is no attribute of the schema -/
#guard_msgs (error) in
example : validIn Ctx.flow (el "svg" [] [el "rect" [("nope", "x")]]) = true := by admits

end WhatwgTest.Html.SvgMarkup