import Whatwg.Html
import WhatwgTest.Html.Svg

/-!
# WhatwgTest.Html.SvgMarkup

Finite evaluations and controls of the meta level over SVG (slices S3e and S5 of
`docs/SVG-PACKAGE-PLAN.md`): the markup term `html!` with an `svg` subtree
(`Whatwg/Html/Syntax/Elaborator.lean`), and the tactic `admits` at a whole tree
(`Whatwg/Html/Node/Admit.lean`).

Since slice S5 the term of an `svg` subtree is the raw tree of a typed tree,
`SvgNode.toRaw e` (`Whatwg/Html/Node/Svg.lean`). Each positive line builds a term and compares
the raw tree it holds, which spells a typed value as its grammar prints it. Each control is a
markup term or a goal that is refused, with the message pinned: the message is the located
refusal of `Whatwg.Html.Content.explain`, and its text is the contract here.
`WhatwgTest/Html/SvgValues.lean` holds the values: the law of a typed tree, and the refusal of a
literal.

What this battery does not claim: that the elaborator decides validity. It reports, and the
kernel checks each obligation again when the declaration is added.
-/

namespace WhatwgTest.Html.SvgMarkup

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Svg.Value (PathData Length)
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

/-- A spliced attribute value on an SVG element is a term of the attribute's type. `x` on `rect`
is a length, and `fill` has no kind, so it is text. The checker reads neither value. -/
def bar (x : Nat) (colour : String) : Child Ctx.flow :=
  html! <svg><rect x={Length.user (.ofInt x)} fill={colour} /></svg>

#guard (bar 7 "red").raw == el "svg" [] [el "rect" [("x", "7"), ("fill", "red")]]

/-- A spliced value below an HTML root. The root's proof names the local variable, so it stays
in the term and is no lemma of its own. -/
def framed (d : PathData) : Element .p Ctx.flow := html! <p><svg><path d={d} /></svg></p>

#guard (framed .none).toRaw == el "p" [] [el "svg" [] [el "path" [("d", "none")]]]

/-- Attribute names that are Lean keywords, as string literals. -/
def moving : Child Ctx.flow :=
  html! <svg><rect><animate attributeName="x" "from"="0" to="9" "by"="1" "end"="2s" /></rect></svg>

#guard moving.raw ==
  el "svg" [] [el "rect" [] [el "animate"
    [("attributeName", "x"), ("from", "0"), ("to", "9"), ("by", "1"), ("end", "2s")]]]

/-- A custom data attribute and the two namespace declarations, each a constructor of its own
in the typed tree. -/
def declared : Child Ctx.flow :=
  html! <svg xmlns="http://www.w3.org/2000/svg" "xmlns:xlink"="http://www.w3.org/1999/xlink" data-look="plain"><rect data-key="a" /></svg>

#guard declared.raw ==
  el "svg" [("xmlns", "http://www.w3.org/2000/svg"),
    ("xmlns:xlink", "http://www.w3.org/1999/xlink"), ("data-look", "plain")]
    [el "rect" [("data-key", "a")]]

/-- HTML again below an integration point: the HTML subtree is a raw literal in the typed
tree. -/
def labelled : Child Ctx.flow :=
  html! <svg><foreignObject><div><p>"x"</p></div></foreignObject><desc>"What it shows"</desc></svg>

#guard validIn Ctx.flow labelled.raw
#guard labelled.raw ==
  el "svg" [] [el "foreignObject" [] [el "div" [] [el "p" [] [.text "x"]]],
    el "desc" [] [.text "What it shows"]]

/-- An `svg` directly below an integration point is a typed element again: a value is spliced
there, and a literal prints as its grammar writes it. An `svg` below an HTML element is a part
of that element's raw literal, and its literal keeps the spelling the author wrote. -/
def nested (d : PathData) : Child Ctx.flow :=
  html! <svg><foreignObject><svg><path d={d} /><path d="M 1 2" /></svg><div><svg><path d="M 1 2" /></svg></div></foreignObject></svg>

#guard (nested .none).raw ==
  el "svg" [] [el "foreignObject" []
    [el "svg" [] [el "path" [("d", "none")], el "path" [("d", "M1,2")]],
     el "div" [] [el "svg" [] [el "path" [("d", "M 1 2")]]]]]

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

-- A value of a raw literal is a literal: the kernel evaluates the literal's values. So no
-- value is spliced on an HTML element below an integration point, nor on an `svg` below one.
/--
error: html!: the value of `class` is spliced on an HTML element inside an SVG subtree; write it as a literal
-/
#guard_msgs (error) in
example (c : String) : Child Ctx.flow :=
  html! <svg><foreignObject><div class={c}></div></foreignObject></svg>

/--
error: html!: the value of `d` is spliced below an HTML element inside an SVG subtree; write it as a literal
-/
#guard_msgs (error) in
example (d : PathData) : Child Ctx.flow :=
  html! <svg><foreignObject><div><svg><path d={d} /></svg></div></foreignObject></svg>

-- A tree with two faults reports the checker's: the structure is judged first, and a value is
-- read only in a tree the checker admits. `x` is no path data, and `rect` takes no `d`.
/-- error: <rect>: the element does not take the attribute `d` -/
#guard_msgs (error) in
example : Child Ctx.flow := html! <svg><rect d="x" /></svg>

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