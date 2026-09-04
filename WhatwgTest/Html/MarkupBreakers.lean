import Whatwg.Html.Syntax.Elaborator

/-!
# WhatwgTest.Html.MarkupBreakers

The error-message contract of slice H5, frozen: each `#guard_msgs` pins the
exact diagnostic `html!` reports, at the token it reports it, and a probe
that starts failing for another reason fails this file rather than passing
it silently. The messages name the element (or the text, or the attribute)
and the set that excludes it, with a transparent payload already resolved,
in the words the `admits` tactic of `Whatwg.Html.Node.Admit` uses for the
combinators, so the two surfaces report the same fact the same way.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.MarkupBreakers

open Whatwg.Html
open Whatwg.Html.Schema (Tag)
open Whatwg.Html.Content (Ctx)

/-- info: <div> is not admitted here: the context is phrasing -/
#guard_msgs in
#check_failure (html! <p><div>"x"</div></p> : Element .p Ctx.flow)

/-- info: <div> is not admitted here: the context is phrasing, excluding interactive content, a -/
#guard_msgs in
#check_failure (html! <p><a><div>"x"</div></a></p> : Element .p Ctx.flow)

/-- info: <a> is not admitted here: the context is phrasing, excluding interactive content, a -/
#guard_msgs in
#check_failure (html! <p><a><a>"x"</a></a></p> : Element .p Ctx.flow)

/-- info: text is not admitted here: the context is only_li -/
#guard_msgs in
#check_failure (html! <ul>"loose"</ul> : Element .ul Ctx.flow)

/-- info: <br> is a void element and takes no children -/
#guard_msgs in
#check_failure (html! <br>"x"</br> : Element .br Ctx.flow)

/-- info: unknown element <blink> -/
#guard_msgs in
#check_failure (html! <blink>"x"</blink> : Element .p Ctx.flow)

/-- info: closing tag </div> does not match <p> -/
#guard_msgs in
#check_failure (html! <p>"x"</div> : Element .p Ctx.flow)

/-- info: unknown attribute `colour` -/
#guard_msgs in
#check_failure (html! <p colour="red">"x"</p> : Element .p Ctx.flow)

/-- info: attribute `href` is not admitted on <div>: the attribute set `div_attrib` does not name it -/
#guard_msgs in
#check_failure (html! <div href="/x">"x"</div> : Element .div Ctx.flow)

/-- info: attribute `id` is given twice on <div> -/
#guard_msgs in
#check_failure (html! <div id="a" id="b">"x"</div> : Element .div Ctx.flow)

/-- info: attribute `data-role`: the prefixed attributes `data-*` and `aria-*` are not representable in `Attr × String` at this pin -/
#guard_msgs in
#check_failure (html! <div data-role="x">"x"</div> : Element .div Ctx.flow)

/-- info: <p> is not admitted here: the context is only_li -/
#guard_msgs in
#check_failure (html! <ul><p>"x"</p></ul> : Element .ul Ctx.flow)

/-- info: the expected type names <div> but the root is <p> -/
#guard_msgs in
#check_failure (html! <p>"x"</p> : Element .div Ctx.flow)

-- A descendant exclusion holds through a non-transparent element.
/-- info: <dfn> is not admitted here: the context is phrasing, excluding dfn -/
#guard_msgs in
#check_failure (html! <dfn><span><dfn>"x"</dfn></span></dfn> : Element .dfn Ctx.phrasing)

/-- info: <title> is not admitted here: the context is flow -/
#guard_msgs in
#check_failure (html! <div><title>"x"</title></div> : Element .div Ctx.flow)

/-! ## Literal values against the attribute index -/

/-- info: attribute `dir` on <p> takes one of `ltr`, `rtl`, `auto`, not `lefty` -/
#guard_msgs in
#check_failure (html! <p dir="lefty">"x"</p> : Element .p Ctx.flow)

/-- info: attribute `hidden` on <p> takes one of `until-found`, `hidden`, or the empty string, not `yes` -/
#guard_msgs in
#check_failure (html! <p hidden="yes">"x"</p> : Element .p Ctx.flow)

/-- info: attribute `open` is a boolean attribute: write it bare, or with the empty string or its own name as its value -/
#guard_msgs in
#check_failure (html! <details open="yes"><summary>"s"</summary></details> : Element .details Ctx.flow)

/-- info: attribute `colspan` takes a valid non-negative integer, not `two` -/
#guard_msgs in
#check_failure (html! <td colspan="two">"x"</td> : Element .td Ctx.flow)

/-- info: attribute `colspan` takes a valid non-negative integer, not `` -/
#guard_msgs in
#check_failure (html! <td colspan>"x"</td> : Element .td Ctx.flow)

end WhatwgTest.Html.MarkupBreakers
