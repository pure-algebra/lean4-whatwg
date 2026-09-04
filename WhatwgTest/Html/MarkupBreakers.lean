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
open Whatwg.Html.Schema (Tag ContentSet)

/-- info: <div> is not admitted here: the content set `phrasing` does not name it -/
#guard_msgs in
#check_failure (html! <p><div>"x"</div></p> : Element .p .phrasing)

/-- info: <div> is not admitted here: the content set `phrasing_without_interactive` does not name it -/
#guard_msgs in
#check_failure (html! <p><a><div>"x"</div></a></p> : Element .p .phrasing)

/-- info: <a> is not admitted here: the content set `phrasing_without_interactive` does not name it -/
#guard_msgs in
#check_failure (html! <p><a><a>"x"</a></a></p> : Element .p .phrasing)

/-- info: text is not admitted here: the content set `only_li` does not name it -/
#guard_msgs in
#check_failure (html! <ul>"loose"</ul> : Element .ul .only_li)

/-- info: <br> is a void element and takes no children -/
#guard_msgs in
#check_failure (html! <br>"x"</br> : Element .br .nothing)

/-- info: unknown element <blink> -/
#guard_msgs in
#check_failure (html! <blink>"x"</blink> : Element .p .phrasing)

/-- info: closing tag </div> does not match <p> -/
#guard_msgs in
#check_failure (html! <p>"x"</div> : Element .p .phrasing)

/-- info: unknown attribute `colour` -/
#guard_msgs in
#check_failure (html! <p colour="red">"x"</p> : Element .p .phrasing)

/-- info: attribute `href` is not admitted on <div>: the attribute set `div_attrib` does not name it -/
#guard_msgs in
#check_failure (html! <div href="/x">"x"</div> : Element .div .flow)

/-- info: attribute `id` is given twice on <div> -/
#guard_msgs in
#check_failure (html! <div id="a" id="b">"x"</div> : Element .div .flow)

/-- info: attribute `data-role`: the prefixed constructor `a_user_data` is not representable in `Attr × String` at this pin -/
#guard_msgs in
#check_failure (html! <div data-role="x">"x"</div> : Element .div .flow)

/-- info: <a> is transparent and needs its context: annotate the expected type as `Child set` or `Element .a inner` -/
#guard_msgs in
#check_failure (html! <a>"x"</a>)

/-- info: <p> is not admitted here: the content set `only_li` does not name it -/
#guard_msgs in
#check_failure (html! <ul><p>"x"</p></ul> : Element .ul .only_li)

/-- info: <video> is transparent and needs its context: annotate the expected type as `Child set` or `Element .video inner` -/
#guard_msgs in
#check_failure (html! <video controls><source src="/v.webm" /></video>)

/-- info: the expected type names <div> but the root is <p> -/
#guard_msgs in
#check_failure (html! <p>"x"</p> : Element .div .flow)

/-- info: the content set of <p> is `phrasing`, not `flow` -/
#guard_msgs in
#check_failure (html! <p>"x"</p> : Element .p .flow)

/-- info: <title> is not admitted here: the content set `flow` does not name it -/
#guard_msgs in
#check_failure (html! <div><title>"x"</title></div> : Element .div .flow)

end WhatwgTest.Html.MarkupBreakers
