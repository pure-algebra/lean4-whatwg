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

/-- info: text is not admitted here: the content set `ul_content_fun` does not name it -/
#guard_msgs in
#check_failure (html! <ul>"loose"</ul> : Element .ul .ul_content_fun)

/-- info: <br> is a void element and takes no children -/
#guard_msgs in
#check_failure (html! <br>"x"</br> : Element .br .notag)

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
#check_failure (html! <div href="/x">"x"</div> : Element .div .flow5)

/-- info: attribute `id` is given twice on <div> -/
#guard_msgs in
#check_failure (html! <div id="a" id="b">"x"</div> : Element .div .flow5)

/-- info: attribute `data-role`: the prefixed constructor `a_user_data` is not representable in `Attr × String` at this pin -/
#guard_msgs in
#check_failure (html! <div data-role="x">"x"</div> : Element .div .flow5)

/-- info: <a> is transparent and needs its context: annotate the expected type as `Child set` or `Element .a inner` -/
#guard_msgs in
#check_failure (html! <a>"x"</a>)

/-- info: <head> requires a <title> child -/
#guard_msgs in
#check_failure (html! <head><meta charset="utf-8" /></head> : Element .head .metadata_without_title)

/-- info: <figure> takes at most one <figcaption> -/
#guard_msgs in
#check_failure (html! <figure><figcaption>"a"</figcaption><figcaption>"b"</figcaption></figure> : Element .figure .flow5)

/-- info: the expected type names <div> but the root is <p> -/
#guard_msgs in
#check_failure (html! <p>"x"</p> : Element .div .flow5)

/-- info: the content set of <p> is `phrasing`, not `flow5` -/
#guard_msgs in
#check_failure (html! <p>"x"</p> : Element .p .flow5)

/-- info: <title> is not admitted here: the content set `flow5` does not name it -/
#guard_msgs in
#check_failure (html! <div><title>"x"</title></div> : Element .div .flow5)

end WhatwgTest.Html.MarkupBreakers
