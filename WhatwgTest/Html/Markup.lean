import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Print.Render

/-!
# WhatwgTest.Html.Markup

Positive probes for slice H5: documents written through `html!` that must
elaborate, and their erasure compared with the same documents built through
the combinators of H3, so that the two surfaces are seen to agree on the
raw tree at these points. `WhatwgTest/Html/MarkupBreakers.lean` holds the
rejections with their pinned diagnostics, and
`WhatwgTest/Html/MarkupBenchmark.lean` the cost.

Each construction here is a finite probe about the sealed TyXML 4.6.0
projection at one point. The repository's elaboration-time axiom gate in
`WhatwgTest.lean` audits every declaration compiled here, so no per-file
axiom report is written.
-/

namespace WhatwgTest.Html.Markup

open Whatwg.Html
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)
open Whatwg.Html.Print

/-! ## Elements, text, attributes -/

/-- A paragraph with phrasing children and a text run. -/
example : Element .p Ctx.flow := html! <p>"Hello, " <em>"world"</em>"."</p>

/-- Attributes: a literal, a spliced `String`, a presence attribute, and the
keyword names `class` and `for`. -/
example : Element .label Ctx.flow :=
  html! <label class="field" for={"q" ++ "1"}>"Query"</label>

example : Element .details Ctx.flow :=
  html! <details open><summary>"More"</summary><p>"Detail"</p></details>

/-- Custom data and ARIA attributes carry their suffix. -/
example : Element .div Ctx.flow := html! <div data-role="nav" aria-label="Intro">"x"</div>
example : (html! <div data-role="nav">"x"</div> : Element .div Ctx.flow).toRaw =
    .element "div" [("data-role", "nav")] [.text "x"] := rfl

/-- A dashed attribute name. -/
example : Element .«meta» Ctx.metadata := html! <meta http-equiv="refresh" />

/-- A keyword attribute with a valid keyword, and a bare boolean one. -/
example : Element .p Ctx.flow := html! <p dir="rtl" hidden>"x"</p>

/-- The keyword element names. -/
example : Element .«section» Ctx.flow := html! <section><h2>"Title"</h2></section>

/-- A void element, self-closing, with attributes. -/
example : Element .br Ctx.flow := html! <br class="spacer" />

/-- A self-closing non-void element is an empty one. -/
example : Element .div Ctx.flow := html! <div />

/-! ## Splices and context -/

/-- A spliced `Child` term inside markup. -/
example : Element .div Ctx.flow :=
  html! <div>{E.el (E.p [E.txt "from the combinators"])}<p>"from markup"</p></div>

/-- A transparent root takes its context from the expected type: under
`phrasing` the link's children are checked against
`phrasing_without_interactive`. -/
example : Child Ctx.phrasing := html! <a href="/x"><em>"go"</em></a>

/-- The same root under `flow`, where a `div` is admitted inside the link. -/
example : Child Ctx.flow := html! <a href="/x"><div>"block link"</div></a>

/-- A transparent root in a named context. -/
example : Element .a Ctx.flow := html! <a><div>"x"</div></a>

/-- A root without an annotation takes the context its categories suggest. -/
example := html! <p>"x"</p>
example := html! <html><head><title>"t"</title></head><body></body></html>

/-- A markup term as a combinator argument: the expected type is
`Element .p (Ctx.child Ctx.flow .div)`, which `html!` reads through `whnf`. -/
example : Element .div Ctx.flow := E.div [E.el (html! <p>"inside"</p>)]

/-! ## Labelled forms -/

example : Element .figure Ctx.flow :=
  html! <figure><img src="/a.png" alt="A" /><figcaption>"Caption"</figcaption></figure>

/-- A table with row groups, and one with rows: both are membership in the
table base; order is a later reading. -/
example : Element .table Ctx.flow :=
  html! <table><caption>"Totals"</caption><thead><tr><th>"h"</th></tr></thead>
          <tbody><tr><td>"1"</td></tr></tbody></table>

example : Element .table Ctx.flow :=
  html! <table><colgroup><col span="2" /></colgroup><tr><td>"1"</td><td>"2"</td></tr></table>

example : Element .video Ctx.flow :=
  html! <video controls><source src="/v.webm" /><source src="/v.mp4" /></video>

/-! ## A whole document, and agreement with the combinators -/

/-- The H3 document of `WhatwgTest/Html/Builders.lean`, in markup. -/
def page : Element .html Ctx.document :=
  html! <html>
    <head><title>"Slice H3"</title><meta charset="utf-8" /><link rel="stylesheet" href="/site.css" /></head>
    <body><h1>"Content models"</h1><p>"A paragraph of " <em>"phrasing"</em>" content."</p></body>
  </html>

/-- The same document through the combinators. -/
def pageCombinators : Element .html Ctx.document :=
  E.html
    [E.el (E.head
      [E.el (E.title [E.txt "Slice H3"]),
       E.el (E.«meta» [A.a_charset "utf-8"]),
       E.el (E.link [A.a_rel "stylesheet", A.a_href "/site.css"])]),
     E.el (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A paragraph of ", E.el (E.em [E.txt "phrasing"]), E.txt " content."])])]

/-- The two erase to the same raw tree, definitionally. -/
example : page.toRaw = pageCombinators.toRaw := rfl

set_option maxRecDepth 8000 in
example : render page.toRaw =
    "<html><head><title>Slice H3</title><meta charset=\"utf-8\"><link rel=\"stylesheet\" href=\"/site.css\"></head><body><h1>Content models</h1><p>A paragraph of <em>phrasing</em> content.</p></body></html>" := by
  decide

set_option maxRecDepth 2000 in
/-- A bare attribute is the empty string. -/
example : render (html! <p hidden>"x"</p> : Element .p Ctx.flow).toRaw = "<p hidden=\"\">x</p>" := by
  decide

end WhatwgTest.Html.Markup
