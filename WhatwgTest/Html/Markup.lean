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
open Whatwg.Html.Schema (Tag ContentSet Attr)
open Whatwg.Html.Print

/-! ## Elements, text, attributes -/

/-- A paragraph with phrasing children and a text run. -/
example : Element .p .phrasing := html! <p>"Hello, " <em>"world"</em>"."</p>

/-- Attributes: a literal, a spliced `String`, a presence attribute, and the
keyword names `class` and `for`. -/
example : Element .label .phrasing_without_label :=
  html! <label class="field" for={"q" ++ "1"}>"Query"</label>

example : Element .details .flow5 :=
  html! <details open><summary>"More"</summary><p>"Detail"</p></details>

/-- A dashed attribute name. -/
example : Element .«meta» .notag := html! <meta http-equiv="refresh" />

/-- The keyword element names. -/
example : Element .«section» .flow5 := html! <section><h2>"Title"</h2></section>

/-- A void element, self-closing, with attributes. -/
example : Element .br .notag := html! <br class="spacer" />

/-- A self-closing non-void element is an empty one. -/
example : Element .div .flow5 := html! <div />

/-! ## Splices and context -/

/-- A spliced `Child` term inside markup. -/
example : Element .div .flow5 :=
  html! <div>{E.el (E.p [E.txt "from the combinators"])}<p>"from markup"</p></div>

/-- A transparent root takes its context from the expected type: under
`phrasing` the link's children are checked against
`phrasing_without_interactive`. -/
example : Child .phrasing := html! <a href="/x"><em>"go"</em></a>

/-- The same root under `flow5`, where a `div` is admitted inside the link. -/
example : Child .flow5 := html! <a href="/x"><div>"block link"</div></a>

/-- A transparent root with an explicit `inner`. -/
example : Element .a .flow5_without_interactive := html! <a><div>"x"</div></a>

/-- A markup term as a combinator argument: the expected type is
`Element .p (childSet .flow5 .p)`, which `html!` reads through `childSet`. -/
example : Element .div .flow5 := E.div [E.el (html! <p>"inside"</p>)]

/-! ## Labelled forms -/

example : Element .figure .flow5 :=
  html! <figure><img src="/a.png" alt="A" /><figcaption>"Caption"</figcaption></figure>

/-- `<table>` with row groups is TyXML's `tablex`; with rows it is `table`.
Both carry the labelled `caption`, `colgroup`, `thead` and `tfoot`. -/
example : Element .table .tablex_content_fun :=
  html! <table><caption>"Totals"</caption><thead><tr><th>"h"</th></tr></thead>
          <tbody><tr><td>"1"</td></tr></tbody></table>

example : Element .table .table_content_fun :=
  html! <table><colgroup><col span="2" /></colgroup><tr><td>"1"</td><td>"2"</td></tr></table>

example : Element .video .flow5_without_media :=
  html! <video controls><source src="/v.webm" /><source src="/v.mp4" /></video>

/-! ## A whole document, and agreement with the combinators -/

/-- The H3 document of `WhatwgTest/Html/Builders.lean`, in markup. -/
def page : Element .html .html_content_fun :=
  html! <html>
    <head><title>"Slice H3"</title><meta charset="utf-8" /><link rel="stylesheet" href="/site.css" /></head>
    <body><h1>"Content models"</h1><p>"A paragraph of " <em>"phrasing"</em>" content."</p></body>
  </html>

/-- The same document through the combinators. -/
def pageCombinators : Element .html .html_content_fun :=
  E.html
    (E.head (E.title (E.txt "Slice H3"))
      [E.el (E.«meta» [A.a_charset "utf-8"]),
       E.el (E.link "stylesheet" "/site.css")])
    (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A paragraph of ", E.el (E.em [E.txt "phrasing"]), E.txt " content."])])

/-- The two erase to the same raw tree, definitionally. -/
example : page.toRaw = pageCombinators.toRaw := rfl

set_option maxRecDepth 8000 in
example : render page.toRaw =
    "<html><head><title>Slice H3</title><meta charset=\"utf-8\" /><link rel=\"stylesheet\" href=\"/site.css\" /></head><body><h1>Content models</h1><p>A paragraph of <em>phrasing</em> content.</p></body></html>" := by
  decide

set_option maxRecDepth 2000 in
/-- A presence attribute prints as its own name, as TyXML prints
`a_hidden ()`. -/
example : render (html! <p hidden>"x"</p> : Element .p .phrasing).toRaw = "<p hidden=\"hidden\">x</p>" := by
  decide

end WhatwgTest.Html.Markup
