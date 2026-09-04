import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Erasure

/-!
# WhatwgTest.Html.Builders

Positive probes for the combinators over the schema generated from the
standard (slice H6.1): constructions that must elaborate. Every
`example` below is a construction whose obligations, one child admission
per child and one attribute admission per element, were all discharged by
the `admits` tactic, so the file failing to elaborate is the gate. A
construction is evidence about the generated content model at one point;
the quantified statements are the theorems in `Whatwg.Html.Node.Erasure`
and `Whatwg.Html.Content`.

`WhatwgTest/Html/Breakers.lean` holds the mirror image: the constructions
that must be rejected, each with the obligation that rejects it.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Builders

open Whatwg.Html
open Whatwg.Html.Schema (Tag ContentSet Attr)

/-! ## A whole document -/

/-- A minimal document: `html` with `head` (a `title` and a `meta`) and
`body` (a heading and a paragraph). `head` admits `title` through metadata
content; no labelled form is needed. -/
example : Element .html .only_head_body_strict :=
  E.html
    [E.el (E.head
      [E.el (E.title [E.txt "Slice H6"]),
       E.el (E.«meta» [A.a_charset "utf-8"]),
       E.el (E.link [A.a_rel "stylesheet", A.a_href "/site.css"])]),
     E.el (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A paragraph of ", E.el (E.em [E.txt "phrasing"]), E.txt " content."])])]

/-! ## Void and childless elements, and the attribute helpers -/

example : Element .img .nothing := E.img [A.a_src "/logo.png", A.a_alt "The logo"]
example : Element .br .nothing := E.br [A.a_class "spacer"]
example : Element .input .nothing := E.input [A.a_type "text", A.a_name "q"]
example : Element .hr .nothing := E.hr
/-- A boolean attribute helper takes no value. -/
example : Element .details .flow_with_summary := E.details [E.el (E.summary [E.txt "s"])] [A.a_open]
/-- `iframe` is not void but takes nothing. -/
example : Element .iframe .nothing := E.iframe [A.a_src "/frame"]

/-! ## Transparency, resolved at the position -/

/-- A link in a paragraph checks its children against
`phrasing_without_interactive`. -/
example : Element .p .phrasing :=
  E.p [E.txt "See ", E.el (E.a [E.txt "the spec"] [A.a_href "/spec"]), E.txt "."]

/-- The same link under `div` may hold a `div`, since the payload there is
`flow_without_interactive`. -/
example : Element .div .flow :=
  E.div [E.el (E.a [E.el (E.div [E.txt "block link"])] [A.a_href "/x"])]

example : childSet .phrasing .a = ContentSet.phrasing_without_interactive := rfl
example : childSet .flow .a = ContentSet.flow_without_interactive := rfl
/-- A nested transparent element composes the exclusions. -/
example : childSet .flow_without_interactive .noscript = ContentSet.flow_without_interactive_noscript := rfl

/-! ## Lists, tables, and the labelled children -/

example : Element .ul .only_li :=
  E.ul [E.el (E.li [E.txt "one"]), E.el (E.li [E.txt "two"]), E.el (E.script [E.txt "// script-supporting"])]

example : Element .table .only_caption_colgroup_thead_tbody_tfoot_tr :=
  E.table
    [E.el (E.caption [E.txt "Totals"]),
     E.el (E.thead [E.el (E.tr [E.el (E.th [E.txt "h"])])]),
     E.el (E.tbody [E.el (E.tr [E.el (E.td [E.txt "1"])])])]

/-- `source` and `track` are labelled direct children of `video`. -/
example : Element .video .flow_without_media :=
  E.video [E.txt "fallback"] [E.source [A.a_src "/v.webm"]] [] [A.a_controls]

/-- `area` is a labelled direct child of `map`. -/
example : Element .map .flow :=
  E.map [E.el (E.p [E.txt "x"])] [E.area [A.a_alt "A", A.a_href "/a"]] [A.a_name "m"]

/-! ## The standard's own rules -/

/-- `figure` admits its `figcaption` through its own set. -/
example : Element .figure .flow_with_figcaption :=
  E.figure [E.el (E.img [A.a_src "/a.png", A.a_alt "A"]), E.el (E.figcaption [E.txt "Caption"])]

/-- A `summary` may hold a heading. -/
example : Element .summary .phrasing_with_heading := E.summary [E.el (E.h2 [E.txt "More"])]

/-- The elements the standard added after TyXML 4.6.0. -/
example : Element .search .flow := E.search [E.el (E.p [E.txt "q"])]
example : Element .p .phrasing := E.p [E.el (E.data [E.txt "one"] [A.a_value "1"]), E.el (E.bdi [E.txt "x"])]

/-- Weakening a child of a derived set to its parent's position: the
inclusion is `parent_subset`, decided on the generated table. -/
example (c : Child .flow_without_interactive_noscript) : Child .flow_without_interactive :=
  Child.weaken (Content.parent_subset .flow_without_interactive_noscript .flow_without_interactive (by decide)) c

/-! ## Erasure -/

example : (E.p [E.txt "x"]).toRaw = .element "p" [] [.text "x"] := rfl
example : (E.br [A.a_class "spacer"]).toRaw = .element "br" [("class", "spacer")] [] := rfl
example : (E.img [A.a_src "/a.png", A.a_alt "A"]).toRaw = .element "img" [("src", "/a.png"), ("alt", "A")] [] := rfl

end WhatwgTest.Html.Builders
