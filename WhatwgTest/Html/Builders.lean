import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Erasure

/-!
# WhatwgTest.Html.Builders

Positive probes for the combinators over the context-indexed typed tree
(slice H7, ruling HP-13): constructions that must elaborate. Every
`example` below is a construction whose obligations, one admission per
child and one attribute obligation per element, were discharged by the
`admits` tactic, so the file failing to elaborate is the gate. The
quantified statement behind every construction is `Element.valid` of
`Whatwg.Html.Node.Typed`: what elaborates here is a raw tree the checker
`validIn` accepts.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Builders

open Whatwg.Html
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)

/-! ## A whole document -/

example : Element .html Ctx.document :=
  E.html
    [E.el (E.head
      [E.el (E.title [E.txt "Slice H7"]),
       E.el (E.«meta» [A.a_charset "utf-8"]),
       E.el (E.link [A.a_rel "stylesheet", A.a_href "/site.css"])]),
     E.el (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A paragraph of ", E.el (E.em [E.txt "phrasing"]), E.txt " content."])])]

/-- The same document, as a document of the checker. -/
example : Content.Doc Ctx.document :=
  (E.html [E.el (E.head [E.el (E.title [E.txt "t"])]), E.el (E.body [])]).toDoc

/-! ## Void and childless elements, and the attribute helpers -/

example : Element .img Ctx.flow := E.img [A.a_src "/logo.png", A.a_alt "The logo"]
example : Element .br Ctx.phrasing := E.br [A.a_class "spacer"]
example : Element .input Ctx.phrasing := E.input [A.a_type "text", A.a_name "q"]
example : Element .hr Ctx.flow := E.hr
example : Element .details Ctx.flow := E.details [E.el (E.summary [E.txt "s"])] [A.a_open]
example : Element .iframe Ctx.flow := E.iframe [A.a_src "/frame"]

/-- A typed keyword helper, its string variant, a custom data attribute and an
ARIA attribute. -/
example : Element .p Ctx.flow :=
  E.p [E.txt "x"] [A.a_dir .rtl, A.a_id "p1", A.data_ "role" "nav", A.aria_ "label" "Intro"]
example : Element .p Ctx.flow := E.p [E.txt "x"] [A.a_dir_str "auto"]
example : (E.p (ctx := Ctx.flow) [] [A.data_ "role" "nav"]).toRaw = .element "p" [("data-role", "nav")] [] := rfl

/-! ## Transparency and the descendant exclusions, computed by `Ctx.child` -/

/-- A link in a paragraph: its children are checked with interactive content
and `a` excluded. -/
example : Element .p Ctx.flow :=
  E.p [E.txt "See ", E.el (E.a [E.txt "the spec"] [A.a_href "/spec"]), E.txt "."]

/-- The same link under `div` may hold a `div`: the base is inherited. -/
example : Element .div Ctx.flow :=
  E.div [E.el (E.a [E.el (E.div [E.txt "block link"])] [A.a_href "/x"])]

example : Ctx.child Ctx.phrasing .a = { base := .phrasing, excl := { interactive := true, a := true } } := by decide
example : Ctx.child Ctx.flow .a = { base := .flow, excl := { interactive := true, a := true } } := by decide
/-- Exclusions accumulate through every element, not only transparent ones. -/
example : (Ctx.child (Ctx.child Ctx.flow .dfn) .span).excl = { dfn := true } := by decide

/-! ## Lists, tables, and the labelled children -/

example : Element .ul Ctx.flow :=
  E.ul [E.el (E.li [E.txt "one"]), E.el (E.li [E.txt "two"]), E.el (E.script [E.txt "// script-supporting"])]

example : Element .table Ctx.flow :=
  E.table
    [E.el (E.caption [E.txt "Totals"]),
     E.el (E.thead [E.el (E.tr [E.el (E.th [E.txt "h"])])]),
     E.el (E.tbody [E.el (E.tr [E.el (E.td [E.txt "1"])])])]

/-- `source` and `track` are admitted under `video` as its labelled direct
children, through the context's extras. -/
example : Element .video Ctx.flow :=
  E.video [E.el (E.source [A.a_src "/v.webm"]), E.txt "fallback"] [A.a_controls]

example : Element .map Ctx.flow :=
  E.map [E.el (E.area [A.a_alt "A", A.a_href "/a"]), E.el (E.p [E.txt "x"])] [A.a_name "m"]

/-! ## The standard's own rules -/

example : Element .figure Ctx.flow :=
  E.figure [E.el (E.img [A.a_src "/a.png", A.a_alt "A"]), E.el (E.figcaption [E.txt "Caption"])]
example : Element .summary (Ctx.child Ctx.flow .details) := E.summary [E.el (E.h2 [E.txt "More"])]
example : Element .search Ctx.flow := E.search [E.el (E.p [E.txt "q"])]
example : Element .p Ctx.flow := E.p [E.el (E.data [E.txt "one"] [A.a_value "1"]), E.el (E.bdi [E.txt "x"])]

/-! ## Erasure -/

example : (E.p (ctx := Ctx.flow) [E.txt "x"]).toRaw = .element "p" [] [.text "x"] := rfl
example : (E.br (ctx := Ctx.phrasing) [A.a_class "spacer"]).toRaw = .element "br" [("class", "spacer")] [] := rfl
example : (E.img (ctx := Ctx.flow) [A.a_src "/a.png", A.a_alt "A"]).toRaw =
    .element "img" [("src", "/a.png"), ("alt", "A")] [] := rfl

end WhatwgTest.Html.Builders
