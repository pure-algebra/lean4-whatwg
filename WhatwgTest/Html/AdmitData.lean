import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.AdmitData

Constructions and rejections of the combinators where a part of the tree is data (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`, its second round; entries W8, W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`): the tactic `admits` of
`Whatwg/Html/Node/Admit.lean`, on the laws of `Whatwg/Html/Node/Splice.lean`.

Each construction below was refused before this round, with "Expected type must not contain
free variables": the tactic read only a list of literals, and its fallback decides only a
closed proposition. A definition that elaborates here is the test. A rejection is pinned with
its words, since the words are what a writer of a page reads.

What this battery does not claim: that every obligation with data in it is closed. A value
that the checker reads must be a literal, and so must a child of an element with an ordered
model.
-/

namespace WhatwgTest.Html.AdmitData

open Whatwg.Html
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)

/-! ## A computed name (W8) -/

/-- `aria-label` beside children that are a variable: the name is `"aria-" ++ "label"`. -/
def contents (items : List (Child ((Ctx.flow.child .nav).child .ol))) : Element .nav Ctx.flow :=
  E.nav [E.el (E.ol items)] [A.aria_ "label" "Contents"]

/-- A custom data attribute whose value is data. -/
def status (word : String) : Element .span Ctx.phrasing :=
  E.span [E.txt word] [A.a_class "status", A.data_ "status" word]

#guard (contents []).render == "<nav aria-label=\"Contents\"><ol></ol></nav>"
#guard (status "proved").render == "<span class=\"status\" data-status=\"proved\">proved</span>"

/-! ## A computed value (W8) -/

def fragment (key : String) : String := "#" ++ key

/-- A link whose address is computed, placed as a child: both obligations hold a value that is
data, the element's own and its admission. -/
def link (key label : String) : Child Ctx.phrasing :=
  E.el (E.a [E.txt label] [A.a_href (fragment key)])

/-- Two values that are data and one literal. -/
def sheet (href media : String) : Element .link Ctx.metadata :=
  E.link [A.a_rel "stylesheet", A.a_href href, A.a_media media]

#guard (link "a" "A").render == "<a href=\"#a\">A</a>"

-- Reader of `Content.attrOk_of_attrFree`: what the tactic tests is a closed test, and the law
-- answers for every address.
example (href : String) : Content.attrOk .a "href" href = true :=
  Content.attrOk_of_attrFree (by decide +kernel) href

-- Control: a value that the checker reads is no data. `scope` takes keywords.
/--
info: could not synthesize default value for parameter '_ho' using tactics
---
info: the value of `scope` on <th> is no literal, and the checker reads the value of this attribute: write a literal, or case on the value
---
info: fun x => E.th [] [A.a_scope_str x] ⋯ : String → Element Tag.th (Ctx.flow.child Tag.tr)
-/
#guard_msgs in
#check_failure (fun x => E.th [] [A.a_scope_str x] : String → Element .th (Ctx.flow.child .tr))

-- Control: an attribute that the element does not take is refused by its name, with a value
-- that is data as with a literal.
/--
info: could not synthesize default value for parameter '_ho' using tactics
---
info: attribute `href` is not admitted on <p>: the attribute set `p_attrib` does not name it
---
info: fun x => E.p [] [A.a_href x] ⋯ : String → Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (fun x => E.p [] [A.a_href x] : String → Element .p Ctx.flow)

-- Control: an admission that reads a value. An `input` is interactive content unless its
-- `type` is `hidden`, so inside a link the type must be a literal.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: whether <input> is admitted here reads the value of `type`, which is no literal: write a literal, or case on the value
---
info: fun x => E.a [E.el (E.input [A.a_type x, A.a_name "q"] ⋯) ⋯] [A.a_href "/x"] ⋯ : String → Element Tag.a Ctx.flow
-/
#guard_msgs in
#check_failure (fun x => E.a [E.el (E.input [A.a_type x, A.a_name "q"])] [A.a_href "/x"] :
  String → Element .a Ctx.flow)

/-! ## An attribute that may be absent (W12) -/

/-- A link that says so when it is the current one: one definition for both cases. -/
def navLink (href label : String) (current : Option String) : Child (Ctx.flow.child .li) :=
  E.el (E.a [E.txt label] (A.a_href href :: A.opt (A.aria_ "current") current))

#guard (navLink "/a/" "A" none).render == "<a href=\"/a/\">A</a>"
#guard (navLink "/a/" "A" (some "page")).render == "<a href=\"/a/\" aria-current=\"page\">A</a>"

/-- Two attributes that may be absent, and an option that is computed. -/
def cell (label : String) (title : Option String) (wide : Bool) : Element .td (Ctx.flow.child .tr) :=
  E.td [E.txt label] (A.opt A.a_title title ++ A.opt A.a_class (if wide then some "wide" else none))

#guard (cell "x" (some "t") true).render == "<td title=\"t\" class=\"wide\">x</td>"
#guard (cell "x" none false).render == "<td>x</td>"

-- Control: an attribute that may be absent is still an attribute of its element.
/--
info: could not synthesize default value for parameter '_ho' using tactics
---
info: attribute `href` is not admitted on <p>: the attribute set `p_attrib` does not name it
---
info: fun o => E.p [] (A.opt A.a_href o) ⋯ : Option String → Element Tag.p Ctx.flow
-/
#guard_msgs in
#check_failure (fun o => E.p [] (A.opt A.a_href o) : Option String → Element .p Ctx.flow)

/-! ## Attributes that are not written out (W9) -/

/-- A `head` that a function returns, by cases on its argument. -/
def head (title : String) : Bool → Element .head (Ctx.document.child .html)
  | true => E.head [E.el (E.title [E.txt title]), E.el (E.«meta» [A.a_charset "utf-8"])]
  | false => E.head [E.el (E.title [E.txt title])]

/-- The head placed as a child: its attributes are those of a variable, and `head` has no
category that reads an attribute, so the admission is that of the tag. No lemma about the
attributes of `head` is written. -/
def headChild (title : String) (charset : Bool) : Child (Ctx.document.child .html) :=
  E.el (head title charset)

/-- The page around it: `html` has an ordered model, which reads the tag of each child, and
`E.el e` shows the tag of `e` by its type. -/
def page (title : String) (charset : Bool) (content : List (Child ((Ctx.document.child .html).child .body))) :
    Element .html Ctx.document :=
  E.html [E.el (head title charset), E.el (E.body content)]

#guard (page "T" false []).render == "<html><head><title>T</title></head><body></body></html>"

-- Control: an element with a conditional category is not placed with attributes unknown. A
-- link is interactive content when it has an `href`.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: <a> is not admitted here by its tag alone: the context is phrasing, excluding interactive content. Whether it is admitted reads its attributes, which are not written out
---
info: fun e => E.button [E.el e ⋯] [] ⋯ : Element Tag.a (Ctx.flow.child Tag.button) → Element Tag.button Ctx.flow
-/
#guard_msgs in
#check_failure (fun e => E.button [E.el e] :
  Element .a (Ctx.flow.child .button) → Element .button Ctx.flow)

end WhatwgTest.Html.AdmitData
