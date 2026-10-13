import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Syntax.Elaborator

/-!
# WhatwgTest.Html.MarkupData

Documents written through `html!` where a part is data (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`, its second round; entries W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`, and the two gaps of the first round's report):
`Whatwg/Html/Syntax/Elaborator.lean`.

- A splice is a child, a list of children, or a child that may be absent. Its type says which.
- An attribute value is a text, or a text that may be absent: `aria-current={o}`.
- A markup term under `E.el` takes its position from the expected type and gives its tag.
- An element with an ordered model reads a spliced child that shows its element.

A definition that elaborates is the test, and the guards hold the text it writes. A rejection is
pinned with its words.

What this battery does not claim: that a list or an absent child may stand under an element
with an ordered model. The kernel evaluates that model, and it stops at a list that is a
variable.
-/

namespace WhatwgTest.Html.MarkupData

open Whatwg.Html
open Whatwg.Html.Schema (Tag Attr)
open Whatwg.Html.Content (Ctx)

/-! ## A list of children, and a child that may be absent -/

/-- A list among written children: the items stand between a first and a last one. -/
def menu (items : List (Child (Ctx.flow.child .ul))) : Element .ul Ctx.flow :=
  html! <ul><li>"First"</li>{items}<li>"Last"</li></ul>

/-- A child that may be absent, after one that is always there. -/
def banner (title : String) (nav : Option (Child (Ctx.flow.child .header))) :
    Element .header Ctx.flow :=
  html! <header><h1>{E.txt title}</h1>{nav}</header>

/-- The three kinds of splice in one element, and a list that is computed in place. -/
def part (title : String) (lead : Option (Child (Ctx.flow.child .«section»)))
    (paragraphs : List String) : Element .«section» Ctx.flow :=
  html! <section><h2>{E.txt title}</h2>{lead}{paragraphs.map fun (text : String) =>
    html! <p>{E.txt text}</p>}</section>

#guard (menu []).render == "<ul><li>First</li><li>Last</li></ul>"
#guard (menu [html! <li>"a"</li>, html! <li>"b"</li>]).render ==
  "<ul><li>First</li><li>a</li><li>b</li><li>Last</li></ul>"
#guard (banner "T" none).render == "<header><h1>T</h1></header>"
#guard (banner "T" (some (html! <nav aria-label="Site"></nav>))).render ==
  "<header><h1>T</h1><nav aria-label=\"Site\"></nav></header>"
#guard (part "S" none ["a", "b"]).render == "<section><h2>S</h2><p>a</p><p>b</p></section>"

-- The raw children of a list splice are the raw nodes of the list, in their place.
example (items : List (Child (Ctx.flow.child .ul))) :
    (menu items).toRaw =
      .element "ul" [] (.element "li" [] [.text "First"] ::
        (items.map Child.raw ++ [.element "li" [] [.text "Last"]])) := rfl

-- Control: a splice that is none of the three is refused by its type.
/--
info: Type mismatch
  5
has type
  Nat
but is expected to have type
  Child { base := Schema.Base.only_li }
-/
#guard_msgs in
#check_failure (html! <ul>{(5 : Nat)}</ul> : Element .ul Ctx.flow)

/-! ## An attribute that may be absent (W12) -/

/-- A link that says so when it is the current one: one markup for both cases. -/
def navItem (href label : String) (current : Option String) : Child (Ctx.flow.child .ol) :=
  html! <li><a href={href} aria-current={current}>{E.txt label}</a></li>

#guard (navItem "/a/" "A" none).render == "<li><a href=\"/a/\">A</a></li>"
#guard (navItem "/a/" "A" (some "page")).render ==
  "<li><a href=\"/a/\" aria-current=\"page\">A</a></li>"

/-- An address that may be absent decides a category: with its `href` a link is interactive
content, and without it none. The admission is proved for each case, and in a paragraph the
link is admitted in both. -/
def anchor (href : Option String) (label : String) : Element .p Ctx.flow :=
  html! <p><a href={href}>{E.txt label}</a></p>

#guard (anchor none "x").render == "<p><a>x</a></p>"
#guard (anchor (some "/x") "x").render == "<p><a href=\"/x\">x</a></p>"

-- Control: the case that is refused refuses the markup. With its `href` a link is interactive
-- content, which a `button` excludes.
/--
info: <a> is not admitted here: the context is phrasing, excluding interactive content
-/
#guard_msgs in
variable (href : Option String) in
#check_failure (html! <button><a href={href}>"x"</a></button> : Element .button Ctx.flow)

-- Control: a spliced value where the checker reads the value. `dir` takes keywords.
/--
info: the value of `dir` on <p> is spliced, and the checker reads the value of this attribute: write a literal
-/
#guard_msgs in
variable (d : String) in
#check_failure (html! <p dir={d}>"x"</p> : Element .p Ctx.flow)

/-! ## A markup term under `E.el`, and an ordered model (W9) -/

/-- The expected type of the markup is `Element ?t ctx`: the position is read from it, and the
tag is the root's. Before this round the term fell to flow content and did not fit. -/
def cell (text : String) : Element .tr (Ctx.flow.child .tbody) :=
  E.tr [E.el (html! <td>{E.txt text}</td>), E.el (html! <td class="n">"0"</td>)]

/-- A `head` that a function returns, by cases. Its ordered model is checked in each case. -/
def head (title : String) : Option String → Element .head (Ctx.document.child .html)
  | some sheet => html! <head><title>{E.txt title}</title><link rel="stylesheet" href={sheet} /></head>
  | none => html! <head><title>{E.txt title}</title></head>

/-- The page: `html` has an ordered model, a head and then a body. Each spliced child shows its
element by the type of what `E.el` places, and the head's attributes are not read: `head` has no
category that depends on them. No lemma about `head` is written. -/
def page (title : String) (sheet : Option String)
    (content : List (Child ((Ctx.document.child .html).child .body))) :
    Element .html Ctx.document :=
  html! <html lang="en">{E.el (head title sheet)}{E.el (E.body content)}</html>

#guard (page "T" none []).render ==
  "<html lang=\"en\"><head><title>T</title></head><body></body></html>"

-- Control: the ordered model is read through the splices, and its words are the element's.
/--
info: the children of <html> do not follow its content model: head body
-/
#guard_msgs in
variable (title : String) in
#check_failure (html! <html lang="en">{E.el (E.body [])}{E.el (head title none)}</html> :
  Element .html Ctx.document)

end WhatwgTest.Html.MarkupData
