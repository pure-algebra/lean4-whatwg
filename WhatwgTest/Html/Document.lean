import Whatwg.Html.Node.SvgDocument
import Whatwg.Html.Print.Render
import Whatwg.Url.PercentEncoding

/-!
# WhatwgTest.Html.Document

The page of lean4-effect4's documentation site on the check across a document
(`Whatwg/Html/Content/Document.lean`; entry W2 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at the checkout beside
this repository: `tools/Tools/Document/Html.lean` (`fragment`, `inline`, the algebra's `part`,
`page`, `Document.html`) and `tools/Tools/View/SvgOut.lean` (`cutNodes`). This module imports
nothing of that package. It restates the page's fold under the consumer's names, on a document
cut down to what meets an identifier: a paragraph, a reference to a part, a part with its key,
a field with its label, and a figure that holds a picture of the view.

What it shows:

- **The clash the consumer has today.** `cutNodes` names a clip path `c` and the index of its
  call, so two pictures on one page both define `c0`. `validIn` accepts that page. The check
  reports the clash with the paths of both `clipPath` elements, and `html` refuses the page
  with those words.
- **Stems mend it.** The same page with a stem before each picture's identifiers has no
  problem, and is a `Page`.
- **The seam with the consumer's `fragment`.** A key with a letter outside ASCII is written
  percent-encoded in `href` and plain in `id`. The check follows the standard's steps and finds
  it.
- **A control for each rule**, with the words of `describe` and what the rule rests on.
- **What a reference asks of its element.** `for` names a labelable element, `list` a
  `datalist`, `form` a `form`, `popovertarget` an element with `popover`, and a token of
  `headers` a `th` of the same table. `validIn` accepts each of the trees refused here.
- **The laws at this page.** `picture_closed`: the picture is closed under every stem, by the
  law of a clipped group and one evaluation of what a stem does not touch. `figures_closed`
  carries any two closed pictures with no identifier in common through the `figure` and the
  `main` that the page wraps them in, and `stems_closed` is the two together: two stems that
  differ give a closed `main`, and no page is evaluated for it. `today_not_apart` is the
  control: with no stem the premise fails.
- **The percent-decoding is the URL library's**: `unescapeBytes_eq`.

What this battery does not claim: that the page is the one lean4-effect4 writes. No theorem
relates this fold to that package's. The guards are finite evaluations.
-/

namespace WhatwgTest.Html.Document

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Content.Document

/-! ## The consumer's fold, as it has it -/

/-- `Tools.Document.Html.fragment`: a key as a fragment, a byte outside the fragment's safe
characters percent-encoded. The safe characters are tested on a list here. -/
def fragment (key : String) : String :=
  "#" ++ String.join (key.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || "-._~:@!$'()*+,;=/?".toList.contains c) then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 b.toNat)
      "%" ++ (if digits.length == 1 then "0" ++ digits else digits).toUpper)

/-- `el` of the consumer: an element by its name, its children, then its attributes. -/
def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- `Tools.Document.Inline`, without the code and the status. -/
inductive Inline where
  | text (s : String)
  | ref (key label : String)
  | link (href label : String)

/-- `Tools.Document.Html.inline`. -/
def inline : Inline → RawNode
  | .text s => .text s
  | .ref k label => el "a" [.text label] [("href", fragment k)]
  | .link href label => el "a" [.text label] [("href", href)]

/-- The box that clips a cut. -/
def cutBox : List SvgNode := [Svg.rect 0 0 100 24]

/-- `Tools.View.SvgOut.cutNodes`: a clip path and the group it clips, named `c` and the index
of the cut. The consumer writes no stem; `stem` is what a builder would put before the name. -/
def cutNodes (stem : String) (index : Nat) (children : List SvgNode) : List SvgNode :=
  Svg.clipped (stem ++ ("c" ++ toString index)) cutBox children

/-- The marks of the picture, inside its cut. -/
def marks : List SvgNode := [Svg.rect 0 0 80 20 [.fill (Rgb.ofNat 0x14110d)]]

/-- The attributes of the picture's `svg`: the namespace, the view's class and the frame. -/
def frameAttrs : List (SvgAttr .svg) :=
  .xmlns :: ([.className "e4-view"] ++ Svg.Frame.attrs { width := 100, height := 24 })

/-- A picture of the view with one cut: `Tools.View.SvgOut.picture`, cut down. -/
def picture (stem : String) : SvgNode :=
  Svg.Frame.svg { width := 100, height := 24 } [.className "e4-view"] (cutNodes stem 0 marks)

/-- `Tools.Document.Block`, cut down, with two blocks the site will have: a field with its
label, and a figure that holds a picture. -/
inductive Block where
  | para (line : List Inline)
  | part (key title : String) (body : List Block)
  | field (key label : String)
  | figure (picture : SvgNode) (caption : String)

mutual

/-- The algebra of `Tools.Document.Html`, at a nesting depth: a part is a `section` whose `id`
is its key, with a heading by its depth and a link to itself. -/
def block (depth : Nat) : Block → List RawNode
  | .para l => [el "p" (l.map inline)]
  | .part k t body =>
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text "#"]
        [("class", "self"), ("href", fragment k), ("aria-label", "Link to " ++ t)]]
    [el "section" (heading :: blocks (depth + 1) body) [("id", k)]]
  | .field k label =>
    [el "p" [el "label" [.text label] [("for", k)], el "input" [] [("id", k), ("type", "search")]]]
  | .figure pic caption => [el "figure" [pic.toRaw, el "figcaption" [.text caption]]]
termination_by structural b => b

/-- The blocks of a body, in order. -/
def blocks (depth : Nat) : List Block → List RawNode
  | [] => []
  | b :: rest => block depth b ++ blocks depth rest
termination_by structural bs => bs

end

/-- `Tools.Document.Html.page`, without its style: the head, a link past the header, the
header with the title and the navigation of the parts, then the parts in `main`. -/
def page (title : String) (body : List Block) : RawNode :=
  let tops := body.filterMap fun
    | .part k t _ => some (el "li" [el "a" [.text t] [("href", fragment k)]])
    | _ => none
  el "html" [
    el "head" [el "meta" [] [("charset", "utf-8")], el "title" [.text title]],
    el "body" [
      el "a" [.text "Skip to the content"] [("class", "skip"), ("href", "#content")],
      el "header" ([el "h1" [.text title]] ++
        (if tops.isEmpty then [] else [el "nav" [el "ol" tops] [("aria-label", "Contents")]])),
      el "main" (blocks 2 body) [("id", "content")]]]
    [("lang", "en")]

/-- `Tools.Document.Html.Document.html`, with the check across the document after the content
model: the page's text, or why it is refused. -/
def html (title : String) (body : List Block) : Except String String :=
  let tree := page title body
  if !validIn Ctx.document tree then
    .error ("HTML refused: " ++
      ((explain Ctx.document tree).map fun r => r.reason.describe).getD "the content model")
  else
    match errors tree with
    | [] => .ok (Whatwg.Html.Print.renderDoc tree)
    | found => .error ("HTML refused across the document: " ++
        "; ".intercalate (found.map fun p => p.describe (trail tree)))

/-! ## The page -/

/-- A page as the site writes one: two parts, references between them, a field, and two
pictures, each under the stem given. -/
def site (first second : String) : List Block :=
  [.part "start" "Start here" [
      .para [.text "Read ", .ref "plan" "the plan", .text " first."],
      .field "q" "Find",
      .figure (picture first) "A run"],
   .part "plan" "Plan" [
      .part "req:R1" "R1: a requirement" [.para [.text "Back to ", .ref "start" "the start"]],
      .figure (picture second) "The plan"]]

/-- The page as the consumer writes it today: no stem, so both pictures define `c0`. -/
def today : RawNode := page "Semantics" (site "" "")

/-- The same page with a stem before each picture's identifiers. -/
def stemmed : RawNode := page "Semantics" (site "run-" "plan-")

/-! ### The clash -/

-- The content model sees nothing wrong with two elements under one identifier.
#guard validIn Ctx.document today

-- The check reports the clash, with the paths of both `clipPath` elements.
#guard problems today == [.duplicateId "c0" [1, 2, 0, 3, 0, 0] [1, 2, 1, 2, 0, 0]]

-- Both paths name the `clipPath` elements, and `trail` writes the names along them.
#guard (problems today).map (fun p => (today.at? p.path).bind RawNode.tagName?) ==
  [some "clipPath"]
#guard (problems today).map (fun p => p.describe (trail today)) ==
  ["the identifier `c0` is defined twice: at " ++
    "html/body[1]/main[2]/section[0]/figure[3]/svg[0]/clipPath[0] and at " ++
    "html/body[1]/main[2]/section[1]/figure[2]/svg[0]/clipPath[0]"]

-- By default a path is written as child indices, as the consumer's picture writer does.
#guard (problems today).map (·.describe) ==
  ["the identifier `c0` is defined twice: at the child path [1, 2, 0, 3, 0, 0] and at " ++
    "the child path [1, 2, 1, 2, 0, 0]"]

-- The rule is a requirement of the sealed standard.
#guard (problems today).map (·.basis) == [.requirement (.html "Global attributes")]

-- The consumer's `html` refuses the page with those words.
#guard (match html "Semantics" (site "" "") with
  | .error why => why == "HTML refused across the document: the identifier `c0` is defined " ++
      "twice: at html/body[1]/main[2]/section[0]/figure[3]/svg[0]/clipPath[0] and at " ++
      "html/body[1]/main[2]/section[1]/figure[2]/svg[0]/clipPath[0]"
  | .ok _ => false)

/-! ### Stems -/

#guard validIn Ctx.document stemmed
#guard problems stemmed == []
#guard (Page.check? stemmed).isSome
#guard (match html "Semantics" (site "run-" "plan-") with | .ok _ => true | .error _ => false)

-- What the page holds: the identifiers, in tree order.
#guard names stemmed == ["content", "start", "q", "run-c0", "plan", "req:R1", "plan-c0"]

-- Its references, by their kind: the link past the header, the navigation, each part's link to
-- itself, the references between parts, the label, and each picture's clip.
#guard (refs stemmed).map (fun r => (r.it.kind, r.it.attr, r.it.target)) ==
  [(.fragment, "href", "content"), (.fragment, "href", "start"), (.fragment, "href", "plan"),
   (.fragment, "href", "start"), (.fragment, "href", "plan"), (.idref, "for", "q"),
   (.svgUrl, "clip-path", "run-c0"), (.fragment, "href", "plan"), (.fragment, "href", "req:R1"),
   (.fragment, "href", "start"), (.svgUrl, "clip-path", "plan-c0")]

-- Its outline: the title, then a part, then a part with a part inside.
#guard (headings stemmed).map (·.it.value) == [1, 2, 2, 3]
#guard (mains stemmed).map (·.path) == [[1, 2]]

/-! ### The seam with `fragment` -/

/-- A page whose part has a key outside ASCII. -/
def accented : RawNode :=
  page "Notes" [.part "état" "State" [.para [.ref "état" "again"]]]

-- The key is written percent-encoded in `href` and plain in `id`.
#guard fragment "état" == "#%C3%A9tat"
#guard names accented == ["content", "état"]
#guard (refs accented).map (·.it.target) == ["content", "%C3%A9tat", "%C3%A9tat", "%C3%A9tat"]

-- The standard looks for the fragment as written, then percent-decoded: the link is found.
#guard problems accented == []
#guard unescape "%C3%A9tat" == some "état"

-- A sequence that is no UTF-8 names nothing.
#guard unescape "%FF" == none

/-! ## A control for each rule -/

/-- A document around some flow content, with a first heading. -/
def doc (content : List RawNode) : RawNode :=
  el "html" [el "head" [el "title" [.text "t"]], el "body" (el "h1" [.text "T"] :: content)]

/-- The words and the basis of each problem of a tree. -/
def told (tree : RawNode) : List (String × Basis) :=
  (problems tree).map fun p => (p.describe, p.basis)

-- An identifier is not empty and holds no white space.
#guard told (doc [el "p" [] [("id", "")], el "p" [] [("id", "a b")]]) ==
  [("an `id` is empty: at the child path [1, 1]", .requirement (.html "Global attributes")),
   ("the identifier `a b` holds white space: at the child path [1, 2]",
    .requirement (.html "Global attributes"))]

-- A link to a part that is not there: a convention of the check, not a claim about a standard.
#guard told (doc [el "p" [el "a" [.text "x"] [("href", "#gone")]]]) ==
  [("the link `#gone` names no identifier of the document: at the child path [1, 1, 0]",
    .convention)]

-- A link to another page, and a link with a path before its fragment, are no references of
-- this document. They are kept as addresses, which the check across a site reads
-- (`WhatwgTest/Html/Site.lean`); a fragment alone is a reference, and is not kept twice.
#guard (addresses (doc [el "p" [el "a" [.text "x"] [("href", "../plan/#gone")],
  el "a" [.text "y"] [("href", "https://example.org/")], el "a" [.text "z"] [("href", "#here")]],
  el "p" [] [("id", "here")]])).map (fun a => (a.path, a.it.element, a.it.href)) ==
  [([1, 1, 0], "a", "../plan/#gone"), ([1, 1, 1], "a", "https://example.org/")]
#guard problems (doc [el "p" [el "a" [.text "x"] [("href", "../plan/#gone")],
  el "a" [.text "y"] [("href", "https://example.org/")]]]) == []

-- The empty fragment and `top`, in any case, are the top of the document.
#guard problems (doc [el "p" [el "a" [.text "x"] [("href", "#")],
  el "a" [.text "y"] [("href", "#Top")]]]) == []

-- `for` of `label`: a requirement of the standard.
#guard told (doc [el "p" [el "label" [.text "Find"] [("for", "q")]]]) ==
  [("`for` of `label` names `q`, and no element has that identifier: at the child path [1, 1, 0]",
    .requirement (.html "The label element"))]

-- A list of identifiers gives one reference for each token; `cap` is there and `note` is not.
#guard told (doc [el "p" [.text "c"] [("id", "cap")],
  el "div" [] [("aria-labelledby", "cap  note")]]) ==
  [("`aria-labelledby` of `div` names `note`, and no element has that identifier: at the " ++
    "child path [1, 2]", .convention)]

#guard told (doc [el "table" [el "tr" [el "th" [.text "h"] [("id", "h1")],
  el "td" [.text "d"] [("headers", "h1 h2")]]]]) ==
  [("`headers` of `td` names `h2`, and no element has that identifier: at the child path " ++
    "[1, 1, 0, 1]", .requirement (.html "Attributes common to td and th elements"))]

-- A clip path that no element defines, and a `use` of nothing.
#guard told (doc [el "svg" [el "g" [] [("clip-path", "url(#c9)")], el "use" [] [("href", "#shape")]]]) ==
  [("`clip-path` of `g` refers to `url(#c9)`, and no element has that identifier: at the " ++
    "child path [1, 1, 0]", .convention),
   ("`href` of `use` refers to `#shape`, and no element has that identifier: at the child " ++
    "path [1, 1, 1]", .convention)]

-- An `a` of SVG is a hyperlink as HTML's is, and an `href` on an HTML `link` is not read.
#guard (refs (doc [el "svg" [el "a" [] [("href", "#x")]], el "link" [] [("href", "#x")]])).map
  (fun r => (r.it.element, r.it.kind)) == [("a", .fragment)]

-- One `main` that shows: a second is an error, and a hidden second is not.
#guard told (doc [el "main" [], el "main" []]) ==
  [("a second `main` that is not hidden: at the child path [1, 2], after the one at the child " ++
    "path [1, 1]", .requirement (.html "The main element"))]
#guard problems (doc [el "main" [], el "main" [] [("hidden", "")]]) == []

-- The standard's own example of a skipped level, and its repair (section "Headings and
-- outlines"): `h1`, then `h3` in a `section`.
#guard told (doc [el "section" [el "h3" [.text "Taste"]]]) ==
  [("a heading of level 3 follows one of level 1: at the child path [1, 1, 0], after the " ++
    "heading at the child path [1, 0]", .requirement (.html "Headings and outlines"))]
#guard problems (doc [el "section" [el "h2" [.text "Taste"]]]) == []

-- The standard's example of offsets (section "Heading levels & offsets"): the levels its
-- comments give, 1, 2, 3 and 1. Its last heading has `aria-level`, which this check does not
-- read.
#guard (headings (el "html" [el "head" [el "title" [.text "t"]], el "body" [el "main" [
    el "h1" [.text "1"],
    el "article" [el "h1" [.text "2"],
      el "section" [el "h1" [.text "3"],
        el "dialog" [el "h1" [.text "1"]] [("headingreset", "")]] [("headingoffset", "1")]]
      [("headingoffset", "1")]]]])).map (·.it.value) == [1, 2, 3, 1]

-- A level stops at 9, and an offset that is no number counts as none.
#guard (headings (doc [el "div" [el "h6" [.text "x"]] [("headingoffset", "8")],
  el "div" [el "h2" [.text "y"]] [("headingoffset", "many")]])).map (·.it.value) == [1, 9, 2]

-- Advice is not an error: an outline with no heading of level 1.
#guard told (el "html" [el "head" [el "title" [.text "t"]], el "body" [el "h2" [.text "T"]]]) ==
  [("no heading of the document has level 1: the first heading is at the child path [1, 0]",
    .advice (.html "Headings and outlines"))]
#guard errors (el "html" [el "head" [el "title" [.text "t"]], el "body" [el "h2" [.text "T"]]]) == []

-- The contents of a `template` are another tree: its identifiers are not the document's.
#guard problems (doc [el "template" [el "p" [] [("id", "row")]],
  el "template" [el "p" [] [("id", "row")]], el "p" [el "a" [.text "x"] [("href", "#row")]]]) ==
  [.dangling [1, 3, 0] ⟨"a", "href", .fragment, "row"⟩]

/-! ## What a reference asks of its element -/

-- `for` of `label` names a labelable element. An `input` is one.
#guard problems (doc [el "p" [el "label" [.text "Find"] [("for", "q")], el "input" [] [("id", "q")]]]) == []

-- A `div` is not, and the content model does not see it.
#guard validIn Ctx.document (doc [el "p" [el "label" [.text "Find"] [("for", "q")]],
  el "div" [] [("id", "q")]])
#guard told (doc [el "p" [el "label" [.text "Find"] [("for", "q")]], el "div" [] [("id", "q")]]) ==
  [("`for` of `label` names `q`, which is a `div`, not a labelable element: at the child path " ++
    "[1, 1, 0]", .requirement (.html "The label element"))]

-- An `input` whose `type` is `hidden`, in any case of its letters, is not labelable.
#guard (problems (doc [el "p" [el "label" [.text "Find"] [("for", "q")],
  el "input" [] [("id", "q"), ("type", "Hidden")]]])).map (·.describe) ==
  ["`for` of `label` names `q`, which is a `input`, not a labelable element: at the child path " ++
    "[1, 1, 0]"]

-- An element whose name holds a hyphen may be a form-associated custom element.
#guard problems (doc [el "p" [el "label" [.text "x"] [("for", "w")]], el "my-field" [] [("id", "w")]]) == []

-- Where two elements have the identifier, the first is the one named: both problems are told.
#guard (problems (doc [el "p" [el "label" [.text "Find"] [("for", "q")]], el "div" [] [("id", "q")],
  el "p" [el "input" [] [("id", "q")]]])).map (·.describe) ==
  ["the identifier `q` is defined twice: at the child path [1, 2] and at the child path [1, 3, 0]",
   "`for` of `label` names `q`, which is a `div`, not a labelable element: at the child path " ++
    "[1, 1, 0]"]

-- `list` names a `datalist`.
#guard problems (doc [el "p" [el "input" [] [("list", "towns")], el "datalist" [] [("id", "towns")]]]) == []
#guard told (doc [el "p" [el "input" [] [("list", "towns")]], el "p" [] [("id", "towns")]]) ==
  [("`list` of `input` names `towns`, which is a `p`, not a `datalist`: at the child path " ++
    "[1, 1, 0]", .requirement (.html "The list attribute"))]

-- `form` names a `form`.
#guard problems (doc [el "form" [] [("id", "f")], el "p" [el "input" [] [("form", "f")]]]) == []
#guard told (doc [el "p" [el "input" [] [("form", "f")]], el "div" [] [("id", "f")]]) ==
  [("`form` of `input` names `f`, which is a `div`, not a `form`: at the child path [1, 1, 0]",
    .requirement (.html "Association of controls and forms"))]

-- `popovertarget` names an element with `popover`.
#guard problems (doc [el "p" [el "button" [.text "Open"] [("popovertarget", "tip")]],
  el "div" [] [("id", "tip"), ("popover", "")]]) == []
#guard told (doc [el "p" [el "button" [.text "Open"] [("popovertarget", "tip")]],
  el "div" [] [("id", "tip")]]) ==
  [("`popovertarget` of `button` names `tip`, which is a `div`, an element with no `popover`: " ++
    "at the child path [1, 1, 0]", .requirement (.html "The popover target attributes"))]

-- A token of `headers` names a `th` of the same table, through `thead` and `tbody` too.
#guard problems (doc [el "table" [el "thead" [el "tr" [el "th" [.text "h"] [("id", "k")]]],
  el "tbody" [el "tr" [el "td" [.text "d"] [("headers", "k")]]]]]) == []

-- A `th` of another table, and a `td`, are not.
#guard (problems (doc [el "table" [el "tr" [el "th" [.text "h"] [("id", "a")],
    el "td" [.text "c"] [("id", "c")]]],
  el "table" [el "tr" [el "td" [.text "d"] [("headers", "a c")]]]])).map (·.describe) ==
  ["`headers` of `td` names `a`, which is a `th`, not a `th` of the same table: at the child " ++
    "path [1, 2, 0, 0]",
   "`headers` of `td` names `c`, which is a `td`, not a `th` of the same table: at the child " ++
    "path [1, 2, 0, 0]"]

-- A table inside a cell is a table of its own: a `th` of the outer one is no cell of it.
#guard (problems (doc [el "table" [el "tr" [el "th" [.text "h"] [("id", "outer")],
  el "td" [el "table" [el "tr" [el "td" [.text "d"] [("headers", "outer")]]]]]]])).map (·.path) ==
  [[1, 1, 0, 1, 0, 0, 0]]
#guard tables (doc [el "table" [el "tr" [el "th" [.text "h"] [("id", "outer")],
  el "td" [el "table" [el "tr" [el "td" [.text "d"] [("headers", "outer")]]]]]]]) ==
  [[1, 1], [1, 1, 0, 1, 0]]

/-! ## The laws at this page -/

/-- The box of a cut and the marks define no identifier, and are closed together. -/
theorem shapes_plain :
    namesAllAt .svg (SvgNode.toRawAll cutBox) ++ namesAllAt .svg (SvgNode.toRawAll marks) = [] ∧
      ClosedAll .svg (SvgNode.toRawAll cutBox ++ SvgNode.toRawAll marks) := by
  decide +kernel

/-- The `svg` of the picture writes no identifier and no reference. -/
theorem frame_plain :
    (frameAttrs.map SvgAttr.toPair).filterMap identOf? = [] ∧
      (frameAttrs.map SvgAttr.toPair).flatMap
        (linksOf .svg Whatwg.Svg.Schema.Tag.svg.name) = [] := by
  decide +kernel

/-- A cut is closed under every stem and at every index: its identifier is new, and its group
refers to it (`Svg.closedAll_clipped`). -/
theorem cut_closed (stem : String) (index : Nat) :
    ClosedAll .svg (SvgNode.toRawAll (cutNodes stem index marks)) :=
  Svg.closedAll_clipped (by rw [shapes_plain.1]; exact nofun) shapes_plain.2

theorem picture_eq (stem : String) :
    picture stem = .element .svg frameAttrs (cutNodes stem 0 marks) := rfl

/-- **The picture is closed under every stem.** -/
theorem picture_closed (stem : String) : Closed .html (picture stem).toRaw := by
  rw [picture_eq]
  exact SvgNode.closed_svg frame_plain.1 frame_plain.2 (cut_closed stem 0)

/-- The picture defines one identifier: its stem, then `c0`. -/
theorem names_picture (stem : String) :
    namesAt .html (picture stem).toRaw = [stem ++ ("c" ++ toString 0)] := by
  rw [picture_eq, SvgNode.namesAt_toRaw_svg_of frame_plain.1, cutNodes, Svg.namesAllAt_clipped,
    shapes_plain.1]

/-- Without stems the premise of the composition fails: the two pictures share `c0`. -/
theorem today_not_apart :
    ¬∀ x ∈ namesAt .html (picture "").toRaw, x ∉ namesAllAt .html [(picture "").toRaw] := by
  decide +kernel

/-- A `figure` around a node and a caption defines what the node defines. -/
theorem namesAt_figure (node : RawNode) (caption : String) :
    namesAt .html (el "figure" [node, el "figcaption" [.text caption]]) = namesAt .html node := by
  rw [el, namesAt_element]
  show namesAllAt .html [node, el "figcaption" [.text caption]] = _
  rw [namesAllAt_cons, namesAllAt_cons, el, namesAt_element]
  show namesAt .html node ++ (namesAllAt .html [RawNode.text caption] ++ namesAllAt .html []) = _
  rw [namesAllAt_cons, namesAt_text]
  exact List.append_nil _

/-- A `figure` around a closed node and a caption is closed. -/
theorem figure_closed {node : RawNode} (caption : String) (h : Closed .html node) :
    Closed .html (el "figure" [node, el "figcaption" [.text caption]]) :=
  Closed.element (ns := .html) (name := "figure") rfl rfl
    (ClosedAll.cons h
      ((closedAll_singleton _ _).mpr
        (Closed.element (ns := .html) (name := "figcaption") rfl rfl
          ((closedAll_singleton _ _).mpr (closed_text _ caption))))
      (by
        intro x _ hx
        rw [namesAllAt_cons, el, namesAt_element] at hx
        exact nomatch hx))

/-- **Any two closed pictures with no identifier in common, each in its figure, make a closed
`main`**: what a builder with distinct stems hands the page. -/
theorem figures_closed {a b : RawNode} (ha : Closed .html a) (hb : Closed .html b)
    (hapart : ∀ x ∈ namesAt .html a, x ∉ namesAt .html b) :
    Closed .html (el "main"
      [el "figure" [a, el "figcaption" [.text "one"]],
       el "figure" [b, el "figcaption" [.text "two"]]]) :=
  Closed.element (ns := .html) (name := "main") rfl rfl
    (ClosedAll.cons (figure_closed "one" ha)
      ((closedAll_singleton _ _).mpr (figure_closed "two" hb))
      (by
        intro x hx
        have hone : x ∈ namesAt .html (el "figure" [a, el "figcaption" [.text "one"]]) := hx
        rw [namesAt_figure] at hone
        show x ∉ namesAllAt .html [el "figure" [b, el "figcaption" [.text "two"]]]
        rw [namesAllAt_cons, namesAt_figure]
        show x ∉ namesAt .html b ++ []
        rw [List.append_nil]
        exact hapart x hone))

/-- **Two pictures under two stems that differ, each in its figure, make a closed `main`.** No
page is evaluated: the premise of `figures_closed` is `names_picture` and the two stems. -/
theorem stems_closed {first second : String} (h : first ≠ second) :
    Closed .html (el "main"
      [el "figure" [(picture first).toRaw, el "figcaption" [.text "one"]],
       el "figure" [(picture second).toRaw, el "figcaption" [.text "two"]]]) :=
  figures_closed (picture_closed first) (picture_closed second) (by
    intro x hx hx'
    rw [names_picture, List.mem_singleton] at hx hx'
    exact h ((String.append_left_inj _).mp (hx.symm.trans hx')))

/-! ## The percent-decoding is the URL library's -/

/-- `Document.unescapeBytes` is `Whatwg.Url.PercentEncoding.percentDecodeBytes`: the check
decodes a fragment as the URL Standard does. -/
theorem unescapeBytes_eq : ∀ bytes : List UInt8,
    unescapeBytes bytes = Whatwg.Url.PercentEncoding.percentDecodeBytes bytes
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | b :: hi :: lo :: tail => by
    rw [unescapeBytes, Whatwg.Url.PercentEncoding.percentDecodeBytes,
      unescapeBytes_eq (hi :: lo :: tail), unescapeBytes_eq tail]
    rfl

/-! ## A page of the consumer's size -/

/-- A page with `n` parts, each with its key, its link to itself, and a reference to another
part: the semantics page has 245. -/
def large (n : Nat) : RawNode :=
  page "Semantics" ((List.range n).map fun i =>
    .part ("claim:" ++ toString i) ("Claim " ++ toString i)
      [.para [.text "See ", .ref ("claim:" ++ toString ((i * 7 + 3) % n)) "another"]])

-- 245 parts: 246 identifiers and 736 references, one pass, no problem.
#guard problems (large 245) == []
#guard (names (large 245)).length == 246 && (refs (large 245)).length == 736

end WhatwgTest.Html.Document
