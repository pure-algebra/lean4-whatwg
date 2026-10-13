import Whatwg.Html.Node.Combinators
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Check

/-!
# WhatwgTest.Html.UseCheck

A page of lean4-effect4's documentation site on the typed tree, with its content checked once
where it enters (slice S17 of `docs/SVG-PACKAGE-PLAN.md`; entry W1 of
`docs/research/2026-10-12-whatwg-requests.md`). This module imports nothing of that package. It
restates the document's types and the fold under the consumer's names.

The consumer is read at two commits. At `07b2b4752` its page is one raw tree, checked whole when
it is written (`page`, `tools/Tools/Document/Html.lean`): `rawPage` here. At `e04ea78a5` it has a
typed shell of its own (`tools/Tools/Site.lean`), with an admission function of its own that is
`Child.check` of this package, definition for definition, and a function `blocks` that admits
each node of the fold alone: `blocksTheirs` here. The shell of this module was written against the first, before
the second was read, and it came to the same form: markup for the fixed parts, a combinator
where a list is data, a typed `let` for a part that may be absent.

What the new interface changes for the consumer:

- **The admission function is the package's**: `Child.check`, with its laws.
- **The content enters by one call** (`page`, `blocks`): `Child.acceptAll` makes the fold's
  nodes the children of `main`, or answers the first refusal in words, with the place of the
  refused block among the blocks. The consumer's `mapM` over its own function is the same list
  (`Child.checkAll?_eq_mapM`).
- **`describe` is the package's** (`Refusal.describeIn`), through `acceptAll`.
- **A position has a short name**: `Ctx.document.below [.html, .body, .main]`.

How a shell is written, and why. The term `html!` writes the fixed markup, a text that is data
(`{E.txt title}`) and an attribute value that is data (`href={looks}`). A list that is data
goes through a combinator, `E.ol toc`, since `html!` splices one child and no list. A part that
may be absent is an element of a list, so `header` and `body` are combinators too.

What this battery proves and what it does not. `page_toRaw` proves the typed page equal to
`rawPage` for every document whose content the checker accepts. `rawPage` and the fold are
copies by hand of the consumer's code, with three differences: a reference's link is its
fragment (no `target`), the styles are the two linked files of a page of the site, and the
summary of a diagram's source does not count its lines. No theorem relates this module to that
package.
-/
namespace WhatwgTest.Html.UseCheck

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Schema (Tag)

/-! ## The document, as the consumer has it (`tools/Tools/Document.lean`) -/

/-- Inline content (`Tools.Document.Inline`). -/
inductive Inline where
  | text (s : String)
  | code (s : String)
  | ref (key label : String)
  | link (href label : String)
  | status (word : String)

/-- A run of inline content (`Tools.Document.Line`). -/
abbrev Line := List Inline

/-- Block content (`Tools.Document.Block`). -/
inductive Block where
  | para (line : Line)
  | fields (rows : List (String × Line))
  | items (lines : List Line)
  | code (language body : String)
  | table (headers : List String) (rows : List (List Line))
  | part (key title : String) (body : List Block)

/-- A document (`Tools.Document.Document`). -/
structure Document where
  title : String
  producer : List String := []
  body : List Block

/-! ## The fold to raw nodes (`tools/Tools/Document/Html.lean`) -/

/-- A fragment identifier for a key (`Tools.Document.Html.fragment`). -/
def fragment (key : String) : String :=
  "#" ++ String.join (key.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || "-._~:@!$'()*+,;=/?".contains c) then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 b.toNat)
      "%" ++ (if digits.length == 1 then "0" ++ digits else digits).toUpper)

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- `Tools.Document.Html.inline`. -/
def inline : Inline → RawNode
  | .text s => .text s
  | .code s => el "code" [.text s]
  | .ref k label => el "a" [.text label] [("href", fragment k)]
  | .link href label => el "a" [.text label] [("href", href)]
  | .status w => el "span" [.text w] [("class", "status"), ("data-status", w)]

def line (l : Line) : List RawNode := l.map inline

mutual

/-- The HTML fold of a block at a nesting depth (`Tools.Document.Html.algebra`). -/
def blockNodes (depth : Nat) : Block → List RawNode
  | .para l => [el "p" (line l)]
  | .fields rs => [el "dl" (rs.flatMap fun (k, v) => [el "dt" [.text k], el "dd" (line v)])]
  | .items ls => [el "ul" (ls.map fun l => el "li" (line l))]
  | .code lang body =>
    let block := el "pre" [el "code" [.text body] [("class", "language-" ++ lang)]]
    if lang == "mermaid" then
      [el "details" [el "summary" [.text "Diagram source (Mermaid)"], block] [("class", "diagram")]]
    else [block]
  | .table hs rs =>
    if rs.isEmpty then [] else
      let head := el "thead" [el "tr" (hs.map fun h => el "th" [.text h] [("scope", "col")])]
      let body := el "tbody" (rs.map fun r => el "tr" (r.map fun c => el "td" (line c)))
      [el "div" [el "table" [head, body]]
        [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
         ("aria-label", "Table: " ++ ", ".intercalate hs)]]
  | .part k t body =>
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text "#"] [("class", "self"), ("href", fragment k), ("aria-label", "Link to " ++ t)]]
    [el "section" (heading :: blocksNodes (depth + 1) body) [("id", k)]]

/-- The fold of a list of blocks. -/
def blocksNodes (depth : Nat) : List Block → List RawNode
  | [] => []
  | block :: rest => blockNodes depth block ++ blocksNodes depth rest

end

/-- The keys and titles of the top-level parts. -/
def tops (d : Document) : List (String × String) :=
  d.body.filterMap fun
    | .part k t _ => some (k, t)
    | _ => none

/-- The page as the consumer builds it today: one raw tree (`Tools.Document.Html.page`, with
the two style files of `Tools.Site.sheet`), checked whole when it is written. -/
def rawPage (d : Document) (looks rules : String) : RawNode :=
  let items := (tops d).map fun (k, t) => el "li" [el "a" [.text t] [("href", fragment k)]]
  el "html" [
    el "head" [
      el "meta" [] [("charset", "utf-8")],
      el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
      el "title" [.text d.title],
      el "link" [] [("rel", "stylesheet"), ("href", looks)],
      el "link" [] [("rel", "stylesheet"), ("href", rules)]],
    el "body" ([
      el "a" [.text "Skip to the content"] [("class", "skip"), ("href", "#content")],
      el "header" ([el "h1" [.text d.title]] ++
        (if items.isEmpty then [] else [el "nav" [el "ol" items] [("aria-label", "Contents")]])),
      el "main" (blocksNodes 2 d.body) [("id", "content")]] ++
      (if d.producer.isEmpty then [] else
        [el "footer" [el "p" [.text "Provenance"] [("class", "label")],
          el "ul" (d.producer.map fun note => el "li" [.text note])]]))]
    [("lang", "en")]

/-! ## The page on the typed tree -/

/-- Where the content of a page stands: the children of `main`. -/
abbrev mainCtx : Ctx := Ctx.document.below [.html, .body, .main]

/-- Where an item of the contents list stands. -/
abbrev tocCtx : Ctx := Ctx.document.below [.html, .body, .header, .nav, .ol]

/-- Where an item of a list of the site's pages stands. -/
abbrev siteCtx : Ctx := Ctx.document.below [.html, .body, .aside, .nav, .ul]

/-- Where a line of the provenance stands. -/
abbrev noteCtx : Ctx := Ctx.document.below [.html, .body, .footer, .ul]

/-- Where the parts of the body stand, and those of the header. -/
abbrev bodyCtx : Ctx := Ctx.document.below [.html, .body]
abbrev headerCtx : Ctx := Ctx.document.below [.html, .body, .header]

/-- The shell of a page: valid for every title, every address of a style file, and every list
of typed children. The contents list, the list of the site's pages and the footer are left out
when they are empty, as the consumer's page leaves them out. -/
def shell (title looks rules : String) (toc : List (Child tocCtx)) (content : List (Child mainCtx))
    (site : List (Child siteCtx)) (notes : List (Child noteCtx)) : Element .html Ctx.document :=
  let skip : Child bodyCtx := html! <a class="skip" href="#content">"Skip to the content"</a>
  let contents : List (Child headerCtx) :=
    if toc.isEmpty then [] else [html! <nav aria-label="Contents">{E.el (E.ol toc)}</nav>]
  let pages : List (Child bodyCtx) :=
    if site.isEmpty then [] else
      [html! <aside><nav aria-label="Pages">{E.el (E.ul site)}</nav></aside>]
  let footer : List (Child bodyCtx) :=
    if notes.isEmpty then [] else
      [html! <footer><p class="label">"Provenance"</p>{E.el (E.ul notes)}</footer>]
  html! <html lang="en">
    <head>
      <meta charset="utf-8" />
      <meta name="viewport" content="width=device-width, initial-scale=1" />
      <title>{E.txt title}</title>
      <link rel="stylesheet" href={looks} />
      <link rel="stylesheet" href={rules} />
    </head>
    {E.el (E.body (skip :: E.el (E.header (E.el (E.h1 [E.txt title]) :: contents)) ::
      E.el (E.main content [A.a_id "content"]) :: (pages ++ footer)))}
  </html>
/-- An item of the contents list: a link to a part of the page. Its address is data, so it is
written in markup, where an attribute takes a spliced value. -/
def tocItem (part : String × String) : Child tocCtx :=
  html! <li><a href={fragment part.1}>{E.txt part.2}</a></li>

/-- An item of the list of the site's pages: a link by its path from this page. -/
def siteItem (page : String × String) : Child siteCtx :=
  html! <li><a href={page.1}>{E.txt page.2}</a></li>

/-- A line of the provenance. -/
def noteItem (note : String) : Child noteCtx := html! <li>{E.txt note}</li>

/-- The page of a document: its content checked once, as the children of `main`, and the shell
around it. `site` is the other pages of the site, each by its path and its title. -/
def page (d : Document) (looks rules : String) (site : List (String × String) := []) :
    Except String (Element .html Ctx.document) :=
  match Child.acceptAll (ctx := mainCtx) (blocksNodes 2 d.body) with
  | .error words => .error ("HTML refused: " ++ words)
  | .ok content =>
    .ok (shell d.title looks rules ((tops d).map tocItem) content (site.map siteItem)
      (d.producer.map noteItem))

/-- The header again, with its items built in place and no position named: an `html!` term
reads its position from the combinator or the markup around it, here `E.ol` and `E.header`.
Only a position that a check names from outside, as `mainCtx` above, needs a name. The optional
part is the tail of a `::`, which hands its type down; the two sides of a `++` get none. The
binder of the item has its type written, since a splice is settled where it stands. -/
def headerInPlace (title : String) (parts : List (String × String)) : Element .header Ctx.flow :=
  E.header (E.el (E.h1 [E.txt title]) ::
    (if parts.isEmpty then [] else
      [html! <nav aria-label="Contents">{E.el (E.ol (parts.map fun (part : String × String) =>
        html! <li><a href={fragment part.1}>{E.txt part.2}</a></li>))}</nav>]))

/-! ## A sample -/

def sample : Document where
  title := "Semantics <1>"
  producer := ["lake exe docs", "commit 0000000"]
  body :=
    [.para [.text "Every claim has a ", .ref "status" "status", .text "."],
     .part "claims" "Claims"
       [.para [.text "A claim is ", .status "proved", .text " or ", .code "open", .text "."],
        .fields [("Owner", [.text "the kernel"]), ("Since", [.link "../history/" "the first slice"])],
        .part "status" "Status"
          [.items [[.status "proved"], [.status "modulo"], [.text "a & b"]],
           .code "lean" "theorem t : 1 = 1 := rfl",
           .code "mermaid" "graph TD; a-->b",
           .table ["Claim", "Status"] [[[.text "t"], [.status "proved"]]]]],
     .part "goals" "Goals" [.para [.text "None yet."]]]

def rendered (d : Document) (site : List (String × String) := []) : Option String :=
  match page d "../looks.css" "../page.css" site with
  | .ok tree => some tree.renderDoc
  | .error _ => none

def refused {α : Type} (result : Except String α) : Option String :=
  match result with
  | .ok _ => none
  | .error words => some words

-- The page renders, and it is the consumer's page: the typed shell around the checked content
-- writes the text that the raw tree writes, character for character.
#guard rendered sample == some (Print.renderDoc (rawPage sample "../looks.css" "../page.css"))

-- The same with nothing optional in it: no part, so no contents list, and no provenance.
#guard rendered { title := "Empty", body := [] } ==
  some (Print.renderDoc (rawPage { title := "Empty", body := [] } "../looks.css" "../page.css"))

-- The list of the site's pages is the shell's own: the consumer's page has none yet.
#guard ((rendered sample [("../", "Home"), ("../plan/", "Plan")]).map fun text =>
  (text.splitOn "<aside><nav aria-label=\"Pages\"><ul><li><a href=\"../\">Home</a></li><li><a href=\"../plan/\">Plan</a></li></ul></nav></aside>").length) == some 2

-- The header built in place writes the header of the page.
#guard (headerInPlace "T" [("a", "A"), ("b c", "B")]).render ==
  "<header><h1>T</h1><nav aria-label=\"Contents\"><ol><li><a href=\"#a\">A</a></li><li><a href=\"#b%20c\">B</a></li></ol></nav></header>"

/-! ## The typed page is the consumer's page, for every document -/

/-- The raw tree of the shell with no list of pages: the consumer's page, with the raw nodes of
the typed children where its lists stand. -/
theorem shell_toRaw (title looks rules : String) (toc : List (Child tocCtx))
    (content : List (Child mainCtx)) (notes : List (Child noteCtx)) :
    (shell title looks rules toc content [] notes).toRaw =
      el "html" [
        el "head" [
          el "meta" [] [("charset", "utf-8")],
          el "meta" [] [("name", "viewport"), ("content", "width=device-width, initial-scale=1")],
          el "title" [.text title],
          el "link" [] [("rel", "stylesheet"), ("href", looks)],
          el "link" [] [("rel", "stylesheet"), ("href", rules)]],
        el "body" ([
          el "a" [.text "Skip to the content"] [("class", "skip"), ("href", "#content")],
          el "header" ([el "h1" [.text title]] ++
            (if toc.isEmpty then [] else
              [el "nav" [el "ol" (toc.map Child.raw)] [("aria-label", "Contents")]])),
          el "main" (content.map Child.raw) [("id", "content")]] ++
          (if notes.isEmpty then [] else
            [el "footer" [el "p" [.text "Provenance"] [("class", "label")],
              el "ul" (notes.map Child.raw)]]))]
        [("lang", "en")] := by
  cases toc <;> cases notes <;> rfl

/-- For every document whose content the checker accepts, the typed page erases to the raw
tree that the consumer builds today. The guards above are two evaluations of this. It reads
`Child.acceptAll_eq_ok_iff`: the children of `main` are the nodes of the fold. -/
theorem page_toRaw (d : Document) (looks rules : String) {tree : Element .html Ctx.document}
    (h : page d looks rules = .ok tree) : tree.toRaw = rawPage d looks rules := by
  unfold page at h
  cases hcontent : Child.acceptAll (ctx := mainCtx) (blocksNodes 2 d.body) with
  | error words =>
    rw [hcontent] at h
    exact nomatch h
  | ok content =>
    rw [hcontent] at h
    cases Except.ok.inj h
    have htoc : ((tops d).map tocItem).map Child.raw =
        (tops d).map fun part => el "li" [el "a" [.text part.2] [("href", fragment part.1)]] := by
      rw [List.map_map]
      rfl
    have hnotes : (d.producer.map noteItem).map Child.raw =
        d.producer.map fun note => el "li" [.text note] := by
      rw [List.map_map]
      rfl
    refine (shell_toRaw d.title looks rules _ content _).trans ?_
    rw [htoc, hnotes, Child.acceptAll_eq_ok_iff.mp hcontent, List.isEmpty_map, List.isEmpty_map,
      rawPage]
    simp only [List.isEmpty_map]

/-! ## The consumer's own admission, since its typed shell

The admission function and `blocks` of `Tools.Site` of lean4-effect4 at `e04ea78a5`, on this
package's names. -/

/-- The consumer's words (`Tools.Document.Html.describe`): the element names along the path. -/
def consumerDescribe (tree : RawNode) (r : Refusal) : String :=
  let names := (List.range (r.path.length + 1)).filterMap fun k =>
    match tree.at? (r.path.take k) with
    | some (.element name _ _) => some name
    | _ => none
  "/" ++ "/".intercalate names ++ ": " ++ r.reason.describe

/-- `Tools.Site.blocks` as the consumer has it: each node admitted alone by its own function,
which is `Child.check`, and a refusal worded inside its node by its own `describe`. -/
def blocksTheirs {ctx : Ctx} (nodes : List RawNode) : Except String (List (Child ctx)) :=
  nodes.mapM fun node =>
    match Child.check node with
    | .ok c => .ok c
    | .error r => .error ("HTML refused: " ++ consumerDescribe node r)

/-- The same on the new interface: one call. -/
def blocks {ctx : Ctx} (nodes : List RawNode) : Except String (List (Child ctx)) :=
  match Child.acceptAll nodes with
  | .ok content => .ok content
  | .error words => .error ("HTML refused: " ++ words)

-- The two take the sample's content, and answer the same children: the nodes of the fold.
#guard ((blocksTheirs (ctx := mainCtx) (blocksNodes 2 sample.body)).toOption.map fun content =>
    content.map Child.raw == blocksNodes 2 sample.body) == some true
#guard ((blocks (ctx := mainCtx) (blocksNodes 2 sample.body)).toOption.map fun content =>
    content.map Child.raw == blocksNodes 2 sample.body) == some true

-- Where the content is refused, the consumer's words name elements, and the package's name the
-- part by its `id` and say what the position is.
#guard refused (blocksTheirs (ctx := mainCtx.child .a) ((blocksNodes 2 sample.body).drop 1)) ==
  some ("HTML refused: /section/h2/a: " ++ Reason.describe .notAdmitted)
#guard refused (blocks (ctx := mainCtx.child .a) ((blocksNodes 2 sample.body).drop 1)) ==
  some "HTML refused: /section#claims/h2/a: <a> is not admitted here: the context is phrasing, excluding interactive content, a"

-- The consumer's control (`Test/Audit/SiteControls.lean`): the content model refuses a block
-- where the shell's `main` would hold it.
#guard !(Child.check (ctx := mainCtx) (el "p" [el "div" []])).toBool

-- Reader of `Ctx.below_cons`: the short name of a position is the chain of `Ctx.child` that the
-- consumer writes (`InMain`).
example : mainCtx = Ctx.child (Ctx.child (Ctx.child Ctx.document .html) .body) .main := rfl

-- Reader of `Child.checkAll?_eq_mapM`: a list that `mapM` admits node by node is the list that
-- `checkAll?` answers, so its raw nodes are the nodes given.
example (nodes : List RawNode) (content : List (Child mainCtx))
    (h : nodes.mapM Child.check? = some content) : content.map Child.raw = nodes :=
  Child.checkAll?_eq_some_iff.mp ((Child.checkAll?_eq_mapM nodes).trans h)

/-! ## The laws, at the page's content -/

-- Reader of `Child.checkAll_eq_error_iff`: when the content of a page is refused, every block
-- before the refused one is good, so a report of the first refusal is a report of the first.
example (d : Document) (e : ListRefusal)
    (h : Child.checkAll (ctx := mainCtx) (blocksNodes 2 d.body) = .error e) :
    validAll mainCtx ((blocksNodes 2 d.body).take e.index) = true :=
  (Child.checkAll_eq_error_iff.mp h).1

-- Reader of `Child.toOption_check` and `Child.isSome_check?`: a node that `check` takes is one
-- the checker accepts, whatever the node is.
example (node : RawNode) (c : Child mainCtx) (h : Child.check node = .ok c) :
    validIn mainCtx node = true := by
  rw [← Child.isSome_check?, ← Child.toOption_check, h]
  rfl

/-! ## Controls: the same content where a position refuses it -/

-- Flow content where phrasing content is required: the blocks of the sample as the children
-- of a paragraph. The first block is refused, and the words name it and the position.
#guard refused (Child.acceptAll (ctx := mainCtx.child .p) (blocksNodes 2 sample.body)) ==
  some "/p: <p> is not admitted here: the context is phrasing"

-- The parts of the sample inside a link: a card that links to a page. A link holds no link,
-- and the first one stands in the heading of the first part. The path is of names: the part by
-- its `id`, its heading, the link.
#guard refused (Child.acceptAll (ctx := mainCtx.child .a) ((blocksNodes 2 sample.body).drop 1)) ==
  some "/section#claims/h2/a: <a> is not admitted here: the context is phrasing, excluding interactive content, a"

-- The first refusal is the one answered, with its place in the list: the second node here.
#guard (match Child.checkAll (ctx := mainCtx) [el "p" [], el "li" [], el "td" []] with
  | .error e => some (e.index, e.refusal.path, e.refusal.reason)
  | .ok _ => none) == some (1, [], .notAdmitted)

-- `check?`, `check` and `accept` agree on one tree: a figure is flow content, and no phrasing.
#guard (Child.check? (ctx := mainCtx) (el "figure" [])).isSome
#guard (Child.check? (ctx := mainCtx.child .p) (el "figure" [])).isNone
#guard refused (Child.accept (ctx := mainCtx.child .p) (el "figure" [])) ==
  some "/figure: <figure> is not admitted here: the context is phrasing"

end WhatwgTest.Html.UseCheck
