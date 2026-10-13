import Whatwg.Html.Node.Region
import Whatwg.Html.Node.Check
import Whatwg.Html.Content.Structure

/-!
# WhatwgTest.Html.SheetFacts

The structural facts that the rules of lean4-effect4's page draw, as values of
`Whatwg/Html/Content/Structure.lean` (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; the HTML half of
entry W14 of `docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at
`6ad8f7b8d`:

- `tools/Tools/Document/page.css`, lines 37 to 170: each rule has a comment that names the fact
  it draws. `rules` below is that sheet's selectors, each beside the fact it names. The selector
  is kept as text, for a reader and for the seat that will print a selector from a fact; nothing
  here reads it. Four facts are wider or narrower than the selector beside them, and the
  difference is the point of naming the fact: `Fact.region` is the element with `role` and
  `tabindex` where the sheet writes the class `.scroll`; `Fact.rowHead` is the first cell of a
  row, a `th` too; `Fact.caption` and `Fact.summary` ask for their parent.
- `tools/Tools/Document/Html.lean`, `algebra`, and `tools/Tools/Site.lean`, `render`: the nodes
  of a page. `page` below is a small page of those nodes: a part with a paragraph, a table in
  its region, a block of code, the three navigations and the footer.

`PageFact` is the consumer's own vocabulary: what its sheet draws that the package does not
name (a status, a part's key, a label, the pager). A fact of the sheet is a fact of the package
or one of these: the sum of the two vocabularies.

What this battery does not claim: that a selector of `rules` selects the elements of its
fact. That is the theorem of the CSS side, and Selectors is not sealed. The texts are the
consumer's, and the facts beside them were chosen by reading its comments.
-/

namespace WhatwgTest.Html.SheetFacts

open Whatwg.Html
open Whatwg.Html.Content (Ctx validIn)
open Whatwg.Html.Content.Structure

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-! ## The consumer's vocabulary -/

/-- What the consumer's sheet draws beyond the package's facts. -/
inductive PageFact where
  /-- A status of a claim, by its word (`.status[data-status=…]`). -/
  | status (word : String)
  /-- Any status. -/
  | anyStatus
  /-- A part's key beside its title. -/
  | key
  /-- A label: a name of a kind of thing. -/
  | label
  /-- A heading. -/
  | title
  /-- The heading of a part at the top of the page: its rule is the part's boundary. -/
  | topPart
  /-- Prose, held to its measure. -/
  | prose
  /-- The list of a navigation. -/
  | navList
  /-- The parts of the page, beside the content. -/
  | contents
  /-- A crumb after the first: a separator stands before it. -/
  | laterCrumb
  /-- The link to the next page. -/
  | pagerNext
  /-- Code in a cell of a table. -/
  | cellCode
  /-- The line of the footer before its last: a gap stands above it. -/
  | footerGap
  deriving DecidableEq, Repr

def PageFact.place : PageFact → Where
  | .status word => .here (.and (.classed "status") (.valued "data-status" word))
  | .anyStatus => .here (.classed "status")
  | .key => .here (.classed "key")
  | .label => .here (.or (.classed "label") (.or (.named "dt") (.named "summary")))
  | .title => .here heading
  | .topPart => .under (.here (.named "section")) (.named "h2")
  | .prose => .here (Test.oneOf ["p", "dd", "li", "figcaption"])
  | .navList => .inside (.here (.named "nav")) (.named "ol")
  | .contents => .under (.here (.named "main")) (.classed "toc")
  | .laterCrumb => .inside (.here (.classed "crumbs")) (.and (.named "li") (.not .first))
  | .pagerNext => .inside (.here (.classed "pager")) (.and (.named "a") (.valued "rel" "next"))
  | .cellCode => .inside (.here (.named "td")) (.named "code")
  | .footerGap => .inside (.here (.named "footer")) (.and (.named "li") (.nthLast 2))

instance : Vocabulary PageFact := ⟨PageFact.place⟩

/-- A fact of the sheet: the package's, or the consumer's. -/
abbrev SheetFact := Fact ⊕ PageFact

/-- The rules of `page.css` that draw structure, each as the fact its comment names, with the
selector the consumer writes today. A rule of a state (`:hover`, `:focus`, `:target`), a rule
of the whole page (`*`, `body`, `:root`) and the faces are no facts of a tree, and are left
out. -/
def rules : List (SheetFact × String) :=
  [(.inl .pageHeader, "body > header"), (.inl .pageFooter, "body > footer"),
    (.inl .main, "body > main"), (.inr .contents, "main > .toc"),
    (.inr .label, ".label, dt, summary"), (.inr .navList, "nav ol"),
    (.inl .current, "[aria-current]"), (.inl .currentPage, "[aria-current=page]"),
    (.inr .laterCrumb, ".crumbs li + li::before"), (.inr .pagerNext, ".pager a[rel=next]"),
    (.inr .title, "h1, h2, h3, h4, h5, h6"), (.inr .topPart, "section > h2"),
    (.inr .key, ".key"), (.inr .prose, "p, dd, li, figcaption"),
    (.inl .codeSpan, ":not(pre) > code"), (.inl .block, "pre"), (.inl .region, ".scroll"),
    (.inl .tableHead, "th"), (.inl .bodyCell, "tbody td"), (.inl .rowHead, "td:first-child"),
    (.inr .cellCode, "td code"), (.inr .anyStatus, ".status"),
    (.inr (.status "proved"), ".status[data-status=proved]::before"),
    (.inr (.status "open"), ".status[data-status=open]::before"),
    (.inl .caption, "figcaption"), (.inl .summary, "details.statement > summary"),
    (.inr .footerGap, "footer li:nth-last-child(2)")]

def facts : List SheetFact := rules.map (·.1)

/-! ## A page of the consumer's nodes -/

/-- A status (`inline`, the case `status`). -/
def status (word : String) : RawNode :=
  el "span" [.text word] [("class", "status"), ("data-status", word)]

/-- A part (`algebra.part`): a `section` with its heading and its key. -/
def part (key title : String) (body : List RawNode) : RawNode :=
  el "section" (el "h2" [.text title, el "a" [.text key] [("class", "key"), ("href", "#" ++ key)]] :: body)
    [("id", key)]

/-- A table in its region (`algebra.table`), on the package's region. -/
def table : RawNode :=
  regionRaw (.label "Table: claim, status")
    [el "table" [
      el "thead" [el "tr" [el "th" [.text "claim"] [("scope", "col")], el "th" [.text "status"] [("scope", "col")]]],
      el "tbody" [
        el "tr" [el "td" [el "code" [.text "keys-once"]], el "td" [status "proved"]],
        el "tr" [el "td" [el "code" [.text "descent"]], el "td" [status "open"]]]]]
    (some "scroll")

def crumb (href label : String) (current : Option String) : RawNode :=
  el "li" [el "a" [.text label] ([("href", href)] ++ (current.map fun how => ("aria-current", how)).toList)]

/-- A page: the shell of `Tools.Site.render` around three blocks. -/
def page : RawNode :=
  el "html" [
    el "head" [el "title" [.text "Claims"]],
    el "body" [
      el "header" [el "a" [.text "Effect4"] [("class", "home"), ("href", "../")],
        el "nav" [el "ol" [crumb "../semantics/" "Semantics" (some "true"), crumb "../plan/" "Plan" none]]
          [("aria-label", "Site")]],
      el "main" [
        el "nav" [el "ol" [crumb "../" "Semantics" none, crumb "./" "Claims" (some "page")]]
          [("class", "crumbs"), ("aria-label", "Breadcrumb")],
        el "h1" [.text "Claims"],
        el "nav" [el "p" [.text "On this page"] [("id", "toc-label"), ("class", "label")],
            el "ol" [el "li" [el "a" [.text "Every claim"] [("href", "#claims")]]]]
          [("class", "toc"), ("aria-labelledby", "toc-label")],
        part "claims" "Every claim" [
          el "p" [.text "A claim is ", status "proved", .text " or ", el "code" [.text "open"], .text "."],
          table,
          el "pre" [el "code" [.text "theorem keys_once : True"] [("class", "language-lean")]]],
        el "nav" [el "a" [.text "Plan"] [("rel", "next"), ("href", "../plan/")]]
          [("class", "pager"), ("aria-label", "Pages")]]
        [("id", "content")],
      el "footer" [el "p" [.text "Provenance"] [("class", "label")],
        el "ul" [el "li" [.text "lake exe docs"], el "li" [.text "This page as data"],
          el "li" [.text "Every page"]]]]]
    [("lang", "en")]

-- The page is one the checker accepts.
#guard validIn Ctx.document page

/-! ## What the page shows -/

-- Every rule of the sheet draws something on this page but two: the page has no figure and no
-- `details`. A rule that draws nothing is found, not reviewed.
#guard unused facts [page] == [.inl .caption, .inl .summary]

-- A page with a figure in words shows those two as well.
def figure : RawNode :=
  Region.figureRaw "plan" [el "svg" []] [.text "The plan"] (some ("The figure in words", [el "p" [.text "x"]]))

#guard unused facts [page, figure] == []

-- The places are paths of the tree, in tree order: the two header cells, then the first cell
-- of each row, the head's too.
#guard placesOfFact (Fact.tableHead) page == [[1, 1, 3, 2, 0, 0, 0, 0], [1, 1, 3, 2, 0, 0, 0, 1]]
#guard placesOfFact (Fact.rowHead) page ==
  [[1, 1, 3, 2, 0, 0, 0, 0], [1, 1, 3, 2, 0, 1, 0, 0], [1, 1, 3, 2, 0, 1, 1, 0]]
#guard (placesOfFact (Fact.rowHead) page).map (Content.Document.trail page) ==
  ["html/body[1]/main[1]/section[3]/div[2]/table[0]/thead[0]/tr[0]/th[0]",
    "html/body[1]/main[1]/section[3]/div[2]/table[0]/tbody[1]/tr[0]/td[0]",
    "html/body[1]/main[1]/section[3]/div[2]/table[0]/tbody[1]/tr[1]/td[0]"]

-- A place reads what stands above an element: code in a line is the `code` of the paragraph
-- and of the two cells, and the `code` of the block is the other fact.
#guard placesOfFact (Fact.codeSpan) page ==
  [[1, 1, 3, 1, 3], [1, 1, 3, 2, 0, 1, 0, 0, 0], [1, 1, 3, 2, 0, 1, 1, 0, 0]]
#guard placesOfFact (Fact.codeBlock) page == [[1, 1, 3, 3, 0]]

-- A place reads what stands beside an element: the second crumb and not the first, and the
-- line of the footer before its last.
#guard placesOfFact (PageFact.laterCrumb) page == [[1, 1, 0, 0, 1]]
#guard placesOfFact (PageFact.footerGap) page == [[1, 2, 1, 1]]

-- The current section and the current page are two facts; the page is one of the two places.
#guard placesOfFact (Fact.current) page == [[1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 1, 0]]
#guard placesOfFact (Fact.currentPage) page == [[1, 1, 0, 0, 1, 0]]

-- A status by its word.
#guard (placesOfFact (PageFact.status "proved") page).length == 2
#guard (placesOfFact (PageFact.status "refuted") page).length == 0

/-! ## Readers of the laws -/

/-- Reader of `mem_places_iff`: the region that the package builds shows the fact `region`,
for every name, every class and every content. What a builder makes, a sheet can name. -/
theorem region_shows (name : Region.Name) (children : List RawNode) (className : Option String) :
    [] ∈ places (Vocabulary.place Fact.region) (regionRaw name children className) := by
  rw [mem_places_iff]
  refine ⟨_, rfl, ?_⟩
  cases name <;> cases className <;> rfl

-- Reader of `mem_places_and`: a status of a word is a status, and has the word.
example (path : List Nat) :
    path ∈ placesOfFact (PageFact.status "proved") page ↔
      path ∈ places (.here (.classed "status")) page ∧
        path ∈ places (.here (.valued "data-status" "proved")) page :=
  mem_places_and _ _ page path

-- Reader of `occurs_of_mem_unused`: a fact that `unused` answers is shown by no tree given.
example (fact : SheetFact) (h : fact ∈ unused facts [page]) :
    occurs (Vocabulary.place fact) page = false :=
  occurs_of_mem_unused h List.mem_cons_self

-- Reader of `mem_placesAmong_iff`: a place in a list of trees is a place in one of them, read
-- with the elements beside it. The same item is the first of its list or not, by what stands
-- before it.
#guard placesAll (.here (.and (.named "li") .first)) [el "li" [], el "li" []] == [[0]]
#guard placesAll (.here (.and (.named "li") (.nthLast 1))) [el "li" [], .text " ", el "li" []] == [[2]]

/-! ## Controls -/

-- A text and a comment are no elements: they are not counted among the elements beside one.
#guard placesAll (.here .first) [.comment "c", .text "t", el "p" []] == [[2]]

-- `inside` is anywhere above, and `under` is the parent alone.
#guard placesAll (.inside (.here (.named "nav")) (.named "a")) [el "nav" [el "ol" [el "li" [el "a" []]]]] ==
  [[0, 0, 0, 0]]
#guard placesAll (.under (.here (.named "nav")) (.named "a")) [el "nav" [el "ol" [el "li" [el "a" []]]]] == []

-- A token of `class` is one of several, and no part of another token.
#guard placesAll (.here (.classed "toc")) [el "nav" [] [("class", "label toc")], el "nav" [] [("class", "toctree")]] ==
  [[0]]

end WhatwgTest.Html.SheetFacts
