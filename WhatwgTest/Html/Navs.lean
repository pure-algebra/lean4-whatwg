import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Check
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Content.Site.Laws
import Whatwg.Html.Content.Structure
import Whatwg.Html.Node.Nav.Laws

/-!
# WhatwgTest.Html.Navs

The navigations of lean4-effect4's page, on `Whatwg/Html/Node/Nav.lean` (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entries W6, W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at `6ad8f7b8d`:

| The consumer's code, `tools/Tools/Site.lean` | Here |
| --- | --- |
| `sectionItem`, lines 252 to 255; `crumb`, lines 258 to 260; `pagerLink`, lines 263 to 265 | `Theirs.sectionItem`, `Theirs.crumb`, `Theirs.pagerLink`, word for word |
| the three `nav` elements of `render`, lines 320 to 328 | `Theirs.siteNav`, `Theirs.crumbsNav`, `Theirs.pagerNav`, word for word |
| `Site.shell`, lines 359 to 367: the sections with their marks, the crumbs, the neighbours | `sectionItems`, `crumbs`, `around`, on `Item.toSection`, `Site.linkTo` and `Item.toPage` |

For each a theorem says that the package's builder erases to the consumer's node, for every
argument. The consumer writes an item by cases and places it by a position named by hand; the
builders are written once for every position, and the three laws of
`Whatwg/Html/Node/Nav/Laws.lean` are read here at the consumer's shell: the current page is
marked once, and a navigation written from the paths of a sound site's pages holds no dead
link.

`site` below is a site of six pages whose trees are that shell. The pages and their titles are
this battery's; the shell is the consumer's, without its document, its styles and its footer.

What this battery does not claim: that this is the consumer's file. The consumer's crumbs are
found by a search of the site for each folder above the page, and are restated here only at
this site.
-/

namespace WhatwgTest.Html.Navs

open Whatwg.Html
open Whatwg.Html.Content (Ctx Site)
open Whatwg.Html.Content.Structure (places)

/-- The positions of the consumer's shell (`Tools.Site`, lines 234 to 240). -/
abbrev InHtml := Ctx.child Ctx.document .html
abbrev InBody := Ctx.child InHtml .body
abbrev InMain := Ctx.child InBody .main
abbrev InHeader := Ctx.child InBody .header
abbrev InSiteList := Ctx.child (Ctx.child InHeader .nav) .ol
abbrev InCrumbs := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InPager := Ctx.child InMain .nav

/-! ## The consumer's code -/

namespace Theirs

/-- A section of the site's navigation; the current one is marked. -/
def sectionItem (href label : String) (current : Option String) : Child InSiteList :=
  match current with
  | some how => html! <li><a href={href} aria-current={how}>{E.txt label}</a></li>
  | none => html! <li><a href={href}>{E.txt label}</a></li>

/-- A breadcrumb; the last is the page itself. -/
def crumb (href label : String) (last : Bool) : Child InCrumbs :=
  if last then html! <li><a href={href} aria-current="page">{E.txt label}</a></li>
  else html! <li><a href={href}>{E.txt label}</a></li>

/-- A link to a neighbouring page in reading order. -/
def pagerLink (rel href label : String) : Child InPager :=
  if rel == "prev" then html! <a rel="prev" href={href}><span class="label">"Previous"</span>{E.txt label}</a>
  else html! <a rel="next" href={href}><span class="label">"Next"</span>{E.txt label}</a>

/-- The sections in the header (`render`, line 321). -/
def siteNav (sections : List (Child InSiteList)) : Child InHeader :=
  html! <nav aria-label="Site">{E.el (E.ol sections)}</nav>

/-- The crumbs (`render`, line 325). -/
def crumbsNav (crumbs : List (Child InCrumbs)) : Child InMain :=
  html! <nav class="crumbs" aria-label="Breadcrumb">{E.el (E.ol crumbs)}</nav>

/-- The neighbours (`render`, line 328). -/
def pagerNav (pager : List (Child InPager)) : Child InMain :=
  E.el (E.nav pager [A.a_class "pager", ⟨.aria_, "aria-label", "Pages"⟩])

/-- The crumbs of a page, each with whether it is the last (`Site.shell`, line 364). -/
def crumbs (crumbs : List (String × String)) : List (Child InCrumbs) :=
  crumbs.zipIdx.map fun (c, k) => crumb c.1 c.2 (k + 1 == crumbs.length)

end Theirs

/-! ## The same on the package's builders -/

/-- The sections in the header. -/
def siteNav (sections : List Nav.Item) : Child InHeader := E.el (Nav.list (.label "Site") sections)

/-- The crumbs: the last is the page. -/
def crumbsNav (crumbs : List (String × String)) : Child InMain :=
  E.el (Nav.trail (.label "Breadcrumb") crumbs (some "crumbs"))

/-- The neighbours. -/
def pagerNav (previous next : Option Nav.Item) : Child InMain :=
  E.el (Nav.pager (.label "Pages") previous next ("Previous", "Next") (some "pager") (some "label"))

/-- An item is the consumer's section item, for every address, title and mark. -/
theorem sectionItem_raw (i : Nav.Item) :
    (Theirs.sectionItem i.href i.label i.current).raw = i.entryRaw := by
  obtain ⟨href, label, current⟩ := i
  cases current <;> rfl

/-- The sections erase to the consumer's node, for every list of items. -/
theorem siteNav_raw (items : List Nav.Item) :
    (siteNav items).raw =
      (Theirs.siteNav (items.map fun i => Theirs.sectionItem i.href i.label i.current)).raw := by
  have hmine : (siteNav items).raw = Nav.listRaw (.label "Site") items := Nav.list_toRaw _ _ _ _
  have htheirs : ∀ sections : List (Child InSiteList), (Theirs.siteNav sections).raw =
      .element "nav" [("aria-label", "Site")] [.element "ol" [] (sections.map Child.raw)] :=
    fun _ => rfl
  rw [hmine, htheirs, List.map_map]
  have hitems : (items.map (Child.raw ∘ fun i => Theirs.sectionItem i.href i.label i.current)) =
      items.map Nav.Item.entryRaw := List.map_congr_left fun i _ => sectionItem_raw i
  rw [hitems]
  rfl

/-- A trail's items are the consumer's crumbs, the last marked. -/
theorem trail_raw : ∀ (crumbs : List (String × String)) (start total : Nat),
    start + crumbs.length = total →
      (Nav.Item.trail crumbs).map Nav.Item.entryRaw =
        ((crumbs.zipIdx start).map fun (c, k) => Theirs.crumb c.1 c.2 (k + 1 == total)).map Child.raw
  | [], _, _, _ => rfl
  | [crumb], start, total, h => by
    have hlast : (start + 1 == total) = true := by
      rw [beq_iff_eq]
      exact h
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, hlast]
    rfl
  | crumb :: next :: rest, start, total, h => by
    have hnot : (start + 1 == total) = false := by
      rw [beq_eq_false_iff_ne]
      simp only [List.length_cons] at h
      omega
    have hrest := trail_raw (next :: rest) (start + 1) total (by simp only [List.length_cons] at h ⊢; omega)
    rw [Nav.Item.trail, List.map_cons, hrest]
    simp only [List.zipIdx_cons, List.map_cons, hnot]
    rfl

/-- The crumbs erase to the consumer's node, for every list of crumbs. -/
theorem crumbsNav_raw (crumbs : List (String × String)) :
    (crumbsNav crumbs).raw = (Theirs.crumbsNav (Theirs.crumbs crumbs)).raw := by
  have hmine : (crumbsNav crumbs).raw =
      Nav.listRaw (.label "Breadcrumb") (Nav.Item.trail crumbs) (some "crumbs") :=
    Nav.trail_toRaw _ _ _ _
  have htheirs : ∀ items : List (Child InCrumbs), (Theirs.crumbsNav items).raw =
      .element "nav" [("class", "crumbs"), ("aria-label", "Breadcrumb")]
        [.element "ol" [] (items.map Child.raw)] := fun _ => rfl
  rw [hmine, htheirs, Theirs.crumbs, ← trail_raw crumbs 0 crumbs.length (Nat.zero_add _)]
  rfl

/-- A link to a neighbour is the consumer's, before and after. -/
theorem pagerLink_raw (href label : String) :
    (Theirs.pagerLink "prev" href label).raw =
        Nav.turnRaw "prev" "Previous" ⟨href, label, none⟩ (some "label") ∧
      (Theirs.pagerLink "next" href label).raw =
        Nav.turnRaw "next" "Next" ⟨href, label, none⟩ (some "label") :=
  ⟨rfl, rfl⟩

/-- The neighbours erase to the consumer's node, whichever of the two there are. -/
theorem pagerNav_raw (previous next : Option (String × String)) :
    (pagerNav (previous.map fun q => ⟨q.1, q.2, none⟩) (next.map fun q => ⟨q.1, q.2, none⟩)).raw =
      (Theirs.pagerNav ((previous.map fun q => Theirs.pagerLink "prev" q.1 q.2).toList ++
        (next.map fun q => Theirs.pagerLink "next" q.1 q.2).toList)).raw := by
  cases previous <;> cases next <;> rfl

/-! ## A site whose pages are that shell -/

/-- A page as the shell reads it: where it stands and what it is called. -/
structure Page where
  path : List String
  title : String

/-- The pages in reading order, the root first. -/
def pages : List Page :=
  [⟨[], "Effect4"⟩, ⟨["semantics"], "Semantics"⟩, ⟨["semantics", "bind"], "Bind"⟩,
    ⟨["semantics", "pure"], "Pure"⟩, ⟨["plan"], "Plan"⟩, ⟨["contents"], "Contents"⟩]

/-- The sections: the pages one folder below the root (`Site.sections`, line 171), each with
its mark from the page at `here` (`Site.shell`, lines 359 to 361). -/
def sectionItems (here : List String) : List Nav.Item :=
  (pages.filter fun q => q.path.length == 1).map fun q => Nav.Item.toSection here (q.path, q.title)

/-- The crumbs: the page at each folder above the page, and the page (lines 362 to 364). -/
def crumbs (here : List String) : List (String × String) :=
  if here.length < 2 then []
  else (List.range here.length).filterMap fun k =>
    (pages.find? fun q => q.path == here.take (k + 1)).map fun q => (Site.linkTo here q.path, q.title)

/-- The page before and the page after in reading order (`Site.around`, lines 174 to 176). -/
def around (here : List String) : Option Page × Option Page :=
  let i := pages.findIdx fun q => q.path == here
  ((if i == 0 then none else pages[i - 1]?), pages[i + 1]?)

/-- The shell of a page: its head with the sheet at the root, the header with the sections, and
the content with the crumbs, the title and the neighbours. -/
def shell (p : Page) : Element .html Ctx.document :=
  let item (q : Page) : Nav.Item := Nav.Item.toPage p.path q.path q.title
  html! <html lang="en"><head><title>{E.txt p.title}</title><link rel="stylesheet" href={Site.linkToFile p.path [] "page.css"} /></head><body><header><a class="home" href={Site.linkTo p.path []}>"Effect4"</a>{siteNav (sectionItems p.path)}</header><main>{crumbsNav (crumbs p.path)}<h1>{E.txt p.title}</h1>{pagerNav ((around p.path).1.map item) ((around p.path).2.map item)}</main></body></html>

/-- The site: its pages, and the sheet at its root. -/
def site : Site := { pages := pages.map fun p => ⟨p.path, (shell p).toRaw⟩, files := [["page.css"]] }

-- Every link of every page's shell leads to a page or to the sheet: the site has no error.
#guard (Site.errors site).isEmpty

-- Control: the sheet is a file of the site. Without it in the list, each of the six pages has
-- a link that leads nowhere.
#guard (Site.errors { site with files := [] }).length == 6

-- The current page is marked once on every page but the root, which is no section and has no
-- crumbs: by its section when it is one, and by its last crumb below that.
#guard (pages.map fun p => (places Nav.pageMark (shell p).toRaw).length) == [0, 1, 1, 1, 1, 1]

-- A page two folders down: its section is current and is not the page; its last crumb is.
#guard ((sectionItems ["semantics", "bind"]).map fun i => i.current) == [some "true", none, none]
#guard Print.render (crumbsNav (crumbs ["semantics", "bind"])).raw ==
  "<nav class=\"crumbs\" aria-label=\"Breadcrumb\"><ol><li><a href=\"../\">Semantics</a></li>" ++
    "<li><a href=\"./\" aria-current=\"page\">Bind</a></li></ol></nav>"
#guard Print.render (siteNav (sectionItems ["semantics"])).raw ==
  "<nav aria-label=\"Site\"><ol><li><a href=\"./\" aria-current=\"page\">Semantics</a></li>" ++
    "<li><a href=\"../plan/\">Plan</a></li><li><a href=\"../contents/\">Contents</a></li></ol></nav>"
#guard Print.render (pagerNav ((around ["plan"]).1.map fun q => Nav.Item.toPage ["plan"] q.path q.title) none).raw ==
  "<nav class=\"pager\" aria-label=\"Pages\"><a rel=\"prev\" href=\"../semantics/pure/\">" ++
    "<span class=\"label\">Previous</span>Pure</a></nav>"

/-! ## Readers of the laws -/

/-- Reader of `list_leads`, `Item.leads_toPage` and `Sound.at?_eq`: **a navigation written from
the pages of a sound site holds no dead link**, from every page, whichever pages are chosen and
whatever they are called. The names of the paths are plain. -/
theorem sections_lead {s : Site} (hs : s.Sound)
    (hplain : ∀ q ∈ s.pages, q.path.all Site.plain = true) (title : Site.Page → String)
    (here : List String) {chosen : List Site.Page} (hchosen : ∀ q ∈ chosen, q ∈ s.pages) :
    ∀ a ∈ Content.Document.hrefsAt .html
        (Nav.listRaw (.label "Site") (chosen.map fun q => Nav.Item.toSection here (q.path, title q))),
      s.faultOf here a = none :=
  Nav.list_leads
    (fun i hi => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      exact Nav.Item.leads_toPage (hs.at?_eq (hchosen q hq)) (hplain q (hchosen q hq)) here _ _)
    _ _

/-- Reader of `trail_leads` and `Item.leads_toPage`: the crumbs written from the pages of a
sound site hold no dead link, from every page. -/
theorem crumbs_lead {s : Site} (hs : s.Sound)
    (hplain : ∀ q ∈ s.pages, q.path.all Site.plain = true) (title : Site.Page → String)
    (here : List String) {chosen : List Site.Page} (hchosen : ∀ q ∈ chosen, q ∈ s.pages) :
    ∀ a ∈ Content.Document.hrefsAt .html
        (Nav.listRaw (.label "Breadcrumb")
          (Nav.Item.trail (chosen.map fun q => (Site.linkTo here q.path, title q))) (some "crumbs")),
      s.faultOf here a = none :=
  Nav.trail_leads
    (fun crumb hcrumb => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcrumb
      exact Nav.Item.leads_toPage (hs.at?_eq (hchosen q hq)) (hplain q (hchosen q hq)) here _ none)
    _ _

/-- Reader of `places_trail`: the consumer's crumbs mark the current page once, at the last
crumb, for every list of at least one crumb. -/
theorem crumbs_mark_once (crumbs : List (String × String)) (h : crumbs ≠ []) :
    places Nav.pageMark (crumbsNav crumbs).raw = [[0, crumbs.length - 1, 0]] := by
  have hraw : (crumbsNav crumbs).raw =
      Nav.listRaw (.label "Breadcrumb") (Nav.Item.trail crumbs) (some "crumbs") :=
    Nav.trail_toRaw _ _ _ _
  rw [hraw]
  exact Nav.places_trail _ crumbs _ h

-- Reader of `pages_toSection_le` and `places_listRaw`: among sections at distinct paths, at
-- most one link of the navigation is the current page.
example (here : List String) (targets : List (List String × String))
    (h : (targets.map (·.1)).Nodup) :
    (places Nav.pageMark
      (Nav.listRaw (.label "Site") (targets.map (Nav.Item.toSection here)))).length ≤ 1 := by
  rw [Nav.places_listRaw, List.length_map]
  exact Nav.pages_toSection_le here targets 0 h

-- Reader of `link_in_list` and `link_in_pager`: a shell written for every position owes one
-- test of the position, and passes it on.
example {ctx : Ctx} (h : Nav.takesLinks ctx = true) (items : List Nav.Item)
    (previous next : Option Nav.Item) : Element .nav ctx × Element .nav ctx :=
  (Nav.list (.label "Site") items none (Nav.link_in_list h),
    Nav.pager (.label "Pages") previous next ("Previous", "Next") none none (Nav.link_in_pager h))

/-! ## Controls -/

-- Control: below a `button` no link may stand, and the builder is refused where it is used.
/--
error: could not synthesize default value for parameter 'hlink' using tactics
---
error: Tactic `decide` proved that the proposition
  ((((Ctx.flow.child Schema.Tag.button).child Schema.Tag.nav).child Schema.Tag.ol).child Schema.Tag.li).admits
      Schema.Tag.a =
    true
is false
-/
#guard_msgs in
example (items : List Nav.Item) : Element .nav (Ctx.flow.child .button) :=
  Nav.list (.label "Site") items

-- Control: the test of the position is false there, and true in the consumer's header.
#guard !Nav.takesLinks (Ctx.flow.child .button)
#guard Nav.takesLinks InHeader

-- Control: a link to a page that the site does not hold is found by the site's check. The law
-- asks that a page stand at the path, and this is why.
#guard !(Site.errors { pages := [⟨[], Nav.listRaw (.label "Site") [Nav.Item.toPage [] ["missing"] "Missing"]⟩] }).isEmpty

-- Control: an item whose `href` is a fragment holds no address: it is a reference to the page
-- itself, which the check of a document judges.
#guard (Content.Document.hrefsAt .html (Nav.listRaw (.label "Parts") [⟨"#part", "Part", none⟩])).isEmpty

end WhatwgTest.Html.Navs
