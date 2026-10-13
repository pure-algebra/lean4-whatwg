import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Syntax.Elaborator

/-!
# WhatwgTest.Html.SiteShell

The shell of lean4-effect4's documentation site (`tools/Tools/Site.lean`, read at `c1faac505`),
with each of its three workarounds written plainly (slice S17 of `docs/SVG-PACKAGE-PLAN.md`, its
second round; entries W8, W9 and W12 of `docs/research/2026-10-12-whatwg-requests.md`). This
module imports nothing of that package. The namespace `Theirs` restates the consumer's
definitions as they stand, and they elaborate unchanged on this round's tactic and markup
term. Beside each stands the plain form:

| The consumer's workaround | Written plainly |
| --- | --- |
| each link twice, with `aria-current` and without (`sectionItem`, `crumb`) | one markup, `aria-current={current}` with an `Option String` (W12) |
| the title twice, with its key and without (`heading`) | one markup: an `id` that may be absent and a child that may be absent |
| `head_attrs`, and `Child.of (head …) (by rw [head_attrs]; admits)` | `E.el (head …)` (W9) |
| the literal `⟨.aria_, "aria-label", "Pages"⟩` beside a list that is a variable | `A.aria_ "label" "Pages"` (W8) |

For each, a theorem says that the plain form erases to the raw node the consumer writes today,
for every argument. `render_toRaw` says it of the whole page. `renderMarkup` is the page once
more with every list and every absent part spliced in markup; a guard holds its text equal on
a sample, since a list spliced among other children erases to an append, which is the same
list and not the same term.

What this battery does not claim: that this is the consumer's file. Its fold, its checks and its
values are not restated, and no theorem relates this module to that package.
-/

namespace WhatwgTest.Html.SiteShell

open Whatwg.Html
open Whatwg.Html.Content (Ctx)

/-! ## The positions of the shell (the consumer's names) -/

abbrev InHtml := Ctx.child Ctx.document .html
abbrev InBody := Ctx.child InHtml .body
abbrev InMain := Ctx.child InBody .main
abbrev InSiteList := Ctx.child (Ctx.child (Ctx.child InBody .header) .nav) .ol
abbrev InCrumbs := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InPager := Ctx.child InMain .nav
abbrev InToc := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InFooterList := Ctx.child (Ctx.child InBody .footer) .ul

/-- Where a page's styles stand (`Tools.Site.Styles`). -/
inductive Styles where
  | files (looks rules : String)
  | inlineLooks (looks : String) (rules : String)

def fragment (key : String) : String := "#" ++ key

/-- What a page's shell holds beyond its document (`Tools.Site.Shell`). -/
structure Shell where
  tabTitle : String
  styles : Styles
  home : String
  key : Option String := none
  sections : List (Child InSiteList) := []
  crumbs : List (Child InCrumbs) := []
  toc : List (Child InToc) := []
  pager : List (Child InPager) := []
  footer : List (Child InFooterList) := []

/-- The head (`Tools.Site.head`): its ordered model is checked in each case, and its type names
its tag. It is the same in both forms. -/
def head (tabTitle : String) : Styles → Element .head InHtml
  | .files looks rules => html! <head><meta charset="utf-8" /><meta name="viewport" content="width=device-width, initial-scale=1" /><title>{E.txt tabTitle}</title><link rel="stylesheet" href={looks} /><link rel="stylesheet" href={rules} /></head>
  | .inlineLooks looks rules => html! <head><meta charset="utf-8" /><meta name="viewport" content="width=device-width, initial-scale=1" /><title>{E.txt tabTitle}</title><style>{E.txt looks}</style><link rel="stylesheet" href={rules} /></head>

/-! ## The consumer's definitions, as they stand -/

namespace Theirs

def sectionItem (href label : String) (current : Option String) : Child InSiteList :=
  match current with
  | some how => html! <li><a href={href} aria-current={how}>{E.txt label}</a></li>
  | none => html! <li><a href={href}>{E.txt label}</a></li>

def crumb (href label : String) (last : Bool) : Child InCrumbs :=
  if last then html! <li><a href={href} aria-current="page">{E.txt label}</a></li>
  else html! <li><a href={href}>{E.txt label}</a></li>

def heading (title : String) : Option String → Child InMain
  | some k => html! <h1 id={k}>{E.txt title}<a class="key" href={fragment k}>{E.txt k}</a></h1>
  | none => html! <h1>{E.txt title}</h1>

theorem head_attrs (tabTitle : String) (styles : Styles) : (head tabTitle styles).attrs = [] := by
  cases styles <;> rfl

def headChild (tabTitle : String) (styles : Styles) : Child InHtml :=
  Child.of (head tabTitle styles) (by rw [head_attrs]; admits)

def render (s : Shell) (title : String) (blocks : List (Child InMain)) : Element .html Ctx.document :=
  let header : Child InBody :=
    if s.sections.isEmpty then html! <header><a class="home" href={s.home}>"Effect4"</a></header>
    else html! <header><a class="home" href={s.home}>"Effect4"</a><nav aria-label="Site">{E.el (E.ol s.sections)}</nav></header>
  let toc : List (Child InMain) := if s.toc.isEmpty then [] else
    [html! <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">"On this page"</p>{E.el (E.ol s.toc)}</nav>]
  let crumbs : List (Child InMain) := if s.crumbs.isEmpty then [] else
    [html! <nav class="crumbs" aria-label="Breadcrumb">{E.el (E.ol s.crumbs)}</nav>]
  let pager : List (Child InMain) := if s.pager.isEmpty then [] else
    [E.el (E.nav s.pager [A.a_class "pager", ⟨.aria_, "aria-label", "Pages"⟩])]
  let footer : List (Child InBody) := if s.footer.isEmpty then [] else
    [html! <footer><p class="label">"Provenance"</p>{E.el (E.ul s.footer)}</footer>]
  let main : Child InBody := E.el (E.main (crumbs ++ [heading title s.key] ++ toc ++ blocks ++ pager) [A.a_id "content"])
  let body : Child InHtml := E.el (E.body ([html! <a class="skip" href="#content">"Skip to the content"</a>, header] ++
    [main] ++ footer))
  html! <html lang="en">{headChild s.tabTitle s.styles}{body}</html>

end Theirs

/-! ## Written plainly -/

/-- A section of the site's navigation: one markup, and the mark of the current one may be
absent. -/
def sectionItem (href label : String) (current : Option String) : Child InSiteList :=
  html! <li><a href={href} aria-current={current}>{E.txt label}</a></li>

/-- A breadcrumb: the last is the page itself. -/
def crumb (href label : String) (last : Bool) : Child InCrumbs :=
  html! <li><a href={href} aria-current={if last then some "page" else none}>{E.txt label}</a></li>

/-- The page's title, with the key of the part it was split from beside it when there is one:
an `id` that may be absent, and a child that may be absent. -/
def heading (title : String) (key : Option String) : Child InMain :=
  html! <h1 id={key}>{E.txt title}{key.map fun (k : String) =>
    html! <a class="key" href={fragment k}>{E.txt k}</a>}</h1>

/-- The page, as the consumer writes it, with the head placed by `E.el` and the name of the
pager's label computed by `A.aria_`. -/
def render (s : Shell) (title : String) (blocks : List (Child InMain)) : Element .html Ctx.document :=
  let header : Child InBody :=
    if s.sections.isEmpty then html! <header><a class="home" href={s.home}>"Effect4"</a></header>
    else html! <header><a class="home" href={s.home}>"Effect4"</a><nav aria-label="Site">{E.el (E.ol s.sections)}</nav></header>
  let toc : List (Child InMain) := if s.toc.isEmpty then [] else
    [html! <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">"On this page"</p>{E.el (E.ol s.toc)}</nav>]
  let crumbs : List (Child InMain) := if s.crumbs.isEmpty then [] else
    [html! <nav class="crumbs" aria-label="Breadcrumb">{E.el (E.ol s.crumbs)}</nav>]
  let pager : List (Child InMain) := if s.pager.isEmpty then [] else
    [E.el (E.nav s.pager [A.a_class "pager", A.aria_ "label" "Pages"])]
  let footer : List (Child InBody) := if s.footer.isEmpty then [] else
    [html! <footer><p class="label">"Provenance"</p>{E.el (E.ul s.footer)}</footer>]
  let main : Child InBody := E.el (E.main (crumbs ++ [heading title s.key] ++ toc ++ blocks ++ pager) [A.a_id "content"])
  let body : Child InHtml := E.el (E.body ([html! <a class="skip" href="#content">"Skip to the content"</a>, header] ++
    [main] ++ footer))
  html! <html lang="en">{E.el (head s.tabTitle s.styles)}{body}</html>

/-! ## The plain forms erase to what the consumer writes -/

theorem sectionItem_raw (href label : String) (current : Option String) :
    (sectionItem href label current).raw = (Theirs.sectionItem href label current).raw := by
  cases current <;> rfl

theorem crumb_raw (href label : String) (last : Bool) :
    (crumb href label last).raw = (Theirs.crumb href label last).raw := by
  cases last <;> rfl

theorem heading_raw (title : String) (key : Option String) :
    (heading title key).raw = (Theirs.heading title key).raw := by
  cases key <;> rfl

/-- The head placed by `E.el` is the head placed with the lemma about its attributes. -/
theorem headChild_raw (tabTitle : String) (styles : Styles) :
    (E.el (head tabTitle styles) : Child InHtml).raw = (Theirs.headChild tabTitle styles).raw := rfl

/-- The whole page: for every shell, title and list of blocks, the plain page erases to the
consumer's page. -/
theorem render_toRaw (s : Shell) (title : String) (blocks : List (Child InMain)) :
    (render s title blocks).toRaw = (Theirs.render s title blocks).toRaw := by
  obtain ⟨tabTitle, styles, home, key, sections, crumbs, toc, pager, footer⟩ := s
  cases key <;> cases pager <;> rfl

/-! ## The page once more, in markup throughout -/

/-- Every list and every part that may be absent is a splice: a list of children, a child that
may be absent, an attribute that may be absent. `html` and `head` keep their ordered models,
which read the two spliced elements. -/
def renderMarkup (s : Shell) (title : String) (blocks : List (Child InMain)) :
    Element .html Ctx.document :=
  let nav (present : Bool) (child : Child (Ctx.child InBody .header)) := if present then some child else none
  let part {ctx : Ctx} (present : Bool) (child : Child ctx) : Option (Child ctx) :=
    if present then some child else none
  let body : Element .body InHtml :=
    html! <body>
      <a class="skip" href="#content">"Skip to the content"</a>
      <header><a class="home" href={s.home}>"Effect4"</a>{nav (!s.sections.isEmpty)
        (html! <nav aria-label="Site"><ol>{s.sections}</ol></nav>)}</header>
      <main id="content">
        {part (!s.crumbs.isEmpty) (html! <nav class="crumbs" aria-label="Breadcrumb"><ol>{s.crumbs}</ol></nav>)}
        {heading title s.key}
        {part (!s.toc.isEmpty) (html! <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">"On this page"</p><ol>{s.toc}</ol></nav>)}
        {blocks}
        {part (!s.pager.isEmpty) (html! <nav class="pager" aria-label="Pages">{s.pager}</nav>)}
      </main>
      {part (!s.footer.isEmpty) (html! <footer><p class="label">"Provenance"</p><ul>{s.footer}</ul></footer>)}
    </body>
  html! <html lang="en">{E.el (head s.tabTitle s.styles)}{E.el body}</html>

/-! ## A sample -/

def sample : Shell where
  tabTitle := "Claims · Effect4"
  styles := .files "../looks.css" "../page.css"
  home := "../"
  key := some "claims"
  sections := [sectionItem "../semantics/" "Semantics" (some "true"), sectionItem "../plan/" "Plan" none]
  crumbs := [crumb "../" "Semantics" false, crumb "./" "Claims" true]
  toc := [html! <li><a href="#a">"A"</a></li>]
  pager := [html! <a rel="prev" href="../a/"><span class="label">"Previous"</span>"A"</a>]
  footer := [html! <li>"lake exe docs"</li>]

def bare : Shell where
  tabTitle := "Root"
  styles := .inlineLooks ":root{}" "page.css"
  home := "./"

def blocks : List (Child InMain) := [html! <p>"A claim is " <code>"open"</code>"."</p>]

-- The plain page writes the consumer's text, with everything in it and with nothing.
#guard (render sample "Claims" blocks).render == (Theirs.render sample "Claims" blocks).render
#guard (render bare "Root" []).render == (Theirs.render bare "Root" []).render

-- The page in markup throughout writes the same text.
#guard (renderMarkup sample "Claims" blocks).render == (Theirs.render sample "Claims" blocks).render
#guard (renderMarkup bare "Root" []).render == (Theirs.render bare "Root" []).render

-- What the marks are: the current section, the page's own breadcrumb, the title's key.
#guard (sectionItem "../plan/" "Plan" (some "page")).render ==
  "<li><a href=\"../plan/\" aria-current=\"page\">Plan</a></li>"
#guard (crumb "./" "Claims" false).render == "<li><a href=\"./\">Claims</a></li>"
#guard (heading "Claims" (some "claims")).render ==
  "<h1 id=\"claims\">Claims<a class=\"key\" href=\"#claims\">claims</a></h1>"
#guard (heading "Root" none).render == "<h1>Root</h1>"

end WhatwgTest.Html.SiteShell
