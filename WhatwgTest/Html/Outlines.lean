import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Check
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Content.Document.Laws
import Whatwg.Html.Node.Outline.Laws

/-!
# WhatwgTest.Html.Outlines

The parts of lean4-effect4's page ("On this page"), on `Whatwg/Html/Node/Outline.lean` (slice
S22 of `docs/SVG-PACKAGE-PLAN.md`; entries W9 and W13 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at `6ad8f7b8d`:

| The consumer's code | Here |
| --- | --- |
| `tocSub`, `tocItem`, `tools/Tools/Site.lean`, lines 267 to 272 | `Theirs.tocSub`, `Theirs.tocItem`, word for word |
| the `nav` of the parts in `render`, lines 322 and 323 | `Theirs.toc`, word for word |
| `parts`, lines 142 and 143: a page's parts and their sub-parts, as data | `entry`: one part of that list as an `Outline.Entry` |
| `Html.fragment`, `tools/Tools/Document/Html.lean`, lines 45 to 51 | `Theirs.fragment`, word for word |

`contents_raw` says that the package's list, given the consumer's writer of fragments, erases to
the consumer's node for every list of parts. The consumer writes two levels by two functions
and two named positions; the builder is one recursion for every depth and every position.

The law of `Whatwg/Html/Node/Outline/Laws.lean` is read at the consumer's title: the list names
the parts that the page has. With the default writer that is a theorem (`contents_names`). The
consumer's writer percent-encodes, and that it is read back is evaluated here at keys of its
kinds, not proved.

What this battery does not claim: that this is the consumer's file. Its fold of a document into
`parts` is not restated.
-/

namespace WhatwgTest.Html.Outlines

open Whatwg.Html
open Whatwg.Html.Content (Ctx)
open Whatwg.Html.Content.Document (linksAt namesAt)

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- The positions of the consumer's shell (`Tools.Site`, lines 234 to 242). -/
abbrev InMain : Ctx := Ctx.document.below [.html, .body, .main]
abbrev InToc := Ctx.child (Ctx.child InMain .nav) .ol
abbrev InTocSub := Ctx.child (Ctx.child InToc .li) .ol

/-! ## The consumer's code -/

namespace Theirs

/-- A fragment identifier for a key: its UTF-8 bytes, a byte outside the URL fragment's safe
characters percent-encoded. -/
def fragment (key : String) : String :=
  "#" ++ String.join (key.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || "-._~:@!$'()*+,;=/?".contains c) then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 b.toNat)
      "%" ++ (if digits.length == 1 then "0" ++ digits else digits).toUpper)

def tocSub (k t : String) : Child InTocSub := html! <li><a href={fragment k}>{E.txt t}</a></li>

/-- A part of the page, with its own parts below it. -/
def tocItem (k t : String) (sub : List (String × String)) : Child InToc :=
  if sub.isEmpty then html! <li><a href={fragment k}>{E.txt t}</a></li>
  else html! <li><a href={fragment k}>{E.txt t}</a>{E.el (E.ol (sub.map fun (k, t) => tocSub k t))}</li>

/-- The parts of the page (`render`, lines 322 and 323). -/
def toc (items : List (Child InToc)) : Child InMain :=
  html! <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">"On this page"</p>{E.el (E.ol items)}</nav>

end Theirs

/-! ## The same on the package's builder -/

/-- A part of the consumer's page (`parts`: its key, its title, its sub-parts) as an entry. -/
def entry (part : String × String × List (String × String)) : Outline.Entry :=
  .mk part.1 part.2.1 (part.2.2.map fun sub => .mk sub.1 sub.2 [])

/-- The title of the consumer's list: a line above it, which the `nav` names. -/
def title : Outline.Title := .shown "toc-label" "On this page" (some "label")

/-- The parts of the page. -/
def contents (parts : List (String × String × List (String × String))) : Child InMain :=
  E.el (Outline.contents title (parts.map entry) Theirs.fragment (some "toc"))

theorem subs_raw : ∀ sub : List (String × String),
    (sub.map fun (k, t) => Theirs.tocSub k t).map Child.raw =
      Outline.rawAll Theirs.fragment (sub.map fun sub => .mk sub.1 sub.2 [])
  | [] => rfl
  | part :: rest => by
    rw [List.map_cons, List.map_cons, List.map_cons, Outline.rawAll, subs_raw rest]
    rfl

/-- An entry is the consumer's item, for every key, title and list of sub-parts. -/
theorem tocItem_raw (part : String × String × List (String × String)) :
    (Theirs.tocItem part.1 part.2.1 part.2.2).raw = (entry part).raw Theirs.fragment := by
  obtain ⟨k, t, sub⟩ := part
  cases sub with
  | nil => rfl
  | cons first rest =>
    have hsubs := subs_raw (first :: rest)
    have htheirs : (Theirs.tocItem k t (first :: rest)).raw =
        el "li" [el "a" [.text t] [("href", Theirs.fragment k)],
          el "ol" (((first :: rest).map fun (k, t) => Theirs.tocSub k t).map Child.raw)] := rfl
    have hmine : (entry (k, t, first :: rest)).raw Theirs.fragment =
        el "li" [el "a" [.text t] [("href", Theirs.fragment k)],
          el "ol" (Outline.rawAll Theirs.fragment ((first :: rest).map fun sub => .mk sub.1 sub.2 []))] := by
      rw [entry, Outline.Entry.raw]
      rfl
    rw [htheirs, hmine, hsubs]

theorem items_raw : ∀ parts : List (String × String × List (String × String)),
    (parts.map fun part => Theirs.tocItem part.1 part.2.1 part.2.2).map Child.raw =
      Outline.rawAll Theirs.fragment (parts.map entry)
  | [] => rfl
  | part :: rest => by
    rw [List.map_cons, List.map_cons, List.map_cons, Outline.rawAll, tocItem_raw part, items_raw rest]

/-- **The contents list erases to the consumer's node**, for every list of parts. -/
theorem contents_raw (parts : List (String × String × List (String × String))) :
    (contents parts).raw =
      (Theirs.toc (parts.map fun part => Theirs.tocItem part.1 part.2.1 part.2.2)).raw := by
  have hmine : (contents parts).raw =
      Outline.contentsRaw title (parts.map entry) Theirs.fragment (some "toc") :=
    Outline.contents_toRaw _ _ _ _ _
  have htheirs : ∀ items : List (Child InToc), (Theirs.toc items).raw =
      el "nav" [el "p" [.text "On this page"] [("id", "toc-label"), ("class", "label")],
          el "ol" (items.map Child.raw)]
        [("class", "toc"), ("aria-labelledby", "toc-label")] := fun _ => rfl
  rw [hmine, htheirs, items_raw]
  rfl

/-! ## A page with its parts -/

/-- A part as the consumer's fold writes it (`algebra.part`): a `section` with the key as its
identifier, and its heading. -/
def part (level : String) (key heading : String) (body : List RawNode) : RawNode :=
  el "section" (el level [.text heading] :: body) [("id", key)]

/-- The parts of a page, as the consumer's `parts` gives them: a key with a colon, a key with a
space and a letter outside ASCII, and a part with two of its own. -/
def parts : List (String × String × List (String × String)) :=
  [("claim:keys-once", "Keys once", []), ("Größe und Maß", "Size", []),
    ("plan", "The plan", [("plan.goals", "Goals"), ("plan.debts", "Debts")])]

/-- The page: its title, its contents, and the three parts. -/
def page (list : RawNode) : RawNode :=
  el "html" [el "head" [el "title" [.text "A page"]],
    el "body" [el "main" [el "h1" [.text "A page"], list,
      part "h2" "claim:keys-once" "Keys once" [], part "h2" "Größe und Maß" "Size" [],
      part "h2" "plan" "The plan" [part "h3" "plan.goals" "Goals" [], part "h3" "plan.debts" "Debts" []]]]]

-- The consumer's list on the consumer's page: no link names nothing, though an identifier
-- with a space is refused by the rule of identifiers (the consumer's own check refuses the key).
#guard (Content.Document.errors (page (contents parts).raw)).map (·.describe) ==
  ["the identifier `Größe und Maß` holds white space: at the child path [1, 0, 3]"]

-- The list in the order of the page, and its text for the part that has parts.
#guard Outline.ids (parts.map entry) == ["claim:keys-once", "Größe und Maß", "plan", "plan.goals", "plan.debts"]
#guard Print.render ((entry ("plan", "The plan", [("plan.goals", "Goals")])).raw Theirs.fragment) ==
  "<li><a href=\"#plan\">The plan</a><ol><li><a href=\"#plan.goals\">Goals</a></li></ol></li>"

-- The consumer's writer of fragments is read back at these keys: finite, not a theorem. The
-- key with a space and a letter outside ASCII is written with escapes, and found after decoding.
#guard Theirs.fragment "Größe und Maß" == "#Gr%C3%B6%C3%9Fe%20und%20Ma%C3%9F"
#guard (Outline.ids (parts.map entry)).all fun id =>
  (Outline.refsOf Theirs.fragment id).all fun r => r.namesBy (· == id)

-- Three levels, which the consumer's two functions do not write: one recursion, at a position
-- that is written once.
#guard Print.render (Outline.contents (ctx := InMain) (.hidden "Contents")
    [.mk "a" "A" [.mk "b" "B" [.mk "c" "C" []]]]).toRaw ==
  "<nav aria-label=\"Contents\"><ol><li><a href=\"#a\">A</a><ol><li><a href=\"#b\">B</a><ol><li>" ++
    "<a href=\"#c\">C</a></li></ol></li></ol></li></ol></nav>"

/-! ## Readers of the laws -/

/-- Reader of `contents_closed`, `readsBack_plainHref` and `title_refs_of_idOk`: **the
consumer's list names what the page has**, for every outline: where the page's identifiers
hold those of the outline and the title's, no reference of the list is dangling. -/
theorem contents_names (entries : List Outline.Entry) {names : List String}
    (hparts : ∀ id ∈ Outline.ids entries, id ∈ names) (htitle : "toc-label" ∈ names) :
    ∀ r ∈ linksAt .html (Outline.contentsRaw title entries Outline.plainHref (some "toc")),
      r.NamesIn names :=
  Outline.contents_closed title entries Outline.readsBack_plainHref _
    (fun r hr => by
      have hown := Outline.title_refs_of_idOk (title := title)
        (fun id hid => by rw [List.mem_singleton.mp hid]; decide) r hr
      rw [List.mem_singleton.mp hown]
      exact htitle)
    hparts

-- Reader of `linksAt_contentsRaw_plain`: the links of a list are the identifiers of the
-- outline, in the order of the page.
example (entries : List Outline.Entry) :
    (linksAt .html (Outline.contentsRaw (.hidden "Contents") entries)).map (·.target) =
      Outline.ids entries := by
  rw [Outline.linksAt_contentsRaw_plain, List.map_append, List.map_map]
  exact List.map_id _

-- Reader of `namesAt_contentsRaw`: the list defines the identifier of its title's line, so two
-- lists with one title on a page define it twice.
example (entries : List Outline.Entry) :
    namesAt .html (Outline.contentsRaw title entries Theirs.fragment (some "toc")) = ["toc-label"] :=
  Outline.namesAt_contentsRaw _ _ _ _

/-! ## Controls -/

-- Control: the law asks that the page have the parts. A list with an entry that the page lacks
-- has a link that names nothing, and the check of the document says which.
#guard (Content.Document.errors (page (contents (parts ++ [("absent", "Absent", [])])).raw)).any fun p =>
  p.describe == "the link `#absent` names no identifier of the document: at the child path [1, 0, 1, 1, 3, 0]"

-- Control: a title that is shown is named by its line. With an identifier that holds a space,
-- the `nav` names two tokens, and neither is the line.
#guard ((Outline.Title.shown "toc label" "On this page").refs.map fun r => r.target) == ["toc", "label"]

-- Control: below a `button` no link may stand, and the list is refused where it is used.
#guard !Nav.takesLinks (Ctx.flow.child .button)

end WhatwgTest.Html.Outlines
