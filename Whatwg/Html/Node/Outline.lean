import Whatwg.Html.Node.Nav

/-!
# Whatwg.Html.Node.Outline

Owner: the parts of a page as data, and the contents list built from them (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entries W9 and W13 of
`docs/research/2026-10-12-whatwg-requests.md`). A page of parts shows them twice: as the parts
themselves, each with an identifier, and as a list of links to them. The list is written from
the same data as the parts, so that it names each part that is there and no other.

```
Outline.contents (.shown "toc-label" "On this page" (some "label"))
  [.mk "claims" "Every claim" [.mk "keys-once" "Keys once" []], .mk "plan" "The plan" []]
  (className := some "toc")
-- <nav class="toc" aria-labelledby="toc-label"><p id="toc-label" class="label">On this page</p>
--   <ol><li><a href="#claims">Every claim</a><ol><li><a href="#keys-once">Keys once</a></li></ol></li>
--       <li><a href="#plan">The plan</a></li></ol></nav>
```

- `Outline.Entry` is one part: its identifier, its title, and its own parts, to any depth.
  `Entry.ids` and `Outline.ids` are the identifiers of an outline in the order of the page.
- `Outline.Title` is how the list is named: by words that are not shown (`aria-label`), or by
  a line of words above the list, a `p` with an identifier that the `nav` names in
  `aria-labelledby`.
- `Outline.contents title entries` is the typed list: a `nav` around an `ol`; each entry is an
  `li` with a link to its part and, when it has parts, an `ol` of them below the link. The link
  of the entry `id` is `href id`, which is `#` and the identifier unless the caller gives
  another writer of fragments.
- `Outline.contentsRaw` is the same tree as a raw node, and `contents_toRaw` says that the
  typed list writes it.

What is proved once. The list is good at every depth wherever the `nav` may stand and a link
may stand below it: the one test is `Nav.takesLinks`, as for the navigations of
`Whatwg/Html/Node/Nav.lean`, and `decide` answers it for a position that is written out.

`Whatwg/Html/Node/Outline/Laws.lean` says which references the list makes: one to each
identifier of the outline, in the order of the page, and one to its own title's line. So the
list is closed against a page that has those identifiers.

The basis. A `nav` of links "to parts within the page" is the HTML Standard's (section "The nav
element", `vendor/whatwg-html-746f2ede/source`, line 19841; its first example has such a list,
line 19875). `aria-labelledby` and `aria-label` are from memory of WAI-ARIA, which is not
sealed here (debt D138).

The outline comes from data, and not from a tree. The consumer has its parts as data before any
tree exists. To read an outline from a tree would need what `Content.Document.Fact.heading`
does not keep: the text of a heading (without the link to itself that the consumer puts in it)
and the identifier of the part it opens.

What this module does not claim:

- That the page has the parts. The law is about the list; that each identifier is there is
  the page's, and `Content.Document.errors` reports a link that names none.
- An escape. The default link writes the identifier as it is. The reader of a fragment takes
  the identifier as written first (`Content.Document.Ref.NamesIn`), so this names the part
  whatever the identifier holds. A writer that percent-encodes is the caller's.
- That the title's identifier is new on the page.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

namespace Outline

/-! ## The data -/

/-- A part of a page: its identifier, its title, and its own parts. -/
inductive Entry where
  | mk (id title : String) (parts : List Entry)

instance : Inhabited Entry := ⟨.mk "" "" []⟩

/-- The identifier of the part. -/
def Entry.id : Entry → String
  | .mk id _ _ => id

/-- The title of the part. -/
def Entry.title : Entry → String
  | .mk _ title _ => title

/-- The part's own parts. -/
def Entry.parts : Entry → List Entry
  | .mk _ _ parts => parts

mutual

/-- The identifiers of a part and of the parts below it, in the order of the page. -/
def Entry.ids : Entry → List String
  | .mk id _ parts => id :: ids parts

/-- The identifiers of an outline, in the order of the page. -/
def ids : List Entry → List String
  | [] => []
  | entry :: rest => entry.ids ++ ids rest

end

/-- How a contents list is named. -/
inductive Title where
  /-- By words that are not shown: `aria-label`. -/
  | hidden (words : String)
  /-- By a line of words above the list: a `p` with the identifier, which the `nav` names in
  `aria-labelledby`. -/
  | shown (id words : String) (className : Option String := none)
  deriving DecidableEq, Repr, Inhabited

/-- The name that the `nav` takes from its title. -/
def Title.name : Title → Region.Name
  | .hidden words => .label words
  | .shown id _ _ => .labelledBy id

/-- The attributes of the title's line: its identifier, and a class when one is given. -/
def lineAttrs (id : String) (className : Option String) : List AttrVal :=
  ⟨.id, "id", id⟩ :: A.opt Region.classAttr className

/-- The title's line as a raw node, when it is shown. -/
def Title.lineRaw : Title → List RawNode
  | .hidden _ => []
  | .shown id words className => [.element "p" (rawAttrs (lineAttrs id className)) [.text words]]

/-! ## The raw tree -/

mutual

/-- The item of a part: an `li` with the link to the part and, when it has parts, the list of
them below the link. -/
def Entry.raw (href : String → String) : Entry → RawNode
  | .mk id title parts =>
    .element "li" []
      (.element "a" [("href", href id)] [.text title] ::
        if parts.isEmpty then [] else [.element "ol" [] (rawAll href parts)])

/-- The items of an outline. -/
def rawAll (href : String → String) : List Entry → List RawNode
  | [] => []
  | entry :: rest => entry.raw href :: rawAll href rest

end

/-- The link to a part that writes its identifier as it is. -/
def plainHref (id : String) : String := "#" ++ id

/-- The contents list as a raw node, for a fold of data. -/
def contentsRaw (title : Title) (entries : List Entry) (href : String → String := plainHref)
    (className : Option String := none) : RawNode :=
  .element "nav" (rawAttrs (Nav.attrs title.name className))
    (title.lineRaw ++ [.element "ol" [] (rawAll href entries)])

/-! ## The typed tree -/

/-- A `p` takes an identifier, and a class when one is given, whatever they are. -/
theorem attrsOk_line (id : String) (className : Option String) :
    Content.attrsOk .p (rawAttrs (lineAttrs id className)) = true := by
  have hid := fun v => Content.attrOk_of_attrFree (t := .p) (name := "id") (by decide +kernel) v
  have hclass := fun c => Content.attrOk_of_attrFree (t := .p) (name := "class")
    (by decide +kernel) c
  cases className <;>
    simp only [lineAttrs, Region.classAttr, A.opt, rawAttrs, List.map_cons, List.map_nil,
      Content.attrsOk, List.all_cons, List.all_nil, List.length_cons, List.length_nil, hid, hclass,
      Bool.and_true, Bool.true_and] <;>
    decide +kernel

/-- The title's line among the children of the `nav`, when it is shown. A `nav` takes a `p`
wherever it stands. -/
def Title.line {ctx : Ctx} : Title → List (Child (ctx.child .nav))
  | .hidden _ => []
  | .shown id words className =>
    [Child.of
      (Element.ofChildren (t := .p)
        [Child.text words (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide))]
        (lineAttrs id className) (Content.elementOk_of_seq_none rfl _ (attrsOk_line id className) _))
      (Content.Ctx.admitsWith_unread _ .p _ (by decide)
        (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))]

theorem Title.line_raw {ctx : Ctx} (title : Title) :
    (title.line (ctx := ctx)).map Child.raw = title.lineRaw := by
  cases title <;> rfl

/-- Below an `ol` and an `li`, a link may stand where it may stand above them. -/
theorem takesLinks_item {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    Nav.takesLinks ((ctx.child .ol).child .li) = true := by
  rw [Nav.takesLinks_child _ .li (by decide), Nav.takesLinks_child _ .ol (by decide)]
  exact h

/-- Below a `nav`, a link may stand where it may stand above it. -/
theorem takesLinks_nav {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    Nav.takesLinks (ctx.child .nav) = true := by
  rw [Nav.takesLinks_child _ .nav (by decide)]
  exact h

mutual

/-- The item of a part, among the children of an `ol` that stands at `ctx`. -/
def Entry.item (href : String → String) {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    Entry → Child (ctx.child .ol)
  | .mk id title parts =>
    Child.of
      (Element.ofChildren (t := .li)
        (Child.of
            ((⟨href id, title, none⟩ : Nav.Item).link
              (Content.Ctx.admits_of_base_of_noHits rfl (by decide)))
            (Content.Ctx.admitsWith_of_admits _ .a _ rfl
              (Nav.admits_a_of_takesLinks (takesLinks_item h) rfl)) ::
          if parts.isEmpty then []
          else
            [Child.of
              (Element.ofChildren (t := .ol) (items href (takesLinks_item h) parts) []
                (Content.elementOk_of_seq_none rfl _ rfl _))
              (Content.Ctx.admitsWith_unread _ .ol _ (by decide)
                (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide)))])
        [] (Content.elementOk_of_seq_none rfl _ rfl _))
      (Content.Ctx.admitsWith_unread _ .li _ (by decide)
        (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))

/-- The items of an outline, among the children of an `ol` that stands at `ctx`. -/
def items (href : String → String) {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    List Entry → List (Child (ctx.child .ol))
  | [] => []
  | entry :: rest => entry.item href h :: items href h rest

end

mutual

/-- The typed item of a part writes the raw one. -/
theorem Entry.item_raw (href : String → String) {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    ∀ entry : Entry, (entry.item href h).raw = entry.raw href
  | .mk id title parts => by
    cases hparts : parts.isEmpty with
    | true =>
      rw [Entry.item, Entry.raw]
      simp only [hparts, ↓reduceIte]
      rfl
    | false =>
      have hbelow := items_raw href (takesLinks_item h) parts
      rw [Entry.item, Entry.raw]
      simp only [hparts, Bool.false_eq_true, ↓reduceIte]
      rw [← hbelow]
      rfl

/-- The typed items of an outline write the raw ones. -/
theorem items_raw (href : String → String) {ctx : Ctx} (h : Nav.takesLinks ctx = true) :
    ∀ entries : List Entry, (items href h entries).map Child.raw = rawAll href entries
  | [] => by
    rw [items, rawAll]
    rfl
  | entry :: rest => by
    rw [items, rawAll, List.map_cons, Entry.item_raw href h entry, items_raw href h rest]

end

/-- **The contents of a page**: a `nav` with its title, around an `ol` of the parts, each a
link to the part and, below it, the list of its own parts. Owed: one closed test, that a link
may stand below the position. -/
def contents {ctx : Ctx} (title : Title) (entries : List Entry)
    (href : String → String := plainHref) (className : Option String := none)
    (h : Nav.takesLinks ctx = true := by decide) : Element .nav ctx :=
  Element.ofChildren
    (title.line ++
      [Child.of
        (Element.ofChildren (t := .ol) (items href (takesLinks_nav h) entries) []
          (Content.elementOk_of_seq_none rfl _ rfl _))
        (Content.Ctx.admitsWith_unread _ .ol _ (by decide)
          (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))])
    (Nav.attrs title.name className)
    (Content.elementOk_of_seq_none rfl ctx (Nav.attrsOk title.name className) _)

/-- The typed list writes the raw one. -/
theorem contents_toRaw {ctx : Ctx} (title : Title) (entries : List Entry)
    (href : String → String) (className : Option String) (h : Nav.takesLinks ctx = true) :
    (contents title entries href className h).toRaw = contentsRaw title entries href className := by
  have hol := items_raw href (takesLinks_nav h) entries
  cases title with
  | hidden words =>
    have hnodes : (contents (.hidden words) entries href className h).toRaw =
        .element "nav" (rawAttrs (Nav.attrs (Title.hidden words).name className))
          [.element "ol" [] ((items href (takesLinks_nav h) entries).map Child.raw)] := rfl
    rw [hnodes, hol]
    rfl
  | shown id words lineClass =>
    have hnodes : (contents (.shown id words lineClass) entries href className h).toRaw =
        .element "nav" (rawAttrs (Nav.attrs (Title.shown id words lineClass).name className))
          [.element "p" (rawAttrs (lineAttrs id lineClass)) [.text words],
            .element "ol" [] ((items href (takesLinks_nav h) entries).map Child.raw)] := rfl
    rw [hnodes, hol]
    rfl

end Outline

end Whatwg.Html
