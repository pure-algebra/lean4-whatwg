import Whatwg.Html.Node.Region
import Whatwg.Html.Node.Check
import Whatwg.Html.Content.Monotone

/-!
# Whatwg.Html.Node.Nav

Owner: the navigations of a page, typed (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entries W9
and W12 of `docs/research/2026-10-12-whatwg-requests.md`). A page of a site says where it
stands three times: among the sections of the site, on the way from the root, and between its
neighbours in reading order. Each is a `nav` of links, and a writer of pages builds each from
data: the hrefs are computed, the list has any length, and one item is the page itself.

```
Nav.list (.label "Site") sections                         -- <nav aria-label="Site"><ol><li><a …>…</a></li>…</ol></nav>
Nav.trail (.label "Breadcrumb") crumbs (some "crumbs")    -- the same, and the last crumb is the page
Nav.pager (.label "Pages") previous next ("Previous", "Next") (some "pager") (some "label")
                                                          -- <nav …><a rel="prev" …><span …>Previous</span>…</a>…</nav>
```

- `Nav.Item` is one link of a navigation: where it leads, its words, and how it is the current
  one (the value of `aria-current`, when it has one).
- `Nav.list name items` is a `nav` around an `ol` of the items, each an `li` around its link.
  The name is that of a region (`Region.Name`): `aria-label` with the words, or
  `aria-labelledby` with the identifier of the element that holds them.
- `Nav.trail name crumbs` is a list whose last crumb is the page: `Item.trail` marks it with
  `aria-current="page"` and marks no other.
- `Nav.pager name previous next words` is a `nav` of at most two links, to the page before and
  the page after, each with `rel` (`prev`, `next`) and a word before its title.
- `listRaw`, `pagerRaw` and the raw forms of an item are the same trees as raw nodes, for a
  fold of data, and `list_toRaw`, `pager_toRaw` say that the typed forms write them.

What is proved once. An `a` takes `href`, `rel` and `aria-current` with every value
(`Item.attrsOk`, `Item.attrsOk_turn`), and a `nav` its name and class (`attrsOk`). An `ol`
stands in a `nav`, an `li` in an `ol`, and text in a link, a `span` in a link and text in a
`span`, wherever the `nav` stands. What is left is one closed test of the position, with
`decide` as its default: that a link may stand where the builder puts it, which fails only
below an element that excludes interactive content or an `a` (a link, a `button`, a `label`).
It is the same test for the three builders (`Nav.takesLinks`), and placing the `nav` is owed
as for any element.

`Whatwg/Html/Node/Nav/Laws.lean` says where the current page is marked, what addresses a
navigation holds, and that a navigation written from the paths of a site's pages has no dead
link.

The basis. That `rel` takes `prev` and `next` on `a` is the HTML Standard's (sections `Link
type "next"` and `Link type "prev"`, `vendor/whatwg-html-746f2ede/source`, lines 30153 and
30173). A `nav` "represents a section of a page that links to other pages or to parts within
the page" (section "The nav element", line 19841), and the standard's first example of it is a
list of links to the pages of a site (line 19856; it writes the list as a `ul`, and the `ol`
here is the consumer's). `aria-current`, its values `page` and `true`, and `aria-label` on a
`nav` are from memory of WAI-ARIA, which is not sealed here (debt D138).

What this module does not claim:

- That an item marked as the page is the page. `Item.trail` marks the last crumb, and a list
  takes its marks from the caller. `Whatwg/Html/Node/Nav/Laws.lean` has the builders that
  compute a mark from two paths.
- That a navigation has one current page: a list marks what its items say.
- The words. `Previous` and `Next` are the caller's.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

namespace Content.Ctx

/-- A tag that the base of a position holds and that no exclusion can refuse is admitted
there. For the children of a transparent element, whose base is that of its position. -/
theorem admits_of_base_of_noHits {c : Ctx} {tag : Tag} (hbase : c.base.contains tag = true)
    (hhits : hits tag = noHits) : c.admits tag = true := by
  rw [admits, excluded_of_noHits hhits, hbase]
  rfl

end Content.Ctx

namespace Nav

/-! ## An item -/

/-- One link of a navigation: where it leads, its words, and how it is the current one: the
value of `aria-current`, or none. -/
structure Item where
  href : String
  label : String
  current : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- The attribute `href`. -/
def hrefAttr (href : String) : AttrVal := ⟨.href, "href", href⟩

/-- The attribute `aria-current`. -/
def currentAttr (how : String) : AttrVal := ⟨.aria_, "aria-current", how⟩

/-- The attribute `rel`. -/
def relAttr (rel : String) : AttrVal := ⟨.rel, "rel", rel⟩

/-- The attributes of an item's link: `href`, and `aria-current` when the item is current. -/
def Item.attrs (i : Item) : List AttrVal := hrefAttr i.href :: A.opt currentAttr i.current

/-- An `a` takes the attributes of an item, whatever the address and the mark are. -/
theorem Item.attrsOk (i : Item) : Content.attrsOk .a (rawAttrs i.attrs) = true := by
  have hhref := fun v => Content.attrOk_of_attrFree (t := .a) (name := "href") (by decide +kernel) v
  have hcurrent := fun v => Content.attrOk_of_attrFree (t := .a) (name := "aria-current")
    (by decide +kernel) v
  cases hc : i.current <;>
    simp only [Item.attrs, hrefAttr, currentAttr, hc, A.opt, rawAttrs, List.map_cons, List.map_nil,
      Content.attrsOk, List.all_cons, List.all_nil, List.length_cons, List.length_nil, hhref,
      hcurrent, Bool.and_true, Bool.true_and] <;>
    decide +kernel

/-- An `a` takes `rel` before the attributes of an item, whatever the three values are. -/
theorem Item.attrsOk_turn (rel : String) (i : Item) :
    Content.attrsOk .a (rawAttrs (relAttr rel :: i.attrs)) = true := by
  have hrel := fun v => Content.attrOk_of_attrFree (t := .a) (name := "rel") (by decide +kernel) v
  have hhref := fun v => Content.attrOk_of_attrFree (t := .a) (name := "href") (by decide +kernel) v
  have hcurrent := fun v => Content.attrOk_of_attrFree (t := .a) (name := "aria-current")
    (by decide +kernel) v
  cases hc : i.current <;>
    simp only [Item.attrs, relAttr, hrefAttr, currentAttr, hc, A.opt, rawAttrs, List.map_cons,
      List.map_nil, Content.attrsOk, List.all_cons, List.all_nil, List.length_cons, List.length_nil,
      hrel, hhref, hcurrent, Bool.and_true, Bool.true_and] <;>
    decide +kernel

/-- The link of an item: an `a` with its attributes around its words. Owed: that text may
stand in the link, which is so wherever the link stands among flow or phrasing content. -/
def Item.link {ctx : Ctx} (i : Item) (htext : (ctx.child .a).admits .pcdata = true) :
    Element .a ctx :=
  Element.ofChildren [Child.text i.label htext] i.attrs
    (Content.elementOk_of_seq_none rfl ctx i.attrsOk _)

/-- The link of an item as a raw node. -/
def Item.linkRaw (i : Item) : RawNode := .element "a" (rawAttrs i.attrs) [.text i.label]

theorem Item.link_toRaw {ctx : Ctx} (i : Item) (htext : (ctx.child .a).admits .pcdata = true) :
    (i.link htext).toRaw = i.linkRaw := rfl

/-- An item of a list: an `li` around the link. Owed: that a link may stand in the `li`. -/
def Item.entry {ctx : Ctx} (i : Item) (hlink : (ctx.child .li).admits .a = true) :
    Element .li ctx :=
  Element.ofChildren
    [Child.of (i.link (Content.Ctx.admits_of_base_of_noHits rfl (by decide)))
      (Content.Ctx.admitsWith_of_admits (ctx.child .li) .a _ rfl hlink)] []
    (Content.elementOk_of_seq_none rfl ctx rfl _)

/-- An item of a list as a raw node. -/
def Item.entryRaw (i : Item) : RawNode := .element "li" [] [i.linkRaw]

theorem Item.entry_toRaw {ctx : Ctx} (i : Item) (hlink : (ctx.child .li).admits .a = true) :
    (i.entry hlink).toRaw = i.entryRaw := rfl

/-! ## A list of links -/

/-- The items of a list, each placed among the children of an `ol` that stands at `ctx`. An
`ol` takes an `li` wherever it stands. -/
def entries {ctx : Ctx} (items : List Item)
    (hlink : ((ctx.child .ol).child .li).admits .a = true) : List (Child (ctx.child .ol)) :=
  items.map fun i =>
    Child.of (i.entry hlink)
      (Content.Ctx.admitsWith_unread _ .li _ (by decide)
        (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))

theorem entries_raw {ctx : Ctx} (items : List Item)
    (hlink : ((ctx.child .ol).child .li).admits .a = true) :
    (entries items hlink).map Child.raw = items.map Item.entryRaw := by
  rw [entries, List.map_map]
  rfl

/-- The `ol` of a list of items. -/
def ordered {ctx : Ctx} (items : List Item)
    (hlink : ((ctx.child .ol).child .li).admits .a = true) : Element .ol ctx :=
  Element.ofChildren (entries items hlink) [] (Content.elementOk_of_seq_none rfl ctx rfl _)

/-- The attributes of a navigation: a class when one is given, and its name. -/
def attrs (name : Region.Name) (className : Option String := none) : List AttrVal :=
  A.opt Region.classAttr className ++ [name.attr]

/-- A `nav` takes the attributes of a navigation, for every name and every class. -/
theorem attrsOk (name : Region.Name) (className : Option String) :
    Content.attrsOk .nav (rawAttrs (attrs name className)) = true := by
  have hlabel := fun words => Content.attrOk_of_attrFree (t := .nav) (name := "aria-label")
    (by decide +kernel) words
  have hlabelledby := fun id => Content.attrOk_of_attrFree (t := .nav) (name := "aria-labelledby")
    (by decide +kernel) id
  have hclass := fun c => Content.attrOk_of_attrFree (t := .nav) (name := "class")
    (by decide +kernel) c
  cases name <;> cases className <;>
    simp only [attrs, Region.Name.attr, Region.classAttr, A.opt, rawAttrs, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, Content.attrsOk, List.all_cons, List.all_nil,
      List.length_cons, List.length_nil, hlabel, hlabelledby, hclass, Bool.and_true,
      Bool.true_and] <;>
    decide +kernel

/-- **A navigation that is a list of links**: a `nav` with its name, around an `ol` of the
items. Owed: one closed test, that a link may stand in an item of the list. -/
def list {ctx : Ctx} (name : Region.Name) (items : List Item) (className : Option String := none)
    (hlink : (((ctx.child .nav).child .ol).child .li).admits .a = true := by decide) :
    Element .nav ctx :=
  Element.ofChildren
    [Child.of (ordered items hlink)
      (Content.Ctx.admitsWith_unread _ .ol _ (by decide)
        (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))]
    (attrs name className) (Content.elementOk_of_seq_none rfl ctx (attrsOk name className) _)

/-- The same navigation as a raw node, for a fold of data. -/
def listRaw (name : Region.Name) (items : List Item) (className : Option String := none) :
    RawNode :=
  .element "nav" (rawAttrs (attrs name className)) [.element "ol" [] (items.map Item.entryRaw)]

/-- The typed list writes the raw one. -/
theorem list_toRaw {ctx : Ctx} (name : Region.Name) (items : List Item)
    (className : Option String)
    (hlink : (((ctx.child .nav).child .ol).child .li).admits .a = true) :
    (list name items className hlink).toRaw = listRaw name items className := by
  have hnodes : (list name items className hlink).toRaw =
      .element "nav" (rawAttrs (attrs name className))
        [.element "ol" [] ((entries items hlink).map Child.raw)] := rfl
  rw [hnodes, entries_raw]
  rfl

/-! ## A trail of crumbs -/

/-- The items of a trail, from each crumb's address and words: the last is the page, and is
marked so; no other is marked. -/
def Item.trail : List (String × String) → List Item
  | [] => []
  | [crumb] => [⟨crumb.1, crumb.2, some "page"⟩]
  | crumb :: next :: rest => ⟨crumb.1, crumb.2, none⟩ :: Item.trail (next :: rest)

/-- **The way to the page**: a list of the crumbs, the last of which is the page. -/
def trail {ctx : Ctx} (name : Region.Name) (crumbs : List (String × String))
    (className : Option String := none)
    (hlink : (((ctx.child .nav).child .ol).child .li).admits .a = true := by decide) :
    Element .nav ctx :=
  list name (Item.trail crumbs) className hlink

theorem trail_toRaw {ctx : Ctx} (name : Region.Name) (crumbs : List (String × String))
    (className : Option String)
    (hlink : (((ctx.child .nav).child .ol).child .li).admits .a = true) :
    (trail name crumbs className hlink).toRaw = listRaw name (Item.trail crumbs) className :=
  list_toRaw name _ className hlink

/-! ## The neighbours in reading order -/

/-- A `span` takes a class when one is given. -/
theorem attrsOk_word (wordClass : Option String) :
    Content.attrsOk .span (rawAttrs (A.opt Region.classAttr wordClass)) = true := by
  cases wordClass with
  | none => rfl
  | some c => exact Content.attrsOk_single (t := .span) (name := "class") (by decide +kernel) c

/-- A link to a neighbour: `rel`, the item's attributes, a `span` with the word that says
which neighbour it is, and the item's words. Owed: that a link may stand at the position. -/
def turn {ctx : Ctx} (rel word : String) (i : Item) (wordClass : Option String := none)
    (hflow : ctx.base = .flow := by rfl) (hlink : ctx.admits .a = true := by decide) : Child ctx :=
  have hbase : (ctx.child .a).base = .flow := by
    rw [Content.child_base_transparent ctx .a rfl, hflow]
    rfl
  have hspan : (ctx.child .a).admits .span = true :=
    Content.Ctx.admits_of_base_of_noHits (by rw [hbase]; rfl) (by decide)
  have htext : (ctx.child .a).admits .pcdata = true :=
    Content.Ctx.admits_of_base_of_noHits (by rw [hbase]; rfl) (by decide)
  let said : Element .span (ctx.child .a) :=
    Element.ofChildren
      [Child.text word (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide))]
      (A.opt Region.classAttr wordClass)
      (Content.elementOk_of_seq_none rfl _ (attrsOk_word wordClass) _)
  Child.of
    (Element.ofChildren
      [Child.of said (Content.Ctx.admitsWith_unread _ .span _ (by decide) hspan),
        Child.text i.label htext]
      (relAttr rel :: i.attrs) (Content.elementOk_of_seq_none rfl ctx (i.attrsOk_turn rel) _))
    (Content.Ctx.admitsWith_of_admits ctx .a _ (by rw [hflow]; rfl) hlink)

/-- A link to a neighbour as a raw node. -/
def turnRaw (rel word : String) (i : Item) (wordClass : Option String := none) : RawNode :=
  .element "a" (rawAttrs (relAttr rel :: i.attrs))
    [.element "span" (rawAttrs (A.opt Region.classAttr wordClass)) [.text word], .text i.label]

theorem turn_raw {ctx : Ctx} (rel word : String) (i : Item) (wordClass : Option String)
    (hflow : ctx.base = .flow) (hlink : ctx.admits .a = true) :
    (turn rel word i wordClass hflow hlink).raw = turnRaw rel word i wordClass := rfl

/-- **The neighbours of the page in reading order**: a `nav` of a link to the page before,
when there is one, and a link to the page after, when there is one. `words` are the two words
that say which is which. Owed: one closed test, that a link may stand in the `nav`. -/
def pager {ctx : Ctx} (name : Region.Name) (previous next : Option Item) (words : String × String)
    (className wordClass : Option String := none)
    (hlink : (ctx.child .nav).admits .a = true := by decide) : Element .nav ctx :=
  Element.ofChildren
    ((previous.map fun i => turn "prev" words.1 i wordClass rfl hlink).toList ++
      (next.map fun i => turn "next" words.2 i wordClass rfl hlink).toList)
    (attrs name className) (Content.elementOk_of_seq_none rfl ctx (attrsOk name className) _)

/-- The same navigation as a raw node. -/
def pagerRaw (name : Region.Name) (previous next : Option Item) (words : String × String)
    (className wordClass : Option String := none) : RawNode :=
  .element "nav" (rawAttrs (attrs name className))
    ((previous.map fun i => turnRaw "prev" words.1 i wordClass).toList ++
      (next.map fun i => turnRaw "next" words.2 i wordClass).toList)

/-- The typed pager writes the raw one. -/
theorem pager_toRaw {ctx : Ctx} (name : Region.Name) (previous next : Option Item)
    (words : String × String) (className wordClass : Option String)
    (hlink : (ctx.child .nav).admits .a = true) :
    (pager name previous next words className wordClass hlink).toRaw =
      pagerRaw name previous next words className wordClass := by
  cases previous <;> cases next <;> rfl

/-! ## One test for the three -/

/-- A navigation of links may stand at the position: nothing above it excludes interactive
content or an `a`. The one test that the three builders ask of a position that is a variable:
`link_in_list` and `link_in_pager` turn it into what each builder owes. -/
def takesLinks (ctx : Ctx) : Bool := !(ctx.excl.interactive || ctx.excl.a)

/-- The exclusions refuse an `a` exactly when they exclude interactive content or `a`. -/
theorem excluded_a (x : Exclusions) : Ctx.excluded x .a = (x.interactive || x.a) := by
  have hhits : Ctx.hits .a = [true, false, false, false, false, false, false, false, false, false,
      false, false, false, false, true] := by decide
  rw [Content.Ctx.excluded_eq_spec, Ctx.excludedSpec, hhits]
  cases x
  simp only [Exclusions.flags, List.zip_cons_cons, List.zip_nil_right, List.any_cons, List.any_nil,
    Bool.and_false, Bool.and_true, Bool.or_false, Bool.false_or]

/-- Below an element that excludes neither interactive content nor `a`, the test is the same. -/
theorem takesLinks_child (ctx : Ctx) (t : Tag)
    (h : (t.ownExcl.interactive || t.ownExcl.a) = false) :
    takesLinks (ctx.child t) = takesLinks ctx := by
  have hboth := Bool.or_eq_false_iff.mp h
  show (!((ctx.excl.interactive || t.ownExcl.interactive) || (ctx.excl.a || t.ownExcl.a))) = _
  rw [hboth.1, hboth.2, Bool.or_false, Bool.or_false]
  rfl

/-- Where the test holds and the base holds `a`, a link is admitted. -/
theorem admits_a_of_takesLinks {ctx : Ctx} (h : takesLinks ctx = true)
    (hbase : ctx.base.contains .a = true) : ctx.admits .a = true := by
  unfold takesLinks at h
  rw [Ctx.admits, excluded_a, hbase, Bool.true_or, Bool.true_and]
  exact h

/-- What `list` and `trail` owe, from the one test of the position. -/
theorem link_in_list {ctx : Ctx} (h : takesLinks ctx = true) :
    (((ctx.child .nav).child .ol).child .li).admits .a = true :=
  admits_a_of_takesLinks
    (by
      rw [takesLinks_child _ .li (by decide), takesLinks_child _ .ol (by decide),
        takesLinks_child _ .nav (by decide)]
      exact h)
    rfl

/-- What `pager` owes, from the one test of the position. -/
theorem link_in_pager {ctx : Ctx} (h : takesLinks ctx = true) : (ctx.child .nav).admits .a = true :=
  admits_a_of_takesLinks
    (by
      rw [takesLinks_child _ .nav (by decide)]
      exact h)
    rfl

end Nav

end Whatwg.Html
