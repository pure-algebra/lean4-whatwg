import Whatwg.Html.Content.Lattice
import Whatwg.Html.Content.Transparent
import Whatwg.Html.Content.Admission
import Whatwg.Html.Node.Raw

/-!
# Whatwg.Html.Node.Typed

The tag-indexed tree of slice H3.3 (`docs/HTML-PACKAGE-PLAN.md`, rulings
HP-4, HP-5 and HP-6): an element carries the admission obligations of its
children and of its attributes as propositions decided at construction, never
as checked booleans, and the value it holds is already erased.

## TyXML's scheme, reproduced through unification

TyXML types a constructor as `('a attrib list, 'b, 'c) star`, where `'c` is
the *result* row. For an ordinary element the result row is a bare variant
(`` [> `Div] ``) and `'b` is that element's own content type. For a
transparent element the result row carries the content parameter
(`` a : ('a attrib, 'a, [> 'a a]) star ``), so a link placed in a phrasing
position is unified against `` `A of phrasing_without_interactive `` and its
children are checked against that payload rather than against the link's own
content type. That is ruling HP-4: transparency is resolved at the enclosing
non-transparent parent, not by a flag passed downward.

`Element t inner` is the Lean transcription of that pair: `t` is the result
tag and `inner` is the content set the element's children were checked
against. A non-transparent combinator fixes `inner` to the element's own
content set; a transparent combinator leaves `inner` universally quantified.
`Child.of` demands `Element t (childSet set t)`, so placing a transparent
element in a `Child set` position assigns `inner := childSet set t`, and
`childSet` reads exactly TyXML's payload table through
`Whatwg.Html.Content.resolveChildSet`.

The inference works as designed on this toolchain, with no fallback needed:
Lean's application elaborator propagates the expected type into the result
type of a function application before elaborating its explicit arguments, so
`?inner` is assigned from the `Child set` position *before* the transparent
element's own children are elaborated, and the `by decide` obligation on each
of those children is stated over a fully assigned content set.
`childSet` is an `abbrev` so that unification may unfold it at reducible
transparency; the obligations themselves reduce at default transparency in
either spelling.

## What is checked, and what is not

- Child admission: `Child.of` and `Child.text` discharge
  `Whatwg.Html.Content.Admits set t` by `decide` at the call site, and the
  resulting `Child` stores that proof. So a `Child set` is evidence that its
  tag is a member of `set` in the sealed TyXML 4.6.0 projection. It is not a
  claim about the HTML Standard; departures of the port are the business of
  `Whatwg.Html.Content.Divergence`.
- Attribute admission: every combinator carries an auto-parameter `_ha`
  proving `AttrsAdmitted` for its element's attribute set. The proof is not
  stored, because `Element` is indexed by the tag and the child content set
  only and the attribute set is not a function of the tag (`table` and
  `tablex` share the tag `Table` and take different attribute sets); the
  parameter is therefore spelled with a leading underscore, and a rejection
  names `_ha`.
- Attribute *values* are plain `String` at this pin. TyXML's typed value
  constructors (`` a_input_type : [< `Text | `Password | ...] wrap -> attrib ``)
  are a later slice.
- Comments have no tag in the content model, so `RawNode.comment` has no
  typed constructor here; a comment enters the tree only through the raw
  layer.

## Cost

Every element node costs the application elaborator about twelve thousand
heartbeats at this pin (`WhatwgTest/Html/DecideBenchmark.lean`): most of it
is the elaborator's own work per combinator application and its unification
of `childSet set t` against the combinator's fixed content set. The default
`maxHeartbeats` of 200 therefore holds a tree of roughly fifteen nested or
fifty flat element nodes, and a larger construction through the combinators
must raise it. The auto-parameters here are `by decide`; the combinators
use the `admits` tactic of `Whatwg.Html.Node.Admit`, which evaluates the
obligation with the compiled schema, hands the kernel `Eq.refl true`, and
names the element and the excluding set on failure. A document is meant to
be written through `html!` (`Whatwg.Html.Syntax.Elaborator`, slice H5),
which builds the term directly through the same evaluation, so that its
cost per node is not the elaborator's.
-/

namespace Whatwg.Html.Schema

/-- The markup name of a tag as a total function: `Tag.markupName` where the
tag is an element, and the name `pcdata` for text, which no element position
ever renders as a tag name, so the fallback is a totality device rather than
a spelling claim. -/
def Tag.markupText (t : Tag) : String := t.markupName.getD t.variantName

end Whatwg.Html.Schema

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)

/-- An element of tag `t` whose children were checked against the content
set `inner` and whose children are already erased to `RawNode`. The two
indices are TyXML's result row: `t` is the variant and `inner` is the payload
that variant carries when the element is transparent. -/
structure Element (t : Tag) (inner : ContentSet) where
  /-- The attributes, as tag/value pairs; admission against the element's
  attribute set was decided by the combinator that built this value. -/
  attrs : List (Attr × String)
  /-- The erased children, each of which was a `Child inner`. -/
  children : List RawNode

/-- Erasure to the untyped tree: the markup name of the tag, the markup names
of the attributes, and the already-erased children. -/
def Element.toRaw {t : Tag} {inner : ContentSet} (e : Element t inner) : RawNode :=
  .element t.markupText (e.attrs.map (fun p => (p.1.markupName, p.2))) e.children

/-- The content set an element of tag `t` placed in the context `set` must
have checked its children against: the transparent payload the context
assigns `t` when there is one, else `t`'s own content set, else the empty set
`nothing`. Total, so that it can index a type; `Whatwg.Html.Content`'s
`resolveChildSet_none` says the fallback is taken only for text, which has
no element row. An `abbrev` so that unification may
unfold it at reducible transparency. -/
abbrev childSet (set : ContentSet) (t : Tag) : ContentSet :=
  (Content.resolveChildSet t set).getD .nothing

/-- A child admitted under the content set `set`: its tag, the proof that
`set` names it, and its erased form. Storing the proof rather than discarding
it is what makes a `Child set` evidence, and it is why `Child.of`'s
auto-parameter is not a dead binder. -/
structure Child (set : ContentSet) where
  /-- The tag of the child. -/
  tag : Tag
  /-- The context admits that tag, in the sense of
  `Whatwg.Html.Content.Admits`. -/
  admitted : Content.Admits set tag
  /-- The erased child. -/
  raw : RawNode

/-- Place a typed element in a child position. The element's `inner` index is
`childSet set t`, so a transparent combinator's content parameter is assigned
by this unification and its children are then checked against TyXML's payload
for `t` in `set`. -/
def Child.of {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t := by decide) : Child set :=
  ⟨t, h, e.toRaw⟩

/-- Weakening: a child admitted under a narrower set is admitted under a
wider one. This is where the inclusion theorems of
`Whatwg.Html.Content.Lattice` become usable at a call site: a
`Child .phrasing` is placed in a `Child .flow5` position by
`Child.weaken Content.phrasing_subset_flow5`. Deliberately not a `Coe`:
`SubsetOf` is a proposition, not a class, and the inclusion used should stay
visible in the source (the same reasoning that ruled out `Fact`, HP-6). -/
def Child.weaken {a b : ContentSet} (h : Content.SubsetOf a.contains b.contains)
    (c : Child a) : Child b :=
  ⟨c.tag, h c.tag c.admitted, c.raw⟩

/-- A text run, admitted wherever the content set names `PCDATA` (ruling
HP-5). -/
def Child.text {set : ContentSet} (s : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  ⟨.pcdata, h, .text s⟩

/-- A named entity reference. TyXML's `entity` has the same result tag as
`txt`, so it is admitted exactly where `PCDATA` is. -/
def Child.entity {set : ContentSet} (name : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  ⟨.pcdata, h, .entity name⟩

/-- Every attribute supplied to a combinator is a member of that element's
attribute set. This is the proposition each combinator's `_ha` auto-parameter
discharges by `decide`. -/
abbrev AttrsAdmitted (set : AttrSet) (attrs : List (Attr × String)) : Prop :=
  attrs.all (fun p => set.contains p.1) = true

end Whatwg.Html
