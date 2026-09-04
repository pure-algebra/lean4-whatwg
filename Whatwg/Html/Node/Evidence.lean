import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Evidence

Evidence for a raw child list, the shape `html!` (slice H5) builds. A term
of `Element t inner` produced through the combinators is a tree of
`Child.of` and `Child.raw` applications that the compiler inlines node by
node and that re-erases itself at run time; a document of a few hundred
nodes exceeds the default heartbeat budget in the compiler alone
(`WhatwgTest/Html/MarkupBenchmark.lean`). `Element.ofRaw` separates the
two: the value is a raw literal, and `Erasure t inner children` is a
proposition, erased by the compiler and checked by the kernel, that every
raw child is the erasure of an admitted `Child inner` or of a labelled
element.

`labelledChild` is the standard's rule for the children a sentence admits
first and outside any content set: `source` and `track` under `audio` and
`video`, and `area` under `map` (the standard admits `area` only with a
`map` ancestor). Such a child is checked against its own content set and
placed as an element, not as an admitted `Child`; the generated
combinators take them as labelled lists.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)

/-- The direct children a sentence admits outside any content set
(`source` and `track` first under `audio` and `video`, `area` under `map`):
the generated table `Whatwg.Html.Schema.labelledChild`, under the name the
evidence and the elaborator use. -/
abbrev labelledChild : Tag → Tag → Bool := Schema.labelledChild

/-- Every raw node of the list is the erasure of an admitted child of the
context `inner`, or of a labelled element of the parent tag `t`. A
proposition, so a term of it is erased by the compiler; the kernel checks
it by evaluating each erasure against the literal it indexes. -/
inductive Erasure (t : Tag) (inner : ContentSet) : List RawNode → Prop
  | nil : Erasure t inner []
  | child (c : Child inner) (rest : List RawNode) (h : Erasure t inner rest) :
      Erasure t inner (c.raw :: rest)
  | labelled (c : Tag) (hl : labelledChild t c = true) (e : Element c (c.content?.getD .nothing))
      (rest : List RawNode) (h : Erasure t inner rest) :
      Erasure t inner (e.toRaw :: rest)

/-- An element from its raw children and the evidence for them. `labelled`
are the attributes TyXML takes as required labelled arguments (`img ~src
~alt`), which are outside the element's attribute set as the combinators
also place them; `attrs` are the ones the set must name. The two proofs are
not stored, for the reason `Typed.lean` gives for the combinators' `_ha`. -/
def Element.ofRaw {t : Tag} {inner : ContentSet} (set : AttrSet)
    (labelled attrs : List (Attr × String)) (children : List RawNode)
    (_ha : AttrsAdmitted set attrs) (_hc : Erasure t inner children) : Element t inner :=
  ⟨labelled ++ attrs, children⟩

/-- The erasure of `Element.ofRaw` is the raw element it was built from. -/
theorem Element.ofRaw_toRaw {t : Tag} {inner : ContentSet} (set : AttrSet)
    (labelled attrs : List (Attr × String)) (children : List RawNode)
    (ha : AttrsAdmitted set attrs) (hc : Erasure t inner children) :
    (Element.ofRaw set labelled attrs children ha hc).toRaw =
      .element t.markupText ((labelled ++ attrs).map (fun p => (p.1.markupName, p.2))) children :=
  rfl

end Whatwg.Html
