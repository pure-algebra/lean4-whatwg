import Whatwg.Html.Content.Valid

/-!
# Whatwg.Html.Node.Typed

The typed tree, as a proven-sound front end over the checker of
`Whatwg.Html.Content.Valid` (ruling HP-13). An `Element t ctx` is an element
of tag `t` placed in the context `ctx`, carrying its attributes, its
already-erased children, and two proofs: that its attributes are admitted
on `t` with conforming values, and that every child is valid at
`ctx.child t`. A `Child ctx` is a raw node with the proof that it is valid
at `ctx`. Placing an element in a child position (`Child.of`) needs only
the admission of its tag, and yields the validity of its erasure:
`Element.valid` is the soundness theorem, and it is by construction.

The index is the *parent* context. A combinator is therefore polymorphic
in the context it is placed in, its children are checked at the context
`Ctx.child` computes, and nothing is unified against a computed set:
transparency, the descendant exclusions and the labelled children are all
inside `Ctx.child`. A root names its context (`Element .html Ctx.document`).

The proofs are propositions, erased by the compiler; the value that
remains is the attributes and the raw children.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag Attr AttrSet)
open Whatwg.Html.Content (Ctx validIn validAll attrsOk)

/-- The raw form of a typed attribute list: markup names and values. -/
def rawAttrs (attrs : List (Attr × String)) : List (String × String) :=
  attrs.map fun p => (p.1.markupName, p.2)

/-- A raw node valid at a position. -/
structure Child (ctx : Ctx) where
  raw : RawNode
  valid : validIn ctx raw = true

/-- An element of tag `t` placed in the context `ctx`: its attributes, its
erased children, and the proofs that make its erasure valid. -/
structure Element (t : Tag) (ctx : Ctx) where
  attrs : List (Attr × String)
  children : List RawNode
  hattrs : attrsOk t (rawAttrs attrs) = true
  hchildren : validAll (ctx.child t) children = true
  htag : t.markupName.isSome = true

/-- Erasure. -/
def Element.toRaw {t : Tag} {ctx : Ctx} (e : Element t ctx) : RawNode :=
  .element t.markupText (rawAttrs e.attrs) e.children

/-- Soundness of the typed tree: an element the position admits erases to a
raw node the checker accepts there. -/
theorem Element.valid {t : Tag} {ctx : Ctx} (e : Element t ctx) (h : ctx.admits t = true) :
    validIn ctx e.toRaw = true := by
  obtain ⟨m, hm⟩ : ∃ m, t.markupName = some m := by
    cases hn : t.markupName with
    | none => have ht := e.htag; simp [hn] at ht
    | some m => exact ⟨m, rfl⟩
  have hmt : t.markupText = m := by simp [Schema.Tag.markupText, hm]
  rw [Element.toRaw, hmt]
  exact Content.validIn_element ctx t m hm _ _ h e.hattrs e.hchildren

/-- Every child of a list of children is valid, so the list is. -/
theorem validAll_children {ctx : Ctx} : ∀ cs : List (Child ctx), validAll ctx (cs.map Child.raw) = true
  | [] => rfl
  | c :: cs => Content.validAll_cons ctx c.raw _ c.valid (validAll_children cs)

/-- Build an element from typed children. The tag must be an element
(`htag`), which every combinator discharges once at its definition. -/
def Element.ofChildren {t : Tag} {ctx : Ctx} (cs : List (Child (ctx.child t)))
    (attrs : List (Attr × String)) (ha : attrsOk t (rawAttrs attrs) = true)
    (ht : t.markupName.isSome = true := by decide) : Element t ctx :=
  ⟨attrs, cs.map Child.raw, ha, validAll_children cs, ht⟩

/-- Place an element in a child position. -/
def Child.of {t : Tag} {ctx : Ctx} (e : Element t ctx) (h : ctx.admits t = true := by decide) : Child ctx :=
  ⟨e.toRaw, e.valid h⟩

/-- A text run, where the base names text. -/
def Child.text {ctx : Ctx} (s : String) (h : ctx.admits .pcdata = true := by decide) : Child ctx :=
  ⟨.text s, Content.validIn_text ctx s h⟩

/-- A named entity reference, admitted where text is. -/
def Child.entity {ctx : Ctx} (name : String) (h : ctx.admits .pcdata = true := by decide) : Child ctx :=
  ⟨.entity name, Content.validIn_entity ctx name h⟩

/-- An element placed at a position, as a document of the checker. -/
def Element.toDoc {t : Tag} {ctx : Ctx} (e : Element t ctx) (h : ctx.admits t = true := by decide) :
    Content.Doc ctx :=
  ⟨e.toRaw, e.valid h⟩

end Whatwg.Html
