import Whatwg.Html.Content.Valid

/-!
# Whatwg.Html.Node.Typed

The typed tree, as a proven-sound front end over the checker of
`Whatwg.Html.Content.Valid` (ruling HP-13). An `Element t ctx` is an element
of tag `t` placed in the context `ctx`, carrying its attributes, its
already-erased children, and three proofs: that its attributes are admitted
on `t` with conforming values, that its children follow its ordered model
when it has one, and that every child is valid at `ctx.child t`. A `Child ctx` is a raw node with the proof that it is valid
at `ctx`. Placing an element in a child position (`Child.of`) needs only
the admission of its tag given its attributes, and yields the validity of
its erasure:
`Element.valid` is the soundness theorem, and it is by construction.

The index is the *parent* context. A combinator is therefore polymorphic
in the context it is placed in, its children are checked at the context
`Ctx.child` computes, and nothing is unified against a computed set:
transparency, the descendant exclusions and the labelled children are all
inside `Ctx.child`. A root names its context (`Element .html Ctx.document`).

The proofs are propositions, erased by the compiler; the value that
remains is the attributes and the raw children.

A note on lists: core's list literal switches to a `let`-based desugaring at
33 elements, and the combinator surface then costs seconds where 32 children
cost milliseconds (performance review §2.1). A list of more than 32 children
is written as chunks joined by `++`; `html!` is not affected.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag Attr AttrSet)
open Whatwg.Html.Content (Ctx validIn validAll attrsOk)

/-- A typed attribute: the attribute, its full markup name (the prefix and
suffix together for `data-*` and `aria-*`), and its value. -/
structure AttrVal where
  attr : Attr
  name : String
  value : String
  deriving Repr, Inhabited

/-- An attribute of the index, by its markup name. -/
def AttrVal.of (a : Attr) (value : String) : AttrVal := ⟨a, a.markupName, value⟩

/-- A custom data attribute `data-<suffix>`. -/
def AttrVal.data (suffix value : String) : AttrVal := ⟨.data_, "data-" ++ suffix, value⟩

/-- An ARIA attribute `aria-<suffix>`. -/
def AttrVal.aria (suffix value : String) : AttrVal := ⟨.aria_, "aria-" ++ suffix, value⟩

/-- The raw form of a typed attribute list: names and values. -/
def rawAttrs (attrs : List AttrVal) : List (String × String) :=
  attrs.map fun a => (a.name, a.value)

/-- A raw node valid at a position. -/
structure Child (ctx : Ctx) where
  raw : RawNode
  valid : validIn ctx raw = true

/-- An element of tag `t` placed in the context `ctx`: its attributes, its
erased children, and the proofs that make its erasure valid. -/
structure Element (t : Tag) (ctx : Ctx) where
  attrs : List AttrVal
  children : List RawNode
  hattrs : attrsOk t (rawAttrs attrs) = true
  hseq : Content.seqOk (ctx.child t) t children = true
  hchildren : validAll (ctx.child t) children = true
  htag : t.markupName.isSome = true

/-- Erasure. -/
def Element.toRaw {t : Tag} {ctx : Ctx} (e : Element t ctx) : RawNode :=
  .element t.markupText (rawAttrs e.attrs) e.children

/-- Soundness of the typed tree: an element the position admits erases to a
raw node the checker accepts there. -/
theorem Element.valid {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (h : ctx.admitsWith t (rawAttrs e.attrs) = true) : validIn ctx e.toRaw = true := by
  obtain ⟨m, hm⟩ : ∃ m, t.markupName = some m := by
    cases hn : t.markupName with
    | none => have ht := e.htag; rw [hn] at ht; exact Bool.noConfusion ht
    | some m => exact ⟨m, rfl⟩
  have hmt : t.markupText = m := by simp only [Schema.Tag.markupText, hm, Option.getD_some]
  rw [Element.toRaw, hmt]
  exact Content.validIn_element ctx t m hm _ _ h e.hattrs e.hseq e.hchildren

/-- Every child of a list of children is valid, so the list is. -/
theorem validAll_children {ctx : Ctx} : ∀ cs : List (Child ctx), validAll ctx (cs.map Child.raw) = true
  | [] => rfl
  | c :: cs => Content.validAll_cons ctx c.raw _ c.valid (validAll_children cs)

/-- Build an element from typed children. The tag must be an element
(`htag`), which every combinator discharges once at its definition. -/
def Element.ofChildren {t : Tag} {ctx : Ctx} (cs : List (Child (ctx.child t)))
    (attrs : List AttrVal) (ho : Content.elementOk ctx t (rawAttrs attrs) (cs.map Child.raw) = true)
    (ht : t.markupName.isSome = true := by decide) : Element t ctx :=
  ⟨attrs, cs.map Child.raw, ((Content.elementOk_iff _ _ _ _).mp ho).1,
    ((Content.elementOk_iff _ _ _ _).mp ho).2, validAll_children cs, ht⟩

/-- Place an element in a child position. -/
def Child.of {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (h : ctx.admitsWith t (rawAttrs e.attrs) = true := by decide) : Child ctx :=
  ⟨e.toRaw, e.valid h⟩

/-- A text run, where the base names text. -/
def Child.text {ctx : Ctx} (s : String) (h : ctx.admits .pcdata = true := by decide) : Child ctx :=
  ⟨.text s, Content.validIn_text ctx s h⟩

/-- A named entity reference, admitted where text is. -/
def Child.entity {ctx : Ctx} (name : String) (h : ctx.admits .pcdata = true := by decide) : Child ctx :=
  ⟨.entity name, Content.validIn_entity ctx name h⟩

/-- An element placed at a position, as a document of the checker. -/
def Element.toDoc {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (h : ctx.admitsWith t (rawAttrs e.attrs) = true := by decide) : Content.Doc ctx :=
  ⟨e.toRaw, e.valid h⟩

end Whatwg.Html
