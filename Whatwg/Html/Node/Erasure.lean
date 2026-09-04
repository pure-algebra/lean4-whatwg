import Whatwg.Html.Node.Combinators

/-!
# Whatwg.Html.Node.Erasure

What erasure forgets and keeps (node T2 and T4 of the proof graph in
`docs/HTML-PACKAGE-PLAN.md`): erasing a child returns the raw node it
carries; the erased element is an element node named by the tag's markup
name with the element's attributes and children unchanged; an element's
validity is `Element.valid` of `Whatwg.Html.Node.Typed`; and no child stands
under a void element.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx)

theorem Child.of_raw {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (h : ctx.admitsWith t (rawAttrs e.attrs) = true) : (Child.of e h).raw = e.toRaw := rfl

theorem Child.text_raw {ctx : Ctx} (s : String) (h : ctx.admits .pcdata = true) :
    (Child.text (ctx := ctx) s h).raw = .text s := rfl

theorem Child.entity_raw {ctx : Ctx} (name : String) (h : ctx.admits .pcdata = true) :
    (Child.entity (ctx := ctx) name h).raw = .entity name := rfl

/-- Erasure reads only the two data fields. -/
theorem Element.toRaw_congr {t : Tag} {c c' : Ctx} (e : Element t c) (e' : Element t c')
    (hattrs : e.attrs = e'.attrs) (hchildren : e.children = e'.children) : e.toRaw = e'.toRaw := by
  simp [Element.toRaw, hattrs, hchildren]

theorem Element.toRaw_tagName? {t : Tag} {ctx : Ctx} (e : Element t ctx) :
    e.toRaw.tagName? = some t.markupText := rfl

theorem Element.toRaw_childNodes {t : Tag} {ctx : Ctx} (e : Element t ctx) :
    e.toRaw.childNodes = e.children := rfl

theorem markupText_eq_markupName (t : Tag) (m : String) (h : t.markupName = some m) :
    t.markupText = m := by
  simp [Tag.markupText, h]

/-- Only text lacks a markup name, and text has no element row. -/
theorem markupName_isSome_eq_elementIndex?_isSome (t : Tag) :
    t.markupName.isSome = (Tag.elementIndex? t).isSome :=
  eq_of_beq <| Content.forall_tag_of_all
    (fun t => (Tag.markupName t).isSome == (Tag.elementIndex? t).isSome) (by decide) t

/-- No typed child can be placed under a void tag, in any context. -/
theorem no_child_under_void {ctx : Ctx} {t : Tag} (hv : t.isVoid = true)
    (c : Child (ctx.child t)) : False := by
  have := Content.validAll_void_nil ctx t hv [c.raw] (Content.validAll_cons _ _ _ c.valid rfl)
  simp at this

/-- A void element has no children, as a value. -/
theorem Element.children_nil_of_void {ctx : Ctx} {t : Tag} (hv : t.isVoid = true) (e : Element t ctx) :
    e.children = [] :=
  Content.validAll_void_nil ctx t hv e.children e.hchildren

theorem void_combinators_children_nil :
    (E.br (ctx := Ctx.flow)).children = [] ∧ (E.hr (ctx := Ctx.flow)).children = []
      ∧ (E.input (ctx := Ctx.flow)).children = []
      ∧ (E.img (ctx := Ctx.flow) [A.a_src "u", A.a_alt "a"]).children = [] := ⟨rfl, rfl, rfl, rfl⟩

end Whatwg.Html
