import Whatwg.Html.Content.Lattice

/-!
# Whatwg.Html.Content.Transparent

Transparent coherence (node L3 of the proof graph in
`docs/HTML-PACKAGE-PLAN.md`, ruling HP-4) and the child-set resolver the
typed tree calls at every element node, over the schema generated from the
standard (ruling HP-12).

An element whose content-model sentence begins with `Transparent` takes its
content set from its context: the context minus what the sentence excludes
(interactive content and `a` under `a`; media elements under `audio` and
`video`; `noscript` under `noscript`; interactive content under `canvas`),
and never more. The generated `ContentSet.transparentPayload` table has an
entry exactly where a set names a transparent tag, and every payload is a
subset of its context: both are decided here over the whole table. That is
transparent coherence by construction, where TyXML's hand-spelled payload
table escaped its context for seventeen sets.

The resolver: a parent's children are checked against the payload the
context assigns it if there is one, else against the parent's own content
set (`Tag.content?`, a flat match proved equal to the row lookup). `none`
is returned only for text, which has no row.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-- A tag whose row is transparent. -/
def isTransparentTag (t : Tag) : Bool := (t.element?.map (·.transparent)).getD false

/-- The ten transparent elements at the pin. -/
theorem transparent_tags : Tag.all.filter isTransparentTag =
    [.a, .ins, .del, .object, .video, .audio, .map, .noscript, .slot, .canvas] := by decide +kernel

/-- The payload table has an entry exactly where the set names a
transparent tag. -/
theorem transparentPayload_isSome : ∀ (s : ContentSet) (t : Tag),
    (s.transparentPayload t).isSome = (s.contains t && isTransparentTag t) := by
  have h := forall_contentSet_tag_of_all
    (fun s t => (s.transparentPayload t).isSome == (s.contains t && isTransparentTag t)) (by decide +kernel)
  intro s t
  exact eq_of_beq (h s t)

/-- Every payload is a subset of its context: transparency never widens. -/
theorem transparentPayload_subset : ∀ (s : ContentSet) (t : Tag) (p : ContentSet),
    s.transparentPayload t = some p → SubsetOf p.contains s.contains := by
  have h := forall_contentSet_tag_of_all
    (fun s t => match s.transparentPayload t with
      | some p => Tag.all.all (fun v => !p.contains v || s.contains v)
      | none => true) (by decide +kernel)
  intro s t p hp
  have hs := h s t
  rw [hp] at hs
  exact subsetOf_of_all hs

/-- A void tag is never transparent, so no set assigns it a payload. -/
theorem transparentPayload_void : ∀ (s : ContentSet) (t : Tag),
    t.isVoid = true → s.transparentPayload t = none := by
  have h := forall_contentSet_tag_of_all
    (fun s t => !t.isVoid || (s.transparentPayload t).isNone) (by decide +kernel)
  intro s t hv
  have := h s t
  simpa [hv] using this

/-- The generated flat table `Tag.content?` agrees with the row lookup it
stands in for, at every tag. -/
theorem content?_eq_element? (t : Tag) :
    t.content? = (Tag.element? t).map Element.content := by
  have h := forall_tag_of_all
    (fun t => Tag.content? t == (Tag.element? t).map Element.content) (by decide +kernel) t
  exact eq_of_beq h

/-! ## The child-set resolver -/

/-- The content set the children of a `parent` element must satisfy when
that element sits in the context set `ctx`: the payload where the table
has one, else the parent's own content set; `none` only for text. -/
def resolveChildSet (parent : Tag) (ctx : ContentSet) : Option ContentSet :=
  match ctx.transparentPayload parent with
  | some payload => some payload
  | none => parent.content?

theorem resolveChildSet_payload (parent : Tag) (ctx : ContentSet) (p : ContentSet)
    (h : ctx.transparentPayload parent = some p) : resolveChildSet parent ctx = some p := by
  simp [resolveChildSet, h]

theorem resolveChildSet_element (parent : Tag) (ctx : ContentSet)
    (h : ctx.transparentPayload parent = none) :
    resolveChildSet parent ctx = (Tag.element? parent).map Element.content := by
  simp [resolveChildSet, h, content?_eq_element?]

/-- The resolver returns nothing only where the tag has no row. -/
theorem resolveChildSet_none (parent : Tag) (ctx : ContentSet)
    (h : resolveChildSet parent ctx = none) : (Tag.element? parent).map Element.content = none := by
  unfold resolveChildSet at h
  cases hp : ctx.transparentPayload parent with
  | some p => rw [hp] at h; exact absurd h (by simp)
  | none => rw [hp, content?_eq_element?] at h; exact h

/-- A void parent resolves to the empty content set in every context. -/
theorem resolveChildSet_void (parent : Tag) (ctx : ContentSet) (h : parent.isVoid = true) :
    resolveChildSet parent ctx = some .nothing := by
  rw [resolveChildSet_element parent ctx (transparentPayload_void ctx parent h)]
  rw [← content?_eq_element?]
  exact void_content?_nothing parent h

end Whatwg.Html.Content
