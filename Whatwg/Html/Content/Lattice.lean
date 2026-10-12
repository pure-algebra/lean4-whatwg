import Whatwg.Html.Schema

/-!
# Whatwg.Html.Content.Lattice

Reflection over the finite universes, and the inclusion facts of the
standard's categories and bases (node L1 of the proof graph in
`docs/HTML-PACKAGE-PLAN.md`, slice H7 under rulings HP-12 and HP-13). Each
fact is one evaluation over `Tag.all` or `Base.all`, by `decide`, and the
reflection lemmas carry it to every tag and every base.
-/

namespace Whatwg.Html.Schema

/-- The markup name of a tag as a total function, `pcdata` for text. -/
def Tag.markupText (t : Tag) : String := t.markupName.getD t.variantName

end Whatwg.Html.Schema

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-! ## Reflection over the finite universes -/

theorem Tag.mem_all (t : Tag) : t ∈ Tag.all := by cases t <;> decide
theorem Base.mem_all (b : Base) : b ∈ Base.all := by cases b <;> decide

theorem Tag.all_length : Tag.all.length = 116 := by decide
theorem Tag.all_nodup : Tag.all.Nodup := by decide +kernel
theorem Base.all_nodup : Base.all.Nodup := by decide +kernel

/-- Reflection over tags: a boolean predicate that `List.all` accepts on
`Tag.all` holds at every tag. -/
theorem forall_tag_of_all (p : Tag → Bool) (h : Tag.all.all p = true) :
    ∀ t : Tag, p t = true :=
  fun t => List.all_eq_true.mp h t (Tag.mem_all t)

/-- The same reflection at `Prop`, for a decidable predicate on tags. -/
theorem forall_tag_of_decide (p : Tag → Prop) [DecidablePred p]
    (h : Tag.all.all (fun t => decide (p t)) = true) : ∀ t : Tag, p t :=
  fun t => of_decide_eq_true (forall_tag_of_all (fun t => decide (p t)) h t)

/-- Reflection over bases. -/
theorem forall_base_of_all (p : Base → Bool) (h : Base.all.all p = true) :
    ∀ b : Base, p b = true :=
  fun b => List.all_eq_true.mp h b (Base.mem_all b)

/-- Reflection over pairs of a base and a tag. -/
theorem forall_base_tag_of_all (p : Base → Tag → Bool)
    (h : Base.all.all (fun b => Tag.all.all (p b)) = true) :
    ∀ (b : Base) (t : Tag), p b t = true :=
  fun b t => forall_tag_of_all (p b) (forall_base_of_all _ h b) t

/-- Reflection over the element rows. -/
theorem forall_elements_of_all (p : Element → Bool) (h : elements.all p = true) :
    ∀ e, e ∈ elements → p e = true :=
  fun e he => List.all_eq_true.mp h e he

/-! ## Inclusion -/

/-- `a ⊆ b` for membership functions. -/
def SubsetOf (a b : Tag → Bool) : Prop := ∀ t : Tag, a t = true → b t = true

theorem subsetOf_of_all {a b : Tag → Bool}
    (h : Tag.all.all (fun t => !a t || b t) = true) : SubsetOf a b := by
  intro t ha
  have := forall_tag_of_all _ h t
  rw [ha, Bool.not_true, Bool.false_or] at this
  exact this

theorem eq_of_all {a b : Tag → Bool}
    (h : Tag.all.all (fun t => a t == b t) = true) : ∀ t, a t = b t :=
  fun t => eq_of_beq (forall_tag_of_all _ h t)

/-! ## The categories of the standard -/

/-- Phrasing content is flow content, with one exception the standard's own
table makes at the pin: `selectedcontent` is listed as phrasing content and
not as flow content (its only context is inside a `button` of a `select`). -/
theorem cats_phrasing_subset_flow : ∀ t, t ≠ .selectedcontent → Cats.phrasing t = true → Cats.flow t = true := by
  have h := forall_tag_of_all (fun t => t == .selectedcontent || !Cats.phrasing t || Cats.flow t) (by decide +kernel)
  intro t hne hp
  have := h t
  rw [beq_false_of_ne hne, hp, Bool.not_true, Bool.or_self, Bool.false_or] at this
  exact this
theorem selectedcontent_phrasing_not_flow :
    Cats.phrasing .selectedcontent = true ∧ Cats.flow .selectedcontent = false := by decide
theorem cats_heading_subset_flow : SubsetOf Cats.heading Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_sectioning_subset_flow : SubsetOf Cats.sectioning Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_embedded_subset_phrasing : SubsetOf Cats.embedded Cats.phrasing := subsetOf_of_all (by decide +kernel)
theorem cats_interactive_subset_flow : SubsetOf Cats.interactive Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_scriptSupporting_subset_phrasing : SubsetOf Cats.scriptSupporting Cats.phrasing :=
  subsetOf_of_all (by decide +kernel)
theorem cats_media_subset_embedded : SubsetOf Cats.media Cats.embedded := subsetOf_of_all (by decide +kernel)

/-! ## The bases -/

/-- The `flow` base is the flow category and text; `phrasing` likewise. -/
theorem flow_eq : ∀ t, Bases.flow t = (t == .pcdata || Cats.flow t) := eq_of_all (by decide +kernel)
theorem phrasing_eq : ∀ t, Bases.phrasing t = (t == .pcdata || Cats.phrasing t) := eq_of_all (by decide +kernel)
theorem nothing_empty : ∀ t, Bases.nothing t = false := eq_of_all (by decide +kernel)
theorem text_eq : ∀ t, Bases.text t = (t == .pcdata) := eq_of_all (by decide +kernel)
theorem document_eq : ∀ t, Bases.document t = (t == .html) := eq_of_all (by decide +kernel)

/-- Every void element's own base is `nothing`. -/
theorem void_ownBase_nothing : ∀ t : Tag, t.isVoid = true → t.ownBase = .nothing := by
  have h := forall_tag_of_all (fun t => !t.isVoid || (t.ownBase == .nothing)) (by decide +kernel)
  intro t hv
  have := h t
  rw [hv, Bool.not_true, Bool.false_or] at this
  exact eq_of_beq this

/-- No void element is transparent, and none has labelled children. -/
theorem void_not_transparent : ∀ t : Tag, t.isVoid = true → t.isTransparent = false := by
  have h := forall_tag_of_all (fun t => !t.isVoid || !t.isTransparent) (by decide +kernel)
  intro t hv
  have := h t
  rw [hv, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
  exact this
theorem void_labelled_nil : ∀ t : Tag, t.isVoid = true → t.labelled = [] := by
  have h := forall_tag_of_all (fun t => !t.isVoid || (t.labelled == [])) (by decide +kernel)
  intro t hv
  have := h t
  rw [hv, Bool.not_true, Bool.false_or] at this
  exact eq_of_beq this

/-- Every element's markup name reads back to it. -/
theorem ofName?_markupName : ∀ t : Tag, ∀ m, t.markupName = some m → Tag.ofName? m = some t := by
  have h := forall_tag_of_all (fun t => match t.markupName with
    | some m => Tag.ofName? m == some t
    | none => true) (by decide +kernel)
  intro t m hm
  have := h t
  rw [hm] at this
  exact eq_of_beq this

theorem void_br : Tag.isVoid .br = true := by decide
theorem void_div_false : Tag.isVoid .div = false := by decide

end Whatwg.Html.Content
