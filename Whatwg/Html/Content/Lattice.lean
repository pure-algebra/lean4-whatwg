import Whatwg.Html.Schema

/-!
# Whatwg.Html.Content.Lattice

The inclusion lattice of the content sets (nodes L1 and L2 of the proof
graph in `docs/HTML-PACKAGE-PLAN.md`, slice H6.1 under ruling HP-12): the
generated sets of `Whatwg.Html.Schema.Families` are the closure of every
element's own set under the transparent exclusions, and each derived set
records the set it came from in `ContentSet.parent?`. The lattice facts are
therefore one statement each, quantified over the generated tables and
decided by reflection over `Tag.all` and `ContentSet.all`, rather than one
theorem per named family.

Every proof here is `decide +kernel` over finite lists: no axiom beyond
`propext` is minted, and the kernel does the evaluation.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-! ## Reflection over the finite universes -/

theorem Tag.mem_all (t : Tag) : t ∈ Tag.all := by cases t <;> decide
theorem ContentSet.mem_all (c : ContentSet) : c ∈ ContentSet.all := by cases c <;> decide

theorem Tag.all_length : Tag.all.length = 114 := by decide
theorem ContentSet.all_length : ContentSet.all.length = 87 := by decide
theorem Tag.all_nodup : Tag.all.Nodup := by decide +kernel
theorem ContentSet.all_nodup : ContentSet.all.Nodup := by decide +kernel

/-- Reflection over tags: a boolean predicate that `List.all` accepts on
`Tag.all` holds at every tag. -/
theorem forall_tag_of_all (p : Tag → Bool) (h : Tag.all.all p = true) :
    ∀ t : Tag, p t = true :=
  fun t => List.all_eq_true.mp h t (Tag.mem_all t)

/-- The same reflection at `Prop`, for a decidable predicate on tags. -/
theorem forall_tag_of_decide (p : Tag → Prop) [DecidablePred p]
    (h : Tag.all.all (fun t => decide (p t)) = true) : ∀ t : Tag, p t :=
  fun t => of_decide_eq_true (forall_tag_of_all (fun t => decide (p t)) h t)

/-- Reflection over content sets. -/
theorem forall_contentSet_of_all (p : ContentSet → Bool)
    (h : ContentSet.all.all p = true) : ∀ c : ContentSet, p c = true :=
  fun c => List.all_eq_true.mp h c (ContentSet.mem_all c)

/-- Reflection over pairs of a content set and a tag. -/
theorem forall_contentSet_tag_of_all (p : ContentSet → Tag → Bool)
    (h : ContentSet.all.all (fun c => Tag.all.all (p c)) = true) :
    ∀ (c : ContentSet) (t : Tag), p c t = true :=
  fun c t => forall_tag_of_all (p c) (forall_contentSet_of_all _ h c) t

/-- Reflection over the element rows. -/
theorem forall_elements_of_all (p : Element → Bool) (h : elements.all p = true) :
    ∀ e, e ∈ elements → p e = true :=
  fun e he => List.all_eq_true.mp h e he

/-! ## Inclusion -/

/-- `a ⊆ b` for membership functions. -/
def SubsetOf (a b : Tag → Bool) : Prop := ∀ t : Tag, a t = true → b t = true

/-- `a` and `b` share no tag. -/
def DisjointFrom (a b : Tag → Bool) : Prop := ∀ t : Tag, a t = true → b t = false

theorem subsetOf_of_all {a b : Tag → Bool}
    (h : Tag.all.all (fun t => !a t || b t) = true) : SubsetOf a b := by
  intro t ha
  have := forall_tag_of_all _ h t
  simpa [ha] using this

theorem disjointFrom_of_all {a b : Tag → Bool}
    (h : Tag.all.all (fun t => !a t || !b t) = true) : DisjointFrom a b := by
  intro t ha
  have := forall_tag_of_all _ h t
  simpa [ha] using this

theorem eq_of_all {a b : Tag → Bool}
    (h : Tag.all.all (fun t => a t == b t) = true) : ∀ t, a t = b t :=
  fun t => eq_of_beq (forall_tag_of_all _ h t)

/-! ## L1: a derived set is included in the set it came from -/

/-- Every set derived by a transparent exclusion is a subset of its parent:
the exclusions only remove. Quantified over the generated `parent?` table. -/
theorem parent_subset : ∀ (s p : ContentSet), s.parent? = some p →
    SubsetOf s.contains p.contains := by
  have h := forall_contentSet_of_all
    (fun s => match s.parent? with
      | some p => Tag.all.all (fun t => !s.contains t || p.contains t)
      | none => true) (by decide +kernel)
  intro s p hp
  have hs := h s
  rw [hp] at hs
  exact subsetOf_of_all hs

/-! ## The categories of the standard -/

/-- Phrasing content is flow content, with one exception the standard's own
table makes at the pin: `selectedcontent` is listed as phrasing content and
not as flow content (its only context is inside a `button` of a `select`). -/
theorem phrasing_subset_flow : ∀ t, t ≠ .selectedcontent → Sets.phrasing t = true → Sets.flow t = true := by
  have h := forall_tag_of_all (fun t => t == .selectedcontent || !Sets.phrasing t || Sets.flow t) (by decide +kernel)
  intro t hne hp
  have := h t
  simp [hne, hp] at this
  exact this
theorem cats_phrasing_subset_flow : ∀ t, t ≠ .selectedcontent → Cats.phrasing t = true → Cats.flow t = true := by
  have h := forall_tag_of_all (fun t => t == .selectedcontent || !Cats.phrasing t || Cats.flow t) (by decide +kernel)
  intro t hne hp
  have := h t
  simp [hne, hp] at this
  exact this
theorem selectedcontent_phrasing_not_flow : Cats.phrasing .selectedcontent = true ∧ Cats.flow .selectedcontent = false := by
  decide
theorem cats_heading_subset_flow : SubsetOf Cats.heading Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_sectioning_subset_flow : SubsetOf Cats.sectioning Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_embedded_subset_phrasing : SubsetOf Cats.embedded Cats.phrasing := subsetOf_of_all (by decide +kernel)
theorem cats_interactive_subset_flow : SubsetOf Cats.interactive Cats.flow := subsetOf_of_all (by decide +kernel)
theorem cats_scriptSupporting_subset_phrasing : SubsetOf Cats.scriptSupporting Cats.phrasing :=
  subsetOf_of_all (by decide +kernel)
theorem cats_media_subset_embedded : SubsetOf Cats.media Cats.embedded := subsetOf_of_all (by decide +kernel)

/-- The `flow` set is the flow category and text; `phrasing` likewise. -/
theorem flow_eq : ∀ t, Sets.flow t = (t == .pcdata || Cats.flow t) := eq_of_all (by decide +kernel)
theorem phrasing_eq : ∀ t, Sets.phrasing t = (t == .pcdata || Cats.phrasing t) :=
  eq_of_all (by decide +kernel)

/-! ## L2: the empty set, text, and void elements -/

theorem nothing_empty : ∀ t, Sets.nothing t = false := eq_of_all (by decide +kernel)
theorem text_eq : ∀ t, Sets.text t = (t == .pcdata) := eq_of_all (by decide +kernel)

/-- Every void element's content set is `nothing`, in the row form. -/
theorem void_content_nothing : ∀ e, e ∈ elements → e.tag.isVoid = true → e.content = .nothing := by
  have h := forall_elements_of_all (fun e => !e.tag.isVoid || e.content == .nothing) (by decide +kernel)
  intro e he hv
  have := h e he
  simpa [hv] using this

/-- The same through `Tag.content?`. -/
theorem void_content?_nothing : ∀ t : Tag, t.isVoid = true → Tag.content? t = some .nothing := by
  have h := forall_tag_of_all (fun t => !t.isVoid || (Tag.content? t == some .nothing)) (by decide +kernel)
  intro t hv
  have := h t
  simpa [hv] using this

/-- A void element has an element row. -/
theorem void_element_isSome : ∀ t : Tag, t.isVoid = true → (Tag.element? t).isSome = true := by
  have h := forall_tag_of_all (fun t => !t.isVoid || (Tag.element? t).isSome) (by decide +kernel) 
  intro t hv
  have := h t
  simpa [hv] using this

/-- Two probes of the lattice at named points, for the tests to cite. -/
theorem void_br : Tag.isVoid .br = true := by decide
theorem void_div_false : Tag.isVoid .div = false := by decide

end Whatwg.Html.Content
