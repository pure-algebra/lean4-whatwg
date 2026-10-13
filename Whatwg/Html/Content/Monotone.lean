import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Automaton

/-!
# Whatwg.Html.Content.Monotone

Owner: what a position admits when a part of the question is not known (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entry W9 of `docs/research/2026-10-12-whatwg-requests.md`). The
checker reads an element's attributes and the base of its position. A program that builds a
page often knows neither in full: an element is a variable, so its attributes are not written
out, and a list of children was checked as flow content before anyone said that it would stand
in a `details`. This module holds the two laws that answer for every case at once.

- **Whatever the attributes.** `attrBlind base t` is a closed test: no attribute can add the
  element to the excluded interactive content, and none is needed for it to be content of the
  base. `Ctx.admitsWith_of_admits` says that such an element is admitted with any attributes
  where its tag is admitted. An `a` is interactive content only with `href`, and `Ctx.admits`
  reads it as if it had one, so an `a` that `Ctx.admits` takes is taken with or without. This
  is `Ctx.admitsWith_unread` of `Whatwg/Html/Node/Splice.lean` without its premise that no
  category reads an attribute.
- **A wider base.** `Base.under narrow wide` is a closed test that a tree which may stand at a
  position of the base `narrow` may stand at one of the base `wide`, the exclusions and the
  labelled children being the same. `validIn_of_under` and `validAll_of_under` are the law. So
  flow content that was checked once is content of a `details` after its `summary`.
- **The tag of a valid child.** `base_contains_of_valid`: at a position with no labelled
  children, the tag a valid node counts as in an ordered model is one the base holds.

What this module does not claim: the converse of either law. A tree may stand at the wider
base and not at the narrower, and an element may be admitted with its attributes where
`Ctx.admits` refuses its tag (an `a` with no `href` inside a `button`).
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode)

/-! ## Whatever the attributes -/

/-- No attribute changes whether the element may stand at a position of this base: its row
states no condition on interactive content, or the element is interactive content in the
category table, which is how `Ctx.admits` reads it; and the base asks no condition of it. -/
def attrBlind (b : Base) (t : Tag) : Bool :=
  (t.interactiveIf.isNone || Cats.interactive t) && (b != .flow || t.flowIf.isNone) &&
    (b != .phrasing || t.phrasingIf.isNone)

/-- With attributes an element is interactive content only if the table says that it can be. -/
theorem interactive_of_interactiveWith {t : Tag}
    (h : (t.interactiveIf.isNone || Cats.interactive t) = true) (attrs : List (String × String))
    (hw : Ctx.interactiveWith t attrs = true) : Cats.interactive t = true := by
  unfold Ctx.interactiveWith at hw
  cases hcond : t.interactiveIf with
  | none =>
    rw [hcond] at hw
    exact hw
  | some cond =>
    rw [hcond] at h
    exact h

/-- What the exclusions refuse of an element with attributes, they refuse of its tag. -/
theorem excluded_of_excludedWith (x : Exclusions) {t : Tag} {attrs : List (String × String)}
    (hi : Ctx.interactiveWith t attrs = true → Cats.interactive t = true)
    (h : Ctx.excludedWith x t attrs = true) : Ctx.excluded x t = true := by
  rw [Ctx.excludedWith_eq_spec] at h
  rw [Ctx.excluded_eq_spec]
  unfold Ctx.excludedWithSpec Ctx.hitsWith at h
  unfold Ctx.excludedSpec
  have hhits : Ctx.hits t = Cats.interactive t :: (Ctx.hits t).tail := rfl
  rw [hhits]
  cases hflags : x.flags with
  | nil =>
    rw [hflags] at h
    exact h
  | cons flag rest =>
    rw [hflags] at h
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.elim (fun first => Or.inl ⟨first.1, hi first.2⟩) Or.inr

/-- Where the base asks no condition of the element, it holds the element with its attributes
exactly when it holds its tag. -/
theorem Ctx.baseContainsWith_of_blind {b : Base} {t : Tag}
    (hflow : (b != .flow || t.flowIf.isNone) = true)
    (hphrasing : (b != .phrasing || t.phrasingIf.isNone) = true) (attrs : List (String × String)) :
    Ctx.baseContainsWith b t attrs = b.contains t := by
  unfold Ctx.baseContainsWith
  cases b with
  | flow =>
    have hnone : t.flowIf = none := Option.isNone_iff_eq_none.mp hflow
    rw [hnone]
    exact Bool.and_true _
  | phrasing =>
    have hnone : t.phrasingIf = none := Option.isNone_iff_eq_none.mp hphrasing
    rw [hnone]
    cases t.flowIf <;> exact Bool.and_true _
  | _ => exact Bool.and_true _

/-- **Whatever its attributes, an element is admitted where its tag is**, when no attribute can
change the answer. The premises are closed tests, and the attributes are not among them. -/
theorem Ctx.admitsWith_of_admits (c : Ctx) (t : Tag) (attrs : List (String × String))
    (hb : attrBlind c.base t = true) (ha : c.admits t = true) : c.admitsWith t attrs = true := by
  unfold attrBlind at hb
  rw [Bool.and_eq_true, Bool.and_eq_true] at hb
  unfold Ctx.admits at ha
  unfold Ctx.admitsWith
  rw [Bool.and_eq_true, Bool.not_eq_true'] at ha ⊢
  rw [Ctx.baseContainsWith_of_blind hb.1.2 hb.2]
  refine ⟨ha.1, ?_⟩
  cases hw : Ctx.excludedWith c.excl t attrs with
  | false => rfl
  | true =>
    have hx := excluded_of_excludedWith c.excl (interactive_of_interactiveWith hb.1.1 attrs) hw
    rw [ha.2] at hx
    exact Bool.noConfusion hx

/-! ## A wider base -/

/-- A tree that may stand at a position of the base `narrow` may stand at one of the base
`wide`: the two are one base; or `wide` holds every tag of `narrow`, asks no condition of an
element (it is neither `flow` nor `phrasing`), takes a comment, and neither is the base that a
transparent child changes (`metadata`, under `noscript`). -/
def Base.under (narrow wide : Base) : Bool :=
  narrow == wide ||
    (narrow != .metadata && wide != .metadata && wide != .flow && wide != .phrasing &&
      wide != .nothing && Tag.all.all fun t => !narrow.contains t || wide.contains t)

/-- The premises of the law of a wider base, as propositions. -/
structure Base.Within (narrow wide : Base) : Prop where
  holds : ∀ t, narrow.contains t = true → wide.contains t = true
  narrowPlain : narrow ≠ .metadata
  widePlain : wide ≠ .metadata
  notFlow : wide ≠ .flow
  notPhrasing : wide ≠ .phrasing
  notNothing : wide ≠ .nothing

theorem Base.within_of_under {narrow wide : Base} (hne : narrow ≠ wide)
    (h : Base.under narrow wide = true) : Base.Within narrow wide := by
  unfold Base.under at h
  rw [beq_false_of_ne hne, Bool.false_or] at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hn, hw⟩, hflow⟩, hphrasing⟩, hnothing⟩, hall⟩ := h
  exact ⟨fun t ht => by
    have hat := forall_tag_of_all _ hall t
    rw [ht, Bool.not_true, Bool.false_or] at hat
    exact hat, hn, hw, hflow, hphrasing, hnothing⟩

/-- No transparent element changes a base other than `metadata`. -/
theorem Base.override_of_plain {b : Base} (h : b ≠ .metadata) (t : Tag) : Base.override b t = none := by
  cases b with
  | metadata => exact absurd rfl h
  | _ => rfl

namespace Base.Within

variable {narrow wide : Base}

/-- The wider base holds an element with its attributes where the narrower does. -/
theorem baseContainsWith (w : Base.Within narrow wide) {t : Tag} {attrs : List (String × String)}
    (h : Ctx.baseContainsWith narrow t attrs = true) : Ctx.baseContainsWith wide t attrs = true := by
  have hcontains : narrow.contains t = true := by
    unfold Ctx.baseContainsWith at h
    exact (Bool.and_eq_true _ _ ▸ h).1
  rw [Ctx.baseContainsWith_of_blind (by rw [bne_iff_ne.mpr w.notFlow]; rfl)
    (by rw [bne_iff_ne.mpr w.notPhrasing]; rfl)]
  exact w.holds t hcontains

theorem admitsWith (w : Base.Within narrow wide) {x : Exclusions} {extra : List Tag} {t : Tag}
    {attrs : List (String × String)} (h : Ctx.admitsWith ⟨narrow, x, extra⟩ t attrs = true) :
    Ctx.admitsWith ⟨wide, x, extra⟩ t attrs = true := by
  unfold Ctx.admitsWith at h ⊢
  rw [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  exact ⟨h.1.elim (fun hb => Or.inl (w.baseContainsWith hb)) Or.inr, h.2⟩

theorem admits (w : Base.Within narrow wide) {x : Exclusions} {extra : List Tag} {t : Tag}
    (h : Ctx.admits ⟨narrow, x, extra⟩ t = true) : Ctx.admits ⟨wide, x, extra⟩ t = true := by
  unfold Ctx.admits at h ⊢
  rw [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  exact ⟨h.1.elim (fun hb => Or.inl (w.holds t hb)) Or.inr, h.2⟩

/-- The children of a child stand at one position under either base, unless the child is
transparent; then they stand at the two bases again. -/
theorem child_eq (w : Base.Within narrow wide) (x : Exclusions) (extra : List Tag) (t : Tag) :
    (t.isTransparent = false ∧
        (⟨narrow, x, extra⟩ : Ctx).child t = (⟨wide, x, extra⟩ : Ctx).child t) ∨
      ((⟨narrow, x, extra⟩ : Ctx).child t = ⟨narrow, x.union t.ownExcl, t.labelled⟩ ∧
        (⟨wide, x, extra⟩ : Ctx).child t = ⟨wide, x.union t.ownExcl, t.labelled⟩) := by
  cases ht : t.isTransparent with
  | false =>
    refine Or.inl ⟨rfl, ?_⟩
    simp only [Ctx.child, ht, Bool.false_eq_true, ↓reduceIte]
  | true =>
    refine Or.inr ⟨?_, ?_⟩
    · simp only [Ctx.child, ht, ↓reduceIte, Base.override_of_plain w.narrowPlain, Option.getD_none]
    · simp only [Ctx.child, ht, ↓reduceIte, Base.override_of_plain w.widePlain, Option.getD_none]

end Base.Within

mutual

/-- The law of a wider base at one node, from its premises. -/
theorem validIn_of_within {narrow wide : Base} (w : Base.Within narrow wide) :
    ∀ (x : Exclusions) (extra : List Tag) (node : RawNode),
      validIn ⟨narrow, x, extra⟩ node = true → validIn ⟨wide, x, extra⟩ node = true
  | x, extra, .element name attrs children => by
    intro h
    cases hname : Tag.ofName? name with
    | some t =>
      rw [validIn_element_eq _ hname] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨⟨⟨hadmit, hattrs⟩, hseq⟩, hchildren⟩ := h
      refine ⟨⟨⟨w.admitsWith hadmit, hattrs⟩, ?_⟩, ?_⟩
      · rcases w.child_eq x extra t with ⟨_, hsame⟩ | ⟨hn, hw⟩
        · rw [← hsame]
          exact hseq
        · rw [hn] at hseq
          rw [hw]
          exact seqOk_mono w.holds t children hseq
      · rcases w.child_eq x extra t with ⟨_, hsame⟩ | ⟨hn, hw⟩
        · rw [← hsame]
          exact hchildren
        · rw [hn] at hchildren
          rw [hw]
          exact validAll_of_within w _ _ children hchildren
    | none =>
      cases hforeign : decide (Tag.ofForeignName? name = some .svg) with
      | true =>
        have hsvg := of_decide_eq_true hforeign
        rw [validIn_svg _ hname hsvg] at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨⟨w.admitsWith h.1.1, h.1.2⟩, h.2⟩
      | false =>
        rw [validIn_unknown _ hname (of_decide_eq_false hforeign)] at h
        exact Bool.noConfusion h
  | x, extra, .text content => by
    intro h
    rw [validIn, validAt_text] at h ⊢
    exact w.admits h
  | x, extra, .entity name => by
    intro h
    rw [validIn, validAt_entity] at h ⊢
    exact w.admits h
  | x, extra, .comment content => by
    intro _
    rw [validIn, validAt_comment]
    exact bne_iff_ne.mpr w.notNothing

/-- The same over a list of nodes. -/
theorem validAll_of_within {narrow wide : Base} (w : Base.Within narrow wide) :
    ∀ (x : Exclusions) (extra : List Tag) (nodes : List RawNode),
      validAll ⟨narrow, x, extra⟩ nodes = true → validAll ⟨wide, x, extra⟩ nodes = true
  | _, _, [] => fun _ => validAll_nil _
  | x, extra, node :: rest => fun h =>
    validAll_cons _ node rest
      (validIn_of_within w x extra node ((validAll_cons_iff _ node rest).mp h).1)
      (validAll_of_within w x extra rest ((validAll_cons_iff _ node rest).mp h).2)

end

/-- **A tree that may stand at a position may stand at the same position with a wider base.**
The premise is a closed test of the two bases. -/
theorem validIn_of_under {narrow wide : Base} (h : Base.under narrow wide = true) (x : Exclusions)
    (extra : List Tag) (node : RawNode) (hvalid : validIn ⟨narrow, x, extra⟩ node = true) :
    validIn ⟨wide, x, extra⟩ node = true := by
  cases hsame : decide (narrow = wide) with
  | true =>
    have heq := of_decide_eq_true hsame
    rw [← heq]
    exact hvalid
  | false =>
    exact validIn_of_within (Base.within_of_under (of_decide_eq_false hsame) h) x extra node hvalid

/-- The same over a list of nodes. -/
theorem validAll_of_under {narrow wide : Base} (h : Base.under narrow wide = true) (x : Exclusions)
    (extra : List Tag) (nodes : List RawNode) (hvalid : validAll ⟨narrow, x, extra⟩ nodes = true) :
    validAll ⟨wide, x, extra⟩ nodes = true := by
  cases hsame : decide (narrow = wide) with
  | true =>
    have heq := of_decide_eq_true hsame
    rw [← heq]
    exact hvalid
  | false =>
    exact validAll_of_within (Base.within_of_under (of_decide_eq_false hsame) h) x extra nodes hvalid

/-! ## The tag of a valid child -/

/-- At a position with no labelled children, the tag that a valid node counts as in an ordered
model is one that the base holds. -/
theorem base_contains_of_valid {b : Base} {x : Exclusions} {node : RawNode}
    (h : validIn ⟨b, x, []⟩ node = true) {tag : Tag} (htag : RawNode.tag? node = some tag) :
    b.contains tag = true := by
  cases node with
  | element name attrs children =>
    have hread : (Tag.ofName? name).orElse (fun _ => Tag.ofForeignName? name) = some tag := htag
    cases hname : Tag.ofName? name with
    | some t =>
      rw [hname] at hread
      cases Option.some.inj hread
      rw [validIn_element_eq _ hname] at h
      simp only [Bool.and_eq_true] at h
      have hle := admitsWith_le_admits _ tag attrs h.1.1.1
      simpa only [List.contains_nil, Bool.or_false] using hle
    | none =>
      rw [hname] at hread
      cases hforeign : decide (Tag.ofForeignName? name = some .svg) with
      | true =>
        have hsvg := of_decide_eq_true hforeign
        have hfound : Tag.ofForeignName? name = some tag := hread
        rw [hsvg] at hfound
        cases Option.some.inj hfound
        rw [validIn_svg _ hname hsvg] at h
        simp only [Bool.and_eq_true] at h
        have hle := admitsWith_le_admits _ .svg attrs h.1.1
        simpa only [List.contains_nil, Bool.or_false] using hle
      | false =>
        rw [validIn_unknown _ hname (of_decide_eq_false hforeign)] at h
        exact Bool.noConfusion h
  | text content =>
    cases Option.some.inj htag
    rw [validIn, validAt_text] at h
    unfold Pos.textOk Ctx.admits at h
    simp only [Bool.and_eq_true, List.contains_nil, Bool.or_false] at h
    exact h.1
  | entity name =>
    cases Option.some.inj htag
    rw [validIn, validAt_entity] at h
    unfold Pos.textOk Ctx.admits at h
    simp only [Bool.and_eq_true, List.contains_nil, Bool.or_false] at h
    exact h.1
  | comment content => exact nomatch htag

/-- The same for every tag the model reads from a list of valid nodes. -/
theorem base_contains_of_validAll {b : Base} {x : Exclusions} : ∀ {nodes : List RawNode},
    validAll ⟨b, x, []⟩ nodes = true → ∀ tag ∈ childTags nodes, b.contains tag = true
  | [], _, tag, htag => nomatch htag
  | node :: rest, h, tag, htag => by
    have hboth := (validAll_cons_iff _ node rest).mp h
    unfold childTags at htag
    rw [List.filterMap_cons] at htag
    cases hnode : RawNode.tag? node with
    | none =>
      rw [hnode] at htag
      exact base_contains_of_validAll hboth.2 tag htag
    | some found =>
      rw [hnode] at htag
      rcases List.mem_cons.mp htag with hhere | hlater
      · rw [hhere]
        exact base_contains_of_valid hboth.1 hnode
      · exact base_contains_of_validAll hboth.2 tag hlater

end Whatwg.Html.Content
