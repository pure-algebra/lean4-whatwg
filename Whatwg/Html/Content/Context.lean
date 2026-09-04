import Whatwg.Html.Content.Lattice

/-!
# Whatwg.Html.Content.Context

A context is a position in a document (ruling HP-13): the base its children
are drawn from, the descendant exclusions inherited from every ancestor,
and the labelled direct children its parent admits besides. `Ctx.admits`
decides whether a tag may stand at the position; `Ctx.child` computes the
context of an element's children: its own base (its context's, if it is
transparent, or the base override), its context's exclusions with its own
added, and its labelled children. This is transparent coherence and the
descendant restrictions in one definition: exclusions only accumulate
(`child_excl_le`), and a transparent element's children are checked
against its context's base with more excluded, never less.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-- A position in a document. -/
structure Ctx where
  base : Base
  excl : Exclusions := {}
  extra : List Tag := []
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Ctx

/-- Flow context, with nothing excluded. -/
def flow : Ctx := { base := .flow }
/-- Phrasing context. -/
def phrasing : Ctx := { base := .phrasing }
/-- Metadata context, the content of `head`. -/
def metadata : Ctx := { base := .metadata }
/-- The document root: `html` alone. -/
def document : Ctx := { base := .document }

/-- What each flag excludes, at a tag, in the field order of
`Exclusions.flags`. -/
def hits (t : Tag) : List Bool :=
  [Cats.interactive t, Cats.media t, Cats.heading t, Cats.sectioning t, t == .noscript, t == .dfn,
   t == .meter, t == .progress, t == .label, t == .form, t == .table, t == .header, t == .footer,
   t == .address, t == .a]

/-- The exclusions exclude the tag: some set flag hits it. This is the
specification, over the flag lists the lemmas reason in; `excludedFast`
below is the same test as a short-circuiting boolean, which the kernel
evaluates in a fifth of the time (performance review §3), and is what the
admission functions use. -/
def excludedSpec (x : Exclusions) (t : Tag) : Bool :=
  (x.flags.zip (hits t)).any fun p => p.1 && p.2

/-- `excludedSpec` as a short-circuiting boolean. -/
def excluded (x : Exclusions) (t : Tag) : Bool :=
  (x.interactive && Cats.interactive t) || (x.media && Cats.media t) ||
  (x.heading && Cats.heading t) || (x.sectioning && Cats.sectioning t) ||
  (x.noscript && t == .noscript) || (x.dfn && t == .dfn) || (x.meter && t == .meter) ||
  (x.progress && t == .progress) || (x.label && t == .label) || (x.form && t == .form) ||
  (x.table && t == .table) || (x.header && t == .header) || (x.footer && t == .footer) ||
  (x.address && t == .address) || (x.a && t == .a)

theorem excluded_eq_spec (x : Exclusions) (t : Tag) : excluded x t = excludedSpec x t := by
  cases x
  simp only [excluded, excludedSpec, Exclusions.flags, hits, List.zip_cons_cons, List.zip_nil_right,
    List.any_cons, List.any_nil, Bool.or_false]
  simp only [Bool.or_assoc]

/-- The tag may stand at the position: the base or the labelled extras name
it, and no inherited exclusion excludes it. This is the attribute-free
reading, in which every conditional category is read as holding. -/
def admits (c : Ctx) (t : Tag) : Bool :=
  (c.base.contains t || c.extra.contains t) && !excluded c.excl t

/-- Interactive content, given the element's attributes: the standard's
condition where its row states one (`a` with `href`, `input` not hidden,
`audio` and `video` with `controls`, `img` with `usemap`), the table otherwise. -/
def interactiveWith (t : Tag) (attrs : List (String × String)) : Bool :=
  match t.interactiveIf with
  | some cond => cond.holds attrs
  | none => Cats.interactive t

/-- Membership of a tag in a base, given its attributes: the flow and
phrasing bases consult the row's condition (`link` and `meta` are flow and
phrasing content with `itemprop`). -/
def baseContainsWith (b : Base) (t : Tag) (attrs : List (String × String)) : Bool :=
  b.contains t &&
    (match b, t.flowIf, t.phrasingIf with
      | .flow, some cond, _ => cond.holds attrs
      | .phrasing, _, some cond => cond.holds attrs
      | _, _, _ => true)

/-- What each flag excludes at a tag with the given attributes. -/
def hitsWith (t : Tag) (attrs : List (String × String)) : List Bool :=
  interactiveWith t attrs :: (hits t).tail

def excludedWithSpec (x : Exclusions) (t : Tag) (attrs : List (String × String)) : Bool :=
  (x.flags.zip (hitsWith t attrs)).any fun p => p.1 && p.2

def excludedWith (x : Exclusions) (t : Tag) (attrs : List (String × String)) : Bool :=
  (x.interactive && interactiveWith t attrs) || (x.media && Cats.media t) ||
  (x.heading && Cats.heading t) || (x.sectioning && Cats.sectioning t) ||
  (x.noscript && t == .noscript) || (x.dfn && t == .dfn) || (x.meter && t == .meter) ||
  (x.progress && t == .progress) || (x.label && t == .label) || (x.form && t == .form) ||
  (x.table && t == .table) || (x.header && t == .header) || (x.footer && t == .footer) ||
  (x.address && t == .address) || (x.a && t == .a)

theorem excludedWith_eq_spec (x : Exclusions) (t : Tag) (attrs : List (String × String)) :
    excludedWith x t attrs = excludedWithSpec x t attrs := by
  cases x
  simp only [excludedWith, excludedWithSpec, Exclusions.flags, hitsWith, hits, List.tail_cons,
    List.zip_cons_cons, List.zip_nil_right, List.any_cons, List.any_nil, Bool.or_false]
  simp only [Bool.or_assoc]

/-- The tag with these attributes may stand at the position. -/
def admitsWith (c : Ctx) (t : Tag) (attrs : List (String × String)) : Bool :=
  (baseContainsWith c.base t attrs || c.extra.contains t) && !excludedWith c.excl t attrs

/-- The context of an element's children. -/
def child (c : Ctx) (t : Tag) : Ctx :=
  { base := if t.isTransparent then (Base.override c.base t).getD c.base else t.ownBase
    excl := c.excl.union t.ownExcl
    extra := t.labelled }

/-- The context in prose, for messages. -/
def describe (c : Ctx) : String :=
  c.base.name ++ (match c.excl.names with
    | [] => ""
    | ns => ", excluding " ++ ", ".intercalate ns)

end Ctx

/-! ## Lemmas -/

/-- Over lists of flags: if every flag of `xs` is a flag of `ys`, a hit
through `xs` is a hit through `ys`. -/
theorem any_hit_mono : ∀ (xs ys hs : List Bool), xs.length = ys.length →
    ((xs.zip ys).all fun p => !p.1 || p.2) = true →
    ((xs.zip hs).any fun p => p.1 && p.2) = true →
    ((ys.zip hs).any fun p => p.1 && p.2) = true
  | [], _, _, _, _, hx => by simp at hx
  | _ :: _, [], _, hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, [], _, _, hx => by simp at hx
  | x :: xs, y :: ys, h :: hs, hlen, hle, hx => by
    simp only [List.zip_cons_cons, List.all_cons, List.any_cons, Bool.and_eq_true, Bool.or_eq_true] at hle hx ⊢
    rcases hx with hx | hx
    · left
      cases x <;> cases y <;> cases h <;> simp_all
    · right
      exact any_hit_mono xs ys hs (by simpa using hlen) hle.2 hx

theorem all_le_zipWith_or : ∀ (xs ys : List Bool),
    ((xs.zip (List.zipWith (· || ·) xs ys)).all fun p => !p.1 || p.2) = true
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨by cases x <;> cases y <;> rfl, all_le_zipWith_or xs ys⟩

theorem Exclusions.le_union_left (x y : Exclusions) : x.le (x.union y) = true := by
  simp only [Exclusions.le, Exclusions.flags_union]
  exact all_le_zipWith_or x.flags y.flags

/-- Exclusions only accumulate down the tree. -/
theorem child_excl_le (c : Ctx) (t : Tag) : c.excl.le (c.child t).excl = true :=
  Exclusions.le_union_left _ _

/-- Larger exclusions exclude more. -/
theorem excluded_mono {x y : Exclusions} (h : x.le y = true) (t : Tag)
    (hx : Ctx.excluded x t = true) : Ctx.excluded y t = true := by
  rw [Ctx.excluded_eq_spec] at hx ⊢
  exact any_hit_mono x.flags y.flags (Ctx.hits t) rfl h hx

/-- Admission is antitone in the exclusions, for one base and extras. -/
theorem admits_antitone {x y : Exclusions} (h : x.le y = true) (b : Base) (e : List Tag) (t : Tag)
    (hy : Ctx.admits ⟨b, y, e⟩ t = true) : Ctx.admits ⟨b, x, e⟩ t = true := by
  simp only [Ctx.admits, Bool.and_eq_true, Bool.not_eq_true'] at hy ⊢
  refine ⟨hy.1, ?_⟩
  cases hxt : Ctx.excluded x t with
  | false => rfl
  | true =>
    have := excluded_mono h t hxt
    rw [hy.2] at this
    exact absurd this (by decide)

/-- With no attributes, a conditional category holds only where its condition
holds of nothing; the attribute-free `admits` is not `admitsWith c t []` in
general, and the two are related only by `admitsWith_le_admits` below. -/
theorem admitsWith_le_admits (c : Ctx) (t : Tag) (attrs : List (String × String)) :
    Ctx.admitsWith c t attrs = true → (c.base.contains t || c.extra.contains t) = true := by
  simp only [Ctx.admitsWith, Ctx.baseContainsWith, Bool.and_eq_true, Bool.or_eq_true]
  intro h
  rcases h.1 with ⟨hb, _⟩ | he
  · exact Or.inl hb
  · exact Or.inr he

/-- A void element's children context admits nothing. -/
theorem void_child_admits_none (c : Ctx) (t : Tag) (hv : t.isVoid = true) (child : Tag) :
    (c.child t).admits child = false := by
  simp only [Ctx.admits, Ctx.child, void_not_transparent t hv, void_ownBase_nothing t hv,
    void_labelled_nil t hv, Bool.false_eq_true, ↓reduceIte, List.contains, List.elem_nil]
  simp [Base.contains, nothing_empty]

theorem void_child_admitsWith_none (c : Ctx) (t : Tag) (hv : t.isVoid = true) (child : Tag)
    (attrs : List (String × String)) : (c.child t).admitsWith child attrs = false := by
  simp only [Ctx.admitsWith, Ctx.baseContainsWith, Ctx.child, void_not_transparent t hv,
    void_ownBase_nothing t hv, void_labelled_nil t hv, Bool.false_eq_true, ↓reduceIte,
    List.contains, List.elem_nil]
  simp [Base.contains, nothing_empty]

/-- A transparent element's children are checked against its context's base
(or the override). -/
theorem child_base_transparent (c : Ctx) (t : Tag) (h : t.isTransparent = true) :
    (c.child t).base = (Base.override c.base t).getD c.base := by
  simp [Ctx.child, h]

end Whatwg.Html.Content
