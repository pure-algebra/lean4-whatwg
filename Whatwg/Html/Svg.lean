import Whatwg.Html.Content.Context
import Whatwg.Html.Schema.Foreign
import Whatwg.Svg.Content.Context
import Whatwg.Svg.Value.Attribute

/-!
# Whatwg.Html.Svg

Owner: the seam, the rules by which an HTML tree holds SVG content (slice S3b of
`docs/SVG-PACKAGE-PLAN.md`; points T1 and T2 of its section 3.1). The HTML Standard owns them:
where `svg` stands, where the namespace changes, and how a foreign element is written. SVG 2
owns the elements themselves, and they are the library `Whatwg.Svg`.

Validation is one top-down pass over a tree, and its state is a position. The seam's position,
`Pos`, is a sum: an HTML position, or an SVG position with the HTML exclusions that pass
through the SVG subtree (ruling SV-9). `Pos.child` is the transition. It is total: a name that
no rule knows leads to a position that admits nothing.

The standard's tree construction has its own automaton on namespaces, `Ns.step`: `svg` enters
the SVG namespace, and `foreignObject`, `desc` and `title` return to HTML. It is written here
from the generated `Whatwg.Html.Schema.Foreign`. `Pos.child_ns` says that the checker's
transition and this automaton agree on every name (node T2 of the plan's section 6). The
printer's state holds `Ns`, so the checker and the printer cannot disagree about a node's
namespace.

Anchors in the pinned `source`: the category lists of "Kinds of content", which name `SVG svg`
under flow, phrasing, embedded and palpable content; the section "SVG" of the embedded content
chapter, which checks the children of `foreignObject` as flow content and those of `title` as
phrasing content; the definition of an HTML integration point; and the rules "in foreign
content". The children of `desc` are checked as phrasing content by the owner's ruling SV-8:
the standard names `desc` an integration point and states no content for it.

What this module does not claim: that `Ns.step` is the parser's function on every tree. It is
on a tree the checker accepts. `math` enters MathML in the parser and is refused here (ruling
SV-10). A start tag of `Foreign.breakout` ends foreign content in the parser, and no SVG
element has such a name (`no_svg_tag_breaks_out`), so the checker refuses one below `svg`.
No parser exists in this package (ruling HP-8).
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Svg.Data (NameTable)

/-! ## The namespace automaton -/

/-- A namespace of the tree construction that this package models. -/
inductive Ns where
  | html | svg
  deriving DecidableEq, Repr, Inhabited

/-- The name of an SVG element that is an HTML integration point. -/
def isIntegrationName (name : String) : Bool :=
  Foreign.svgIntegrationPoints.any fun point => point.toList == name.toList

/-- The namespace of an element's children, from the element's namespace and name: `svg`
enters SVG, and an integration point returns to HTML. -/
def Ns.step : Ns → String → Ns
  | .html, name =>
    match Tag.ofForeignName? name with
    | some .svg => .svg
    | _ => .html
  | .svg, name => if isIntegrationName name then .html else .svg

/-! ## The position -/

/-- A position in a tree that may hold SVG: an HTML position, or a position in an SVG subtree
with the HTML exclusions inherited from outside it. -/
inductive Pos where
  | html (c : Ctx)
  | svg (c : Whatwg.Svg.Content.Ctx) (excl : Exclusions)
  deriving DecidableEq, Repr, Inhabited

namespace Pos

/-- The namespace of the position. -/
def ns : Pos → Ns
  | .html _ => .html
  | .svg _ _ => .svg

/-- The HTML exclusions in force at the position. -/
def excl : Pos → Exclusions
  | .html c => c.excl
  | .svg _ x => x

/-- The position with other exclusions. -/
def withExcl : Pos → Exclusions → Pos
  | .html c, x => .html { c with excl := x }
  | .svg c _, x => .svg c x

end Pos

/-- The HTML base below an SVG integration point: flow content below `foreignObject`, and
phrasing content below `title` and `desc` (ruling SV-8). -/
def integrationBase : Whatwg.Svg.Schema.Tag → Option Base
  | .foreignObject => some .flow
  | .desc => some .phrasing
  | .title => some .phrasing
  | _ => none

/-- The position of an element's children, from the element's position and name. -/
def Pos.child : Pos → String → Pos
  | .html c, name =>
    match Tag.ofName? name with
    | some t => .html (c.child t)
    | none =>
      match Tag.ofForeignName? name with
      | some .svg => .svg (Whatwg.Svg.Content.Ctx.outside.child .svg) (c.child .svg).excl
      | _ => .html ⟨.nothing, c.excl, []⟩
  | .svg c x, name =>
    match Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t =>
      match integrationBase t with
      | some base => .html ⟨base, x, []⟩
      | none => .svg (c.child t) x
    | none => .svg Whatwg.Svg.Content.Ctx.outside x

/-! ## Names -/

/-- No foreign element of the category lists has the name of an HTML element. -/
theorem ofChars?_eq_none_of_foreign {cs : List Char} {f : Tag}
    (h : Tag.ofForeignChars? cs = some f) : Tag.ofChars? cs = none := by
  unfold Tag.ofForeignChars? at h
  split at h
  · rfl
  · rfl
  · exact nomatch h

/-- An HTML element's name is no foreign element's. -/
theorem ofForeignName?_eq_none_of_element {name : String} {t : Tag}
    (h : Tag.ofName? name = some t) : Tag.ofForeignName? name = none := by
  cases hf : Tag.ofForeignName? name with
  | none => rfl
  | some f =>
    have hnone : Tag.ofName? name = none := ofChars?_eq_none_of_foreign hf
    rw [hnone] at h
    exact nomatch h

/-- The integration points of the hand table are those the standard lists: `integrationBase`
answers a base exactly at the SVG elements of `Foreign.svgIntegrationPoints`. -/
theorem integrationBase_isSome (t : Whatwg.Svg.Schema.Tag) :
    (integrationBase t).isSome =
      Foreign.svgIntegrationPoints.any fun point => point.toList == t.chars :=
  Whatwg.Svg.Data.Universe.forall_of_decide
    (fun t : Whatwg.Svg.Schema.Tag => (integrationBase t).isSome =
      Foreign.svgIntegrationPoints.any fun point => point.toList == t.chars)
    (by decide +kernel) t

/-- Every integration point the standard lists is an SVG element of the schema. -/
theorem integrationPoints_are_tags :
    (Foreign.svgIntegrationPoints.all fun point =>
      (Whatwg.Svg.Schema.Tag.ofChars? point.toList).isSome) = true := by
  decide +kernel

/-- Node N3: no SVG element has the name of a start tag that ends foreign content, nor the
name `font`, which ends it with some attributes. -/
theorem no_svg_tag_breaks_out :
    (Whatwg.Svg.Schema.Tag.all.all fun t =>
      !(("font" :: Foreign.breakout).any fun name => name.toList == t.chars)) = true := by
  decide +kernel

/-- The lower-case form of a name, as the tokenizer makes it. -/
def lowerChars (cs : List Char) : List Char := cs.map Char.toLower

/-- The name that a table restores from a lower-case name: the table's answer, or the name
itself. -/
def restore (table : List (String × String)) (lower : List Char) : List Char :=
  match table.find? fun row => row.1.toList == lower with
  | some row => row.2.toList
  | none => lower

/-- Node N2 for elements: the tree construction restores every SVG element name from its
lower-case form. -/
theorem restore_tag (t : Whatwg.Svg.Schema.Tag) :
    restore Foreign.svgTagNames (lowerChars t.chars) = t.chars :=
  Whatwg.Svg.Data.Universe.forall_of_decide
    (fun t : Whatwg.Svg.Schema.Tag =>
      restore Foreign.svgTagNames (lowerChars t.chars) = t.chars)
    (by decide +kernel) t

/-- Node N2 for attributes: "adjust SVG attributes" restores every SVG attribute name from its
lower-case form. -/
theorem restore_attr (a : Whatwg.Svg.Schema.Attr) :
    restore Foreign.svgAttrNames (lowerChars a.chars) = a.chars :=
  Whatwg.Svg.Data.Universe.forall_of_decide
    (fun a : Whatwg.Svg.Schema.Attr =>
      restore Foreign.svgAttrNames (lowerChars a.chars) = a.chars)
    (by decide +kernel) a
/-! ## The transition, case by case -/

theorem Pos.child_html_element {c : Ctx} {name : String} {t : Tag}
    (h : Tag.ofName? name = some t) : Pos.child (.html c) name = .html (c.child t) := by
  simp only [Pos.child, h]

theorem Pos.child_html_svg {c : Ctx} {name : String} (h : Tag.ofName? name = none)
    (hf : Tag.ofForeignName? name = some .svg) :
    Pos.child (.html c) name =
      .svg (Whatwg.Svg.Content.Ctx.outside.child .svg) (c.child .svg).excl := by
  simp only [Pos.child, h, hf]

theorem Pos.child_html_other {c : Ctx} {name : String} (h : Tag.ofName? name = none)
    (hf : Tag.ofForeignName? name ≠ some .svg) :
    Pos.child (.html c) name = .html ⟨.nothing, c.excl, []⟩ := by
  simp only [Pos.child, h]

theorem Pos.child_svg_integration {c : Whatwg.Svg.Content.Ctx} {x : Exclusions} {name : String}
    {t : Whatwg.Svg.Schema.Tag} {base : Base}
    (h : Whatwg.Svg.Schema.Tag.ofChars? name.toList = some t)
    (hb : integrationBase t = some base) : Pos.child (.svg c x) name = .html ⟨base, x, []⟩ := by
  simp only [Pos.child, h, hb]

theorem Pos.child_svg_element {c : Whatwg.Svg.Content.Ctx} {x : Exclusions} {name : String}
    {t : Whatwg.Svg.Schema.Tag} (h : Whatwg.Svg.Schema.Tag.ofChars? name.toList = some t)
    (hb : integrationBase t = none) : Pos.child (.svg c x) name = .svg (c.child t) x := by
  simp only [Pos.child, h, hb]

theorem Pos.child_svg_other {c : Whatwg.Svg.Content.Ctx} {x : Exclusions} {name : String}
    (h : Whatwg.Svg.Schema.Tag.ofChars? name.toList = none) :
    Pos.child (.svg c x) name = .svg Whatwg.Svg.Content.Ctx.outside x := by
  simp only [Pos.child, h]

theorem Ns.step_html_svg {name : String} (hf : Tag.ofForeignName? name = some .svg) :
    Ns.step .html name = .svg := by
  simp only [Ns.step, hf]

theorem Ns.step_html_other {name : String} (hf : Tag.ofForeignName? name ≠ some .svg) :
    Ns.step .html name = .html := by
  simp only [Ns.step]

/-- In the SVG namespace, a name is an integration point exactly when the hand table gives
its element a base. -/
theorem isIntegrationName_of_tag {name : String} {t : Whatwg.Svg.Schema.Tag}
    (h : Whatwg.Svg.Schema.Tag.ofChars? name.toList = some t) :
    isIntegrationName name = (integrationBase t).isSome := by
  rw [integrationBase_isSome t, Whatwg.Svg.Schema.Tag.ofChars?_exact h]
  rfl

/-- A name that is no SVG element is no integration point. -/
theorem isIntegrationName_of_unknown {name : String}
    (h : Whatwg.Svg.Schema.Tag.ofChars? name.toList = none) : isIntegrationName name = false := by
  cases hany : isIntegrationName name with
  | false => rfl
  | true =>
    obtain ⟨point, hmem, heq⟩ := List.any_eq_true.mp hany
    have hpoint := List.all_eq_true.mp integrationPoints_are_tags point hmem
    rw [eq_of_beq heq, h] at hpoint
    exact nomatch hpoint

/-! ## The transition and the namespace automaton agree -/

/-- Node T2: the checker's transition and the namespace automaton agree on every name. -/
theorem Pos.child_ns (p : Pos) (name : String) : (p.child name).ns = p.ns.step name := by
  cases p with
  | html c =>
    cases ht : Tag.ofName? name with
    | some t =>
      have hf : Tag.ofForeignName? name ≠ some .svg := by
        rw [ofForeignName?_eq_none_of_element ht]
        exact fun h => nomatch h
      rw [Pos.child_html_element ht, Pos.ns, Pos.ns, Ns.step_html_other hf]
    | none =>
      cases hd : decide (Tag.ofForeignName? name = some .svg) with
      | true =>
        have hf := of_decide_eq_true hd
        rw [Pos.child_html_svg ht hf, Pos.ns, Pos.ns, Ns.step_html_svg hf]
      | false =>
        have hf := of_decide_eq_false hd
        rw [Pos.child_html_other ht hf, Pos.ns, Pos.ns, Ns.step_html_other hf]
  | svg c x =>
    cases ht : Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t =>
      have hname := isIntegrationName_of_tag ht
      cases hb : integrationBase t with
      | some base =>
        rw [hb, Option.isSome_some] at hname
        rw [Pos.child_svg_integration ht hb, Pos.ns, Pos.ns, Ns.step, hname, if_pos rfl]
      | none =>
        rw [hb, Option.isSome_none] at hname
        rw [Pos.child_svg_element ht hb, Pos.ns, Pos.ns, Ns.step, hname,
          if_neg Bool.false_ne_true]
    | none =>
      rw [Pos.child_svg_other ht, Pos.ns, Pos.ns, Ns.step, isIntegrationName_of_unknown ht,
        if_neg Bool.false_ne_true]

/-! ## The exclusions -/

theorem Exclusions.le_refl (x : Exclusions) : x.le x = true := by
  cases x
  simp only [Exclusions.le, Exclusions.flags, List.zip_cons_cons, List.zip_nil_right,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (Bool.eq_false_or_eq_true _).symm

/-- Node X1: the HTML exclusions only grow along the transition, in both namespaces. -/
theorem Pos.excl_le_child (p : Pos) (name : String) : p.excl.le (p.child name).excl = true := by
  cases p with
  | html c =>
    cases ht : Tag.ofName? name with
    | some t =>
      rw [Pos.child_html_element ht]
      exact child_excl_le c t
    | none =>
      cases hd : decide (Tag.ofForeignName? name = some .svg) with
      | true =>
        rw [Pos.child_html_svg ht (of_decide_eq_true hd)]
        exact child_excl_le c .svg
      | false =>
        rw [Pos.child_html_other ht (of_decide_eq_false hd)]
        exact Exclusions.le_refl _
  | svg c x =>
    cases ht : Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t =>
      cases hb : integrationBase t with
      | some base =>
        rw [Pos.child_svg_integration ht hb]
        exact Exclusions.le_refl _
      | none =>
        rw [Pos.child_svg_element ht hb]
        exact Exclusions.le_refl _
    | none =>
      rw [Pos.child_svg_other ht]
      exact Exclusions.le_refl _
end Whatwg.Html.Content
