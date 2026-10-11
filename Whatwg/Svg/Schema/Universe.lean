import Whatwg.Svg.Data.Mask
import Whatwg.Svg.Data.NameTable
import Whatwg.Svg.Schema.Attributes
import Whatwg.Svg.Schema.ContentModel

/-!
# Whatwg.Svg.Schema.Universe

Owner: what the generated schema is an instance of (slice S3a of `docs/SVG-PACKAGE-PLAN.md`).
The generator writes data. This module, written by hand, says what the data is:

- the four enumerations are finite universes, indexed by Lean's own constructor index;
- the element names and the attribute names are name tables, and each is an exact embedding
  (node N1 of the plan's section 6): `ofChars?_chars` is the retraction and `ofChars?_exact`
  the exactness;
- each resolved set is the join of what the definitions state (node K1): `Tag.model_tags`,
  `Tag.model_text` and `Tag.attrs_eq`.

Every proof here is one evaluation over a census. The generic laws are in `Whatwg/Svg/Data/`.

What this module does not claim: that the definitions are the content model of SVG 2. It ties
the resolved values to the stated ones, and the drift gate ties the stated ones to the sealed
bytes.
-/

namespace Whatwg.Svg.Schema

open Whatwg.Svg.Data

/-! ## The universes -/

instance : Universe Tag := ⟨Tag.all, Tag.ctorIdx, by intro t; cases t <;> rfl⟩
instance : Universe Category := ⟨Category.all, Category.ctorIdx, by intro c; cases c <;> rfl⟩
instance : Universe Attr := ⟨Attr.all, Attr.ctorIdx, by intro a; cases a <;> rfl⟩
instance : Universe AttrCategory :=
  ⟨AttrCategory.all, AttrCategory.ctorIdx, by intro c; cases c <;> rfl⟩

/-! ## The name tables -/

/-- The name table of the elements: the generated spelling and the generated guess. -/
def Tag.table : NameTable Tag := ⟨Tag.chars, Tag.guess⟩

/-- The tag that a spelling names; `none` for any other list. Names are compared exactly:
`clippath` is not `clipPath`. -/
def Tag.ofChars? (s : List Char) : Option Tag := Tag.table.read s

/-- The element's name as a string, for a message. No judgment reads it. -/
def Tag.name (t : Tag) : String := String.ofList t.chars

theorem Tag.table_covers : Tag.table.covers = true := by decide +kernel

/-- The retraction: an element's spelling reads back as the element. -/
theorem Tag.ofChars?_chars (t : Tag) : Tag.ofChars? t.chars = some t :=
  NameTable.read_chars (NameTable.guess_chars Tag.table_covers) t

/-- Exactness: a spelling that reads as an element is that element's spelling. -/
theorem Tag.ofChars?_exact {s : List Char} {t : Tag} (h : Tag.ofChars? s = some t) :
    t.chars = s :=
  NameTable.read_exact h

/-- The name table of the attributes. -/
def Attr.table : NameTable Attr := ⟨Attr.chars, Attr.guess⟩

/-- The attribute that a spelling names; `none` for any other list. Names are compared
exactly: `viewbox` is not `viewBox`. -/
def Attr.ofChars? (s : List Char) : Option Attr := Attr.table.read s

/-- The attribute's name as a string, for a message. No judgment reads it. -/
def Attr.name (a : Attr) : String := String.ofList a.chars

theorem Attr.table_covers : Attr.table.covers = true := by decide +kernel

/-- The retraction: an attribute's spelling reads back as the attribute. -/
theorem Attr.ofChars?_chars (a : Attr) : Attr.ofChars? a.chars = some a :=
  NameTable.read_chars (NameTable.guess_chars Attr.table_covers) a

/-- Exactness: a spelling that reads as an attribute is that attribute's spelling. -/
theorem Attr.ofChars?_exact {s : List Char} {a : Attr} (h : Attr.ofChars? s = some a) :
    a.chars = s :=
  NameTable.read_exact h

/-! ## Resolution -/

/-- The members of every category of a set. -/
def Category.join (cs : Mask Category) : Mask Tag :=
  Category.all.foldl (fun acc c => if cs.mem c then acc.union c.members else acc) .empty

/-- The members of every attribute category of a set. -/
def AttrCategory.join (cs : Mask AttrCategory) : Mask Attr :=
  AttrCategory.all.foldl (fun acc c => if cs.mem c then acc.union c.members else acc) .empty

/-- A kind that admits character data. -/
def ContentKind.hasText : ContentKind → Bool
  | .anyOf => false
  | .textOrAnyOf => true
  | .text => true
  | .any => true

/-- The elements that a model's stated kind, categories and elements admit together: the
points of the Boolean algebra that the kinds spell. -/
def Model.resolvedTags (m : Model) : Mask Tag :=
  match m.kind with
  | .anyOf => (Category.join m.categories).union m.elements
  | .textOrAnyOf => (Category.join m.categories).union m.elements
  | .text => .empty
  | .any => .ofList Tag.all

/-- Each model's resolved set is the join of its stated categories and elements. -/
theorem Tag.model_tags (t : Tag) : t.model.tags = t.model.resolvedTags :=
  Universe.forall_of_decide (fun t : Tag => t.model.tags = t.model.resolvedTags)
    (by decide +kernel) t

/-- Each model's text bit is its kind's. -/
theorem Tag.model_text (t : Tag) : t.model.text = t.model.kind.hasText :=
  Universe.forall_of_decide (fun t : Tag => t.model.text = t.model.kind.hasText)
    (by decide +kernel) t

/-- Each element's attributes are its own and the members of its attribute categories. -/
theorem Tag.attrs_eq (t : Tag) :
    t.attrs = t.ownAttrs.union (AttrCategory.join t.attrCategories) :=
  Universe.forall_of_decide
    (fun t : Tag => t.attrs = t.ownAttrs.union (AttrCategory.join t.attrCategories))
    (by decide +kernel) t

end Whatwg.Svg.Schema
