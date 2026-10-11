import Whatwg.Svg.Schema.Universe
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Value.Length
import Whatwg.Svg.Value.Refusal

/-!
# Whatwg.Svg.Value.Attribute

Owner: which grammar judges the value of which attribute (slices S4b to S4d of
`docs/SVG-PACKAGE-PLAN.md`; rulings SV-13, SV-30, SV-31 and SV-32; point G5 of
`docs/research/2026-10-11-svg-seat-guidance-3.md`). `kindOf` is the one table: it gives the
kind of an attribute's value on an element. A `ValueKind` has its typed value, `carrier`, and
its grammar. `valueOk` and `explainValue` are the two functions the seam calls, and both read
the table.

| Attribute | On | Kind | Source at the pin |
| --- | --- | --- | --- |
| `d` | any element | `pathData` | `PathDataBNF`, `master/paths.html` |
| `points` | any element | `points` | `DataTypePoints`, `master/shapes.html` |
| `viewBox` | any element | `viewBox` | `ViewBoxAttribute`, `master/coords.html` |
| `transform` | any element | `transformList` | `svg-syntax`, CSS Transforms 1 |
| `gradientTransform`, `patternTransform` | any element | `transformList` | the same |
| `x1`, `y1`, `x2`, `y2` | `line` | `length` | `LineElementX1Attribute`, `master/shapes.html` |

A row says "any element" where the name has one grammar wherever it stands. The four names of
the last row have a second definition, on `linearGradient`, in a chapter that is not sealed. So
the table gives them a kind on `line` alone, where the sealed table of `line` states it (ruling
SV-32).

An attribute with no row takes any text. That is a limit of this package and no statement of
SVG. The geometry properties (`x`, `y`, `width`, `height`, `cx`, `cy`, `r`, `rx` and `ry`) are
lengths in SVG, and their values are stated in the chapter `geometry.html`, which is not
sealed: they are not judged. A colour, a paint and a URL are not judged.

`valueOk_print` says that the text of a typed value is admitted wherever the table gives its
kind. It is the grammar's `check_print`, so it holds for every value and evaluates no text.
`explainValue` is the located refusal of a value: the offset at which no reading of the
grammar continues (`Whatwg/Svg/Value/Refusal.lean`). `explainValue_eq_none_iff` says that it
is absent exactly when `valueOk` holds.

What this module does not claim: that an attribute stands on the right element, which
`Whatwg.Svg.Content.attrOk` judges by the name; or that a value that passes means what its
author intends.
-/

namespace Whatwg.Svg.Value

open Whatwg.Svg.Schema

/-! ## The kinds -/

/-- A kind of attribute value that this package holds a grammar for. -/
inductive ValueKind where
  /-- Path data, or `none`. -/
  | pathData
  /-- A list of coordinate pairs. -/
  | points
  /-- A rectangle of user space. -/
  | viewBox
  /-- A list of transform functions. -/
  | transformList
  /-- A number with a unit, a percentage or a number. -/
  | length
  deriving DecidableEq, Repr, Inhabited

/-- The typed value of a kind. -/
abbrev ValueKind.carrier : ValueKind → Type
  | .pathData => PathData
  | .points => Points
  | .viewBox => ViewBox
  | .transformList => TransformList
  | .length => Length

/-- The grammar of a kind. -/
abbrev ValueKind.grammar : (k : ValueKind) → Grammar k.carrier
  | .pathData => PathData.grammar
  | .points => Points.grammar
  | .viewBox => ViewBox.grammar
  | .transformList => TransformList.grammar
  | .length => Length.grammar

/-- The kind of an attribute's value on an element, where the sealed text states its grammar
and this package holds it. -/
def kindOf (t : Tag) : Attr → Option ValueKind
  | .d => some .pathData
  | .points => some .points
  | .viewBox => some .viewBox
  | .transform => some .transformList
  | .gradientTransform => some .transformList
  | .patternTransform => some .transformList
  | .x1 | .y1 | .x2 | .y2 =>
    match t with
    | .line => some .length
    | _ => none
  | _ => none

/-! ## The check -/

/-- The value is of the attribute's grammar, where the table gives the attribute a kind. -/
def valueOk (t : Tag) (a : Attr) (text : List Char) : Bool :=
  match kindOf t a with
  | some k => k.grammar.check text
  | none => true

/-- The same, by the names of the element and of the attribute. A name that is no element's or
no attribute's has no kind: the seam judges the names, and this function passes the value. -/
def valueOkByName (element name value : List Char) : Bool :=
  match Tag.ofChars? element, Attr.ofChars? name with
  | some t, some a => valueOk t a value
  | _, _ => true

/-- By their own names, an element and an attribute give the table's judgment. -/
theorem valueOkByName_chars (t : Tag) (a : Attr) (text : List Char) :
    valueOkByName t.chars a.chars text = valueOk t a text := by
  rw [valueOkByName, Tag.ofChars?_chars, Attr.ofChars?_chars]

/-- Node V2 at the table: the text of a typed value is admitted wherever the table gives its
kind. -/
theorem valueOk_print {t : Tag} {a : Attr} {k : ValueKind} (h : kindOf t a = some k)
    (v : k.carrier) : valueOk t a (k.grammar.print v) = true := by
  rw [valueOk, h]
  exact k.grammar.check_print v

/-! ## The located refusal -/

/-- Where a value is refused: the offset of the first character that no reading of the
attribute's grammar continues. `none` when the value passes. -/
def explainValue (t : Tag) (a : Attr) (text : List Char) : Option Nat :=
  match kindOf t a with
  | some k => k.grammar.explain text
  | none => none

/-- Node V6: the refusal of a value is absent exactly when the value passes. -/
theorem explainValue_eq_none_iff (t : Tag) (a : Attr) (text : List Char) :
    explainValue t a text = none ↔ valueOk t a text = true := by
  rw [explainValue, valueOk]
  cases kindOf t a with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some k => exact k.grammar.explain_eq_none_iff text

/-- The same, by the names of the element and of the attribute. -/
def explainValueByName (element name value : List Char) : Option Nat :=
  match Tag.ofChars? element, Attr.ofChars? name with
  | some t, some a => explainValue t a value
  | _, _ => none

theorem explainValueByName_eq_none_iff (element name value : List Char) :
    explainValueByName element name value = none ↔ valueOkByName element name value = true := by
  rw [explainValueByName, valueOkByName]
  cases Tag.ofChars? element with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some t =>
    cases Attr.ofChars? name with
    | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | some a => exact explainValue_eq_none_iff t a value

end Whatwg.Svg.Value
