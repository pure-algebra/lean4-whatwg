import Whatwg.Svg.Schema.Universe
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Transform

/-!
# Whatwg.Svg.Value.Attribute

Owner: which grammar judges the value of which attribute (slices S4b and S4c of
`docs/SVG-PACKAGE-PLAN.md`; rulings SV-13 and SV-30). `valueOk` is the one function the seam
calls. Six attributes have a grammar here:

- `d`: path data, or `none` (`PathData.grammar`);
- `points` (`Points.grammar`);
- `viewBox` (`ViewBox.grammar`);
- `transform`, `gradientTransform` and `patternTransform` (`TransformList.grammar`).

An attribute with no grammar here takes any text. That is a limit of this package and no
statement of SVG: a length, a colour, a paint and a URL are not judged.

Each law below says that the text of a typed value is admitted as its attribute's value. It
is the grammar's `check_print`, so it holds for every value and evaluates no text.

What this module does not claim: that an attribute stands on the right element, which
`Whatwg.Svg.Content.attrOk` judges by the name; or that a value that passes means what its
author intends.
-/

namespace Whatwg.Svg.Value

open Whatwg.Svg.Schema

/-- The value is of the attribute's grammar, where this package holds the grammar. -/
def valueOk : Attr → List Char → Bool
  | .d, text => PathData.grammar.check text
  | .points, text => Points.grammar.check text
  | .viewBox, text => ViewBox.grammar.check text
  | .transform, text => TransformList.grammar.check text
  | .gradientTransform, text => TransformList.grammar.check text
  | .patternTransform, text => TransformList.grammar.check text
  | _, _ => true

/-- The same, by the attribute's name. A name that is no attribute's has no grammar: the seam
judges the name, and this function passes the value. -/
def valueOkByName (name value : List Char) : Bool :=
  match Attr.ofChars? name with
  | some a => valueOk a value
  | none => true

/-- By its own name, an attribute's value is judged by its grammar. -/
theorem valueOkByName_chars (a : Attr) (text : List Char) :
    valueOkByName a.chars text = valueOk a text := by
  rw [valueOkByName, Attr.ofChars?_chars]

/-- The text of typed path data is a value of `d`. -/
theorem valueOk_d (p : PathData) : valueOk .d (PathData.grammar.print p) = true :=
  PathData.grammar.check_print p

/-- The text of typed points is a value of `points`. -/
theorem valueOk_points (p : Points) : valueOk .points (Points.grammar.print p) = true :=
  Points.grammar.check_print p

/-- The text of a typed rectangle is a value of `viewBox`. -/
theorem valueOk_viewBox (v : ViewBox) : valueOk .viewBox (ViewBox.grammar.print v) = true :=
  ViewBox.grammar.check_print v

/-- The text of a typed transform list is a value of `transform`. -/
theorem valueOk_transform (ts : TransformList) :
    valueOk .transform (TransformList.grammar.print ts) = true :=
  TransformList.grammar.check_print ts

/-- The text of a typed transform list is a value of `gradientTransform`. -/
theorem valueOk_gradientTransform (ts : TransformList) :
    valueOk .gradientTransform (TransformList.grammar.print ts) = true :=
  TransformList.grammar.check_print ts

/-- The text of a typed transform list is a value of `patternTransform`. -/
theorem valueOk_patternTransform (ts : TransformList) :
    valueOk .patternTransform (TransformList.grammar.print ts) = true :=
  TransformList.grammar.check_print ts

end Whatwg.Svg.Value
