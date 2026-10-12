import Whatwg.Svg.Geometry.Affine
import Whatwg.Svg.Geometry.Arith.Laws

/-!
# Whatwg.Svg.Geometry.Affine.Laws

Owner: the laws of `Whatwg/Svg/Geometry/Affine.lean` (slice S10 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-46). The authority for the order of a transform list is CSS Transforms 1, sealed at
`vendor/w3c-csswg-drafts-50337328/css-transforms-1/Overview.bs`, under
`transformation-matrix-computation`: the matrices multiply from left to right, so on a point
the last function applies first. Each law here is an equation of values: the product of two
matrices on a point is the one after the other, a list on a point is its functions from the
right, and a view that is moved and scaled composes and means what its list means.
-/

namespace Whatwg.Svg.Value

/-! ## A matrix -/

namespace Matrix

/-- The product written with `*` is `Matrix.mul`. -/
theorem mul_def (m n : Matrix) : m * n = Matrix.mul m n := rfl

/-- The product of two matrices sends a point where the right one and then the left one do. -/
theorem apply_mul (m n : Matrix) (p : Point) : (m * n).apply p = m.apply (n.apply p) := by
  simp only [mul_def, mul, apply, Decimal.mul_add, Decimal.add_mul, Decimal.mul_assoc]
  congr 1 <;> ac_rfl

/-- The product of three matrices does not depend on which two are multiplied first. -/
theorem mul_assoc (l m n : Matrix) : l * m * n = l * (m * n) := by
  simp only [mul_def, mul, Decimal.mul_add, Decimal.add_mul, Decimal.mul_assoc]
  congr 1 <;> ac_rfl

end Matrix

/-! ## A transform on a point -/

namespace Transform

/-- A `matrix` function sends a point where its matrix does. -/
theorem image?_matrix (a b c d e f : Decimal) (p : Point) :
    (Transform.matrix a b c d e f).image? p = some ((Matrix.mk a b c d e f).apply p) := rfl

/-- A shift adds its two numbers to the coordinates of a point. -/
theorem image?_shift (x y : Decimal) (p : Point) :
    (Transform.shift x y).image? p = some ⟨p.x + x, p.y + y⟩ := rfl

/-- A zoom multiplies both coordinates of a point by its factor. -/
theorem image?_zoom (k : Decimal) (p : Point) :
    (Transform.zoom k).image? p = some ⟨k * p.x, k * p.y⟩ := rfl

/-- A function has no image of a point exactly when it has no matrix. -/
theorem image?_eq_none_iff_matrix? (t : Transform) (p : Point) :
    t.image? p = none ↔ t.matrix? = none := by
  cases t <;> simp only [image?, matrix?, reduceCtorEq]

end Transform

/-! ## A list on a point -/

namespace TransformList

/-- The empty list moves no point. -/
theorem image?_nil (p : Point) : TransformList.image? [] p = some p := rfl

/-- The first function of a list applies after the rest of the list. -/
theorem image?_cons (t : Transform) (ts : TransformList) (p : Point) :
    TransformList.image? (t :: ts) p = (TransformList.image? ts p).bind t.image? := rfl

/-- Of two lists joined, the one that is written first applies last. -/
theorem image?_append (ts us : TransformList) (p : Point) :
    TransformList.image? (ts ++ us) p =
      (TransformList.image? us p).bind (TransformList.image? ts) := by
  induction ts with
  | nil =>
    rw [List.nil_append]
    cases TransformList.image? us p <;> rfl
  | cons t ts ih =>
    rw [List.cons_append, image?_cons, ih]
    cases TransformList.image? us p <;> rfl

/-- A list of one function sends a point where the function does. -/
theorem image?_singleton (t : Transform) (p : Point) :
    TransformList.image? [t] p = t.image? p := rfl

end TransformList

/-! ## A view that is moved and scaled -/

namespace PanZoom

/-- The list that writes a view sends a point where the view does. -/
theorem image?_toList (t : PanZoom) (p : Point) :
    TransformList.image? t.toList p = some (t.apply p) := rfl

/-- One view and then another sends a point where the first and then the second do. -/
theorem apply_andThen (a b : PanZoom) (p : Point) :
    (a.andThen b).apply p = b.apply (a.apply p) := by
  show (⟨b.k * a.k * p.x + (b.k * a.x + b.x), b.k * a.k * p.y + (b.k * a.y + b.y)⟩ : Point) =
    ⟨b.k * (a.k * p.x + a.x) + b.x, b.k * (a.k * p.y + a.y) + b.y⟩
  rw [Decimal.mul_add, Decimal.mul_add, Decimal.mul_assoc, Decimal.mul_assoc,
    Decimal.add_assoc, Decimal.add_assoc]

/-- Three views in a row do not depend on which two are composed first. -/
theorem andThen_assoc (a b c : PanZoom) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := by
  show (⟨c.k * (b.k * a.k), c.k * (b.k * a.x + b.x) + c.x, c.k * (b.k * a.y + b.y) + c.y⟩ :
      PanZoom) =
    ⟨c.k * b.k * a.k, c.k * b.k * a.x + (c.k * b.x + c.x), c.k * b.k * a.y + (c.k * b.y + c.y)⟩
  rw [Decimal.mul_add, Decimal.mul_add, Decimal.mul_assoc, Decimal.mul_assoc,
    Decimal.mul_assoc, Decimal.add_assoc, Decimal.add_assoc]

/-- A view scaled by a further factor sends a point where the view sends the scaled point. -/
theorem apply_scale (t : PanZoom) (s : Decimal) (p : Point) :
    (t.scale s).apply p = t.apply (Point.scale s p) := by
  show (⟨t.k * s * p.x + t.x, t.k * s * p.y + t.y⟩ : Point) =
    ⟨t.k * (s * p.x) + t.x, t.k * (s * p.y) + t.y⟩
  rw [Decimal.mul_assoc, Decimal.mul_assoc]

/-- A view moved by an offset sends a point where the view sends the point moved by it. -/
theorem apply_translate (t : PanZoom) (dx dy : Decimal) (p : Point) :
    (t.translate dx dy).apply p = t.apply (p + ⟨dx, dy⟩) := by
  show (⟨t.k * p.x + (t.k * dx + t.x), t.k * p.y + (t.k * dy + t.y)⟩ : Point) =
    ⟨t.k * (p.x + dx) + t.x, t.k * (p.y + dy) + t.y⟩
  rw [Decimal.mul_add, Decimal.mul_add, Decimal.add_assoc, Decimal.add_assoc]

end PanZoom

end Whatwg.Svg.Value
