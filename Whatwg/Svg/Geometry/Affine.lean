import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Geometry.Arith

/-!
# Whatwg.Svg.Geometry.Affine

Owner: what a transform does to a point, and the transforms a program builds most (slice S10
of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-46). The authority is CSS Transforms 1, sealed at
`vendor/w3c-csswg-drafts-50337328/css-transforms-1/Overview.bs`, which the `transform`
attribute of SVG 2 follows:

- `matrix(a, b, c, d, e, f)` sends `(x, y)` to `(a x + c y + e, b x + d y + f)`;
- `translate(tx, ty)` adds, and `ty` is zero when it is not written;
- `scale(sx, sy)` multiplies, and `sy` is `sx` when it is not written;
- a list of functions is the product of their matrices from left to right, so on a point the
  last function of the list applies first.

`Matrix` is the six numbers, with `apply` and the product. `Transform.image?` is one function
on a point, and `TransformList.image?` a list on a point, in that order. Each is `none` for
`rotate`, `skewX` and `skewY`: their matrices hold a sine, a cosine or a tangent of the angle,
which no value of this package has exactly.

`PanZoom` is the transform of a view that is moved and scaled, the three numbers of d3-zoom:
`translate(x, y) scale(k)`. It composes, and its list means what its `apply` computes.

`Transform.shift` and `Transform.zoom` are the two functions a program writes most.

The laws are in `Whatwg/Svg/Geometry/Affine/Laws.lean`. They are equations of values, because the
sum and the product of `Whatwg/Svg/Geometry/Arith.lean` are exact as operations on values.

What this module does not claim: a rotation or a skew on a point; the inverse of a transform,
which divides; or the transform that a `viewBox` makes of a viewport, which divides too.

Copyright (c) 2026 World Wide Web Consortium. This file includes material copied from or
derived from CSS Transforms Module Level 1, https://drafts.csswg.org/css-transforms-1/, under
the W3C Software and Document License, https://www.w3.org/copyright/software-license-2023/
-/

namespace Whatwg.Svg.Value

/-! ## A matrix -/

/-- The six numbers of `matrix(a, b, c, d, e, f)`: the map of `(x, y)` to
`(a x + c y + e, b x + d y + f)`. -/
structure Matrix where
  a : Decimal
  b : Decimal
  c : Decimal
  d : Decimal
  e : Decimal
  f : Decimal
  deriving DecidableEq, Repr, Inhabited

namespace Matrix

/-- The matrix that moves no point. -/
def identity : Matrix := ⟨1, 0, 0, 1, 0, 0⟩

/-- The image of a point. -/
def apply (m : Matrix) (p : Point) : Point :=
  ⟨m.a * p.x + m.c * p.y + m.e, m.b * p.x + m.d * p.y + m.f⟩

/-- The product: the map that applies `n` and then `m`. -/
def mul (m n : Matrix) : Matrix :=
  ⟨m.a * n.a + m.c * n.b, m.b * n.a + m.d * n.b, m.a * n.c + m.c * n.d,
    m.b * n.c + m.d * n.d, m.a * n.e + m.c * n.f + m.e, m.b * n.e + m.d * n.f + m.f⟩

instance : Mul Matrix := ⟨mul⟩

/-- The matrix as a transform function. -/
def toTransform (m : Matrix) : Transform := .matrix m.a m.b m.c m.d m.e m.f

end Matrix

/-! ## A transform on a point -/

namespace Transform

/-- `translate(x, y)`. -/
def shift (x y : Decimal) : Transform := .translate x (some y)

/-- `scale(k)`: the same factor on both axes. -/
def zoom (k : Decimal) : Transform := .scale k none

/-- The matrix of a function, and none for a rotation or a skew. -/
def matrix? : Transform → Option Matrix
  | .matrix a b c d e f => some ⟨a, b, c, d, e, f⟩
  | .translate tx ty => some ⟨1, 0, 0, 1, tx, ty.getD 0⟩
  | .scale sx sy => some ⟨sx, 0, 0, sy.getD sx, 0, 0⟩
  | .rotate _ _ => none
  | .skewX _ => none
  | .skewY _ => none

/-- The image of a point under one function, and none for a rotation or a skew. -/
def image? : Transform → Point → Option Point
  | .matrix a b c d e f, p => some ((Matrix.mk a b c d e f).apply p)
  | .translate tx ty, p => some ⟨p.x + tx, p.y + ty.getD 0⟩
  | .scale sx sy, p => some ⟨sx * p.x, sy.getD sx * p.y⟩
  | .rotate _ _, _ => none
  | .skewX _, _ => none
  | .skewY _, _ => none

end Transform

namespace TransformList

/-- The image of a point under a list of functions: the last function applies first. -/
def image? : TransformList → Point → Option Point
  | [], p => some p
  | t :: rest, p => (image? rest p).bind t.image?

/-- The matrix of a list: the product of its functions' matrices from left to right. -/
def matrix? : TransformList → Option Matrix
  | [] => some .identity
  | t :: rest => t.matrix?.bind fun m => (matrix? rest).map fun n => m * n

end TransformList

/-! ## A view that is moved and scaled -/

/-- The transform `translate(x, y) scale(k)`: a point is scaled by `k` and then moved by
`(x, y)`. -/
structure PanZoom where
  /-- The scale. -/
  k : Decimal
  /-- The move along `x`. -/
  x : Decimal
  /-- The move along `y`. -/
  y : Decimal
  deriving DecidableEq, Repr, Inhabited

namespace PanZoom

/-- The view that moves no point. -/
def identity : PanZoom := ⟨1, 0, 0⟩

/-- The image of a point: scaled, then moved. -/
def apply (t : PanZoom) (p : Point) : Point := ⟨t.k * p.x + t.x, t.k * p.y + t.y⟩

/-- The transform that applies `a` and then `b`. -/
def andThen (a b : PanZoom) : PanZoom := ⟨b.k * a.k, b.k * a.x + b.x, b.k * a.y + b.y⟩

/-- The view scaled by a further factor about its own origin. -/
def scale (t : PanZoom) (s : Decimal) : PanZoom := ⟨t.k * s, t.x, t.y⟩

/-- The view moved by an offset given in its own coordinates. -/
def translate (t : PanZoom) (dx dy : Decimal) : PanZoom := ⟨t.k, t.k * dx + t.x, t.k * dy + t.y⟩

/-- The same view with no zero at the end of a fraction: what a view that was computed should
be before it is written, since `0.5 + 0.5` is the value `1.0`. -/
def tidy (t : PanZoom) : PanZoom := ⟨t.k.trim, t.x.trim, t.y.trim⟩

/-- The list that writes the view: `translate(x, y) scale(k)`. -/
def toList (t : PanZoom) : TransformList := [.shift t.x t.y, .zoom t.k]

/-- The matrix of the view. -/
def toMatrix (t : PanZoom) : Matrix := ⟨t.k, 0, 0, t.k, t.x, t.y⟩

end PanZoom

end Whatwg.Svg.Value
