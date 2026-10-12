import Whatwg.Svg.Geometry.Affine.Laws
import Whatwg.Svg.Geometry.Rational.Laws
import Whatwg.Svg.Geometry.Box

/-!
# Whatwg.Svg.Geometry.Affine.Map

Owner: an affine map of the plane as a thing to compute with (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-57). `Whatwg/Svg/Geometry/Affine.lean` has the six
numbers of `matrix(a, b, c, d, e, f)` as they are written, in `Decimal`: enough to compose
what a `transform` attribute says, and not to undo it, since the inverse divides.

`Affine` is the same six numbers in `Rat`. With them:

- the maps are a group where it matters: `identity` moves no point as an equation,
  the product is associative, and a map whose determinant is not zero has an `inverse`;
- a rotation is exact where its sine and cosine are rational: by quarter turns
  (`quarterTurns`), and by any angle whose half has a rational tangent (`turn`), which keeps
  every length;
- a cubic segment under a map is the segment of the mapped points (`Cubic.transform`), and its
  point at a parameter is the mapped point (`Cubic.transform_pointAt`): an affine map keeps
  steps (`apply_lerp`).

`Transform.affine?` reads one function of a `transform` attribute, and `TransformList.affine?`
a list, in the order that CSS Transforms 1 gives: the product from left to right. It reads
`rotate` by a multiple of ninety degrees, which the `Decimal` reading of slice S10 refuses, and
is `none` for any other angle and for a skew.

`Affine.fit` is the map of a view box onto a viewport that the chapter Coordinate Systems of
SVG 2 computes for `preserveAspectRatio` (sealed at
`vendor/w3c-svgwg-47e645ef/master/coords.html`, "computing the equivalent transform of an SVG
viewport"): one scale on both axes for `meet` and `slice`, and the view box placed at the
start, the middle or the end of the room that is left on each axis.

What this module does not claim: a rotation by an angle in degrees whose sine is not
rational; a skew; that `turn u` turns by a stated number of degrees, which takes an
arctangent.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- An affine map of the plane: `(x, y)` goes to `(a x + c y + e, b x + d y + f)`. -/
structure Affine where
  a : Rat
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Affine

/-- The map that moves no point. -/
def identity : Affine := ⟨1, 0, 0, 1, 0, 0⟩

/-- The image of a point. -/
def apply (m : Affine) (p : Vec) : Vec := ⟨m.a * p.x + m.c * p.y + m.e, m.b * p.x + m.d * p.y + m.f⟩

/-- The product: the map that applies `n` and then `m`. -/
def mul (m n : Affine) : Affine :=
  ⟨m.a * n.a + m.c * n.b, m.b * n.a + m.d * n.b, m.a * n.c + m.c * n.d, m.b * n.c + m.d * n.d,
    m.a * n.e + m.c * n.f + m.e, m.b * n.e + m.d * n.f + m.f⟩

instance : Mul Affine := ⟨mul⟩

/-- The move by `d`. -/
def translate (d : Vec) : Affine := ⟨1, 0, 0, 1, d.x, d.y⟩

/-- The scaling by `sx` along `x` and `sy` along `y`, about the origin. -/
def scale (sx sy : Rat) : Affine := ⟨sx, 0, 0, sy, 0, 0⟩

/-- The scaling by one factor on both axes. -/
def zoom (k : Rat) : Affine := scale k k

/-- `n` quarter turns about the origin: `rotate(90 n)`. One quarter turn takes `(x, y)` to
`(-y, x)`. -/
def quarterTurns (n : Int) : Affine :=
  if n % 4 = 1 then ⟨0, 1, -1, 0, 0, 0⟩
  else if n % 4 = 2 then ⟨-1, 0, 0, -1, 0, 0⟩
  else if n % 4 = 3 then ⟨0, -1, 1, 0, 0, 0⟩
  else identity

/-- The rotation about the origin whose half angle has the tangent `u`: its cosine is
`(1 - u²) / (1 + u²)` and its sine `2 u / (1 + u²)`. Every rotation with a rational sine and
cosine is one of these, but the half turn. -/
def turn (u : Rat) : Affine :=
  ⟨(1 - u * u) / (1 + u * u), 2 * u / (1 + u * u), -(2 * u / (1 + u * u)),
    (1 - u * u) / (1 + u * u), 0, 0⟩

/-- The map `m` about a centre: the centre is moved to the origin, mapped, and moved back. -/
def about (center : Vec) (m : Affine) : Affine := translate center * m * translate (-center)

/-- The determinant: the factor by which the map scales an area, with its sign. -/
def det (m : Affine) : Rat := m.a * m.d - m.b * m.c

/-- The map that undoes `m`, for a determinant that is not zero. -/
def inverse (m : Affine) : Affine :=
  ⟨m.d / m.det, -m.b / m.det, -m.c / m.det, m.a / m.det, (m.c * m.f - m.d * m.e) / m.det,
    (m.b * m.e - m.a * m.f) / m.det⟩

/-- The map of the six numbers as they are written. -/
def ofMatrix (m : Matrix) : Affine :=
  ⟨m.a.toRat, m.b.toRat, m.c.toRat, m.d.toRat, m.e.toRat, m.f.toRat⟩

/-- The six numbers that write the map, each at `places` places. -/
def toMatrix (m : Affine) (places : Nat := 6) : Matrix :=
  ⟨.ofRat m.a places, .ofRat m.b places, .ofRat m.c places, .ofRat m.d places, .ofRat m.e places,
    .ofRat m.f places⟩

/-- The function `matrix(…)` that writes the map, each number at `places` places. -/
def toTransform (m : Affine) (places : Nat := 6) : Transform := (m.toMatrix places).toTransform

end Affine

/-! ## A view box onto a viewport -/

/-- Where a view box stands along one axis, in the room that a uniform scale leaves: at the
start, in the middle or at the end. -/
inductive Align where
  | min
  | mid
  | max
  deriving DecidableEq, Repr, Inhabited

/-- How a view box is fitted to a viewport: `none` stretches it to fill; `meet` scales it by
one factor so that all of it shows; `slice` scales it by one factor so that it covers the
viewport. -/
inductive Fit where
  | none
  | meet (x : Align := .mid) (y : Align := .mid)
  | slice (x : Align := .mid) (y : Align := .mid)
  deriving DecidableEq, Repr, Inhabited

namespace Align

/-- The share of the room that stands before the view box. -/
def share : Align → Rat
  | .min => 0
  | .mid => 1 / 2
  | .max => 1

end Align

namespace Affine

/-- **The map of a view box onto a viewport**, as the chapter Coordinate Systems computes it:
a scale on each axis, made one for `meet` (the lesser) and for `slice` (the greater), and a
move that puts the corner of the view box at the corner of the viewport, and then at its
share of the room left. The first box is the view box and the second the viewport. A view box
of no width or no height has no such map: the chapter says that it disables rendering, and
the result here means nothing. A viewport with `y1` below `y0` turns the picture over, which
is how a chart puts its least value at the bottom. -/
def fit (viewBox viewport : Box) (how : Fit := .meet) : Affine :=
  let sx := viewport.width / viewBox.width
  let sy := viewport.height / viewBox.height
  match how with
  | .none => ⟨sx, 0, 0, sy, viewport.x0 - viewBox.x0 * sx, viewport.y0 - viewBox.y0 * sy⟩
  | .meet ax ay =>
    ⟨min sx sy, 0, 0, min sx sy,
      viewport.x0 - viewBox.x0 * min sx sy + ax.share * (viewport.width - viewBox.width * min sx sy),
      viewport.y0 - viewBox.y0 * min sx sy + ay.share * (viewport.height - viewBox.height * min sx sy)⟩
  | .slice ax ay =>
    ⟨max sx sy, 0, 0, max sx sy,
      viewport.x0 - viewBox.x0 * max sx sy + ax.share * (viewport.width - viewBox.width * max sx sy),
      viewport.y0 - viewBox.y0 * max sx sy + ay.share * (viewport.height - viewBox.height * max sx sy)⟩

end Affine

/-! ## A transform attribute -/

/-- The map of one function, and none for a skew and for a rotation that is no whole number
of quarter turns. -/
def Transform.affine? : Transform → Option Affine
  | .matrix a b c d e f => some ⟨a.toRat, b.toRat, c.toRat, d.toRat, e.toRat, f.toRat⟩
  | .translate tx ty => some (.translate ⟨tx.toRat, (ty.getD 0).toRat⟩)
  | .scale sx sy => some (.scale sx.toRat (sy.getD sx).toRat)
  | .rotate angle center =>
    if (angle.toRat / 90).den = 1 then
      match center with
      | none => some (.quarterTurns (angle.toRat / 90).num)
      | some (cx, cy) => some (.about ⟨cx.toRat, cy.toRat⟩ (.quarterTurns (angle.toRat / 90).num))
    else none
  | .skewX _ => none
  | .skewY _ => none

/-- The map of a list: the product of its functions' maps from left to right, so the last
function applies first. -/
def TransformList.affine? : TransformList → Option Affine
  | [] => some .identity
  | t :: rest => t.affine?.bind fun m => (affine? rest).map fun n => m * n

namespace Cubic

/-- The segment under an affine map. -/
def transform (m : Affine) (c : Cubic) : Cubic := c.map m.apply

end Cubic

/-! ## Laws -/

namespace Affine

theorem ext {m n : Affine} (ha : m.a = n.a) (hb : m.b = n.b) (hc : m.c = n.c) (hd : m.d = n.d)
    (he : m.e = n.e) (hf : m.f = n.f) : m = n := by
  cases m
  cases n
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  cases hf
  rfl

theorem mul_def (m n : Affine) : m * n = mul m n := rfl

/-- The identity moves no point. -/
theorem apply_identity (p : Vec) : identity.apply p = p := by
  apply Vec.ext <;> simp only [apply, identity] <;> grind

/-- The product sends a point where the right map and then the left one do. -/
theorem apply_mul (m n : Affine) (p : Vec) : (m * n).apply p = m.apply (n.apply p) := by
  apply Vec.ext <;> simp only [mul_def, mul, apply] <;> grind

theorem mul_assoc (l m n : Affine) : l * m * n = l * (m * n) := by
  apply ext <;> simp only [mul_def, mul] <;> grind

theorem identity_mul (m : Affine) : identity * m = m := by
  apply ext <;> simp only [mul_def, mul, identity] <;> grind

theorem mul_identity (m : Affine) : m * identity = m := by
  apply ext <;> simp only [mul_def, mul, identity] <;> grind

theorem apply_translate (d p : Vec) : (translate d).apply p = p + d := by
  apply Vec.ext <;> simp only [apply, translate, Vec.add_def] <;> grind

theorem apply_scale (sx sy : Rat) (p : Vec) : (scale sx sy).apply p = ⟨sx * p.x, sy * p.y⟩ := by
  apply Vec.ext <;> simp only [apply, scale] <;> grind

theorem apply_zoom (k : Rat) (p : Vec) : (zoom k).apply p = Vec.scale k p := by
  apply Vec.ext <;> simp only [apply, zoom, scale, Vec.scale] <;> grind

/-- One quarter turn is `Vec.perp`. -/
theorem apply_quarterTurn (p : Vec) : (quarterTurns 1).apply p = p.perp := by
  apply Vec.ext <;> simp only [apply, quarterTurns, Vec.perp] <;> grind

/-- **An affine map keeps steps**: the image of a step between two points is the step between
their images. -/
theorem apply_lerp (m : Affine) (a b : Vec) (t : Rat) :
    m.apply (a.lerp b t) = (m.apply a).lerp (m.apply b) t := by
  apply Vec.ext <;> simp only [apply, Vec.lerp] <;> grind

/-- The determinant of a product is the product of the determinants. -/
theorem det_mul (m n : Affine) : (m * n).det = m.det * n.det := by
  simp only [mul_def, mul, det]
  grind

theorem det_identity : identity.det = 1 := by
  simp only [det, identity]
  grind

/-- **The inverse undoes the map**, for a determinant that is not zero. -/
theorem inverse_apply (m : Affine) (h : m.det ≠ 0) (p : Vec) : m.inverse.apply (m.apply p) = p := by
  have hd : m.a * m.d - m.b * m.c ≠ 0 := h
  apply Vec.ext <;> simp only [apply, inverse, det] <;> grind

/-- The map undoes its inverse, for a determinant that is not zero. -/
theorem apply_inverse (m : Affine) (h : m.det ≠ 0) (p : Vec) : m.apply (m.inverse.apply p) = p := by
  have hd : m.a * m.d - m.b * m.c ≠ 0 := h
  apply Vec.ext <;> simp only [apply, inverse, det] <;> grind


/-- One more than a square is not zero. -/
theorem one_add_sq_ne (u : Rat) : 1 + u * u ≠ 0 := by
  have h : 0 ≤ u * u := rat_mul_self_nonneg u
  grind

/-- **A turn keeps every length.** -/
theorem normSq_turn (u : Rat) (p : Vec) : ((turn u).apply p).normSq = p.normSq := by
  have h := one_add_sq_ne u
  simp only [apply, turn, Vec.normSq, Vec.dot]
  grind

/-- A turn keeps the orientation and every area. -/
theorem det_turn (u : Rat) : (turn u).det = 1 := by
  have h := one_add_sq_ne u
  simp only [turn, det]
  grind

/-- A map about a centre leaves the centre where the map leaves the origin. -/
theorem apply_about (center : Vec) (m : Affine) (p : Vec) :
    (about center m).apply p = m.apply (p - center) + center := by
  apply Vec.ext <;> simp only [about, mul_def, mul, apply, translate, Vec.add_def, Vec.sub_def,
    Vec.neg_def] <;> grind

/-- **Stretching to fill**: with `Fit.none` the corner of the view box goes to the corner of
the viewport, and its far corner to the far corner, for a view box of some width and
height. -/
theorem fit_none_corner (viewBox viewport : Box) (hw : viewBox.width ≠ 0) (hh : viewBox.height ≠ 0) :
    (fit viewBox viewport .none).apply viewBox.corner = viewport.corner ∧
      (fit viewBox viewport .none).apply viewBox.far = viewport.far := by
  have hw' : viewBox.x1 - viewBox.x0 ≠ 0 := hw
  have hh' : viewBox.y1 - viewBox.y0 ≠ 0 := hh
  constructor <;> apply Vec.ext <;>
    simp only [fit, apply, Box.corner, Box.far, Box.width, Box.height] <;> grind

end Affine

/-! ## The two readings of a transform agree

`Transform.image?` of `Whatwg/Svg/Geometry/Affine.lean` computes the image of a point in
`Decimal`. Wherever it has an image, the map of this module has the same one, as numbers. -/

/-- The map of six written numbers sends the number of a point where the matrix sends the
point. -/
theorem Affine.apply_ofMatrix (m : Matrix) (p : Point) :
    (Affine.ofMatrix m).apply p.toVec = (m.apply p).toVec := by
  apply Vec.ext <;>
    simp only [Affine.apply, Affine.ofMatrix, Matrix.apply, Point.toVec, Decimal.toRat_add,
      Decimal.toRat_mul]

/-- **One function**: where the `Decimal` reading has an image of a point, the exact map has
the same one. -/
theorem Transform.toVec_image? (t : Transform) (p q : Point) (h : t.image? p = some q) :
    ∃ m, t.affine? = some m ∧ m.apply p.toVec = q.toVec := by
  cases t with
  | matrix a b c d e f =>
    cases h
    exact ⟨_, rfl, Affine.apply_ofMatrix ⟨a, b, c, d, e, f⟩ p⟩
  | translate tx ty =>
    cases h
    refine ⟨_, rfl, ?_⟩
    apply Vec.ext <;>
      simp only [Affine.apply, Affine.translate, Point.toVec, Decimal.toRat_add] <;> grind
  | scale sx sy =>
    cases h
    refine ⟨_, rfl, ?_⟩
    apply Vec.ext <;>
      simp only [Affine.apply, Affine.scale, Point.toVec, Decimal.toRat_mul] <;> grind
  | rotate angle center => cases h
  | skewX angle => cases h
  | skewY angle => cases h

/-- **A list**: where the `Decimal` reading has an image of a point, the exact map of the list
has the same one. -/
theorem TransformList.toVec_image? : ∀ (ts : TransformList) (p q : Point),
    TransformList.image? ts p = some q → ∃ m, TransformList.affine? ts = some m ∧ m.apply p.toVec = q.toVec
  | [], p, q, h => by
    cases h
    exact ⟨_, rfl, Affine.apply_identity _⟩
  | t :: rest, p, q, h => by
    rw [TransformList.image?_cons] at h
    cases hr : TransformList.image? rest p with
    | none =>
      rw [hr] at h
      cases h
    | some r =>
      rw [hr] at h
      have ⟨n, hn, hnp⟩ := TransformList.toVec_image? rest p r hr
      have ⟨m, hm, hmr⟩ := Transform.toVec_image? t r q h
      refine ⟨m * n, ?_, ?_⟩
      · show (t.affine?.bind fun m => (TransformList.affine? rest).map fun n => m * n) = _
        rw [hm, hn]
        rfl
      · rw [Affine.apply_mul, hnp, hmr]

/-- The map of two lists, one after the other, is the product of their maps. -/
theorem TransformList.affine?_append : ∀ (ts us : TransformList),
    TransformList.affine? (ts ++ us) =
      (TransformList.affine? ts).bind fun m => (TransformList.affine? us).map fun n => m * n
  | [], us => by
    show TransformList.affine? us = (TransformList.affine? us).map fun n => Affine.identity * n
    cases TransformList.affine? us with
    | none => rfl
    | some n => exact congrArg some (Affine.identity_mul n).symm
  | t :: ts, us => by
    show (t.affine?.bind fun m => (TransformList.affine? (ts ++ us)).map fun n => m * n) = _
    rw [TransformList.affine?_append ts us]
    show _ = ((t.affine?.bind fun m => (TransformList.affine? ts).map fun n => m * n).bind fun m =>
      (TransformList.affine? us).map fun n => m * n)
    cases t.affine? with
    | none => rfl
    | some m =>
      cases TransformList.affine? ts with
      | none => rfl
      | some n =>
        cases TransformList.affine? us with
        | none => rfl
        | some k => exact congrArg some (Affine.mul_assoc m n k).symm

namespace Cubic

/-- **A segment under an affine map**: its point at a parameter is the mapped point. -/
theorem transform_pointAt (m : Affine) (c : Cubic) (t : Rat) :
    (c.transform m).pointAt t = m.apply (c.pointAt t) :=
  map_pointAt m.apply (Affine.apply_lerp m) c t

/-- A part of a mapped segment is the part, mapped. -/
theorem transform_between (m : Affine) (c : Cubic) (a b : Rat) :
    (c.transform m).between a b = (c.between a b).transform m :=
  map_between m.apply (Affine.apply_lerp m) c a b

/-- A segment mapped twice is the segment under the product. -/
theorem transform_transform (m n : Affine) (c : Cubic) :
    (c.transform n).transform m = c.transform (m * n) := by
  apply ext <;> exact (Affine.apply_mul m n _).symm

theorem transform_identity (c : Cubic) : c.transform .identity = c := by
  apply ext <;> exact Affine.apply_identity _

/-- A moved segment is the segment under the move. -/
theorem transform_translate (d : Vec) (c : Cubic) : c.transform (.translate d) = c.move d := by
  apply ext <;> exact Affine.apply_translate d _

/-- A chain under an affine map is a chain. -/
theorem chained_transform (m : Affine) (cs : List Cubic) (h : Chained cs = true) :
    Chained (cs.map (transform m)) = true :=
  chained_map m.apply cs h

end Cubic

end Whatwg.Svg.Value
