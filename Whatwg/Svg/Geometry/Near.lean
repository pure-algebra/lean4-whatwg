import Whatwg.Svg.Geometry.Box
import Whatwg.Svg.Geometry.Rational.Laws

/-!
# Whatwg.Svg.Geometry.Near

Owner: how near two segments are (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-64).

The kit rounds a number once, where it writes it. This module bounds what that does to a curve,
and how far a curve is from a straight line.

- `Cubic.sub`, `sub_pointAt`: the difference of two segments is a segment, point by point.
- `Cubic.pointAt_near`: where a box holds the four differences of the control points, it holds
  the difference of the two curves at every parameter from `0` to `1`. Moving the four points a
  little moves no point of the curve further.
- `Cubic.written c places`: the segment whose four points are the numbers that a path writes
  at `places`. `written_near`: it is within half a unit of the last place of `c`, along each
  axis, at every parameter from `0` to `1`. `line_near`: so is a straight segment between two
  rounded ends.
- `Cubic.chord_error`: a segment at `t` stands off its chord by `t (1 - t)` times a mean of its
  two bends. A program that draws a curve as straight pieces reads its number of pieces from
  this.

What this module does not claim: the same at a real parameter that is not rational, which is
`bezier_near` of `analysis/WhatwgAnalysis/Box.lean`; a distance in the plane, which takes a
root. The bounds here are along each axis.
-/

namespace Whatwg.Svg.Value

/-- The box of half a unit of the last place, of `places`, around the origin. -/
def Box.halfUnit (places : Nat) : Box :=
  ⟨-(1 / (2 * (10 : Rat) ^ places)), -(1 / (2 * (10 : Rat) ^ places)),
    1 / (2 * (10 : Rat) ^ places), 1 / (2 * (10 : Rat) ^ places)⟩

/-- **A rounded point is within half a unit of the last place of the point**, along each
axis. -/
theorem Vec.round_near (v : Vec) (places : Nat) :
    (Box.halfUnit places).Contains (v - (v.round places).toVec) := by
  have hx1 := Decimal.toRat_ofRat_le v.x places
  have hx2 := Decimal.lt_toRat_ofRat v.x places
  have hy1 := Decimal.toRat_ofRat_le v.y places
  have hy2 := Decimal.lt_toRat_ofRat v.y places
  simp only [Box.Contains, Box.halfUnit, Vec.sub_def, Vec.round, Point.toVec]
  generalize (Decimal.ofRat v.x places).toRat = rx at hx1 hx2 ⊢
  generalize (Decimal.ofRat v.y places).toRat = ry at hy1 hy2 ⊢
  generalize 1 / (2 * (10 : Rat) ^ places) = h at hx1 hx2 hy1 hy2 ⊢
  grind

namespace Cubic

/-- The difference of two segments, control point by control point. -/
def sub (c d : Cubic) : Cubic := ⟨c.p0 - d.p0, c.p1 - d.p1, c.p2 - d.p2, c.p3 - d.p3⟩

/-- The difference of two segments at a parameter is the difference of their points there. -/
theorem sub_pointAt (c d : Cubic) (t : Rat) : (c.sub d).pointAt t = c.pointAt t - d.pointAt t := by
  apply Vec.ext <;> simp only [sub, pointAt, blossom, Vec.lerp, Vec.sub_def] <;> grind

/-- **Moving the four points a little moves no point of the segment further.** Where a box
holds the four differences of the control points, it holds the difference of the two segments
at every parameter from `0` to `1`. -/
theorem pointAt_near {b : Box} {c d : Cubic} (h0 : b.Contains (c.p0 - d.p0))
    (h1 : b.Contains (c.p1 - d.p1)) (h2 : b.Contains (c.p2 - d.p2)) (h3 : b.Contains (c.p3 - d.p3))
    {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : b.Contains (c.pointAt t - d.pointAt t) := by
  rw [← sub_pointAt]
  exact contains_pointAt_of (c := c.sub d) h0 h1 h2 h3 ht0 ht1

/-- The segment whose four points are the numbers that a path writes at `places`: what a `C`
command of the written path draws. -/
def written (c : Cubic) (places : Nat := 3) : Cubic := c.map fun v => (v.round places).toVec

/-- **A written segment is within half a unit of the last place of the exact one**, along each
axis, at every parameter from `0` to `1`. -/
theorem written_near (c : Cubic) (places : Nat) {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Box.halfUnit places).Contains (c.pointAt t - (c.written places).pointAt t) :=
  pointAt_near (d := c.written places) (Vec.round_near c.p0 places) (Vec.round_near c.p1 places)
    (Vec.round_near c.p2 places) (Vec.round_near c.p3 places) ht0 ht1

/-- **A straight segment between two rounded ends is within half a unit of the last place of
the exact one**: what an `L` command of the written path draws. -/
theorem line_near (a b : Vec) (places : Nat) {t : Rat} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Box.halfUnit places).Contains
      ((line a b).pointAt t -
        (line (a.round places).toVec (b.round places).toVec).pointAt t) := by
  have ha := Vec.round_near a places
  have hb := Vec.round_near b places
  have e : ∀ (p q p' q' : Vec) (s : Rat), p.lerp q s - p'.lerp q' s = (p - p').lerp (q - q') s := by
    intro p q p' q' s
    apply Vec.ext <;> simp only [Vec.lerp, Vec.sub_def] <;> grind
  refine pointAt_near (c := line a b) (d := line (a.round places).toVec (b.round places).toVec)
    ha ?_ ?_ hb ht0 ht1
  · show (Box.halfUnit places).Contains
      (a.lerp b (1 / 3) - (a.round places).toVec.lerp (b.round places).toVec (1 / 3))
    rw [e]
    exact Box.contains_lerp ha hb (by grind) (by grind)
  · show (Box.halfUnit places).Contains
      (a.lerp b (2 / 3) - (a.round places).toVec.lerp (b.round places).toVec (2 / 3))
    rw [e]
    exact Box.contains_lerp ha hb (by grind) (by grind)

/-- **How far a segment stands off its chord.** At the parameter `t` it is `t (1 - t)` times a
mean of the second differences of its control points, the first weighted `2 - t` and the second
`1 + t`. So along each axis the distance is at most three quarters of the greater of the two. -/
theorem chord_error (c : Cubic) (t : Rat) :
    c.pointAt t - c.p0.lerp c.p3 t =
      Vec.scale (-(t * (1 - t)))
        (Vec.scale (2 - t) (c.p0 - Vec.scale 2 c.p1 + c.p2) +
          Vec.scale (1 + t) (c.p1 - Vec.scale 2 c.p2 + c.p3)) := by
  apply Vec.ext <;> simp only [pointAt, blossom, Vec.lerp, Vec.scale, Vec.add_def, Vec.sub_def] <;>
    grind

end Cubic

end Whatwg.Svg.Value
