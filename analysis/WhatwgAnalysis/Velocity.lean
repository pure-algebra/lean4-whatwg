import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Rat.Cast.Order
import Whatwg.Svg.Geometry.Cubic

/-!
# WhatwgAnalysis.Velocity

The velocity of a cubic Bézier segment is its derivative.

`Whatwg/Svg/Geometry/Cubic.lean` computes a segment in `Rat`: `Cubic.pointAt` is its point at
a rational parameter, and `Cubic.velocity` is called its velocity. The header of that module
says what it cannot say: that `velocity` is the derivative in the sense of analysis, which is
a statement about real numbers.

This module says it. `bezier a b c d` is one coordinate of a segment at a real parameter, a
cubic polynomial. It is the function that `pointAt` computes (`pointAt_x`, `pointAt_y`), and
its derivative at a rational parameter is the number that `velocity` computes
(`hasDerivAt_pointAt_x`, `hasDerivAt_pointAt_y`).

The library computes; this package says what the computation means. Nothing here runs.
-/

namespace WhatwgAnalysis

open Whatwg.Svg.Value

/-- One coordinate of a cubic Bézier segment with the control values `a`, `b`, `c`, `d`, at a
real parameter: the polynomial of de Casteljau's construction, in powers of the parameter. -/
noncomputable def bezier (a b c d : ℝ) (t : ℝ) : ℝ :=
  a + 3 * (b - a) * t + 3 * (a - 2 * b + c) * t ^ 2 + (d - 3 * c + 3 * b - a) * t ^ 3

/-- The polynomial that is the derivative of `bezier`. -/
noncomputable def bezierVelocity (a b c d : ℝ) (t : ℝ) : ℝ :=
  3 * (b - a) + 6 * (a - 2 * b + c) * t + 3 * (d - 3 * c + 3 * b - a) * t ^ 2

/-- `bezierVelocity` is the derivative of `bezier`, at every real parameter. -/
theorem hasDerivAt_bezier (a b c d t : ℝ) :
    HasDerivAt (bezier a b c d) (bezierVelocity a b c d t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 3 * (b - a) * t) (3 * (b - a)) t := by
    simpa using (hasDerivAt_id t).const_mul (3 * (b - a))
  have h2 : HasDerivAt (fun t : ℝ => 3 * (a - 2 * b + c) * t ^ 2)
      (3 * (a - 2 * b + c) * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (3 * (a - 2 * b + c))
  have h3 : HasDerivAt (fun t : ℝ => (d - 3 * c + 3 * b - a) * t ^ 3)
      ((d - 3 * c + 3 * b - a) * (3 * t ^ 2)) t := by
    simpa using (hasDerivAt_pow 3 t).const_mul (d - 3 * c + 3 * b - a)
  have h := (((hasDerivAt_const t a).add h1).add h2).add h3
  have e : bezierVelocity a b c d t =
      0 + 3 * (b - a) + 3 * (a - 2 * b + c) * (2 * t) + (d - 3 * c + 3 * b - a) * (3 * t ^ 2) := by
    unfold bezierVelocity
    ring
  rw [e]
  exact h

/-- The `x` of the point that the library computes is the polynomial, at every rational
parameter. -/
theorem pointAt_x (c : Cubic) (q : ℚ) :
    ((c.pointAt q).x : ℝ) = bezier c.p0.x c.p1.x c.p2.x c.p3.x q := by
  simp only [Cubic.pointAt, Cubic.blossom, Vec.lerp, bezier]
  push_cast
  ring

/-- The `y` of the point that the library computes is the polynomial. -/
theorem pointAt_y (c : Cubic) (q : ℚ) :
    ((c.pointAt q).y : ℝ) = bezier c.p0.y c.p1.y c.p2.y c.p3.y q := by
  simp only [Cubic.pointAt, Cubic.blossom, Vec.lerp, bezier]
  push_cast
  ring

/-- The `x` of the velocity that the library computes is the derivative polynomial. -/
theorem velocity_x (c : Cubic) (q : ℚ) :
    ((c.velocity q).x : ℝ) = bezierVelocity c.p0.x c.p1.x c.p2.x c.p3.x q := by
  simp only [Cubic.velocity, Vec.scale, Vec.lerp, Vec.sub_def, bezierVelocity]
  push_cast
  ring

/-- The `y` of the velocity that the library computes is the derivative polynomial. -/
theorem velocity_y (c : Cubic) (q : ℚ) :
    ((c.velocity q).y : ℝ) = bezierVelocity c.p0.y c.p1.y c.p2.y c.p3.y q := by
  simp only [Cubic.velocity, Vec.scale, Vec.lerp, Vec.sub_def, bezierVelocity]
  push_cast
  ring

/-- **The velocity of a segment is its derivative**, along `x`: the real function that
`pointAt` computes has, at a rational parameter, the derivative that `velocity` computes. -/
theorem hasDerivAt_pointAt_x (c : Cubic) (q : ℚ) :
    HasDerivAt (bezier c.p0.x c.p1.x c.p2.x c.p3.x) ((c.velocity q).x : ℝ) (q : ℝ) := by
  rw [velocity_x]
  exact hasDerivAt_bezier _ _ _ _ _

/-- **The velocity of a segment is its derivative**, along `y`. -/
theorem hasDerivAt_pointAt_y (c : Cubic) (q : ℚ) :
    HasDerivAt (bezier c.p0.y c.p1.y c.p2.y c.p3.y) ((c.velocity q).y : ℝ) (q : ℝ) := by
  rw [velocity_y]
  exact hasDerivAt_bezier _ _ _ _ _

end WhatwgAnalysis
