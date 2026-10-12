import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Rat.Cast.Order
import Whatwg.Svg.Geometry.Affine.Map

/-!
# WhatwgAnalysis.Turn

The exact rotation of the library is a rotation by a stated angle.

`Whatwg/Svg/Geometry/Affine/Map.lean` has `Affine.turn u`, a rotation with a rational sine
and cosine, and proves in `Rat` that it keeps every length. Its header says what it cannot
say: by what angle it turns, which takes an arctangent.

This module says it: `turn u` is the rotation by `2 * arctan u` (`turn_cos`, `turn_sin`,
`apply_turn`).
-/

namespace WhatwgAnalysis

open Whatwg.Svg.Value

/-- The cosine of the turn: `turn u` has the cosine of twice the arctangent of `u`. -/
theorem turn_cos (u : ℚ) : ((Affine.turn u).a : ℝ) = Real.cos (2 * Real.arctan u) := by
  have h : (1 : ℝ) + (u : ℝ) ^ 2 ≠ 0 := by positivity
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  simp only [Affine.turn]
  push_cast
  field_simp
  ring

/-- The sine of the turn: `turn u` has the sine of twice the arctangent of `u`. -/
theorem turn_sin (u : ℚ) : ((Affine.turn u).b : ℝ) = Real.sin (2 * Real.arctan u) := by
  have hpos : (0 : ℝ) < 1 + (u : ℝ) ^ 2 := by positivity
  have hs : √(1 + (u : ℝ) ^ 2) * √(1 + (u : ℝ) ^ 2) = 1 + (u : ℝ) ^ 2 :=
    Real.mul_self_sqrt hpos.le
  have hs' : (1 : ℝ) + (u : ℝ) * u = √(1 + (u : ℝ) ^ 2) * √(1 + (u : ℝ) ^ 2) := by
    rw [hs]
    ring
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  simp only [Affine.turn]
  push_cast
  rw [hs']
  ring

/-- **`turn u` is the rotation by `2 * arctan u`**: the image of a point has the coordinates
that the rotation by that angle gives. -/
theorem apply_turn (u : ℚ) (p : Vec) :
    ((((Affine.turn u).apply p).x : ℚ) : ℝ) =
        Real.cos (2 * Real.arctan u) * p.x - Real.sin (2 * Real.arctan u) * p.y ∧
      ((((Affine.turn u).apply p).y : ℚ) : ℝ) =
        Real.sin (2 * Real.arctan u) * p.x + Real.cos (2 * Real.arctan u) * p.y := by
  rw [← turn_cos, ← turn_sin]
  constructor
  · simp only [Affine.apply, Affine.turn]
    push_cast
    ring
  · simp only [Affine.apply, Affine.turn]
    push_cast
    ring

end WhatwgAnalysis
