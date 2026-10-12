import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Cast.Order
import WhatwgAnalysis.Velocity
import Whatwg.Svg.Geometry.Box

/-!
# WhatwgAnalysis.Box

The box of a segment holds the whole segment, and a rounded segment stays near the exact one.

`Whatwg/Svg/Geometry/Box.lean` proves that the box of the four points of a cubic holds its point
at every rational parameter from `0` to `1` (`Cubic.contains_pointAt`). A drawn curve has a point
at every real parameter. `Whatwg/Svg/Geometry/Write.lean` rounds the four points of a segment
where it writes them, and says in its header that it states no bound on how far the written curve
is from the exact one.

This module says both, of the real function that `pointAt` computes (`pointAt_x`, `pointAt_y`):

- `box_holds_x`, `box_holds_y`: the box holds the curve at every real parameter from `0` to `1`;
- `bezier_near`: where each of the four control values moves by `δ` at most, the curve moves by
  `δ` at most, at every real parameter from `0` to `1`. A path written at `n` places has each
  control value within half a unit of the last place, so the written curve is within that of the
  exact one along each axis.

Both rest on `bezier_mem`: the value at a parameter from `0` to `1` is a mean of the four control
values with weights that are not negative and sum to one.
-/

namespace WhatwgAnalysis

open Whatwg.Svg.Value

/-- One coordinate of a segment stays between any two bounds on its four control values, at
every real parameter from `0` to `1`. -/
theorem bezier_mem (a b c d lo hi t : ℝ) (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hc : lo ≤ c ∧ c ≤ hi) (hd : lo ≤ d ∧ d ≤ hi) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lo ≤ bezier a b c d t ∧ bezier a b c d t ≤ hi := by
  have e : bezier a b c d t =
      (1 - t) ^ 3 * a + 3 * (1 - t) ^ 2 * t * b + 3 * (1 - t) * t ^ 2 * c + t ^ 3 * d := by
    unfold bezier
    ring
  have s : (1 - t) ^ 3 + 3 * (1 - t) ^ 2 * t + 3 * (1 - t) * t ^ 2 + t ^ 3 = 1 := by ring
  have h1 : 0 ≤ 1 - t := by linarith
  have w0 : 0 ≤ (1 - t) ^ 3 := by positivity
  have w1 : 0 ≤ 3 * (1 - t) ^ 2 * t := by positivity
  have w2 : 0 ≤ 3 * (1 - t) * t ^ 2 := by positivity
  have w3 : 0 ≤ t ^ 3 := by positivity
  have el : lo = (1 - t) ^ 3 * lo + 3 * (1 - t) ^ 2 * t * lo + 3 * (1 - t) * t ^ 2 * lo +
      t ^ 3 * lo := by linear_combination (-lo) * s
  have eh : hi = (1 - t) ^ 3 * hi + 3 * (1 - t) ^ 2 * t * hi + 3 * (1 - t) * t ^ 2 * hi +
      t ^ 3 * hi := by linear_combination (-hi) * s
  rw [e]
  constructor
  · rw [el]
    linarith [mul_le_mul_of_nonneg_left ha.1 w0, mul_le_mul_of_nonneg_left hb.1 w1,
      mul_le_mul_of_nonneg_left hc.1 w2, mul_le_mul_of_nonneg_left hd.1 w3]
  · rw [eh]
    linarith [mul_le_mul_of_nonneg_left ha.2 w0, mul_le_mul_of_nonneg_left hb.2 w1,
      mul_le_mul_of_nonneg_left hc.2 w2, mul_le_mul_of_nonneg_left hd.2 w3]

/-- **The box of a segment holds the segment at every real parameter**, along `x`. -/
theorem box_holds_x (c : Cubic) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (c.box.x0 : ℝ) ≤ bezier c.p0.x c.p1.x c.p2.x c.p3.x t ∧
      bezier c.p0.x c.p1.x c.p2.x c.p3.x t ≤ (c.box.x1 : ℝ) := by
  have h0 := c.contains_p0
  have h1 := c.contains_p1
  have h2 := c.contains_p2
  have h3 := c.contains_p3
  exact bezier_mem _ _ _ _ _ _ t
    ⟨by exact_mod_cast h0.1, by exact_mod_cast h0.2.1⟩
    ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2.1⟩
    ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2.1⟩
    ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2.1⟩ ht0 ht1

/-- **The box of a segment holds the segment at every real parameter**, along `y`. -/
theorem box_holds_y (c : Cubic) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (c.box.y0 : ℝ) ≤ bezier c.p0.y c.p1.y c.p2.y c.p3.y t ∧
      bezier c.p0.y c.p1.y c.p2.y c.p3.y t ≤ (c.box.y1 : ℝ) := by
  have h0 := c.contains_p0
  have h1 := c.contains_p1
  have h2 := c.contains_p2
  have h3 := c.contains_p3
  exact bezier_mem _ _ _ _ _ _ t
    ⟨by exact_mod_cast h0.2.2.1, by exact_mod_cast h0.2.2.2⟩
    ⟨by exact_mod_cast h1.2.2.1, by exact_mod_cast h1.2.2.2⟩
    ⟨by exact_mod_cast h2.2.2.1, by exact_mod_cast h2.2.2.2⟩
    ⟨by exact_mod_cast h3.2.2.1, by exact_mod_cast h3.2.2.2⟩ ht0 ht1

/-- **A rounded segment stays near the exact one.** Where each of the four control values moves
by `δ` at most, the coordinate moves by `δ` at most, at every real parameter from `0` to `1`. -/
theorem bezier_near (a b c d a' b' c' d' δ t : ℝ) (ha : |a - a'| ≤ δ) (hb : |b - b'| ≤ δ)
    (hc : |c - c'| ≤ δ) (hd : |d - d'| ≤ δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |bezier a b c d t - bezier a' b' c' d' t| ≤ δ := by
  have e : bezier a b c d t - bezier a' b' c' d' t =
      bezier (a - a') (b - b') (c - c') (d - d') t := by
    unfold bezier
    ring
  rw [e, abs_le]
  exact bezier_mem _ _ _ _ _ _ t (abs_le.mp ha) (abs_le.mp hb) (abs_le.mp hc) (abs_le.mp hd) ht0 ht1

end WhatwgAnalysis
