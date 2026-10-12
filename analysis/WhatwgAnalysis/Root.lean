import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Whatwg.Svg.Geometry.Root.Laws

/-!
# WhatwgAnalysis.Root

The root that the library computes encloses the real square root.

`Whatwg/Svg/Geometry/Root.lean` has no square root: the root of a rational number is seldom
rational. It has `sqrtDown q n`, computed by `Nat.sqrt` on a scaled integer, with two laws
proved in the library about squares of rational numbers.

This module says what those two laws mean: `sqrtDown q n` is no more than the real square root
of `q`, and the real square root is less than one unit of the last place above it
(`sqrtDown_le_sqrt`, `sqrt_lt_sqrtDown_succ`). The same holds of the length of a vector
(`norm_le`, `lt_norm_succ`).
-/

namespace WhatwgAnalysis

open Whatwg.Svg.Value

/-- The computed root is no more than the real square root, for a number that is not
negative. -/
theorem sqrtDown_le_sqrt {q : ℚ} (h : 0 ≤ q) (n : ℕ) : ((sqrtDown q n : ℚ) : ℝ) ≤ √(q : ℝ) := by
  have h0 : (0 : ℝ) ≤ ((sqrtDown q n : ℚ) : ℝ) := by exact_mod_cast sqrtDown_nonneg q n
  have hq : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
  rw [Real.le_sqrt h0 hq, sq]
  exact_mod_cast sqrtDown_mul_self_le h n

/-- The real square root is less than one unit of the last place above the computed root. -/
theorem sqrt_lt_sqrtDown_succ (q : ℚ) (n : ℕ) :
    √(q : ℝ) < ((sqrtDown q n : ℚ) : ℝ) + 1 / (10 : ℝ) ^ n := by
  have h0 : (0 : ℝ) ≤ ((sqrtDown q n : ℚ) : ℝ) := by exact_mod_cast sqrtDown_nonneg q n
  have hpos : (0 : ℝ) < ((sqrtDown q n : ℚ) : ℝ) + 1 / (10 : ℝ) ^ n := by positivity
  rw [Real.sqrt_lt' hpos, sq]
  have h := (Rat.cast_lt (K := ℝ)).mpr (lt_sqrtDown_succ q n)
  push_cast at h
  exact h

/-- The computed length of a vector is no more than its Euclidean length. -/
theorem norm_le (v : Vec) (n : ℕ) : ((v.norm n : ℚ) : ℝ) ≤ √((v.x : ℝ) ^ 2 + (v.y : ℝ) ^ 2) := by
  have h := sqrtDown_le_sqrt (Vec.normSq_nonneg v) n
  have e : ((v.normSq : ℚ) : ℝ) = (v.x : ℝ) ^ 2 + (v.y : ℝ) ^ 2 := by
    simp only [Vec.normSq, Vec.dot]
    push_cast
    ring
  rw [e] at h
  exact h

/-- The Euclidean length of a vector is less than one unit of the last place above its
computed length. -/
theorem lt_norm_succ (v : Vec) (n : ℕ) :
    √((v.x : ℝ) ^ 2 + (v.y : ℝ) ^ 2) < ((v.norm n : ℚ) : ℝ) + 1 / (10 : ℝ) ^ n := by
  have h := sqrt_lt_sqrtDown_succ v.normSq n
  have e : ((v.normSq : ℚ) : ℝ) = (v.x : ℝ) ^ 2 + (v.y : ℝ) ^ 2 := by
    simp only [Vec.normSq, Vec.dot]
    push_cast
    ring
  rw [e] at h
  exact h

end WhatwgAnalysis
