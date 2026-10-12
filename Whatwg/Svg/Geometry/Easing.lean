import Whatwg.Svg.Scene.Motion
import Whatwg.Svg.Geometry.Grid

/-!
# Whatwg.Svg.Geometry.Easing

Owner: what an easing means in exact numbers (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-62).

`Whatwg/Svg/Scene/Motion.lean` reads an easing in whole thousandths, with one division that
rounds down. This module says what each of those numbers is the floor of, and what CSS draws.

- **A cubic easing is a segment of the kit.** CSS Easing Functions gives `cubic-bezier(x1, y1,
  x2, y2)` as the cubic Bézier curve from `(0, 0)` to `(1, 1)` with the controls `(x1, y1)` and
  `(x2, y2)`: the output for an input `x` is the `y` of the point of the curve whose abscissa is
  `x`. `Easing.segment y1 y2` is that curve for `x1 = 1/3` and `x2 = 2/3`, as a `Cubic`. Its
  point at the parameter `s` has the abscissa `s` (`segment_pointAt`). So the output for the
  input `s` is the `y` of its point at `s`, the polynomial `Easing.cubicExact`, and no equation
  is solved.
- `cubicAt_eq_floor`: the whole-number reading is that polynomial in thousandths, rounded down.
- `stopsAt_eq_floor`: the reading of stops is the straight line between two stops in exact
  numbers, rounded down.

What this module does not claim: anything about a `cubic-bezier` with other abscissae, whose
output takes the root of a cubic; that a browser computes in exact numbers (it computes in
floating point, and writes `1/3` with a finite number of digits).
-/

namespace Whatwg.Svg.Value

/-- The quotient of whole numbers that rounds down is the floor of the exact quotient, for a
divisor that is more than zero. -/
theorem rat_floor_intCast_div (n : Int) {b : Int} (hb : 0 < b) :
    ((n : Rat) / (b : Rat)).floor = n / b := by
  have hB : (0 : Rat) < (b : Rat) := Rat.intCast_pos.mpr hb
  have h1 := Rat.intCast_le_intCast.mpr (Int.ediv_mul_le n (Int.ne_of_gt hb))
  have h2 := Rat.intCast_lt_intCast.mpr (Int.lt_ediv_add_one_mul_self n hb)
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat] at h1 h2
  apply Decimal.rat_floor_eq
  · generalize ((n / b : Int) : Rat) = k at h1 h2 ⊢
    generalize (b : Rat) = B at hB h1 h2 ⊢
    have e : k = k * B / B := by grind
    rw [e]
    exact Decimal.rat_div_le_div hB h1
  · generalize ((n / b : Int) : Rat) = k at h1 h2 ⊢
    generalize (b : Rat) = B at hB h1 h2 ⊢
    have e : k + 1 = (k + 1) * B / B := by grind
    rw [e]
    exact Decimal.rat_div_lt_div hB h2

end Whatwg.Svg.Value

namespace Whatwg.Svg.Scene.Easing

open Whatwg.Svg.Value

/-- The cubic easing of the heights `y1` and `y2`, in per mille, at the exact progress `s`:
`3 y1 s (1 - s)² + 3 y2 s² (1 - s) + s³`. -/
def cubicExact (y1 y2 : Int) (s : Rat) : Rat :=
  3 * ((y1 : Rat) / 1000) * s * (1 - s) * (1 - s) + 3 * ((y2 : Rat) / 1000) * s * s * (1 - s) +
    s * s * s

/-- The curve that CSS draws for `cubic-bezier(1/3, y1, 2/3, y2)`, the heights in per mille:
from `(0, 0)` to `(1, 1)`. -/
def segment (y1 y2 : Int) : Cubic :=
  ⟨⟨0, 0⟩, ⟨1 / 3, (y1 : Rat) / 1000⟩, ⟨2 / 3, (y2 : Rat) / 1000⟩, ⟨1, 1⟩⟩

/-- **The abscissa of the curve is its parameter**, and its ordinate is the polynomial. So the
output of the easing for the input `s` is `cubicExact y1 y2 s`. -/
theorem segment_pointAt (y1 y2 : Int) (s : Rat) :
    (segment y1 y2).pointAt s = ⟨s, cubicExact y1 y2 s⟩ := by
  apply Vec.ext <;> simp only [segment, cubicExact, Cubic.pointAt, Cubic.blossom, Vec.lerp] <;>
    grind

/-- A cubic easing starts at nothing. -/
theorem cubicExact_zero (y1 y2 : Int) : cubicExact y1 y2 0 = 0 := by
  simp only [cubicExact]
  grind

/-- A cubic easing ends at the whole. -/
theorem cubicExact_one (y1 y2 : Int) : cubicExact y1 y2 1 = 1 := by
  simp only [cubicExact]
  grind

/-- A cubic easing leaves its start with the slope `3 y1`: the velocity of its curve there. -/
theorem segment_velocity_zero (y1 y2 : Int) :
    (segment y1 y2).velocity 0 = ⟨1, 3 * ((y1 : Rat) / 1000)⟩ := by
  rw [Cubic.velocity_zero]
  apply Vec.ext <;> simp only [segment, Vec.scale, Vec.sub_def] <;> grind

/-- A cubic easing arrives at its end with the slope `3 (1 - y2)`. -/
theorem segment_velocity_one (y1 y2 : Int) :
    (segment y1 y2).velocity 1 = ⟨1, 3 * (1 - (y2 : Rat) / 1000)⟩ := by
  rw [Cubic.velocity_one]
  apply Vec.ext
  · show (3 : Rat) * (1 - 2 / 3) = 1
    grind
  · show (3 : Rat) * (1 - (y2 : Rat) / 1000) = 3 * (1 - (y2 : Rat) / 1000)
    rfl

/-- **The whole-number reading of a cubic easing is the exact one, rounded down**: at `p` per
mille it is the floor of a thousand times the polynomial at `p / 1000`. -/
theorem cubicAt_eq_floor (y1 y2 : Int) (p : Nat) :
    cubicAt y1 y2 p = (1000 * cubicExact y1 y2 ((p : Rat) / 1000)).floor := by
  have e : 1000 * cubicExact y1 y2 ((p : Rat) / 1000) =
      ((3 * y1 * (p : Int) * (1000 - (p : Int)) ^ 2 + 3 * y2 * (p : Int) ^ 2 * (1000 - (p : Int)) +
        1000 * (p : Int) ^ 3 : Int) : Rat) / ((1000000000 : Int) : Rat) := by
    simp only [cubicExact, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_pow,
      Rat.intCast_ofNat, Rat.intCast_natCast]
    grind
  rw [e, rat_floor_intCast_div _ (by decide)]
  rfl

/-- **The reading of stops is a straight line, rounded down.** With `a` and `b` the two stops
around the progress and `n` the whole thousandths of the way from the one to the other, the
reading is the floor of `a + (b - a) n / 1000`. -/
theorem stopsAt_eq_floor (values : List Int) (p : Nat) :
    stopsAt values p =
      (((values.getD (p * (values.length - 1) / 1000) (values.getLast?.getD 0) : Int) : Rat) +
        (((values.getD (p * (values.length - 1) / 1000 + 1) (values.getLast?.getD 0) : Int) : Rat) -
            ((values.getD (p * (values.length - 1) / 1000) (values.getLast?.getD 0) : Int) : Rat)) *
          ((p * (values.length - 1) - 1000 * (p * (values.length - 1) / 1000) : Nat) : Rat) /
            1000).floor := by
  simp only [stopsAt]
  generalize values.getD (p * (values.length - 1) / 1000) (values.getLast?.getD 0) = a
  generalize values.getD (p * (values.length - 1) / 1000 + 1) (values.getLast?.getD 0) = b
  generalize p * (values.length - 1) - 1000 * (p * (values.length - 1) / 1000) = n
  have e : (a : Rat) + ((b : Rat) - (a : Rat)) * (n : Rat) / 1000 =
      (((b - a) * (n : Int) : Int) : Rat) / 1000 + ((a : Int) : Rat) := by
    simp only [Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_natCast]
    grind
  rw [e, Rat.floor_add_intCast, rat_floor_div_thousand]
  exact Int.add_comm _ _

/-- **The reading of a cubic easing at a share is the exact one, rounded down**: at the share
`num / den` it is the floor of a thousand times the polynomial there. The progress is not
rounded first. -/
theorem cubicOf_eq_floor (y1 y2 : Int) (num den : Nat) (hd : 0 < den) :
    cubicOf y1 y2 num den = (1000 * cubicExact y1 y2 ((num : Rat) / (den : Rat))).floor := by
  have hD : (den : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hd)
  have e : 1000 * cubicExact y1 y2 ((num : Rat) / (den : Rat)) =
      ((3 * y1 * (num : Int) * ((den : Int) - (num : Int)) ^ 2 +
        3 * y2 * (num : Int) ^ 2 * ((den : Int) - (num : Int)) + 1000 * (num : Int) ^ 3 : Int) :
          Rat) / (((den : Int) ^ 3 : Int) : Rat) := by
    simp only [cubicExact, Rat.intCast_add, Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_pow,
      Rat.intCast_ofNat, Rat.intCast_natCast]
    generalize (num : Rat) = n
    generalize (den : Rat) = d at hD ⊢
    grind
  rw [e, rat_floor_intCast_div _ (Int.pow_pos (Int.natCast_pos.mpr hd))]
  rfl

/-- **The reading of stops at a share is a straight line, rounded down**: with `a` and `b` the
two stops around the share and `n / den` the part of the way from the one to the other, the
reading is the floor of `a + (b - a) n / den`. -/
theorem stopsOf_eq_floor (values : List Int) (num den : Nat) (hd : 0 < den) :
    stopsOf values num den =
      (((values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0) : Int) : Rat) +
        (((values.getD (num * (values.length - 1) / den + 1) (values.getLast?.getD 0) : Int) :
              Rat) -
            ((values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0) : Int) :
              Rat)) *
          ((num * (values.length - 1) - den * (num * (values.length - 1) / den) : Nat) : Rat) /
            (den : Rat)).floor := by
  simp only [stopsOf]
  generalize values.getD (num * (values.length - 1) / den) (values.getLast?.getD 0) = a
  generalize values.getD (num * (values.length - 1) / den + 1) (values.getLast?.getD 0) = b
  generalize num * (values.length - 1) - den * (num * (values.length - 1) / den) = n
  have hD : (den : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos hd)
  have e : (a : Rat) + ((b : Rat) - (a : Rat)) * (n : Rat) / (den : Rat) =
      (((b - a) * (n : Int) : Int) : Rat) / (((den : Int) : Int) : Rat) + ((a : Int) : Rat) := by
    simp only [Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_natCast]
    generalize (den : Rat) = d at hD ⊢
    grind
  rw [e, Rat.floor_add_intCast, rat_floor_intCast_div _ (Int.natCast_pos.mpr hd)]
  exact Int.add_comm _ _

end Whatwg.Svg.Scene.Easing

namespace Whatwg.Svg.Scene.Transition

open Whatwg.Svg.Value

/-- **What a transition with a cubic easing reads between its delay and its end**: the floor
of a thousand times the polynomial at the share of the duration that has passed. A browser
that animates the same transition computes that polynomial at that share, so the reading is
the browser's value in per mille, rounded down. -/
theorem at_cubic (tr : Transition) (y1 y2 : Int) (he : tr.ease = .cubic y1 y2) (t : Nat)
    (h1 : tr.delay < t) (h2 : t < tr.delay + tr.duration) :
    tr.at t =
      (1000 * Easing.cubicExact y1 y2 (((t - tr.delay : Nat) : Rat) / (tr.duration : Rat))).floor := by
  have hd : 0 < tr.duration := by omega
  have n1 : ¬ (tr.delay + tr.duration ≤ t) := by omega
  have n2 : ¬ (t ≤ tr.delay) := by omega
  simp only [Transition.at, if_neg n1, if_neg n2, he, Easing.of]
  exact Easing.cubicOf_eq_floor y1 y2 _ _ hd

end Whatwg.Svg.Scene.Transition
