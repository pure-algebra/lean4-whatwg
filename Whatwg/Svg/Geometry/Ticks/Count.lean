import Whatwg.Svg.Geometry.Ticks.Laws

/-!
# Whatwg.Svg.Geometry.Ticks.Count

Owner: how many ticks a range has, against how many were asked for (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

d3 says of its ticks that there are "approximately count + 1" of them, and tests it on thirty
ranges (`d3-array`, `test/ticks-test.js`). Here it is a bound that holds of every range.

- **About as many ticks as were asked for** (`plain_count`). Let a range that rises have `n`
  multiples of its step for the count `c`. Then `2 (n - 1)² < 5 c²` and `2 c² < 5 (n + 1)²`. In
  words: `n - 1` is less than `1.59` times `c`, and `c` is less than `1.59` times `n + 1`. For
  the count `10` that is from `6` to `16` ticks.

The bound is of `Ticks.between` with `Ticks.plain`, which is what `Ticks.ticks` gives for every
count but `1`. For the count `1`, where the step for one gap has no multiple in the range, the
ticks are those of the count `2`, and the bound is the bound of that count.

What this module does not claim: the bound as whole numbers. It is stated in rational numbers,
with the counts cast, since the proof squares a length.
-/

namespace Whatwg.Svg.Value

namespace Ticks

/-- Of two numbers that are not negative, the lesser has the lesser square. -/
theorem sq_le_sq {x y : Rat} (hx : 0 ≤ x) (h : x ≤ y) : x * x ≤ y * y :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left h hx)
    (Rat.mul_le_mul_of_nonneg_right h (Rat.le_trans hx h))

theorem sq_lt_sq {x y : Rat} (hx : 0 ≤ x) (h : x < y) : x * x < y * y := by
  have a := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h) hx
  have b := Rat.mul_lt_mul_of_pos_right h (by grind : (0 : Rat) < y)
  grind

/-- **About as many ticks as were asked for.** For a range that rises and a count `c` that is
not zero, let `n` be the count of the multiples of the round step in the range. Then
`2 (n - 1)² < 5 c²`, where there is a multiple at all, and `2 c² < 5 (n + 1)²`. -/
theorem plain_count {start stop : Rat} (h : start < stop) {count : Nat} (hc : count ≠ 0) :
    (1 ≤ (between start stop (plain start stop count)).length →
      2 * ((((between start stop (plain start stop count)).length : Rat) - 1) *
        (((between start stop (plain start stop count)).length : Rat) - 1)) <
        5 * ((count : Rat) * (count : Rat))) ∧
      2 * ((count : Rat) * (count : Rat)) <
        5 * ((((between start stop (plain start stop count)).length : Rat) + 1) *
          (((between start stop (plain start stop count)).length : Rat) + 1)) := by
  have hS : 0 < (plain start stop count).toRat := nearest_pos _
  have nn := plain_near h hc
  unfold Near at nn
  obtain ⟨n1, n2⟩ := nn
  obtain ⟨b1, b2⟩ := between_count (Rat.le_of_lt h) hS
  have hcp : (0 : Rat) < (count : Rat) := Rat.natCast_pos.mpr (Nat.pos_of_ne_zero hc)
  have hq : (stop - start) / (count : Rat) * (count : Rat) = stop - start :=
    Rat.div_mul_cancel (Rat.ne_of_gt hcp)
  have hw : (0 : Rat) < stop - start := by grind
  have hqp : (0 : Rat) < (stop - start) / (count : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_pos hw (Rat.inv_pos.mpr hcp)
  have hN0 : (0 : Rat) ≤ ((between start stop (plain start stop count)).length : Rat) :=
    Rat.natCast_nonneg
  rw [← hq] at b1 b2
  constructor
  · intro h1
    have hN1 : (1 : Rat) ≤ ((between start stop (plain start stop count)).length : Rat) := by
      have := Rat.natCast_le_natCast.mpr h1
      rw [Rat.natCast_ofNat] at this
      exact this
    generalize ((between start stop (plain start stop count)).length : Rat) = n at b1 hN1 ⊢
    generalize (plain start stop count).toRat = s at hS n1 n2 b1 ⊢
    generalize (stop - start) / (count : Rat) = q at hqp n1 n2 b1 ⊢
    generalize (count : Rat) = c at hcp b1 ⊢
    have hx : 0 ≤ (n - 1) * s := Rat.mul_nonneg (by grind) (Rat.le_of_lt hS)
    have a1 := sq_le_sq hx b1
    have a2 := Rat.mul_lt_mul_of_pos_right n2 (Rat.mul_pos hcp hcp)
    have key : 2 * ((n - 1) * (n - 1)) * (s * s) < 5 * (c * c) * (s * s) := by grind
    exact (Rat.mul_lt_mul_right (Rat.mul_pos hS hS)).mp key
  · generalize ((between start stop (plain start stop count)).length : Rat) = n at b2 hN0 ⊢
    generalize (plain start stop count).toRat = s at hS n1 n2 b2 ⊢
    generalize (stop - start) / (count : Rat) = q at hqp n1 n2 b2 ⊢
    generalize (count : Rat) = c at hcp b2 ⊢
    have hx : 0 ≤ q * c := Rat.le_of_lt (Rat.mul_pos hqp hcp)
    have a1 := sq_lt_sq hx b2
    have hn : (0 : Rat) ≤ (n + 1) * (n + 1) := Rat.mul_nonneg (by grind) (by grind)
    have a2 := Rat.mul_le_mul_of_nonneg_right n1 hn
    have key : 2 * (c * c) * (q * q) < 5 * ((n + 1) * (n + 1)) * (q * q) := by grind
    exact (Rat.mul_lt_mul_right (Rat.mul_pos hqp hqp)).mp key

end Ticks

/-! ## Finite evaluations -/

-- For the count `10` the bound allows from `6` to `16` ticks. d3's ranges of
-- `test/ticks-test.js` with that count have `11`, `11`, `11` and `9`.
#guard [Ticks.values 0 1 10, Ticks.values 0 10 10, Ticks.values (-10) 10 10,
  Ticks.values 0.98 1.14 10].map List.length == [11, 11, 11, 9]
-- Both ends of the bound are met. A range `31.6` long asked for in ten gaps has the step `2`
-- and sixteen ticks. A range `31.7` long from `1` has the step `5` and six.
#guard (Ticks.values 0 31.6 10).length == 16 && (Ticks.values 1 32.7 10).length == 6
#guard (Ticks.step 0 31.6 10).toRat == 2 && (Ticks.step 1 32.7 10).toRat == 5

end Whatwg.Svg.Value
