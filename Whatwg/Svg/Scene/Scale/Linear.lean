import Whatwg.Svg.Scene.Scale.Invert

/-!
# Whatwg.Svg.Scene.Scale.Linear

Owner: a straight line over quantities of both signs, and what its inverse undoes (slice S22
of `docs/SVG-PACKAGE-PLAN.md`; ask W16 of `docs/research/2026-10-12-whatwg-requests.md`).

A run has counts of several kinds on one axis: units held up to a brim, a pressure above it,
and a deficit below zero (`docs/research/2026-10-13-living-quantities/README.md`, the layer
"one level"). A `Scale.linear` takes such a domain as it is: its data are whole numbers of
either sign. This module says where zero stands on it, how high a value stands from there,
and how far the inverse of `Whatwg/Svg/Scene/Scale/Invert.lean` is from undoing it.

- `Scale.baseline s`: **where zero stands**, the length of no quantity.

Where zero stands, and the height of a value:

- `at_le_baseline`, `baseline_le_at`: on a scale that rises, a deficit is drawn at the baseline
  or before it, and a count that is not negative at the baseline or after it. On a scale that
  falls, as down a screen, it is the other way (`baseline_le_at_of_falling`,
  `at_le_baseline_of_falling`).
- **A height is the value on the scale** (`linear_height`): on a `linear` scale with a whole
  number `u` of units of length for each unit of the quantity, a value `v` stands `u * v` from
  the baseline, with no rounding, and the baseline is `lo - u * dataLo` (`linear_baseline`). A
  layer drawn from the baseline to the mark of its count is as high as its count.
- **With rounding, to one unit** (`linear_height_near`): on any `linear` scale a value `v`
  stands its share of the range from the baseline, rounded down, or one unit more.

**The inverse undoes the scale**, on a `linear` scale that rises, in both directions:

- From a value (`linear_undo_value`): `invert (at v)` is `v` or a later value, and the two are
  less than one unit of length apart on the scale. With one unit of length or more for each
  unit of the quantity it is `v` (`Scale.invert_at_linear`).
- From a mark (`linear_undo_mark`): `at (invert y)` is `y` or an earlier mark, and the two are
  no further apart than the whole units of length in one unit of the quantity. With one unit of
  the quantity or more for each unit of length it is `y` (`Scale.at_invert_linear`).
- **With exactly one unit of length for each unit of the quantity, both are equalities**
  (`linear_undo_exact`): the scale and its inverse undo each other, and nothing is rounded.

What this module does not claim: the same two bounds for a `linear` scale that falls, where the
inverse answers the first value drawn like `v` and the bounds hold with the signs turned; nor
any of this for a `root`, a `log2` or a `steps` scale.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Scale

/-! ## Where zero stands -/

/-- **Where zero stands**: the length of no quantity. On a scale from nothing it is nothing
(`Scale.fromZero_at`), and on a scale over quantities of both signs it is the line that a
deficit hangs below. -/
def baseline (s : Scale) : Int := s.at 0

/-- On a scale that rises, a deficit is drawn at the baseline or before it. -/
theorem at_le_baseline (s : Scale) (h : s.Rising) {v : Int} (hv : v ≤ 0) : s.at v ≤ s.baseline :=
  at_mono s h hv

/-- On a scale that rises, a count that is not negative is drawn at the baseline or after
it. -/
theorem baseline_le_at (s : Scale) (h : s.Rising) {v : Int} (hv : 0 ≤ v) : s.baseline ≤ s.at v :=
  at_mono s h hv

/-- On a scale that falls, a deficit is drawn at the baseline or after it: below it, on a
screen whose ordinates grow downward. -/
theorem baseline_le_at_of_falling (s : Scale) (h : s.Falling) {v : Int} (hv : v ≤ 0) :
    s.baseline ≤ s.at v :=
  at_anti s h hv

/-- On a scale that falls, a count that is not negative is drawn at the baseline or before
it. -/
theorem at_le_baseline_of_falling (s : Scale) (h : s.Falling) {v : Int} (hv : 0 ≤ v) :
    s.at v ≤ s.baseline :=
  at_anti s h hv

/-- A scale from nothing has its baseline at nothing. -/
theorem baseline_of_fromZero (s : Scale) (h : s.fromZero = true) : s.baseline = 0 :=
  fromZero_at s h

/-! ## The height of a value -/

/-- The quotient of a sum is the sum of the quotients, or one more: two roundings down differ
from one by a unit at most. -/
theorem ediv_add_near {d : Int} (hd : 0 < d) (x y : Int) :
    x / d + y / d ≤ (x + y) / d ∧ (x + y) / d ≤ x / d + y / d + 1 := by
  have hx := Int.emod_add_mul_ediv x d
  have hy := Int.emod_add_mul_ediv y d
  have rx0 := Int.emod_nonneg x (Int.ne_of_gt hd)
  have rx1 := Int.emod_lt_of_pos x hd
  have ry0 := Int.emod_nonneg y (Int.ne_of_gt hd)
  have ry1 := Int.emod_lt_of_pos y hd
  have e : x + y = x % d + y % d + d * (x / d + y / d) := by
    rw [Int.mul_add]
    omega
  have q : (x + y) / d = (x % d + y % d) / d + (x / d + y / d) := by
    rw [e, Int.add_mul_ediv_left _ _ (Int.ne_of_gt hd)]
  have l0 : 0 ≤ (x % d + y % d) / d := Int.ediv_nonneg (by omega) (Int.le_of_lt hd)
  have l1 : (x % d + y % d) / d < 2 := Int.ediv_lt_of_lt_mul hd (by omega)
  constructor
  · omega
  · omega

/-- **Where zero stands on a line with no rounding.** -/
theorem linear_baseline (dataLo dataHi lo hi u : Int) (hd : dataLo < dataHi)
    (hu : hi - lo = u * (dataHi - dataLo)) (h0 : dataLo ≤ 0) (h1 : 0 ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).baseline = lo - u * dataLo := by
  unfold baseline
  rewrite [linear_exact dataLo dataHi lo hi u hd hu h0 h1, Int.mul_sub, Int.mul_zero]
  omega

/-- **A height is the value on the scale.** On a `linear` scale with a whole number `u` of
units of length for each unit of the quantity, over quantities of both signs, a value stands
`u` units from the baseline for each unit of it: above the baseline for a count, below it for a
deficit, on the other sides where `u` is negative. Nothing is rounded. -/
theorem linear_height (dataLo dataHi lo hi u : Int) (hd : dataLo < dataHi)
    (hu : hi - lo = u * (dataHi - dataLo)) (h0 : dataLo ≤ 0) (h1 : 0 ≤ dataHi) {v : Int}
    (hv0 : dataLo ≤ v) (hv1 : v ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).at v - (Scale.linear dataLo dataHi lo hi).baseline =
      u * v := by
  rewrite [linear_baseline dataLo dataHi lo hi u hd hu h0 h1,
    linear_exact dataLo dataHi lo hi u hd hu hv0 hv1, Int.mul_sub]
  omega

/-- **A height is the value's share of the range, to one unit.** On any `linear` scale over
quantities of both signs, a value stands from the baseline by its share of the range rounded
down, or by one unit more. -/
theorem linear_height_near (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) (h0 : dataLo ≤ 0)
    (h1 : 0 ≤ dataHi) {v : Int} (hv0 : dataLo ≤ v) (hv1 : v ≤ dataHi) :
    (hi - lo) * v / (dataHi - dataLo) ≤
        (Scale.linear dataLo dataHi lo hi).at v - (Scale.linear dataLo dataHi lo hi).baseline ∧
      (Scale.linear dataLo dataHi lo hi).at v - (Scale.linear dataLo dataHi lo hi).baseline ≤
        (hi - lo) * v / (dataHi - dataLo) + 1 := by
  have hD : 0 < dataHi - dataLo := by omega
  have n := ediv_add_near hD ((hi - lo) * (0 - dataLo)) ((hi - lo) * v)
  have e : (hi - lo) * (0 - dataLo) + (hi - lo) * v = (hi - lo) * (v - dataLo) := by
    rw [← Int.mul_add]
    exact congrArg ((hi - lo) * ·) (by omega)
  rw [e] at n
  show (hi - lo) * v / (dataHi - dataLo) ≤
      lineAt dataLo dataHi lo hi v - lineAt dataLo dataHi lo hi 0 ∧
    lineAt dataLo dataHi lo hi v - lineAt dataLo dataHi lo hi 0 ≤
      (hi - lo) * v / (dataHi - dataLo) + 1
  unfold lineAt
  rw [clamp_of_mem hv0 hv1, clamp_of_mem h0 h1]
  obtain ⟨n1, n2⟩ := n
  constructor
  · omega
  · omega

/-! ## What the inverse undoes -/

/-- Two values that a line draws alike are less than one unit of length apart on it. -/
theorem lineAt_tie_near (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) {a b : Int}
    (ha : dataLo ≤ a) (hab : a ≤ b) (hb : b ≤ dataHi)
    (he : lineAt dataLo dataHi lo hi a = lineAt dataLo dataHi lo hi b) :
    (hi - lo) * (b - a) < dataHi - dataLo := by
  have hD : 0 < dataHi - dataLo := by omega
  unfold lineAt at he
  rw [clamp_of_mem ha (by omega), clamp_of_mem (by omega) hb] at he
  have q : (hi - lo) * (a - dataLo) / (dataHi - dataLo) =
      (hi - lo) * (b - dataLo) / (dataHi - dataLo) := by omega
  have l1 := Int.ediv_mul_le ((hi - lo) * (a - dataLo)) (Int.ne_of_gt hD)
  have l2 := Int.lt_ediv_add_one_mul_self ((hi - lo) * (b - dataLo)) hD
  rw [← q, Int.add_mul, Int.one_mul] at l2
  have e : (hi - lo) * (b - dataLo) - (hi - lo) * (a - dataLo) = (hi - lo) * (b - a) := by
    rw [← Int.mul_sub]
    exact congrArg ((hi - lo) * ·) (by omega)
  generalize (hi - lo) * (a - dataLo) / (dataHi - dataLo) * (dataHi - dataLo) = k at l1 l2
  omega

/-- One unit of the quantity moves the mark by the whole units of length in it, or by one
more. -/
theorem lineAt_succ_near (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) {v : Int}
    (h1 : dataLo ≤ v) (h2 : v < dataHi) :
    lineAt dataLo dataHi lo hi (v + 1) ≤
      lineAt dataLo dataHi lo hi v + (hi - lo) / (dataHi - dataLo) + 1 := by
  have hD : 0 < dataHi - dataLo := by omega
  have n := (ediv_add_near hD ((hi - lo) * (v - dataLo)) (hi - lo)).2
  have e : (hi - lo) * (v - dataLo) + (hi - lo) = (hi - lo) * (v + 1 - dataLo) := by
    have e' : v + 1 - dataLo = v - dataLo + 1 := by omega
    rw [e', Int.mul_add, Int.mul_one]
  rw [e] at n
  unfold lineAt
  rw [clamp_of_mem (v := v + 1) (by omega) (by omega), clamp_of_mem h1 (by omega)]
  omega

/-- **The inverse undoes the scale, from a value.** On a `linear` scale that rises, the value
under the mark of `v` is `v` or a later value, and the two are less than one unit of length
apart on the scale: the scale had drawn them alike. -/
theorem linear_undo_value (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) (hr : lo ≤ hi)
    {v : Int} (h1 : dataLo ≤ v) (h2 : v ≤ dataHi) :
    v ≤ (Scale.linear dataLo dataHi lo hi).invert ((Scale.linear dataLo dataHi lo hi).at v) ∧
      (hi - lo) *
          ((Scale.linear dataLo dataHi lo hi).invert ((Scale.linear dataLo dataHi lo hi).at v) -
            v) < dataHi - dataLo := by
  have hR : (Scale.linear dataLo dataHi lo hi).Rising := hr
  have hle : v ≤ (Scale.linear dataLo dataHi lo hi).invert
      ((Scale.linear dataLo dataHi lo hi).at v) := le_invert_at _ hR h1 h2
  have hm : (Scale.linear dataLo dataHi lo hi).invert
      ((Scale.linear dataLo dataHi lo hi).at v) ≤ dataHi :=
    (invert_mem (Scale.linear dataLo dataHi lo hi) (Int.le_of_lt hd) _).2
  have he : lineAt dataLo dataHi lo hi v = lineAt dataLo dataHi lo hi
      ((Scale.linear dataLo dataHi lo hi).invert ((Scale.linear dataLo dataHi lo hi).at v)) :=
    (at_invert_at _ hR h1 h2).symm
  exact ⟨hle, lineAt_tie_near dataLo dataHi lo hi hd h1 hle hm he⟩

/-- **The inverse undoes the scale, from a mark.** On a `linear` scale that rises, the mark of
the value under a mark `y` of the range is `y` or an earlier mark, and the two are no further
apart than the whole units of length in one unit of the quantity. -/
theorem linear_undo_mark (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) (hr : lo ≤ hi)
    {y : Int} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    (Scale.linear dataLo dataHi lo hi).at ((Scale.linear dataLo dataHi lo hi).invert y) ≤ y ∧
      y - (Scale.linear dataLo dataHi lo hi).at ((Scale.linear dataLo dataHi lo hi).invert y) ≤
        (hi - lo) / (dataHi - dataLo) := by
  have hR : (Scale.linear dataLo dataHi lo hi).Rising := hr
  have hdm : (Scale.linear dataLo dataHi lo hi).domain.1 ≤
      (Scale.linear dataLo dataHi lo hi).domain.2 := Int.le_of_lt hd
  have e1 : (Scale.linear dataLo dataHi lo hi).at dataLo = lo :=
    linear_lo dataLo dataHi lo hi (Int.le_of_lt hd)
  have e2 : (Scale.linear dataLo dataHi lo hi).at dataHi = hi := linear_hi dataLo dataHi lo hi hd
  have hy : (Scale.linear dataLo dataHi lo hi).at
      (Scale.linear dataLo dataHi lo hi).domain.1 ≤ y := by
    show (Scale.linear dataLo dataHi lo hi).at dataLo ≤ y
    rw [e1]
    exact h1
  have hle := at_invert_le _ hR hy
  have hq : 0 ≤ (hi - lo) / (dataHi - dataLo) := Int.ediv_nonneg (by omega) (by omega)
  refine ⟨hle, ?_⟩
  rcases Int.lt_or_eq_of_le h2 with hlt | heq
  · have hlt' : y < (Scale.linear dataLo dataHi lo hi).at
        (Scale.linear dataLo dataHi lo hi).domain.2 := by
      show y < (Scale.linear dataLo dataHi lo hi).at dataHi
      rw [e2]
      exact hlt
    have hs : y < lineAt dataLo dataHi lo hi ((Scale.linear dataLo dataHi lo hi).invert y + 1) :=
      lt_at_invert_succ _ hR hdm hy hlt'
    have hm := invert_mem (Scale.linear dataLo dataHi lo hi) hdm y
    have hm2 : (Scale.linear dataLo dataHi lo hi).invert y ≤ dataHi := hm.2
    have hne : (Scale.linear dataLo dataHi lo hi).invert y < dataHi := by
      rcases Int.lt_or_eq_of_le hm2 with hl | he
      · exact hl
      · rw [he, e2] at hle
        exact absurd hlt (Int.not_lt.mpr hle)
    have hstep := lineAt_succ_near dataLo dataHi lo hi hd hm.1 hne
    show y - lineAt dataLo dataHi lo hi ((Scale.linear dataLo dataHi lo hi).invert y) ≤
      (hi - lo) / (dataHi - dataLo)
    omega
  · have ei : (Scale.linear dataLo dataHi lo hi).invert y = dataHi :=
      invert_of_le _ hR hdm (by
        show (Scale.linear dataLo dataHi lo hi).at dataHi ≤ y
        rw [e2]
        exact Int.le_of_eq heq.symm)
    rw [ei, e2]
    omega

/-- **With exactly one unit of length for each unit of the quantity, the scale and its inverse
undo each other**: every value of the domain is given back, and every mark of the range. -/
theorem linear_undo_exact (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi)
    (hu : hi - lo = dataHi - dataLo) :
    (∀ v : Int, dataLo ≤ v → v ≤ dataHi →
        (Scale.linear dataLo dataHi lo hi).invert ((Scale.linear dataLo dataHi lo hi).at v) = v) ∧
      ∀ y : Int, lo ≤ y → y ≤ hi →
        (Scale.linear dataLo dataHi lo hi).at ((Scale.linear dataLo dataHi lo hi).invert y) = y :=
  ⟨fun _ h1 h2 => invert_at_linear dataLo dataHi lo hi (by omega) h1 h2,
    fun _ h1 h2 => at_invert_linear dataLo dataHi lo hi hd (by omega) (by omega) h1 h2⟩

end Scale

/-! ## Finite evaluations -/

-- The level of the living-quantities sketch: counts from a deficit of `1` to a pressure of `3`
-- on a screen, from the ordinate `176` up to the ordinate `72`. Zero stands at `150`, the brim
-- of a vessel of two at `98`, and each unit is `26` high.
#guard (Scale.linear (-1) 3 176 72).baseline == 150
#guard [-1, 0, 1, 2, 3].map (Scale.linear (-1) 3 176 72).at == [176, 150, 124, 98, 72]
#guard [-1, 1, 2, 3].map (fun v => (Scale.linear (-1) 3 176 72).at v -
  (Scale.linear (-1) 3 176 72).baseline) == [26, -26, -52, -78]

-- A control of `linear_height`, which asks for a whole number of units of length for each unit
-- of the quantity. Seven values on ten units of length: the heights from the baseline are
-- `10 * v / 6` rounded down, or one more.
#guard [-2, -1, 1, 2, 3, 4].map (fun v => (Scale.linear (-2) 4 0 10).at v -
  (Scale.linear (-2) 4 0 10).baseline) == [-3, -2, 2, 3, 5, 7]
#guard [-2, -1, 1, 2, 3, 4].map (fun v => (10 : Int) * v / 6) == [-4, -2, 1, 3, 5, 6]

-- What the inverse undoes, with the rounding. A scale with ties, ten values on five units:
-- from a value, the answer is the value or the next, less than one unit of length away.
#guard (List.range 11).map (fun v => (Scale.linear 0 10 0 5).invert ((Scale.linear 0 10 0 5).at
  (v : Nat)) - (v : Nat)) == [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]
-- A scale with gaps, five values on ten units: from a mark, the answer is the mark or the one
-- before, and `10 / 5 = 2` units of length is the most that can lie between them.
#guard (List.range 11).map (fun (y : Nat) => (y : Int) - (Scale.linear 0 5 0 10).at
  ((Scale.linear 0 5 0 10).invert (y : Int))) == [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
-- With one unit of length for each unit of the quantity, both ways give back what was asked:
-- the eight values from `-3` to `4`, and the eight marks from `10` to `17`.
#guard [-3, -2, -1, 0, 1, 2, 3, 4].all fun (v : Int) =>
  (Scale.linear (-3) 4 10 17).invert ((Scale.linear (-3) 4 10 17).at v) == v
#guard [10, 11, 12, 13, 14, 15, 16, 17].all fun (y : Int) =>
  (Scale.linear (-3) 4 10 17).at ((Scale.linear (-3) 4 10 17).invert y) == y

end Whatwg.Svg.Scene
