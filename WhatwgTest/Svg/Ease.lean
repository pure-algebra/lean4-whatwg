import Whatwg.Svg.Geometry.Ease
import Whatwg.Svg.Scene.Vector

/-!
# WhatwgTest.Svg.Ease

The family of an easing (`Whatwg/Svg/Scene/Ease.lean`, `Whatwg/Svg/Geometry/Ease.lean`) under
two tests: lean4-effect4's own easings written on it, and d3-ease's tests of its cubic and its
`back` easings.

**The consumer.** `tools/Tools/View/Look.lean` of lean4-effect4 (read at `6ad8f7b8d`) has `in_`,
`out`, `inOut` and `outBack` as four formulas in per mille. `Ease.kit` below is the same seven
easings with no formula: one cubic, its turn, the two in a row, a second cubic, and two tables.
The guards compare it with the consumer's formulas, typed here as the consumer has them.

**d3.** https://github.com/d3/d3-ease, the files `test/cubic-test.js`, `test/back-test.js` and
`test/generic.js` at commit `4099c6d715f5` of `main`. Copyright 2010-2021 Mike Bostock and 2001
Robert Penner, BSD 3-Clause licence, as its `LICENSE` file has it: not the ISC licence of
d3-shape. d3 compares within a millionth (`test/asserts.js`). Here a cubic is exact, so d3's
values of `easeCubicIn` are compared as equal. Its two derived tests, `easeCubicOut` against
`out(easeCubicIn)` and `easeBackOut` against `out(easeBackIn)`, are each one law at every
progress, cited at d3's easing. `easeCubicInOut` against `inOut(easeCubicIn)` is compared at
d3's eleven moments, where the stops of the kit are exact. `easeBackIn` is compared within a
ten-thousandth and not a millionth: the kit's `back` has the heights `1567` and `-567`, which is
the overshoot `1.701`, and d3's is `1.70158`.

Not converted: `easeBackInOut`, and the tests that an easing coerces a string to a number.
-/

namespace WhatwgTest.Svg.Ease

open Whatwg.Svg.Scene

/-! ## lean4-effect4's easings, on the family -/

/-- The consumer's easings, by name. -/
inductive Ease where
  | linear | in_ | out | inOut | outBack | settle | spring
  deriving DecidableEq, Repr

/-- The consumer's critically damped spring, in per mille at every twentieth of the step. -/
def settleTable : List Int :=
  [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992, 995,
    998, 1000]

/-- The consumer's underdamped spring, in per mille at every twentieth of the step. -/
def springTable : List Int :=
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019,
    1012, 1007, 1003, 1000]

/-- **The consumer's seven easings with no formula**: a cubic, its turn, the two in a row, the
turn of a second cubic, and two tables. -/
def Ease.kit : Ease → Easing
  | .linear => Easing.linear
  | .in_ => Easing.cubicIn
  | .out => Easing.cubicIn.out
  | .inOut => Easing.cubicIn.inOut
  | .outBack => Easing.backIn.out
  | .settle => .stops settleTable
  | .spring => .stops springTable

/-- The consumer's formula for `out`, as `Look.lean` has it. -/
def consumerOut (p : Nat) : Int := 1000 - (1000 - (p : Int)) ^ 3 / 1000000

/-- The consumer's formula for `inOut`, as `Look.lean` has it. -/
def consumerInOut (p : Nat) : Int :=
  if p < 500 then 4 * (p : Int) ^ 3 / 1000000
  else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000

-- The consumer's `inOut` at its twenty-one points is `cubicIn.inOut`, stop for stop: what the
-- consumer writes to CSS for it is what the family writes.
#guard Ease.kit .inOut == Easing.sampled consumerInOut

-- The consumer's `out` is its `in_` turned, in whole numbers at every moment: its formula is
-- d3's `1 - easeIn(1 - t)` with the cube rounded down.
#guard (List.range 1001).all fun p => consumerOut p == 1000 - Easing.cubicIn.at (1000 - p)

-- The turned cubic rounds the whole reading down, so it reads the consumer's `out` or one
-- less, at every moment: the rounding that `Ease.lean` says the two differ by.
#guard (List.range 1001).all fun p =>
  let d := consumerOut p - (Ease.kit .out).at p
  d == 0 || d == 1

-- The named easings of the kit that the family now gives: the battery of
-- `Whatwg/Svg/Scene/Vector.lean` typed two of them as formulas.
#guard Easing.cubicInOut == Case.inOut
#guard Easing.backIn == Case.backIn
#guard Ease.kit .outBack == Easing.backOut

/-- The consumer's `inOut` arrives as it left: it is its own turn. The law at this carrier. -/
example : (Ease.kit .inOut).out = Ease.kit .inOut :=
  Easing.inOut_out _ _ (Easing.values_last Easing.proper_cubicIn (by decide))

/-- Five of the consumer's seven never fall: the test passes by evaluation. -/
example : [Ease.linear, .in_, .out, .inOut, .settle].all (fun e => decide e.kit.Rises) = true := by
  decide

-- A control: the two that go past the end fail the test, as they must.
#guard !decide (Ease.kit .outBack).Rises && !decide (Ease.kit .spring).Rises

-- A control of the law: the spring does go back. It reads more at six tenths of its way than
-- at its end.
#guard (Ease.kit .spring).at 600 > (Ease.kit .spring).at 1000

/-- The consumer's default move, in per mille of its step: 270 ms of 600, on its `settle`. -/
def move : Transition := { duration := 450, ease := Ease.kit .settle }

/-- **A kept thing of the consumer never goes back**: under its default move, a coordinate on
its way up is no lower at a later moment. The law at this carrier, for every two places and
every two moments. -/
example (u v : Int) (h : u ≤ v) (t t' : Nat) (ht : t ≤ t') :
    mix u v (move.at t) ≤ mix u v (move.at t') :=
  Transition.mix_mono (by decide) h ht

/-- A cubic whose first height is above its second still never goes back, where both are in
range: the law at `cubic 1000 0`. -/
example (p q : Nat) (hpq : p ≤ q) (hq : q ≤ 1000) :
    (Easing.cubic 1000 0).at p ≤ (Easing.cubic 1000 0).at q :=
  Easing.at_mono (by decide) hpq hq

-- A control of the premise: with both heights out of range by a half, the cubic goes back.
#guard (Easing.cubic 1500 (-500)).at 400 > (Easing.cubic 1500 (-500)).at 500

/-! ## d3-ease: cubic-test.js -/

-- easeCubicIn(t) returns the expected results: t = 0, 0.1, …, 1
#guard [((0 : Rat), (0 : Rat)), (1 / 10, 1 / 1000), (2 / 10, 8 / 1000), (3 / 10, 27 / 1000),
    (4 / 10, 64 / 1000), (5 / 10, 125 / 1000), (6 / 10, 216 / 1000), (7 / 10, 343 / 1000),
    (8 / 10, 512 / 1000), (9 / 10, 729 / 1000), (1, 1)].all fun x =>
  Easing.cubicIn.exact x.1 == x.2

/-- easeCubicOut(t) returns the expected results: d3 compares `easeCubicOut` with
`out(easeCubicIn)` at eleven moments. Here it is one law at every progress. -/
example (t : Rat) : Easing.cubicOut.exact t = 1 - Easing.cubicIn.exact (1 - t) :=
  Easing.exact_out_cubic 0 0 t

-- easeCubicInOut(t) returns the expected results: d3 compares `easeCubicInOut` with
-- `inOut(easeCubicIn)`, which is `(t < 0.5 ? (2t)³ : 2 - (2(1 - t))³) / 2`. Its values at
-- t = 0, 0.1, …, 1 are whole numbers of per mille, and the stops of the kit there are exact.
#guard (List.range 11).map (fun k => Easing.cubicInOut.at (100 * k)) ==
  [0, 4, 32, 108, 256, 500, 744, 892, 968, 996, 1000]

/-! ## d3-ease: back-test.js -/

-- easeBackIn(t) returns the expected results: t = 0, 0.1, …, 1. Within a ten-thousandth, and
-- not d3's millionth: the kit's heights are the overshoot 1.701, and d3's is 1.70158.
#guard [((0 : Rat), (0 : Rat)), (1 / 10, -14314 / 1000000), (2 / 10, -46451 / 1000000),
    (3 / 10, -80200 / 1000000), (4 / 10, -99352 / 1000000), (5 / 10, -87698 / 1000000),
    (6 / 10, -29028 / 1000000), (7 / 10, 92868 / 1000000), (8 / 10, 294198 / 1000000),
    (9 / 10, 591172 / 1000000), (1, 1)].all fun x =>
  let d := Easing.backIn.exact x.1 - x.2
  decide (-1 / 10000 < d) && decide (d < 1 / 10000)

-- A control of the tolerance: at d3's own millionth the kit's `back` differs at the middle.
#guard decide (1 / 1000000 < Easing.backIn.exact (1 / 2) - (-87698 / 1000000 : Rat))

/-- easeBackOut(t) returns the expected results: d3 compares `easeBackOut` with
`out(easeBackIn)` at eleven moments. Here it is one law at every progress. -/
example (t : Rat) : Easing.backOut.exact t = 1 - Easing.backIn.exact (1 - t) := by
  have e : Easing.backIn = .cubic 0 (-567) := by decide
  have o : Easing.backOut = (Easing.cubic 0 (-567)).out := by decide
  rw [e, o]
  exact Easing.exact_out_cubic 0 (-567) t

end WhatwgTest.Svg.Ease
