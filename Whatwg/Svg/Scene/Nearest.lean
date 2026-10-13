import Whatwg.Svg.Scene.Ease

/-!
# Whatwg.Svg.Scene.Nearest

Owner: the cubic easing nearest to an easing (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

An easing of the kit is stops or a cubic (`Whatwg/Svg/Scene/Motion.lean`). CSS writes stops as
`linear(…)` and a cubic as `cubic-bezier(1/3, y1, 2/3, y2)`. A reader that knows `cubic-bezier`
alone needs a cubic for an easing that is stops: a spring, an easing in and out, a table.
lean4-effect4 computes one by hand for each of its easings (`Ease.bezier` of its
`tools/Tools/View/Look.lean`, with `roundDiv`): the cubic of the family whose values at the
twenty-one points of the easing are nearest those points, by least squares. This module has
that computation, for any number of stops.

The cubic of the heights `y1` and `y2` reads `3 y1 s (1 - s)² + 3 y2 s² (1 - s) + s³` at the
progress `s`. It is linear in the two heights. So the two heights for which the sum of the
squares of the distances to the stops is least are the solution of two linear equations, the
normal equations, whose five numbers are sums over the stops. Every stop is at a share `i / n`
of the progress, and with each term multiplied by `n³` every number is whole.

- `Easing.roundDiv a b`: the quotient to the nearest whole number, a half going up, for a `b`
  that is more than zero.
- `Easing.nearestRow n i v`: what the stop `i` of `n` pieces, with the value `v`, adds to the
  equations: the two terms that the heights multiply, and what is left of the value after the
  cube of the progress.
- `Easing.Sums.of rows`: the five sums. `Sums.det` is the number both heights are divided by,
  and `Sums.num1` and `Sums.num2` are what is divided.
- `Easing.nearestCubic values`: **the two heights, in per mille, each rounded to the nearest
  whole number.** `Easing.points e pieces`: the readings of an easing at `pieces + 1` evenly
  spaced moments, which are lean4-effect4's `Ease.points` at twenty pieces.
  `Easing.nearest e pieces`: the cubic easing nearest to `e`, by those points. It reads the
  points and not the stops of the easing: the easing `linear` has two stops, which are too few
  for the two equations, and twenty-one points.

The laws of this module are of the data: `nearest` gives a cubic, so it is proper
(`nearest_proper`), and a quotient of a multiple is the multiplier (`roundDiv_mul`).
`Whatwg/Svg/Geometry/Nearest.lean` says what the two heights are: the exact answer of the
least squares, rounded (`nearestCubic_eq_round`); that no pair of rational heights is nearer
the stops than the exact answer (`nearestExact_least`); and that stops which stand on a cubic
give that cubic back (`nearestCubic_of_cubic`).

What this module does not claim. With fewer than four stops the two equations are one, the
number `Sums.det` is `0`, and both heights read `0`, since a quotient by `0` is `0`: the laws
ask that it is more than `0`. The nearest cubic is nearest at the stops, and nothing is said of
the progress between two stops. It is the nearest of the cubics whose two control points stand
at a third and at two thirds of the progress, and a `cubic-bezier` with other abscissae may be
nearer. A cubic that is nearest an easing which goes past its end need not go past it.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Easing

/-- `a / b` to the nearest whole number, a half going up, for a `b` that is more than zero. -/
def roundDiv (a b : Int) : Int := (2 * a + b) / (2 * b)

/-- **What a stop adds to the two equations.** For the stop `i` of `pieces` pieces, with the
value `v` per mille: `3 i (n - i)²` and `3 i² (n - i)`, which are the two terms of the cubic
that the heights multiply, each times `n³`; and `n³ v - 1000 i³`, which is what is left of the
value after the cube of the progress, times `n³`. -/
def nearestRow (pieces i : Nat) (v : Int) : Int × Int × Int :=
  (3 * (i : Int) * ((pieces : Int) - (i : Int)) ^ 2,
    3 * (i : Int) ^ 2 * ((pieces : Int) - (i : Int)),
    (pieces : Int) ^ 3 * v - 1000 * (i : Int) ^ 3)

/-- The rows of the stops of an easing, one for each stop. -/
def nearestRows (values : List Int) : List (Int × Int × Int) :=
  values.zipIdx.map fun vi => nearestRow (values.length - 1) vi.2 vi.1

/-- The five sums of the two normal equations. With `b1` and `b2` the two terms of a row and
`r` what it leaves: the sums of `b1 b1`, of `b1 b2`, of `b2 b2`, of `b1 r` and of `b2 r`. -/
structure Sums where
  a11 : Int
  a12 : Int
  a22 : Int
  r1 : Int
  r2 : Int

namespace Sums

/-- The five sums over a list of rows. -/
def of : List (Int × Int × Int) → Sums
  | [] => ⟨0, 0, 0, 0, 0⟩
  | row :: rest =>
    ⟨row.1 * row.1 + (of rest).a11, row.1 * row.2.1 + (of rest).a12,
      row.2.1 * row.2.1 + (of rest).a22, row.1 * row.2.2 + (of rest).r1,
      row.2.1 * row.2.2 + (of rest).r2⟩

/-- The number both heights are divided by. It is `0` exactly where the two terms of every row
stand in one ratio, as with three stops or fewer. -/
def det (s : Sums) : Int := s.a11 * s.a22 - s.a12 * s.a12

/-- What the first height is: this number over `det`. -/
def num1 (s : Sums) : Int := s.r1 * s.a22 - s.r2 * s.a12

/-- What the second height is: this number over `det`. -/
def num2 (s : Sums) : Int := s.a11 * s.r2 - s.a12 * s.r1

end Sums

/-- **The two heights of the cubic nearest to stops**, in per mille, each rounded to the
nearest whole number. Of the cubics `cubic-bezier(1/3, y1, 2/3, y2)` it is the one whose values
at the stops are nearest the values of the stops, by the sum of the squares of the
distances. -/
def nearestCubic (values : List Int) : Int × Int :=
  (roundDiv (Sums.of (nearestRows values)).num1 (Sums.of (nearestRows values)).det,
    roundDiv (Sums.of (nearestRows values)).num2 (Sums.of (nearestRows values)).det)

/-- **The points of an easing**: its readings at `pieces + 1` evenly spaced moments, from `0`
to `1000`. They are the stops of `Easing.sampled e.at pieces`, and what CSS's `linear(…)` is
written from. Stops are read too, so stops of two values have as many points as any easing. -/
def points (e : Easing) (pieces : Nat := 20) : List Int :=
  (List.range (pieces + 1)).map fun i => e.at (i * 1000 / pieces)

/-- **The cubic easing nearest to an easing**, by its points at `pieces + 1` evenly spaced
moments. A reader that knows `cubic-bezier` alone takes this in place of the easing. -/
def nearest (e : Easing) (pieces : Nat := 20) : Easing :=
  .cubic (nearestCubic (e.points pieces)).1 (nearestCubic (e.points pieces)).2

/-- The points of an easing are the stops of the easing sampled. -/
theorem sampled_points (e : Easing) (pieces : Nat) :
    sampled e.at pieces = stops (e.points pieces) := rfl

/-- The points of a cubic are its values. -/
theorem points_cubic (y1 y2 : Int) (pieces : Nat) :
    (cubic y1 y2).points pieces = (cubic y1 y2).values pieces := rfl

/-- An easing has a point for each piece, and one more. -/
theorem length_points (e : Easing) (pieces : Nat) : (e.points pieces).length = pieces + 1 := by
  show ((List.range (pieces + 1)).map fun i => e.at (i * 1000 / pieces)).length = pieces + 1
  rw [List.length_map, List.length_range]

/-- The nearest cubic is a cubic of the two heights. -/
theorem nearest_eq (e : Easing) (pieces : Nat) :
    e.nearest pieces = cubic (nearestCubic (e.points pieces)).1 (nearestCubic (e.points pieces)).2 :=
  rfl

/-- **The nearest cubic starts at `0` and ends at `1000`**, whatever the easing does. -/
theorem nearest_proper (e : Easing) (pieces : Nat) : (e.nearest pieces).Proper :=
  proper_cubic _ _

/-- **A multiple of a number, over that number, rounds to the multiplier.** Heights that are
whole come back as they are. -/
theorem roundDiv_mul (y : Int) {b : Int} (hb : 0 < b) : roundDiv (y * b) b = y := by
  have h2 : (2 : Int) * b ≠ 0 := fun h => absurd h (by omega)
  have e : 2 * (y * b) + b = b + y * (2 * b) := by
    rw [Int.mul_left_comm 2 y b, Int.add_comm]
  show (2 * (y * b) + b) / (2 * b) = y
  rw [e, Int.add_mul_ediv_right b y h2, Int.ediv_eq_zero_of_lt (Int.le_of_lt hb) (by omega),
    Int.zero_add]

end Easing

end Whatwg.Svg.Scene
