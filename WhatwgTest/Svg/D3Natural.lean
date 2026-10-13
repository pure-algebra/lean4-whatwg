import Whatwg.Svg.Geometry.Natural.Laws
import WhatwgTest.Svg.D3Through

/-!
# WhatwgTest.Svg.D3Natural

The tests of d3-shape for its natural spline, converted and run against `Curve.natural` of
`Whatwg/Svg/Geometry/Natural.lean` and against the generator `Curve.Through.natural` of
`Whatwg/Svg/Geometry/Natural/Laws.lean`.

**Source.** https://github.com/d3/d3-shape, the file `test/curve/natural-test.js` at commit
`a82254af78f0` of `main`. Copyright 2010-2022 Mike Bostock, ISC licence. Every expected path
below is one of d3's test vectors, typed as the test has it.

## How a case is converted

One `#guard` for one assertion of d3, with d3's call above it.

- `line().curve(curveNatural)(data)` is `Curve.natural data`.
- `area().curve(curveNatural)(data)` has d3's own `y0` of zero, so its base is the points at
  `y = 0`, and its outline is one call: `Curve.Through.natural.areaCubics data (base data)`.
  The spline has no area of its own in the kit; this is the area of every generator.
- A path of d3 is compared as an outline, piece by piece, each coordinate at six places
  (`sameOutline` of `WhatwgTest/Svg/D3Through.lean`).
- `assert.strictEqual(path, null)` is no piece.

## What was found

d3 has 10 assertions in the file, and all are converted. In 9 the kit's outline is d3's: 7
compare with d3's vector and 2 are d3's `null`. In 1, marked *dot*, d3 writes a closed subpath
of no length for one point (`M0,1Z`), and the kit has no segment, as for every curve of
`WhatwgTest/Svg/D3Shape.lean`.

Along the base of an area, at `y = 0`, the natural spline through level points is level, and
its control points stand at the thirds of each piece: d3 writes `C1.666667,0,1.333333,0,1,0`,
and the kit's piece has those four points.

The last guards are finite evaluations of what no theorem of the laws covers: the two ends of
the spline do not bend, and it bends the same way on both sides of a point.
-/

namespace WhatwgTest.Svg.D3Natural

open Whatwg.Svg.Value
open WhatwgTest.Svg.D3Through (sameOutline base)

/-- d3's `area().curve(curveNatural)(data)`: one call of the kit. -/
def area (data : List Vec) : List Cubic := Curve.Through.natural.areaCubics data (base data)

/-! ## natural-test.js -/

-- line.curve(curveNatural)([])
#guard Curve.natural [] == []
-- line.curve(curveNatural)([[0, 1]])
-- dot: d3 has "M0,1Z".
#guard Curve.natural [⟨0, 1⟩] == []
-- line.curve(curveNatural)([[0, 1], [1, 3]])
#guard sameOutline (Curve.natural [⟨0, 1⟩, ⟨1, 3⟩]) "M0,1L1,3"
-- line.curve(curveNatural)([[0, 1], [1, 3], [2, 1]])
#guard sameOutline (Curve.natural [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1"
-- line.curve(curveNatural)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard sameOutline (Curve.natural [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
  "M0,1C0.333333,2.111111,0.666667,3.222222,1,3C1.333333,2.777778,1.666667,1.222222,2,1C2.333333,0.777778,2.666667,1.888889,3,3"

-- area.curve(curveNatural)([])
#guard area [] == []
-- area.curve(curveNatural)([[0, 1]])
#guard sameOutline (area [⟨0, 1⟩]) "M0,1L0,0Z"
-- area.curve(curveNatural)([[0, 1], [1, 3]])
#guard sameOutline (area [⟨0, 1⟩, ⟨1, 3⟩]) "M0,1L1,3L1,0L0,0Z"
-- area.curve(curveNatural)([[0, 1], [1, 3], [2, 1]])
#guard sameOutline (area [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩])
  "M0,1C0.333333,2,0.666667,3,1,3C1.333333,3,1.666667,2,2,1L2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"
-- area.curve(curveNatural)([[0, 1], [1, 3], [2, 1], [3, 3]])
#guard sameOutline (area [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨3, 3⟩])
  "M0,1C0.333333,2.111111,0.666667,3.222222,1,3C1.333333,2.777778,1.666667,1.222222,2,1C2.333333,0.777778,2.666667,1.888889,3,3L3,0C2.666667,0,2.333333,0,2,0C1.666667,0,1.333333,0,1,0C0.666667,0,0.333333,0,0,0Z"

/-! ## What the rows of the system say, on five points

No theorem of the laws says that the solution satisfies its rows. These evaluations do, of one
list of five points with no pattern in it. -/

/-- Five points with no pattern. -/
def five : List Vec := [⟨0, 1⟩, ⟨2, 7⟩, ⟨3, -4⟩, ⟨7, 0⟩, ⟨8, 5⟩]

-- The spline does not bend at its two ends.
#guard ((Curve.natural five).head?.map Cubic.bend0) == some Vec.zero &&
  ((Curve.natural five).getLast?.map Cubic.bend1) == some Vec.zero

-- It bends the same way on both sides of every point between: the bend at the end of each
-- piece is the bend at the start of the next.
#guard ((Curve.natural five).dropLast.map Cubic.bend1) ==
  ((Curve.natural five).tail.map Cubic.bend0)

-- A control of the two: the cardinal spline through the same points has one velocity at each
-- point (`smooth_cubics_cardinal`), and it does not bend the same way on both sides.
#guard ((Curve.catmullRom.cubics five).dropLast.map Cubic.bend1) !=
  ((Curve.catmullRom.cubics five).tail.map Cubic.bend0)

-- A control of the generator's first law for a curve that is not the monotone one: the natural
-- spline goes above its points. Its second piece through these three passes the height `3` of
-- its highest point.
#guard (Curve.natural [⟨0, 0⟩, ⟨1, 3⟩, ⟨2, 3⟩]).any fun c => 3 < (c.pointAt (1 / 2)).y

end WhatwgTest.Svg.D3Natural
