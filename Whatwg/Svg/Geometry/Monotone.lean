import Whatwg.Svg.Geometry.Cubic

/-!
# Whatwg.Svg.Geometry.Monotone

Owner: the curve through points that does not overshoot them (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`). `Whatwg/Svg/Geometry/Shape.lean` says that it does not claim
`curveMonotoneX`; this module has it.

A cardinal spline through values that rise and then stay level goes above the level before it
comes back to it. A chart drawn so shows a value that the data never had: a count below zero, a
share above the whole. The monotone curve is a cubic through every point whose slope at each
point is chosen so that this cannot happen.

The algorithm is d3-shape's `curveMonotoneX`, read from its source `src/curve/monotone.js` at
commit `a82254af78f0` (ISC licence, Copyright 2010-2022 Mike Bostock). d3 takes the slopes from
Steffen, "A Simple Method for Monotonic Interpolation in One Dimension", Astronomy and
Astrophysics 239 (1990), as its source says.

- `Monotone.slope3 p0 p1 p2`: the slope at the middle of three points (d3's `slope3`). It is
  `0` where the two chords go opposite ways, and otherwise no steeper than twice either chord.
- `Monotone.slope2 p0 p1 t`: the slope at an end of the curve, from the slope `t` at the other
  end of the same piece (d3's `slope2`).
- `Monotone.segment p0 p1 t0 t1`: the cubic from `p0` to `p1` with those slopes (d3's `point`):
  each control point a third of the way across.
- `Monotone.distinct`: the points with no point that is the one before it again. d3 passes over
  such a point.
- `Curve.monotoneX points`: the curve, one cubic between each point and the next. Two points
  give a straight segment. `Curve.monotoneY points` is the same with the two axes exchanged, as
  d3's `curveMonotoneY` is.

d3 computes in floating point, and where an abscissa is repeated it divides by zero and reads
the result as an infinite slope with a sign. Here the numbers are exact and nothing is divided
by zero: `slope3` has a case for each of those readings, and the tests of
`WhatwgTest/Svg/D3Monotone.lean` run d3's own vectors against it, the ones with a repeated
abscissa included.

The laws are in `Whatwg/Svg/Geometry/Monotone/Laws.lean`. A path is written with
`Path.ofCubics` of `Whatwg/Svg/Geometry/Write.lean`.

What this module does not claim: d3's dot for one point (`M0,1Z`), where this module has no
segment, as for every other curve of the kit; d3's reading where the abscissae go forth and
back by the same amount, which depends there on how a product rounds, and is exact here.
-/

namespace Whatwg.Svg.Value

namespace Monotone

/-- `-1` below zero and `1` from zero on: d3's `sign`. -/
def sign (x : Rat) : Rat := if x < 0 then -1 else 1

/-- A number with no sign. -/
def size (x : Rat) : Rat := if x < 0 then -x else x

/-- The sign of the slope of a piece that stands upright, as d3 reads it. The piece rises by
`d`, and its neighbour runs across by `h`: the slope is read as endless, upward where `d` and
`h` have one sign. -/
def upright (d h : Rat) : Rat :=
  if d < 0 then (if h < 0 then 1 else -1) else (if h < 0 then -1 else 1)

/-- **The slope at the middle of three points**: d3's `slope3`, after Steffen. With `s0` and
`s1` the slopes of the two chords and `p` the slope there of the parabola through the three
points, it is `(sign s0 + sign s1) * min |s0| |s1| (|p| / 2)`. So it is `0` where the chords go
opposite ways, and it is no more than twice either chord. A chord that stands upright has no
slope, and the cases before the last are d3's readings of it. -/
def slope3 (p0 p1 p2 : Vec) : Rat :=
  let h0 := p1.x - p0.x
  let h1 := p2.x - p1.x
  let d0 := p1.y - p0.y
  let d1 := p2.y - p1.y
  if h0 = 0 then
    if h1 = 0 ∨ d0 = 0 then 0 else (upright d0 h1 + sign (d1 / h1)) * size (d1 / h1)
  else if h1 = 0 then
    if d1 = 0 then 0 else (sign (d0 / h0) + upright d1 h0) * size (d0 / h0)
  else if h0 + h1 = 0 then
    if d0 + d1 = 0 then 0
    else (sign (d0 / h0) + sign (d1 / h1)) * min (size (d0 / h0)) (size (d1 / h1))
  else
    (sign (d0 / h0) + sign (d1 / h1)) *
      min (min (size (d0 / h0)) (size (d1 / h1)))
        (size ((d0 / h0 * h1 + d1 / h1 * h0) / (h0 + h1)) / 2)

/-- **The slope at an end of the curve**: d3's `slope2`. `t` is the slope at the other end of
the piece from `p0` to `p1`. An upright piece keeps `t`. -/
def slope2 (p0 p1 : Vec) (t : Rat) : Rat :=
  if p1.x - p0.x = 0 then t else (3 * (p1.y - p0.y) / (p1.x - p0.x) - t) / 2

/-- **The piece from `p0` to `p1`** that leaves with the slope `t0` and arrives with the slope
`t1`: d3's `point`. Each control point is a third of the way across from its end. -/
def segment (p0 p1 : Vec) (t0 t1 : Rat) : Cubic :=
  ⟨p0, ⟨p0.x + (p1.x - p0.x) / 3, p0.y + (p1.x - p0.x) / 3 * t0⟩,
    ⟨p1.x - (p1.x - p0.x) / 3, p1.y - (p1.x - p0.x) / 3 * t1⟩, p1⟩

/-- The points with no point that is the one before it again. -/
def distinct : List Vec → List Vec
  | a :: b :: rest => if a = b then distinct (b :: rest) else a :: distinct (b :: rest)
  | points => points

/-- The pieces from `p0` on, where the curve leaves `p0` with the slope `t0`: to `p1`, and on
through `rest`. The slope at each point between two others is `slope3`, and at the last point
`slope2`. -/
def pieces (p0 : Vec) (t0 : Rat) (p1 : Vec) : List Vec → List Cubic
  | [] => [segment p0 p1 t0 (slope2 p0 p1 t0)]
  | p2 :: rest => segment p0 p1 t0 (slope3 p0 p1 p2) :: pieces p1 (slope3 p0 p1 p2) p2 rest

/-- A point with its two coordinates exchanged. -/
def swap (p : Vec) : Vec := ⟨p.y, p.x⟩

end Monotone

namespace Curve

/-- **The monotone curve through the points**, along `x`: d3's `curveMonotoneX`. One cubic
joins each point to the next, and two points give a straight segment. No piece leaves the box
of its own two points, and a piece between two points of which the second is no lower never
falls (`monotoneX_within` and `monotoneX_rises` of `Whatwg/Svg/Geometry/Monotone/Laws.lean`). -/
def monotoneX (points : List Vec) : List Cubic :=
  match Monotone.distinct points with
  | a :: b :: c :: rest =>
    Monotone.pieces a (Monotone.slope2 a b (Monotone.slope3 a b c)) b (c :: rest)
  | [a, b] => [Cubic.line a b]
  | _ => []

/-- **The monotone curve through the points**, along `y`: d3's `curveMonotoneY`. It is
`monotoneX` with the two axes exchanged, before and after. -/
def monotoneY (points : List Vec) : List Cubic :=
  (monotoneX (points.map Monotone.swap)).map (Cubic.map Monotone.swap)

end Curve

end Whatwg.Svg.Value
