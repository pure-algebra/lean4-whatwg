import Whatwg.Svg.Geometry.Cubic

/-!
# Whatwg.Svg.Geometry.Natural

Owner: the natural cubic spline through a list of points (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`). `Whatwg/Svg/Geometry/Shape.lean` says that it does not claim
`curveNatural`; this module has it.

A cardinal spline chooses the direction at a point from its two neighbours. The natural spline
chooses every direction at once, so that the curve bends the same way on both sides of every
point and does not bend at its two ends. Of the curves through the points with one direction at
each, it is the one a thin rod takes when it is held at the points.

The algorithm is d3-shape's `curveNatural`, read from its source `src/curve/natural.js` at
commit `a82254af78f0` (ISC licence, Copyright 2010-2022 Mike Bostock). d3 solves one system of
equations for the abscissae and the same system for the ordinates; here the unknowns are points,
and it is solved once. The system has one row for each piece, and its unknown is the first
control point of the piece. With `K` the points and `P` the unknowns:

- the first row is `2 P₀ + P₁ = K₀ + 2 K₁`;
- a row between is `Pᵢ₋₁ + 4 Pᵢ + Pᵢ₊₁ = 4 Kᵢ + 2 Kᵢ₊₁`;
- the last row is `2 Pₙ₋₂ + 7 Pₙ₋₁ = 8 Kₙ₋₁ + Kₙ`.

Each row has three unknowns at most, each beside the next, so the system is solved in one pass
down and one pass up (`Natural.solve`). The numbers are exact, and nothing is divided by zero:
the number a row is divided by is `2` in the first row and is more than `2` in every other
(`Natural.pivots_rows` of the laws).

- `Natural.solve b r rows`: the unknowns from a row on, where the row reads `b P + P' = r`
  after the rows before it have been taken out of it, and `rows` are the rows after it.
- `Natural.rows points`: the rows after the first, each its three numbers: what stands before
  the unknown of the row before, what stands before its own, and its right side.
- `Natural.firsts points`: the first control point of each piece.
- `Natural.pieces points firsts`: the pieces. The second control point of a piece is the
  mirror image of the first control point of the next piece in the point between them, so the
  curve has one velocity there; the second control point of the last piece is half way between
  its first control point and its end.
- `Curve.natural points`: the curve. Two points give a straight segment, as in d3.

The laws are in `Whatwg/Svg/Geometry/Natural/Laws.lean`, with the curve as a generator
(`Curve.Through.natural`), which gives it a line, a pen and an area.

What this module does not claim: d3's dot for one point (`M0,1Z`), where this module has no
segment, as for every other curve of the kit; that the curve stays between its points, which it
does not (the monotone curve of `Whatwg/Svg/Geometry/Monotone.lean` does).
-/

namespace Whatwg.Svg.Value

namespace Natural

/-- The unknown of a row that reads `b P + P' = r`, and the unknowns after it: `P` is what is
left of `r` after the first of them, over `b`. -/
def back (b : Rat) (r : Vec) (tail : List Vec) : List Vec :=
  Vec.scale (1 / b) (r - tail.headD Vec.zero) :: tail

/-- **The unknowns from a row on.** The row reads `b P + P' = r`, with no `P'` where no row
follows. Each row after it is three numbers: `a'` before the unknown of the row before, `b'`
before its own, and its right side `r'`. The row before is taken out of it, which leaves
`b' - a' / b` before its own unknown and `r' - (a' / b) r` on its right. -/
def solve (b : Rat) (r : Vec) : List (Rat × Rat × Vec) → List Vec
  | [] => [Vec.scale (1 / b) r]
  | (a', b', r') :: rest => back b r (solve (b' - a' / b) (r' - Vec.scale (a' / b) r) rest)

/-- **The rows of the system after the first**, for the points from the second on: a row
between two others for each point with two after it, and the last row for the last two. -/
def rows : List Vec → List (Rat × Rat × Vec)
  | [] => []
  | [_] => []
  | [k, kn] => [(2, 7, Vec.scale 8 k + kn)]
  | k :: k' :: k'' :: rest => (1, 4, Vec.scale 4 k + Vec.scale 2 k') :: rows (k' :: k'' :: rest)

/-- **The first control point of each piece** of the natural spline through the points. -/
def firsts : List Vec → List Vec
  | k0 :: k1 :: rest => solve 2 (k0 + Vec.scale 2 k1) (rows (k1 :: rest))
  | _ => []

/-- **The pieces through the points**, given the first control point of each. The second
control point of a piece mirrors the first control point of the next in the point between them;
that of the last piece is half way between its first control point and its end. -/
def pieces : List Vec → List Vec → List Cubic
  | [k0, k1], [p] => [⟨k0, p, Vec.scale (1 / 2) (k1 + p), k1⟩]
  | k0 :: k1 :: k2 :: ks, p :: q :: ps =>
    ⟨k0, p, Vec.scale 2 k1 - q, k1⟩ :: pieces (k1 :: k2 :: ks) (q :: ps)
  | _, _ => []

end Natural

namespace Curve

/-- **The natural cubic spline through the points**: d3's `curveNatural`. One cubic joins each
point to the next, and two points give a straight segment. The curve has one velocity at every
point and bends the same way on both sides of it, and it does not bend at its two ends
(`Whatwg/Svg/Geometry/Natural/Laws.lean`). -/
def natural (points : List Vec) : List Cubic :=
  match points with
  | [a, b] => [Cubic.line a b]
  | _ => Natural.pieces points (Natural.firsts points)

end Curve

end Whatwg.Svg.Value
