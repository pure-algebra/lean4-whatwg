import Whatwg.Svg.Geometry.Write

/-!
# Whatwg.Svg.Geometry.Shape

Owner: curves through a list of points (slice S10 of `docs/SVG-PACKAGE-PLAN.md`, on exact
geometry since slice S11; rulings SV-45 and SV-54). The algorithms are those of d3-shape
(https://github.com/d3/d3-shape, ISC licence, Copyright 2010-2022 Mike Bostock), read from its
source under `src/curve/`: each form here draws the outline that the d3 curve of that name
draws for the same points, with the one exception below the table. A review ran d3's ten
curve files beside this module on 1176 cases and found no other difference in an outline.

| `Curve` | d3-shape | Between the points |
| --- | --- | --- |
| `linear` | `curveLinear` | straight segments |
| `stepX` | `curveStep` | across to the middle `x`, to the `y`, across |
| `stepY` | `curveStep`, axes exchanged | to the middle `y`, across, to the `y` |
| `stepBefore` | `curveStepBefore` | to the `y`, then across |
| `stepAfter` | `curveStepAfter` | across, then to the `y` |
| `bumpX r` | `curveBumpX` at `r = 1/2` | one cubic that leaves and arrives along `x`, each control `r` of the way across from its end |
| `bumpY r` | `curveBumpY` at `r = 1/2` | the same along `y` |
| `cardinal t` | `curveCardinal.tension(t)` | cubics through every point, each control a sixth of `1 - t` along the chord of its neighbours |
| `basis` | `curveBasis` | a uniform cubic B-spline: it starts and ends at the first and the last point and passes near the others |

`Curve.catmullRom` is `cardinal 0`: the uniform Catmull-Rom spline, d3's
`curveCatmullRom.alpha(0)`, and not d3's default, whose `alpha` is a half.

The exception: `stepX` and `stepY` pass through every point. d3's `curveStep` runs from one
middle to the next, which is the same outline where the coordinate runs one way, and cuts the
corner at a point where it turns back.

**One result, three ways to treat the ends.** A curve is a list of cubic segments
(`Whatwg/Svg/Geometry/Cubic.lean`), computed exactly in `Rat`: the sixths and the thirds of a
spline are numbers here and are not rounded. d3 has three curves for each form, and so has
this module:

- `Curve.cubics` runs from the first point to the last (`curveCardinal`, `curveBasis`);
- `Curve.cubicsOpen` reads the first and the last point as guides only and runs between the
  second and the last but one (`curveCardinalOpen`, `curveBasisOpen`);
- `Curve.cubicsClosed` runs through the points and back to the first (`curveCardinalClosed`,
  `curveBasisClosed`, `curveLinearClosed`).

**How a spline is built.** A spline is one rule for four consecutive points
(`cardinalSegment`, `basisSegment`), applied to every four in a row (`windows`). The three
ways differ only in what stands beyond the ends of the list: for `cubics` the neighbour of
each end again, which makes the tangent at an end zero as d3's is (`reflected`), or each end
twice for a basis spline (`doubled`); for `cubicsOpen` nothing; for `cubicsClosed` the points
of the other end (`wrapped`). A program with ends of its own applies `windows` to its own
list: the Catmull-Rom spline with each end repeated is
`windows (cardinalSegment (1 / 6)) (doubled points)`.

The seven forms that join two points with no regard to their neighbours are `pair`, applied to
every two in a row (`pairs`).

`Shape.line`, `Shape.link`, `Shape.loop` and `Shape.area` are the paths of these lists, each
coordinate written once at a number of places (`Whatwg/Svg/Geometry/Write.lean`).

The laws are in `Whatwg/Svg/Geometry/Shape/Laws.lean`: every form is a chain from the first
point to the last; a cardinal spline passes through every point; a closed form ends where it
starts; a curve through moved points is the curve, moved.

What this module does not claim: d3's `curveCatmullRom` with a positive `alpha`, which takes
a root of a distance; `curveMonotoneX` and `curveNatural`; and the dot that d3 writes for an
open curve of one point, or of three for its open splines, a closed subpath of no length,
where this module writes nothing. A closed curve of one point is such a dot here as in d3.
-/

namespace Whatwg.Svg.Value

/-- The form of a curve through a list of points. -/
inductive Curve where
  /-- Straight segments. -/
  | linear
  /-- Across to the middle `x`, then to the `y`, then across. -/
  | stepX
  /-- To the middle `y`, then across, then to the `y`. -/
  | stepY
  /-- To the `y`, then across. -/
  | stepBefore
  /-- Across, then to the `y`. -/
  | stepAfter
  /-- One cubic between two points that leaves and arrives along `x`: each control is `reach`
  of the way across from its end. A half is d3's bump, and zero a straight segment. -/
  | bumpX (reach : Rat := 1 / 2)
  /-- One cubic between two points that leaves and arrives along `y`. -/
  | bumpY (reach : Rat := 1 / 2)
  /-- A cardinal spline with a tension: zero is the Catmull-Rom spline, and one is straight
  segments. -/
  | cardinal (tension : Rat := 0)
  /-- A uniform cubic B-spline. -/
  | basis
  deriving DecidableEq, Repr, Inhabited

namespace Curve

/-- The uniform Catmull-Rom spline: the cardinal spline of tension zero. -/
def catmullRom : Curve := .cardinal 0

/-! ## The forms that join two points -/

/-- The segments that join `a` to `b` with no regard to their neighbours. A spline between two
points alone is a straight segment. -/
def pair : Curve → Vec → Vec → List Cubic
  | .stepX, a, b =>
    [.line a ⟨(a.x + b.x) / 2, a.y⟩, .line ⟨(a.x + b.x) / 2, a.y⟩ ⟨(a.x + b.x) / 2, b.y⟩,
      .line ⟨(a.x + b.x) / 2, b.y⟩ b]
  | .stepY, a, b =>
    [.line a ⟨a.x, (a.y + b.y) / 2⟩, .line ⟨a.x, (a.y + b.y) / 2⟩ ⟨b.x, (a.y + b.y) / 2⟩,
      .line ⟨b.x, (a.y + b.y) / 2⟩ b]
  | .stepBefore, a, b => [.line a ⟨a.x, b.y⟩, .line ⟨a.x, b.y⟩ b]
  | .stepAfter, a, b => [.line a ⟨b.x, a.y⟩, .line ⟨b.x, a.y⟩ b]
  | .bumpX r, a, b => [⟨a, ⟨a.x + r * (b.x - a.x), a.y⟩, ⟨b.x - r * (b.x - a.x), b.y⟩, b⟩]
  | .bumpY r, a, b => [⟨a, ⟨a.x, a.y + r * (b.y - a.y)⟩, ⟨b.x, b.y - r * (b.y - a.y)⟩, b⟩]
  | _, a, b => [.line a b]

/-- The segments through the points of a list, every two in a row joined on their own. -/
def pairs (c : Curve) : List Vec → List Cubic
  | a :: b :: rest => c.pair a b ++ pairs c (b :: rest)
  | _ => []

/-! ## The splines -/

/-- One segment for every four points in a row. -/
def windows (segment : Vec → Vec → Vec → Vec → Cubic) : List Vec → List Cubic
  | p0 :: p1 :: p2 :: p3 :: rest => segment p0 p1 p2 p3 :: windows segment (p1 :: p2 :: p3 :: rest)
  | _ => []

/-- The segment of a cardinal spline for four points in a row, from the second to the third:
it leaves along the chord of its neighbours, from the first to the third, and arrives along
the chord from the second to the fourth, each control `k` of the chord from its end. d3's `k`
is a sixth of one less the tension. -/
def cardinalSegment (k : Rat) (p0 p1 p2 p3 : Vec) : Cubic :=
  ⟨p1, p1 + Vec.scale k (p2 - p0), p2 - Vec.scale k (p3 - p1), p2⟩

/-- The segment of a uniform cubic B-spline for four points in a row: it runs near the second
and the third, from a sixth of the first, four of the second and the third, to a sixth of the
second, four of the third and the fourth. -/
def basisSegment (p0 p1 p2 p3 : Vec) : Cubic :=
  ⟨Vec.scale (1 / 6) (p0 + Vec.scale 4 p1 + p2), Vec.scale (1 / 3) (Vec.scale 2 p1 + p2),
    Vec.scale (1 / 3) (p1 + Vec.scale 2 p2), Vec.scale (1 / 6) (p1 + Vec.scale 4 p2 + p3)⟩

/-- The scaling of a cardinal spline: a sixth of one less the tension. -/
def cardinalScale (tension : Rat) : Rat := (1 - tension) / 6

/-! ## What stands beyond the ends -/

/-- The list with the neighbour of each end beyond it: the second point before the first, and
the last but one after the last. Nothing for fewer than two points. -/
def reflected (points : List Vec) : List Vec :=
  match points.tail.head?, points.dropLast.getLast? with
  | some second, some lastButOne => second :: points ++ [lastButOne]
  | _, _ => []

/-- The list with each end twice. Nothing for no point. -/
def doubled (points : List Vec) : List Vec :=
  match points.head?, points.getLast? with
  | some first, some last => first :: points ++ [last]
  | _, _ => []

/-- The list as a ring: the last point before the first, and the first two after the last.
Nothing for no point. -/
def wrapped (points : List Vec) : List Vec :=
  match points, points.getLast? with
  | first :: rest, some last => last :: points ++ [first, rest.head?.getD first]
  | _, _ => []

/-! ## Every form -/

/-- **The curve through a list of points**, from the first to the last: nothing for fewer than
two points. -/
def cubics (c : Curve) (points : List Vec) : List Cubic :=
  match c with
  | .cardinal tension => windows (cardinalSegment (cardinalScale tension)) (reflected points)
  | .basis =>
    match points with
    | [a, b] => [.line a b]
    | _ =>
      match points.head?, points.getLast?, (windows basisSegment (doubled points)).head?,
        (windows basisSegment (doubled points)).getLast? with
      | some first, some last, some w0, some wn =>
        .line first w0.p0 :: windows basisSegment (doubled points) ++ [.line wn.p3 last]
      | _, _, _, _ => []
  | c => c.pairs points

/-- **The open curve**: the first and the last point guide it. A cardinal spline, and a form
that joins two points, runs from the second point to the last but one; a basis spline runs
near them. -/
def cubicsOpen (c : Curve) (points : List Vec) : List Cubic :=
  match c with
  | .cardinal tension => windows (cardinalSegment (cardinalScale tension)) points
  | .basis => windows basisSegment points
  | c => c.pairs points.tail.dropLast

/-- **The closed curve**: through the points and back to the first; a basis spline runs near
them, round the ring. -/
def cubicsClosed (c : Curve) (points : List Vec) : List Cubic :=
  match c with
  | .cardinal tension => windows (cardinalSegment (cardinalScale tension)) (wrapped points)
  | .basis => windows basisSegment (wrapped points)
  | c =>
    match points with
    | [] => []
    | first :: rest => c.pairs (first :: rest ++ [first])

/-- The form that draws the same steps when the points are taken in reverse: `stepBefore` and
`stepAfter` change places, and every other form is its own. d3 makes this exchange for the
second line of an area. -/
def flip : Curve → Curve
  | .stepBefore => .stepAfter
  | .stepAfter => .stepBefore
  | c => c

/-- **The outline of the region between two lines**: along `top`, straight to the last point
of `base`, and back along `base` in the flipped form. A closepath joins its end to its
start. -/
def areaCubics (c : Curve) (top base : List Vec) : List Cubic :=
  c.cubics top ++
    (match top.getLast?, base.getLast? with
      | some t, some b => [Cubic.line t b]
      | _, _ => []) ++
    c.flip.cubics base.reverse

end Curve

/-- A curve through a list of points, drawn by the pen. Its first point starts a subpath
where the pen is not there already. -/
def Pen.curve (pen : Pen) (c : Curve) (points : List Vec) (places : Nat := 3) : Pen :=
  pen.cubics (c.cubics points) places

namespace Shape

/-- The path through a list of points: the empty path for fewer than two. -/
def line (c : Curve) (points : List Vec) (places : Nat := 3) : Path :=
  .ofCubics (c.cubics points) places

/-- The curve from one point to another. -/
def link (c : Curve) (a b : Vec) (places : Nat := 3) : Path := line c [a, b] places

/-- The closed curve through a list of points. -/
def loop (c : Curve) (points : List Vec) (places : Nat := 3) : Path :=
  .ofLoop (c.cubicsClosed points) places

/-- The closed region between two lines: along `top` in order, straight to the last point of
`base`, back along `base` in the flipped form, and closed. -/
def area (c : Curve) (top base : List Vec) (places : Nat := 3) : Path :=
  .ofLoop (c.areaCubics top base) places

end Shape

end Whatwg.Svg.Value
