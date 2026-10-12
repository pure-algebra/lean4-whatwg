import Whatwg.Svg.Geometry.Pen

/-!
# Whatwg.Svg.Geometry.Shape

Owner: curves through a list of points, and the three shapes built on them (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-45). The algorithms are those of d3-shape
(https://github.com/d3/d3-shape, ISC licence, Copyright 2010-2022 Mike Bostock), read from its
source under `src/curve/`: each form here draws the outline that the d3 curve of that name
draws for the same points. The commands can differ where the outline does not: a step here is
an `H` and a `V` through each point of the data, where d3 writes a straight segment to each
corner.

| `Curve` | d3-shape | Between the points |
| --- | --- | --- |
| `linear` | `curveLinear` | straight segments |
| `stepX` | `curveStep` | across to the middle `x`, to the `y`, across |
| `stepY` | `curveStep`, axes exchanged | to the middle `y`, across, to the `y` |
| `stepBefore` | `curveStepBefore` | to the `y`, then across |
| `stepAfter` | `curveStepAfter` | across, then to the `y` |
| `bumpX` | `curveBumpX` | one cubic, its controls at the middle `x` |
| `bumpY` | `curveBumpY` | one cubic, its controls at the middle `y` |
| `cardinal t n` | `curveCardinal.tension(t)` | cubics through every point, each control a sixth of `1 - t` along the chord of its neighbours |
| `basis n` | `curveBasis` | a uniform cubic B-spline: it starts and ends at the first and the last point and passes near the others |

`Curve.catmullRom n` is `cardinal 0 n`: the uniform Catmull-Rom spline, d3's
`curveCatmullRom.alpha(0)`.

**Exact and rounded.** The first seven forms need a sum and a half, so every coordinate they
write is exact. A cardinal spline divides by six and a basis spline by three and by six, which
no value of this package does exactly, so those two take a number of places `n`, and each
control point is rounded to it by `Decimal.divRound`. d3 computes in binary floating point
and rounds the path it writes; here the rounding is one stated step. The points that the data
gives are never rounded: a cardinal spline passes through each of them as written, and both
splines end at the last point exactly. That is why the laws of
`Whatwg/Svg/Geometry/Shape/Laws.lean` hold for every form with no error term.

`Shape.line` is the path through a list of points, `Shape.area` the closed region between two
lines, and `Shape.link` the curve between two points.

What this module does not claim: d3's `curveCatmullRom` with a positive `alpha`, which takes
a root of a distance; `curveMonotoneX` and `curveNatural`, which divide by differences of the
data and need rational arithmetic that is not here yet; the closed and open variants; and d3's
single-point behaviour, a closed subpath of no length, where this module writes nothing.
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
  /-- One cubic between two points, with its controls at the middle `x`. -/
  | bumpX
  /-- One cubic between two points, with its controls at the middle `y`. -/
  | bumpY
  /-- A cardinal spline with a tension, its control points rounded to a number of places. -/
  | cardinal (tension : Decimal) (places : Nat)
  /-- A uniform cubic B-spline, its points rounded to a number of places. -/
  | basis (places : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Curve

/-- The uniform Catmull-Rom spline: the cardinal spline of tension zero. -/
def catmullRom (places : Nat := 3) : Curve := .cardinal 0 places

/-! ## The forms that join two points -/

/-- The commands that join `a` to `b` in one of the seven exact forms, each absolute. A spline
between two points alone is a straight segment. -/
def pair : Curve → Point → Point → List Command
  | .stepX, a, b =>
    [.horizontalLineto false (Decimal.mid a.x b.x) [], .verticalLineto false b.y [],
      .horizontalLineto false b.x []]
  | .stepY, a, b =>
    [.verticalLineto false (Decimal.mid a.y b.y) [], .horizontalLineto false b.x [],
      .verticalLineto false b.y []]
  | .stepBefore, _, b => [.verticalLineto false b.y [], .horizontalLineto false b.x []]
  | .stepAfter, _, b => [.horizontalLineto false b.x [], .verticalLineto false b.y []]
  | .bumpX, a, b =>
    [.curveto false (⟨(Decimal.mid a.x b.x), a.y⟩, ⟨(Decimal.mid a.x b.x), b.y⟩, b) []]
  | .bumpY, a, b =>
    [.curveto false (⟨a.x, (Decimal.mid a.y b.y)⟩, ⟨b.x, (Decimal.mid a.y b.y)⟩, b) []]
  | _, _, b => [.lineto false b []]

/-- The commands from `a` through each point of a list, each pair joined on its own. -/
def pairwise (c : Curve) : Point → List Point → List Command
  | _, [] => []
  | a, b :: rest => c.pair a b ++ c.pairwise b rest

/-! ## The cardinal spline -/

/-- One segment of a cardinal spline, from `a` to `b`: a cubic whose first control is `a` moved
along the chord from the point before `a` to `b`, and whose second is `b` moved along the chord
from the point after `b` to `a`. Where a neighbour is missing, at an end of the line, the
control is the end itself. `along` is the scaling by a sixth of one less the tension. -/
def cardinalSegment (along : Point → Point) (before : Option Point) (a b : Point)
    (after : Option Point) : Command :=
  .curveto false
    (match before with
      | none => a
      | some z => a + along (b - z),
     match after with
      | none => b
      | some c => b + along (a - c),
     b) []

/-- The segments of a cardinal spline from `a` through a list of points, `before` being the
point before `a`. -/
def cardinalFrom (along : Point → Point) (before : Option Point) (a : Point) :
    List Point → List Command
  | [] => []
  | [b] => [cardinalSegment along before a b none]
  | b :: c :: rest =>
    cardinalSegment along before a b (some c) :: cardinalFrom along (some a) b (c :: rest)

/-- The scaling of a cardinal spline: a sixth of one less the tension, rounded. -/
def cardinalAlong (tension : Decimal) (places : Nat) (v : Point) : Point :=
  ⟨((1 - tension) * v.x).divRound 6 places, ((1 - tension) * v.y).divRound 6 places⟩

/-! ## The basis spline -/

/-- A point divided by an integer, each coordinate rounded. -/
def over (places : Nat) (den : Int) (p : Point) : Point :=
  ⟨p.x.divRound den places, p.y.divRound den places⟩

/-- One segment of a basis spline for three consecutive points: its controls at a third and at
two thirds from the first to the second, and its end at a sixth of the first, four of the
second and the third. -/
def basisSegment (places : Nat) (p q r : Point) : Command :=
  .curveto false
    (over places 3 (Point.scale 2 p + q), over places 3 (p + Point.scale 2 q),
      over places 6 (p + Point.scale 4 q + r)) []

/-- The segments of a basis spline whose last two points are `p` and `q`, through a list of
further points, and then a straight segment to the last point. -/
def basisFrom (places : Nat) (p q : Point) : List Point → List Command
  | [] => [basisSegment places p q q, .lineto false q []]
  | r :: rest => basisSegment places p q r :: basisFrom places q r rest

/-- The commands of a basis spline from `a` through a list of points: a straight segment to a
sixth of the way to the next point, the segments, and a straight segment to the last point. -/
def basisThrough (places : Nat) (a : Point) : List Point → List Command
  | [] => []
  | [b] => [.lineto false b []]
  | b :: c :: rest =>
    .lineto false (over places 6 (Point.scale 5 a + b)) [] :: basisFrom places a b (c :: rest)

/-! ## Every form -/

/-- The commands from `a` through each point of a list, in order. -/
def through (c : Curve) (a : Point) (points : List Point) : List Command :=
  match c with
  | .cardinal tension places =>
    match points with
    | [] => []
    | [b] => [.lineto false b []]
    | b :: d :: rest => cardinalFrom (cardinalAlong tension places) none a (b :: d :: rest)
  | .basis places => basisThrough places a points
  | c => c.pairwise a points

/-- The commands that join `a` to `b`. -/
def join (c : Curve) (a b : Point) : List Command := c.through a [b]

/-- The form that draws the same steps when the points are taken in reverse: `stepBefore` and
`stepAfter` change places, and every other form is its own. d3 makes this exchange for the
second line of an area. -/
def flip : Curve → Curve
  | .stepBefore => .stepAfter
  | .stepAfter => .stepBefore
  | c => c

/-- The way back along a list of points: a straight segment to the first, and then through
the others. -/
def back (c : Curve) : List Point → List Command
  | [] => []
  | q :: rest => Command.lineto false q [] :: c.through q rest

/-- The last of a point and the points after it. -/
def last : Point → List Point → Point
  | a, [] => a
  | _, b :: rest => last b rest

end Curve

/-- Draw from the pen's current point through each point of a list. -/
def Pen.through (pen : Pen) (c : Curve) (points : List Point) : Pen :=
  pen.pushAll (c.through pen.current points)

namespace Shape

/-- The path through a list of points, and the empty path for no point. -/
def line (c : Curve) : List Point → Path
  | [] => .empty
  | p :: rest => .moveto false p [] (c.through p rest)

/-- The curve from one point to another. -/
def link (c : Curve) (a b : Point) : Path := .moveto false a [] (c.join a b)

/-- The closed region between two lines: along `top` in order, straight to the last point of
`base`, back along `base` in the flipped form, and closed. -/
def area (c : Curve) : List Point → List Point → Path
  | [], _ => .empty
  | p :: rest, base =>
    .moveto false p [] (c.through p rest ++ c.flip.back base.reverse ++ [.closepath false])

/-- A cubic from `a` to `b` that leaves and arrives along `x`: each control is `reach` of the
way across from its end. A reach of `0.5` is `bumpX`, and of `0` a straight segment. -/
def bumpX (reach : Decimal) (a b : Point) : Path :=
  .moveto false a []
    [.curveto false
      (⟨(a.x + reach * (b.x - a.x)).trim, a.y⟩, ⟨(b.x - reach * (b.x - a.x)).trim, b.y⟩, b) []]

/-- A cubic from `a` to `b` that leaves and arrives along `y`: each control is `reach` of the
way down from its end. A reach of `0.5` is `bumpY`, and of `0` a straight segment. -/
def bumpY (reach : Decimal) (a b : Point) : Path :=
  .moveto false a []
    [.curveto false
      (⟨a.x, (a.y + reach * (b.y - a.y)).trim⟩, ⟨b.x, (b.y - reach * (b.y - a.y)).trim⟩, b) []]

end Shape

end Whatwg.Svg.Value
