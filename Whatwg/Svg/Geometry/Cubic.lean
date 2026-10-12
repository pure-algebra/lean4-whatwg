import Whatwg.Svg.Geometry.Vec

/-!
# Whatwg.Svg.Geometry.Cubic

Owner: one cubic Bézier segment as a thing to compute with (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-51). The path chapter of SVG 2 draws with four kinds of
segment, and three of them are this one: a straight segment and a quadratic Bézier segment are
each a cubic exactly (`line`, `ofQuad`). The fourth, the elliptical arc, is no cubic.

A segment is its four points: the start, the two control points and the end. A program that
lays out a picture keeps its edges and its outlines as lists of these, and asks of one:

- the point at a parameter (`pointAt`);
- the part between two parameters, which is a cubic again (`between`, and `upTo`, `after` and
  `split` for the two parts at one parameter);
- the segment run backwards (`reverse`), moved (`move`), scaled (`scale`) or under any map of
  the plane (`map`);
- how it leaves a point (`velocity`, `direction`);
- whether it draws a straight segment (`isStraight`).

**The meaning function.** All of these come from one function, the blossom of the cubic
(`blossom`): de Casteljau's three rounds of steps between neighbours, with a parameter of its
own for each round. The point at `t` is the blossom at `t, t, t`, and the control points of the
part between `a` and `b` are the blossoms at `a, a, a`, at `a, a, b`, at `a, b, b` and at
`b, b, b`. The laws of `Whatwg/Svg/Geometry/Cubic/Laws.lean` are stated against `pointAt`, and
each is an equation between two polynomials, which core's `grind` proves.

A list of segments is a chain when each starts where the one before ends (`Chained`).

`corner` is the cubic that rounds a corner: with `kappa` its distance from the centre is
within three parts in ten thousand of the radius of a quarter circle (the square of that
distance is checked at five parameters by `corner_near_circle` of
`Whatwg/Svg/Geometry/Outline/Laws.lean`).

What this module does not claim: a length, a normal or a tangent of unit length, which take a
square root; the tight bounding box, which takes the roots of the derivative
(`Whatwg/Svg/Geometry/Box.lean` has the box of the control points, which holds the segment);
that `velocity` is the derivative in the sense of analysis, which is a statement about real
numbers and not about `Rat`.
-/

namespace Whatwg.Svg.Value

/-- A cubic Bézier segment: its start, its two control points and its end. -/
structure Cubic where
  p0 : Vec
  p1 : Vec
  p2 : Vec
  p3 : Vec
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace Cubic

/-! ## Making one -/

/-- The straight segment from `a` to `b`, with its control points at a third and at two
thirds, so that the point at `t` is `t` of the way along. -/
def line (a b : Vec) : Cubic := ⟨a, a.lerp b (1 / 3), a.lerp b (2 / 3), b⟩

/-- The quadratic Bézier segment from `a` to `b` with the control point `c`, as a cubic: each
control point is two thirds of the way from its end to `c`. -/
def ofQuad (a c b : Vec) : Cubic := ⟨a, a.lerp c (2 / 3), b.lerp c (2 / 3), b⟩

/-- The share of a corner that makes a quarter circle, to four places: `4 (√2 - 1) / 3`. -/
def kappa : Rat := 0.5523

/-- The segment from `a` to `b` that leaves towards the corner `c` and arrives from it: each
control point is `k` of the way from its end to the corner. With `a`, `c` and `b` three corners
of a square it is a quarter circle to within three parts in ten thousand. -/
def corner (a c b : Vec) (k : Rat := kappa) : Cubic := ⟨a, a.lerp c k, b.lerp c k, b⟩

/-! ## Under a map of the plane -/

/-- Each of the four points under a map. For a map that keeps the steps between points (a
move, a scaling, any affine map) this is the segment under the map (`map_pointAt` of the
laws). -/
def map (f : Vec → Vec) (c : Cubic) : Cubic := ⟨f c.p0, f c.p1, f c.p2, f c.p3⟩

/-- The segment moved by `d`. -/
def move (d : Vec) (c : Cubic) : Cubic := c.map (· + d)

/-- The segment scaled by `k` about the origin. -/
def scale (k : Rat) (c : Cubic) : Cubic := c.map (Vec.scale k)

/-- The segment run from its end to its start. -/
def reverse (c : Cubic) : Cubic := ⟨c.p3, c.p2, c.p1, c.p0⟩

/-! ## The blossom -/

/-- The blossom of the cubic: de Casteljau's three rounds of steps between neighbours, the
first at `r`, the second at `s` and the third at `t`. It is the same for every order of the
three (`blossom_comm` of the laws). -/
def blossom (c : Cubic) (r s t : Rat) : Vec :=
  ((c.p0.lerp c.p1 r).lerp (c.p1.lerp c.p2 r) s).lerp
    ((c.p1.lerp c.p2 r).lerp (c.p2.lerp c.p3 r) s) t

/-- The point of the segment at the parameter `t`: the start at `0` and the end at `1`. -/
def pointAt (c : Cubic) (t : Rat) : Vec := c.blossom t t t

/-- The part of the segment from the parameter `a` to the parameter `b`, as a cubic of its
own: its point at `s` is the point of the whole at `a + s (b - a)`. With `b` before `a` it runs
backwards. -/
def between (c : Cubic) (a b : Rat) : Cubic :=
  ⟨c.blossom a a a, c.blossom a a b, c.blossom a b b, c.blossom b b b⟩

/-- The part from the start to the parameter `t` (de Casteljau's split). -/
def upTo (c : Cubic) (t : Rat) : Cubic :=
  ⟨c.p0, c.p0.lerp c.p1 t, (c.p0.lerp c.p1 t).lerp (c.p1.lerp c.p2 t) t, c.pointAt t⟩

/-- The part from the parameter `t` to the end. -/
def after (c : Cubic) (t : Rat) : Cubic :=
  ⟨c.pointAt t, (c.p1.lerp c.p2 t).lerp (c.p2.lerp c.p3 t) t, c.p2.lerp c.p3 t, c.p3⟩

/-- The two parts at the parameter `t`. -/
def split (c : Cubic) (t : Rat) : Cubic × Cubic := (c.upTo t, c.after t)

/-- The points at `n + 1` parameters, evenly from `0` to `1`; the start alone for `n = 0`. -/
def samples (c : Cubic) (n : Nat) : List Vec :=
  (List.range (n + 1)).map fun (k : Nat) => c.pointAt ((k : Rat) / (n : Rat))

/-! ## How it moves -/

/-- The velocity at the parameter `t`: three times the quadratic Bézier of the three
differences of neighbouring points. At `0` it points from the start to the first control
point, and at `1` from the second control point to the end. -/
def velocity (c : Cubic) (t : Rat) : Vec :=
  Vec.scale 3 (((c.p1 - c.p0).lerp (c.p2 - c.p1) t).lerp ((c.p2 - c.p1).lerp (c.p3 - c.p2) t) t)

/-- A direction at the parameter `t`: the velocity, and where that is zero, the direction in
which the segment leaves the point. At the start of a segment whose first control point is its
start that is towards the second control point, and at the end of a segment whose second
control point is its end it is from the first control point: the tangents of d3's cardinal
curve at its two ends. Anywhere else, and where those are zero too, it is the chord. -/
def direction (c : Cubic) (t : Rat) : Vec :=
  if c.velocity t = Vec.zero then
    if t = 0 ∧ c.p2 - c.p0 ≠ Vec.zero then c.p2 - c.p0
    else if t = 1 ∧ c.p3 - c.p1 ≠ Vec.zero then c.p3 - c.p1
    else c.p3 - c.p0
  else c.velocity t

/-! ## Straight segments -/

/-- The point `p` is on the closed straight segment from `a` to `b`. -/
def onChord (a b p : Vec) : Bool :=
  if a = b then p = a
  else
    (b - a).cross (p - a) = 0 && 0 ≤ (b - a).dot (p - a) && (b - a).dot (p - a) ≤ (b - a).normSq

/-- Both control points are on the chord: the segment draws the straight segment from its
start to its end, and nothing else. -/
def isStraight (c : Cubic) : Bool := onChord c.p0 c.p3 c.p1 && onChord c.p0 c.p3 c.p2

/-! ## Measures and chains -/

/-- The length of the control polygon along the axes: a measure of the segment that needs no
root, and is no less than the distance from its start to its end along the axes. -/
def taxi (c : Cubic) : Rat := c.p0.taxi c.p1 + c.p1.taxi c.p2 + c.p2.taxi c.p3

/-- Each segment of the list starts where the one before it ends. -/
def Chained : List Cubic → Bool
  | a :: b :: rest => a.p3 = b.p0 && Chained (b :: rest)
  | _ => true

/-- The list is a chain that ends where it starts: a closed outline. -/
def Closed : List Cubic → Bool
  | [] => true
  | c :: rest => Chained (c :: rest) && ((c :: rest).getLast?.map (·.p3) == some c.p0)

/-- The segments in reverse, each run backwards: the same outline drawn the other way. -/
def reverseAll (cs : List Cubic) : List Cubic := cs.reverse.map reverse

end Cubic

end Whatwg.Svg.Value
