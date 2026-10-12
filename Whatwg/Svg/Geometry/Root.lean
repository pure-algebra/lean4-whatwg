import Whatwg.Svg.Geometry.Cubic.Laws

/-!
# Whatwg.Svg.Geometry.Root

Owner: a square root to a stated number of places, and what needs one: a length, a distance, a
vector of length one and the normal of a segment (slice S11 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-56). A program needs these to draw beside a line: the outline of a stroke, the head
of an arrow, a label that stands off an edge.

The square root of a rational number is seldom rational, so this module does not have it. It
has `sqrtDown`: the greatest number of a given count of places whose square is no more than
its argument. It is computed by `Nat.sqrt` of Lean's core library on a scaled integer, and the
two bounds that core proves for `Nat.sqrt` are the two bounds of the result
(`sqrtDown_mul_self_le`, `lt_sqrtDown_succ`): the root lies between `sqrtDown q n` and one
unit of the last place above it. On the square of a number of that many places it is exact
(`sqrtDown_sq`).

Everything else is stated through it, with the same count of places: `Vec.norm`, `Vec.dist`,
`Vec.unit`, `Vec.normal`, and for a segment `Cubic.normalAt` and `Cubic.offsetAt`. A length is
rounded down, so a unit vector is no shorter than one (`Vec.one_le_normSq_unit`), and longer
by less than the part that one unit of the last place is of its rounded length
(`Vec.normSq_unit_lt`). That part is small for a vector that is long against one unit of the
last place, and not for a short one: at three places a vector `0.00199` long has a unit vector
`1.99` long. A vector whose length rounds down to zero has the unit vector zero, so a segment
whose four points are one point has the normal zero, and a point beside it is the point
itself. Ask for more places where the lengths are small.

A distance reads a difference of two points and a normal reads a direction, so each is the
same for a moved figure (`Vec.dist_move`, `Cubic.normalAt_move`, `Cubic.offsetAt_move`).

What this module does not claim: an angle, a sine or a cosine; the length of a curve, which
is a limit; an offset curve as cubics.
-/

namespace Whatwg.Svg.Value

/-- The greatest number with at most `places` places whose square is no more than `q`, and
zero for a `q` below zero: the square root of `q`, rounded down. -/
def sqrtDown (q : Rat) (places : Nat := 3) : Rat :=
  ((Nat.sqrt (q * (100 : Rat) ^ places).floor.toNat : Nat) : Rat) / (10 : Rat) ^ places

namespace Vec

/-- The length, rounded down at `places` places. -/
def norm (v : Vec) (places : Nat := 3) : Rat := sqrtDown v.normSq places

/-- The distance between two points, rounded down at `places` places. -/
def dist (a b : Vec) (places : Nat := 3) : Rat := (b - a).norm places

/-- The vector along `v` of length one, nearly: `v` divided by its length as `norm` gives it.
Zero for a vector whose length rounds down to zero. -/
def unit (v : Vec) (places : Nat := 3) : Vec :=
  if v.norm places = 0 then zero else scale (1 / v.norm places) v

/-- The vector of length one, nearly, a quarter turn on from `v`: to the right of the direction
`v` on a screen, where `y` grows downwards. -/
def normal (v : Vec) (places : Nat := 3) : Vec := v.perp.unit places

end Vec

namespace Cubic

/-- The normal of the segment at the parameter `t`: of length one, nearly, a quarter turn on
from its direction, so to the right of the direction of travel on a screen. -/
def normalAt (c : Cubic) (t : Rat) (places : Nat := 3) : Vec := (c.direction t).normal places

/-- The point of the segment at `t`, moved by `distance` along its normal: a point of the
line that runs beside the segment. -/
def offsetAt (c : Cubic) (t distance : Rat) (places : Nat := 3) : Vec :=
  c.pointAt t + Vec.scale distance (c.normalAt t places)

/-- The length of the segment through `n` chords, each rounded down: no more than the length
of the segment. Each chord can be short by one unit of the last place, so the sum can be
short by `n` of them: ask for more places with more chords. -/
def chordLength (c : Cubic) (n : Nat) (places : Nat := 3) : Rat :=
  ((c.samples n).zip (c.samples n).tail).foldl (fun total pair => total + pair.1.dist pair.2 places) 0

end Cubic

end Whatwg.Svg.Value
