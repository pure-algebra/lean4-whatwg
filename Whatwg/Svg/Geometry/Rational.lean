import Whatwg.Svg.Geometry.Arith.Same
import Whatwg.Svg.Geometry.Order
import Whatwg.Svg.Geometry.Vec

/-!
# Whatwg.Svg.Geometry.Rational

Owner: the number that a typed value denotes, and the typed value that writes a number (slice
S11 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-50). This is the one place where the two kinds of
number of the package meet:

- a `Decimal` is a spelling, `mantissa × 10 ^ exponent`, and it is what an attribute holds;
- a `Rat` is a number, and it is what the geometry computes with.

`Decimal.toRat` is the number of a spelling, exactly. It is the meaning that the arithmetic
and the order of `Whatwg/Svg/Geometry/Arith.lean` and `Order.lean` are about: the laws of
`Whatwg/Svg/Geometry/Rational/Laws.lean` say that it takes `+`, `-` and `*` to the operations
of `Rat`, that two values are `Same` exactly when their numbers are equal, and that `≤` is the
order of the numbers. So a fact about decimals is a fact about rational numbers, which core
proves.

`Decimal.ofRat` writes a number: the nearest decimal with at most a given number of places, a
half going up, with no zero at the end of its fraction. `ofRatDown` and `ofRatUp` round to the
decimal below and above, for a box that must still hold what it held. These three are the only
roundings of a number that is written; the one other rounding of the geometry is the square
root of `Whatwg/Svg/Geometry/Root.lean`. A number that has no more than that many places is
written exactly (`ofRat_div_pow`), so a program that counts in thousandths and writes three
places loses nothing.

`Point.toVec` and `Vec.round` are the same two for a point.

What this module does not claim: a spelling for a number that keeps every digit of a fraction
with no end, such as a third.
-/

namespace Whatwg.Svg.Value

namespace Decimal

/-- The number that the value denotes: `mantissa × 10 ^ exponent`, exactly. -/
def toRat (d : Decimal) : Rat := (d.mantissa : Rat) * (10 : Rat) ^ d.exponent

/-- The nearest decimal to `q` with at most `places` places, a half going up, and no zero at
the end of its fraction: `ofRat (1 / 3) 3` is `0.333`, and `ofRat (1 / 2) 3` is `0.5`. -/
def ofRat (q : Rat) (places : Nat := 3) : Decimal :=
  fixed places (q * (10 : Rat) ^ places + 1 / 2).floor

/-- The greatest decimal with at most `places` places that is no more than `q`. -/
def ofRatDown (q : Rat) (places : Nat := 3) : Decimal := fixed places (q * (10 : Rat) ^ places).floor

/-- The least decimal with at most `places` places that is no less than `q`. -/
def ofRatUp (q : Rat) (places : Nat := 3) : Decimal := fixed places (q * (10 : Rat) ^ places).ceil

end Decimal

/-- The point of the plane that a coordinate pair denotes. -/
def Point.toVec (p : Point) : Vec := ⟨p.x.toRat, p.y.toRat⟩

namespace Vec

/-- The coordinate pair that writes a point: each coordinate the nearest decimal with at most
`places` places. -/
def round (v : Vec) (places : Nat := 3) : Point := ⟨.ofRat v.x places, .ofRat v.y places⟩

end Vec

end Whatwg.Svg.Value
