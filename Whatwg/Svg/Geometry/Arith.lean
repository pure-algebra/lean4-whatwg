import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Geometry.Arith

Owner: arithmetic on the exact numbers (slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-43).
`Whatwg/Svg/Geometry/` is the layer that computes with the typed values of
`Whatwg/Svg/Value/`. It is under the repository's ordinary axiom ceiling, so that it can use the
arithmetic of Lean's core library (`Rat`, `Nat.sqrt`, `grind`) and not prove it again; the
value grammars stay under the strict one.

A `Decimal` is an integer mantissa and a power of ten. Three operations are exact on such a
value and are defined here: the sum, the difference and the product. A quotient is not exact,
so there is none. A number is rounded in two places only, each to a stated number of places
with a half going up: `ofQuotient`, the quotient of two integers, and `divRound`, a number
divided by an integer. `half` is the one quotient that is exact.

What is here:

- `Decimal`: `+`, `-`, `*`, `half`, `mid`, `fixed` (a count of thousandths as a number),
  `ofQuotient`, `divRound`, the casts of an `Int` and a `Nat`, a decimal literal such as
  `13.25`, and `toString`, which is the grammar's printer.
- `Point`: `+`, `-`, `scale`, `mid`, `ofInts`, `ofPair`, `fixed`.

A sum or a product keeps the places of its operands: `0.5 + 0.5` is the value `1.0`, which
denotes one and prints as `1.0`. `Decimal.trim` drops the zeros at the end of a fraction, and
`mid` and the rounded quotients are trimmed already.

The laws are in `Whatwg/Svg/Geometry/Arith/Laws.lean`, which states the three operations as
exact on values (`a * (b + c) = a * b + a * c` is an equation of values), and in
`Whatwg/Svg/Geometry/Arith/Same.lean`, which states what they do to the numbers. The order is
`Whatwg/Svg/Geometry/Order.lean`, and the conversions to a length, a size and a list are
`Whatwg/Svg/Geometry/Convert.lean`.

What this module does not claim: an exact quotient, a square root or a trigonometric function.
-/

namespace Whatwg.Svg.Value

/-! ## Decimals -/

namespace Decimal

/-- The mantissa of the value at the exponent `e`: for `e` at most the value's exponent, the
integer `n` with the value's number equal to `n × 10 ^ e`. -/
def mantissaAt (d : Decimal) (e : Int) : Int := d.mantissa * 10 ^ (d.exponent - e).toNat

/-- The sum, exactly, at the lesser of the two exponents: `1.5 + 0.25` is `1.75`. -/
def add (a b : Decimal) : Decimal :=
  ⟨a.mantissaAt (min a.exponent b.exponent) + b.mantissaAt (min a.exponent b.exponent),
    min a.exponent b.exponent⟩

instance : Add Decimal := ⟨add⟩

/-- The difference, exactly: the sum with the opposite number. -/
def sub (a b : Decimal) : Decimal := a + -b

instance : Sub Decimal := ⟨sub⟩

/-- The product, exactly: the mantissas multiply and the exponents add. -/
def mul (a b : Decimal) : Decimal := ⟨a.mantissa * b.mantissa, a.exponent + b.exponent⟩

instance : Mul Decimal := ⟨mul⟩

/-- Half of the number, exactly: five times the mantissa, one place lower. -/
def half (d : Decimal) : Decimal := ⟨d.mantissa * 5, d.exponent - 1⟩

/-- The number half way between two numbers, exactly, with no zero at the end of its fraction:
`mid 0 10` is `5`. -/
def mid (a b : Decimal) : Decimal := (a + b).half.trim

/-- A decimal literal is the number it writes, digit for digit: `(13.25 : Decimal)`. -/
instance : OfScientific Decimal :=
  ⟨fun mantissa negative exponent =>
    ⟨Int.ofNat mantissa, if negative then -Int.ofNat exponent else Int.ofNat exponent⟩⟩

/-- An integer is a number: `(n : Decimal)` for `n : Int`. -/
instance : IntCast Decimal := ⟨ofInt⟩

/-- A natural number is a number: `(n : Decimal)` for `n : Nat`. -/
instance : NatCast Decimal := ⟨fun n => ofInt (Int.ofNat n)⟩

/-- `n / 10 ^ places` with no zero at the end of its fraction: `fixed 3 13250` is `13.25` and
`fixed 3 10000` is `10`. A program that counts in thousandths writes its numbers so. -/
def fixed (places : Nat) (n : Int) : Decimal := (ofScaled n places).trim

/-- The integer nearest to `num × 10 ^ places / den`, a half going up; zero for a zero
divisor. -/
def roundQuotient (num den : Int) (places : Nat) : Int :=
  if den = 0 then 0
  else
    let n := (if 0 < den then num else -num) * 10 ^ places
    let d : Int := den.natAbs
    (2 * n + d) / (2 * d)

/-- The quotient `num / den` rounded to a number of places, a half going up: the one rounding
of this module. `ofQuotient 1 3 3` is `0.333`, and `ofQuotient 2 3 3` is `0.667`. -/
def ofQuotient (num den : Int) (places : Nat) : Decimal := fixed places (roundQuotient num den places)

/-- The number divided by an integer and rounded to a number of places, a half going up; zero
for a zero divisor. `divRound 1 3 3` is `0.333`. It is exact where the quotient has that many
places: `divRound 3 6 1` is `0.5`. -/
def divRound (d : Decimal) (den : Int) (places : Nat) : Decimal :=
  fixed places
    (roundQuotient (d.mantissa * 10 ^ (d.exponent + places).toNat)
      (den * 10 ^ (-(d.exponent + places)).toNat) 0)

/-- The text of a number: the one spelling its grammar prints. -/
instance : ToString Decimal := ⟨fun d => String.ofList (grammar.print d)⟩

end Decimal

/-! ## Points -/

namespace Point

/-- The sum, coordinate by coordinate. -/
instance : Add Point := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩

/-- The difference, coordinate by coordinate. -/
instance : Sub Point := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩

/-- The point with each coordinate multiplied by `k`. -/
def scale (k : Decimal) (p : Point) : Point := ⟨k * p.x, k * p.y⟩

/-- The point half way between two points, exactly. -/
def mid (p q : Point) : Point := ⟨(p.x + q.x).half, (p.y + q.y).half⟩

/-- A point of whole units. -/
def ofInts (x y : Int) : Point := ⟨.ofInt x, .ofInt y⟩

/-- A point of a pair of whole units. -/
def ofPair (p : Int × Int) : Point := ⟨.ofInt p.1, .ofInt p.2⟩

/-- A point whose coordinates are counts of `10 ^ -places`: `fixed 3 1500 250` is
`1.5,0.25`. -/
def fixed (places : Nat) (x y : Int) : Point := ⟨.fixed places x, .fixed places y⟩

end Point

end Whatwg.Svg.Value
