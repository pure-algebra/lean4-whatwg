import Whatwg.Html.Node.SvgBuild
import Whatwg.Svg.Geometry.Rational.Laws

/-!
# Whatwg.Html.Node.SvgLit

Owner: a literal where a typed value stands (slice S17 of `docs/SVG-PACKAGE-PLAN.md`).
`Whatwg/Svg/Geometry/Convert.lean` lets a program write a number where a `Length` is expected.
The sizes had a numeral and nothing else: a size with a fraction was
`.user (Magnitude.ofDecimal (.ofRat (25 / 2)))`, a size that a program holds as a `Nat` was
`.user (.ofNat n)`, and a colour was `Rgb.ofNat 0x14110d`. This module gives the rest:

- a decimal literal is a `Magnitude`, an `Extent`, an `AutoExtent`, a `LengthList` of one and a
  `NumberList` of one: `Svg.circle 10 10 2.5`, `Svg.rect 0 0 12.5 20`;
- a `Nat` is a `Magnitude`, an `Extent`, an `AutoExtent` and a `LengthList` of one:
  `.attr .width (width : AutoExtent)`;
- a `Magnitude` is an `Extent` and an `AutoExtent`, and an `Extent` an `AutoExtent`;
- a numeral is a colour, read as `0xRRGGBB`: `(0x14110d : Rgb)`. A paint is no number, so
  `.fill` takes the colour by the coercion that was there: `.fill ink` for `ink : Rgb`;
- `toString` of a size, a view box, a list of lengths or numbers, a colour and a paint is the
  text that an attribute holds, and `SvgNode` has a default, the empty text;
- `Svg.view` is the outer `svg` of a picture drawn at another size than its view box, which
  `Svg.Frame` does not write.

Every literal is exact: a decimal literal has an integer mantissa and a power of ten, which is
what a `Decimal` and a `Magnitude` hold. `Decimal.toRat_ofScientific` says so against core's
own reading of the literal as a `Rat`, and `Magnitude.toDecimal_ofScientific` that a size
written with a literal has the digits of the number written with it. `Rgb.toNat_ofNat` says
which colour a numeral is: the numeral itself below `0x1000000`, and its last twenty-four bits
above.

What this module does not claim: that a literal is the spelling a reader would choose. `2.50`
keeps its zero, as every `Decimal` keeps its digits; `Decimal.trim` drops it.
-/

namespace Whatwg.Svg.Value

/-! ## Sizes -/

namespace Magnitude

/-- The number that a size holds, as a signed number: the same digits. -/
def toDecimal (m : Magnitude) : Decimal := ⟨m.mantissa, m.exponent⟩

/-- A natural number is a size: `(n : Magnitude)` for `n : Nat`. -/
instance : NatCast Magnitude := ⟨ofNat⟩

/-- A decimal literal is the size it writes, digit for digit: `(2.5 : Magnitude)`. A literal
has no sign, so every literal is a size. -/
instance : OfScientific Magnitude :=
  ⟨fun mantissa negative exponent =>
    ⟨mantissa, if negative then -Int.ofNat exponent else Int.ofNat exponent⟩⟩

/-- A size written with a literal has the digits of the number written with it. -/
theorem toDecimal_ofScientific (mantissa : Nat) (negative : Bool) (exponent : Nat) :
    (OfScientific.ofScientific mantissa negative exponent : Magnitude).toDecimal =
      OfScientific.ofScientific mantissa negative exponent := rfl

/-- A size of a natural number has the digits of that number. -/
theorem toDecimal_natCast (n : Nat) : ((n : Magnitude)).toDecimal = Decimal.ofInt n := rfl

end Magnitude

/-- A size is a length that is not negative, in user units. -/
instance : Coe Magnitude Extent := ⟨Extent.user⟩

/-- A natural number is that many user units: `(n : Extent)` for `n : Nat`. -/
instance : NatCast Extent := ⟨fun n => Extent.user (.ofNat n)⟩

/-- A decimal literal is that many user units: `Svg.circle 10 10 2.5`. -/
instance : OfScientific Extent :=
  ⟨fun mantissa negative exponent =>
    Extent.user (OfScientific.ofScientific mantissa negative exponent)⟩

/-- A size is a size or `auto`. -/
instance : Coe Magnitude AutoExtent := ⟨AutoExtent.user⟩

/-- A length that is not negative is a size or `auto`. -/
instance : Coe Extent AutoExtent := ⟨AutoExtent.extent⟩

/-- A natural number is that many user units: `.attr .width (width : AutoExtent)`. -/
instance : NatCast AutoExtent := ⟨fun n => AutoExtent.user (.ofNat n)⟩

/-- A decimal literal is that many user units: `Svg.rect 0 0 12.5 20`. -/
instance : OfScientific AutoExtent :=
  ⟨fun mantissa negative exponent =>
    AutoExtent.user (OfScientific.ofScientific mantissa negative exponent)⟩

/-! ## Lists of one -/

/-- A natural number is one length of that many user units: the place of a text. -/
instance : NatCast LengthList := ⟨fun n => LengthList.single (Length.user (.ofInt (Int.ofNat n)))⟩

/-- A decimal literal is one length in user units: `Svg.text 4.5 14 "label"`. -/
instance : OfScientific LengthList :=
  ⟨fun mantissa negative exponent =>
    LengthList.single (Length.user (OfScientific.ofScientific mantissa negative exponent))⟩

/-- A numeral is a list of one number: `.attr .rotate 90` on `text`. -/
instance (n : Nat) : OfNat NumberList n := ⟨NumberList.single (.ofInt n)⟩

/-- A decimal literal is a list of one number. -/
instance : OfScientific NumberList :=
  ⟨fun mantissa negative exponent =>
    NumberList.single (OfScientific.ofScientific mantissa negative exponent)⟩

/-! ## A value as text -/

/-- The text of a size: the one spelling its grammar prints. -/
instance : ToString Magnitude := ⟨fun m => String.ofList (Magnitude.grammar.print m)⟩

/-- The text of a length that is not negative. -/
instance : ToString Extent := ⟨fun e => String.ofList (Extent.grammar.print e)⟩

/-- The text of a size or `auto`. -/
instance : ToString AutoExtent := ⟨fun e => String.ofList (AutoExtent.grammar.print e)⟩

/-- The text of a view box. -/
instance : ToString ViewBox := ⟨fun b => String.ofList (ViewBox.grammar.print b)⟩

/-- The text of a list of lengths. -/
instance : ToString LengthList := ⟨fun l => String.ofList (LengthList.grammar.print l)⟩

/-- The text of a list of numbers. -/
instance : ToString NumberList := ⟨fun l => String.ofList (NumberList.grammar.print l)⟩

/-! ## A literal is the number it writes -/

namespace Decimal

/-- **A decimal literal is the number it writes.** The value of a literal as a `Decimal`
denotes the rational number that core reads the same literal as: `(13.288 : Decimal).toRat` is
`(13.288 : Rat)`, for every mantissa and every exponent. Nothing is rounded. -/
theorem toRat_ofScientific (mantissa : Nat) (negative : Bool) (exponent : Nat) :
    (OfScientific.ofScientific mantissa negative exponent : Decimal).toRat =
      (OfScientific.ofScientific mantissa negative exponent : Rat) := by
  cases negative with
  | false =>
    show ((Int.ofNat mantissa : Int) : Rat) * (10 : Rat) ^ (Int.ofNat exponent) =
      Rat.ofScientific mantissa false exponent
    rw [Rat.ofScientific_false_def]
    simp only [Int.ofNat_eq_natCast, Rat.zpow_natCast, Rat.intCast_natCast, Rat.natCast_mul,
      Rat.natCast_pow]
    rfl
  | true =>
    show ((Int.ofNat mantissa : Int) : Rat) * (10 : Rat) ^ (-Int.ofNat exponent) =
      Rat.ofScientific mantissa true exponent
    rw [Rat.ofScientific_true_def, Rat.mkRat_eq_div, Rat.zpow_neg, Rat.div_def]
    simp only [Int.ofNat_eq_natCast, Rat.zpow_natCast, Rat.natCast_pow]
    rfl

/-- A numeral is the integer it writes. -/
theorem toRat_ofNat (n : Nat) : (OfNat.ofNat n : Decimal).toRat = (n : Rat) := by
  show (ofInt (n : Int)).toRat = (n : Rat)
  rw [toRat_ofInt, Rat.intCast_natCast]

end Decimal

end Whatwg.Svg.Value

namespace Whatwg.Html

open Whatwg.Svg.Value

/-! ## A colour -/

/-- The text of a colour: `#rrggbb`. -/
instance : ToString Rgb := ⟨Rgb.hex⟩

/-- The text of a paint, as `fill` holds it. -/
instance : ToString Paint := ⟨Paint.css⟩

/-- A tree to stand where one is needed and none is given: an empty text. -/
instance : Inhabited SvgNode := ⟨.text ""⟩

/-- A numeral is the colour `0xRRGGBB`: `(0x14110d : Rgb)`. -/
instance (n : Nat) : OfNat Rgb n := ⟨.ofNat n⟩


/-- **Which colour a numeral is**: the number of the colour of `n` is `n` without its bits above
the twenty-fourth. -/
theorem Rgb.toNat_ofNat (n : Nat) : (Rgb.ofNat n).toNat = n % 16777216 := by
  show (UInt8.ofNat (n / 65536)).toNat * 65536 + (UInt8.ofNat (n / 256)).toNat * 256 +
    (UInt8.ofNat n).toNat = _
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  omega

/-- A numeral of six hexadecimal digits or fewer is the colour it writes, exactly. -/
theorem Rgb.toNat_ofNat_of_lt {n : Nat} (h : n < 16777216) : (Rgb.ofNat n).toNat = n := by
  rw [Rgb.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## A picture at another size than its view box -/

/-- The outer `svg` of a picture that is `width` by `height` pixels and shows the rectangle
`box` of user space: the namespace, the caller's attributes, then `width`, `height` and
`viewBox`. `Svg.Frame` is the case where the box starts at the origin and has the viewport's
aspect ratio; this one writes any box, so the default `preserveAspectRatio` may leave a band. -/
def Svg.view (width height : Nat) (box : ViewBox) (more : List (SvgAttr .svg))
    (children : List SvgNode) : SvgNode :=
  Svg.svg
    (more ++ [.attr .width (width : AutoExtent), .attr .height (height : AutoExtent),
      .attr .viewBox box])
    children

/-- A frame is the view of its own box: `Svg.view` writes what `Svg.Frame.svg` writes. -/
theorem Svg.Frame.svg_eq_view (f : Svg.Frame) (more : List (SvgAttr .svg))
    (children : List SvgNode) :
    f.svg more children = Svg.view f.width f.height f.viewBox more children := rfl

end Whatwg.Html
