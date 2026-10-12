import Whatwg.Svg.Geometry.Arith
import Whatwg.Svg.Value.Length
import Whatwg.Svg.Value.Extent
import Whatwg.Svg.Value.Lists
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Transform

/-!
# Whatwg.Svg.Geometry.Convert

Owner: a number where a typed value stands, and a typed value as text (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-43). An attribute of the typed tree takes the carrier of
its grammar: a `Length`, an `AutoExtent`, a `LengthList`. A program computes with integers and
`Decimal`s. The instances here let it write the number where the value is expected:

- an `Int`, a `Nat`, a `Decimal` or a decimal literal is a `Length` in user units;
- a `Length` or a `Decimal` is a `LengthList` of one, and a `Decimal` a `NumberList` of one;
- `clamp` makes a size of an integer and writes a negative one as zero, where `ofInt?` of
  `Whatwg/Svg/Value/Extent.lean` refuses it;
- `ViewBox.ofSize` and `Points.ofList?` build the two values a picture needs most;
- `toString` of a path, of path data and of a transform list is the text its grammar prints.

Arithmetic under a cast is the arithmetic of the type inside it: `((x1 - x0 : Int) : Length)`
subtracts integers. A product of a `Nat` and an `Int` has no meaning to Lean until one of them
is cast, so write `((ratio : Int) * x : Length)`.
-/

namespace Whatwg.Svg.Value

/-! ## A number where a typed value stands -/

/-- A number is a length in user units. -/
instance : Coe Decimal Length := ⟨Length.user⟩

/-- An integer is a length in user units: `.attr .x (n : Int)` on `rect`. -/
instance : IntCast Length := ⟨fun n => Length.user (.ofInt n)⟩

/-- A decimal literal is a length in user units: `.attr .x 13.25` on `rect`. -/
instance : OfScientific Length :=
  ⟨fun mantissa negative exponent =>
    Length.user (OfScientific.ofScientific mantissa negative exponent)⟩

/-- A natural number is a length in user units. -/
instance : NatCast Length := ⟨fun n => Length.user (.ofInt (Int.ofNat n))⟩

/-- A length is a list of one length: the place of a text. -/
instance : Coe Length LengthList := ⟨LengthList.single⟩

/-- A number is a list of one length in user units. -/
instance : Coe Decimal LengthList := ⟨fun d => LengthList.single (Length.user d)⟩

/-- An integer is a list of one length in user units: `.attr .x (n : Int)` on `text`. -/
instance : IntCast LengthList := ⟨fun n => LengthList.single (Length.user (.ofInt n))⟩

/-- A number is a list of one number. -/
instance : Coe Decimal NumberList := ⟨NumberList.single⟩

/-- A size of an integer: a negative one is zero. `Magnitude.ofInt?` refuses a negative one
instead. -/
def Magnitude.clamp (v : Int) : Magnitude := .ofNat v.toNat

/-- A size in user units of an integer: a negative one is zero. -/
def Extent.clamp (v : Int) : Extent := .user (.clamp v)

/-- A size in user units of an integer: a negative one is zero. `AutoExtent.ofInt?` refuses a
negative one instead. -/
def AutoExtent.clamp (v : Int) : AutoExtent := .user (.clamp v)

/-- The view box of a picture `width` by `height` user units, from the origin. -/
def ViewBox.ofSize (width height : Nat) : ViewBox := ⟨0, 0, .ofNat width, .ofNat height⟩

/-- The points of a list, which has one point or more. -/
def Points.ofList? : List Point → Option Points
  | [] => none
  | p :: ps => some ⟨p, ps⟩

/-- The text of a path: the one spelling its grammar prints. -/
instance : ToString Path := ⟨fun p => String.ofList (Path.grammar.print p)⟩

/-- The text of path data. -/
instance : ToString PathData := ⟨fun d => String.ofList (PathData.grammar.print d)⟩

/-- The text of a transform list. -/
instance : ToString TransformList := ⟨fun ts => String.ofList (TransformList.grammar.print ts)⟩

/-- The text of a length. -/
instance : ToString Length := ⟨fun l => String.ofList (Length.grammar.print l)⟩

end Whatwg.Svg.Value
