import Whatwg.Html.Node.Svg
import Whatwg.Svg.Geometry.Arith

/-!
# Whatwg.Html.Node.SvgPaint

Owner: the presentation attributes a picture writes most, with typed arguments (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-47). A paint, an opacity and a stroke width have no
grammar in this package: no sealed text of this repository states the grammar of a colour, so
the table of kinds gives `fill`, `stroke` and their like the type `String` (ruling SV-26).

This module does not change that. It gives a program typed things to write instead of
strings, and writes the string for it:

- `Rgb` is a colour of three bytes, with `hex`, the text `#rrggbb`, and `ofHex?`, its reader;
  `Rgb.ofHex?_hex` says that the text of a colour reads back as the colour.
- `Paint` is `none`, `currentColor`, a colour, a reference `url(#id)`, or a text as it is.
- `SvgAttr.fill`, `stroke`, `strokeWidth`, `strokeDasharray`, the three opacities, the family,
  size and weight of a font, `textAnchor`, `xmlSpacePreserve`, `className`, `ident` and
  `clipPath` are attributes of any element (an attribute whose value is one of a closed set of
  keywords, such as `fill-rule`, is in `Whatwg/Html/Node/SvgKeyword.lean` since slice S17), and `dataKey?` is the `data-key`
  attribute of a key that is not empty. A number is written with no zero at the end of its
  fraction.

A helper is an attribute of every tag `t` because the table of kinds gives its name no kind on
any element: the value type computes to `String` with the tag a variable.

What this module does not claim: that a text it writes is a `<paint>` or an `<alpha-value>` of
SVG or CSS. `Paint.raw` is any string, and an opacity is any number. Nor that the element
takes the attribute: `SvgAttr.allOk` judges that, as for any attribute.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value (Decimal)

/-! ## A colour -/

/-- A colour by its red, green and blue. -/
structure Rgb where
  r : UInt8
  g : UInt8
  b : UInt8
  deriving DecidableEq, Repr, Inhabited

namespace Rgb

/-- The colour that the number `0xRRGGBB` writes. Bits above the twenty-fourth are dropped. -/
def ofNat (n : Nat) : Rgb := ⟨UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n⟩

/-- The number `0xRRGGBB` of a colour. -/
def toNat (c : Rgb) : Nat := c.r.toNat * 65536 + c.g.toNat * 256 + c.b.toNat

/-- The hexadecimal digit of a number under sixteen, in lower case. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The two hexadecimal digits of a byte. -/
def hexByte (b : UInt8) : List Char := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- `#rrggbb`, in lower case. -/
def hexChars (c : Rgb) : List Char := '#' :: (hexByte c.r ++ hexByte c.g ++ hexByte c.b)

/-- The text `#rrggbb` of a colour. -/
def hex (c : Rgb) : String := String.ofList c.hexChars

/-- The value of a hexadecimal digit, in either case. -/
def digitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

/-- The byte of two hexadecimal digits. -/
def byte? (hi lo : Char) : Option UInt8 :=
  (digitValue? hi).bind fun h => (digitValue? lo).map fun l => UInt8.ofNat (h * 16 + l)

/-- Read `#rrggbb`, or `#rgb`, where each digit stands twice. -/
def ofHexChars? : List Char → Option Rgb
  | ['#', r1, r0, g1, g0, b1, b0] =>
    (byte? r1 r0).bind fun r => (byte? g1 g0).bind fun g => (byte? b1 b0).map fun b => ⟨r, g, b⟩
  | ['#', r, g, b] =>
    (byte? r r).bind fun red => (byte? g g).bind fun green => (byte? b b).map fun blue =>
      ⟨red, green, blue⟩
  | _ => none

/-- Read the text of a colour: `#rrggbb` or `#rgb`. -/
def ofHex? (s : String) : Option Rgb := ofHexChars? s.toList

/-- A hexadecimal digit reads back as its value. -/
theorem digitValue?_hexDigit : ∀ n : Fin 16, digitValue? (hexDigit n.val) = some n.val := by
  decide +kernel

/-- The two digits of a byte read back as the byte. -/
theorem byte?_hexByte (b : UInt8) :
    byte? (hexDigit (b.toNat / 16)) (hexDigit (b.toNat % 16)) = some b := by
  have hi := digitValue?_hexDigit ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩
  have lo := digitValue?_hexDigit ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩
  simp only at hi lo
  rw [byte?, hi, lo, Option.bind_some, Option.map_some, Nat.div_add_mod', UInt8.ofNat_toNat]

/-- The text of a colour reads back as the colour: `hex` is an exact embedding. -/
theorem ofHexChars?_hexChars (c : Rgb) : ofHexChars? c.hexChars = some c := by
  show ofHexChars? ['#', hexDigit (c.r.toNat / 16), hexDigit (c.r.toNat % 16),
    hexDigit (c.g.toNat / 16), hexDigit (c.g.toNat % 16), hexDigit (c.b.toNat / 16),
    hexDigit (c.b.toNat % 16)] = some c
  rw [ofHexChars?, byte?_hexByte, byte?_hexByte, byte?_hexByte]
  rfl

/-- The text of a colour reads back as the colour. -/
theorem ofHex?_hex (c : Rgb) : ofHex? c.hex = some c := by
  rw [ofHex?, hex, String.toList_ofList, ofHexChars?_hexChars]

end Rgb

/-! ## A paint -/

/-- What `fill` and `stroke` take. -/
inductive Paint where
  /-- No paint. -/
  | none
  /-- The value of the `color` property. -/
  | currentColor
  /-- A colour. -/
  | rgb (c : Rgb)
  /-- A paint server by its identifier: `url(#id)`. -/
  | url (id : String)
  /-- A text as it is: a colour name, a function of CSS, or anything else. -/
  | raw (css : String)
  deriving DecidableEq, Repr, Inhabited

/-- A reference to an element by its identifier, as a presentation attribute writes it:
`url(#id)`. The identifier is written as it is: one that holds a `)` or white space makes a
reference that no element answers. -/
def urlRef (id : String) : String := "url(#" ++ id ++ ")"

/-- The text of a paint. -/
def Paint.css : Paint → String
  | .none => "none"
  | .currentColor => "currentColor"
  | .rgb c => c.hex
  | .url id => urlRef id
  | .raw css => css

/-- A colour is a paint. -/
instance : Coe Rgb Paint := ⟨.rgb⟩

/-! ## Attributes of any element -/

/-- Where a text is anchored at its place: `text-anchor`. -/
inductive TextAnchor where
  | start | middle | «end»
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of an anchor. -/
def TextAnchor.css : TextAnchor → String
  | .start => "start"
  | .middle => "middle"
  | .«end» => "end"

namespace SvgAttr

variable {t : Tag}

/-- The text of a number that was computed: with no zero at the end of its fraction. -/
def numberText (d : Decimal) : String := toString d.trim

/-- `fill`. -/
def fill (p : Paint) : SvgAttr t := .attr .fill p.css

/-- `stroke`. -/
def stroke (p : Paint) : SvgAttr t := .attr .stroke p.css

/-- `stroke-width`, a number of user units. -/
def strokeWidth (w : Decimal) : SvgAttr t := .attr .stroke_width (numberText w)

/-- `stroke-dasharray`: the lengths of the dashes and the gaps, in user units. -/
def strokeDasharray (lengths : List Decimal) : SvgAttr t :=
  .attr .stroke_dasharray (" ".intercalate (lengths.map numberText))

/-- `opacity`. -/
def opacity (o : Decimal) : SvgAttr t := .attr .opacity (numberText o)

/-- `fill-opacity`. -/
def fillOpacity (o : Decimal) : SvgAttr t := .attr .fill_opacity (numberText o)

/-- `stroke-opacity`. -/
def strokeOpacity (o : Decimal) : SvgAttr t := .attr .stroke_opacity (numberText o)


/-- `font-family`, as CSS writes a list of families. -/
def fontFamily (css : String) : SvgAttr t := .attr .font_family css

/-- `font-size`, a number of user units. -/
def fontSize (size : Decimal) : SvgAttr t := .attr .font_size (numberText size)

/-- `font-weight`, a number such as 400 or 700. -/
def fontWeight (weight : Nat) : SvgAttr t := .attr .font_weight (toString weight)


/-- `text-anchor`. -/
def textAnchor (anchor : TextAnchor) : SvgAttr t := .attr .text_anchor anchor.css


/-- `xml:space="preserve"`: the white space of a text is kept. -/
def xmlSpacePreserve : SvgAttr t := .attr .xml_space "preserve"

/-- `class`. -/
def className (c : String) : SvgAttr t := .attr .«class» c

/-- `id`. -/
def ident (i : String) : SvgAttr t := .attr .id i

/-- `clip-path`, by the identifier of a `clipPath` element: `url(#id)`. -/
def clipPath (id : String) : SvgAttr t := .attr .clip_path (urlRef id)

/-- The `data-key` attribute of a key, and no attribute for the empty key. -/
def dataKey? (key : String) : List (SvgAttr t) := if key.isEmpty then [] else [.data "key" key]
end SvgAttr

end Whatwg.Html
