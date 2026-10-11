import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.ViewBox

Owner: the value of the `viewBox` attribute (slice S4b of `docs/SVG-PACKAGE-PLAN.md`, section
5.3). The authority is the section `ViewBoxAttribute` of
`vendor/w3c-svgwg-47e645ef/master/coords.html`: the Value column
`[<min-x>,? <min-y>,? <width>,? <height>]`, the line under the table that makes each of the four
a `<number>`, and the paragraphs after it.

The typed value is `ViewBox`: four numbers. `minX` and `minY` are `Decimal`s. `width` and
`height` are `Magnitude`s, which have no sign. The section says that a negative width or height
is an error, so no value has one. A zero width or height is a value: the section says that it
disables rendering, and does not call it an error.

`ViewBox.grammar` is a `Grammar`, so its laws are those of `Whatwg/Svg/Value/Grammar.lean`. The
printer writes one spelling: the four numbers with one space between two, `0 0 1500 1000`. The
steps under `TermReserialize` of `master/types.html` write a rectangle that way, and
`ExampleViewBox` spells its value so. Each number is spelled as `Decimal` and `Magnitude` spell
it, so a width prints with no sign.

The reader takes
`wsp* coordinate comma_wsp? coordinate comma_wsp? extent comma_wsp? extent wsp*`. Here `extent`
is `"+"? number`, and the other names are productions of the path data grammar (`PathDataBNF`
of `master/paths.html`).

## The reading of the notation

The section `syntax` of `master/types.html` says that a Value column is written in the CSS
Value Definition Syntax by default, and its paragraph `attribute-css-value` says that such a
value is parsed against that grammar. The sealed text names the notation and does not restate
its marks. CSS Values defines them, and no CSS Values file is sealed (ruling SV-26). So a
reading below is either a statement of the sealed text, cited, or the mark as the named
notation has it, and each line says which.

- `<number>` is the production `coordinate` of the path data grammar, `sign? number`: the type
  `Decimal` (ruling SV-26).
- `,?` is at most one comma. This is the notation's. The sealed paragraph after the table says
  the same of the whole value: four numbers, "separated by whitespace and/or a comma". The
  production `comma_wsp` spells that phrase: white space in any amount around at most one comma.
- This module reads `comma_wsp?` between two numbers, so nothing is needed where a sign or a
  point parts them: `-50-50 500 500` is four numbers. The sealed rule is the paragraph after the
  path data grammar, that a production consumes as much as it can. It is applied here because
  the number is that grammar's. The sealed phrase above, read alone, asks for a separator
  there. The named notation asks for none, and this module follows the notation.
- White space at either end is read and printed as nothing. This is the notation's. The sealed
  text states it for path data alone: `svg_path` opens and closes with `wsp*`.
- A width or a height is `"+"? number`: a `coordinate` with no minus sign. The sealed text
  states the error in words and gives no production for it.

What this module does not claim:

- That `-0` is a width. Zero is not negative, so the sealed text does not call `0 0 -0 10` an
  error, and the reader refuses it. A description cannot read a sign and then decide by the
  value. A reader that took `-0` alone would stop inside `-0.5` and read `0 0 -0.5` as four
  numbers.
- A CSS comment. The note after `attribute-css-value` says that one may stand in such a value.
  The reader takes none.
- That the reader accepts every text of the expression's language (node V3b of the library,
  open). `0 0 12` is a text of four numbers in that language, and three numbers to the reader.
- What a value does. The transform of `ComputingAViewportsTransform`, the effect of
  `preserveAspectRatio` and the rule that a zero width disables rendering are not modelled.
- That two values which denote one rectangle are equal. A number keeps its digits, so
  `0 0 1.50 1` and `0 0 1.5 1` are two values.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- The typed value of `viewBox`: the rectangle `<min-x>`, `<min-y>`, `<width>`, `<height>`.
A width or a height has no sign, so none is negative. -/
structure ViewBox where
  /-- `<min-x>`. -/
  minX : Decimal
  /-- `<min-y>`. -/
  minY : Decimal
  /-- `<width>`. Zero is a value. -/
  width : Magnitude
  /-- `<height>`. Zero is a value. -/
  height : Magnitude
  deriving DecidableEq, Repr, Inhabited

namespace ViewBox

/-! ## A number that is not negative

A number that is not negative is no production of the path data grammar, and `Number.lean` has
no description of one. Any attribute whose number must not be negative reads the same two
parts. -/

/-- `"+"?`, read and printed as nothing. -/
def plus : Syn Unit := .skip (Syn.one (.single '+')).opt none

/-- The one value of `plus` prints: its canonical reading is no sign. -/
theorem plus_total : plus.Total := Syn.Total.of_unit (by decide)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] plus_total

/-- A `<number>` that is not negative: `"+"? number`, printed with no sign. A minus sign is
refused, before a zero too. -/
def extent : Syn Magnitude := .right plus Magnitude.syn

/-- Every `Magnitude` prints as an extent. -/
theorem extent_total : extent.Total := by
  unfold extent
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] extent_total

/-! ## The value -/

/-- The description of `viewBox`: `wsp*`, two numbers and two extents with `comma_wsp?` between
two of them, and `wsp*`. The four print with one space between two. -/
def syn : Syn ViewBox :=
  .map (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun v => (v.minX, v.minY, v.width, v.height))
    (fun _ => rfl)
    (.right wsps (.seq Decimal.syn (.seq (.right spaceSep Decimal.syn)
      (.seq (.right spaceSep extent) (.left (.right spaceSep extent) wsps)))))

/-- Every value prints: a `ViewBox` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `viewBox`. -/
def grammar : Grammar ViewBox := ⟨syn, by decide +kernel, syn_total⟩

end ViewBox

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] ViewBox.syn_total

end Whatwg.Svg.Value
