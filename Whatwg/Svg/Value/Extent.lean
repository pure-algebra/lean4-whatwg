import Whatwg.Svg.Value.Length

/-!
# Whatwg.Svg.Value.Extent

Owner: the lengths of the geometry properties that must not be negative (slice S5 of
`docs/SVG-PACKAGE-PLAN.md`; debt D93 of `COORDINATION.md`; rulings SV-26 and SV-31: a length
takes only what the sealed SVG text states). The authority is the sealed text under
`vendor/w3c-svgwg-47e645ef/master/`, in five places:

- `geometry.html`, the paragraph `geometry-negative-values` and the table after it, the
  handling of negative values for the geometry properties. The properties `r`, `rx`, `ry`,
  `width` and `height` accept no negative value: for them "a negative `<length-percentage>` is
  invalid". The Value column of the table gives `<length-percentage>` for `r`, and
  `<length-percentage> | auto` for `rx`, `ry`, `width` and `height`.
- `geometry.html`, the property definitions `RProperty`, `RxProperty` and `RyProperty`, under
  the headings `R`, `RX` and `RY`. Their Value rows state the same grammars for `r`, `rx` and
  `ry`. The section `Sizing` has no such row for `width` and `height`: its first note sends
  their definitions to CSS 2.1. So the table above is the sealed statement of their value.
- `types.html`, the section `syntax`, the steps under `presentation-attribute-css-value`. When
  a presentation attribute is parsed, each `<length-percentage>` of its grammar becomes
  `[<length-percentage> | <number>]`.
- `types.html`, the section `syntax`, the annotation before those steps. Its resolution makes
  property values case-insensitive.
- `types.html`, the section `InterfaceSVGLength`. The table of the unit type constants names
  the ten kinds of a length: `LengthUnit` of `Whatwg/Svg/Value/Length.lean`.

Two typed values:

- `Extent` is a length that is not negative: a `Magnitude` of `Whatwg/Svg/Value/Number.lean`,
  which has no sign, and a `LengthUnit`. It is a value of the grammar that the table gives for
  `r`.
- `AutoExtent` is the keyword `auto` or an `Extent`. It is a value of the grammar that the
  table gives for `rx`, `ry`, `width` and `height`.

A negative length is a value of neither type, so no range is checked after a read.
`Extent.toLength` is the `Length` of an extent, and `Extent.print_eq_length` says that the two
have one text.

`Extent.grammar` and `AutoExtent.grammar` are each a `Grammar`, so their laws are those of
`Whatwg/Svg/Value/Grammar.lean`. The printer writes one spelling of a value: the number as
`Magnitude.grammar` prints it and then the mark in lower case with nothing between, or the
keyword in lower case. `10`, `1.5em`, `50%` and `auto` are four. No spelling has a sign.

The readers take

    extent      = wsp* core wsp*
    auto-extent = wsp* ( "auto" | core ) wsp*
    core        = "+"? fractional-constant tail

Here `wsp` and `fractional-constant` are productions of the path data grammar (`PathDataBNF` of
`paths.html`), `"+"?` is `plus` of `Number.lean`, and `tail` is `Length.tail`: the exponent of
the number and the mark of one of the ten kinds, left-factored at the letter `e`. The language
of `core` is that of `"+"? number mark`, for the reason `Length.lean` gives. A letter of a mark
or of the keyword is read in either case: `1EM` and `1em` are one value, and so are `AUTO` and
`auto`. A reading keeps the digits it is given, as `Magnitude` does.

## The readings

The sealed text sends a presentation attribute to the parser of CSS, and names
`<length-percentage>` and `<number>` by reference. CSS Values and CSS Syntax are not sealed
(ruling SV-26). The readings of `Length.lean` stand here: the marks, the mark after the number
with nothing between, and the number as SVG's own production. Each line below is a statement of
the sealed text, cited, or a reading of this module, and says which.

- A length that is not negative is `"+"? number mark`: a length with no minus sign. The sealed
  text states the rule in words and gives no production for it. This is a reading of this
  module. `Whatwg/Svg/Value/ViewBox.lean` reads a width of `viewBox` the same way.
- `-0` is refused, although zero is not negative. A description cannot read a sign and then
  decide by the value. This is a reading of this module.
- The keyword is `auto`, in the letters the table writes. A letter in either case is the
  annotation's resolution, which speaks of property values. This module applies it to the
  letters of the keyword and of a mark, and to nothing else. This is a reading of this module.
- White space at either end is read in any amount and printed as nothing, around the keyword
  too. The sealed text states that for path data alone: `svg_path` opens and closes with
  `wsp*`. The set here is `wspSet`, the `wsp` of path data. This is a reading of this module.

## One character decides

The two alternatives of `auto-extent` open with different characters: the keyword with `a` or
`A`, and a length with a plus sign, a digit or a point. The rest is `Length.tail`, which is
left-factored. So `Syn.ok` holds, and both descriptions are deterministic (`Syn.deterministic`
of `Whatwg/Svg/Value/Deterministic.lean`): `WhatwgTest/Svg/Extent.lean` evaluates the test. So
the check of each decides the language of its description's expression (node V3c of the plan).

What this module does not claim: this is the check of a text, and not the handling of a value.

- The fallback. The paragraph `geometry-negative-values` says that an invalid negative value is
  treated as the initial value of its property, `auto` or `0`, and that it never puts the
  element into an error state. The check here refuses the text and gives no value in its place.
  A caller that wants the fallback reads the refusal.
- A unit that the sealed table does not name, a `calc()` expression, a CSS comment and a CSS
  escape are refused, as for `Length`. The sealed text admits them by reference to
  specifications that are not pinned.
- Which attribute takes an extent, and which of the two types it takes, is
  `Whatwg/Svg/Value/Attribute.lean`'s.
- What a value measures. `auto` is not resolved, no percentage is resolved, and no unit is
  converted to another.
- That two values which denote one length are equal. A number keeps its digits, so `1.50em`
  and `1.5em` are two values.
- That another reading of a length that is not negative is wrong. Ruling SV-31 of the plan is
  the reading of a length, and an owner may widen it.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- A length that is not negative: an unsigned exact decimal and its unit. -/
structure Extent where
  /-- The number before the mark, with the digits the text gives. It has no sign. -/
  value : Magnitude
  /-- The kind of the length: the mark after the number. -/
  unit : LengthUnit
  deriving DecidableEq, Repr, Inhabited

/-- `auto`, or a length that is not negative. -/
inductive AutoExtent where
  /-- The keyword `auto`. -/
  | auto
  /-- A length that is not negative. -/
  | extent (value : Extent)
  deriving DecidableEq, Repr, Inhabited

namespace Extent

/-! ## The length that is not negative

A part of a larger description is an `abbrev`: the search that proves a grammar total
(`Whatwg.Syn`) reads through it, so a part states no totality lemma of its own. -/

/-- The value of a reading: the digits and the exponent as `Magnitude.ofReading` reads them,
and the unit. -/
def ofReading
    (r : (((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × (Option (Option Bool × Nat) × LengthUnit)) : Extent :=
  ⟨Magnitude.ofReading (r.1, r.2.1), r.2.2⟩

/-- The one spelling of a value: the number as `Magnitude.toReading` spells it, and the unit. -/
def toReading (e : Extent) :
    (((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × (Option (Option Bool × Nat) × LengthUnit) :=
  ((Magnitude.toReading e.value).1, ((Magnitude.toReading e.value).2, e.unit))

/-- A value's spelling reads as the value: the law of the magnitude. -/
theorem ofReading_toReading (e : Extent) : ofReading (toReading e) = e := by
  cases e with
  | mk m u =>
    show Extent.mk (Magnitude.ofReading (Magnitude.toReading m)) u = Extent.mk m u
    rw [Magnitude.ofReading_toReading]

/-- An extent without its white space: `"+"? fractional-constant tail`. A plus sign is read and
printed as nothing, and a minus sign is refused, before a zero too. The tail is that of a
length: the exponent and the mark, left-factored at `e`. -/
abbrev core : Syn Extent :=
  .map ofReading toReading ofReading_toReading (.right plus (.seq fractionalConstant Length.tail))

/-- The description of an extent: `wsp*`, the core, and `wsp*`. The number prints as
`Magnitude.syn` prints it, and the mark after it in lower case. -/
def syn : Syn Extent := .right wsps (.left core wsps)

/-- Every value prints: an `Extent` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of an extent: `<length-percentage> | <number>` over the ten kinds of the table,
with no minus sign. -/
def grammar : Grammar Extent := ⟨syn, by decide +kernel, syn_total⟩

/-- An extent in user units. -/
def user (m : Magnitude) : Extent := ⟨m, .number⟩

/-- The extent as a length: every extent is a length. -/
def toLength (e : Extent) : Length := ⟨⟨e.value.mantissa, e.value.exponent⟩, e.unit⟩

/-- An extent's text is its length's text: a length that is not negative prints with no sign,
so the two printers write the same number and the same mark. The two texts differ only in
where the empty text of the last `wsp*` is appended. -/
theorem print_eq_length (e : Extent) : grammar.print e = Length.grammar.print e.toLength := by
  show [] ++ ([] ++ (_ ++ _) ++ []) = [] ++ ([] ++ (_ ++ (_ ++ [])))
  rw [List.append_nil, List.append_nil]
  rfl

end Extent

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Extent.syn_total

namespace AutoExtent

/-! ## The keyword or a length -/

/-- The keyword `auto`: each letter read in either case, printed in lower case. -/
abbrev keyword : Syn Unit :=
  .right (Length.letter 'a')
    (.right (Length.letter 'u') (.right (Length.letter 't') (Length.letter 'o')))

/-- The value of a reading: the first alternative is the keyword, and the second a length. -/
def ofReading : Unit ⊕ Extent → AutoExtent
  | .inl _ => .auto
  | .inr e => .extent e

/-- The one spelling of a value: the alternative that spells it. -/
def toReading : AutoExtent → Unit ⊕ Extent
  | .auto => .inl ()
  | .extent e => .inr e

/-- A value's spelling reads as the value: by cases on the two constructors. -/
theorem ofReading_toReading (v : AutoExtent) : ofReading (toReading v) = v := by
  cases v <;> rfl

/-- The value without its white space: `"auto" | core`. One character decides: the keyword
opens with `a` or `A`, and an extent with a plus sign, a digit or a point. -/
abbrev core : Syn AutoExtent :=
  .map ofReading toReading ofReading_toReading (.alt keyword Extent.core)

/-- The description of `auto` or an extent: `wsp*`, the core, and `wsp*`. -/
def syn : Syn AutoExtent := .right wsps (.left core wsps)

/-- Every value prints: an `AutoExtent` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `auto` or an extent: `<length-percentage> | <number> | auto`, with no minus
sign. -/
def grammar : Grammar AutoExtent := ⟨syn, by decide +kernel, syn_total⟩

/-- A size in user units. -/
def user (m : Magnitude) : AutoExtent := .extent (.user m)

end AutoExtent

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] AutoExtent.syn_total

end Whatwg.Svg.Value
