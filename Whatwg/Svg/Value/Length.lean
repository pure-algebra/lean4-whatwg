import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Length

Owner: the length of an SVG attribute value (slice S4d of `docs/SVG-PACKAGE-PLAN.md`; debt D89
of `COORDINATION.md`; rulings SV-26 and SV-31: a length takes only what the sealed SVG text
states). The authority is the sealed text under `vendor/w3c-svgwg-47e645ef/master/`, in four
places:

- `types.html`, the section `syntax`, the steps under `presentation-attribute-css-value`. When
  a presentation attribute is parsed, each `<length>` of its grammar becomes
  `[<length> | <number>]`, and each `<length-percentage>` becomes
  `[<length-percentage> | <number>]`. The note after the steps gives the reason: a presentation
  attribute takes a length with no unit.
- `types.html`, the section `syntax`, the annotation before those steps. Its resolution makes
  property values case-insensitive.
- `types.html`, the section `InterfaceSVGLength`. An `SVGLength` value "can be a `<length>`,
  `<percentage>` or `<number>`". The table of the unit type constants names ten kinds: a number
  with no unit, a percentage, and a length with the unit `em`, `ex`, `px`, `cm`, `mm`, `in`,
  `pt` or `pc`. The note under `__svg__SVGLength__unitType` names `ch` and `calc()` as examples
  of a value that has no kind of its own.
- `shapes.html`, the attribute tables `LineElementX1Attribute` and `LineElementX2Attribute`.
  The Value column of `x1`, `y1`, `x2` and `y2` is `<length-percentage> | <number>`.

The number is SVG's own production (ruling SV-26): `coordinate`, `sign? number`, of the grammar
under `PathDataBNF` of `paths.html`. Its typed value is `Decimal` of
`Whatwg/Svg/Value/Number.lean`.

The typed value is `Length`: a `Decimal` and a `LengthUnit`. `LengthUnit` has the ten kinds of
the table and no other. `LengthUnit.number` is the number with no unit, `percentage` is `%`, and
`inch` is the unit `in`, which is a keyword of Lean.

`Length.grammar` is a `Grammar`, so its laws are those of `Whatwg/Svg/Value/Grammar.lean`. The
printer writes one spelling of a value: the number as `Decimal.grammar` prints it, then the mark
in lower case with nothing between. `10`, `1.5em`, `50%`, `-0.5in` and `15e1px` are five. The
mark of a number with no unit is the empty text.

The reader takes `wsp* sign? number mark wsp*`, where `sign`, `number` and `wsp` are
productions of the path data grammar and `mark` is the mark of one of the ten kinds, which is
empty for a number with no unit. A mark is read in either letter case: `1em`, `1EM` and `1Em`
are one value. A reading keeps the digits it is given, as `Decimal` does: `1.50em` reads as
`150 × 10 ^ -2` with the unit `em`.

## The readings

The sealed text sends a presentation attribute to the parser of CSS, and names `<length>`,
`<percentage>` and `<number>` by reference. CSS Values and CSS Syntax are not sealed (ruling
SV-26). So each line below is a statement of the sealed text, cited, or a reading of this
module, and says which.

- The marks are the table's, in the letters the table writes. The mark of a percentage is `%`:
  the note under `__svg__SVGLength__valueInSpecifiedUnits` writes `12%`.
- The mark follows the number with nothing between. The sealed text gives no production for a
  length. It writes one that way wherever it writes one: `10px` in the note after
  `attribute-css-value` of `types.html`, `12%` and `12em` in the note above, and `4in`, `25%`
  and `10cm` in the examples under `EstablishingANewSVGViewport` and `SizingSVGInCSS` of
  `coords.html`. That nothing may stand between is a reading of this module.
- A mark in either letter case is the annotation's resolution. It speaks of property values.
  This module applies it to the letters of a mark, and to nothing else.
- White space at either end is read in any amount and printed as nothing. The sealed text
  states that for path data alone: `svg_path` opens and closes with `wsp*`. The set here is
  `wspSet`, the `wsp` of path data, as in `Whatwg/Svg/Value/ViewBox.lean`. This is a reading
  of this module.

## One character decides

After a number, `e` may open an exponent, as in `1e3`, or the mark `em` or `ex`, as in `1em`.
The description `Decimal.syn` and then a mark reads both, because the reader of a choice starts
again where the choice began. But `Syn.ok` is a test of one character, and it is the premise of
the retraction `Grammar.read_print`. That description fails the test: the exponent of a number
may be absent, and a mark that follows may open with the `e` that opens an exponent. So the
description here is left-factored. It reads the sign and `fractional-constant`, and then
`Length.tail`:

    tail       = "e" ( sign? digit+ mark | "m" | "x" ) | other-mark?
    mark       = "e" ( "m" | "x" ) | other-mark?
    other-mark = "%" | "p" ( "x" | "t" | "c" ) | "cm" | "mm" | "in"

Each letter is read in either case. At an `e`, an exponent follows and then the mark of any
kind, or `m` or `x` follows: the marks `em` and `ex` with no exponent. The marks `px`, `pt` and
`pc` open with one letter, so they are under one `p`. The language is that of
`sign? number mark`, because concatenation distributes over a choice. `Length.ofReading` hands
the sign, the digits and the exponent to `Decimal.ofReading` and `Magnitude.ofReading`, so the
number of a length is theirs and no arithmetic is done again.

The left-factored description is deterministic (`Syn.deterministic` of
`Whatwg/Svg/Value/Deterministic.lean`): `WhatwgTest/Svg/Deterministic.lean` evaluates the
test. So the check of a length decides the language of the description's expression (node V3c
of the plan).

What this module does not claim: this is a part of what SVG admits, not all of it.

- A unit that the sealed table does not name (`rem`, `vw`, `ch` and the rest of CSS Values), a
  `calc()` expression, a CSS comment and a CSS escape are refused here. The sealed text admits
  them by reference to specifications that are not pinned: the section `Units` of `coords.html`
  takes its values and units from CSS Values, and the note after `attribute-css-value` of
  `types.html` says that `10\px/**/` parses as `10px`.
- No range is checked. A negative `width` passes.
- Which attribute takes a length, and which of the ten kinds it takes, is
  `Whatwg/Svg/Value/Attribute.lean`'s. This grammar reads `<length-percentage> | <number>`.
- What a length measures. No unit is converted to another, no percentage is resolved, and
  `SVG_LENGTHTYPE_UNKNOWN` has no kind here.
- That two values which denote one length are equal. A number keeps its digits, so `1.50em`
  and `1.5em` are two values.
- That another reading of `<length>` is wrong. Ruling SV-31 of the plan is this one, and an
  owner may widen it.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-- The kind of a length, as the unit table of `SVGLength` names them. -/
inductive LengthUnit where
  /-- A number with no unit: a length in user units. Its mark is the empty text. -/
  | number
  /-- A percentage: the mark `%`. -/
  | percentage
  /-- The unit `em`. -/
  | em
  /-- The unit `ex`. -/
  | ex
  /-- The unit `px`. -/
  | px
  /-- The unit `cm`. -/
  | cm
  /-- The unit `mm`. -/
  | mm
  /-- The unit `in`. -/
  | inch
  /-- The unit `pt`. -/
  | pt
  /-- The unit `pc`. -/
  | pc
  deriving DecidableEq, Repr, Inhabited

/-- A length of an attribute value: an exact decimal and its unit. -/
structure Length where
  /-- The number before the mark, with the digits the text gives. -/
  value : Decimal
  /-- The kind of the length: the mark after the number. -/
  unit : LengthUnit
  deriving DecidableEq, Repr, Inhabited

namespace Length

/-! ## The marks

A part of a larger description is an `abbrev`: the search that proves a grammar total
(`Whatwg.Syn`) reads through it, so a part states no totality lemma of its own. A letter is the
one part with a lemma, because its totality is an evaluation at that letter. -/

/-- One letter of a unit mark: read in either case, printed in lower case. -/
def letter (c : Char) : Syn Unit := .skip (.one (.ofList [c, c.toUpper])) c

/-- A letter prints, when it is ASCII: one evaluation. -/
theorem letter_total (c : Char) (h : (letter c).valid () = true) : (letter c).Total :=
  Syn.Total.of_unit h

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] letter_total

/-- `"m" | "x"`: what is left of the marks `em` and `ex` after their `e`. -/
abbrev emOrEx : Syn (Unit ⊕ Unit) := .alt (letter 'm') (letter 'x')

/-- A mark that does not open with `e`: `"%" | "p" ("x" | "t" | "c") | "cm" | "mm" | "in"`. The
three marks that open with `p` are under one `p`. -/
abbrev otherMark : Syn (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))) :=
  .alt (.lit ['%'])
    (.alt (.right (letter 'p') (.alt (letter 'x') (.alt (letter 't') (letter 'c'))))
      (.alt (.right (letter 'c') (letter 'm'))
        (.alt (.right (letter 'm') (letter 'm')) (.right (letter 'i') (letter 'n')))))

/-- The mark of any of the ten kinds: `"e" ("m" | "x") | other-mark?`. The mark of a number
with no unit is the empty text. -/
abbrev mark :
    Syn ((Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit))))) :=
  .alt (.right (letter 'e') emOrEx) otherMark.opt

/-- What follows `fractional-constant`: `"e" (sign? digit+ mark | "m" | "x") | other-mark?`.
At an `e`, an exponent follows and then the mark of any kind, or the `m` or `x` of `em` and
`ex` follows. With no `e`, a mark that does not open with `e` follows, or nothing. The `e` of
an exponent and the `e` of `em` and `ex` are one description, printed as `e`. -/
abbrev tailSpellings :
    Syn ((((Option Bool × Nat) ×
        ((Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))))) ⊕
        (Unit ⊕ Unit)) ⊕
      Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit))))) :=
  .alt (.right (letter 'e') (.alt (.seq (.seq sign.opt natural) mark) emOrEx)) otherMark.opt

/-- The unit of a reading of `mark`: the alternative names it, and the empty mark is a number
with no unit. -/
def markUnit :
    (Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))) →
      LengthUnit
  | .inl (.inl _) => .em
  | .inl (.inr _) => .ex
  | .inr none => .number
  | .inr (some (.inl _)) => .percentage
  | .inr (some (.inr (.inl (.inl _)))) => .px
  | .inr (some (.inr (.inl (.inr (.inl _))))) => .pt
  | .inr (some (.inr (.inl (.inr (.inr _))))) => .pc
  | .inr (some (.inr (.inr (.inl _)))) => .cm
  | .inr (some (.inr (.inr (.inr (.inl _))))) => .mm
  | .inr (some (.inr (.inr (.inr (.inr _))))) => .inch

/-- The reading of a unit: the alternative of `mark` that spells it. -/
def markReading : LengthUnit →
    (Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit))))
  | .em => .inl (.inl ())
  | .ex => .inl (.inr ())
  | .number => .inr none
  | .percentage => .inr (some (.inl ()))
  | .px => .inr (some (.inr (.inl (.inl ()))))
  | .pt => .inr (some (.inr (.inl (.inr (.inl ())))))
  | .pc => .inr (some (.inr (.inl (.inr (.inr ())))))
  | .cm => .inr (some (.inr (.inr (.inl ()))))
  | .mm => .inr (some (.inr (.inr (.inr (.inl ())))))
  | .inch => .inr (some (.inr (.inr (.inr (.inr ())))))

/-- The exponent reading and the unit of a reading of `tailSpellings`. With no exponent, the
two alternatives are the two halves of a reading of `mark`: the one at an `e`, and the other. -/
def tailValue :
    (((Option Bool × Nat) ×
        ((Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))))) ⊕
        (Unit ⊕ Unit)) ⊕
      Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))) →
      Option (Option Bool × Nat) × LengthUnit
  | .inl (.inl (e, m)) => (some e, markUnit m)
  | .inl (.inr m) => (none, markUnit (.inl m))
  | .inr m => (none, markUnit (.inr m))

/-- The reading of an exponent reading and a unit: with an exponent, the unit's mark after it;
with none, the mark alone, on the side of the `e` for `em` and `ex`. -/
def tailReading : Option (Option Bool × Nat) × LengthUnit →
    (((Option Bool × Nat) ×
        ((Unit ⊕ Unit) ⊕ Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit)))))) ⊕
        (Unit ⊕ Unit)) ⊕
      Option (Unit ⊕ ((Unit ⊕ (Unit ⊕ Unit)) ⊕ (Unit ⊕ (Unit ⊕ Unit))))
  | (some e, u) => .inl (.inl (e, markReading u))
  | (none, u) =>
    match markReading u with
    | .inl m => .inl (.inr m)
    | .inr m => .inr m

/-- A reading of an exponent and a unit is read as the two: by cases on the exponent and on
the ten units. -/
theorem tailValue_tailReading (p : Option (Option Bool × Nat) × LengthUnit) :
    tailValue (tailReading p) = p := by
  cases p with
  | mk e u => cases e <;> cases u <;> rfl

/-- What follows `fractional-constant`, as the exponent reading of `exponentPart` and the
unit. -/
abbrev tail : Syn (Option (Option Bool × Nat) × LengthUnit) :=
  .map tailValue tailReading tailValue_tailReading tailSpellings

/-! ## The value -/

/-- The value of a reading: the sign, the digits and the exponent as `Decimal.ofReading` and
`Magnitude.ofReading` read them, and the unit. -/
def ofReading
    (r : Option Bool × ((((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × (Option (Option Bool × Nat) × LengthUnit))) : Length :=
  ⟨Decimal.ofReading (r.1, Magnitude.ofReading (r.2.1, r.2.2.1)), r.2.2.2⟩

/-- The one spelling of a value: the number as `Decimal.toReading` and `Magnitude.toReading`
spell it, and the unit. -/
def toReading (l : Length) :
    Option Bool × ((((Fin 10 × List (Fin 10)) × Option (Fin 10 × List (Fin 10))) ⊕
      (Fin 10 × List (Fin 10))) × (Option (Option Bool × Nat) × LengthUnit)) :=
  ((Decimal.toReading l.value).1,
    ((Magnitude.toReading (Decimal.toReading l.value).2).1,
      ((Magnitude.toReading (Decimal.toReading l.value).2).2, l.unit)))

/-- A value's spelling reads as the value: the law of the magnitude, then the law of the
decimal. -/
theorem ofReading_toReading (l : Length) : ofReading (toReading l) = l := by
  cases l with
  | mk d u =>
    show Length.mk (Decimal.ofReading ((Decimal.toReading d).1,
      Magnitude.ofReading (Magnitude.toReading (Decimal.toReading d).2))) u = Length.mk d u
    rw [Magnitude.ofReading_toReading]
    show Length.mk (Decimal.ofReading (Decimal.toReading d)) u = Length.mk d u
    rw [Decimal.ofReading_toReading]

/-- The description of a length: `wsp*`, a sign or none, `fractional-constant`, the tail, and
`wsp*`. The number prints as `Decimal.syn` prints it, and the mark after it in lower case. -/
def syn : Syn Length :=
  .map ofReading toReading ofReading_toReading
    (.right wsps (.seq sign.opt (.seq fractionalConstant (.left tail wsps))))

/-- Every value prints: a `Length` is made of typed parts. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of a length: `<length-percentage> | <number>` over the ten kinds of the
table. -/
def grammar : Grammar Length := ⟨syn, by decide +kernel, syn_total⟩

/-- A length in user units. -/
def user (d : Decimal) : Length := ⟨d, .number⟩

/-- A numeral is that many user units: `10 : Length`. -/
instance (n : Nat) : OfNat Length n := ⟨user (.ofInt n)⟩

end Length

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Length.syn_total

end Whatwg.Svg.Value
