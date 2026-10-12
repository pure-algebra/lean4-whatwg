import Whatwg.Svg.Value.Length

/-!
# WhatwgTest.Svg.Length

Readers, controls and finite evaluations of the length grammar (debt D89 of `COORDINATION.md`;
ruling SV-26 of `docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Length.lean`.

The first section replays lengths that the sealed text writes out, in the places the module
cites. The files are under `vendor/w3c-svgwg-47e645ef/master/`:

- `types.html` writes `10px` in the note after `attribute-css-value`, and `12%` and `12em` in
  the note under `__svg__SVGLength__valueInSpecifiedUnits`.
- `coords.html` writes `100px` and `200px` under `ViewportSpace`, `4in`, `3in`, `25%` and `50%`
  under `EstablishingANewSVGViewport`, and `10cm`, `5cm`, `100%` and `75%` under
  `SizingSVGInCSS`.

These are not all the lengths of the sealed chapters. The same two notes of `types.html` write
`10\px/**/` and `calc(12px + 5%)`, which the sealed text admits and this grammar refuses: they
are controls below. Every other text is made for the battery.

A reader applies a law of `Grammar` at a real value. A control shows where the grammar or a law
stops.
-/

namespace WhatwgTest.Svg.Length

open Whatwg.Svg.Value

/-- The text of a value. -/
def text (v : Length) : String := String.ofList (Length.grammar.print v)

/-- The value of a whole text. -/
def read (s : String) : Option Length := Length.grammar.read s.toList

/-- The text is a spelling of some value. -/
def check (s : String) : Bool := Length.grammar.check s.toList

/-! ## The sealed text's lengths -/

-- The two notes of `types.html`.
#guard read "10px" == some ⟨⟨10, 0⟩, .px⟩
#guard read "12%" == some ⟨⟨12, 0⟩, .percentage⟩ && read "12em" == some ⟨⟨12, 0⟩, .em⟩

-- `ViewportSpace` of `coords.html`.
#guard read "100px" == some ⟨⟨100, 0⟩, .px⟩ && read "200px" == some ⟨⟨200, 0⟩, .px⟩

-- `EstablishingANewSVGViewport` of `coords.html`: the outer `svg` in inches, and the inner one
-- in percentages.
#guard read "4in" == some ⟨⟨4, 0⟩, .inch⟩ && read "3in" == some ⟨⟨3, 0⟩, .inch⟩
#guard read "25%" == some ⟨⟨25, 0⟩, .percentage⟩ && read "50%" == some ⟨⟨50, 0⟩, .percentage⟩

-- The four examples of an intrinsic aspect ratio, under `SizingSVGInCSS` of `coords.html`.
#guard read "10cm" == some ⟨⟨10, 0⟩, .cm⟩ && read "5cm" == some ⟨⟨5, 0⟩, .cm⟩
#guard read "100%" == some ⟨⟨100, 0⟩, .percentage⟩ && read "75%" == some ⟨⟨75, 0⟩, .percentage⟩

/-! ## The one spelling of a value -/

-- One value of each of the ten kinds. The number is spelled as `Decimal.grammar` spells it, and
-- the mark follows in lower case with nothing between. A number with no unit has no mark.
#guard text ⟨⟨10, 0⟩, .number⟩ == "10"
#guard text ⟨⟨50, 0⟩, .percentage⟩ == "50%"
#guard text ⟨⟨15, -1⟩, .em⟩ == "1.5em"
#guard text ⟨⟨1, 0⟩, .ex⟩ == "1ex"
#guard text ⟨⟨15, 1⟩, .px⟩ == "15e1px"
#guard text ⟨⟨25, -1⟩, .cm⟩ == "2.5cm"
#guard text ⟨⟨5, -3⟩, .mm⟩ == "5e-3mm"
#guard text ⟨⟨-5, -1⟩, .inch⟩ == "-0.5in"
#guard text ⟨⟨12, 0⟩, .pt⟩ == "12pt"
#guard text ⟨⟨-3, 0⟩, .pc⟩ == "-3pc"

-- An exponent and then a mark that opens with `e`: the printer writes both letters `e`.
#guard text ⟨⟨1, 3⟩, .em⟩ == "1e3em" && text ⟨⟨1, 3⟩, .ex⟩ == "1e3ex"
#guard text ⟨⟨5, -3⟩, .em⟩ == "5e-3em"

-- A length in user units, from the two exact constructors of `Decimal`.
#guard text (.user (.ofInt (-40))) == "-40" && text (.user (.ofScaled 125 2)) == "1.25"

/-! ## What the reader takes -/

-- A number with no unit, and a mark after a number.
#guard read "10" == some ⟨⟨10, 0⟩, .number⟩
#guard read "1.5em" == some ⟨⟨15, -1⟩, .em⟩
#guard read "-0.5in" == some ⟨⟨-5, -1⟩, .inch⟩

-- A mark in either letter case, letter by letter: the resolution of the annotation in the
-- section `syntax` of `types.html`.
#guard read "1EM" == some ⟨⟨1, 0⟩, .em⟩ && read "1Em" == some ⟨⟨1, 0⟩, .em⟩
#guard read "1eM" == some ⟨⟨1, 0⟩, .em⟩ && read "3PC" == some ⟨⟨3, 0⟩, .pc⟩
#guard read "1E2PX" == some ⟨⟨1, 2⟩, .px⟩

-- Every spelling of the number: a sign of either kind, a bare fraction, an exponent with its
-- own sign.
#guard read "+.5e-2mm" == some ⟨⟨5, -3⟩, .mm⟩ && read "1e+3ex" == some ⟨⟨1, 3⟩, .ex⟩
#guard read ".5%" == some ⟨⟨5, -1⟩, .percentage⟩ && read "12pt" == some ⟨⟨12, 0⟩, .pt⟩

-- White space at both ends, of every kind of `wsp`.
#guard read " 10px " == some ⟨⟨10, 0⟩, .px⟩
#guard read "\t\n10px\r\x0c " == some ⟨⟨10, 0⟩, .px⟩

-- A reading keeps the digits it is given.
#guard read "1.50em" == some ⟨⟨150, -2⟩, .em⟩

/-! ## The letter `e` after a number

`e` opens an exponent or the marks `em` and `ex`. The next character decides. -/

-- One em.
#guard read "1em" == some ⟨⟨1, 0⟩, .em⟩

-- A thousand user units.
#guard read "1e3" == some ⟨⟨1, 3⟩, .number⟩

-- A thousand em.
#guard read "1e3em" == some ⟨⟨1, 3⟩, .em⟩

-- One ex.
#guard read "1ex" == some ⟨⟨1, 0⟩, .ex⟩

-- Control: an `e` with neither a digit nor `m` nor `x` after it. The reader takes `1` as a
-- number with no unit and leaves the `e`, so the whole text is refused.
#guard read "1e" == none
#guard Length.syn.read "1e".toList == some (⟨⟨1, 0⟩, .number⟩, ['e'])

-- Controls: a second exponent, a mark after a mark, and a sign with no digit.
#guard !check "1e3e3" && !check "1emm" && !check "1e3e" && !check "1e+em"

-- Control: the description that is not left-factored, `Decimal.syn` and then an optional `em`
-- or `ex`. Its reader takes `1em` and `1e3`, because the reader of a choice starts again where
-- the choice began. It fails the one-character test, so it is no value of `Grammar` and has no
-- retraction law. The description of the module passes that test.
#guard !(Syn.seq Decimal.syn (Syn.right (Length.letter 'e') Length.emOrEx).opt).ok
#guard (Syn.seq Decimal.syn (Syn.right (Length.letter 'e') Length.emOrEx).opt).read "1em".toList
  == some ((⟨1, 0⟩, some (.inl ())), [])
#guard (Syn.seq Decimal.syn (Syn.right (Length.letter 'e') Length.emOrEx).opt).read "1e3".toList
  == some ((⟨1, 3⟩, none), [])
#guard Length.syn.ok

/-! ## Where the grammar stops -/

-- White space between the number and the mark.
#guard !check "10 px" && !check "10 %" && !check "1e3 em"

-- A unit that the table of `SVGLength` does not name. `ch` is the example of the note under
-- `__svg__SVGLength__unitType`. The sealed text admits these by reference to CSS Values.
#guard !check "10rem" && !check "10ch" && !check "10vw"

-- `calc()`. The second text is the one of the note under
-- `__svg__SVGLength__valueInSpecifiedUnits`.
#guard !check "calc(1px)" && !check "calc(12px + 5%)"

-- A CSS escape and a CSS comment. The note after `attribute-css-value` of `types.html` says
-- that the second text parses as `10px`. This reader refuses both.
#guard !check "10\\px" && !check "10\\px/**/"

-- A mark with no number, the empty text and white space alone.
#guard !check "px" && !check "%" && !check "em" && !check "" && !check " "

-- Two lengths, and a length with something after it.
#guard !check "10px 20px" && !check "10px," && !check "1pxx"

-- Half a mark: each first letter alone.
#guard !check "1p" && !check "1c" && !check "1m" && !check "1i" && !check "1x"

-- The number format `10.` that the path chapter disallows, a digit outside ASCII, two signs,
-- and a keyword.
#guard !check "10." && !check "10.px" && !check "１px" && !check "--1px" && !check "auto"

-- Control: no range is checked. A negative length is a value here, whatever attribute holds
-- it.
#guard read "-10px" == some ⟨⟨-10, 0⟩, .px⟩

/-! ## The laws at this grammar -/

-- Reader of V1: every value reads back from its spelling. The value here is not a literal.
example (d : Decimal) (u : LengthUnit) :
    Length.grammar.read (Length.grammar.print ⟨d, u⟩) = some ⟨d, u⟩ :=
  Length.grammar.read_print _

-- Reader of V2 at a whole number of user units.
example (n : Int) : Length.grammar.check (Length.grammar.print (.user (.ofInt n))) = true :=
  Length.grammar.check_print _

-- Reader of the embedding: two lengths with one spelling are one length.
example (a b : Length) (h : Length.grammar.print a = Length.grammar.print b) : a = b :=
  Length.grammar.print_injective h

-- Reader of the embedding at two kinds: a number of user units and the same number of `px`
-- never have one spelling.
example (d : Decimal) : Length.grammar.print (.user d) ≠ Length.grammar.print ⟨d, .px⟩ :=
  fun h => nomatch Length.grammar.print_injective h

-- Control: the reader is no embedding. A mark in capitals, a plus sign and white space are
-- read and not printed, and the printer writes its own spelling back: the digits `15` at
-- exponent zero.
#guard read "1EM" == read "1em" && read " +10 " == read "10"
#guard (read " +1.5E1PX ").map text == some "15px"

-- Control: the value is the pair, not the length it denotes. A number keeps its digits, and no
-- unit is converted.
#guard read "1.50em" != read "1.5em" && read "1e3" != read "1000" && read "10" != read "10px"

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : Length.syn.erase.Matches "1e3em".toList :=
  Length.grammar.matches_of_check (by decide +kernel)

-- Reader of the print law at a value that is no literal.
example (n : Int) : Length.syn.erase.Matches (Length.grammar.print ⟨.ofInt n, .percentage⟩) :=
  Length.grammar.print_matches _

end WhatwgTest.Svg.Length
