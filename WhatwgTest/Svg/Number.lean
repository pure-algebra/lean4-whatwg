import Whatwg.Svg.Value.Number
import Whatwg.Svg.Value.Cohort

/-!
# WhatwgTest.Svg.Number

Readers, controls and finite evaluations of the number of an SVG attribute value and of the
separators between numbers (slice S4b of `docs/SVG-PACKAGE-PLAN.md`):
`Whatwg/Svg/Value/Number.lean` and `Whatwg/Svg/Value/Cohort.lean`. The texts are those of the
chapter where it writes one: the
two paragraphs after the grammar under `PathDataBNF` of
`vendor/w3c-svgwg-47e645ef/master/paths.html` give `100-200`, `0.6.5` and `23.`.

A reader applies a law of `Grammar` at a real value. A control shows where a law stops: the
printer is an embedding, and the reader is not.
-/

namespace WhatwgTest.Svg.Number

open Whatwg.Svg.Value

/-- The text of a value. -/
def text (d : Decimal) : String := String.ofList (Decimal.grammar.print d)

/-- The value of a whole text. -/
def value (s : String) : Option Decimal := Decimal.grammar.read s.toList

/-! ## The one spelling of a value -/

-- Exponent zero is plain digits. A positive exponent is written as one. A negative exponent
-- is a point, with a zero before a bare fraction and the zeros the exponent asks for.
#guard text ⟨150, 0⟩ == "150" && text ⟨0, 0⟩ == "0" && text ⟨-7, 0⟩ == "-7"
#guard text ⟨15, 1⟩ == "15e1" && text ⟨-2, 30⟩ == "-2e30"
#guard text ⟨15, -1⟩ == "1.5" && text ⟨150, -2⟩ == "1.50" && text ⟨-25, -3⟩ == "-0.025"
#guard text ⟨0, -2⟩ == "0.00" && text ⟨-1234567, -3⟩ == "-1234.567"

-- Where the point would be longer than the exponent, the printer writes the exponent: `0.05`
-- and `5e-2` are as long, and `0.005` is longer than `5e-3`.
#guard text ⟨5, -2⟩ == "0.05" && text ⟨5, -3⟩ == "5e-3" && text ⟨-125, -9⟩ == "-125e-9"

-- So a print costs the length of its text, as a read does: no zero is written that an
-- exponent can say.
#guard text ⟨1, -999999999999⟩ == "1e-999999999999"

-- The two exact constructors.
#guard text (.ofInt (-40)) == "-40" && text (.ofScaled 125 2) == "1.25"

-- The unsigned number prints no sign, for there is none in the value.
#guard String.ofList (Magnitude.grammar.print ⟨25, -1⟩) == "2.5"

/-! ## What the reader takes -/

-- Every spelling of `coordinate`: a sign of either kind, a bare fraction, an exponent with
-- either mark and its own sign.
#guard value "+.5E-2" == some ⟨5, -3⟩ && value "-.5" == some ⟨-5, -1⟩
#guard value "1e3" == some ⟨1, 3⟩ && value "1.5e+3" == some ⟨15, 2⟩ && value "007" == some ⟨7, 0⟩

-- A reading keeps the digits it is given: the zero at the end of a fraction stays in the
-- mantissa.
#guard value "1.50" == some ⟨150, -2⟩

-- An exponent of any size costs the length of its text: nothing is raised to it.
#guard value "1e999999999999" == some ⟨1, 999999999999⟩

-- Control: `23.` is the number format the chapter disallows in SVG 2 (the advisement after
-- the grammar under `PathDataBNF`). The reader takes `23` and leaves the point.
#guard value "23." == none && Decimal.syn.read "23.".toList == some (⟨23, 0⟩, ['.'])

-- Controls: no digit, an exponent mark with no digit, a unit, a digit outside ASCII, two
-- signs, white space.
#guard value "." == none && value "" == none && value "-" == none
#guard value "1e" == none && value "10px" == none && value "１" == none
#guard value "--1" == none && value " 1" == none && value "1 " == none

-- Control: `number` has no sign, so the unsigned grammar refuses one.
#guard Magnitude.grammar.read "-1".toList == none && Magnitude.grammar.read "+1".toList == none

/-! ## Where one number ends

The chapter's two examples of the rule that a production consumes as much as it can
(`PathDataBNF`, the paragraphs after the grammar). -/

-- `100-200`: the first coordinate is `100`, and the minus sign starts the second.
#guard Decimal.syn.read "100-200".toList == some (⟨100, 0⟩, "-200".toList)

-- `0.6.5`: the first coordinate is `0.6`, and the second point starts `.5`.
#guard Decimal.syn.read "0.6.5".toList == some (⟨6, -1⟩, ".5".toList)

-- So a pair needs no separator where a sign or a point parts the two numbers.
#guard Point.grammar.read "100-200".toList == some ⟨⟨100, 0⟩, ⟨-200, 0⟩⟩
#guard Point.grammar.read "0.6.5".toList == some ⟨⟨6, -1⟩, ⟨5, -1⟩⟩
#guard String.ofList (Point.grammar.print ⟨⟨100, 0⟩, ⟨-200, 0⟩⟩) == "100,-200"

-- Control: two numbers of digits alone need one. `100200` is one number, not a pair.
#guard Point.grammar.read "100200".toList == none

/-! ## The separators -/

-- `comma_wsp` in each spelling: white space, a comma, and white space on either side of one
-- comma.
#guard commaWsp.read " x".toList == some ((), ['x']) && commaWsp.read ",x".toList == some ((), ['x'])
#guard commaWsp.read " \t\n\x0c\r,  x".toList == some ((), ['x'])

-- Controls: two commas are two separators, and `comma_wsp` is not optional.
#guard commaWsp.read ",,x".toList == some ((), [',', 'x']) && commaWsp.read "x".toList == none

-- `comma_wsp?` reads nothing where there is none. The two printers differ, and nothing else.
#guard spaceSep.read "x".toList == some ((), ['x'])
#guard spaceSep.print () == [' '] && commaSep.print () == [','] && wsps.print () == []

/-! ## The laws at this grammar -/

-- Reader of V1: every value reads back from its spelling. The value here is not a literal.
example (n : Int) (places : Nat) :
    Decimal.grammar.read (Decimal.grammar.print (.ofScaled n places)) = some (.ofScaled n places) :=
  Decimal.grammar.read_print _

-- Reader of the embedding: two values with one spelling are one value.
example (a b : Decimal) (h : Decimal.grammar.print a = Decimal.grammar.print b) : a = b :=
  Decimal.grammar.print_injective h

-- Control: the reader is no embedding. `+5`, `5` and `05` are one value.
#guard value "+5" == value "5" && value "05" == value "5"

-- Control: the value is the pair, not the number it denotes. One hundred and fifty is two
-- values, and the reader tells them apart.
#guard value "150" != value "15e1" && value "1.5" != value "1.50"

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : Decimal.syn.erase.Matches "-1.5e-3".toList :=
  Decimal.grammar.matches_of_check (by decide +kernel)

/-! ## The canonical value -/

-- The values of one number have one canonical value: no zero at the end of the mantissa.
#guard Decimal.reduce ⟨150, -2⟩ == ⟨15, -1⟩ && Decimal.reduce ⟨1500, 0⟩ == ⟨15, 2⟩
#guard Decimal.reduce ⟨0, -3⟩ == ⟨0, 0⟩ && Decimal.reduce ⟨-1200, -2⟩ == ⟨-12, 0⟩

-- So `reduce` tells that two texts denote one number, at the cost of their digits.
#guard (value "150").map Decimal.reduce == (value "15e1").map Decimal.reduce
#guard (value "1.50").map Decimal.reduce == (value "1.5").map Decimal.reduce
#guard (value "1e999999999999").map Decimal.reduce == (value "10e999999999998").map Decimal.reduce

-- Reader of the two laws of the invariant together: the canonical value is a fixed point.
example (d : Decimal) : d.reduce.reduce = d.reduce :=
  Decimal.reduce_of_isReduced (Decimal.isReduced_reduce d)

-- Reader of the arithmetic law: the canonical value denotes the number of the value.
example : (Decimal.reduce ⟨1500, -1⟩).Same ⟨1500, -1⟩ := Decimal.same_reduce _

-- Reader of the cohort law (`Whatwg/Svg/Value/Cohort.lean`): two values denote one number
-- exactly when they have one canonical value.
example (a b : Decimal) (h : a.Same b) : a.reduce = b.reduce := (Decimal.same_iff_reduce a b).mp h

-- So the relation is decided by `reduce`, and the evaluation takes no power of ten: the two
-- values here differ by a billion in the exponent.
example : Decimal.Same ⟨1, 1000000000⟩ ⟨10, 999999999⟩ := by decide
example : ¬ Decimal.Same ⟨150, 0⟩ ⟨15, 2⟩ := by decide

-- The canonical value of an integer that ends in zeros is spelled with an exponent. `tidy`
-- writes it plain where that is no longer: one zero or two.
#guard text (Decimal.reduce ⟨150, 0⟩) == "15e1" && text (Decimal.tidy ⟨150, 0⟩) == "150"
#guard text (Decimal.tidy ⟨1500, -1⟩) == "150" && text (Decimal.tidy ⟨150, -2⟩) == "1.5"
#guard text (Decimal.tidy ⟨15000, 0⟩) == "15e3" && text (Decimal.tidy ⟨20, -1⟩) == "2"

-- Control: a text is read as it is written. The reader returns no canonical value.
#guard value "1.50" != (value "1.50").map Decimal.reduce

end WhatwgTest.Svg.Number
