import Whatwg.Svg.Value.Points

/-!
# WhatwgTest.Svg.Points

Readers, controls and finite evaluations of the `points` grammar (slice S4b of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Points.lean`.

The sealed chapters write no `points` value. `vendor/w3c-svgwg-47e645ef/master/shapes.html`
gives its two examples, `ExamplePolyline01` and `ExamplePolygon01`, as links to files outside
the seal, and no other sealed file writes the attribute. So the two values here are the
coordinate pairs of two paths that the sealed text does write, taken back through the chapter's
own mapping of a shape to a path (`PolylineElement`, `PolygonElement`): a move to the first
pair, a line to each pair after it, and for a polygon a closed path. Every other text is made
for the battery.

A reader applies a law of `Grammar` at a real value. A control shows where the grammar or a law
stops.
-/

namespace WhatwgTest.Svg.Points

open Whatwg.Svg.Value

/-- The text of a value. -/
def text (p : Points) : String := String.ofList (Points.grammar.print p)

/-- The value of a whole text. -/
def value (s : String) : Option Points := Points.grammar.read s.toList

/-- The text is a spelling of some value. -/
def check (s : String) : Bool := Points.grammar.check s.toList

/-- A pair of whole numbers. -/
def pair (x y : Int) : Point := ⟨.ofInt x, .ofInt y⟩

/-- The polyline of the path `M 100 200 L 200 100 -100 -200`, which the path chapter writes
under `PathDataGeneralInformation` of `master/paths.html`. -/
def zigzag : Points := ⟨pair 100 200, [pair 200 100, pair (-100) (-200)]⟩

/-- The polygon of the path `M 750,100 L 250,900 L 1250,900 z`, the red triangle of
`ExampleViewBox` in `master/coords.html`. -/
def triangle : Points := ⟨pair 750 100, [pair 250 900, pair 1250 900]⟩

/-! ## The two shapes -/

-- The pairs of each path, spelled as the path spells them: white space alone in the first,
-- a comma inside a pair and a space between two pairs in the second.
#guard value "100 200 200 100 -100 -200" == some zigzag
#guard value "750,100 250,900 1250,900" == some triangle

-- The printer's one spelling is the second: the spelling of a list of points under
-- `TermReserialize` of `master/types.html`.
#guard text triangle == "750,100 250,900 1250,900"
#guard text zigzag == "100,200 200,100 -100,-200"

-- One pair is a value, and a number is spelled as `Decimal` spells it.
#guard text ⟨⟨.ofScaled (-25) 1, ⟨3, 2⟩⟩, []⟩ == "-2.5,3e2"

/-! ## What the reader takes -/

-- A comma parts two groups and carries no value: the same six numbers with a comma between
-- two pairs, with a comma after every number, and with none.
#guard value "750 100,250 900,1250 900" == some triangle
#guard value "750,100,250,900,1250,900" == some triangle
#guard value "750 100 250 900 1250 900" == some triangle

-- White space of every kind on either side of a comma, and at both ends of the value.
#guard value "750 , 100\n250\t,900 ,\r\n1250 \x0c 900" == some triangle
#guard value " \n750,100 250,900 1250,900\t " == some triangle

-- Nothing is needed where a sign or a point parts two numbers.
#guard value "100 200 200 100-100-200" == some zigzag
#guard value ".5.5+1e2-1E-2" == some ⟨⟨⟨5, -1⟩, ⟨5, -1⟩⟩, [⟨⟨1, 2⟩, ⟨-1, -2⟩⟩]⟩

/-! ## Where the grammar stops -/

-- An odd count of coordinates: the element is in error (the paragraph after
-- `DataTypePoints`).
#guard !check "750,100 250,900 1250" && !check "5"

-- The reader stops before the odd coordinate and hands it back. The user agent of that
-- paragraph drops the coordinate and renders these pairs. This module reads no prefix as a
-- value, so the line is an evaluation and no claim of recovery.
#guard Points.syn.read "750,100 250,900 1250".toList
  == some (⟨pair 750 100, [pair 250 900]⟩, "1250".toList)

-- The empty text and white space alone: `+` and `#` each ask for one item or more.
#guard !check "" && !check " \n\t"

-- A comma with no number after it, a comma first, and two commas between two numbers.
#guard !check "750,100 250,900," && !check ",750,100" && !check "750,,100" && !check "750 , , 100"

-- A unit, a percentage, a keyword, and the number format `1.` that the path chapter disallows.
#guard !check "10px 20px" && !check "10% 20%" && !check "none" && !check "1. 2"

-- A CSS comment, which the note after `attribute-css-value` of `master/types.html` allows in
-- such a value, and a space outside `wsp`.
#guard !check "750,100/**/250,900" && !check "750 100"

/-! ## The laws at this grammar -/

-- Reader of V1: every value reads back from its spelling. The value here is not a literal.
example (p : Point) (ps : List Point) :
    Points.grammar.read (Points.grammar.print ⟨p, ps⟩) = some ⟨p, ps⟩ :=
  Points.grammar.read_print _

-- Reader of V2 at a shape with one more pair in front.
example (p : Point) : Points.grammar.check (Points.grammar.print ⟨p, triangle.toList⟩) = true :=
  Points.grammar.check_print _

-- Reader of the embedding: two shapes with one spelling are one shape.
example (a b : Points) (h : Points.grammar.print a = Points.grammar.print b) : a = b :=
  Points.grammar.print_injective h

-- Control: the reader is no embedding. Four spellings read as one value, and the printer
-- writes one of them back.
#guard value "0 0 1 1" == value "0,0,1,1" && value "+0,0 1,1" == value "0 0 1 1"
#guard (value " 750 100,250 900,\n1250 900 ").map text == some "750,100 250,900 1250,900"

-- Control: a number keeps its digits, so two spellings of one shape may be two values.
#guard value "1.50,2" != value "1.5,2"

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : Points.syn.erase.Matches "750,100 250,900 1250,900".toList :=
  Points.grammar.matches_of_check (by decide +kernel)

-- Reader of the print law at a value that is no literal.
example (p : Point) : Points.syn.erase.Matches (Points.grammar.print ⟨p, []⟩) :=
  Points.grammar.print_matches _

/-! ## A text of the language that the reader refuses

The other direction of V3a is open (node V3b of the library). The language has `12` as a pair:
the number `1`, no separator, and the number `2`. The reader takes the longest number, as the
paragraph after the path data grammar asks, so it reads one coordinate and refuses the text. -/

/-- One digit is a text of `coordinate`: no sign, one digit, no fraction and no exponent. -/
theorem digit_matches {c : Char} (h : digitSet.mem c = true) : Decimal.syn.erase.Matches [c] :=
  .seq (l₁ := []) (l₂ := [c]) (.altR .eps)
    (.seq (l₁ := [c]) (l₂ := [])
      (.altL (.seq (l₁ := [c]) (l₂ := []) (.seq (l₁ := [c]) (l₂ := []) (.set h) .starNil)
        (.altR .eps)))
      (.altR .eps))

example : Points.syn.erase.Matches ['1', '2'] :=
  .seq (l₁ := []) (l₂ := ['1', '2']) .starNil
    (.seq (l₁ := ['1', '2']) (l₂ := [])
      (.seq (l₁ := ['1', '2']) (l₂ := [])
        (.seq (l₁ := ['1']) (l₂ := ['2']) (digit_matches (by decide))
          (.seq (l₁ := []) (l₂ := ['2']) (.altR .eps) (digit_matches (by decide))))
        .starNil)
      .starNil)

#guard !check "12"

end WhatwgTest.Svg.Points
