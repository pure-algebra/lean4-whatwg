import Whatwg.Svg.Value.ViewBox

/-!
# WhatwgTest.Svg.ViewBox

Readers, controls and finite evaluations of the `viewBox` grammar (slice S4b of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/ViewBox.lean`.

The first section replays every `viewBox` value that a sealed chapter writes out. The files are
under `vendor/w3c-svgwg-47e645ef/master/`:

- `coords.html` writes three: `0 0 1500 1000` in `ExampleViewBox`, `0 0 200 200` in three
  examples under `SizingSVGInCSS`, and `-50,-50,500,500` twice under `VectorEffectsExamples`.
- `struct.html` writes three: `0 0 100 100` three times under `Namespace`, and `0 0 820 430` and
  `0 0 10 6` in the figure under `UseShadowTree`.
- `shapes.html` writes none.

`ExamplePreserveAspectRatio` and `ExampleUnits` of `coords.html` give their sources as links to
files outside the seal, so their values are not here. Every other text is made for the battery.

A reader applies a law of `Grammar` at a real value. A control shows where the grammar or a law
stops.
-/

namespace WhatwgTest.Svg.ViewBox

open Whatwg.Svg.Value

/-- The text of a value. -/
def text (v : ViewBox) : String := String.ofList (ViewBox.grammar.print v)

/-- The value of a whole text. -/
def value (s : String) : Option ViewBox := ViewBox.grammar.read s.toList

/-- The text is a spelling of some value. -/
def check (s : String) : Bool := ViewBox.grammar.check s.toList

/-- A rectangle of whole numbers. A width is a natural number, so none is negative. -/
def box (x y : Int) (w h : Nat) : ViewBox := ⟨.ofInt x, .ofInt y, .ofNat w, .ofNat h⟩

/-! ## The chapters' values -/

-- `ExampleViewBox` of `coords.html`.
#guard value "0 0 1500 1000" == some (box 0 0 1500 1000)

-- The examples 2, 3 and 4 of an intrinsic aspect ratio, under `SizingSVGInCSS` of
-- `coords.html`.
#guard value "0 0 200 200" == some (box 0 0 200 200)

-- `VectorEffectsExamples` of `coords.html`, on the outer `svg` and on the nested one: commas
-- with no white space, and an origin below zero.
#guard value "-50,-50,500,500" == some (box (-50) (-50) 500 500)

-- `Namespace` of `struct.html`, and the diagram and its two markers under `UseShadowTree`.
#guard value "0 0 100 100" == some (box 0 0 100 100)
#guard value "0 0 820 430" == some (box 0 0 820 430) && value "0 0 10 6" == some (box 0 0 10 6)

/-! ## The one spelling of a value -/

-- One space between two numbers, as `TermReserialize` of `types.html` writes a rectangle.
-- Five of the chapters' six values are spelled so, and the sixth is not.
#guard text (box 0 0 1500 1000) == "0 0 1500 1000"
#guard text (box (-50) (-50) 500 500) == "-50 -50 500 500"

-- Each number is spelled as its type spells it. A width has no sign to print.
#guard text ⟨.ofScaled (-25) 1, ⟨0, 0⟩, ⟨15, -1⟩, ⟨2, 3⟩⟩ == "-2.5 0 1.5 2e3"

/-! ## What the reader takes -/

-- "Whitespace and/or a comma" between two numbers (the paragraph after the table of
-- `ViewBoxAttribute`): a comma, white space of every kind, and white space around one comma.
#guard value "0,0,1500,1000" == some (box 0 0 1500 1000)
#guard value "0\t0\n1500\r\x0c1000" == some (box 0 0 1500 1000)
#guard value "0 , 0 ,1500, 1000" == some (box 0 0 1500 1000)

-- White space at both ends of the value.
#guard value " \n0 0 1500 1000\t " == some (box 0 0 1500 1000)

-- A plus sign on any of the four. On a width it is read and not printed.
#guard value "+0 +0 +1500 +1000" == some (box 0 0 1500 1000)

-- A zero width and a zero height. The section says that they disable rendering, and does not
-- call them an error.
#guard value "0 0 0 0" == some (box 0 0 0 0)
#guard value "0 0 0.0 0e3" == some ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 3⟩⟩

-- Nothing is needed where a sign or a point parts two numbers.
#guard value "-50-50 500 500" == some (box (-50) (-50) 500 500)
#guard value "0 0 .5.5" == some ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨5, -1⟩, ⟨5, -1⟩⟩
#guard value "0 0 1+2" == some (box 0 0 1 2)

/-! ## Where the grammar stops -/

-- Three numbers, and five.
#guard !check "0 0 200" && !check "0 0 200 200 200"

-- A negative width and a negative height: the section's error. No value has either, so the
-- type has no text to print for one.
#guard !check "0 0 -200 200" && !check "0 0 200 -200" && !check "0 0 -1e-9 1"

-- `-0` is refused too, though zero is not negative. The next line is why: a reader that took
-- `-0` alone would stop inside `-0.5`, and this text of three numbers would read as four.
#guard !check "0 0 -0 10" && !check "0 0 10 -0"
#guard !check "0 0 -0.5"

-- A comma with no number after it, a comma first, and two commas between two numbers.
#guard !check "0 0 200 200," && !check ",0 0 200 200"
#guard !check "0 0,,200 200" && !check "0 0 , , 200 200"

-- A unit, a percentage, a keyword, and the number format `10.` that the path chapter
-- disallows.
#guard !check "0 0 10px 10px" && !check "0 0 100% 100%" && !check "none" && !check "0 0 10. 10"

-- The empty text and white space alone.
#guard !check "" && !check " \n"

-- A CSS comment, which the note after `attribute-css-value` of `types.html` allows in such a
-- value, and a space outside `wsp`.
#guard !check "0 0 10/**/10" && !check "0 0 10\u00a010"

/-! ## The laws at this grammar -/

-- Reader of V1: every value reads back from its spelling. The value here is not a literal.
example (x y : Int) (w h : Nat) :
    ViewBox.grammar.read (ViewBox.grammar.print (box x y w h)) = some (box x y w h) :=
  ViewBox.grammar.read_print _

-- Reader of V2 at any origin and any two extents.
example (x y : Decimal) (w h : Magnitude) :
    ViewBox.grammar.check (ViewBox.grammar.print ⟨x, y, w, h⟩) = true :=
  ViewBox.grammar.check_print _

-- Reader of the embedding: two rectangles with one spelling are one rectangle.
example (a b : ViewBox) (h : ViewBox.grammar.print a = ViewBox.grammar.print b) : a = b :=
  ViewBox.grammar.print_injective h

-- Control: the reader is no embedding. The chapter's spelling with commas and the printer's
-- with spaces are one value, and the printer writes its own back.
#guard value "-50,-50,500,500" == value "-50 -50 +500 500"
#guard (value "-50,-50,500,500").map text == some "-50 -50 500 500"

-- Control: a number keeps its digits, so two spellings of one rectangle may be two values.
#guard value "0 0 1.50 1" != value "0 0 1.5 1"

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : ViewBox.syn.erase.Matches "-50,-50,500,500".toList :=
  ViewBox.grammar.matches_of_check (by decide +kernel)

-- Reader of the print law at a value that is no literal.
example (w : Nat) : ViewBox.syn.erase.Matches (ViewBox.grammar.print (box 0 0 w w)) :=
  ViewBox.grammar.print_matches _

/-! ## A text of the language that the reader refuses

The other direction of V3a holds for a deterministic description (`Syn.read_complete`, node
V3c of the library), and this one is not: `comma_wsp?` stands between two numbers. The
language has `0 0 12` as four numbers: after the two zeros, the number `1`, no separator, and
the number `2`. The reader takes the longest number, as the paragraph after the path data
grammar asks, so it reads three numbers and refuses the text. -/

/-- One digit is a text of `number`: one digit, no fraction and no exponent. -/
theorem digit_number {c : Char} (h : digitSet.mem c = true) : Magnitude.syn.erase.Matches [c] :=
  .seq (l₁ := [c]) (l₂ := [])
    (.altL (.seq (l₁ := [c]) (l₂ := []) (.seq (l₁ := [c]) (l₂ := []) (.set h) .starNil)
      (.altR .eps)))
    (.altR .eps)

/-- One digit is a text of `coordinate`: no sign, and the digit. -/
theorem digit_coordinate {c : Char} (h : digitSet.mem c = true) :
    Decimal.syn.erase.Matches [c] :=
  .seq (l₁ := []) (l₂ := [c]) (.altR .eps) (digit_number h)

/-- One digit is a text of an extent: no plus sign, and the digit. -/
theorem digit_extent {c : Char} (h : digitSet.mem c = true) :
    ViewBox.extent.erase.Matches [c] :=
  .seq (l₁ := []) (l₂ := [c]) (.altR .eps) (digit_number h)

/-- One space is a text of `comma_wsp?`: white space, and no comma. -/
theorem space_separator : spaceSep.erase.Matches [' '] :=
  .altL (.altL (.seq (l₁ := [' ']) (l₂ := [])
    (.seq (l₁ := [' ']) (l₂ := []) (.set (by decide)) .starNil) (.altR .eps)))

example : ViewBox.syn.erase.Matches ['0', ' ', '0', ' ', '1', '2'] :=
  .seq (l₁ := []) (l₂ := ['0', ' ', '0', ' ', '1', '2']) .starNil
    (.seq (l₁ := ['0']) (l₂ := [' ', '0', ' ', '1', '2']) (digit_coordinate (by decide))
      (.seq (l₁ := [' ', '0']) (l₂ := [' ', '1', '2'])
        (.seq (l₁ := [' ']) (l₂ := ['0']) space_separator (digit_coordinate (by decide)))
        (.seq (l₁ := [' ', '1']) (l₂ := ['2'])
          (.seq (l₁ := [' ']) (l₂ := ['1']) space_separator (digit_extent (by decide)))
          (.seq (l₁ := ['2']) (l₂ := [])
            (.seq (l₁ := []) (l₂ := ['2']) (.altR .eps) (digit_extent (by decide)))
            .starNil))))

#guard !check "0 0 12"

end WhatwgTest.Svg.ViewBox
