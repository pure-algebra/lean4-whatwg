import Whatwg.Svg.Value.Lists
import Whatwg.Svg.Value.Grammar.Laws
import Whatwg.Svg.Value.Deterministic

/-!
# WhatwgTest.Svg.Lists

Readers, controls and finite evaluations of the two lists of a text's attributes (slice S8 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-41): `Whatwg/Svg/Value/Lists.lean`. The chapter is
`vendor/w3c-svgwg-47e645ef/master/text.html`, which writes no example of a list in the table
under `TSpanAttributes`: the texts here are the forms its prose names, "a comma- or
space-separated list".

A reader applies a law of `Grammar` at a real value. A control is a text the reader refuses,
or a place where a law stops.
-/

namespace WhatwgTest.Svg.Lists

open Whatwg.Svg.Value

/-- The value of a whole text, as a list of lengths. -/
def lengths (s : String) : Option LengthList := LengthList.grammar.read s.toList

/-- The value of a whole text, as a list of numbers. -/
def numbers (s : String) : Option NumberList := NumberList.grammar.read s.toList

/-! ## A list of lengths -/

-- One length is a list, and so is a numeral.
#guard lengths "10" == some 10 && lengths " 10 " == some (.single 10)

-- A comma, white space or both between two lengths, and each length with its own mark.
#guard lengths "10, 20px 3.5em,4%" ==
  some ⟨10, [⟨⟨20, 0⟩, .px⟩, ⟨⟨35, -1⟩, .em⟩, ⟨⟨4, 0⟩, .percentage⟩]⟩

-- The printer writes one space between two lengths.
#guard String.ofList (LengthList.grammar.print ⟨10, [⟨⟨35, -1⟩, .em⟩, ⟨⟨4, 0⟩, .percentage⟩]⟩) ==
  "10 3.5em 4%"

-- Controls: no length, a comma with nothing after it, and a unit that the table does not
-- name.
#guard lengths "" == none && lengths "10," == none && lengths "10rem" == none

-- Where a length cannot continue into the next, no separator is two lengths.
#guard lengths "10px20" == some ⟨⟨⟨10, 0⟩, .px⟩, [20]⟩

-- Reader of V1: every list reads back from its text, whatever its lengths are.
example (l : LengthList) : LengthList.grammar.read (LengthList.grammar.print l) = some l :=
  LengthList.grammar.read_print l

-- Reader of the embedding: two places that are written alike are one place.
example (a b : Length)
    (h : LengthList.grammar.print (.single a) = LengthList.grammar.print (.single b)) : a = b :=
  congrArg LengthList.head (LengthList.grammar.print_injective h)

-- Reader of `toList_ne_nil` with V1: a text that reads holds a length.
example (l : LengthList) : l.toList ≠ [] := l.toList_ne_nil

/-! ## A list of numbers -/

-- The rotations of three characters, with a comma or a space between.
#guard numbers "0 45,90" == some ⟨0, [45, 90]⟩
#guard String.ofList (NumberList.grammar.print ⟨0, [45, -90]⟩) == "0 45 -90"

-- A point opens a number, so two numbers may stand with nothing between.
#guard numbers "-.5.5" == some ⟨⟨-5, -1⟩, [⟨5, -1⟩]⟩

-- Controls: two commas, and an exponent with no digit.
#guard numbers "0,,1" == none && numbers "1e" == none

-- Reader of V1 at a list that is a variable.
example (l : NumberList) : NumberList.grammar.read (NumberList.grammar.print l) = some l :=
  NumberList.grammar.read_print l

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : NumberList.syn.erase.Matches "0 45,90".toList :=
  NumberList.grammar.matches_of_check (by decide +kernel)

/-! ## The test of `Deterministic.lean` -/

-- Neither description passes it, as `<points>` does not: with no separator, a run of digits is
-- one item to the reader and may be two to a derivation of the expression.
#guard !LengthList.syn.deterministic && !NumberList.syn.deterministic

-- The item of a list of lengths does pass it, as the length does.
#guard Length.item.deterministic

end WhatwgTest.Svg.Lists
