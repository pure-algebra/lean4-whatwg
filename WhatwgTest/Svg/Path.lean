import Whatwg.Svg.Value.Path

/-!
# WhatwgTest.Svg.Path

Readers, controls and finite evaluations of the path data grammar (slice S4b of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Path.lean`. The authority is
`vendor/w3c-svgwg-47e645ef/master/paths.html`.

A reader applies a law of `Whatwg/Svg/Value/Grammar.lean` at `Path.grammar` or
`PathData.grammar` and a real value. A finite evaluation replays a path data string that the
chapter's prose writes out in full, under the id of the heading it stands under: it checks
that the string reads, and the text it prints back as. A control is a text the grammar
refuses, or a description that the premise `Syn.ok` refuses.

What this battery does not claim: that the reader accepts every text of the description's
expression. The last section holds a text the expression has and the reader refuses. The
replayed strings are finite evidence about those strings and no more.
-/

namespace WhatwgTest.Svg.Path

open Whatwg.Svg.Value

/-- A pair of whole numbers. -/
def pt (x y : Int) : Point := ⟨.ofInt x, .ofInt y⟩

/-- The text as a value of `d`. -/
def value (s : String) : Option PathData := PathData.grammar.read s.toList

/-- The text read as a value of `d` and printed. -/
def reprint (s : String) : Option (List Char) := (value s).map PathData.grammar.print

/-- A triangle: a moveto, a lineto with two pairs, and a closepath. -/
def triangle : Path :=
  .moveto false (pt 100 100) [] [.lineto false (pt 300 100) [pt 200 300], .closepath true]

/-! ## The one spelling, and the laws -/

-- The printer writes one spelling, and the reader takes many.
#guard Path.grammar.print triangle == "M100,100L300,100 200,300z".toList
#guard Path.grammar.read "M 100 100 L 300 100 200 300 z".toList == some triangle
#guard Path.grammar.read " M100,100\n\tL300,100,200,300z ".toList == some triangle

-- Reader of V1: the triangle's spelling reads back as the triangle.
example : Path.grammar.read (Path.grammar.print triangle) = some triangle :=
  Path.grammar.read_print triangle

-- Reader of V2, for every value of `d`.
example (v : PathData) : PathData.grammar.check (PathData.grammar.print v) = true :=
  PathData.grammar.check_print v

-- Reader of the embedding: no other path has the triangle's spelling.
example (v : Path) (h : Path.grammar.print v = Path.grammar.print triangle) : v = triangle :=
  Path.grammar.print_injective h

-- Reader of V3a: a text that passes the check is a text of the expression's language.
example : Path.grammar.syn.erase.Matches "M 100-200".toList :=
  Path.grammar.matches_of_check (by decide +kernel)

-- Reader of the print law at a value of `d`.
example : PathData.grammar.syn.erase.Matches (PathData.grammar.print (.path triangle)) :=
  PathData.grammar.print_matches _

-- Reader of V1 over `Syn`, with a text after the print: a printed command, then a closepath.
-- `z` continues no command, so commands are printed with nothing between them.
example (c : Command) :
    Command.syn.read (Command.syn.print c ++ ['z']) = some (c, ['z']) :=
  Syn.read_print Command.syn (by decide +kernel) c _ (Command.syn_total c) (fun ch t h => by
    cases h
    decide +kernel)

/-! ## The chapter's own strings -/

-- `PathDataGeneralInformation`: a text with spaces to spare, and its compact form. One value.
#guard reprint "M 100 100 L 200 200" == some "M100,100L200,200".toList
#guard reprint "M100 100L200 200" == some "M100,100L200,200".toList
#guard value "M 100 100 L 200 200" == value "M100 100L200 200"

-- `PathDataGeneralInformation`: a second `L`, and the text without it. Both read. They are two
-- values here: the value keeps the commands the text states.
#guard reprint "M 100 200 L 200 100 L -100 -200" == some "M100,200L200,100L-100,-200".toList
#guard reprint "M 100 200 L 200 100 -100 -200" == some "M100,200L200,100 -100,-200".toList
#guard value "M 100 200 L 200 100 L -100 -200" != value "M 100 200 L 200 100 -100 -200"

-- `PathDataGeneralInformation`: `13,000.56` is no number, and `13000.56` is one. Control: path
-- data cannot refuse the first. After `M` it is two coordinates.
#guard !Decimal.grammar.check "13,000.56".toList && Decimal.grammar.check "13000.56".toList
#guard reprint "M13,000.56" == some "M13,0.56".toList

-- `PathDataEllipticalArcCommands`: the path of the four arcs, one text for each pair of flags.
#guard reprint "M 125,75 a100,50 0 0,0 100,50" == some "M125,75a100,50 0 0,0 100,50".toList
#guard reprint "M 125,75 a100,50 0 0,1 100,50" == some "M125,75a100,50 0 0,1 100,50".toList
#guard reprint "M 125,75 a100,50 0 1,0 100,50" == some "M125,75a100,50 0 1,0 100,50".toList
#guard reprint "M 125,75 a100,50 0 1,1 100,50" == some "M125,75a100,50 0 1,1 100,50".toList
#guard value "M 125,75 a100,50 0 1,0 100,50" == some (.path (.moveto false (pt 125 75) []
  [.ellipticalArc true ⟨.ofNat 100, .ofNat 50, .ofNat 0, true, false, pt 100 50⟩ []]))

-- `PathDataBNF`: in `M 100-200` the first coordinate stops at the minus sign.
#guard value "M 100-200" == some (.path (.moveto false (pt 100 (-200)) [] []))
#guard reprint "M 100-200" == some "M100,-200".toList

-- `PathDataBNF`: in `M 0.6.5` the first coordinate stops at the second point.
#guard value "M 0.6.5" == some (.path (.moveto false ⟨.ofScaled 6 1, .ofScaled 5 1⟩ [] []))
#guard reprint "M 0.6.5" == some "M0.6,0.5".toList

-- `PathDataBNF`, control: a number with a point and no digit after it, `23.`, is refused.
#guard !Decimal.grammar.check "23.".toList && Decimal.grammar.check "23.0".toList
#guard value "M 23. 5" == none && (value "M 23.0 5").isSome

-- `PathDataBNF`: the path data string may be empty. White space alone is the same value.
#guard value "" == some (.path .empty) && value " \t\n" == some (.path .empty)
#guard reprint " \t\n" == some []

-- `TheDProperty`: the keyword. Controls: it is taken as the sealed text writes it.
#guard value "none" == some .none && reprint "none" == some "none".toList
#guard value " none" == none && value "none " == none && value "None" == none

-- `PathDataErrorHandling`, control: `M 10,10 L 20,20,30` has an odd coordinate, and the reader
-- refuses the whole text. The part the chapter says to draw reads.
#guard value "M 10,10 L 20,20,30" == none
#guard reprint "M 10,10 L 20,20" == some "M10,10L20,20".toList

-- `PathDataErrorHandling`, control: `L 20 20` is a segment and no path. It opens with no moveto.
#guard value "L 20 20" == none

/-! ## Every command -/

-- The ten commands in both cases, with every separator the grammar has.
#guard reprint ("M1,2 \n\t L3,4 Z m 5 6 H 1 2 3 v -1e3 +.5E-2 C1,2 3,4 5,6 7,8,9,10,11,12" ++
    " s1,2 3,4 Q1,2 3,4 t5,6 7,8 A1,2 3 0,1 4,5 6 7 8 1 0 9 10z") ==
  some ("M1,2L3,4Zm5,6H1 2 3v-1e3 5e-3C1,2 3,4 5,6 7,8 9,10 11,12" ++
    "s1,2 3,4Q1,2 3,4t5,6 7,8A1,2 3 0,1 4,5 6,7 8 1,0 9,10z").toList

/-! ## Controls -/

-- A path opens with a moveto.
#guard value "z" == none && value "Z M1,2" == none && value "H1" == none

-- A coordinate pair has two coordinates, and a command that takes arguments has one group.
#guard value "M 1 2 3" == none && value "M1,2 L3" == none && value "M1,2 H" == none

-- A comma stands between two arguments only.
#guard value "M1,2,L3,4" == none && value ",M1,2" == none && value "M,1,2" == none

-- A character of no production: a letter that is no command, and a no-break space.
#guard value "M1,2 X3,4" == none && value "M1,2 L3,4" == none

-- The flags of an arc are one character each, so they need no separator: `0150-25` is the
-- flags `0` and `1` and the pair `50`, `-25`.
#guard value "M0,0a1 1 0 0150-25" == some (.path (.moveto false (pt 0 0) []
  [.ellipticalArc true ⟨.ofNat 1, .ofNat 1, .ofNat 0, false, true, pt 50 (-25)⟩ []]))

-- Control: the rotation is the production `number`, which has no sign, so an arc with a
-- negative rotation is refused. The grammar of SVG 1.1 gave the rotation a sign.
#guard value "M0,0a1 1 -30 0 1 50-25" == none && (value "M0,0a1 1 30 0 1 50-25").isSome

-- Control: a radius has no sign either, though `ArcOutOfRangeParameters` speaks of one.
#guard value "M0,0a-1 1 30 0 1 50-25" == none

-- Control: a flag is `0` or `1`, and an arc ends with a pair.
#guard value "M0,0a1 1 30 2 1 50-25" == none && value "M0,0a1 1 30 0 1 50" == none

/-- Pairs with nothing printed between two. -/
def tight : Syn (Point × List Point) := Point.syn.sepBy1 wsps

-- Control: `ok` refuses this description, and its print does not read back. The second pair's
-- first digit continues the first pair's last number. So a space is printed between two pairs.
example : tight.ok = false := by decide +kernel
#guard tight.print (pt 1 2, [pt 3 4]) == "1,23,4".toList
#guard tight.readAll (tight.print (pt 1 2, [pt 3 4])) == none

/-- A moveto and the commands after it, with one space printed before each command. -/
def spaced : Syn ((Bool × (Point × List Point)) × List Command) :=
  .seq Drawto.moveto (.many (.right (.skip (.many (.one wspSet)) [' ']) Command.syn))

-- Control: `ok` refuses this description too, because a space after a command's arguments
-- could open one more argument group. Here the reader still reads the print back: it gives
-- the space up when no group follows. `ok` is the premise of the law and is stricter than the
-- reader, so the one spelling has nothing between two commands.
example : spaced.ok = false := by decide +kernel
#guard spaced.readAll (spaced.print ((false, (pt 1 2, [])), [.lineto false (pt 3 4) []])) ==
  some ((false, (pt 1 2, [])), [.lineto false (pt 3 4) []])

/-! ## The reader is not the whole language (V3b) -/

/-- One digit is a text of the expression of `coordinate`. -/
theorem digit_matches {c : Char} (h : digitSet.mem c = true) : Decimal.syn.erase.Matches [c] :=
  .seq (l₁ := []) (l₂ := [c]) (.altR .eps)
    (.seq (l₁ := [c]) (l₂ := [])
      (.altL (.seq (l₁ := [c]) (l₂ := []) (.seq (l₁ := [c]) (l₂ := []) (.set h) .starNil)
        (.altR .eps)))
      (.altR .eps))

-- The expression of `svg_path` has the text `M10`: `1` and `0` are two coordinates with an
-- empty `comma_wsp?` between them.
example : Path.grammar.syn.erase.Matches "M10".toList :=
  .seq (l₁ := []) (l₂ := ['M', '1', '0']) .starNil
    (.seq (l₁ := ['M', '1', '0']) (l₂ := [])
      (.altL (.seq (l₁ := ['M', '1', '0']) (l₂ := [])
        (.seq (l₁ := ['M']) (l₂ := ['1', '0']) (.set (by decide))
          (.seq (l₁ := []) (l₂ := ['1', '0']) .starNil
            (.seq (l₁ := ['1', '0']) (l₂ := [])
              (.seq (l₁ := ['1']) (l₂ := ['0']) (digit_matches (by decide))
                (.seq (l₁ := []) (l₂ := ['0']) (.altR .eps) (digit_matches (by decide))))
              .starNil)))
        .starNil))
      .starNil)

-- The reader takes the longest match, as the paragraph after the grammar under `PathDataBNF`
-- says a production does: the first coordinate is `10`, and no second one follows.
#guard !Path.grammar.check "M10".toList

end WhatwgTest.Svg.Path
