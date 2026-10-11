import Whatwg.Svg.Value.Refusal
import Whatwg.Svg.Value.Path

/-!
# WhatwgTest.Svg.Refusal

Readers, controls and finite evaluations of the located refusal of a value
(`Whatwg/Svg/Value/Refusal.lean`; node V6 of `docs/SVG-PACKAGE-PLAN.md`, section 6).

A finite evaluation gives a text to `explain` at a real grammar and states the offset it
answers. Offsets count characters from zero, and the length of a text is the offset of its
end. A control is a small description on which the reach and the reader's stopping place
differ, or on which a part refuses and the text is still read in full. A reader applies a law
of the module at a real grammar.

What this battery does not claim: that an offset is where an author's mistake is, or that a
text which shares a refused text's prefix is refused. The offsets are finite evidence about
these texts and no more.
-/

namespace WhatwgTest.Svg.Refusal

open Whatwg.Svg.Value

/-! ## Path data -/

-- A lineto with one coordinate is refused at the end of the text. The pair wants a second
-- coordinate, and the text has twelve characters.
#guard PathData.grammar.explain "M 10 20 L 40".toList == some 12

-- The offset is the furthest position of the reading, not the place where the reader
-- stopped. The repetition of commands gives up the lineto, and the reader stops at `L`,
-- offset 8. The refusal names `x`, offset 13, where the lineto could not go on.
#guard (PathData.syn.read "M 10 20 L 40 x".toList).map (·.2) == some "L 40 x".toList
#guard PathData.grammar.explain "M 10 20 L 40 x".toList == some 13

-- A character that opens no command, a path with no moveto, and a keyword cut short.
#guard PathData.grammar.explain "M 10 20 x".toList == some 8
#guard PathData.grammar.explain "L 1 2".toList == some 0
#guard PathData.grammar.explain "nope".toList == some 2

-- The rotation of an arc has no sign: the refusal names the `-`.
#guard PathData.grammar.explain "M 10 20 A 5 5 -30 0 1 9 9".toList == some 14

-- The reader takes `10` as one coordinate, so `M10` is refused at its end.
#guard PathData.grammar.explain "M10".toList == some 3

-- A spelling of a value has no refusal: a path, the keyword, and the empty path.
#guard PathData.grammar.explain "M 10 20 L 40 50".toList == none
#guard PathData.grammar.explain "none".toList == none
#guard PathData.grammar.explain "".toList == none

/-! ## A number -/

-- An exponent with no digit, and a point with no digit, are refused at the end of the text.
#guard Decimal.grammar.explain "1e".toList == some 2
#guard Decimal.grammar.explain "23.".toList == some 3

-- A second point, at the point.
#guard Decimal.grammar.explain "1.5.5".toList == some 3

-- No number opens with a letter. The empty text is refused at offset 0, which is its end.
#guard Decimal.grammar.explain "abc".toList == some 0
#guard Decimal.grammar.explain "".toList == some 0

-- A spelling of a number has no refusal.
#guard Decimal.grammar.explain "-1.5e3".toList == none

/-! ## The reach and the stopping place -/

/-- The digits. -/
def digits : CharSet := .ofList "0123456789".toList

/-- Two letters. -/
def letters : CharSet := .ofList "ab".toList

/-- A letter and then a digit, any number of times. -/
def pairs : Syn (List (Char × Char)) := .many (.seq (.one letters) (.one digits))

/-- A letter and a digit, or else a letter alone. -/
def pairOrLetter : Syn ((Char × Char) ⊕ Char) :=
  .alt (.seq (.one letters) (.one digits)) (.one letters)

-- Control: the reader's stopping place is not the offset. On `a1b2ax` the repetition gives up
-- its third pair and hands the text back from offset 4. The refusal names offset 5, where
-- that pair wanted a digit. So `Syn.le_explain_of_read` is an inequality and no equation.
#guard pairs.read "a1b2ax".toList == some ([('a', '1'), ('b', '2')], "ax".toList)
#guard pairs.explain "a1b2ax".toList == some 5

-- The two agree where the next character opens no pair.
#guard pairs.read "a1b2x".toList == some ([('a', '1'), ('b', '2')], "x".toList)
#guard pairs.explain "a1b2x".toList == some 4

-- A pair cut short by the end of the text: the offset is the length of the text.
#guard pairs.explain "a1b2a".toList == some 5

-- Control: a part that refuses is no refusal of the text. On `a` the first alternative wants
-- a digit at the end, so the reach is zero. The second alternative reads the text in full,
-- and there is no offset to name. `explain` asks the answer before it asks the reach.
#guard (pairOrLetter.run "a".toList).1 == 0 && pairOrLetter.explain "a".toList == none

/-! ## The laws at a grammar -/

-- Reader of the refusal law at the grammar of `d`: a text with no refusal passes the check.
example : PathData.grammar.check "M 10 20 L 40 50".toList = true :=
  (PathData.grammar.explain_eq_none_iff _).mp (by decide +kernel)

-- Reader of the same law in the other direction, for every text: a text with an offset fails
-- the check.
example (s : List Char) (n : Nat) (h : PathData.grammar.explain s = some n) :
    PathData.grammar.check s = false := by
  cases hc : PathData.grammar.check s with
  | false => rfl
  | true =>
    rw [(PathData.grammar.explain_eq_none_iff s).mpr hc] at h
    exact nomatch h

-- Reader of the print law: no value of `d` prints a refused text.
example (v : PathData) : PathData.grammar.explain (PathData.grammar.print v) = none :=
  PathData.grammar.explain_print v

-- Reader of the bound at a number: an offset is a position of the text.
example (s : List Char) (n : Nat) (h : Decimal.grammar.explain s = some n) : n ≤ s.length :=
  Decimal.grammar.explain_le h

-- Reader of the stopping-place law at path data: the offset is no earlier than the place
-- where the reader stopped.
example (s r : List Char) (v : PathData) (n : Nat) (hread : PathData.syn.read s = some (v, r))
    (h : PathData.grammar.explain s = some n) : s.length - r.length ≤ n :=
  Syn.le_explain_of_read PathData.syn hread h

end WhatwgTest.Svg.Refusal
