import Whatwg.Svg.Value.Grammar.Laws

/-!
# WhatwgTest.Svg.Grammar

Readers, controls and finite evaluations of the value-grammar library (slice S4a of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Grammar.lean`. The grammars here are small and
made for the battery: digits, a separator read in many spellings, a list.

A reader applies the retraction, the soundness of the reader or the print law at a real
description. A control is a description that the decidable check refuses, beside the text on
which its reader and its printer disagree: it shows why the premise `ok` stands.

What this battery does not claim: that the reader accepts every text of a description's
language. The last section holds a text that the language has and the reader refuses.
-/

namespace WhatwgTest.Svg.Grammar

open Whatwg.Svg.Value

def digits : CharSet := .ofList "0123456789".toList
def spaces : CharSet := .ofList [' ', '\t', '\n']
def letters : CharSet := .ofList "ab".toList

/-- One digit or more. -/
def number : Syn (Char × List Char) := .seq (.one digits) (.many (.one digits))

/-- White space in any amount, printed as one space. -/
def gap : Syn Unit := .skip (.many (.one spaces)) [' ']

/-- Numbers, each followed by a gap. -/
def numbers : Syn (List ((Char × List Char) × Unit)) := .many (.seq number gap)

/-- A number or a letter: a choice that one character decides. -/
def atom : Syn ((Char × List Char) ⊕ Char) := .alt number (.one letters)

/-- The value `12 3`. -/
def twelveThree : List ((Char × List Char) × Unit) := [(('1', ['2']), ()), (('3', []), ())]

/-! ## Sets of characters -/

#guard digits.mem '7' && !digits.mem 'a' && !digits.mem ' '

-- Control: a character outside ASCII is in no set, though its code point repeats modulo no
-- mask.
#guard !digits.mem 'é' && !(CharSet.single 'é').mem 'é'
#guard digits.disjoint spaces && !digits.disjoint (.ofList ['9', 'x'])

/-! ## Reading and printing -/

-- The printer writes one spelling, and the reader takes many.
#guard numbers.print twelveThree == "12 3 ".toList
#guard numbers.read "12 3 ".toList == some (twelveThree, [])
#guard numbers.read "12\t\n 3".toList == some (twelveThree, [])

-- The reader stops at the first character that continues nothing, and hands the rest back.
#guard numbers.read "12 3 x9".toList == some (twelveThree, "x9".toList)

-- A whole text: the check refuses a text with a tail.
#guard numbers.check "12 3".toList && !numbers.check "12 3 x".toList
#guard atom.readAll "a".toList == some (.inr 'a') && atom.readAll "40".toList == some (.inl ('4', ['0']))

-- Controls: a value that is not printable, and the empty list, which is.
#guard !number.valid ('x', []) && numbers.valid [] && numbers.print [] == []

/-! ## The retraction (V1 and V2) -/

-- The premise is one evaluation.
example : numbers.ok = true := by decide
example : atom.ok = true := by decide

-- Reader of V1: a printed value reads back, with the text after it.
example : numbers.read (numbers.print twelveThree ++ "x".toList) = some (twelveThree, "x".toList) :=
  Syn.read_print numbers (by decide) twelveThree _ (by decide) (fun c t h => by
    cases h
    decide)

-- Reader of V1 at the end of the text, for every printable value.
example (v : List ((Char × List Char) × Unit)) (hv : numbers.valid v = true) :
    numbers.readAll (numbers.print v) = some v :=
  Syn.readAll_print numbers (by decide) v hv

-- Reader of V2.
example : atom.check (atom.print (.inl ('7', []))) = true :=
  Syn.check_print atom (by decide) _ (by decide)

/-- A description that the check refuses: digits, then one more digit. After the repeated
part, the next character continues it. -/
def greedy : Syn (List Char × Char) := .seq (.many (.one digits)) (.one digits)

-- Control: `ok` is false, and the retraction fails on a printable value. The repetition
-- takes the last digit, and nothing is left for the part after it.
example : greedy.ok = false := by decide
#guard greedy.valid (['1'], '2') && greedy.read (greedy.print (['1'], '2')) == none

/-- A choice that its first character does not decide: two alternatives open alike. -/
def ambiguous : Syn ((Char × Char) ⊕ Char) :=
  .alt (.seq (.one letters) (.one digits)) (.one letters)

-- Control: `ok` is false. The second alternative's print opens as the first one reads. Here
-- the reader still answers, because the first alternative fails and the second is tried.
example : ambiguous.ok = false := by decide
#guard ambiguous.readAll "a".toList == some (.inr 'a')

/-! ## The expression (V3a) -/

-- Reader of V3a: a text that passes the check is a text of the expression's language.
example : numbers.erase.Matches "12 3".toList := Syn.matches_of_check numbers (by decide)

-- Reader of the print law: a printed value is a text of that language.
example : numbers.erase.Matches (numbers.print twelveThree) :=
  Syn.print_matches numbers twelveThree (by decide)

-- The other direction needs a premise that `ok` is not (V3c: `Syn.deterministic`, whose
-- battery is `WhatwgTest/Svg/Deterministic.lean`). The language of `greedy` has the text
-- `12`: one digit for the star, one for the part after it. The reader commits to the longest
-- match and refuses it.
example : greedy.erase.Matches "12".toList :=
  .seq (l₁ := ['1']) (l₂ := ['2']) (.starCons (l₁ := ['1']) (l₂ := []) (.set (by decide)) .starNil)
    (.set (by decide))

#guard !greedy.check "12".toList

end WhatwgTest.Svg.Grammar
