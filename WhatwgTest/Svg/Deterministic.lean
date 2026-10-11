import Whatwg.Svg.Value.Deterministic
import Whatwg.Svg.Value.Attribute

/-!
# WhatwgTest.Svg.Deterministic

Readers and controls of the completeness of the reader for a deterministic description (node
V3c of `docs/SVG-PACKAGE-PLAN.md`, section 6): `Whatwg/Svg/Value/Deterministic.lean`.

A reader applies the check law, the completeness or the head law at the number of
`Whatwg/Svg/Value/Number.lean`, whose two descriptions are deterministic. A control is a
description that fails one clause of `Syn.deterministic`, beside a text of its language that
its reader refuses: it shows why the clause stands. The descriptions of the controls are small
and made for the battery. The texts of the number are those of the paragraphs after the
grammar under `PathDataBNF` of `vendor/w3c-svgwg-47e645ef/master/paths.html`: `100-200`,
`0.6.5` and `23.`.

What this battery does not claim: that a description which fails `Syn.deterministic` refuses a
text of its language. The last section holds one that fails the test and reads its language.
-/

namespace WhatwgTest.Svg.Deterministic

open Whatwg.Svg.Value

/-! ## The number is deterministic -/

-- Readers of the check law at `number` and at `coordinate`: the premise is one evaluation, and
-- the check then decides the language of the expression.
example (s : List Char) :
    Magnitude.grammar.check s = true ↔ Magnitude.grammar.syn.erase.Matches s :=
  Magnitude.grammar.check_iff_matches (by decide +kernel) s

example (s : List Char) : Decimal.grammar.check s = true ↔ Decimal.grammar.syn.erase.Matches s :=
  Decimal.grammar.check_iff_matches (by decide +kernel) s

-- Reader of the check law from the reader to the language: a refusal by the reader proves
-- that the language has no such text. `23.` is the number format that the advisement under
-- `PathDataBNF` disallows.
example : ¬ Decimal.syn.erase.Matches ['2', '3', '.'] := fun h =>
  absurd ((Decimal.grammar.check_iff_matches (by decide +kernel) _).mpr h) (by decide +kernel)

-- Reader of V3c at the chapter's first example, `100-200`: a minus sign cannot continue a
-- coordinate, so every coordinate is read whole before one, whatever follows it.
example (pre t : List Char) (h : Decimal.syn.erase.Matches pre) :
    ∃ v, Decimal.syn.read (pre ++ '-' :: t) = some (v, '-' :: t) :=
  Syn.read_complete Decimal.syn (by decide +kernel) pre ('-' :: t) h (fun c _ hc => by
    cases hc
    decide +kernel)

-- Control of the premise on the text after: a digit may continue a coordinate. `1` is a text
-- of the language, and before `2` the reader takes both digits.
#guard Decimal.syn.readContinues.mem '2' && (Decimal.syn.read ['1', '2']).map (·.2) == some []

-- Where the law stops: the premise is one set of characters for the whole description. A
-- point may continue `0` and cannot continue `0.6`, and the set holds it for both. So the law
-- is silent on `0.6` before `.5`, the chapter's second example, where the reader stops.
#guard Decimal.syn.readContinues.mem '.' &&
  (Decimal.syn.read "0.6.5".toList).map (·.2) == some ".5".toList

-- Readers of the head law: the language of `coordinate` has no empty text, and no text of it
-- opens with a letter.
example : ¬ Decimal.syn.erase.Matches [] := fun h =>
  absurd ((Syn.matches_head Decimal.syn [] h).1 rfl) (by decide +kernel)

example (t : List Char) : ¬ Decimal.syn.erase.Matches ('x' :: t) := fun h =>
  absurd ((Syn.matches_head Decimal.syn _ h).2 'x' t rfl) (by decide +kernel)

/-! ## Which grammar is deterministic

One evaluation for each grammar of the package. This is the table that node V3c of the plan
cites. -/

-- The number, the coordinate and the length: one character decides every choice of the reader.
#guard Magnitude.syn.deterministic && Decimal.syn.deterministic && Length.syn.deterministic

-- Reader of the check law at the length. Its description is left-factored at the `e` that
-- opens an exponent or a unit, so the check decides the language of `sign? number mark?`.
example (s : List Char) : Length.grammar.check s = true ↔ Length.syn.erase.Matches s :=
  Length.grammar.check_iff_matches (by decide +kernel) s

-- Reader of the bridge at the coordinate: the rule reads a text whole exactly when the text is
-- of the expression's language.
example (s : List Char) :
    (∃ v, Greedy Decimal.syn s (some (v, []))) ↔ Decimal.syn.erase.Matches s :=
  Syn.greedy_iff_matches Decimal.syn (by decide +kernel) s

-- Controls: every description that reads `comma_wsp?` between two numbers fails the test, by
-- design. Each grammar's own battery holds a text of its expression that its reader refuses.
#guard !Point.syn.deterministic && !Points.syn.deterministic && !ViewBox.syn.deterministic
#guard !Path.syn.deterministic && !PathData.syn.deterministic
#guard !Transform.syn.deterministic && !TransformList.syn.deterministic

/-! ## The premise `ok` does not give the completeness -/

-- Control at a grammar of the package: the coordinate pair passes `ok`, as every `Grammar`
-- does, and fails `deterministic`. Its two parts pass: the pair fails where a digit may
-- continue the first coordinate and open the second.
example : Point.syn.deterministic = false := by decide +kernel
#guard Decimal.syn.deterministic && (Syn.right commaSep Decimal.syn).deterministic

/-- Two naturals with an optional separator between them: the shape of a coordinate pair. -/
def pair : Syn (Nat × Unit × Nat) := .seq natural (.seq spaceSep natural)

-- Control of the sequence clause: the description passes `ok` and its two parts pass
-- `deterministic`. It fails where a digit may continue the first natural and open the second.
example : pair.ok = true := by decide +kernel
example : pair.deterministic = false := by decide +kernel
#guard natural.deterministic && (Syn.seq spaceSep natural).deterministic

-- The text `12` is two naturals to the expression, with an empty separator between them.
example : pair.erase.Matches ['1', '2'] :=
  .seq (l₁ := ['1']) (l₂ := ['2'])
    (.seq (l₁ := ['1']) (l₂ := []) (.set (by decide)) .starNil)
    (.seq (l₁ := []) (l₂ := ['2']) (.altR .eps)
      (.seq (l₁ := ['2']) (l₂ := []) (.set (by decide)) .starNil))

-- It is one natural to the reader, which commits to the longest match and finds no second one.
#guard !pair.check ['1', '2']

/-! ## A control for each other clause -/

/-- The letter `x`. -/
def xs : CharSet := .single 'x'

/-- The letter `y`. -/
def ys : CharSet := .single 'y'

/-- A choice whose first alternative reads the empty text: nothing, or else `x`. -/
def emptyFirst : Syn (Unit ⊕ Char) := .alt .eps (.one xs)

-- Control of the choice clause, the first alternative that reads no empty text: the reader
-- takes the empty text and never tries the second alternative.
example : emptyFirst.deterministic = false := by decide +kernel
example : emptyFirst.erase.Matches ['x'] := .altR (.set (by decide))
#guard !emptyFirst.check ['x']

/-- A choice that its first character does not decide: `x`, or else `xy`. -/
def sharedFirst : Syn (Char ⊕ (Char × Char)) := .alt (.one xs) (.seq (.one xs) (.one ys))

-- Control of the choice clause, the two first sets: the reader takes `x` by the first
-- alternative and leaves `y`.
example : sharedFirst.deterministic = false := by decide +kernel
example : sharedFirst.erase.Matches ['x', 'y'] :=
  .altR (.seq (l₁ := ['x']) (l₂ := ['y']) (.set (by decide)) (.set (by decide)))
#guard !sharedFirst.check ['x', 'y']

/-- The part of `overlap`: `x`, then `y`, then `x` or nothing. -/
def piece : Syn (Char × Char × Option Char) := .seq (.one xs) (.seq (.one ys) (Syn.one xs).opt)

/-- A repeated part that may run into its next copy: `xy` or `xyx`, any number of times. -/
def overlap : Syn (List (Char × Char × Option Char)) := .many piece

-- Control of the repetition clause, the copy that ends before the next one: the part passes
-- `deterministic` and reads no empty text, and the `x` that may end one copy opens the next.
-- The text `xyxy` is two copies of `xy`.
#guard piece.deterministic && !piece.readsEmpty
example : overlap.deterministic = false := by decide +kernel
example : overlap.erase.Matches ['x', 'y', 'x', 'y'] :=
  have copy : piece.erase.Matches ['x', 'y'] :=
    .seq (l₁ := ['x']) (l₂ := ['y']) (.set (by decide))
      (.seq (l₁ := ['y']) (l₂ := []) (.set (by decide)) (.altR .eps))
  .starCons (l₁ := ['x', 'y']) (l₂ := ['x', 'y']) copy
    (.starCons (l₁ := ['x', 'y']) (l₂ := []) copy .starNil)

-- The reader takes `xyx` as the first copy, and `y` opens no second one.
#guard !overlap.check ['x', 'y', 'x', 'y']

/-! ## The test is sufficient, not necessary -/

/-- A choice of `x` with itself: no character decides it. -/
def same : Syn (Char ⊕ Char) := .alt (.one xs) (.one xs)

-- Where the law stops: the description fails the test, and its reader still accepts `x`, the
-- one text of its language.
#guard !same.deterministic && same.check ['x']

end WhatwgTest.Svg.Deterministic
