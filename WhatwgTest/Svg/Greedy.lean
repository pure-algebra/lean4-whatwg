import Whatwg.Svg.Value.Greedy
import Whatwg.Svg.Value.Number

/-!
# WhatwgTest.Svg.Greedy

Derivations, readers and controls of the rule of the reader (node V3b of
`docs/SVG-PACKAGE-PLAN.md`, section 6): `Whatwg/Svg/Value/Greedy.lean`.

A derivation is written by hand at a small description made for the battery, and shows one
rule of `Greedy` at work. A reader applies a law of the module at the coordinate of
`Whatwg/Svg/Value/Number.lean`, where no derivation is written by hand: the law turns one
evaluation of the reader into a fact about the rule. A control is a text that separates the
rule from the expression, or a fuel that separates two runs of `readMany`. The texts of the
coordinate are those of the paragraphs after the grammar under `PathDataBNF` of
`vendor/w3c-svgwg-47e645ef/master/paths.html`: `100-200`, `0.6.5` and `23.`.

What this battery does not claim: that the rule reads every text of a description's
expression. The second section holds a text of the expression that the rule does not read
whole.
-/

namespace WhatwgTest.Svg.Greedy

open Whatwg.Svg.Value

/-- The letter `x`. -/
def xs : CharSet := .single 'x'

/-- The letter `y`. -/
def ys : CharSet := .single 'y'

/-! ## Derivations by hand -/

/-- A repetition of a repetition: its part may read nothing. -/
def runs : Syn (List (List Char)) := .many (.many (.one xs))

-- The stall rule of `many`. The part reads `xx` as one run and leaves the empty text. On the
-- empty text the part succeeds again and reads nothing, so the repetition stops there, with
-- the one run as its value.
example : Greedy runs ['x', 'x'] (some ([['x', 'x']], [])) :=
  .manyStep
    (.manyStep (.oneMem (by decide)) (by decide)
      (.manyStep (.oneMem (by decide)) (by decide) (.manyStop .oneNil)))
    (by decide)
    (.manyStall (.manyStop .oneNil) (Nat.le_refl _))

-- Reader of `Syn.greedy_read` at that description: every text has an outcome, though the
-- part may succeed and read nothing.
example (s : List Char) : ∃ o, Greedy runs s o := ⟨_, Syn.greedy_read runs s⟩

/-- A choice whose first alternative may fail after it has read a character: `xy`, or else
`x`. -/
def retried : Syn ((Char × Char) ⊕ Char) := .alt (.seq (.one xs) (.one ys)) (.one xs)

/-- The second alternative of a choice. On `xz` the first alternative reads `x` and fails at
`z`. The second alternative then reads from the start of the text, not from `z`. -/
theorem retried_xz : Greedy retried ['x', 'z'] (some (.inr 'x', ['z'])) :=
  .altRight (.seqRight (.oneMem (by decide)) (.oneNot (by decide))) (.oneMem (by decide))

-- A refusal is a derivation too: on `z` both alternatives fail.
example : Greedy retried ['z'] none :=
  .altFail (.seqFail (.oneNot (by decide))) (.oneNot (by decide))

-- Reader of `Greedy.sound` at the derivation above: what the rule read of `xz` is a text of
-- the expression.
example : ∃ pre, ['x', 'z'] = pre ++ ['z'] ∧ retried.erase.Matches pre := retried_xz.sound

/-- A choice that its first character does not decide: `x`, or else `xy`. -/
def committed : Syn (Char ⊕ (Char × Char)) := .alt (.one xs) (.seq (.one xs) (.one ys))

-- Control of the ordered choice, and reader of `Greedy.unique`. On `xy` the first alternative
-- succeeds and leaves `y`. That outcome is the only one, so no derivation takes the second
-- alternative, which would read the text whole.
example (o : Option ((Char ⊕ (Char × Char)) × List Char)) (h : Greedy committed ['x', 'y'] o) :
    o = some (.inl 'x', ['y']) :=
  h.unique (.altLeft (.oneMem (by decide)))

/-! ## The rule and the expression -/

/-- Two naturals with an optional separator between them: the shape of a coordinate pair. -/
def pair : Syn (Nat × Unit × Nat) := .seq natural (.seq spaceSep natural)

-- The text `12` is a text of the expression: two naturals, with an empty separator between
-- them.
example : pair.erase.Matches ['1', '2'] :=
  .seq (l₁ := ['1']) (l₂ := ['2'])
    (.seq (l₁ := ['1']) (l₂ := []) (.set (by decide)) .starNil)
    (.seq (l₁ := []) (l₂ := ['2']) (.altR .eps)
      (.seq (l₁ := ['2']) (l₂ := []) (.set (by decide)) .starNil))

-- Control: the rule reads no value from `12` whole. The check decides it by one evaluation.
example : ¬ ∃ v, Greedy pair ['1', '2'] (some (v, [])) := fun h =>
  absurd ((Syn.check_iff_greedy pair _).mpr h) (by decide +kernel)

-- The outcome of the rule on `12` is a refusal: the first natural takes both digits, as the
-- chapter's rule asks, and no second natural follows.
example : Greedy pair ['1', '2'] none := (Syn.greedy_iff_read _ _ _).mpr (by decide +kernel)

/-! ## The coordinate -/

-- Reader of V3b at the chapter's first example, `100-200`: the rule reads the coordinate
-- `100` and leaves `-200`. One evaluation of the reader gives the derivation.
example : Greedy Decimal.grammar.syn ['1', '0', '0', '-', '2', '0', '0']
    (some (⟨100, 0⟩, ['-', '2', '0', '0'])) :=
  (Syn.greedy_iff_read _ _ _).mpr (by decide +kernel)

-- Reader of V3b at the chapter's second example, `0.6.5`: the rule reads `0.6` and leaves
-- `.5`.
example : Greedy Decimal.grammar.syn ['0', '.', '6', '.', '5'] (some (⟨6, -1⟩, ['.', '5'])) :=
  (Syn.greedy_iff_read _ _ _).mpr (by decide +kernel)

-- Reader of `Greedy.unique`: the rule refuses a text that opens with a letter, and a refusal
-- is the only outcome. So the rule reads no coordinate from that text, whatever value and
-- rest are proposed.
example (v : Decimal) (r : List Char) : ¬ Greedy Decimal.grammar.syn ['x', '1'] (some (v, r)) :=
  fun h =>
    have refused : Greedy Decimal.grammar.syn ['x', '1'] none :=
      (Syn.greedy_iff_read _ _ _).mpr (by decide +kernel)
    nomatch h.unique refused

-- Readers of the check law at the coordinate. The rule reads `+.5E-2` whole.
example : ∃ v, Greedy Decimal.grammar.syn ['+', '.', '5', 'E', '-', '2'] (some (v, [])) :=
  (Decimal.grammar.check_iff_greedy _).mp (by decide +kernel)

-- It reads no value from `23.` whole: the number format that the advisement under
-- `PathDataBNF` disallows.
example : ¬ ∃ v, Greedy Decimal.grammar.syn ['2', '3', '.'] (some (v, [])) := fun h =>
  absurd ((Decimal.grammar.check_iff_greedy _).mpr h) (by decide +kernel)

/-! ## The fuel -/

-- Reader of `readMany_fuel` at the digit: with any fuel that covers the text `12x`, the
-- repetition reads its two digits. The one evaluation is at the fuel 3.
example (fuel : Nat) (h : 3 ≤ fuel) :
    readMany digit.read fuel ['1', '2', 'x'] = ([1, 2], ['x']) := by
  rw [readMany_fuel digit.read fuel 3 ['1', '2', 'x'] h (by decide)]
  decide +kernel

-- Control of the premise: a fuel below the length of the text stops the run early.
#guard readMany digit.read 1 ['1', '2', 'x'] == ([1], ['2', 'x'])

end WhatwgTest.Svg.Greedy
