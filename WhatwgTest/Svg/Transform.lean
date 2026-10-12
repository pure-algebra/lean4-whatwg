import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Value.Grammar.Laws

/-!
# WhatwgTest.Svg.Transform

Readers, controls and finite evaluations of the grammar of the `transform` attribute (slice
S4c of `docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Transform.lean`. The texts are those of
the sealed file where it writes one.
`vendor/w3c-csswg-drafts-50337328/css-transforms-1/Overview.bs` writes four values of a
`transform` attribute, all in examples, and each is replayed here under the anchor nearest to
it.

A reader applies a law of `Grammar` at a real value. A control is a text that the grammar
refuses, or a description that `Syn.ok` refuses: it shows where the grammar or a law stops.

What this battery does not claim: that the reader takes every text of the description's
expression. The section "Where one number ends" holds a text of the expression that the
reader refuses.
-/

namespace WhatwgTest.Svg.Transform

open Whatwg.Svg.Value

/-- The text of a list. -/
def text (ts : TransformList) : String := String.ofList (TransformList.grammar.print ts)

/-- The value of a whole text. -/
def value (s : String) : Option TransformList := TransformList.grammar.read s.toList

/-- What a whole text prints back as. -/
def reprint (s : String) : Option String := (value s).map text

/-! ## The attribute values that the sealed file writes -/

-- `current-transformation-matrix-computation`, the example of nested elements: three values.
-- The first carries a sign, a comma and a space.
#guard value "translate(-10, 20)" == some [.translate ⟨-10, 0⟩ (some ⟨20, 0⟩)]
#guard reprint "translate(-10, 20)" == some "translate(-10,20)"
#guard value "scale(2)" == some [.scale ⟨2, 0⟩ none] && reprint "scale(2)" == some "scale(2)"
#guard value "rotate(45)" == some [.rotate ⟨45, 0⟩ none]
#guard reprint "rotate(45)" == some "rotate(45)"

-- `transform-attribute-specificity`, the example of the attribute beside the property: two
-- numbers with a space and no comma.
#guard value "translate(200 200)" == some [.translate ⟨200, 0⟩ (some ⟨200, 0⟩)]
#guard reprint "translate(200 200)" == some "translate(200,200)"

-- Controls: the values of the `transform` property that the file writes in the style sheets
-- of its examples, under `transform-attribute-specificity`, `svg-user-coordinate-space` and
-- `transformation-matrix-computation`. They carry units. `svg-syntax` says that the syntax of
-- the attribute differs from the property's, and the productions have no unit.
#guard value "translate(100px, 100px)" == none
#guard value "translate(-10px, -20px) scale(2) rotate(45deg)" == none

/-! ## The six functions -/

-- Each function with each number of arguments that its production takes.
#guard value "matrix(1 0 0 1 30 40)" ==
  some [.matrix ⟨1, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ ⟨30, 0⟩ ⟨40, 0⟩]
#guard value "translate(5)" == some [.translate ⟨5, 0⟩ none]
#guard value "scale(2,3)" == some [.scale ⟨2, 0⟩ (some ⟨3, 0⟩)]
#guard value "rotate(45,100,50)" == some [.rotate ⟨45, 0⟩ (some (⟨100, 0⟩, ⟨50, 0⟩))]
#guard value "skewX(30)" == some [.skewX ⟨30, 0⟩] && value "skewY(-30)" == some [.skewY ⟨-30, 0⟩]

-- Controls: a number of arguments that no production takes. `rotate` with two, `matrix` with
-- five and with seven, `translate` with three, `skewX` with two, and none at all.
#guard value "rotate(45 100)" == none
#guard value "matrix(1 0 0 1 30)" == none && value "matrix(1 0 0 1 30 40 50)" == none
#guard value "translate(1 2 3)" == none && value "skewX(1 2)" == none && value "scale()" == none

-- One function is a grammar of its own, the production `transform`. It has no white space
-- around the function, and no second function.
#guard Transform.grammar.read "skewX(30)".toList == some (.skewX ⟨30, 0⟩)
#guard Transform.grammar.read " skewX(30)".toList == none
#guard Transform.grammar.read "skewX(30)skewX(30)".toList == none

/-! ## The names -/

-- Controls: the description reads `s`, then `cale` or `kew`, then `X` or `Y`. A part of a
-- factored name is no name.
#guard value "s(1)" == none && value "skew(1)" == none
#guard value "cale(1)" == none && value "kewX(1)" == none

-- Controls: the five functions that `svg-syntax` names as not supported in the attribute. The
-- texts are the examples of an identity transform function under `terminology`, and
-- `translateX(1)` is one more.
#guard value "translateX(0)" == none && value "translateY(0)" == none
#guard value "scaleX(1)" == none && value "scaleY(1)" == none && value "skew(0, 0)" == none
#guard value "translateX(1)" == none

-- The six other examples of that definition are texts of the attribute's grammar too.
#guard ["translate(0)", "scale(1)", "rotate(0)", "skewX(0)", "skewY(0)",
  "matrix(1, 0, 0, 1, 0, 0)"].all fun s => (value s).isSome

-- Controls: a name is read as its production writes it. The section does not say that the
-- letters match in either case, so an upper-case letter for a lower-case one is refused, and
-- so is the reverse.
#guard value "Rotate(45)" == none && value "ROTATE(45)" == none && value "Translate(1)" == none
#guard value "skewx(30)" == none && value "SkewX(30)" == none && value "skewy(30)" == none

-- Control: `none` is a value of the property (`transform-property`) and no text of this
-- grammar.
#guard value "none" == none

/-! ## White space and separators -/

-- `wsp*` in each place where a production has it: after the name, inside each parenthesis and
-- at both ends of the list. It prints as nothing.
#guard reprint " \t translate \n ( \r 1 , 2 \t ) \n " == some "translate(1,2)"

-- `comma-wsp?` between two numbers: white space, a comma, both, or nothing where a sign parts
-- the two.
#guard value "translate(1 2)" == value "translate(1,2)"
#guard value "translate(1 \n,\t 2)" == value "translate(1,2)"
#guard value "translate(1-2)" == some [.translate ⟨1, 0⟩ (some ⟨-2, 0⟩)]

-- White space after the last number is the `wsp*` before `)`, and no separator: the reader
-- tries a further number, finds none and goes back.
#guard value "translate(1 )" == some [.translate ⟨1, 0⟩ none]
#guard value "rotate(45 )" == some [.rotate ⟨45, 0⟩ none]
#guard reprint "matrix(1 0 0 1 30 40 )" == some "matrix(1,0,0,1,30,40)"

-- `comma-wsp?` between two functions: the same spellings, and nothing at all.
#guard ["scale(2)rotate(45)", "scale(2) rotate(45)", "scale(2),rotate(45)",
  "scale(2) \n,\t rotate(45)"].all fun s => reprint s == some "scale(2) rotate(45)"

-- Controls: `comma-wsp` has one comma at most, and a comma only parts two numbers or two
-- functions.
#guard value "translate(1,,2)" == none && value "translate(,1)" == none
#guard value "translate(1,)" == none && value "translate,(1)" == none
#guard value "scale(2),,rotate(45)" == none && value ",scale(2)" == none
#guard value "scale(2)," == none && value "," == none

-- Each of the four characters of `svg-wsp` is white space: line feed, carriage return, tab
-- and space.
#guard ["\n", "\r", "\t", " "].all fun w =>
  reprint (w ++ "scale(" ++ w ++ "2" ++ w ++ ")" ++ w ++ "rotate" ++ w ++ "(45)" ++ w) ==
    some "scale(2) rotate(45)"

-- Control: a form feed is not. The white space of path data has it, and so does the
-- informative railroad diagram of `svg-wsp`; the text of `svg-wsp` does not.
#guard wspSet.mem '\x0c' && !Transform.wspSet.mem '\x0c'
#guard value "scale(2)\x0crotate(45)" == none && value "rotate(\x0c45)" == none
#guard value "\x0c" == none

-- Controls: a vertical tab and a no-break space are no white space either.
#guard !Transform.wspSet.mem '\x0b' && !Transform.wspSet.mem '\u00a0'
#guard value "scale(2)\u00a0rotate(45)" == none

-- The empty text is a list, because `transforms` is optional in `transform-list`. So is white
-- space alone. The empty list prints as the empty text.
#guard value "" == some [] && value " \n\t\r" == some [] && text [] == ""

/-! ## Units and parentheses -/

-- Controls: a unit, a percentage, and a parenthesis that is missing or extra.
#guard value "rotate(45deg)" == none && value "translate(10px)" == none
#guard value "scale(50%)" == none
#guard value "rotate(45" == none && value "rotate 45)" == none && value "rotate" == none
#guard value "rotate(45))" == none && value "rotate((45)" == none && value "(45)" == none

/-! ## Where one number ends -/

-- A number is the `coordinate` of path data (ruling SV-26): a sign of either kind, a bare
-- fraction, an exponent with either mark.
#guard value "translate(+.5e1,-1E-2)" == some [.translate ⟨5, 0⟩ (some ⟨-1, -2⟩)]
#guard reprint "translate(+.5e1,-1E-2)" == some "translate(5,-0.01)"

-- A number is read to its longest match, so a second point starts a second number.
#guard value "scale(1.5.5)" == some [.scale ⟨15, -1⟩ (some ⟨5, -1⟩)]

-- Control (V3c): the description is not deterministic, and two numbers with nothing between
-- them show it. The text `12` is of the expression, as `1` and then `2` with an empty
-- `comma-wsp?`. The reader takes `12` as one number, and no second number is left.
example : (Syn.seq Decimal.syn Transform.next).erase.Matches "12".toList :=
  .seq (l₁ := ['1']) (l₂ := ['2']) (Decimal.grammar.matches_of_check (by decide +kernel))
    (.seq (l₁ := []) (l₂ := ['2']) (.altR .eps)
      (Decimal.grammar.matches_of_check (by decide +kernel)))

#guard (Syn.seq Decimal.syn Transform.next).read "12".toList == none

-- So `123456` is one number and not the six of `matrix`, and `12` is one argument of
-- `translate` and not two.
#guard value "matrix(123456)" == none
#guard value "translate(12)" == some [.translate ⟨12, 0⟩ none]

/-! ## The one spelling of a value -/

-- One comma between two numbers, one space between two functions, and no other white space.
#guard text [.translate ⟨10, 0⟩ (some ⟨20, 0⟩), .rotate ⟨45, 0⟩ none] ==
  "translate(10,20) rotate(45)"
#guard text [.matrix ⟨1, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ ⟨-15, -1⟩ ⟨2, 1⟩] == "matrix(1,0,0,1,-1.5,2e1)"
#guard text [.rotate ⟨-45, 0⟩ (some (⟨1, 0⟩, ⟨2, 0⟩)), .skewX ⟨3, 0⟩, .skewY ⟨4, 0⟩,
  .scale ⟨1, 0⟩ none] == "rotate(-45,1,2) skewX(3) skewY(4) scale(1)"
#guard String.ofList (Transform.grammar.print (.scale ⟨2, 0⟩ (some ⟨3, 0⟩))) == "scale(2,3)"

-- Control: the value is what the text states. `translate(10)` and `translate(10,0)` are two
-- values with two spellings, whatever they mean.
#guard value "translate(10)" != value "translate(10,0)"
#guard text [.translate ⟨10, 0⟩ none] != text [.translate ⟨10, 0⟩ (some ⟨0, 0⟩)]

/-! ## The laws at this grammar -/

-- Reader of V1: every list reads back from its spelling. The value here is not a literal.
example (angle cx cy : Decimal) (rest : TransformList) :
    TransformList.grammar.read
        (TransformList.grammar.print (.rotate angle (some (cx, cy)) :: rest)) =
      some (.rotate angle (some (cx, cy)) :: rest) :=
  TransformList.grammar.read_print _

-- Reader of V1 with a text after the value. A function ends at its right parenthesis and
-- nothing continues it, so the reader hands back whatever text follows.
example (t : Transform) (rest : List Char) :
    Transform.syn.read (Transform.syn.print t ++ rest) = some (t, rest) :=
  Syn.read_print Transform.syn Transform.grammar.ok t rest (Transform.grammar.total t) (by
    have h : Transform.syn.continues = CharSet.empty := by decide +kernel
    rw [h]
    exact fun c _ _ => CharSet.mem_empty c)

-- Reader of V2, the face a dispatcher calls: a printed list passes the check.
example (angle : Decimal) (rest : TransformList) :
    TransformList.grammar.check (TransformList.grammar.print (.skewX angle :: rest)) = true :=
  TransformList.grammar.check_print _

-- Reader of the embedding: an argument that is absent and one that is zero have two
-- spellings, whatever the first argument is.
example (tx : Decimal) :
    TransformList.grammar.print [.translate tx none] ≠
      TransformList.grammar.print [.translate tx (some ⟨0, 0⟩)] :=
  fun h => nomatch TransformList.grammar.print_injective h

-- Control: the reader is no embedding. Many texts are one value.
#guard value "translate(1 2)" == value "translate(+1,2)" && value " scale(2)" == value "scale(2)"

-- Reader of V3a: a text that passes the check is a text of the description's language.
example : TransformList.syn.erase.Matches "rotate(45) scale(2)".toList :=
  TransformList.grammar.matches_of_check (by decide +kernel)

/-! ## Why the description has its shape -/

/-- Two numbers with `wsp*` between them, which prints as nothing. -/
def glued : Syn (Decimal × Decimal) := .seq Decimal.syn (.right Transform.wsps Decimal.syn)

-- Control: `ok` is false, and the retraction fails. `1` and `2` print as `12`, which reads as
-- one number. So the separator of two numbers prints a comma.
example : glued.ok = false := by decide +kernel
#guard glued.print (⟨1, 0⟩, ⟨2, 0⟩) == "12".toList && glued.read "12".toList == none

/-- Two names as their productions write them: `scale`, or `skewX`. -/
def unfactored : Syn (Unit ⊕ Unit) :=
  .alt (.lit ['s', 'c', 'a', 'l', 'e']) (.lit ['s', 'k', 'e', 'w', 'X'])

-- Control: `ok` is false, because both alternatives open with `s`. So the description puts
-- the three names under one `s`, and `Transform.grammar` holds its `ok`. The reader of this
-- choice still answers: it reads the second alternative from the start when the first fails.
example : unfactored.ok = false := by decide
#guard unfactored.readAll "skewX".toList == some (.inr ())

end WhatwgTest.Svg.Transform
