import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Transform

Owner: the value of the `transform` attribute, which is also the value of `gradientTransform`
and of `patternTransform` (slice S4c of `docs/SVG-PACKAGE-PLAN.md`, section 5.3; ruling SV-26).
The authority is the section `svg-syntax` of
`vendor/w3c-csswg-drafts-50337328/css-transforms-1/Overview.bs`, under `svg-transform`. Its
productions, each with its anchor: `comma` (`svg-comma`), `wsp` (`svg-wsp`), `comma-wsp`
(`svg-comma-wsp`), `translate` (`svg-translate`), `scale` (`svg-scale`), `rotate`
(`svg-rotate`), `skewX` (`svg-skewX`), `skewY` (`svg-skewY`), `matrix` (`svg-matrix`),
`transform` (`svg-transform-function`), `transforms` (`svg-transforms`) and `transform-list`
(`svg-transform-list`). The railroad diagram beside a production is informative: the section
says so, and this module reads the productions and the text.

Two typed values:

- `Transform` is the production `transform`: one function and its numbers. An argument that a
  production makes optional is an `Option` in the type.
- `TransformList` is the production `transform-list`: the functions in order. The empty list
  is a value, because `transforms` is optional in that production.

Each is a `Grammar`, so its laws are those of `Whatwg/Svg/Value/Grammar.lean`. The printer
writes one spelling of a value, such as `translate(10,20) rotate(45)`:

- a function is its name, `(`, its numbers with one comma between two, and `)`;
- a list is its functions with one space between two;
- every `wsp*` prints as nothing, so the empty list prints as the empty text.

The reader takes more spellings than the printer writes. It reads `comma-wsp?` between two
numbers and between two functions, and `wsp*` after a name, inside each parenthesis and at
both ends of a list.

Three productions are described with another shape, and the language is the same:

- `transform` is `matrix | translate | scale | rotate | skewX | skewY`. One character decides
  a choice of this library (`Syn.ok`), and three of the names open with `s`. The description
  is `"matrix" M | "translate" T | "s" ("cale" T | "kew" ("X" K | "Y" K)) | "rotate" R`, where
  a capital is what follows the name in its production: the arguments between their
  parentheses. Concatenation distributes over a choice, and the order of a choice's
  alternatives does not change its language.
- `transforms` is `transform | transform comma-wsp? transforms`. The description is
  `transform (comma-wsp? transform)*`, which is that right recursion as a repetition.
- `comma-wsp` is `(wsp+ comma? wsp*) | (comma wsp*)`. It is the production `comma_wsp` of path
  data over another set of white space, and `Whatwg/Svg/Value/Number.lean` states its
  description.

Two rulings of this package:

- White space. The text of `svg-wsp` names four characters: U+000A, U+000D, U+0009 and U+0020.
  `Transform.wspSet` is that set. It is not `wspSet` of path data, which also holds U+000C. The
  railroad diagram of `svg-wsp` lists space, tab, carriage return and form feed, which is
  another set again. The diagram is informative, and this module follows the text.
- The number. The productions write `number`, and the section has no production of that name.
  Its list of notation names `<number-token>` of CSS Syntax 3, and the railroad diagrams write
  that name where the productions write `number`. CSS Syntax 3 is not sealed (SV-26). So a
  number of this grammar is SVG's own production: the `coordinate` of the path data grammar,
  `sign? number`, whose typed value is `Decimal`. The signed production is the one because the
  sealed file writes the attribute value `translate(-10, 20)` (the example under
  `current-transformation-matrix-computation`). This is a ruling of this package. It says
  nothing about `<number-token>`.

One reading. The section does not say whether the letters of a name match in either case. The
names are read as the productions write them: `skewX` and not `skewx`, `translate` and not
`Translate`.

What this module does not claim:

- Anything about the syntax of the CSS property, `none | <transform-list>`. The section
  `svg-syntax` says that the attribute's syntax differs from it and that the attribute does
  not support `translateX()`, `translateY()`, `scaleX()`, `scaleY()` and `skew()`. The
  productions have no unit and no `none`. The reader refuses each of these.
- Anything about what a transform means. No matrix is computed, and the mapping of
  `svg-transform-functions` to the CSS functions is not modelled. `translate(10)` and
  `translate(10,0)` are two values.
- That the printer's spelling is a serialization the sealed text asks for. The rule under
  `serialization-of-transform-functions` is for the CSS functions of the property, and it
  puts a space after each comma. The spelling here is this module's choice among the texts of
  the grammar.
- That the reader takes every text of the description's expression (node V3b of the library,
  open). A number is read to its longest match. Two numbers with nothing between them, such as
  `12` for `1` and `2`, are a text of the expression that the reader takes as one number. So
  the reader refuses `matrix(123456)`.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from CSS
Transforms Module Level 1, https://drafts.csswg.org/css-transforms-1/, under the W3C Software
and Document License, https://www.w3.org/copyright/software-license-2023/
-/

namespace Whatwg.Svg.Value

/-- One function of a `transform` attribute value: the typed value of the production
`transform` (`svg-transform-function`). An argument is a number of the grammar, and an
argument that the production makes optional is an `Option`. The value is what the text states
and not a matrix: `translate 10 none` and `translate 10 (some 0)` are two values. -/
inductive Transform where
  /-- `matrix` (`svg-matrix`): six numbers. -/
  | matrix (a b c d e f : Decimal)
  /-- `translate` (`svg-translate`): one number, or two. -/
  | translate (tx : Decimal) (ty : Option Decimal)
  /-- `scale` (`svg-scale`): one number, or two. -/
  | scale (sx : Decimal) (sy : Option Decimal)
  /-- `rotate` (`svg-rotate`): one number, or three. The production takes the second and the
  third together or not at all, so they are one optional pair. -/
  | rotate (angle : Decimal) (center : Option (Decimal × Decimal))
  /-- `skewX` (`svg-skewX`): one number. -/
  | skewX (angle : Decimal)
  /-- `skewY` (`svg-skewY`): one number. -/
  | skewY (angle : Decimal)
  deriving DecidableEq, Repr, Inhabited

namespace Transform

/-! ## White space and the separator of two numbers -/

/-- `wsp` of this grammar (`svg-wsp`): line feed, carriage return, tab and space. It has no
form feed, so it is not `wspSet` of path data. -/
def wspSet : CharSet := .ofList ['\n', '\r', '\t', ' ']

/-- `wsp*`, read in any amount and printed as nothing. -/
def wsps : Syn Unit := wspsOf wspSet

/-- `comma-wsp?` between two numbers (`svg-comma-wsp`), printed as a comma. -/
def argSep : Syn Unit := commaSepOf wspSet

/-- `wsps` prints its one value. -/
theorem wsps_total : wsps.Total := Syn.Total.of_unit (by decide)

/-- `argSep` prints its one value. -/
theorem argSep_total : argSep.Total := Syn.Total.of_unit (by decide)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] wsps_total argSep_total

/-! ## The arguments -/

/-- `comma-wsp? number`: a number after another one. -/
def next : Syn Decimal := .right argSep Decimal.syn

/-- Every number after another one prints. -/
theorem next_total : next.Total := by
  unfold next
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] next_total

/-- `number ( comma-wsp? number )?`: the arguments of `translate` and of `scale`. -/
def oneOrTwo : Syn (Decimal × Option Decimal) := .seq Decimal.syn next.opt

/-- `number ( comma-wsp? number comma-wsp? number )?`: the arguments of `rotate`. -/
def oneOrThree : Syn (Decimal × Option (Decimal × Decimal)) :=
  .seq Decimal.syn (Syn.seq next next).opt

/-- Six numbers with `comma-wsp?` between two: the arguments of `matrix`. -/
def six : Syn (Decimal × Decimal × Decimal × Decimal × Decimal × Decimal) :=
  .seq Decimal.syn (.seq next (.seq next (.seq next (.seq next next))))

/-- Every argument list of `translate` and of `scale` prints. -/
theorem oneOrTwo_total : oneOrTwo.Total := by
  unfold oneOrTwo
  aesop (rule_sets := [Whatwg.Syn])

/-- Every argument list of `rotate` prints. -/
theorem oneOrThree_total : oneOrThree.Total := by
  unfold oneOrThree
  aesop (rule_sets := [Whatwg.Syn])

/-- Every argument list of `matrix` prints. -/
theorem six_total : six.Total := by
  unfold six
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] oneOrTwo_total oneOrThree_total six_total

/-! ## The functions -/

/-- Letters, then `wsp* "(" wsp* args wsp* ")"`: what the six productions of a function share.
The letters are a whole name, or what is left of a name whose first letters are factored.
Each `wsp*` prints as nothing. -/
def call {α : Type} (letters : List Char) (args : Syn α) : Syn α :=
  .right (.lit letters)
    (.right wsps (.right (.lit ['(']) (.right wsps (.left args (.right wsps (.lit [')']))))))

/-- A function prints every value, when its letters and its arguments do. -/
theorem call_total {α : Type} {letters : List Char} {args : Syn α}
    (hletters : (Syn.lit letters).Total) (hargs : args.Total) : (call letters args).Total := by
  unfold call
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] call_total

/-- The production `transform`, with the three names that open with `s` under one `s`, and
the two that open with `skew` under one `kew`:
`"matrix" M | "translate" T | "s" ("cale" T | "kew" ("X" K | "Y" K)) | "rotate" R`, where a
capital is the arguments of that function between their parentheses. -/
def spellings :
    Syn ((Decimal × Decimal × Decimal × Decimal × Decimal × Decimal) ⊕
      ((Decimal × Option Decimal) ⊕
        (((Decimal × Option Decimal) ⊕ (Decimal ⊕ Decimal)) ⊕
          (Decimal × Option (Decimal × Decimal))))) :=
  .alt (call ['m', 'a', 't', 'r', 'i', 'x'] six)
    (.alt (call ['t', 'r', 'a', 'n', 's', 'l', 'a', 't', 'e'] oneOrTwo)
      (.alt
        (.right (.lit ['s'])
          (.alt (call ['c', 'a', 'l', 'e'] oneOrTwo)
            (.right (.lit ['k', 'e', 'w'])
              (.alt (call ['X'] Decimal.syn) (call ['Y'] Decimal.syn)))))
        (call ['r', 'o', 't', 'a', 't', 'e'] oneOrThree)))

/-- Every reading of a function prints. -/
theorem spellings_total : spellings.Total := by
  unfold spellings
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] spellings_total

/-- The value of a reading: the alternative names the function. -/
def ofReading :
    (Decimal × Decimal × Decimal × Decimal × Decimal × Decimal) ⊕
      ((Decimal × Option Decimal) ⊕
        (((Decimal × Option Decimal) ⊕ (Decimal ⊕ Decimal)) ⊕
          (Decimal × Option (Decimal × Decimal)))) → Transform
  | .inl (a, b, c, d, e, f) => .matrix a b c d e f
  | .inr (.inl (tx, ty)) => .translate tx ty
  | .inr (.inr (.inl (.inl (sx, sy)))) => .scale sx sy
  | .inr (.inr (.inl (.inr (.inl angle)))) => .skewX angle
  | .inr (.inr (.inl (.inr (.inr angle)))) => .skewY angle
  | .inr (.inr (.inr (angle, center))) => .rotate angle center

/-- The reading of a value: its function's alternative, with its arguments. -/
def toReading : Transform →
    (Decimal × Decimal × Decimal × Decimal × Decimal × Decimal) ⊕
      ((Decimal × Option Decimal) ⊕
        (((Decimal × Option Decimal) ⊕ (Decimal ⊕ Decimal)) ⊕
          (Decimal × Option (Decimal × Decimal))))
  | .matrix a b c d e f => .inl (a, b, c, d, e, f)
  | .translate tx ty => .inr (.inl (tx, ty))
  | .scale sx sy => .inr (.inr (.inl (.inl (sx, sy))))
  | .skewX angle => .inr (.inr (.inl (.inr (.inl angle))))
  | .skewY angle => .inr (.inr (.inl (.inr (.inr angle))))
  | .rotate angle center => .inr (.inr (.inr (angle, center)))

/-- A value's reading is read as the value. -/
theorem ofReading_toReading (t : Transform) : ofReading (toReading t) = t := by
  cases t <;> rfl

/-- The description of `transform`. -/
def syn : Syn Transform := .map ofReading toReading ofReading_toReading spellings

/-- Every function prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `transform`: one function. -/
def grammar : Grammar Transform := ⟨syn, by decide +kernel, syn_total⟩

end Transform

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Transform.syn_total

/-! ## The list -/

/-- The value of a `transform` attribute: the typed value of the production `transform-list`
(`svg-transform-list`), the functions in order. The empty list is a value. -/
abbrev TransformList : Type := List Transform

namespace TransformList

/-- `comma-wsp?` between two functions (`svg-transforms`), printed as one space. -/
def sep : Syn Unit := spaceSepOf Transform.wspSet

/-- `sep` prints its one value. -/
theorem sep_total : sep.Total := Syn.Total.of_unit (by decide)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] sep_total

/-- The production `transforms` as a repetition: `transform (comma-wsp? transform)*`. -/
def transforms : Syn (Transform × List Transform) :=
  Transform.syn.sepBy1 sep

/-- Every non-empty run of functions prints. -/
theorem transforms_total : transforms.Total := by
  unfold transforms
  aesop (rule_sets := [Whatwg.Syn])

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] transforms_total

/-- The value of a reading: no `transforms` is the empty list. -/
def ofReading : Option (Transform × List Transform) → TransformList
  | none => []
  | some (t, ts) => t :: ts

/-- The reading of a value: the empty list is no `transforms`. -/
def toReading : TransformList → Option (Transform × List Transform)
  | [] => none
  | t :: ts => some (t, ts)

/-- A value's reading is read as the value. -/
theorem ofReading_toReading (ts : TransformList) : ofReading (toReading ts) = ts := by
  cases ts <;> rfl

/-- The description of `transform-list`: `wsp* transforms? wsp*`. -/
def syn : Syn TransformList :=
  .map ofReading toReading ofReading_toReading
    (.right Transform.wsps (.left transforms.opt Transform.wsps))

/-- Every list of functions prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `transform-list`: the value of a `transform`, `gradientTransform` or
`patternTransform` attribute. -/
def grammar : Grammar TransformList := ⟨syn, by decide +kernel, syn_total⟩

end TransformList

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] TransformList.syn_total

end Whatwg.Svg.Value
