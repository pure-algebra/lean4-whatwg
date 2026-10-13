import Whatwg.Css.Syntax.Write
import Whatwg.Css.Syntax.Parse

/-!
# Whatwg.Css.Syntax.Build

Owner: the builders of the tree of CSS (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; ruling CS-9 of
`docs/CSS-PACKAGE-PLAN.md`: one tree is written and read).

`Whatwg/Css/Syntax/Tree.lean` has the tree that parsing gives, and
`Whatwg/Css/Syntax/Write.lean` writes it. A program that writes CSS builds that tree. This
module is the few constructors it builds with, so that no value is spliced from text and none
is written token by token.

A value, a prelude and the arguments of a function are one type: component values in a row
(`Value`, and `Prelude` for a reader's eye).

- **One component value.** `Component.ident`, `Component.string`, `Component.hash`,
  `Component.delim`, `Component.space`, `Component.comma`, `Component.colon`.
  `Component.number` of a rational number, `Component.int`, `Component.thousandths` of a count
  of thousandths, `Component.dimension` with `px`, `ms`, `s` and `deg`, and `Component.percent`.
  `Component.call` is a function with its arguments, and `Component.parens` and
  `Component.brackets` a simple block. `Component.custom` is the name of a custom property and
  `Component.var` a reference to one, with its fallback. `Component.calc` is `calc()` of an
  expression (`Calc`).
- **A row.** `Value.spaced` puts a space between two components, `Value.commas` a comma and a
  space, and `Value.list` a comma and a space between two values. `Value.ofText` is the value of
  a text, for a caller who has only a string: the tokenizer and then the parser. `Value.text` is
  the text of a value.
- **A prelude.** `Prelude.class`, `Prelude.type`, `Prelude.id`, `Prelude.attr`,
  `Prelude.pseudo`, `Prelude.root`; `Prelude.feature`, a media feature in its parentheses;
  `Prelude.from`, `Prelude.to` and `Prelude.percent`, the selectors of a keyframe;
  `Prelude.ofText`, the prelude of a text.
- **A declaration.** `Declaration.of` and `Declaration.custom`.

```
Component.var "--e4-color-ink"                              -- var(--e4-color-ink)
Value.spaced [.ident "m-2", .ms 94.2, .ms 180, .ident "both"]  -- m-2 94.2ms 180ms both
Component.calc (.mul (.sub (.leaf (.int 300)) (.leaf (.var "--t" [.int 0]))) (.leaf (.ms 0.6)))
                                                            -- calc((300 - var(--t, 0)) * 0.6ms)
Prelude.attr "data-track" "m-0"                             -- [data-track="m-0"]
Value.ofText "1px solid #555"                               -- the value of a caller's text
```

How a number is spelled. A number is a rational number, and its text is its decimal expansion
(`Numeric.text`): a hyphen-minus below nothing, the whole part, and the digits after the full
stop with no zero at the end. A whole number is of the type "integer" and has no full stop. So
`Component.thousandths 1567` is `1.567`, and `Component.thousandths 1000` is `1`.

Where white space goes. A row holds its own white space: `Value.spaced` and `Value.commas` put
a whitespace token between two components, and the parser keeps one there. A value and a
prelude built here have none at their two ends. The white space that the parser drops, at the
ends of a value and around a block, is the writer's to put (`Whatwg/Css/Syntax/Write.lean`).

What a built value satisfies, as two tests that compute.

- `Value.writable`, `Component.writable`: the tokens of the value are `Writable`
  (`Whatwg/Css/Syntax/Serialize.lean`), which is the premise of the round trip of
  `Whatwg/Css/Syntax/Laws.lean`.
- `Value.quiet`, `Component.quiet`: no two tokens of the value that stand next to each other
  need a comment between them (`needsComment`), so its text holds no `/**/`.
- `Calc.writable`, `Calc.quiet`: the same of each leaf of an expression.

`Whatwg/Css/Syntax/Build/Laws.lean` has the laws: which builders give a writable and a quiet
value for every argument, and what the others ask of theirs.

Why no text is a value by itself. A text becomes a value by `Value.ofText`, said by name, and
no coercion does it. Lean puts a coercion at each leaf of `a ++ b`, so `".e4_" ++ name` would
be two values read apart and then joined, two identifiers with a comment between them, and not
the value of the joined text.

What this module does not claim. That a built value is a value of its property: the grammar of
a property is judged by `Whatwg/Css/Values/Admits.lean`. That a selector selects anything: a
prelude is component values, and no grammar of selectors is here. That a number has a decimal
text: `1/3` has none, and `Component.number (1/3)` is a value that is not writable
(`isDecimal`). A unit and a name are the caller's: `Component.dimension 1 "e3"` would be read
back as a number with an exponent, and is not writable either.

`Whatwg.Css` is under the ordinary axiom ceiling. A builder that takes a `String` reaches
`Classical.choice` through `String.toList` of core, `Component.thousandths` through `mkRat`, and
`Value.ofText` through the tokenizer too. The others, a number, a row, a block, an expression of
`calc()` and the two tests, depend on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Css.Syntax

/-- Component values in a row: the value of a declaration, the arguments of a function. -/
abbrev Value : Type := List Component

/-- Component values in a row, as the prelude of a rule: a selector, a media query, the name of
an animation. -/
abbrev Prelude : Type := List Component

/-! ## Numbers -/

/-- The numeric value of a rational number, with the sign character that its text has: a
hyphen-minus below nothing, and none otherwise. -/
def Numeric.of (q : Rat) : Numeric :=
  { value := q, sign := if q.num < 0 then some .minus else none }

/-- The type a number is written in: "integer" where it is whole. -/
def NumberFlag.of (q : Rat) : NumberFlag := if q.den = 1 then .integer else .number

/-- **Whether a number has a decimal text**: its denominator divides the power of ten that the
writer writes it to. A count of thousandths always does (`isDecimal_mkRat_thousand`), and so
does a whole number; a third does not. -/
def isDecimal (q : Rat) : Bool := 10 ^ max 1 (fractionDigits q.den) % q.den == 0

/-- A name with the two hyphen-minus of a custom property before it, where it has none. -/
def dashed : List Char → List Char
  | '-' :: '-' :: rest => '-' :: '-' :: rest
  | name => '-' :: '-' :: name

/-- A unit that is written with no escape and is not read as an exponent. -/
def isUnit (unit : String) : Bool := isPlainIdentifier unit.toList && !readsAsExponent unit.toList

namespace Component

/-! ## One component value -/

/-- A whitespace token: what stands between two components of a row. -/
def space : Component := .token .whitespace

/-- A comma. -/
def comma : Component := .token .comma

/-- A colon. -/
def colon : Component := .token .colon

/-- A delimiter: `.`, `*`, `>`, `=`. -/
def delim (c : Char) : Component := .token (.delim c)

/-- An identifier: `both`, `fill-box`, `m-2`. It is written with the escapes it needs. -/
def ident (name : String) : Component := .token (.ident name.toList)

/-- A string, written between quotation marks with the escapes it needs. -/
def string (text : String) : Component := .token (.string text.toList)

/-- A hash token: `#fig3`, `#14110d`. Its type is "id" where the name starts as an identifier
does. -/
def hash (name : String) : Component :=
  .token (.hash name.toList (if startsIdent name.toList then .id else .unrestricted))

/-- **A number.** It is writable where it has a decimal text (`isDecimal`). -/
def number (q : Rat) : Component := .token (.number (.of q) (.of q))

/-- A whole number. -/
def int (n : Int) : Component := number n

/-- A count of thousandths as a number: `1567` is `1.567`, `-50` is `-0.05`, `1000` is `1`. -/
def thousandths (n : Int) : Component := number (mkRat n 1000)

/-- **A dimension**: a number and its unit. -/
def dimension (q : Rat) (unit : String) : Component :=
  .token (.dimension (.of q) (.of q) unit.toList)

/-- A length in pixels. -/
def px (q : Rat) : Component := dimension q "px"

/-- A time in milliseconds. -/
def ms (q : Rat) : Component := dimension q "ms"

/-- A time in seconds. -/
def s (q : Rat) : Component := dimension q "s"

/-- An angle in degrees. -/
def deg (q : Rat) : Component := dimension q "deg"

/-- A per cent. -/
def percent (q : Rat) : Component := .token (.percentage (.of q))

/-- **A function with its arguments**: `name(arguments)`. -/
def call (name : String) (arguments : Value) : Component := .function name.toList arguments

/-- A value in parentheses. -/
def parens (value : Value) : Component := .block .paren value

/-- A value in square brackets. -/
def brackets (value : Value) : Component := .block .square value

/-- **The name of a custom property**, as an identifier with its two hyphen-minus: `t` and
`--t` are both `--t`. -/
def custom (name : String) : Component := .token (.ident (dashed name.toList))

/-- **A reference to a custom property**: `var(--name)`, and `var(--name, fallback)` where a
fallback is given. -/
def var (name : String) (fallback : Value := []) : Component :=
  .function ['v', 'a', 'r']
    (custom name :: (if fallback.isEmpty then [] else comma :: space :: fallback))

end Component

/-! ## Rows -/

namespace Value

/-- Components in a row, with a space between two: `m-2 94.2ms 180ms both`. -/
def spaced : List Component → Value
  | [] => []
  | [c] => [c]
  | c :: d :: rest => c :: .space :: spaced (d :: rest)

/-- Components in a row, with a comma and a space between two: the arguments of
`cubic-bezier(0.333333, 1, 0.666667, 1)`. -/
def commas : List Component → Value
  | [] => []
  | [c] => [c]
  | c :: d :: rest => c :: .comma :: .space :: commas (d :: rest)

/-- Values in a row, with a comma and a space between two: the animations of one `animation`
declaration, the selectors of `h1, h2`. -/
def list : List Value → Value
  | [] => []
  | [v] => v
  | v :: w :: rest => v ++ .comma :: .space :: list (w :: rest)

/-- The component value is a whitespace token. -/
def isSpace : Component → Bool
  | .token .whitespace => true
  | _ => false

/-- A value with no white space at its two ends, as the parser gives the value of a
declaration. -/
def trim (v : Value) : Value := ((v.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- **The value of a text**: the tokens of the text, each run of whitespace tokens as one,
parsed as a list of component values, with no white space at the two ends. A caller who has
only a string comes in here. A comment in the text is dropped: the white space on its two sides
is two whitespace tokens to the tokenizer, and one here. -/
def ofText (text : String) : Value :=
  trim (parseComponentValues (collapse (tokenizeText text)))

/-- The text of a value. -/
def text (v : Value) : String := Component.textAll v

end Value

/-! ## An expression of `calc()` -/

/-- An expression of `calc()`: a leaf, or two expressions under one of the four operators. A
leaf is a number, a dimension, a per cent, a keyword, or a function such as `var()`. -/
inductive Calc where
  | leaf (c : Component)
  | add (a b : Calc)
  | sub (a b : Calc)
  | mul (a b : Calc)
  | div (a b : Calc)

instance : Coe Component Calc := ⟨.leaf⟩

namespace Calc

/-- The expression is a sum or a difference. -/
def isSum : Calc → Bool
  | .add _ _ | .sub _ _ => true
  | _ => false

/-- The expression is a product or a quotient. -/
def isProduct : Calc → Bool
  | .mul _ _ | .div _ _ => true
  | _ => false

/-- A value, in parentheses where `wrap`. -/
def group (wrap : Bool) (v : Value) : Value := if wrap then [.parens v] else v

/-- Two values with an operator between them, and a space on each side of it. CSS asks for
white space on both sides of `+` and `-`, and takes it around `*` and `/`. -/
def around (op : Char) (a b : Value) : Value := a ++ .space :: .delim op :: .space :: b

/-- **The components of an expression.** A sum under a product or a quotient stands in
parentheses, and so does a sum that is taken away and a product that is divided by: the text
means what the tree says. -/
def value : Calc → Value
  | .leaf c => [c]
  | .add a b => around '+' a.value b.value
  | .sub a b => around '-' a.value (group b.isSum b.value)
  | .mul a b => around '*' (group a.isSum a.value) (group b.isSum b.value)
  | .div a b => around '/' (group a.isSum a.value) (group (b.isSum || b.isProduct) b.value)

end Calc

/-- **`calc()` of an expression.** -/
def Component.calc (e : Calc) : Component := .function ['c', 'a', 'l', 'c'] e.value

/-! ## Preludes -/

namespace Prelude

/-- **The prelude of a text**, for a caller who has a selector or a query as a string:
`Value.ofText` at this type. -/
def ofText (text : String) : Prelude := Value.ofText text

/-- The text of a prelude. -/
def text (p : Prelude) : String := Component.textAll p

/-- A class selector: `.e4-text`. -/
def «class» (name : String) : Prelude := [.delim '.', .ident name]

/-- A type selector: `path`, `h1`. -/
def type (name : String) : Prelude := [.ident name]

/-- An ID selector: `#fig3`. -/
def id (name : String) : Prelude := [.hash name]

/-- An attribute selector with a value: `[data-track="m-0"]`. The value is a string, so it
holds any text. -/
def attr (name value : String) : Prelude :=
  [.brackets [.ident name, .delim '=', .string value]]

/-- A pseudo-class: `:hover`. -/
def pseudo (name : String) : Prelude := [.colon, .ident name]

/-- `:root`. -/
def root : Prelude := pseudo "root"

/-- A media feature in its parentheses: `(prefers-reduced-motion: reduce)`. -/
def feature (name : String) (value : Value) : Prelude :=
  [.parens (.ident name :: .colon :: .space :: value)]

/-- `from`: the selector of the first keyframe. -/
def «from» : Prelude := [.ident "from"]

/-- `to`: the selector of the last keyframe. -/
def to : Prelude := [.ident "to"]

/-- A per cent: the selector of a keyframe between the two ends. -/
def percent (q : Rat) : Prelude := [.percent q]

end Prelude

/-! ## Declarations -/

namespace Declaration

/-- **A declaration** of a name, as a caller spells it, and a value. -/
def of (name : String) (value : Value) (important : Bool := false) : Declaration :=
  { name := name.toList, value := value, important := important }

/-- **A declaration of a custom property**: `--t: 400`. The name has its two hyphen-minus put
before it where it has none. -/
def custom (name : String) (value : Value) : Declaration :=
  { name := dashed name.toList, value := value }

end Declaration

/-! ## What a built value satisfies -/

/-- **Whether no two tokens that stand next to each other need a comment between them.** The
text of such a list is the texts of its tokens and nothing else (`serialize_of_quiet`). -/
def Quiet : List Token → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => !needsComment a b && Quiet (b :: rest)

namespace Component

/-- Whether a writer may write the component value: its tokens are `Writable`. -/
def writable (c : Component) : Bool := Writable c.tokens

/-- Whether the text of the component value holds no comment: its tokens are `Quiet`. -/
def quiet (c : Component) : Bool := Quiet c.tokens

end Component

namespace Value

/-- **Whether a writer may write the value**: its tokens are `Writable`. -/
def writable (v : Value) : Bool := Writable (Component.tokensAll v)

/-- **Whether the text of the value holds no comment**: its tokens are `Quiet`. -/
def quiet (v : Value) : Bool := Quiet (Component.tokensAll v)

end Value

namespace Calc

/-- Whether a writer may write each leaf of an expression. -/
def writable : Calc → Bool
  | .leaf c => c.writable
  | .add a b => a.writable && b.writable
  | .sub a b => a.writable && b.writable
  | .mul a b => a.writable && b.writable
  | .div a b => a.writable && b.writable

/-- Whether the text of each leaf of an expression holds no comment. -/
def quiet : Calc → Bool
  | .leaf c => c.quiet
  | .add a b => a.quiet && b.quiet
  | .sub a b => a.quiet && b.quiet
  | .mul a b => a.quiet && b.quiet
  | .div a b => a.quiet && b.quiet

end Calc

end Whatwg.Css.Syntax
