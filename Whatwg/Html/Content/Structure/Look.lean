import Whatwg.Css.Syntax.Build

/-!
# Whatwg.Html.Content.Structure.Look

Owner: the values that a sheet takes from a look, as types (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entry W14 of `docs/research/2026-10-12-whatwg-requests.md`: "the
values taken from a look's custom properties").

A look is the one place where a colour and a family are written down: each is a custom property
with a name. A sheet that draws with the look says `var(--name)`, and never the colour. The
consumer holds that rule today by a check on the tokens of its sheet. This module makes it a
type: a declaration of a property that carries a colour or a family is built from a token of
the look, and there is no constructor that takes a literal.

- `Kind`: the kinds of token that a sheet tells apart: a colour, a family, and any other (a
  size, a weight, a style, a number).
- `Look τ`: the class of a look's tokens. The tokens are a type of the consumer's, indexed by
  kind (`τ : Kind → Type`), and the instance gives each the name of its custom property. No name
  of a look stands in this package. `Look.var token` is `var(--name)`.
- `Paint τ`: a colour as a sheet may say one: a colour token, `currentColor`, `inherit`, no
  paint (`none`), or a mix of two paints. `Share τ` is how much of the first a mix takes.
  `Paint.value` writes one.
- `Decl τ`: a declaration. `colour` and `line` take their colour as a `Paint`, and `noLine` is
  a line with none; `family` and `font` take their family as a family token; `plain` is every
  other property: its name is refused, by a proof that `decide` finds, where the name is one
  that carries a colour or a family (`carries`). `Decl.declaration` is the declaration of the
  tree.
- `Definition τ`: a token defined on the root from other tokens: a colour from a paint, a
  family from a family, another from any value.

```
.colour "color" (.token .ink)                             -- color: var(--e4-color-ink)
.line "border-top" (Look.var .rule) "solid" (.token .line)  -- border-top: var(--…) solid var(--…)
.family .label                                            -- font-family: var(--e4-font-label-family)
.plain "margin" [.int 0]                                  -- margin: 0
.plain "color" [.hash "fff"]                              -- does not elaborate: `color` carries a colour
.colour "color" (.hash "fff")                             -- does not elaborate: a hash is no paint
```

So "emphasis is a function from a status to a tone" is an ordinary function into `τ .colour`,
and a rule of each status takes `.colour "color" (.token (emphasis status))`.

What the types give. A declaration of a typed sheet names a property of `carries` exactly when
it is not a plain one (`Decl.carries_iff` of the sheet's laws). So the value of such a property
is a `Paint`, a line that ends in a `Paint`, or a family token: a literal has no way in.

What this module does not claim.

- **That the lists are those of CSS.** `colourProperties`, `lineProperties` and
  `untypedCarriers` are from memory of CSS: of the modules that define them only CSS Color 4 is
  sealed here, and it defines `color` alone. A property that is missing from the lists is a
  plain one, and takes any value.
- That a plain value holds no colour. `text-decoration`, `list-style` and `content` are
  shorthands or take an image, and can carry a colour; they are plain here, since a sheet needs
  them with none (`text-decoration: underline`). `.plain "text-decoration" [.ident "red"]`
  elaborates.
- That the width of a line and what stands before a family are no colour: they are component
  values of the caller's.
- That a value is one of its property: `.colour "color" .clear` writes `color: none`, which CSS
  refuses. The grammar of a property is judged by `Whatwg/Css/Values/Admits.lean`.
- A shadow, a filter and an image have no typed declaration: a sheet of this type has none.
  `!important` has none either.
- A property name in upper case is refused by `plain`, so that a name is compared as written:
  CSS reads `COLOR` as `color`.

Every definition here that takes a `String` reaches `Classical.choice` through `String.toList`
of core. `Whatwg.Html` is under the ordinary axiom ceiling.
-/

namespace Whatwg.Html.Content.Structure

open Whatwg.Css.Syntax (Component Value Declaration)

/-! ## A look's tokens -/

/-- The kinds of token that a sheet tells apart. -/
inductive Kind where
  /-- A colour. -/
  | colour
  /-- A family of a face. -/
  | family
  /-- Any other token: a size, a weight, a style, a number. A sheet asks nothing of it. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- **A look's tokens**: a type of the consumer's, indexed by kind, whose every value names a
custom property. A sheet takes its colours and its families from such a type and from nowhere
else. -/
class Look (τ : Kind → Type) where
  /-- The name of the token's custom property, with its two hyphen-minus or without. -/
  property : {kind : Kind} → τ kind → String

/-- **A reference to a token**: `var(--name)`. -/
def Look.var {τ : Kind → Type} [Look τ] {kind : Kind} (token : τ kind) : Component :=
  Component.var (Look.property token)

/-! ## A colour -/

/-- How much of the first colour a mix takes. -/
inductive Share (τ : Kind → Type) where
  /-- A per cent. -/
  | percent (q : Rat)
  /-- A token that holds a number from 0 to 1, as a per cent: `calc(var(--name) * 100%)`. -/
  | tone (token : τ .other)

/-- **A colour as a sheet may say one.** No constructor takes a literal. -/
inductive Paint (τ : Kind → Type) where
  /-- A colour of the look: `var(--name)`. -/
  | token (colour : τ .colour)
  /-- The colour of the text: `currentColor`. -/
  | current
  /-- The colour of the parent: `inherit`. -/
  | inherit
  /-- No paint: `none`, for a property that takes it (`background`, `border`, `fill`). -/
  | clear
  /-- A mix of two paints in sRGB: `color-mix(in srgb, a share, b)`. -/
  | mix (a : Paint τ) (share : Share τ) (b : Paint τ)

variable {τ : Kind → Type}

/-- The component values of a share. -/
def Share.value [Look τ] : Share τ → Value
  | .percent q => [.percent q]
  | .tone token => [.calc (.mul (.leaf (Look.var token)) (.leaf (.percent 100)))]

/-- **The component values of a paint.** -/
def Paint.value [Look τ] : Paint τ → Value
  | .token colour => [Look.var colour]
  | .current => [.ident "currentColor"]
  | .inherit => [.ident "inherit"]
  | .clear => [.ident "none"]
  | .mix a share b =>
    [.call "color-mix"
      (Value.list [[.ident "in", .space, .ident "srgb"], a.value ++ .space :: share.value, b.value])]

/-! ## The properties that carry a colour or a family -/

/-- The properties whose whole value may be one colour. From memory of CSS. -/
def colourProperties : List String :=
  ["color", "background", "background-color", "border-color", "border-top-color",
    "border-right-color", "border-bottom-color", "border-left-color", "border-block-color",
    "border-inline-color", "border-block-start-color", "border-block-end-color",
    "border-inline-start-color", "border-inline-end-color", "outline-color",
    "text-decoration-color", "text-emphasis-color", "column-rule-color", "caret-color",
    "accent-color", "fill", "stroke", "stop-color", "flood-color", "lighting-color"]

/-- The properties of a line: a width, a style and a colour. From memory of CSS. -/
def lineProperties : List String :=
  ["border", "border-top", "border-right", "border-bottom", "border-left", "border-block",
    "border-inline", "border-block-start", "border-block-end", "border-inline-start",
    "border-inline-end", "outline", "column-rule"]

/-- The properties that carry a colour and have no typed declaration here: a shadow, a filter,
an image, which may be a gradient. From memory of CSS. -/
def untypedCarriers : List String :=
  ["box-shadow", "text-shadow", "filter", "backdrop-filter", "background-image", "border-image",
    "border-image-source", "mask", "mask-image", "list-style-image", "scrollbar-color"]

/-- Whether a property takes one colour as its whole value: a property of one colour, or a line
with its width and its style left out. -/
def takesColour (property : String) : Bool :=
  colourProperties.contains property || lineProperties.contains property

/-- Whether a property is a line. -/
def takesLine (property : String) : Bool := lineProperties.contains property

/-- Whether a name is not all in lower case, or is the name of a custom property. -/
def isOddName : List Char → Bool
  | '-' :: '-' :: _ => true
  | name => name.any Char.isUpper

/-- **Whether a property carries a colour or a family**, so that a plain declaration may not
name it: a property of the three lists, `font-family`, `font`, a custom property, and a name
with a letter in upper case. -/
def carries (name : String) : Bool :=
  takesColour name || name == "font-family" || name == "font" || untypedCarriers.contains name ||
    isOddName name.toList

/-! ## A declaration -/

/-- **A declaration of a sheet.** -/
inductive Decl (τ : Kind → Type) where
  /-- A property whose value is one colour: `color: var(--name)`. -/
  | colour (property : String) (paint : Paint τ)
      (known : takesColour property = true := by decide)
  /-- A line: `border-top: width style colour`. -/
  | line (property : String) (width : Component) (style : String) (paint : Paint τ)
      (known : takesLine property = true := by decide)
  /-- No line: `border: 0`. -/
  | noLine (property : String) (known : takesLine property = true := by decide)
  /-- `font-family`, of a family of the look. -/
  | family (face : τ .family)
  /-- `font`: what stands before the family (a weight, a size, a line height), then a family of
  the look. -/
  | font (before : Value) (face : τ .family)
  /-- Any other property, with its value. -/
  | plain (name : String) (value : Value) (free : carries name = false := by decide)

namespace Decl

/-- The name of the property. -/
def property : Decl τ → String
  | .colour property _ _ => property
  | .line property _ _ _ _ => property
  | .noLine property _ => property
  | .family _ => "font-family"
  | .font _ _ => "font"
  | .plain name _ _ => name

/-- Whether the declaration is a plain one. -/
def isPlain : Decl τ → Bool
  | .plain _ _ _ => true
  | _ => false

/-- The component values of the declaration. -/
def value [Look τ] : Decl τ → Value
  | .colour _ paint _ => paint.value
  | .line _ width style paint _ => width :: .space :: .ident style :: .space :: paint.value
  | .noLine _ _ => [.int 0]
  | .family face => [Look.var face]
  | .font before face => if before.isEmpty then [Look.var face] else before ++ [.space, Look.var face]
  | .plain _ value _ => value

/-- **The declaration of the tree.** -/
def declaration [Look τ] (d : Decl τ) : Declaration := .of d.property d.value

end Decl

/-! ## A token defined from tokens -/

/-- **The definition of a token** on the root, from other tokens: `--name: value`. A colour is
defined by a paint and a family by a family, so a look's rule holds of a token that a sheet
adds to the look. -/
inductive Definition (τ : Kind → Type) where
  | colour (token : τ .colour) (paint : Paint τ)
  | family (token : τ .family) (face : τ .family)
  | other (token : τ .other) (value : Value)

/-- The declaration of the tree: a custom property. -/
def Definition.declaration [Look τ] : Definition τ → Declaration
  | .colour token paint => .custom (Look.property token) paint.value
  | .family token face => .custom (Look.property token) [Look.var face]
  | .other token value => .custom (Look.property token) value

end Whatwg.Html.Content.Structure
