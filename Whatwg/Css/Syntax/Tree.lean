
/-!
# Whatwg.Css.Syntax.Tree

Owner: the tokens of CSS and the tree that parsing gives (slice K2 of
`docs/CSS-PACKAGE-PLAN.md`; rulings CS-6 and CS-9).

The authority is CSS Syntax Module Level 3, sealed at
`vendor/w3c-csswg-drafts-50337328/css-syntax-3/Overview.bs`: the list of tokens under the
heading `tokenization`, and the results of parsing under `css-tree`.

- `Token`: one constructor for each token of the standard's list, with what the standard says
  each carries: a value of code points, a type flag, a numeric value with its sign character, a
  unit.
- `Component`: a component value, which is a preserved token, a function or a simple block.
- `Declaration`, `Rule`, `Stylesheet`: what the standard's parser gives.

One tree is written and read: a writer builds these values and a parser returns them.

A value of code points is a `List Char`, as the tokenizer reads a list of code points; `String`
is a spelling of it for a caller (`Token.ofIdent`). A numeric value is a rational number: the
standard gives it by arithmetic on the digits (`convert a string to a number`).

What this module does not claim: that a value is one the tokenizer can give. An identifier with
no code point, a delimiter that the tokenizer would read as another token, and a number that no
decimal text writes are all values of these types. The serializer states what it asks of a
token.
-/

namespace Whatwg.Css.Syntax

/-- The type flag of a hash token: "id" where its value is an identifier. -/
inductive HashFlag where
  | id
  | unrestricted
  deriving DecidableEq, Repr, Inhabited

/-- The type flag of a number: "integer" where its text had no fraction and no exponent. -/
inductive NumberFlag where
  | integer
  | number
  deriving DecidableEq, Repr, Inhabited

/-- The sign character of a number, where its text had one. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq, Repr, Inhabited

/-- The numeric value of a token and its sign character. -/
structure Numeric where
  value : Rat
  sign : Option Sign := none
  deriving DecidableEq, Repr, Inhabited

/-- A token of CSS: the output of tokenization. -/
inductive Token where
  | ident (value : List Char)
  | function (value : List Char)
  | atKeyword (value : List Char)
  | hash (value : List Char) (flag : HashFlag)
  | string (value : List Char)
  | badString
  | url (value : List Char)
  | badUrl
  | delim (value : Char)
  | number (n : Numeric) (flag : NumberFlag)
  | percentage (n : Numeric)
  | dimension (n : Numeric) (flag : NumberFlag) (unit : List Char)
  | unicodeRange (start stop : Nat)
  | whitespace
  | cdo
  | cdc
  | colon
  | semicolon
  | comma
  | openSquare
  | closeSquare
  | openParen
  | closeParen
  | openCurly
  | closeCurly
  deriving DecidableEq, Repr, Inhabited

namespace Token

/-- The identifier token of a string. -/
def ofIdent (s : String) : Token := .ident s.toList

/-- A preserved token: any token but a function token and the three that open a block, which
parsing always takes into a function or a simple block. -/
def preserved : Token → Bool
  | .function _ | .openSquare | .openParen | .openCurly => false
  | _ => true

end Token

/-- The token that opens a simple block. -/
inductive Bracket where
  | square
  | paren
  | curly
  deriving DecidableEq, Repr, Inhabited

/-- A component value: a preserved token, a function with its value, or a simple block with its
value. -/
inductive Component where
  | token (t : Token)
  | function (name : List Char) (value : List Component)
  | block (bracket : Bracket) (value : List Component)
  deriving Inhabited

/-- A declaration: a name, a value, and the `important` flag. -/
structure Declaration where
  name : List Char
  value : List Component
  important : Bool := false
  deriving Inhabited

/-- A rule: an at-rule that ends in a semicolon, an at-rule that ends in a block, a qualified
rule, or a nested declarations rule. A block holds a list of declarations and a list of child
rules.

The standard's `consume a block's contents` gives rules and lists of declarations in the order
they stand. The first list, where the block opens with one, is the block's declarations. Each
later list stands among the child rules as a nested declarations rule (`consume a qualified
rule`), so the order of a block is kept. -/
inductive Rule where
  | statement (name : List Char) (prelude : List Component)
  | blockAt (name : List Char) (prelude : List Component) (declarations : List Declaration)
      (rules : List Rule)
  | qualified (prelude : List Component) (declarations : List Declaration) (rules : List Rule)
  | nested (declarations : List Declaration)
  deriving Inhabited

/-- A stylesheet: a list of rules. -/
structure Stylesheet where
  rules : List Rule
  deriving Inhabited

end Whatwg.Css.Syntax
