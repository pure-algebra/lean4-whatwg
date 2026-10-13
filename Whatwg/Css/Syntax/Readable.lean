import Whatwg.Css.Syntax.Parse

/-!
# Whatwg.Css.Syntax.Readable

Owner: the test of whether the parser reads a tree back from what the writer wrote of it (slice
K4 of `docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

`Whatwg/Css/Syntax/Write.lean` writes every tree. Not every tree comes back: a value of the
types of `Whatwg/Css/Syntax/Tree.lean` can hold what no parse gives, such as a right parenthesis
loose inside a function, or a declaration whose value ends in white space. This module says which
trees come back, as tests that compute:

- `Component.readable`, `Component.readableAll`: a component value, and a row of them up to a
  token that ends the row;
- `Declaration.readable`: a declaration;
- `Rule.readable`, `Rule.readableAll`: a rule, and the child rules of a block;
- `Stylesheet.readable`: a stylesheet;
- `Stylesheet.writable`, `Stylesheet.writableLines`: what the text of a stylesheet needs
  besides, on one line and with a line for each rule, so that its tokens come back from the
  text.

A caller checks a tree with `#guard` or `decide`. The laws that take these tests as their premise
are in `Whatwg/Css/Syntax/Parse/Laws.lean`. Each docstring says what each clause of a test
excludes, and `WhatwgTest/Css/Parse.lean` shows each excluded tree read back as another.

What this module does not claim: that a tree outside a test does not come back. Each test is
enough for its law. One clause is known to be stricter than a round trip needs
(`declarationLike`, in `Rule.readable`), and its docstring says so. Nor is it claimed that every
tree the parser returns passes the tests: a rule in a block whose prelude is an identifier and a
colon alone is returned for `a { b: {} c { } }`, and that clause excludes it.
-/

namespace Whatwg.Css.Syntax

/-- The first token of a component value's tokens. -/
def Component.head : Component → Token
  | .token t => t
  | .function name _ => .function name
  | .block bracket _ => bracket.opening

mutual

/-- **Whether the parser reads a component value back.**

- A token is a preserved token. The others open a function or a block, and the parser never
  leaves one as a token.
- The value of a function has no right parenthesis at its top, and the value of a block has no
  token at its top that closes the block: the parser would end the function or the block there.
- Every component value inside is readable. -/
def Component.readable : Component → Bool
  | .token t => t.preserved
  | .function _ value => Component.readableAll (· == .closeParen) value
  | .block bracket value => Component.readableAll (· == bracket.closing) value

/-- **Whether the parser reads a row of component values back, up to a token that `ends` the
row.** Each is readable, and none opens with a token that ends the row. -/
def Component.readableAll (ends : Token → Bool) : List Component → Bool
  | [] => true
  | c :: rest => !ends c.head && Component.readable c && Component.readableAll ends rest

end

/-- Whether a list of tokens stops a row that `ends` ends: it is empty, or it opens with a token
that ends the row. -/
def stopsAt (ends : Token → Bool) : List Token → Bool
  | [] => true
  | token :: _ => ends token

/-- **Whether the parser reads a declaration back**, in a block (`nested`) or in a `style`
attribute.

- Its value is a readable row up to a semicolon: no semicolon at its top, and in a block no
  right curly bracket at its top. The parser ends the value there.
- Its value does not open with white space, and does not end with white space: the parser drops
  both (steps 4 and 7 of `consume a declaration`).
- Where the flag `important` is not set, the value does not end with `!` and `important`: the
  parser would take them for the flag (step 6).
- Where the name is not a custom property's, the value does not hold a block in curly brackets
  beside another value: the parser returns nothing for it (step 8). -/
def Declaration.readable (nested : Bool) (d : Declaration) : Bool :=
  Component.readableAll (endsList (some .semicolon) nested) d.value &&
  !d.value.head?.any Component.isWhitespace &&
  !d.value.getLast?.any Component.isWhitespace &&
  (d.important || !(takeImportant d.value).2) &&
  (isCustomPropertyName d.name || !blockAmongOthers d.value)

/-- Whether a rule is a nested declarations rule. -/
def Rule.isNested : Rule → Bool
  | .nested _ => true
  | _ => false

/-- The stop token of a qualified rule: a semicolon in a block, and none at the top of a
stylesheet. -/
def stopOf (nested : Bool) : Option Token := if nested then some .semicolon else none

/-- Whether a prelude is an identifier, a colon, and nothing else but white space: `a: {}`.
In a block the parser first reads a rule as a declaration, and for such a prelude what follows
the rule decides whether that succeeds. -/
def declarationLike : List Component → Bool
  | .token (.ident _) :: rest =>
    match rest.dropWhile Component.isWhitespace with
    | .token .colon :: after => after.all Component.isWhitespace
    | _ => false
  | _ => false

/-- Whether the first component value of a qualified rule's prelude lets the rule start: it is
not white space, which the parser discards before a rule; not an at-keyword token, which starts
an at-rule; and at the top of a stylesheet not a CDO or a CDC token, which the parser discards
there. An empty prelude starts with the block. -/
def preludeOpens (nested : Bool) : List Component → Bool
  | [] => true
  | c :: _ =>
    !c.isWhitespace && c.head.atKeyword?.isNone && (nested || (c.head != .cdo && c.head != .cdc))

mutual

/-- **Whether the parser reads a rule back**, in a block (`nested`) or at the top of a
stylesheet.

An at-rule:

- its prelude is a readable row up to a semicolon or a left curly bracket: none of the two at
  its top (a block in curly brackets at the top of a prelude would be read as the rule's block),
  and in a block no right curly bracket at its top;
- for a block at-rule, the block is readable (below).

A qualified rule:

- its prelude is a readable row up to a left curly bracket, and in a block up to a semicolon or
  a right curly bracket as well;
- its prelude starts a rule (`preludeOpens`);
- its prelude does not start as a custom property does (`startsAsCustomProperty`): the parser
  returns nothing for `--x:hover { }`;
- in a block, its prelude is not `declarationLike`. This clause is stricter than needed: `a: {}`
  before another rule is read as a rule;
- its block is readable.

A nested declarations rule stands in a block only, holds a declaration at least, and each of its
declarations is readable.

A block is readable where each declaration is readable, the child rules are (`Rule.readableAll`),
and the first child rule is not a nested declarations rule: its declarations would be read as
the block's own. -/
def Rule.readable (nested : Bool) : Rule → Bool
  | .statement _ prelude => Component.readableAll (endsPrelude (some .semicolon) nested) prelude
  | .blockAt _ prelude declarations rules =>
    Component.readableAll (endsPrelude (some .semicolon) nested) prelude &&
    declarations.all (Declaration.readable true) &&
    !rules.head?.any Rule.isNested && Rule.readableAll rules
  | .qualified prelude declarations rules =>
    Component.readableAll (endsPrelude (stopOf nested) nested) prelude &&
    preludeOpens nested prelude && !startsAsCustomProperty prelude &&
    !(nested && declarationLike prelude) &&
    declarations.all (Declaration.readable true) &&
    !rules.head?.any Rule.isNested && Rule.readableAll rules
  | .nested declarations =>
    nested && !declarations.isEmpty && declarations.all (Declaration.readable true)

/-- **Whether the parser reads the child rules of a block back.** Each is readable in a block,
and no two nested declarations rules stand together: the parser would read them as one. -/
def Rule.readableAll : List Rule → Bool
  | [] => true
  | r :: rest =>
    Rule.readable true r && !(r.isNested && rest.head?.any Rule.isNested) && Rule.readableAll rest

end

/-- **Whether the parser reads a stylesheet back**: each of its rules is readable at the top of
a stylesheet. So none is a nested declarations rule. -/
def Stylesheet.readable (s : Stylesheet) : Bool := s.rules.all (Rule.readable false)

/-- **Whether the tokens of a text come back from the text.**

- The tokens are `Writable`: the premise of `tokenize_serialize`.
- No two whitespace tokens stand together: the tokenizer gives one token for a run of white
  space.
- The text is its own preprocessing: it has no carriage return, no form feed and no U+0000.
  `Writable` admits a delimiter that holds one of the three, since `tokenize` reads a list of
  code points that was preprocessed; `tokenizeText` preprocesses, and would change it. -/
def writableText (tokens : List Token) : Bool :=
  Writable tokens && noWhitespaceRun tokens &&
    filterCodePoints (serialize tokens) == serialize tokens

/-- **Whether the parser reads a stylesheet back from its text**: its tokens come back from the
text, and the stylesheet is readable. -/
def Stylesheet.writable (s : Stylesheet) : Bool := writableText s.tokens && s.readable

/-- The code points of the lines of a row of rules: the text of each rule, and a line feed
between two. These are the code points of `Stylesheet.lines`
(`Stylesheet.lines_toList` in `Whatwg/Css/Syntax/Parse/Lines.lean`). -/
def Rule.linesText : List Rule → List Char
  | [] => []
  | [r] => serialize r.tokens
  | r :: s :: rest => serialize r.tokens ++ '\n' :: Rule.linesText (s :: rest)

/-- **Whether the parser reads a stylesheet back from its lines** (`Stylesheet.lines`): the
tokens of each rule are `Writable` with no two whitespace tokens together, the text of the lines
is its own preprocessing, and the stylesheet is readable. -/
def Stylesheet.writableLines (s : Stylesheet) : Bool :=
  s.rules.all (fun r => Writable r.tokens && noWhitespaceRun r.tokens) &&
    filterCodePoints (Rule.linesText s.rules) == Rule.linesText s.rules && s.readable

end Whatwg.Css.Syntax
