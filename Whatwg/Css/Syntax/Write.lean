import Whatwg.Css.Syntax.Serialize

/-!
# Whatwg.Css.Syntax.Write

Owner: the tree of CSS as tokens and as text, and the test of whether two trees are one (slice K4
of `docs/CSS-PACKAGE-PLAN.md`; ruling CS-9: one tree is written and read).

`Whatwg/Css/Syntax/Tree.lean` has the tree that parsing gives. This module writes it: a tree as
the tokens that the parser of CSS Syntax Module Level 3 reads back as that tree, and those tokens
as text by `serialize` (`Whatwg/Css/Syntax/Serialize.lean`).

- `Component.tokens`: a preserved token is itself; a function is its function token, its value
  and a right parenthesis; a simple block is its value between its two brackets.
- `Declaration.tokens`: `name: value`, and ` !important` where the flag is set.
  `Declaration.tokensAll`: declarations in a row, with `; ` between two. This is what a `style`
  attribute holds.
- `Rule.tokens`: a qualified rule is its prelude and its block; an at-rule is its at-keyword, its
  prelude, and its block or a semicolon. A block is `{ declarations; rules }`, the declarations
  first. A nested declarations rule is its declarations, with a semicolon after them where
  another rule follows.
- `Stylesheet.tokens`: the rules with a whitespace token between two.
- `Component.text`, `Declaration.text`, `Rule.text`, `Stylesheet.text`: the text of each, a
  `String`. `Stylesheet.lines`: the same sheet with a line break between two rules where
  `Stylesheet.text` has a space.

Where a writer puts white space. The parser keeps a whitespace token inside a prelude and inside
a value, so that white space belongs to the tree: the prelude of `.a { }` holds the whitespace
token before the brace, and the value of `translate: 1px 2px` holds the one between the two
lengths. The parser drops white space after the colon of a declaration, at the two ends of a
declaration's value, between two declarations, inside a brace next to it, and between two rules.
The writer puts one whitespace token at each of those places, so the text reads as people write
CSS.

Two trees are told apart by `==` and `=` (`Component.beq_iff`, `Rule.beq_iff`): a tree holds
lists of itself, and for such a type the test is written here by recursion on the tree.

What this module does not claim: that the parser reads these tokens back as the tree. That is
the law of slice K4, and it needs a premise on the tree (a value with no whitespace at its ends,
no semicolon at the top of a value, and so on).
-/

namespace Whatwg.Css.Syntax

namespace Bracket

/-- The token that opens a simple block. -/
def opening : Bracket → Token
  | .square => .openSquare
  | .paren => .openParen
  | .curly => .openCurly

/-- The token that closes a simple block: the mirror of the one that opens it. -/
def closing : Bracket → Token
  | .square => .closeSquare
  | .paren => .closeParen
  | .curly => .closeCurly

end Bracket

/-! ## The tokens of a tree -/

mutual

/-- The tokens of a component value. -/
def Component.tokens : Component → List Token
  | .token t => [t]
  | .function name value => Token.function name :: (Component.tokensAll value ++ [Token.closeParen])
  | .block bracket value => bracket.opening :: (Component.tokensAll value ++ [bracket.closing])

/-- The tokens of component values in a row. -/
def Component.tokensAll : List Component → List Token
  | [] => []
  | c :: rest => c.tokens ++ Component.tokensAll rest

end

namespace Declaration

/-- The tokens of a declaration: `name: value`, and ` !important` where the flag is set. -/
def tokens (d : Declaration) : List Token :=
  Token.ident d.name :: Token.colon :: Token.whitespace :: (Component.tokensAll d.value ++
    (if d.important then [Token.whitespace, Token.delim '!', Token.ident "important".toList]
    else []))

/-- The tokens of declarations in a row, with `; ` between two and nothing after the last. -/
def tokensAll : List Declaration → List Token
  | [] => []
  | [d] => d.tokens
  | d :: e :: rest => d.tokens ++ Token.semicolon :: Token.whitespace :: tokensAll (e :: rest)

end Declaration

/-- A block, from the tokens of its declarations and the tokens of its child rules: `{ }` where
both are empty, and `{ declarations; rules }`. -/
def blockTokens (declarations rules : List Token) : List Token :=
  let inner :=
    if declarations.isEmpty then rules
    else if rules.isEmpty then declarations
    else declarations ++ Token.semicolon :: Token.whitespace :: rules
  if inner.isEmpty then [Token.openCurly, Token.whitespace, Token.closeCurly]
  else Token.openCurly :: Token.whitespace :: (inner ++ [Token.whitespace, Token.closeCurly])

/-- What stands after a rule that another follows in a block: a whitespace token, and a semicolon
first after a nested declarations rule, whose last declaration would else read on into the next
rule. -/
def Rule.gap : Rule → List Token
  | .nested _ => [Token.semicolon, Token.whitespace]
  | _ => [Token.whitespace]

mutual

/-- The tokens of a rule. -/
def Rule.tokens : Rule → List Token
  | .statement name prelude =>
    Token.atKeyword name :: (Component.tokensAll prelude ++ [Token.semicolon])
  | .blockAt name prelude declarations rules =>
    Token.atKeyword name :: (Component.tokensAll prelude ++
      blockTokens (Declaration.tokensAll declarations) (Rule.tokensAll rules))
  | .qualified prelude declarations rules =>
    Component.tokensAll prelude ++
      blockTokens (Declaration.tokensAll declarations) (Rule.tokensAll rules)
  | .nested declarations => Declaration.tokensAll declarations

/-- The tokens of rules in a row, with `Rule.gap` between two. -/
def Rule.tokensAll : List Rule → List Token
  | [] => []
  | [r] => r.tokens
  | r :: s :: rest => r.tokens ++ (Rule.gap r ++ Rule.tokensAll (s :: rest))

end

/-- The tokens of a stylesheet. -/
def Stylesheet.tokens (s : Stylesheet) : List Token := Rule.tokensAll s.rules

/-! ## The text of a tree -/

/-- The text of component values in a row: a value, a prelude. -/
def Component.textAll (value : List Component) : String :=
  String.ofList (serialize (Component.tokensAll value))

/-- The text of one component value. -/
def Component.text (c : Component) : String := String.ofList (serialize c.tokens)

/-- The text of a declaration. -/
def Declaration.text (d : Declaration) : String := String.ofList (serialize d.tokens)

/-- The text of declarations in a row: what a `style` attribute holds. -/
def Declaration.textAll (ds : List Declaration) : String :=
  String.ofList (serialize (Declaration.tokensAll ds))

/-- The text of a rule, on one line. -/
def Rule.text (r : Rule) : String := String.ofList (serialize r.tokens)

/-- The text of a stylesheet, on one line: the text of its tokens. -/
def Stylesheet.text (s : Stylesheet) : String := String.ofList (serialize s.tokens)

/-- The text of a stylesheet, one rule a line. -/
def Stylesheet.lines (s : Stylesheet) : String := "\n".intercalate (s.rules.map Rule.text)

/-! ## Telling two trees apart -/

mutual

/-- Whether two component values are one. -/
def Component.beq : Component → Component → Bool
  | .token t, .token t' => t == t'
  | .function n v, .function n' v' => n == n' && Component.beqAll v v'
  | .block b v, .block b' v' => b == b' && Component.beqAll v v'
  | .token _, .function _ _ => false
  | .token _, .block _ _ => false
  | .function _ _, .token _ => false
  | .function _ _, .block _ _ => false
  | .block _ _, .token _ => false
  | .block _ _, .function _ _ => false

/-- Whether two rows of component values are one row. -/
def Component.beqAll : List Component → List Component → Bool
  | [], [] => true
  | c :: cs, c' :: cs' => Component.beq c c' && Component.beqAll cs cs'
  | [], _ :: _ => false
  | _ :: _, [] => false

end

mutual

/-- The test of two component values answers yes exactly when they are one. -/
theorem Component.beq_iff : ∀ a b : Component, Component.beq a b = true ↔ a = b
  | .token t, .token t' => by
    simp only [Component.beq, beq_iff_eq, Component.token.injEq]
  | .function n v, .function n' v' => by
    simp only [Component.beq, Bool.and_eq_true, beq_iff_eq, Component.function.injEq,
      Component.beqAll_iff v v']
  | .block b v, .block b' v' => by
    simp only [Component.beq, Bool.and_eq_true, beq_iff_eq, Component.block.injEq,
      Component.beqAll_iff v v']
  | .token _, .function _ _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]
  | .token _, .block _ _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]
  | .function _ _, .token _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]
  | .function _ _, .block _ _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]
  | .block _ _, .token _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]
  | .block _ _, .function _ _ => by simp only [Component.beq, Bool.false_eq_true, reduceCtorEq]

/-- The test of two rows of component values answers yes exactly when they are one row. -/
theorem Component.beqAll_iff : ∀ a b : List Component, Component.beqAll a b = true ↔ a = b
  | [], [] => by simp only [Component.beqAll]
  | c :: cs, c' :: cs' => by
    simp only [Component.beqAll, Bool.and_eq_true, Component.beq_iff c c',
      Component.beqAll_iff cs cs', List.cons.injEq]
  | [], _ :: _ => by simp only [Component.beqAll, Bool.false_eq_true, reduceCtorEq]
  | _ :: _, [] => by simp only [Component.beqAll, Bool.false_eq_true, reduceCtorEq]

end

instance : DecidableEq Component := fun a b => decidable_of_iff _ (Component.beq_iff a b)

deriving instance DecidableEq for Declaration

mutual

/-- Whether two rules are one rule. -/
def Rule.beq : Rule → Rule → Bool
  | .statement n p, .statement n' p' => n == n' && p == p'
  | .blockAt n p ds rs, .blockAt n' p' ds' rs' =>
    n == n' && p == p' && ds == ds' && Rule.beqAll rs rs'
  | .qualified p ds rs, .qualified p' ds' rs' => p == p' && ds == ds' && Rule.beqAll rs rs'
  | .nested ds, .nested ds' => ds == ds'
  | .statement _ _, .blockAt _ _ _ _ => false
  | .statement _ _, .qualified _ _ _ => false
  | .statement _ _, .nested _ => false
  | .blockAt _ _ _ _, .statement _ _ => false
  | .blockAt _ _ _ _, .qualified _ _ _ => false
  | .blockAt _ _ _ _, .nested _ => false
  | .qualified _ _ _, .statement _ _ => false
  | .qualified _ _ _, .blockAt _ _ _ _ => false
  | .qualified _ _ _, .nested _ => false
  | .nested _, .statement _ _ => false
  | .nested _, .blockAt _ _ _ _ => false
  | .nested _, .qualified _ _ _ => false

/-- Whether two rows of rules are one row. -/
def Rule.beqAll : List Rule → List Rule → Bool
  | [], [] => true
  | r :: rs, r' :: rs' => Rule.beq r r' && Rule.beqAll rs rs'
  | [], _ :: _ => false
  | _ :: _, [] => false

end

mutual

/-- The test of two rules answers yes exactly when they are one rule. -/
theorem Rule.beq_iff : ∀ a b : Rule, Rule.beq a b = true ↔ a = b
  | .statement n p, .statement n' p' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.statement.injEq]
  | .blockAt n p ds rs, .blockAt n' p' ds' rs' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.blockAt.injEq,
      Rule.beqAll_iff rs rs', and_assoc]
  | .qualified p ds rs, .qualified p' ds' rs' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.qualified.injEq,
      Rule.beqAll_iff rs rs', and_assoc]
  | .nested ds, .nested ds' => by simp only [Rule.beq, beq_iff_eq, Rule.nested.injEq]
  | .statement _ _, .blockAt _ _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .statement _ _, .qualified _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .statement _ _, .nested _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .blockAt _ _ _ _, .statement _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .blockAt _ _ _ _, .qualified _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .blockAt _ _ _ _, .nested _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .qualified _ _ _, .statement _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .qualified _ _ _, .blockAt _ _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .qualified _ _ _, .nested _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .nested _, .statement _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .nested _, .blockAt _ _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .nested _, .qualified _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]

/-- The test of two rows of rules answers yes exactly when they are one row. -/
theorem Rule.beqAll_iff : ∀ a b : List Rule, Rule.beqAll a b = true ↔ a = b
  | [], [] => by simp only [Rule.beqAll]
  | r :: rs, r' :: rs' => by
    simp only [Rule.beqAll, Bool.and_eq_true, Rule.beq_iff r r', Rule.beqAll_iff rs rs',
      List.cons.injEq]
  | [], _ :: _ => by simp only [Rule.beqAll, Bool.false_eq_true, reduceCtorEq]
  | _ :: _, [] => by simp only [Rule.beqAll, Bool.false_eq_true, reduceCtorEq]

end

instance : DecidableEq Rule := fun a b => decidable_of_iff _ (Rule.beq_iff a b)

deriving instance DecidableEq for Stylesheet

end Whatwg.Css.Syntax
