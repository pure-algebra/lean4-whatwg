import WhatwgGates.Ledger.Model

/-!
# WhatwgTest.Ledger.CssSyntax

The graph ledger's entry for `CSS-PG-SYNTAX`: the tokens of CSS, the tokenizer of CSS Syntax 3,
the writer of tokens, and the round trip between them (slice K2 of `docs/CSS-PACKAGE-PLAN.md`);
since slice K4 the parser, the tree as tokens and text, the round trip at a stylesheet, and the
builders of values that the picture kit writes with. `docs/CSS-SYNTAX-DAG.md` is the graph's
document. Ruling R-S36 of `COORDINATION.md` opened the graph and ruling R-S42 widened its fence;
neither changes an edge's status, so the entry acknowledges both.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The assurance graph of the syntax of CSS: a tokenizer, a parser, a writer and their round
trips. -/
def cssSyntax : Graph where
  id := "CSS-PG-SYNTAX"
  document := "docs/CSS-SYNTAX-DAG.md"
  fence := [`Whatwg.Css.Syntax.Tree, `Whatwg.Css.Syntax.Tokenize, `Whatwg.Css.Syntax.Serialize,
    `Whatwg.Css.Syntax.Laws, `Whatwg.Css.Syntax.Laws.Dispatch, `Whatwg.Css.Syntax.Laws.Name,
    `Whatwg.Css.Syntax.Laws.Number, `Whatwg.Css.Syntax.Laws.String,
    `Whatwg.Css.Syntax.Laws.Escape, `Whatwg.Css.Syntax.Laws.Token, `Whatwg.Css.Syntax.Laws.Text,
    `Whatwg.Css.Syntax.Write, `Whatwg.Css.Syntax.Parse, `Whatwg.Css.Syntax.Readable,
    `Whatwg.Css.Syntax.Located, `Whatwg.Css.Syntax.Parse.Component,
    `Whatwg.Css.Syntax.Parse.Declaration, `Whatwg.Css.Syntax.Parse.Step,
    `Whatwg.Css.Syntax.Parse.Rule, `Whatwg.Css.Syntax.Parse.Laws, `Whatwg.Css.Syntax.Parse.Lines,
    `Whatwg.Css.Syntax.Build, `Whatwg.Css.Syntax.Build.Laws,
    `Whatwg.Css.Syntax.Readable.Append]
  acknowledged := ["R-S36", "R-S42", "R-S47"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "no declaration record names each declaration's owner and the anchor of the algorithm it models; the docstrings name the heading identifiers of the sealed source"]
      grounds := [.declarations [`Whatwg.Css.Syntax.Token, `Whatwg.Css.Syntax.Numeric,
        `Whatwg.Css.Syntax.Component, `Whatwg.Css.Syntax.Declaration, `Whatwg.Css.Syntax.Rule,
        `Whatwg.Css.Syntax.Stylesheet]]
      note := "A token is one of the twenty-five kinds of the standard's list, with what the standard says each carries. A value of code points is a list of characters, and a numeric value is a rational number. A component value, a declaration and a rule are the results of parsing as the standard names them. One tree is written and read." }
    construction := {
      status := .requiredOpen
      remaining := [
        .named "not every value of `Token` is one the tokenizer gives: `Writable` is a test and not a type, and a caller that builds tokens by hand holds no proof until it runs the test"]
      grounds := [.declarations [`Whatwg.Css.Syntax.Token.ofIdent, `Whatwg.Css.Syntax.Token.writable,
        `Whatwg.Css.Syntax.Writable, `Whatwg.Css.Syntax.Component.readable,
        `Whatwg.Css.Syntax.Declaration.readable, `Whatwg.Css.Syntax.Rule.readable,
        `Whatwg.Css.Syntax.Stylesheet.readable, `Whatwg.Css.Syntax.writableText,
        `Whatwg.Css.Syntax.Stylesheet.writable, `Whatwg.Css.Syntax.Stylesheet.writableLines,
        `Whatwg.Css.Syntax.Value.ofText, `Whatwg.Css.Syntax.Calc, `Whatwg.Css.Syntax.Quiet],
        .theorems [`Whatwg.Css.Syntax.writable_append, `Whatwg.Css.Syntax.serialize_of_quiet,
          `Whatwg.Css.Syntax.Component.writable_thousandths, `Whatwg.Css.Syntax.Calc.value_writable]]
      note := "A writer builds a list of tokens and asks whether it is writable: each token is one the tokenizer can give and the writer can write, and three kinds say what must follow them. A tree asks the same of itself: `readable` says the parser reads its tokens back as the tree, and `writable` that its text does. Since slice K4 a value is built from builders that are writable by theorem, and two writable lists in a row are writable." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "parse errors are comments at their place and not values: the model returns the tokens the standard says are returned, and says nothing of which inputs are errors",
        .named "the parser has no context: every rule and every declaration is valid, the original text of a custom property is not kept, and the `unicode-range` descriptor is not read again from its source text",
        .named "at the end of a block's contents the model keeps the declarations it holds as the last item, where the sealed text returns without them",
        .named "decoding bytes to code points is not modelled: the input is a list of code points, after the standard's preprocessing (`filterCodePoints`)"]
      grounds := [.declarations [`Whatwg.Css.Syntax.tokenize, `Whatwg.Css.Syntax.tokenizeText,
        `Whatwg.Css.Syntax.consumeToken, `Whatwg.Css.Syntax.filterCodePoints,
        `Whatwg.Css.Syntax.consumeComponentValue, `Whatwg.Css.Syntax.consumeDeclaration,
        `Whatwg.Css.Syntax.consumeQualifiedRule, `Whatwg.Css.Syntax.consumeAtRule,
        `Whatwg.Css.Syntax.consumeBlockContents, `Whatwg.Css.Syntax.consumeStylesheetContents,
        `Whatwg.Css.Syntax.parseStylesheet, `Whatwg.Css.Syntax.parseStylesheetText,
        `Whatwg.Css.Syntax.parseComponentValues, `Whatwg.Css.Syntax.parseStyleAttribute],
        .theorems [`Whatwg.Css.Syntax.consumeToken_length_lt,
          `Whatwg.Css.Syntax.consumeDeclaration_length_lt,
          `Whatwg.Css.Syntax.consumeQualifiedRule_length_lt]]
      note := "`consumeToken` is the standard's `consume a token`, with one function for each algorithm it calls, each named after its heading in the sealed source. `tokenize` repeats it to the end of the input. Every token takes at least one code point, which is how `tokenize` ends. Since slice K4 the parser is modelled the same way: one function for each of its twelve algorithms and eight entry points, over a list of tokens, each ending because what remains is no longer." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "the round trip is proved for writable tokens only: a URL token, a bad URL, a range of code points, a unit or an unrestricted hash that needs an escape are written and guarded, with no theorem",
        .named "the premises of the parser's round trip suffice and are not necessary, and nothing says that a tree the parser returns passes them: `a { b: {} c { } }` gives one that does not",
        .named "nothing says that a comment is needed where the writer puts one: only guards show a pair misread without it",
        .named "the search for the digits of a fraction is bounded by the size of the denominator, and that it finds every decimal value is not proved: the test `Writable` checks its result, so the theorem does not rest on it"]
      grounds := [.theorems [`Whatwg.Css.Syntax.tokenize_serialize,
        `Whatwg.Css.Syntax.tokenize_serialize_eq, `Whatwg.Css.Syntax.tokenize_text,
        `Whatwg.Css.Syntax.stops_text, `Whatwg.Css.Syntax.stops_comment,
        `Whatwg.Css.Syntax.Component.read, `Whatwg.Css.Syntax.parseComponentValues_tokensAll,
        `Whatwg.Css.Syntax.consumeDeclaration_tokens,
        `Whatwg.Css.Syntax.parseStyleAttribute_tokensAll, `Whatwg.Css.Syntax.Rule.read,
        `Whatwg.Css.Syntax.parseRule_tokens, `Whatwg.Css.Syntax.parseStylesheet_tokens,
        `Whatwg.Css.Syntax.tokenizeText_serialize, `Whatwg.Css.Syntax.parseStylesheetText_text,
        `Whatwg.Css.Syntax.tokenize_serialize_append,
        `Whatwg.Css.Syntax.parseStylesheetText_lines]]
      note := "Tokenizing what the writer wrote gives the tokens back, with each run of white space as one, for every writable list. It is built from one law for each kind of token (the text of a token before a text that stops it reads as the token and then that text) and from the table of pairs, cell by cell (the next token's text stops the one before, where no comment is put). Since slice K4 the law reaches the tree: the parser reads the tokens of a readable tree back as the tree, from a component value to a stylesheet, and the text of a writable stylesheet, on one line or one rule a line, parses to the stylesheet. That the standard's preprocessing leaves the writer's text as it is holds under `writableText`, which asks one clause more than `Writable`." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "the writer's table of pairs is typed from the sealed table cell by cell, and the extractor writes the same table as `Whatwg/Css/Data/Pairs.lean`: no gate compares the two yet",
        .named "the rule for an identifier differs from the sealed CSSOM text on purpose: that text writes every code point from U+0080 as itself, and the tokenizer takes only some of them in a name, so the writer escapes the others"]
      grounds := [.declarations [`Whatwg.Css.Syntax.serialize, `Whatwg.Css.Syntax.Token.text,
        `Whatwg.Css.Syntax.needsComment, `Whatwg.Css.Syntax.extraPairs,
        `Whatwg.Css.Syntax.Component.tokens, `Whatwg.Css.Syntax.Declaration.tokens,
        `Whatwg.Css.Syntax.Rule.tokens, `Whatwg.Css.Syntax.Stylesheet.tokens,
        `Whatwg.Css.Syntax.Stylesheet.text, `Whatwg.Css.Syntax.Stylesheet.lines,
        `Whatwg.Css.Syntax.Rule.splitBlock]]
      note := "The writer puts an empty comment between two tokens where the standard's table marks the pair, and in two more places that the table misses: the identifier `--` before `>`, and `<` before `!`." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .named "no register row: the two pairs that the sealed table misses, and the identifier that CSSOM's rule writes and the tokenizer reads as three tokens, are guards of `WhatwgTest/Css/Syntax.lean` and not registered counterexamples"] }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "no host was asked: no browser's tokens were compared with the model's, and the Web Platform Tests of `css/css-syntax` are not sealed (slice K6)"] }
    targets := {
      status := .requiredOpen
      remaining := [
        .named "the picture kit writes through this tree since slice K4, each value from a builder that is writable by theorem; that the whole sheet of a step is writable is a guard and no theorem, and that each value is one its property's sealed grammar admits is evaluated in `WhatwgTest/Css/Kit.lean` with one theorem (slice K5)",
        .named "the consumer's stylesheet is read by the parser in a test of this repository; no build of lean4-effect4 calls the parser yet"]
      grounds := [.declarations [`Whatwg.Css.Syntax.Stylesheet.located],
        .theorems [`Whatwg.Css.Syntax.Rule.located_under],
        .modules [`Whatwg.Html.Node.Css, `Whatwg.Html.Node.SvgMotion,
          `Whatwg.Html.Node.SvgMotion.Laws, `WhatwgTest.Css.Kit, `WhatwgTest.Css.Parse]] }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the test's texts of the picture kit are copied from its port and not produced by calling the kit"]
      grounds := [.modules [`Whatwg.Css.Syntax.Tree, `Whatwg.Css.Syntax.Tokenize,
        `Whatwg.Css.Syntax.Serialize, `Whatwg.Css.Syntax.Laws, `WhatwgTest.Css.Syntax,
        `Whatwg.Css.Syntax.Write, `Whatwg.Css.Syntax.Parse, `Whatwg.Css.Syntax.Readable,
        `Whatwg.Css.Syntax.Parse.Laws, `Whatwg.Css.Syntax.Parse.Lines,
        `Whatwg.Css.Syntax.Located, `Whatwg.Css.Syntax.Build, `Whatwg.Css.Syntax.Build.Laws,
        `WhatwgTest.Css.Parse, `WhatwgTest.Css.Kit],
        .gate .build]
      note := "The twenty-three modules are under the ceiling of ruling R-11: `propext`, `Quot.sound` and `Classical.choice`." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "CSS Syntax 3 is not a standard of the census yet (ruling CS-6): the sixteen algorithms of the tokenizer and the twenty of the parser each have a function, and no report counts them"] } }

end WhatwgTest.Ledger