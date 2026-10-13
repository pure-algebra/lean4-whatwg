import WhatwgGates.Ledger.Model

/-!
# WhatwgTest.Ledger.CssSyntax

The graph ledger's entry for `CSS-PG-SYNTAX`: the tokens of CSS, the tokenizer of CSS Syntax 3,
the writer of tokens, and the round trip between them (slice K2 of `docs/CSS-PACKAGE-PLAN.md`).
`docs/CSS-SYNTAX-DAG.md` is the graph's document. Ruling R-S36 of `COORDINATION.md` opened the
graph and changes no edge's status, so the entry acknowledges it.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The assurance graph of the tokens of CSS: a tokenizer, a writer and their round trip. -/
def cssSyntax : Graph where
  id := "CSS-PG-SYNTAX"
  document := "docs/CSS-SYNTAX-DAG.md"
  fence := [`Whatwg.Css.Syntax.Tree, `Whatwg.Css.Syntax.Tokenize, `Whatwg.Css.Syntax.Serialize,
    `Whatwg.Css.Syntax.Laws, `Whatwg.Css.Syntax.Laws.Dispatch, `Whatwg.Css.Syntax.Laws.Name,
    `Whatwg.Css.Syntax.Laws.Number, `Whatwg.Css.Syntax.Laws.String,
    `Whatwg.Css.Syntax.Laws.Escape, `Whatwg.Css.Syntax.Laws.Token, `Whatwg.Css.Syntax.Laws.Text]
  acknowledged := ["R-S36"]
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
        `Whatwg.Css.Syntax.Writable]]
      note := "A writer builds a list of tokens and asks whether it is writable: each token is one the tokenizer can give and the writer can write, and three kinds say what must follow them." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "parse errors are comments at their place and not values: the model returns the tokens the standard says are returned, and says nothing of which inputs are errors",
        .named "the parser of the standard, from tokens to rules, is not modelled (slice K4)",
        .named "decoding bytes to code points is not modelled: the input is a list of code points, after the standard's preprocessing (`filterCodePoints`)"]
      grounds := [.declarations [`Whatwg.Css.Syntax.tokenize, `Whatwg.Css.Syntax.tokenizeText,
        `Whatwg.Css.Syntax.consumeToken, `Whatwg.Css.Syntax.filterCodePoints],
        .theorems [`Whatwg.Css.Syntax.consumeToken_length_lt]]
      note := "`consumeToken` is the standard's `consume a token`, with one function for each algorithm it calls, each named after its heading in the sealed source. `tokenize` repeats it to the end of the input. Every token takes at least one code point, which is how `tokenize` ends." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "the round trip is proved for writable tokens only: a URL token, a bad URL, a range of code points, a unit or an unrestricted hash that needs an escape are written and guarded, with no theorem",
        .named "the law is about `tokenize` and not `tokenizeText`: that preprocessing leaves the writer's text as it is is not proved",
        .named "nothing says that a comment is needed where the writer puts one: only guards show a pair misread without it",
        .named "the search for the digits of a fraction is bounded by the size of the denominator, and that it finds every decimal value is not proved: the test `Writable` checks its result, so the theorem does not rest on it"]
      grounds := [.theorems [`Whatwg.Css.Syntax.tokenize_serialize,
        `Whatwg.Css.Syntax.tokenize_serialize_eq, `Whatwg.Css.Syntax.tokenize_text,
        `Whatwg.Css.Syntax.stops_text, `Whatwg.Css.Syntax.stops_comment]]
      note := "Tokenizing what the writer wrote gives the tokens back, with each run of white space as one, for every writable list. It is built from one law for each kind of token (the text of a token before a text that stops it reads as the token and then that text) and from the table of pairs, cell by cell (the next token's text stops the one before, where no comment is put)." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "the writer's table of pairs is typed from the sealed table cell by cell, and the extractor writes the same table as `Whatwg/Css/Data/Pairs.lean`: no gate compares the two yet",
        .named "the rule for an identifier differs from the sealed CSSOM text on purpose: that text writes every code point from U+0080 as itself, and the tokenizer takes only some of them in a name, so the writer escapes the others"]
      grounds := [.declarations [`Whatwg.Css.Syntax.serialize, `Whatwg.Css.Syntax.Token.text,
        `Whatwg.Css.Syntax.needsComment, `Whatwg.Css.Syntax.extraPairs]]
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
        .named "the picture kit's writer of CSS (`Whatwg/Html/Node/Css.lean`) still writes text by rule and not through these tokens (slice K5)"] }
    trust := {
      status := .requiredOpen
      remaining := [
        .named "the test's texts of the picture kit are copied from its port and not produced by calling the kit"]
      grounds := [.modules [`Whatwg.Css.Syntax.Tree, `Whatwg.Css.Syntax.Tokenize,
        `Whatwg.Css.Syntax.Serialize, `Whatwg.Css.Syntax.Laws, `WhatwgTest.Css.Syntax],
        .gate .build]
      note := "The eleven modules are under the ceiling of ruling R-11: `propext`, `Quot.sound` and `Classical.choice`." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "CSS Syntax 3 is not a standard of the census yet (ruling CS-6): the sixteen algorithms of the tokenizer each have a function, and no report counts them"] } }

end WhatwgTest.Ledger