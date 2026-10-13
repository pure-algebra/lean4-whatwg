import Whatwg.Css.Syntax.Parse.Lines
import Whatwg.Css.Syntax.Located
import WhatwgTest.Css.ParseCorpus

/-!
# WhatwgTest.Css.Parse

Owner: readers and controls of the parser of CSS (slice K4 of `docs/CSS-PACKAGE-PLAN.md`; proof
graph `CSS-PG-SYNTAX`; entry W5 of `docs/research/2026-10-12-whatwg-requests.md`).

The test is real text: the stylesheet of the documentation site of lean4-effect4
(`WhatwgTest/Css/ParseCorpus.lean`). Every line is a reader, a control, or a finite evaluation
that no theorem covers.

- **The consumer's stylesheet, read.** What a reader of it needs: how many rules, the at-rules by
  name, the declarations with the rules they stand under (`Stylesheet.located`).
- **The consumer's check, ported.** lean4-effect4 refuses a literal colour, a family that is not
  taken from the look, a shadow, a gradient and a filter, and allows a family in `@font-face`.
  Today it finds these on lines of text. `problem` is the same check on the tree, by the fold of
  `Whatwg/Css/Syntax/Located.lean`; its coordinator writes its port from it. Controls show each
  clause find its case.
- **The round trip at the consumer's stylesheet.** The tree is written by `Stylesheet.text` and
  `Stylesheet.lines` and parsed again; it passes `Stylesheet.writable` and
  `Stylesheet.writableLines`, so `parseStylesheetText_text` and `parseStylesheetText_lines`
  speak of it.
- **Readers**: the laws at trees written as data, with their premises closed by `decide`.
- **The standard's corner cases**, each from a sentence or a note of the chapter `parsing`.
- **Controls of the premises**: for each clause of `Component.readable`, `Declaration.readable`,
  `Rule.readable` and `writableText`, a tree that the clause excludes, and what the parser reads
  from its tokens in its place.
-/

namespace WhatwgTest.Css.Parse

open Whatwg.Css.Syntax WhatwgTest.Css.ParseCorpus

/-! ## Spellings -/

def ident (s : String) : Component := .token (.ident s.toList)
def sp : Component := .token .whitespace
def colon : Component := .token .colon
def semicolon : Component := .token .semicolon
def integer (n : Int) : Component := .token (.number { value := n } .integer)
def px (n : Int) : Component :=
  .token (.dimension { value := n, sign := if n < 0 then some .minus else none } .integer
    "px".toList)
def decl (name : String) (value : List Component) (important : Bool := false) : Declaration :=
  { name := name.toList, value := value, important := important }
def style (prelude : List Component) (declarations : List Declaration)
    (rules : List Rule := []) : Rule :=
  .qualified prelude declarations rules
def atBlock (name : String) (prelude : List Component) (declarations : List Declaration)
    (rules : List Rule := []) : Rule :=
  .blockAt name.toList prelude declarations rules

/-- The rules of a text. -/
def rulesOf (text : String) : List Rule := (parseStylesheetText text).rules

/-! ## The consumer's stylesheet, read -/

/-- The consumer's stylesheet as a tree. -/
def sheet : Stylesheet := parseStylesheetText pageCss

-- 11,378 code points are 2,994 tokens and 80 rules.
#guard pageCss.length == 11378
#guard (tokenizeText pageCss).length == 2994
#guard sheet.rules.length == 80

/-- The at-rules at the top of a stylesheet, each by its name and the text of its prelude. -/
def atRules (s : Stylesheet) : List (String × String) :=
  s.rules.filterMap fun
    | .statement name prelude => some (String.ofList name, Component.textAll prelude)
    | .blockAt name prelude _ _ => some (String.ofList name, Component.textAll prelude)
    | _ => none

-- Three faces and two media rules. A prelude keeps its white space.
#guard atRules sheet ==
  [("font-face", " "), ("font-face", " "), ("font-face", " "),
    ("media", " (max-width: 64rem) "), ("media", " print ")]

-- An at-rule's block is split as a qualified rule's: `@font-face` has declarations and no child
-- rule, `@media` has child rules and no declaration.
#guard sheet.rules.filterMap (fun
    | .blockAt _ _ declarations rules => some (declarations.length, rules.length)
    | _ => none) == [(5, 0), (5, 0), (5, 0), (0, 2), (0, 5)]

-- No rule of the sheet holds a nested declarations rule, and no rule was dropped: the 75 others
-- are qualified rules.
#guard (sheet.rules.filter fun | .qualified _ _ [] => true | _ => false).length == 75

-- The fold: 247 declarations, 15 of them under `@font-face`, 15 under `@media`; 14 custom
-- properties, all in `:root`; 86 property names; none flagged `!important`.
#guard sheet.located.length == 247
#guard (sheet.located.filter (·.underAtRule "font-face")).length == 15
#guard (sheet.located.filter (·.underAtRule "media")).length == 15
#guard (sheet.located.filter fun l => isCustomPropertyName l.declaration.name).length == 14
#guard (sheet.located.map (·.declaration.name)).eraseDups.length == 86
#guard sheet.located.all fun l => !l.declaration.important

/-- The text of a path: the name of an at-rule, the prelude of a qualified rule. -/
def pathText (l : Located) : List String :=
  l.path.map fun
    | .atRule name _ => "@" ++ String.ofList name
    | .qualified prelude => Component.textAll prelude

-- A declaration in a rule in `@media` stands under both, the outer first.
#guard (sheet.located.filter (·.underAtRule "media")).head?.map
  (fun l => (pathText l, l.declaration.text)) == some (["@media", "body "], "display: block")

/-! ## The consumer's check, ported onto the tree

`Tools.Document.Html.Sheet.problem` of lean4-effect4 (at `6ad8f7b8d`) reads lines of text. Each
of its clauses is a test on a declaration and its path here. -/

mutual

/-- Whether a component value, or one inside it at any depth, passes a test. -/
def holds (p : Component → Bool) : Component → Bool
  | .token t => p (.token t)
  | .function name value => p (.function name value) || holdsAny p value
  | .block bracket value => p (.block bracket value) || holdsAny p value

/-- Whether a component value of a row, or one inside it at any depth, passes a test. -/
def holdsAny (p : Component → Bool) : List Component → Bool
  | [] => false
  | c :: rest => holds p c || holdsAny p rest

end

/-- A hash token of three to eight hex digits: a colour written in the sheet. -/
def isHexColour : Component → Bool
  | .token (.hash value _) => 3 ≤ value.length && value.length ≤ 8 && value.all isHexDigit
  | _ => false

/-- A function that writes a colour by its numbers. -/
def isColourFunction : Component → Bool
  | .function name _ =>
    ["rgb", "rgba", "hsl", "hsla", "hwb", "lab", "lch", "oklab", "oklch"].contains
      (String.ofList name)
  | _ => false

/-- A function whose name ends in `gradient`. -/
def isGradient : Component → Bool
  | .function name _ => "gradient".toList.isSuffixOf name
  | _ => false

/-- A `var()` whose first argument is a custom property with this start of a name. -/
def isVarOf (start : String) : Component → Bool
  | .function name (.token (.ident property) :: _) =>
    name == "var".toList && start.toList.isPrefixOf property
  | _ => false

/-- **What the design language refuses in a declaration, if anything**: a literal colour; a
shadow, a gradient or a filter; outside `@font-face`, a family that is not a look's custom
property, and a `font` that takes no family from the look. -/
def problem (l : Located) : Option String :=
  let name := String.ofList l.declaration.name
  let value := l.declaration.value
  if holdsAny (fun c => isHexColour c || isColourFunction c) value then some "a literal colour"
  else if name == "box-shadow" || name == "text-shadow" || name == "filter" ||
      holdsAny isGradient value then some "an ornament with no meaning"
  else if l.underAtRule "font-face" then none
  else if name == "font-family" && !value.head?.any (isVarOf "--") then some "a literal family"
  else if name == "font" && !holdsAny (isVarOf "--e4-font-") value then
    some "a font without the look's family"
  else none

/-- The problems of a text, each with the path and the text of its declaration. -/
def problems (text : String) : List (String × List String × String) :=
  (parseStylesheetText text).located.filterMap fun l =>
    (problem l).map fun what => (what, pathText l, l.declaration.text)

-- The consumer's stylesheet has none.
#guard (sheet.located.filterMap problem).isEmpty

-- It names a family eight times: three in `@font-face`, as strings, and five outside, each a
-- look's custom property.
#guard (sheet.located.filter fun l => l.declaration.name == "font-family".toList).map
    (fun l => (l.underAtRule "font-face", Component.textAll l.declaration.value)) ==
  [(true, "\"Source Serif 4\""), (true, "\"Source Serif 4\""), (true, "\"JetBrains Mono\""),
    (false, "var(--e4-font-label-family)"), (false, "var(--e4-font-title-family)"),
    (false, "var(--e4-font-title-family)"), (false, "var(--e4-font-data-family)"),
    (false, "var(--e4-font-label-family)")]

-- Controls: each clause finds its case, and names where it stands.
#guard problems "a { color: #fff }" == [("a literal colour", ["a "], "color: #fff")]
#guard problems "@media print { a { color: rgb(0 0 0) } }" ==
  [("a literal colour", ["@media", "a "], "color: rgb(0 0 0)")]
#guard problems "a { border: 1px solid color-mix(in srgb, #abcdef 50%, var(--c)) }" ==
  [("a literal colour", ["a "], "border: 1px solid color-mix(in srgb, #abcdef 50%, var(--c))")]
#guard (problems "a { box-shadow: 0 0 1px var(--c); background: linear-gradient(var(--a), var(--b)) }").map
    (·.1) == ["an ornament with no meaning", "an ornament with no meaning"]
#guard problems "@font-face { font-family: \"X\" } a { font-family: \"X\" }" ==
  [("a literal family", ["a "], "font-family: \"X\"")]
#guard problems "a { font: 1rem serif } b { font: 1rem var(--e4-font-name-family) }" ==
  [("a font without the look's family", ["a "], "font: 1rem serif")]
-- An identifier that is not a colour is not taken for one: `#toc` in a value is a hash token of
-- three letters that are not hex digits.
#guard problems "a { anchor: #toc }" == []

/-! ## The round trip at the consumer's stylesheet -/

-- The tree passes the test of the law `parseStylesheetText_text`: its tokens are writable, no
-- two whitespace tokens stand together, its text is its own preprocessing, and it is readable.
#guard sheet.writable

-- What that law concludes, evaluated: the kernel does not run the parser, so `decide` gives no
-- proof of the line above for a tree that the parser made.
#guard parseStylesheetText sheet.text == sheet

-- The same with a line for each rule: the tree passes the test of `parseStylesheetText_lines`,
-- and what that law concludes is evaluated.
#guard sheet.writableLines
#guard parseStylesheetText sheet.lines == sheet
#guard (sheet.lines.splitOn "\n").length == 80

-- The text written is shorter than the text read: the comments are gone, and each run of white
-- space is one space.
#guard sheet.text.length == 8353

/-! ## Readers: the laws at trees written as data -/

/-- A stylesheet written as data: a statement at-rule, a block at-rule with rules in it, a rule
with a flagged declaration, a child rule and declarations after it. -/
def written : Stylesheet :=
  ⟨[.statement "import".toList [sp, .token (.string "looks.css".toList)],
    atBlock "media" [sp, ident "print", sp] []
      [style [ident "nav", sp] [decl "display" [ident "none"]]],
    style [ident "a", colon, ident "hover", sp]
      [decl "margin" [integer 0, sp, px 2] true, decl "--gap" [.block .curly [ident "x"]]]
      [style [ident "b", colon, ident "focus", sp] [decl "color" [ident "inherit"]],
        .nested [decl "top" [px 1], decl "left" [px 1]],
        atBlock "media" [sp, ident "print", sp] [decl "color" [ident "black"]]]]⟩

#guard written.text ==
  "@import \"looks.css\"; @media print { nav { display: none } } " ++
  "a:hover { margin: 0 2px !important; --gap: {x}; b:focus { color: inherit } top: 1px; left: 1px; " ++
  "@media print { color: black } }"

-- The law at the text, its premise closed by `decide`: a caller that builds a stylesheet as
-- data holds a proof that the parser reads its text back.
example : parseStylesheetText written.text = written :=
  parseStylesheetText_text written (by decide)

-- The same with a line for each rule.
example : parseStylesheetText written.lines = written :=
  parseStylesheetText_lines written (by decide)

-- The law at the tokens.
example : parseStylesheet written.tokens = written :=
  parseStylesheet_tokens written (by decide)

-- One rule alone, as `parse a rule` reads it.
example : parseRule (atBlock "media" [sp, ident "print", sp] [decl "color" [ident "black"]]).tokens =
    some (atBlock "media" [sp, ident "print", sp] [decl "color" [ident "black"]]) :=
  parseRule_tokens _ (by decide)

-- A row of declarations, as a `style` attribute holds it.
def row : List Declaration :=
  [decl "translate" [px (-60), sp, px 0], decl "opacity" [integer 1] true]

example : parseStyleAttribute (Declaration.tokensAll row) = row :=
  parseStyleAttribute_tokensAll row (by decide)

-- A list of component values with a right parenthesis and a right curly bracket loose at its
-- top: both are preserved tokens there.
def loose : List Component :=
  [.function "f".toList [ident "a", .token .closeCurly], .token .closeParen, .token .closeCurly]

example : parseComponentValues (Component.tokensAll loose) = loose :=
  parseComponentValues_tokensAll loose (by decide)

-- The text of the row comes back as well.
example : parseStyleAttributeText (Declaration.textAll row) = row :=
  parseStyleAttributeText_textAll row (by decide) (by decide)

#guard Declaration.textAll row == "translate: -60px 0px; opacity: 1 !important"

/-! ## The standard's corner cases -/

-- `consume-block-contents`: "Otherwise, restore a mark from input, then consume a qualified
-- rule". `b:hover { ... }` in a block starts as a declaration named `b`; step 8 of
-- `consume-declaration` returns nothing for a value that holds a block beside `hover`, and the
-- same tokens are a rule.
#guard rulesOf "a { b:hover { color: red } }" ==
  [style [ident "a", sp] []
    [style [ident "b", colon, ident "hover", sp] [decl "color" [ident "red"]]]]

-- The same step: "a top-level {}-block is only allowed as the entire value of a non-custom
-- property". Alone it is a declaration; beside another value the tokens are a rule; for a custom
-- property the value is kept whole.
#guard rulesOf "a { x: { y: z } }" ==
  [style [ident "a", sp] [decl "x" [.block .curly [sp, ident "y", colon, sp, ident "z", sp]]]]
#guard rulesOf "a { x: { y: z } w }" ==
  [style [ident "a", sp] [] [style [ident "x", colon, sp] [decl "y" [ident "z"]]]]
#guard rulesOf "a { --x: { y: z } w }" ==
  [style [ident "a", sp]
    [decl "--x" [.block .curly [sp, ident "y", colon, sp, ident "z", sp], sp, ident "w"]]]

-- `consume-qualified-rule`, the note "What's this check for?": at the top of a stylesheet
-- "--foo:hover { color: blue; } is consistently invalid", and the rule after it is read.
#guard rulesOf "--foo:hover { color: blue; } b { }" == [style [ident "b", sp] []]

-- The same note: in a block it is a custom property, "all the way to the ending semicolon".
#guard rulesOf "a { --foo:hover { color: blue; } c: d; e: f }" ==
  [style [ident "a", sp]
    [decl "--foo" [ident "hover", sp,
        .block .curly [sp, ident "color", colon, sp, ident "blue", semicolon, sp],
        sp, ident "c", colon, sp, ident "d"],
      decl "e" [ident "f"]]]

-- `consume-block`: "Discard a token from input" after the contents, which at the end of the
-- input discards nothing. A block left open is a block. Its declaration is kept: the reading of
-- `consumeBlockContents` at the end of a block's contents.
#guard rulesOf "a { color: red" == [style [ident "a", sp] [decl "color" [ident "red"]]]
#guard rulesOf "a { color: red" == rulesOf "a { color: red }"

-- `consume-qualified-rule`, a right curly bracket where `nested` is false: "consume a token and
-- append the result to rule's prelude".
#guard rulesOf "} a { }" == [style [.token .closeCurly, sp, ident "a", sp] []]

-- `consume-declaration`, step 6: "an ASCII case-insensitive match for "important"".
#guard rulesOf "a { color: red !IMPORTANT }" == [style [ident "a", sp] [decl "color" [ident "red"] true]]
#guard rulesOf "a { color: red ! important }" == rulesOf "a { color: red !important }"

-- Steps 2, 4 and 7: white space around the colon and at the two ends of a value is dropped.
#guard rulesOf "a {   color  :   red   ;  }" == [style [ident "a", sp] [decl "color" [ident "red"]]]

-- `consume-qualified-rule`: "If any remaining items of child rules are lists of declarations,
-- replace them with nested declarations rules". Declarations after a child rule are one.
#guard rulesOf "a { color: red; b { } color: blue; width: 1px }" ==
  [style [ident "a", sp] [decl "color" [ident "red"]]
    [style [ident "b", sp] [], .nested [decl "color" [ident "blue"], decl "width" [px 1]]]]

-- `consume-block-contents`, an at-keyword token: the declarations before it are closed, so the
-- ones after it are a nested declarations rule. The at-rule's own block is split the same way.
#guard rulesOf "a { color: red; @media print { color: blue } margin: 0 }" ==
  [style [ident "a", sp] [decl "color" [ident "red"]]
    [atBlock "media" [sp, ident "print", sp] [decl "color" [ident "blue"]],
      .nested [decl "margin" [integer 0]]]]

-- The same algorithm, "If nothing was returned: Do nothing". What is neither a declaration nor a
-- rule is dropped to its semicolon, and the declarations on its two sides stay one list.
#guard rulesOf "a { color: red; foo bar; margin: 0 }" ==
  [style [ident "a", sp] [decl "color" [ident "red"], decl "margin" [integer 0]]]

-- `consume-stylesheet-contents`: a CDO and a CDC token at the top are discarded.
#guard rulesOf "<!-- a { } --> b { }" == [style [ident "a", sp] [], style [ident "b", sp] []]

-- `consume-at-rule`: a semicolon or the end of the input ends a statement at-rule.
#guard rulesOf "@import \"x\"; @charset \"y\"" ==
  [.statement "import".toList [sp, .token (.string "x".toList)],
    .statement "charset".toList [sp, .token (.string "y".toList)]]

-- `consume-style-attribute`: an at-rule is ignored, and what is not a declaration is dropped to
-- its semicolon.
#guard parseStyleAttributeText "color: red; @media x { } margin: 0 !important; a { } ; width: 1px" ==
  [decl "color" [ident "red"], decl "margin" [integer 0] true, decl "width" [px 1]]

-- `parse-block-contents`: a right curly bracket ends the reading, as it ends a block.
#guard parseBlockContentsText "color: red; } margin: 0" == [.nested [decl "color" [ident "red"]]]

-- `parse-rule`: one rule, with white space around it, and nothing else.
#guard parseRuleText " a { } " == some (style [ident "a", sp] [])
#guard parseRuleText " a { } b { }" == none
#guard parseRuleText "  " == none
#guard parseRuleText "@x y;" == some (.statement "x".toList [sp, ident "y"])

-- `parse-declaration`: what follows the declaration is not looked at.
#guard parseDeclarationText " color: red; junk" == some (decl "color" [ident "red"])
#guard parseDeclarationText "color red" == none

-- `parse-component-value`: one value, or none.
#guard parseComponentValueText " f(a) " == some (.function "f".toList [ident "a"])
#guard parseComponentValueText " f(a) b" == none
#guard parseComponentValueText "" == none

-- `parse-comma-separated-list-of-component-values`: a comma at the end gives no empty group
-- after it; a comma alone gives one empty group.
#guard parseCommaSeparatedComponentValuesText "a b, c," == [[ident "a", sp, ident "b"], [sp, ident "c"]]
#guard parseCommaSeparatedComponentValuesText "," == [[]]

-- `consume-simple-block` and `consume-function` at the end of the input: both close.
#guard parseComponentValuesText "f(a [b" == [.function "f".toList [ident "a", sp, .block .square [ident "b"]]]

-- What is not modelled, shown: the value of `unicode-range` is the tokens as the tokenizer gave
-- them with no unicode ranges, an identifier and a number.
#guard (rulesOf "@font-face { unicode-range: U+26 }") ==
  [atBlock "font-face" [sp]
    [decl "unicode-range" [ident "U", .token (.number { value := 26, sign := some .plus } .integer)]]]

/-! ## Controls of the premises

For each clause: a tree that the clause excludes, and what the parser reads from its tokens. -/

/-- What the parser reads from the tokens of a list of component values. -/
def reread (value : List Component) : List Component :=
  parseComponentValues (Component.tokensAll value)

-- `Component.readable`. A token that opens a block is not a component value: it is read as the
-- block.
#guard !Component.readable (.token .openParen)
#guard reread [.token .openParen] == [.block .paren []]
-- A right parenthesis at the top of a function's value ends the function.
#guard !Component.readable (.function "f".toList [.token .closeParen])
#guard reread [.function "f".toList [.token .closeParen]] ==
  [.function "f".toList [], .token .closeParen]
-- The token that closes a block, at the top of the block's value, ends the block.
#guard !Component.readable (.block .square [.token .closeSquare, ident "a"])
#guard reread [.block .square [.token .closeSquare, ident "a"]] ==
  [.block .square [], ident "a", .token .closeSquare]

/-- What the parser reads from the tokens of one declaration in a `style` attribute. -/
def rereadDeclaration (d : Declaration) : List Declaration :=
  parseStyleAttribute (Declaration.tokensAll [d])

-- `Declaration.readable`. White space at the start of a value, and at its end, is dropped.
#guard !Declaration.readable false (decl "a" [sp, ident "b"])
#guard rereadDeclaration (decl "a" [sp, ident "b"]) == [decl "a" [ident "b"]]
#guard !Declaration.readable false (decl "a" [ident "b", sp])
#guard rereadDeclaration (decl "a" [ident "b", sp]) == [decl "a" [ident "b"]]
-- `!important` at the end of a value that is not flagged is taken for the flag.
#guard !Declaration.readable false (decl "a" [ident "b", .token (.delim '!'), ident "important"])
#guard rereadDeclaration (decl "a" [ident "b", .token (.delim '!'), ident "important"]) ==
  [decl "a" [ident "b"] true]
-- A semicolon at the top of a value ends the value.
#guard !Declaration.readable false (decl "a" [ident "b", semicolon, ident "c", colon, ident "d"])
#guard rereadDeclaration (decl "a" [ident "b", semicolon, ident "c", colon, ident "d"]) ==
  [decl "a" [ident "b"], decl "c" [ident "d"]]
-- A right curly bracket at the top of a value ends the value in a block, and not in a `style`
-- attribute, which no bracket closes.
#guard !Declaration.readable true (decl "a" [.token .closeCurly])
#guard Declaration.readable false (decl "a" [.token .closeCurly])
#guard rulesOf (Rule.text (style [ident "s", sp] [decl "a" [.token .closeCurly]])) !=
  [style [ident "s", sp] [decl "a" [.token .closeCurly]]]
-- A block in curly brackets beside another value, where the name is not a custom property's:
-- nothing is read.
#guard !Declaration.readable false (decl "a" [.block .curly [], ident "b"])
#guard rereadDeclaration (decl "a" [.block .curly [], ident "b"]) == []
#guard Declaration.readable false (decl "--a" [.block .curly [], ident "b"])

/-- What the parser reads from the tokens of a stylesheet of these rules. -/
def rereadRules (rules : List Rule) : List Rule := (parseStylesheet (Stylesheet.tokens ⟨rules⟩)).rules

-- `Rule.readable`, an at-rule. A block in curly brackets at the top of a prelude is read as the
-- rule's block.
#guard !Rule.readable false (.statement "x".toList [.block .curly []])
#guard rereadRules [.statement "x".toList [.block .curly []]] == [atBlock "x" [] []]
-- A semicolon at the top of a prelude ends the rule.
#guard !Rule.readable false (.statement "x".toList [semicolon, ident "a"])
#guard rereadRules [.statement "x".toList [semicolon, ident "a"]] == [.statement "x".toList []]

-- A qualified rule. White space at the start of a prelude is discarded before the rule.
#guard !Rule.readable false (style [sp, ident "a", sp] [])
#guard rereadRules [style [sp, ident "a", sp] []] == [style [ident "a", sp] []]
-- An at-keyword token at the start of a prelude starts an at-rule.
#guard !Rule.readable false (style [.token (.atKeyword "x".toList), sp] [])
#guard rereadRules [style [.token (.atKeyword "x".toList), sp] []] == [atBlock "x" [sp] []]
-- A CDO token at the start of a prelude is discarded at the top of a stylesheet, and is kept in
-- a block.
#guard !Rule.readable false (style [.token .cdo, ident "a", sp] [])
#guard Rule.readable true (style [.token .cdo, ident "a", sp] [])
#guard rereadRules [style [.token .cdo, ident "a", sp] []] == [style [ident "a", sp] []]
-- A prelude that starts as a custom property does: nothing is read.
#guard !Rule.readable false (style [ident "--x", colon, ident "hover", sp] [])
#guard rereadRules [style [ident "--x", colon, ident "hover", sp] []] == []
-- A semicolon at the top of a prelude: at the top of a stylesheet it is part of the prelude, and
-- in a block it is the stop token.
#guard Rule.readable false (style [ident "a", semicolon, ident "b", sp] [])
#guard !Rule.readable true (style [ident "a", semicolon, ident "b", sp] [])
#guard rereadRules [style [ident "s", sp] [] [style [ident "a", semicolon, ident "b", sp] []]] ==
  [style [ident "s", sp] [] [style [ident "b", sp] []]]
-- In a block, a prelude that is an identifier and a colon alone: the rule is read as a
-- declaration whose value is its block.
#guard !Rule.readable true (style [ident "b", colon, sp] [])
#guard Rule.readable false (style [ident "b", colon, sp] [])
#guard rereadRules [style [ident "s", sp] [] [style [ident "b", colon, sp] []]] ==
  [style [ident "s", sp] [decl "b" [.block .curly [sp]]]]
-- The clause is stricter than needed: before another rule the same rule is read back.
#guard rereadRules [style [ident "s", sp] [] [style [ident "b", colon, sp] [], style [ident "c", sp] []]] ==
  [style [ident "s", sp] [] [style [ident "b", colon, sp] [], style [ident "c", sp] []]]

-- A block. A nested declarations rule that is the first child rule is read as the block's own
-- declarations.
#guard !Rule.readable false (style [ident "s", sp] [] [.nested [decl "a" [ident "b"]]])
#guard rereadRules [style [ident "s", sp] [] [.nested [decl "a" [ident "b"]]]] ==
  [style [ident "s", sp] [decl "a" [ident "b"]]]
-- Two nested declarations rules that stand together are read as one.
#guard !Rule.readable false (style [ident "s", sp] []
  [style [ident "t", sp] [], .nested [decl "a" [ident "b"]], .nested [decl "c" [ident "d"]]])
#guard rereadRules [style [ident "s", sp] []
    [style [ident "t", sp] [], .nested [decl "a" [ident "b"]], .nested [decl "c" [ident "d"]]]] ==
  [style [ident "s", sp] []
    [style [ident "t", sp] [], .nested [decl "a" [ident "b"], decl "c" [ident "d"]]]]
-- A nested declarations rule with no declaration is not read.
#guard !Rule.readable true (.nested [])
#guard rereadRules [style [ident "s", sp] [] [style [ident "t", sp] [], .nested []]] ==
  [style [ident "s", sp] [] [style [ident "t", sp] []]]
-- A nested declarations rule does not stand at the top of a stylesheet: its declarations are
-- read as the start of a qualified rule that never comes.
#guard !Stylesheet.readable ⟨[.nested [decl "a" [ident "b"]]]⟩
#guard rereadRules [.nested [decl "a" [ident "b"]]] == []

-- `writableText`. A delimiter that holds a carriage return is `Writable`, and `tokenize` reads it
-- back; `tokenizeText` preprocesses the text, and reads white space. The third clause of
-- `writableText` excludes it.
#guard Writable [.delim '\r']
#guard tokenize (serialize [.delim '\r']) == [.delim '\r']
#guard tokenizeText (String.ofList (serialize [.delim '\r'])) == [.whitespace]
#guard !writableText [.delim '\r']
-- Two whitespace tokens together are written as two spaces, which are one token.
#guard !writableText [.whitespace, .whitespace]
#guard tokenizeText (String.ofList (serialize [.whitespace, .whitespace])) == [.whitespace]

end WhatwgTest.Css.Parse
