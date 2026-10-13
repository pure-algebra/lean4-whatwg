import Whatwg.Css.Syntax.Laws

/-!
# WhatwgTest.Css.Syntax

Owner: readers and controls of the tokenizer and the writer of CSS (slice K2 of
`docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

Every line is a finite evaluation that no theorem covers, a control, or a reader.

- The tokens of the CSS that the picture kit writes today. The texts are the ones that the
  guards of `WhatwgTest/Html/SvgMotion.lean` hold and that the docstrings of
  `Whatwg/Html/Node/SvgMotion.lean` describe: a `@keyframes` rule, an `animation` declaration
  with each easing, a `d: path("…")`.
- Readers: those tokens are writable, so `tokenize_serialize` speaks of them; and the writer
  writes the kit's own text back, code point for code point.
- Controls: a pair that the table marks, written with no comment, is other tokens; a token
  outside the premise does not come back.
- Findings against the note `serialization-tables` of the sealed text: two shapes that the
  table does not mark and that do not come back without a comment.
- The text of a name that needs an escape, which the law covers; and what is outside the law
  and still comes back at examples: a unit that would be read as an exponent, a url.
-/

namespace WhatwgTest.Css.Syntax

open Whatwg.Css.Syntax

/-! ## Spellings -/

def ident (s : String) : Token := .ident s.toList
def function (s : String) : Token := .function s.toList
def atKeyword (s : String) : Token := .atKeyword s.toList
def string (s : String) : Token := .string s.toList
def ws : Token := .whitespace
def integer (n : Int) : Token := .number { value := n } .integer
def number (v : Rat) : Token := .number { value := v } .number
def dimension (v : Rat) (unit : String) (flag : NumberFlag := .integer)
    (sign : Option Sign := none) : Token :=
  .dimension { value := v, sign := sign } flag unit.toList

/-- The text that a list of tokens is written as. -/
def written (tokens : List Token) : String := String.ofList (serialize tokens)

/-! ## The tokens of what the picture kit writes -/

def keyframes : String :=
  "@keyframes m0 { from { translate: -60px 0px } to { translate: 0px 0px } }"

#guard tokenizeText keyframes ==
  [atKeyword "keyframes", ws, ident "m0", ws, .openCurly, ws,
    ident "from", ws, .openCurly, ws, ident "translate", .colon, ws,
    dimension (-60) "px" .integer (some .minus), ws, dimension 0 "px", ws, .closeCurly, ws,
    ident "to", ws, .openCurly, ws, ident "translate", .colon, ws,
    dimension 0 "px", ws, dimension 0 "px", ws, .closeCurly, ws, .closeCurly]

def cubicAnimation : String :=
  "animation: m2 94.2ms cubic-bezier(0.333333, 1, 0.666667, 1) 180ms both; stroke-dasharray: 1000;"

-- A duration written to a tenth of a millisecond is the rational number 471/5, of type
-- "number"; a whole one is of type "integer". `cubic-bezier(` is one function token.
#guard tokenizeText cubicAnimation ==
  [ident "animation", .colon, ws, ident "m2", ws, dimension (471 / 5) "ms" .number, ws,
    function "cubic-bezier", number (333333 / 1000000), .comma, ws, integer 1, .comma, ws,
    number (666667 / 1000000), .comma, ws, integer 1, .closeParen, ws,
    dimension 180 "ms", ws, ident "both", .semicolon, ws,
    ident "stroke-dasharray", .colon, ws, integer 1000, .semicolon]

def springAnimation : String :=
  "animation: m3 126ms linear(0, 0.059, 0.195, 0.363, 0.531, 0.681, 0.804, 0.898, " ++
    "0.964, 1.007, 1.032, 1.043, 1.045, 1.041, 1.034, 1.026, 1.019, 1.012, 1.007, 1.003, 1) " ++
    "474ms both; transform-box: fill-box; transform-origin: center;"

/-- The values of the number tokens of a list, in thousandths. -/
def thousandths (tokens : List Token) : List Rat :=
  tokens.filterMap fun
    | .number n _ => some (n.value * 1000)
    | _ => none

-- The twenty-one stops of the spring, read exactly.
#guard thousandths (tokenizeText springAnimation) ==
  [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026, 1019, 1012,
    1007, 1003, 1000]

#guard (tokenizeText springAnimation).take 8 ==
  [ident "animation", .colon, ws, ident "m3", ws, dimension 126 "ms", ws, function "linear"]

def shapeDeclaration : String := "d: path(\"M0,0C1.5,2 3,4 -5,6\")"

-- The path data is one string token: nothing inside it is a token of CSS.
#guard tokenizeText shapeDeclaration ==
  [ident "d", .colon, ws, function "path", string "M0,0C1.5,2 3,4 -5,6", .closeParen]

-- A delay of less than nothing, and the `paused` that a step opened at a moment has.
#guard tokenizeText "m0 90ms linear(0, 1) -120.5ms both paused" ==
  [ident "m0", ws, dimension 90 "ms", ws, function "linear", integer 0, .comma, ws, integer 1,
    .closeParen, ws, dimension (-241 / 2) "ms" .number (some .minus), ws, ident "both", ws,
    ident "paused"]

/-! ## Readers: the law speaks of these tokens -/

-- Each list is writable, so `tokenize_serialize` says that it comes back.
#guard [keyframes, cubicAnimation, springAnimation, shapeDeclaration].all fun css =>
  Writable (tokenizeText css)

-- And the writer writes the kit's own text back, code point for code point: no comment is put
-- in, and every number has the digits it had.
#guard [keyframes, cubicAnimation, springAnimation, shapeDeclaration].all fun css =>
  written (tokenizeText css) == css

-- A style sheet has a line feed between two rules: it is a whitespace token like a space, and
-- is written back as a space.
#guard written (tokenizeText (keyframes ++ "\n" ++ keyframes)) == keyframes ++ " " ++ keyframes

-- A sheet of four hundred rules, some thirty thousand code points, in one pass.
#guard (tokenizeText ("\n".intercalate (List.replicate 400 keyframes))).length == 400 * 33 + 399

/-! ## Preprocessing and comments -/

-- A carriage return and a line feed are one line feed; a form feed is one; U+0000 is U+FFFD.
#guard filterCodePoints "a\r\nb\rc\x0cd\x00".toList == "a\nb\nc\nd�".toList

-- A comment gives no token, and the whitespace on its two sides is two tokens: the standard
-- lets a writer and a reader differ by that, and `collapse` is that.
#guard tokenizeText "a /* note */ b" == [ident "a", ws, ws, ident "b"]
#guard collapse (tokenizeText "a /* note */ b") == [ident "a", ws, ident "b"]
#guard written (tokenizeText "a /* note */ b") == "a  b"

-- A comment that the end of the input closes is a parse error and gives no token.
#guard tokenizeText "a/* open" == [ident "a"]

/-! ## Controls: why a comment goes between two tokens -/

/-- A text with no comment anywhere. -/
def bare (tokens : List Token) : String := String.ofList (tokens.flatMap Token.text)

-- An identifier after an identifier (row "ident", column "ident"): one identifier.
#guard tokenizeText (bare [ident "a", ident "b"]) == [ident "ab"]
#guard written [ident "a", ident "b"] == "a/**/b"

-- An identifier `e3` after a number (row "number", column "ident"): the number 1000.
#guard tokenizeText (bare [integer 1, ident "e3"]) == [number 1000]
#guard written [integer 1, ident "e3"] == "1/**/e3"
#guard tokenizeText "1/**/e3" == [integer 1, ident "e3"]

-- A number after a number (row "number", column "number"): one number.
#guard tokenizeText (bare [integer 1, integer 2]) == [integer 12]

-- A delimiter `%` after a number (row "number", column "%"): a percentage.
#guard tokenizeText (bare [integer 1, .delim '%']) == [.percentage { value := 1 }]

-- A left parenthesis after an identifier (row "ident", column "("): a function token.
#guard tokenizeText (bare [ident "a", .openParen]) == [function "a"]

-- A delimiter `*` after a delimiter `/` (the last row): the start of a comment.
#guard tokenizeText (bare [.delim '/', .delim '*', ident "a"]) == []

-- A hyphen-minus after a number is not marked, and needs no mark: what may follow the
-- hyphen-minus without a comment does not go on an identifier.
#guard tokenizeText (bare [integer 1, .delim '-']) == [integer 1, .delim '-']
#guard written [integer 1, .delim '-', ident "a"] == "1-/**/a"

/-! ## Findings: two shapes that the table does not mark -/

/-- The text of a list written by the table alone, with none of `extraPairs`. -/
def byTable : List Token → List Char
  | [] => []
  | [a] => a.text
  | a :: b :: rest =>
    a.text ++ (if tableMarks a b then "/**/".toList else []) ++ byTable (b :: rest)

-- The identifier `--` and then a delimiter `>`. A text has those two tokens, and the table
-- marks nothing between them; written so, they are a CDC token.
#guard tokenizeText "--/**/>" == [ident "--", .delim '>']
#guard tableMarks (ident "--") (.delim '>') == false
#guard tokenize (byTable [ident "--", .delim '>']) == [.cdc]
#guard written [ident "--", .delim '>'] == "--/**/>"

-- A delimiter `<`, a delimiter `!`, and an identifier that starts with two hyphen-minus. A
-- text has those three tokens, and the table marks neither pair; written so, they start with a
-- CDO token.
#guard tokenizeText "<!/**/--x" == [.delim '<', .delim '!', ident "--x"]
#guard tableMarks (.delim '<') (.delim '!') == false && tableMarks (.delim '!') (ident "--x") == false
#guard tokenize (byTable [.delim '<', .delim '!', ident "--x"]) == [.cdo, ident "x"]
#guard tokenize (byTable [.delim '<', .delim '!', .cdc]) == [.cdo, .delim '>']
#guard written [.delim '<', .delim '!', ident "--x"] == "</**/!--x"

/-- Tokens of each kind, for the sweep below. -/
def sample : List Token :=
  (["a", "e", "--", "--x", "-a", "url", "u"].map ident) ++ (["a", "--"].map function) ++
  [atKeyword "a", .hash "a".toList .id, .hash "1".toList .unrestricted, string "a"] ++
  (((List.range 128).map Char.ofNat).filter isDelimiter).map Token.delim ++
  [integer 1, number (3 / 2), .number { value := -1, sign := some .minus } .integer,
    .number { value := 1, sign := some .plus } .integer, .percentage { value := 1 },
    dimension 1 "px", dimension 1 "e", ws, .cdo, .cdc, .colon, .semicolon, .comma, .openSquare,
    .closeSquare, .openParen, .closeParen, .openCurly, .closeCurly]

-- Over every pair of the sample that a writer may write, the table alone fails at one pair.
#guard (sample.flatMap fun a => sample.filterMap fun b =>
    if Writable [a, b] && tokenize (byTable [a, b]) != collapse [a, b] then some (a, b) else none) ==
  [(ident "--", .delim '>')]

/-! ## The table as data -/

-- The marks of each row of `serialization-tables`, counted: seventy-seven in all.
#guard serializationTable.map (fun row => row.2.count true) == [10, 9, 9, 9, 9, 9, 9, 6, 3, 3, 1]
#guard serializationTable.all fun row => row.2.length == 12

/-! ## Controls: the premise -/

-- A delimiter that holds a reverse solidus is written with a newline, which is read back as
-- whitespace: with no whitespace token after it, one more token comes back.
#guard Writable [.delim '\\'] == false
#guard tokenize (serialize [.delim '\\']) == [.delim '\\', ws]
#guard Writable [.delim '\\', ws] && tokenize (serialize [.delim '\\', ws]) == [.delim '\\', ws]

-- The same holds of a bad string, which the tokenizer gives only before a newline.
#guard tokenizeText "\"a\nb" == [.badString, ws, ident "b"]
#guard Writable [.badString, ws, ident "b"]

-- A function token named `url` before anything but a string starts a url token.
#guard Writable [function "url", ident "x", .closeParen] == false
#guard tokenize (serialize [function "url", ident "x", .closeParen]) == [.url "x".toList]
#guard Writable [function "url", string "x", .closeParen]

-- A value with no decimal text is not writable; neither is a sign character against the value.
#guard (integer 1).writable && (number (1 / 8)).writable && !(number (1 / 3)).writable
#guard !(Token.number { value := 1, sign := some .minus } .integer).writable
#guard !(Token.number { value := 1 / 2 } .integer).writable

-- A number of type "number" with a whole value keeps its type: it is written with a fraction.
#guard written [number 1] == "1.0" && tokenizeText "1.0" == [number 1]
#guard tokenizeText "1e3" == [number 1000] && written [number 1000] == "1000.0"

-- An identifier with no code point is no token at all.
#guard !(ident "").writable && tokenize (serialize [ident ""]) == []

-- A hash token whose value starts as an identifier does is of type "id" whatever was asked.
#guard !(Token.hash "a".toList .unrestricted).writable
#guard tokenize (serialize [.hash "a".toList .unrestricted]) == [.hash "a".toList .id]

-- A delimiter holds a code point that starts no other token.
#guard !(Token.delim 'a').writable && !(Token.delim '1').writable && !(Token.delim '(').writable

/-! ## Escapes: inside the premise, and outside it -/

/-- Whether a list comes back, by evaluation. -/
def comesBack (tokens : List Token) : Bool := tokenize (serialize tokens) == collapse tokens

-- A unit that would be read as an exponent has its first code point escaped (the third rule
-- of `serialization-tables`). A unit that needs an escape is outside the premise; these come
-- back by evaluation.
#guard written [dimension 1 "e3"] == "1\\65 3" && comesBack [dimension 1 "e3"]
#guard written [dimension 1 "e-3"] == "1\\65 -3" && comesBack [dimension 1 "e-3"]
#guard tokenizeText "1e3" != [dimension 1 "e3"] && !(dimension 1 "e3").writable

-- A name that needs an escape, as CSSOM's "serialize an identifier" writes it. Every name
-- with a code point and no U+0000 is inside the premise, so the law speaks of these.
#guard written [ident "1a"] == "\\31 a" && comesBack [ident "1a"]
#guard written [ident "-"] == "\\-" && comesBack [ident "-"]
#guard written [ident "-1"] == "-\\31 " && comesBack [ident "-1"]
#guard written [ident "a b"] == "a\\ b" && comesBack [ident "a b"]
#guard written [ident "a\nb"] == "a\\a b" && comesBack [ident "a\nb"]
#guard comesBack [.hash "1a".toList .unrestricted, .hash "1a".toList .id, atKeyword "a.b"]
#guard Writable [ident "1a", ws, ident "-", ws, ident "-1", ws, ident "a b", ws, ident "a\nb", ws,
  .hash "1a".toList .unrestricted, .hash "1a".toList .id, atKeyword "a.b", function "a b"]
#guard !(ident "a\x00b").writable

-- CSSOM writes a code point from U+0080 up as itself. The tokenizer of CSS Syntax 3 does not
-- take U+00D7 in a name, so the writer escapes it.
#guard tokenizeText "a×b" == [ident "a", .delim '×', ident "b"]
#guard written [ident "a×b"] == "a\\×b" && comesBack [ident "a×b"] && (ident "a×b").writable

-- A string with a quotation mark, a reverse solidus, a newline and a control character is
-- inside the premise; here is its text.
#guard written [string "a\"b\\c\nd\x01"] == "\"a\\\"b\\\\c\\a d\\1 \""
#guard Writable [string "a\"b\\c\nd\x01"]

-- A url token and a bad url token are outside the premise; these come back by evaluation.
#guard written [.url "a b)c".toList] == "url(a\\ b\\)c)" && comesBack [.url "a b)c".toList]
#guard comesBack [.badUrl, ident "a"] && !(Token.url "a".toList).writable && !Token.badUrl.writable

-- A unicode-range token is given only where a caller allows it, and `tokenize` does not.
#guard consumeToken "U+26-3F x".toList true == some (.unicodeRange 0x26 0x3F, " x".toList)
#guard consumeToken "u+4??".toList true == some (.unicodeRange 0x400 0x4FF, [])
#guard tokenizeText "U+26" == [ident "U", .number { value := 26, sign := some .plus } .integer]

end WhatwgTest.Css.Syntax
