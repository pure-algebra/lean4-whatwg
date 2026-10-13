import Whatwg.Css.Syntax.Tokenize

/-!
# Whatwg.Css.Syntax.Serialize

Owner: the writer of tokens (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; ruling CS-7).

The authority is the section `serialization` of CSS Syntax Module Level 3, sealed at
`vendor/w3c-csswg-drafts-50337328/css-syntax-3/Overview.bs`. It asks one thing of a writer:
that what it writes parses back to what it was given, up to runs of whitespace tokens. Its
note `serialization-tables` says how:

- a delimiter that holds a reverse solidus is written as the reverse solidus and a newline;
- a hash token of type "unrestricted" needs less escaping than one of type "id";
- the unit of a dimension may need an escape, so that it is not read as an exponent;
- two tokens whose pair the table marks are written with a comment between them.

What this module gives.

- `Token.text`: the text of one token.
- `serializationTable`: the table of the note, cell by cell, as data.
- `needsComment`: whether a comment goes between two tokens. It is the table, and two pairs
  more that the table does not mark and that do not tokenize back without a comment
  (`extraPairs`; the witnesses are in `WhatwgTest/Css/Syntax.lean`).
- `serialize`: the text of a list of tokens.
- `Token.writable`, `Writable`: what a writer's tokens must satisfy for the law of
  `Whatwg/Css/Syntax/Laws.lean` to hold, as a check that computes.

How an identifier and a string are written is not said by CSS Syntax 3: it leaves that to
CSSOM. The authority for both is the section "Common Serializing Idioms" of CSSOM, sealed at
`vendor/w3c-csswg-drafts-50337328/cssom-1/Overview.bs`: "escape a character", "escape a
character as code point", "serialize an identifier" and "serialize a string". One rule is
changed, and the change is forced: CSSOM writes every code point from U+0080 up as itself, and
the tokenizer of CSS Syntax 3 takes only the non-ASCII ident code points in a name. Here a
code point is written as itself where the tokenizer takes it in a name, and escaped otherwise.

How a number is written is not said by either: here it is the sign character, the digits of
the whole part, and for the type "number" a full stop and the digits after it. No exponent is
written. A url token is not written as CSSOM writes a url (a function and a string, which are
other tokens): it is `url(`, the value with escapes, and `)`.

What this module does not claim: that the text is the shortest, or the one a browser writes.
-/

namespace Whatwg.Css.Syntax

/-! ## Escapes (CSSOM, "Common Serializing Idioms", sealed under `vendor/.../cssom-1/`) -/

/-- "Escape a character": a reverse solidus and the character. -/
def escapeCharacter (c : Char) : List Char := ['\\', c]

/-- "Escape a character as code point": a reverse solidus, the code point in the fewest
hexadecimal digits, and one space. -/
def escapeAsCodePoint (c : Char) : List Char := '\\' :: (Nat.toDigits 16 c.toNat ++ [' '])

/-- A code point in U+0001 to U+001F, or U+007F: CSSOM escapes these as code points. -/
def isControl (c : Char) : Bool := (1 ≤ c.toNat && c.toNat ≤ 31) || c.toNat == 127

/-- One code point of a name, where no rule of position applies. U+0000 is written as U+FFFD,
as CSSOM says; a token that holds it is not writable, since it does not come back. -/
def serializeNameCodePoint (c : Char) : List Char :=
  if c.toNat = 0 then ['�']
  else if isControl c = true then escapeAsCodePoint c
  else if isIdent c = true then [c]
  else escapeCharacter c

/-- The code points of a name, each as `serializeNameCodePoint` writes it. A hash token of type
"unrestricted" is written so: it needs no rule for its first code points. -/
def serializeName : List Char → List Char
  | [] => []
  | c :: rest => serializeNameCodePoint c ++ serializeName rest

/-- "Serialize an identifier". The rules of position: a digit that comes first is escaped as a
code point; so is a digit that comes second after a hyphen-minus; a hyphen-minus that is the
whole identifier is escaped. Every other code point is written as `serializeNameCodePoint`
writes it. -/
def serializeIdentifier : List Char → List Char
  | [] => []
  | [c] =>
    if c = '-' then escapeCharacter c
    else if isDigit c = true then escapeAsCodePoint c
    else serializeNameCodePoint c
  | c :: d :: rest =>
    if isDigit c = true then escapeAsCodePoint c ++ serializeName (d :: rest)
    else if c = '-' ∧ isDigit d = true then c :: (escapeAsCodePoint d ++ serializeName rest)
    else serializeNameCodePoint c ++ serializeName (d :: rest)

/-- Whether a unit, written after a number, would be read as the number's exponent: an `e` or
an `E`, and then a digit, or a hyphen-minus and a digit. -/
def readsAsExponent (unit : List Char) : Bool :=
  (unit[0]? == some 'e' || unit[0]? == some 'E') &&
    (unit[1]?.any isDigit || (unit[1]? == some '-' && unit[2]?.any isDigit))

/-- The unit of a dimension: an identifier, with its first code point escaped where the unit
would be read as an exponent (the third rule of `serialization-tables`). -/
def serializeUnit (unit : List Char) : List Char :=
  match unit with
  | [] => []
  | c :: rest =>
    if readsAsExponent (c :: rest) = true then escapeAsCodePoint c ++ serializeName rest
    else serializeIdentifier (c :: rest)

/-- One code point of a string: "serialize a string" of CSSOM. -/
def serializeStringCodePoint (c : Char) : List Char :=
  if c.toNat = 0 then ['�']
  else if isControl c = true then escapeAsCodePoint c
  else if c = '"' ∨ c = '\\' then escapeCharacter c
  else [c]

/-- The code points of a string between its quotation marks. -/
def serializeStringValue : List Char → List Char
  | [] => []
  | c :: rest => serializeStringCodePoint c ++ serializeStringValue rest

/-- One code point of the value of a url token. A newline is escaped as a code point; a code
point that would end the url or make it a bad url is escaped; any other is written as itself. -/
def serializeUrlCodePoint (c : Char) : List Char :=
  if c.toNat = 0 then ['�']
  else if isNewline c = true then escapeAsCodePoint c
  else if isWhitespace c = true ∨ isNonPrintable c = true ∨ c = '"' ∨ c = '\'' ∨ c = '(' ∨ c = ')' ∨
      c = '\\' then escapeCharacter c
  else [c]

/-- The value of a url token between `url(` and `)`. -/
def serializeUrlValue : List Char → List Char
  | [] => []
  | c :: rest => serializeUrlCodePoint c ++ serializeUrlValue rest

/-! ## Numbers -/

/-- The count of digits after the full stop that a denominator needs: the least `k` with the
denominator dividing `10 ^ k`, looked for up to the binary length of the denominator. Where
there is none the count is of no use, and `Numeric.writable` says so. -/
def fractionDigits (den : Nat) : Nat :=
  go den (den.log2 + 1) 0
where
  go (den : Nat) : Nat → Nat → Nat
    | 0, k => k
    | fuel + 1, k => if 10 ^ k % den = 0 then k else go den fuel (k + 1)

/-- A number in exactly `k` digits, with zeros in front. -/
def fixedDigits (k n : Nat) : List Char :=
  List.replicate (k - (Nat.toDigits 10 n).length) '0' ++ Nat.toDigits 10 n

/-- The count of digits after the full stop in the text of a number: none for the type
"integer", and one at least for the type "number". -/
def Numeric.places (n : Numeric) : NumberFlag → Nat
  | .integer => 0
  | .number => max 1 (fractionDigits n.value.den)

/-- The text of a sign character. -/
def signText : Option Sign → List Char
  | none => []
  | some .plus => ['+']
  | some .minus => ['-']

/-- The text of a number: its sign character, the digits of the whole part, and for the type
"number" a full stop and the digits after it. -/
def Numeric.text (n : Numeric) (flag : NumberFlag) : List Char :=
  let k := n.places flag
  let scaled := n.value.num.natAbs * (10 ^ k / n.value.den)
  signText n.sign ++ (Nat.toDigits 10 (scaled / 10 ^ k) ++
    (if k = 0 then [] else '.' :: fixedDigits k (scaled % 10 ^ k)))

/-- The type a percentage is written in: it has none of its own. -/
def Numeric.percentageFlag (n : Numeric) : NumberFlag :=
  if n.value.den = 1 then .integer else .number

/-- Whether the tokenizer can give the number and `Numeric.text` writes it. The sign character
agrees with the value: a value under nothing has a hyphen-minus, and a value over nothing has
none or a plus sign. The type "integer" has a whole value. The value has a decimal text. -/
def Numeric.writable (n : Numeric) (flag : NumberFlag) : Bool :=
  (match n.sign with
    | some .minus => decide (n.value.num ≤ 0)
    | _ => decide (0 ≤ n.value.num)) &&
  (match flag with
    | .integer => n.value.den == 1
    | .number => 10 ^ n.places .number % n.value.den == 0)

/-! ## The text of a token -/

namespace Token

/-- The text of one token.

- An identifier, the name of a function, of an at-keyword, of a hash token of type "id", and a
  unit: `serializeIdentifier`, `serializeUnit`.
- A hash token of type "unrestricted": `serializeName`.
- A string: between quotation marks, `serializeStringValue`.
- A delimiter: its code point; a reverse solidus is followed by a newline (the first rule of
  `serialization-tables`). The newline is read back as whitespace, so a whitespace token has to
  follow.
- A bad string: a quotation mark and a newline. The tokenizer gives a bad string only before
  a newline, so the same holds of it.
- A bad url: `url(()`.
- Whitespace: one space. -/
def text : Token → List Char
  | .ident value => serializeIdentifier value
  | .function value => serializeIdentifier value ++ ['(']
  | .atKeyword value => '@' :: serializeIdentifier value
  | .hash value .id => '#' :: serializeIdentifier value
  | .hash value .unrestricted => '#' :: serializeName value
  | .string value => '"' :: (serializeStringValue value ++ ['"'])
  | .badString => ['"', '\n']
  | .url value => 'u' :: 'r' :: 'l' :: '(' :: (serializeUrlValue value ++ [')'])
  | .badUrl => ['u', 'r', 'l', '(', '(', ')']
  | .delim c => if c = '\\' then ['\\', '\n'] else [c]
  | .number n flag => n.text flag
  | .percentage n => n.text n.percentageFlag ++ ['%']
  | .dimension n flag unit => n.text flag ++ serializeUnit unit
  | .unicodeRange start stop =>
    'U' :: '+' :: (Nat.toDigits 16 start ++ '-' :: Nat.toDigits 16 stop)
  | .whitespace => [' ']
  | .cdo => ['<', '!', '-', '-']
  | .cdc => ['-', '-', '>']
  | .colon => [':']
  | .semicolon => [';']
  | .comma => [',']
  | .openSquare => ['[']
  | .closeSquare => [']']
  | .openParen => ['(']
  | .closeParen => [')']
  | .openCurly => ['{']
  | .closeCurly => ['}']

end Token

/-! ## The table of pairs (`serialization-tables`) -/

/-- The rows of the table, in its order. A single character is the delimiter that holds it. -/
inductive TableRow where
  | ident
  | atKeyword
  | hash
  | dimension
  | numberSign
  | minus
  | number
  | at
  | fullStop
  | plus
  | solidus
  deriving DecidableEq, Repr, Inhabited

/-- The columns of the table, in its order. A single character is the delimiter that holds it,
but for the left parenthesis, which is its own token. -/
inductive TableColumn where
  | ident
  | function
  | url
  | badUrl
  | minus
  | number
  | percentage
  | dimension
  | cdc
  | openParen
  | asterisk
  | percent
  deriving DecidableEq, Repr, Inhabited

/-- The place of a column in a row of cells. -/
def TableColumn.index : TableColumn → Nat
  | .ident => 0
  | .function => 1
  | .url => 2
  | .badUrl => 3
  | .minus => 4
  | .number => 5
  | .percentage => 6
  | .dimension => 7
  | .cdc => 8
  | .openParen => 9
  | .asterisk => 10
  | .percent => 11

/-- **The table of `serialization-tables`, cell by cell.** Each row has its twelve cells in
the order of the columns: `true` where the sealed table has its mark, `false` where the cell is
empty. -/
def TableRow.cells : TableRow → List Bool
  --               ident  func   url    badUrl -      number %age   dimen  CDC    (      *      %
  | .ident      => [true,  true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false]
  | .atKeyword  => [true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false, false]
  | .hash       => [true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false, false]
  | .dimension  => [true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false, false]
  | .numberSign => [true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false, false]
  | .minus      => [true,  true,  true,  true,  true,  true,  true,  true,  true,  false, false, false]
  | .number     => [true,  true,  true,  true,  false, true,  true,  true,  true,  false, false, true]
  | .at         => [true,  true,  true,  true,  true,  false, false, false, true,  false, false, false]
  | .fullStop   => [false, false, false, false, false, true,  true,  true,  false, false, false, false]
  | .plus       => [false, false, false, false, false, true,  true,  true,  false, false, false, false]
  | .solidus    => [false, false, false, false, false, false, false, false, false, false, true,  false]

/-- The rows of the table in its order, each with its cells: the table as one value, for a gate
that compares it with the sealed bytes. -/
def serializationTable : List (TableRow × List Bool) :=
  [.ident, .atKeyword, .hash, .dimension, .numberSign, .minus, .number, .at, .fullStop, .plus,
    .solidus].map fun row => (row, row.cells)

/-- Whether the table has its mark in a cell. -/
def TableRow.marks (row : TableRow) (column : TableColumn) : Bool :=
  row.cells[column.index]?.getD false

namespace Token

/-- The row of the table that a token shows up in, where it does. -/
def row? : Token → Option TableRow
  | .ident _ => some .ident
  | .atKeyword _ => some .atKeyword
  | .hash _ _ => some .hash
  | .dimension _ _ _ => some .dimension
  | .number _ _ => some .number
  | .delim c =>
    if c = '#' then some .numberSign
    else if c = '-' then some .minus
    else if c = '@' then some .at
    else if c = '.' then some .fullStop
    else if c = '+' then some .plus
    else if c = '/' then some .solidus
    else none
  | _ => none

/-- The column of the table that a token shows up in, where it does. -/
def column? : Token → Option TableColumn
  | .ident _ => some .ident
  | .function _ => some .function
  | .url _ => some .url
  | .badUrl => some .badUrl
  | .number _ _ => some .number
  | .percentage _ => some .percentage
  | .dimension _ _ _ => some .dimension
  | .cdc => some .cdc
  | .openParen => some .openParen
  | .delim c =>
    if c = '-' then some .minus
    else if c = '*' then some .asterisk
    else if c = '%' then some .percent
    else none
  | _ => none

end Token

/-- Whether the table marks a pair of tokens: the first shows up in a row, the second in a
column, and the cell has the mark. -/
def tableMarks (a b : Token) : Bool :=
  match a.row?, b.column? with
  | some row, some column => row.marks column
  | _, _ => false

/-- **Two pairs that the table does not mark and that need a comment.** The table is a note,
and these are findings against it; a guard of `WhatwgTest/Css/Syntax.lean` shows each.

- A delimiter `<` and then a delimiter `!`. Before two hyphen-minus the three are read as a
  CDO token: a text can have the tokens `<`, `!` and an identifier that starts with two
  hyphen-minus (it has a comment after the `!`), and written with no comment they start a
  CDO token.
- The identifier `--` and then a delimiter `>`. The tokenizer looks for `-->` before it looks
  for an identifier, so the two with no comment are a CDC token. -/
def extraPairs (a b : Token) : Bool :=
  (a == .delim '<' && b == .delim '!') || (a == .ident ['-', '-'] && b == .delim '>')

/-- Whether a comment goes between two tokens. -/
def needsComment (a b : Token) : Bool := tableMarks a b || extraPairs a b

/-! ## The text of a list of tokens -/

/-- What goes between two tokens: an empty comment where the pair needs one. -/
def separator (a b : Token) : List Char :=
  if needsComment a b = true then ['/', '*', '*', '/'] else []

/-- What is written after the token `a`: each later token, with what goes before it. -/
def serializeAfter : Token → List Token → List Char
  | _, [] => []
  | a, b :: rest => separator a b ++ (b.text ++ serializeAfter b rest)

/-- **The text of a list of tokens**: the text of each, and an empty comment between two that
need one. -/
def serialize : List Token → List Char
  | [] => []
  | a :: rest => a.text ++ serializeAfter a rest

/-- The tokens of a list with each run of whitespace tokens as one: the standard lets a
writer and a reader differ by that. -/
def collapse : List Token → List Token
  | [] => []
  | [a] => [a]
  | a :: b :: rest =>
    if a = .whitespace ∧ b = .whitespace then collapse (b :: rest) else a :: collapse (b :: rest)

/-- Whether no two whitespace tokens of a list are next to each other: such a list is its own
`collapse`. -/
def noWhitespaceRun : List Token → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => !(a == .whitespace && b == .whitespace) && noWhitespaceRun (b :: rest)

/-! ## What a writer's tokens must satisfy -/

/-- A name that the tokenizer can give as the value of an identifier, a function, an at-keyword
or a hash token of type "id": at least one code point, and no U+0000. `serializeIdentifier`
writes every such name, with the escapes it needs. -/
def isNameValue (name : List Char) : Bool := !name.isEmpty && name.all fun c => c.toNat != 0

/-- Whether the three code points at the start of a name would start an ident sequence. -/
def startsIdent (name : List Char) : Bool := wouldStartIdentSequence name[0]? name[1]? name[2]?

/-- A name that is written with no escape: every code point is an ident code point, and the
name starts as an identifier does. So it is not empty, does not start with a digit, and a
hyphen-minus at its start is followed by a hyphen-minus or an ident-start code point. -/
def isPlainIdentifier (name : List Char) : Bool := name.all isIdent && startsIdent name

/-- The value of a hash token of type "unrestricted" that is written with no escape: ident
code points, at least one, that do not start as an identifier does. -/
def isPlainRestrictedName (name : List Char) : Bool :=
  !name.isEmpty && name.all isIdent && !startsIdent name

/-- A code point that the tokenizer gives as a delimiter: not whitespace, not a quotation mark
or an apostrophe, not a punctuation token of its own, not a digit, not an ident-start code
point. -/
def isDelimiter (c : Char) : Bool :=
  !isWhitespace c && c != '"' && c != '\'' && c != '(' && c != ')' && c != ',' && c != ':' &&
    c != ';' && c != '[' && c != ']' && c != '{' && c != '}' && !isDigit c && !isIdentStart c

namespace Token

/-- **Whether a writer may write the token**: the tokenizer can give it, and `Token.text`
writes a text that reads back as it.

- An identifier, and the name of a function, of an at-keyword and of a hash token of type
  "id": `isNameValue`, which is every name the tokenizer can give.
- A hash token of type "unrestricted": `isPlainRestrictedName`.
- A string: no U+0000.
- A delimiter: `isDelimiter`.
- A number, a percentage, a dimension: `Numeric.writable`; a unit is a plain identifier that
  would not be read as an exponent. A unit that needs an escape is outside this slice.
- A url, a bad url and a unicode-range are outside this slice. -/
def writable : Token → Bool
  | .ident value => isNameValue value
  | .function value => isNameValue value
  | .atKeyword value => isNameValue value
  | .hash value .id => isNameValue value
  | .hash value .unrestricted => isPlainRestrictedName value
  | .string value => value.all fun c => c.toNat != 0
  | .url _ => false
  | .badUrl => false
  | .delim c => isDelimiter c
  | .number n flag => n.writable flag
  | .percentage n => n.writable n.percentageFlag
  | .dimension n flag unit => n.writable flag && isPlainIdentifier unit && !readsAsExponent unit
  | .unicodeRange _ _ => false
  | _ => true

/-- Whether `b` may come next after `a`. Three tokens say what follows them: a delimiter that
holds a reverse solidus and a bad string are followed by whitespace, as the tokenizer only
ever gives them; and a function token named `url` is followed by a string, since `url(` before
anything else starts a url token. -/
def mayPrecede (a b : Token) : Bool :=
  match a with
  | .delim c => c != '\\' || b == .whitespace
  | .badString => b == .whitespace
  | .function value =>
    !isUrlName value ||
      (match b with
        | .string _ => true
        | _ => false)
  | _ => true

/-- Whether a list may end with the token: not the three that say what follows them. -/
def mayEnd : Token → Bool
  | .delim c => c != '\\'
  | .badString => false
  | .function value => !isUrlName value
  | _ => true

end Token

/-- Whether the tokens after `a` are writable, `a` included. -/
def writableAfter : Token → List Token → Bool
  | a, [] => a.writable && a.mayEnd
  | a, b :: rest => a.writable && a.mayPrecede b && writableAfter b rest

/-- **Whether a writer may write the list**: each token is writable, and each of the three
tokens that say what follows them is followed by it. -/
def Writable : List Token → Bool
  | [] => true
  | a :: rest => writableAfter a rest

end Whatwg.Css.Syntax
