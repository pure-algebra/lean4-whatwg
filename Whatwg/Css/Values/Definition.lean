
/-!
# Whatwg.Css.Values.Definition

Owner: the Value Definition Syntax of CSS as data (slice K3 of `docs/CSS-PACKAGE-PLAN.md`;
rulings CS-2 and CS-4): the tree of a definition, one printer and one reader.

The authority is CSS Values and Units Module Level 4, section "Value Definition Syntax"
(anchor `value-defs`), with its parts `component-types`, `component-combinators`,
`component-multipliers`, `combinator-multiplier-patterns`, `component-whitespace`,
`component-functions` and `production-blocks`, and `numeric-ranges` for a bracketed range. The
sealed authority is `vendor/w3c-csswg-drafts-50337328/css-values-4/Overview.bs`, the Bikeshed
source at the pinned commit of `w3c/csswg-drafts` (blob `8c0e7713`). A sentence quoted in this
module is that file's, under the anchor named beside it.

What this module gives:

- `Definition`: the tree. It has four forms, and each is a rule of the standard. An `Atom` is
  a component that holds no other: a keyword, a delimiter, a name in angle brackets. A `nest`
  is a definition inside brackets, parentheses, braces or a function. A `combine` is two parts
  or more under one of the four combinators. A `mult` is a part with a multiplier after it.
  The names a hand writes are `Definition.keyword`, `Definition.type`, `Definition.function`,
  `Definition.seq`, `Definition.one` and the others below the tree.
- `Definition.print`: one spelling of a tree, spaced as the standard spaces its examples:
  `none | [ <number> | <percentage> ]{1,3}`.
- `Definition.read`: the tree of a text. It is two steps. `lex` cuts the text into lexemes
  and skips white space. `parse` nests them by their brackets and splits each level at `|`,
  then `||`, then `&&`, then into parts with their multipliers: the standard's precedence.
- `Definition.wf`: the trees the printer writes with nothing lost. A tree that is not of them
  is still a value, but it prints as the text of another tree: brackets that are missing are
  not written. Every collected line reads as one (`WhatwgTest/Css/Values.lean`); that the
  reader gives no other tree is not proved.
- `Definition.leanTerm`: a tree as a term of Lean, for the generated data modules.

The law is `Definition.read_print` of `Whatwg/Css/Values/Definition/Laws.lean`: reading what
was printed gives the tree back, for every tree with `wf`.

Why the reader and the printer are two functions and not one `Syn` of
`Whatwg/Svg/Value/Grammar.lean` (ruling SV-25). A `Syn` describes a regular grammar, and this
one nests: brackets and function arguments hold whole definitions. A set of characters of
`Syn` is a mask over ASCII, and a range is written with U+221E. And `Syn.read` takes one
character to decide a choice, where `|` and `||`, a keyword and a function name, `{` as a
brace and `{2}` as a multiplier each need more.

What this module does not claim:

- That a tree means anything. `Whatwg/Css/Values/Admits.lean` gives a definition its meaning.
- That the reader takes every text the standard would call a definition. It refuses a bound
  of a range with a fraction, `{A,B}` with a space inside, a function with no argument, and a
  multiplier stack the standard does not list. Each is a refusal, never another tree.
- That a name is a known one. `<no-such-type>` reads.
-/

namespace Whatwg.Css.Values

/-! ## The tree -/

/-- One end of a bracketed range (`numeric-ranges`): "Range extremes that are ideally
unlimited are indicated using ∞ or −∞ as appropriate." A finite end is a whole number with the
unit it is written with: `0`, `0s`, `180deg`. -/
inductive Bound where
  /-- `-∞`: no lower limit. -/
  | negInfinity
  /-- `∞`: no upper limit. -/
  | infinity
  /-- A whole number and its unit, which is empty where none is written. -/
  | finite (value : Int) (unit : String)
  deriving DecidableEq, Repr, Inhabited

/-- A bracketed range (`numeric-ranges`): "`[min,max]` within the angle brackets, after the
identifying keyword, indicating a closed range between (and including) min and max." -/
structure Range where
  /-- The least value. -/
  min : Bound
  /-- The greatest value. -/
  max : Bound
  deriving DecidableEq, Repr, Inhabited

/-- A component that holds no other (`component-types`). -/
inductive Atom where
  /-- "Keyword values (such as `auto`, `disc`, etc.) … which appear literally, without
  quotes". -/
  | keyword (name : String)
  /-- "at-keywords representing the start of an at-rule, which appear literally": `@media`.
  The name is without its `@`. -/
  | atKeyword (name : String)
  /-- "Delimiters, which represent their corresponding tokens. Slashes (`/`), commas (`,`),
  colons (`:`), semicolons (`;`) … are written literally." Parentheses and braces are an
  `Enclosure`. -/
  | literal (c : Char)
  /-- "Other delimiters must be written enclosed in single quotes (such as `'+'`)." -/
  | quoted (text : String)
  /-- "Basic data types, which appear between `<` and `>`", and "Other non-terminals. These
  are written as the name of the non-terminal between `<` and `>`". The range is the
  bracketed range of a numeric type: `<number [0,∞]>`. -/
  | type (name : String) (range : Option Range)
  /-- A function "referenced by a non-terminal using the function's name, followed
  by an empty parentheses pair, between `<` and `>`, e.g. `<calc()>`". The name is without
  its parentheses. -/
  | functionType (name : String)
  /-- "Property value ranges, which represent the same pattern of values as a property bearing
  the same name. These are written as the property name, surrounded by single quotes, between
  `<` and `>`, e.g., `<'border-width'>`". -/
  | property (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- What holds a definition inside it. -/
inductive Enclosure where
  /-- "Brackets (`[ ]`) are for grouping" (`component-combinators`). -/
  | brackets
  /-- Parentheses written literally (`component-types`, item 6): `( <calc-sum> )`. -/
  | parens
  /-- Braces written literally (`component-types`, item 6): `{ <declaration-list> }`. -/
  | braces
  /-- "The function's name written as an identifier followed by an open parenthesis", "The
  function's arguments", "A literal closing parenthesis" (`component-functions`). -/
  | function (name : String)
  /-- "or the `<function-token>` production to indicate a function with an arbitrary name"
  (`component-functions`): `<function-token> <any-value> )`. -/
  | anyFunction
  deriving DecidableEq, Repr, Inhabited

/-- A combinator (`component-combinators`). "Juxtaposition is stronger than the double
ampersand, the double ampersand is stronger than the double bar, and the double bar is
stronger than the bar." -/
inductive Combinator where
  /-- "Juxtaposing components means that all of them must occur, in the given order." -/
  | seq
  /-- "A double ampersand (`&&`) separates two or more components, all of which must occur,
  in any order." -/
  | all
  /-- "A double bar (`||`) separates two or more options: one or more of them must occur, in
  any order." -/
  | any
  /-- "A bar (`|`) separates two or more alternatives: exactly one of them must occur." -/
  | one
  deriving DecidableEq, Repr, Inhabited

/-- The three forms in curly braces (`component-multipliers`). -/
inductive Repeat where
  /-- "A single number in curly braces (`{A}`) indicates that the preceding type, word, or
  group occurs A times." -/
  | exactly (a : Nat)
  /-- "A comma-separated pair of numbers in curly braces (`{A,B}`) indicates that the
  preceding type, word, or group occurs at least A and at most B times." -/
  | between (a b : Nat)
  /-- "The B may be omitted (`{A,}`) to indicate that there must be at least A repetitions,
  with no upper bound on the number of repetitions." -/
  | atLeast (a : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A multiplier (`component-multipliers`). -/
inductive Multiplier where
  /-- "An asterisk (`*`) indicates that the preceding type, word, or group occurs zero or more
  times." -/
  | star
  /-- "A plus (`+`) indicates that the preceding type, word, or group occurs one or more
  times." -/
  | plus
  /-- "A question mark (`?`) indicates that the preceding type, word, or group is optional
  (occurs zero or one times)." -/
  | opt
  /-- `{A}`, `{A,B}` or `{A,}`. -/
  | times (r : Repeat)
  /-- "A hash mark (`#`) indicates that the preceding type, word, or group occurs one or more
  times, separated by comma tokens … It may optionally be followed by the curly brace forms,
  above, to indicate precisely how many times the repetition occurs, like `<length>#{1,4}`."
  So `#{1,4}` is one multiplier, and it is not `#` under `{1,4}`. -/
  | hash (r : Option Repeat)
  /-- "An exclamation point (`!`) after a group indicates that the group is required and must
  produce at least one value". -/
  | req
  deriving DecidableEq, Repr, Inhabited

/-- A definition in the Value Definition Syntax.

A stack of multipliers is a `mult` of a `mult`: `+#` is `#` of `+`. "These stacks each
represent the later multiplier applied to the result of the earlier multiplier"
(`component-multipliers`). -/
inductive Definition where
  /-- A component that holds no other. -/
  | atom (a : Atom)
  /-- A definition inside brackets, parentheses, braces or a function. -/
  | nest (e : Enclosure) (inner : Definition)
  /-- Parts under one combinator. "Combinators are not associative, so grouping is
  significant" (`component-combinators`): `a || b || c` is one `combine` of three parts. -/
  | combine (c : Combinator) (parts : List Definition)
  /-- A part and the multiplier after it. -/
  | mult (inner : Definition) (m : Multiplier)
  deriving Inhabited

mutual

/-- Two definitions are equal or not: by the form, then part by part. -/
def Definition.decEq : (a b : Definition) → Decidable (a = b)
  | .atom a, .atom b =>
    if h : a = b then isTrue (congrArg Definition.atom h)
    else isFalse fun e => h (Definition.atom.inj e)
  | .nest e x, .nest f y =>
    if h : e = f then
      match Definition.decEq x y with
      | isTrue hx => isTrue (by rw [h, hx])
      | isFalse hx => isFalse fun e => hx (Definition.nest.inj e).2
    else isFalse fun e => h (Definition.nest.inj e).1
  | .combine c ps, .combine d qs =>
    if h : c = d then
      match Definition.decEqList ps qs with
      | isTrue hp => isTrue (by rw [h, hp])
      | isFalse hp => isFalse fun e => hp (Definition.combine.inj e).2
    else isFalse fun e => h (Definition.combine.inj e).1
  | .mult x m, .mult y n =>
    if h : m = n then
      match Definition.decEq x y with
      | isTrue hx => isTrue (by rw [h, hx])
      | isFalse hx => isFalse fun e => hx (Definition.mult.inj e).1
    else isFalse fun e => h (Definition.mult.inj e).2
  | .atom _, .nest _ _ => isFalse nofun
  | .atom _, .combine _ _ => isFalse nofun
  | .atom _, .mult _ _ => isFalse nofun
  | .nest _ _, .atom _ => isFalse nofun
  | .nest _ _, .combine _ _ => isFalse nofun
  | .nest _ _, .mult _ _ => isFalse nofun
  | .combine _ _, .atom _ => isFalse nofun
  | .combine _ _, .nest _ _ => isFalse nofun
  | .combine _ _, .mult _ _ => isFalse nofun
  | .mult _ _, .atom _ => isFalse nofun
  | .mult _ _, .nest _ _ => isFalse nofun
  | .mult _ _, .combine _ _ => isFalse nofun

/-- Two lists of definitions are equal or not. -/
def Definition.decEqList : (as bs : List Definition) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match Definition.decEq a b, Definition.decEqList as bs with
    | isTrue h, isTrue hs => isTrue (by rw [h, hs])
    | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
    | _, isFalse hs => isFalse fun e => hs (List.cons.inj e).2
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun

end

instance : DecidableEq Definition := Definition.decEq

namespace Definition

/-! ## The names a hand writes

Each is one form of the tree. A generated data module is written with them
(`Definition.leanTerm`). -/

/-- A keyword: `auto`. -/
def keyword (name : String) : Definition := .atom (.keyword name)

/-- An at-keyword, named without its `@`: `@media`. -/
def atKeyword (name : String) : Definition := .atom (.atKeyword name)

/-- A delimiter written literally: `/`, `,`, `:` or `;`. -/
def literal (c : Char) : Definition := .atom (.literal c)

/-- A delimiter in single quotes: `'+'`. -/
def quoted (text : String) : Definition := .atom (.quoted text)

/-- A name in angle brackets, with its bracketed range where it has one: `<number [0,∞]>`. -/
def type (name : String) (range : Option Range) : Definition := .atom (.type name range)

/-- A function named in angle brackets: `<calc()>`. -/
def functionType (name : String) : Definition := .atom (.functionType name)

/-- The grammar of a property: `<'border-width'>`. -/
def property (name : String) : Definition := .atom (.property name)

/-- A bracketed group: `[ inner ]`. -/
def group (inner : Definition) : Definition := .nest .brackets inner

/-- Parentheses written literally: `( inner )`. -/
def parens (inner : Definition) : Definition := .nest .parens inner

/-- Braces written literally: `{ inner }`. -/
def braces (inner : Definition) : Definition := .nest .braces inner

/-- A function and its arguments: `name( arguments )`. -/
def function (name : String) (arguments : Definition) : Definition :=
  .nest (.function name) arguments

/-- A function of any name: `<function-token> arguments )`. -/
def anyFunction (arguments : Definition) : Definition := .nest .anyFunction arguments

/-- A juxtaposition: `a b c`. -/
def seq (parts : List Definition) : Definition := .combine .seq parts

/-- `a && b && c`. -/
def all (parts : List Definition) : Definition := .combine .all parts

/-- `a || b || c`. -/
def any (parts : List Definition) : Definition := .combine .any parts

/-- `a | b | c`. -/
def one (parts : List Definition) : Definition := .combine .one parts

end Definition

/-! ## Characters -/

/-- White space between two lexemes: space, tab, line feed, carriage return, form feed. -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- A character of a keyword or of a name: an ASCII letter or digit, `-` or `_`. -/
def isWord (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- A character of the unit of a bound: an ASCII letter or `%`. -/
def isUnit (c : Char) : Bool := (c.isAlpha || c == '%') && !c.isDigit

/-- The name between angle brackets that is no type: it opens a function of any name. -/
def functionToken : List Char :=
  ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n', '-', 't', 'o', 'k', 'e', 'n']

/-- A character a keyword or a name opens with: one of `isWord` that is no digit, as an
identifier of CSS opens with none. -/
def isStart (c : Char) : Bool := isWord c && !c.isDigit

/-- Characters of a keyword or of a name the reader can give: the first of `isStart`, the
others of `isWord`. -/
def isNameChars : List Char → Bool
  | [] => false
  | c :: cs => isStart c && cs.all isWord

/-- A keyword or a name the reader can give. -/
def isName (n : String) : Bool := isNameChars n.toList

/-! ## Lexemes

A lexeme is one mark of a definition's text. An atom is one lexeme: `<number [0,∞]>` is read
whole. A function name is one with its parenthesis: `scale(`. -/

/-- What closes an enclosure. -/
inductive Closer where
  /-- `]`. -/
  | square
  /-- `)`. -/
  | paren
  /-- `}`. -/
  | curly
  deriving DecidableEq, Repr, Inhabited

/-- What closes an enclosure of each kind. A function closes with a parenthesis. -/
def Enclosure.closer : Enclosure → Closer
  | .brackets => .square
  | .braces => .curly
  | .parens | .function _ | .anyFunction => .paren

/-- One mark of a definition's text. -/
inductive Lexeme where
  /-- An atom. -/
  | atom (a : Atom)
  /-- `&&`, `||` or `|`. Juxtaposition has no mark. -/
  | op (c : Combinator)
  /-- A multiplier. `#{A,B}` is two lexemes, `#` and `{A,B}`. -/
  | mult (m : Multiplier)
  /-- What opens an enclosure: `[`, `(`, `{`, `name(` or `<function-token>`. -/
  | enter (e : Enclosure)
  /-- What closes one. -/
  | leave (c : Closer)
  deriving DecidableEq, Repr, Inhabited

/-! ## The printer -/

/-- A natural number in decimal digits. -/
def natText (n : Nat) : List Char := Nat.toDigits 10 n

/-- A whole number in decimal digits, with `-` before a negative one. -/
def intText : Int → List Char
  | .ofNat n => natText n
  | .negSucc n => '-' :: natText (n + 1)

/-- A bound as written. The printer writes U+002D before `∞`; the reader also takes U+2212,
which the standard's prose writes. -/
def Bound.text : Bound → List Char
  | .negInfinity => ['-', '∞']
  | .infinity => ['∞']
  | .finite v u => intText v ++ u.toList

/-- A range as written: `[0,∞]`. -/
def Range.text (r : Range) : List Char := '[' :: r.min.text ++ ',' :: r.max.text ++ [']']

/-- An atom as written. -/
def Atom.text : Atom → List Char
  | .keyword n => n.toList
  | .atKeyword n => '@' :: n.toList
  | .literal c => [c]
  | .quoted t => '\'' :: t.toList ++ ['\'']
  | .type n none => '<' :: n.toList ++ ['>']
  | .type n (some r) => '<' :: n.toList ++ ' ' :: r.text ++ ['>']
  | .functionType n => '<' :: n.toList ++ ['(', ')', '>']
  | .property n => '<' :: '\'' :: n.toList ++ ['\'', '>']

/-- What stands between the curly braces of a repeat. -/
def Repeat.body : Repeat → List Char
  | .exactly a => natText a
  | .between a b => natText a ++ ',' :: natText b
  | .atLeast a => natText a ++ [',']

/-- A multiplier as written. -/
def Multiplier.text : Multiplier → List Char
  | .star => ['*']
  | .plus => ['+']
  | .opt => ['?']
  | .times r => '{' :: r.body ++ ['}']
  | .hash none => ['#']
  | .hash (some r) => '#' :: '{' :: r.body ++ ['}']
  | .req => ['!']

/-- A lexeme as written. -/
def Lexeme.text : Lexeme → List Char
  | .atom a => a.text
  | .op .seq => []
  | .op .all => ['&', '&']
  | .op .any => ['|', '|']
  | .op .one => ['|']
  | .mult m => m.text
  | .enter .brackets => ['[']
  | .enter .parens => ['(']
  | .enter .braces => ['{']
  | .enter (.function n) => n.toList ++ ['(']
  | .enter .anyFunction => '<' :: functionToken ++ ['>']
  | .leave .square => [']']
  | .leave .paren => [')']
  | .leave .curly => ['}']

/-- The lexeme is a multiplier: it is written against what it follows. -/
def Lexeme.isMult : Lexeme → Bool
  | .mult _ => true
  | _ => false

/-- What is written before the next lexeme: nothing before a multiplier, one space before any
other. -/
def gap : List Lexeme → List Char
  | [] => []
  | t :: _ => if t.isMult then [] else [' ']

/-- Lexemes as one text. -/
def render : List Lexeme → List Char
  | [] => []
  | t :: ts => t.text ++ gap ts ++ render ts

/-- The lexemes between two parts of a combination: none for juxtaposition. -/
def Combinator.sep : Combinator → List Lexeme
  | .seq => []
  | c => [.op c]

/-- The lexemes of a multiplier: `#{A,B}` is `#` and `{A,B}`. -/
def Multiplier.lexemes : Multiplier → List Lexeme
  | .hash (some r) => [.mult (.hash none), .mult (.times r)]
  | m => [.mult m]

/-- Lists joined with a separator between two of them. -/
def joined {α : Type} (sep : List α) : List (List α) → List α
  | [] => []
  | x :: xs => x ++ xs.flatMap (sep ++ ·)

mutual

/-- The lexemes of a definition. No bracket is added: a tree with `wf` needs none. -/
def Definition.lexemes : Definition → List Lexeme
  | .atom a => [.atom a]
  | .nest e x => .enter e :: x.lexemes ++ [.leave e.closer]
  | .combine c ps => joined c.sep (Definition.lexemesList ps)
  | .mult x m => x.lexemes ++ m.lexemes

/-- The lexemes of each definition of a list. -/
def Definition.lexemesList : List Definition → List (List Lexeme)
  | [] => []
  | p :: ps => p.lexemes :: Definition.lexemesList ps

end

/-- A definition as text: one spelling. -/
def Definition.print (d : Definition) : String := String.ofList (render d.lexemes)

/-! ## The reader: text to lexemes -/

/-- The number of decimal digits. -/
def readNat (digits : List Char) : Nat := Nat.ofDigitChars 10 digits 0

/-- What stands between the curly braces of a repeat: `A`, `A,B` or `A,`. No space is read. -/
def readRepeat (s : List Char) : Option Repeat :=
  if (s.takeWhile Char.isDigit).isEmpty then none
  else
    match s.dropWhile Char.isDigit with
    | [] => some (.exactly (readNat (s.takeWhile Char.isDigit)))
    | ',' :: b =>
      if b.isEmpty then some (.atLeast (readNat (s.takeWhile Char.isDigit)))
      else if b.all Char.isDigit then
        some (.between (readNat (s.takeWhile Char.isDigit)) (readNat b))
      else none
    | _ => none

/-- Digits and a unit: `0`, `0s`, `180deg`. A fraction is refused. -/
def readMagnitude (s : List Char) : Option (Nat × String) :=
  if (s.takeWhile Char.isDigit).isEmpty || !(s.dropWhile Char.isDigit).all isUnit then none
  else some (readNat (s.takeWhile Char.isDigit), String.ofList (s.dropWhile Char.isDigit))

/-- One end of a range: `∞`, `-∞` (with U+002D or U+2212), or a whole number with its unit. -/
def readBound : List Char → Option Bound
  | [] => none
  | c :: t =>
    if c.isDigit then (readMagnitude (c :: t)).map fun p => .finite (Int.ofNat p.1) p.2
    else if c == '∞' then (if t.isEmpty then some .infinity else none)
    else if c == '-' then
      if t == ['∞'] then some .negInfinity
      else (readMagnitude t).map fun p => .finite (-(Int.ofNat p.1)) p.2
    else if c == Char.ofNat 0x2212 then (if t == ['∞'] then some .negInfinity else none)
    else none

/-- The two ends of a range, each read. -/
def rangeOf : Option Bound → Option Bound → Option Range
  | some lo, some hi => some ⟨lo, hi⟩
  | _, _ => none

/-- A range with its white space removed: `[min,max]`. -/
def readRange : List Char → Option Range
  | '[' :: body =>
    match body.dropWhile (· != ',') with
    | ',' :: rest =>
      if rest.dropWhile (· != ']') == [']'] then
        rangeOf (readBound (body.takeWhile (· != ','))) (readBound (rest.takeWhile (· != ']')))
      else none
    | _ => none
  | _ => none

/-- What stands between `<` and `>`: `'name'`, `name`, `name()`, or `name [min,max]` with
white space anywhere in the range. `function-token` alone opens a function of any name. -/
def readAngle : List Char → Option Lexeme
  | [] => none
  | c :: t =>
    if c == '\'' then
      if isNameChars (t.takeWhile isWord) && t.dropWhile isWord == ['\''] then
        some (.atom (.property (String.ofList (t.takeWhile isWord))))
      else none
    else if !isStart c then none
    else if (((c :: t).dropWhile isWord).filter (fun x => !isSpace x)).isEmpty then
      if (c :: t).takeWhile isWord == functionToken then some (.enter .anyFunction)
      else some (.atom (.type (String.ofList ((c :: t).takeWhile isWord)) none))
    else if ((c :: t).dropWhile isWord).filter (fun x => !isSpace x) == ['(', ')'] then
      some (.atom (.functionType (String.ofList ((c :: t).takeWhile isWord))))
    else
      (readRange (((c :: t).dropWhile isWord).filter (fun x => !isSpace x))).map fun r =>
        .atom (.type (String.ofList ((c :: t).takeWhile isWord)) (some r))

/-- A keyword, or a function name with its parenthesis. -/
def lexWord (s : List Char) : Option (Lexeme × List Char) :=
  if (s.dropWhile isWord).head? == some '(' then
    some (.enter (.function (String.ofList (s.takeWhile isWord))), (s.dropWhile isWord).tail)
  else some (.atom (.keyword (String.ofList (s.takeWhile isWord))), s.dropWhile isWord)

/-- An at-keyword, after its `@`. -/
def lexAt (s : List Char) : Option (Lexeme × List Char) :=
  if isNameChars (s.takeWhile isWord) then
    some (.atom (.atKeyword (String.ofList (s.takeWhile isWord))), s.dropWhile isWord)
  else none

/-- A name in angle brackets, after its `<`. -/
def lexAngle (s : List Char) : Option (Lexeme × List Char) :=
  match s.dropWhile (· != '>') with
  | '>' :: rest => (readAngle (s.takeWhile (· != '>'))).map fun t => (t, rest)
  | _ => none

/-- A quoted delimiter, after its first quote. -/
def lexQuoted (s : List Char) : Option (Lexeme × List Char) :=
  match s.dropWhile (· != '\'') with
  | '\'' :: rest => some (.atom (.quoted (String.ofList (s.takeWhile (· != '\'')))), rest)
  | _ => none

/-- `|` or `||`, after the first bar. -/
def lexBar (s : List Char) : Option (Lexeme × List Char) :=
  if s.head? == some '|' then some (.op .any, s.tail) else some (.op .one, s)

/-- `&&`, after the first ampersand. -/
def lexAmp : List Char → Option (Lexeme × List Char)
  | '&' :: rest => some (.op .all, rest)
  | _ => none

/-- After `{`: a repeat where the text to the next `}` is one, and an open brace otherwise. -/
def lexBrace (s : List Char) : Option (Lexeme × List Char) :=
  match readRepeat (s.takeWhile (· != '}')) with
  | none => some (.enter .braces, s)
  | some r =>
    if (s.dropWhile (· != '}')).head? == some '}' then
      some (.mult (.times r), (s.dropWhile (· != '}')).tail)
    else some (.enter .braces, s)

/-- A lexeme of one character. A bare `*`, `+`, `?`, `!` or `#` is a multiplier: as a
delimiter each is written in quotes. -/
def single (c : Char) : Option Lexeme :=
  if c == '*' then some (.mult .star)
  else if c == '+' then some (.mult .plus)
  else if c == '?' then some (.mult .opt)
  else if c == '!' then some (.mult .req)
  else if c == '#' then some (.mult (.hash none))
  else if c == '[' then some (.enter .brackets)
  else if c == '(' then some (.enter .parens)
  else if c == ']' then some (.leave .square)
  else if c == ')' then some (.leave .paren)
  else if c == '}' then some (.leave .curly)
  else if c == '/' || c == ',' || c == ':' || c == ';' then some (.atom (.literal c))
  else none

/-- The lexeme at the head of a text that does not open with white space, and what is left. -/
def lexOne : List Char → Option (Lexeme × List Char)
  | [] => none
  | c :: cs =>
    if isStart c then lexWord (c :: cs)
    else if c == '@' then lexAt cs
    else if c == '<' then lexAngle cs
    else if c == '\'' then lexQuoted cs
    else if c == '|' then lexBar cs
    else if c == '&' then lexAmp cs
    else if c == '{' then lexBrace cs
    else (single c).map fun t => (t, cs)

/-- The lexemes of a text, in at most `fuel` steps. A step skips one character of white space
or reads one lexeme. -/
def lexGo : Nat → List Char → Option (List Lexeme)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, c :: cs =>
    match lexOne (c :: cs) with
    | some (t, rest) => (lexGo fuel rest).map (t :: ·)
    | none => if isSpace c then lexGo fuel cs else none

/-- The lexemes of a text. A step consumes a character, so the length of the text is fuel
enough. -/
def lex (s : List Char) : Option (List Lexeme) := lexGo s.length s

/-! ## The reader: lexemes to a tree -/

/-- What one level of a definition is made of, once what its enclosures hold is read: terms,
the marks of combinators, and multipliers. -/
inductive Item where
  /-- An atom, or an enclosure with what it holds. -/
  | term (d : Definition)
  /-- `&&`, `||` or `|`. -/
  | op (c : Combinator)
  /-- A multiplier. -/
  | mult (m : Multiplier)
  deriving Inhabited

/-- The multiplier may follow the part (`component-multipliers`).

- "Every type, keyword, or bracketed group may be followed by one of the following
  modifiers". A delimiter and a function are taken too: CSS Syntax 3 writes `'+'?`, and SVG 2
  writes `,?`.
- "An exclamation point (`!`) after a group": after brackets only.
- "The `+` and `#` multipliers may be stacked as `+#`; similarly, the `#` and `?`
  multipliers, `{A}` and `?` multipliers, and `{A,B}` and `?` multipliers may be stacked as
  `#?`, `{A}?`, and `{A,B}?`". No other stack is taken. Two that follow each other are
  judged, so `+#?` is taken, which the sentence does not list. -/
def canTake : Definition → Multiplier → Bool
  | .nest .brackets _, _ => true
  | _, .req => false
  | .atom _, _ => true
  | .nest _ _, _ => true
  | .mult _ .plus, .hash _ => true
  | .mult _ (.hash _), .opt => true
  | .mult _ (.times _), .opt => true
  | _, _ => false

/-- A part with one more multiplier. `{A,B}` after `#` makes the one multiplier `#{A,B}`. -/
def attach (f : Definition) (m : Multiplier) : Option Definition :=
  match f, m with
  | .mult x (.hash none), .times r => some (.mult x (.hash (some r)))
  | f, m => if canTake f m then some (.mult f m) else none

/-- The part being read, put with the parts that are done. -/
def push : Option Definition → List Definition → List Definition
  | some f, done => f :: done
  | none, done => done

/-- The parts of a juxtaposition: each a term with the multipliers after it. `current` is the
part being read, `done` the ones before it, last first. -/
def factors : List Item → Option Definition → List Definition → Option (List Definition)
  | [], current, done => some (push current done).reverse
  | .term d :: is, current, done => factors is (some d) (push current done)
  | .mult m :: is, some f, done =>
    match attach f m with
    | some g => factors is (some g) done
    | none => none
  | .mult _ :: _, none, _ => none
  | .op _ :: _, _, _ => none

/-- A juxtaposition: one part is itself, and two or more are a `combine`. -/
def readSeq (is : List Item) : Option Definition :=
  match factors is none [] with
  | some [f] => some f
  | some (f :: g :: fs) => some (.combine .seq (f :: g :: fs))
  | _ => none

/-- The item is the mark of the combinator. -/
def Item.isOp (c : Combinator) : Item → Bool
  | .op c' => c' == c
  | _ => false

/-- The items cut at each mark of the combinator: what is before the first mark, and what is
after each. -/
def split (c : Combinator) : List Item → List Item × List (List Item)
  | [] => ([], [])
  | i :: is =>
    if i.isOp c then ([], (split c is).1 :: (split c is).2)
    else (i :: (split c is).1, (split c is).2)

/-- Every piece read, or nothing. -/
def mapAll (f : List Item → Option Definition) : List (List Item) → Option (List Definition)
  | [] => some []
  | x :: xs =>
    match f x, mapAll f xs with
    | some d, some ds => some (d :: ds)
    | _, _ => none

/-- One level of precedence: the items cut at the marks of `c`, each piece read by `lower`.
One piece is itself, and two or more are a `combine`. -/
def level (c : Combinator) (lower : List Item → Option Definition) (is : List Item) :
    Option Definition :=
  match (split c is).2 with
  | [] => lower (split c is).1
  | others => (mapAll lower ((split c is).1 :: others)).map (.combine c)

/-- The reader of one level and of every stronger one. `|` is the weakest, so `readAt .one`
reads a whole level. -/
def readAt : Combinator → List Item → Option Definition
  | .seq => readSeq
  | .all => level .all readSeq
  | .any => level .any (level .all readSeq)
  | .one => level .one (level .any (level .all readSeq))

/-- The definition of one level. -/
def assemble : List Item → Option Definition := readAt .one

/-- Lexemes to a tree. `acc` holds the items of the level being read, last first. `stack`
holds the enclosures that are open, each with the items before it. A closer must be the one
its enclosure asks for, and what it closes is read as one level. -/
def build : List Lexeme → List Item → List (Enclosure × List Item) → Option Definition
  | [], acc, [] => assemble acc.reverse
  | [], _, _ :: _ => none
  | .atom a :: ts, acc, stack => build ts (.term (.atom a) :: acc) stack
  | .op c :: ts, acc, stack => build ts (.op c :: acc) stack
  | .mult m :: ts, acc, stack => build ts (.mult m :: acc) stack
  | .enter e :: ts, acc, stack => build ts [] ((e, acc) :: stack)
  | .leave _ :: _, _, [] => none
  | .leave c :: ts, acc, (e, outer) :: stack =>
    if e.closer = c then
      match assemble acc.reverse with
      | some d => build ts (.term (.nest e d) :: outer) stack
      | none => none
    else none

/-- The tree of a list of lexemes. -/
def parse (ts : List Lexeme) : Option Definition := build ts [] []

/-- The tree of a text, or nothing where the text is no definition this reader takes. -/
def Definition.read (s : String) : Option Definition := (lex s.toList).bind parse

/-! ## The trees the reader gives -/

/-- A bound the reader can give: its unit is letters, or `%`. -/
def Bound.wf : Bound → Bool
  | .finite _ u => u.toList.all isUnit
  | _ => true

/-- A range the reader can give. -/
def Range.wf (r : Range) : Bool := r.min.wf && r.max.wf

/-- An atom the reader can give. `<function-token>` is no type: it opens a function. -/
def Atom.wf : Atom → Bool
  | .keyword n => isName n
  | .atKeyword n => isName n
  | .literal c => c == '/' || c == ',' || c == ':' || c == ';'
  | .quoted t => t.toList.all (· != '\'')
  | .type n none => isName n && n.toList != functionToken
  | .type n (some r) => isName n && r.wf
  | .functionType n => isName n
  | .property n => isName n

/-- An enclosure the reader can give. -/
def Enclosure.wf : Enclosure → Bool
  | .function n => isName n
  | _ => true

/-- How weakly a combinator binds: juxtaposition is the strongest. -/
def Combinator.rank : Combinator → Nat
  | .seq => 0
  | .all => 1
  | .any => 2
  | .one => 3

/-- The definition may stand as a part under `c` with no brackets: it is no combination, or
its combinator binds more strongly than `c`. -/
def Definition.standsUnder (c : Combinator) : Definition → Bool
  | .combine c' _ => decide (c'.rank < c.rank)
  | _ => true

mutual

/-- A tree the reader gives, and so one the printer writes with nothing lost. A combination
has two parts or more, each of which stands under it with no brackets; a multiplier follows a
part that may take it. -/
def Definition.wf : Definition → Bool
  | .atom a => a.wf
  | .nest e x => e.wf && x.wf
  | .combine c ps => decide (2 ≤ ps.length) && Definition.wfParts c ps
  | .mult x m => x.wf && canTake x m

/-- Every part is a tree the reader gives and stands under `c`. -/
def Definition.wfParts (c : Combinator) : List Definition → Bool
  | [] => true
  | p :: ps => p.wf && p.standsUnder c && Definition.wfParts c ps

end

/-! ## A tree as a term of Lean -/

/-- A natural number as a term. -/
def natLean (n : Nat) : String := String.ofList (natText n)

/-- A bound as a term. -/
def Bound.leanTerm : Bound → String
  | .negInfinity => ".negInfinity"
  | .infinity => ".infinity"
  | .finite (.ofNat n) u => ".finite " ++ natLean n ++ " " ++ u.quote
  | .finite (.negSucc n) u => ".finite (-" ++ natLean (n + 1) ++ ") " ++ u.quote

/-- An optional range as a term. -/
def rangeLean : Option Range → String
  | none => "none"
  | some r => "(some ⟨" ++ r.min.leanTerm ++ ", " ++ r.max.leanTerm ++ "⟩)"

/-- A repeat as a term. -/
def Repeat.leanTerm : Repeat → String
  | .exactly a => ".exactly " ++ natLean a
  | .between a b => ".between " ++ natLean a ++ " " ++ natLean b
  | .atLeast a => ".atLeast " ++ natLean a

/-- A multiplier as a term. -/
def Multiplier.leanTerm : Multiplier → String
  | .star => ".star"
  | .plus => ".plus"
  | .opt => ".opt"
  | .times r => "(.times (" ++ r.leanTerm ++ "))"
  | .hash none => "(.hash none)"
  | .hash (some r) => "(.hash (some (" ++ r.leanTerm ++ ")))"
  | .req => ".req"

/-- An atom as a term: one of the names a hand writes. -/
def Atom.leanTerm : Atom → String
  | .keyword n => ".keyword " ++ n.quote
  | .atKeyword n => ".atKeyword " ++ n.quote
  | .literal c => ".literal " ++ c.quote
  | .quoted t => ".quoted " ++ t.quote
  | .type n r => ".type " ++ n.quote ++ " " ++ rangeLean r
  | .functionType n => ".functionType " ++ n.quote
  | .property n => ".property " ++ n.quote

/-- The name a hand writes for a combination. -/
def Combinator.leanName : Combinator → String
  | .seq => ".seq"
  | .all => ".all"
  | .any => ".any"
  | .one => ".one"

mutual

/-- A definition as a term of Lean whose type is `Definition`: `.one [.keyword "none",
.type "transform-list" none]`. A generated data module holds one such term for each
production. -/
def Definition.leanTerm : Definition → String
  | .atom a => a.leanTerm
  | .nest .brackets x => ".group (" ++ x.leanTerm ++ ")"
  | .nest .parens x => ".parens (" ++ x.leanTerm ++ ")"
  | .nest .braces x => ".braces (" ++ x.leanTerm ++ ")"
  | .nest (.function n) x => ".function " ++ n.quote ++ " (" ++ x.leanTerm ++ ")"
  | .nest .anyFunction x => ".anyFunction (" ++ x.leanTerm ++ ")"
  | .combine c ps => c.leanName ++ " [" ++ ", ".intercalate (Definition.leanTerms ps) ++ "]"
  | .mult x m => ".mult (" ++ x.leanTerm ++ ") " ++ m.leanTerm

/-- The term of each definition of a list. -/
def Definition.leanTerms : List Definition → List String
  | [] => []
  | p :: ps => p.leanTerm :: Definition.leanTerms ps

end

end Whatwg.Css.Values
