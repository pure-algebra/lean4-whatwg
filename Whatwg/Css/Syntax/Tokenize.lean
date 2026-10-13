import Whatwg.Css.Syntax.Tree

/-!
# Whatwg.Css.Syntax.Tokenize

Owner: the tokenizer of CSS (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; ruling CS-6).

The authority is CSS Syntax Module Level 3, sealed at
`vendor/w3c-csswg-drafts-50337328/css-syntax-3/Overview.bs`. Each algorithm under the heading
`tokenizer-algorithms` is one function here, named after it, and its docstring names the
algorithm by its heading identifier and follows its steps in the standard's order.

- `filterCodePoints`: the preprocessing of `input-preprocessing`.
- `consumeToken`: one token from a list of code points, and the code points after it. The end
  of the input is `none`, where the standard returns its EOF token.
- `tokenize`: every token of a list of code points, as `tokenization` says: consume a token
  until the end.

What is assumed of the input. `tokenize` reads a list of code points as the standard's
tokenizer reads its input stream: after preprocessing. It does not preprocess. A `Char` is
never a surrogate, so that part of preprocessing has nothing to do; `filterCodePoints` does the
rest, and `tokenizeText` is the two together. On an input that was not preprocessed `tokenize`
is still total: a carriage return, a form feed and U+0000 are then code points like any other,
and each comes out as a delimiter or inside a value.

How the standard's words are read here.

- The *next input code point* is the head of the list, and the EOF code point is `none`: a
  check on "the next two input code points" reads `input[0]?` and `input[1]?`.
- To *reconsume the current input code point* is to hand a callee the list with that code point
  still at its head.
- A *parse error* is not a value here. The tokenizer returns the tokens the standard says it
  returns, and a comment marks each place where the standard flags a parse error.
- A comment gives no token: `consumeComments` drops it.

What this module does not claim: that a browser tokenizes so. It claims a reading of the sealed
text. The laws about it are in `Whatwg/Css/Syntax/Laws.lean`: what a writer wrote tokenizes
back to the tokens it was given.
-/

namespace Whatwg.Css.Syntax

/-! ## Preprocessing the input stream (`input-preprocessing`) -/

/-- One code point filtered: a carriage return or a form feed becomes a line feed, and U+0000
becomes U+FFFD. -/
def filterCodePoint (c : Char) : Char :=
  if c = '\r' ∨ c = '\x0c' then '\n' else if c = '\x00' then '�' else c

/-- `input-preprocessing`, "filter code points". A carriage return, a form feed, and a
carriage return followed by a line feed each become one line feed; U+0000 becomes U+FFFD. A
surrogate cannot be a `Char`, so there is none to replace. -/
def filterCodePoints : List Char → List Char
  | [] => []
  | [c] => [filterCodePoint c]
  | c :: d :: rest =>
    if c = '\r' ∧ d = '\n' then '\n' :: filterCodePoints rest
    else filterCodePoint c :: filterCodePoints (d :: rest)

/-! ## Definitions (`tokenizer-definitions`) -/

/-- A digit: U+0030 to U+0039. -/
def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- A hex digit: a digit, or `A` to `F`, or `a` to `f`. -/
def isHexDigit (c : Char) : Bool :=
  isDigit c || (65 ≤ c.toNat && c.toNat ≤ 70) || (97 ≤ c.toNat && c.toNat ≤ 102)

/-- A letter: an uppercase letter or a lowercase letter. -/
def isLetter (c : Char) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122)

/-- A non-ASCII ident code point: the fifteen ranges of the standard's list, all inclusive. -/
def isNonAsciiIdent (c : Char) : Bool :=
  c.toNat == 0xB7 || (0xC0 ≤ c.toNat && c.toNat ≤ 0xD6) || (0xD8 ≤ c.toNat && c.toNat ≤ 0xF6) ||
  (0xF8 ≤ c.toNat && c.toNat ≤ 0x37D) || (0x37F ≤ c.toNat && c.toNat ≤ 0x1FFF) ||
  c.toNat == 0x200C || c.toNat == 0x200D || c.toNat == 0x203F || c.toNat == 0x2040 ||
  (0x2070 ≤ c.toNat && c.toNat ≤ 0x218F) || (0x2C00 ≤ c.toNat && c.toNat ≤ 0x2FEF) ||
  (0x3001 ≤ c.toNat && c.toNat ≤ 0xD7FF) || (0xF900 ≤ c.toNat && c.toNat ≤ 0xFDCF) ||
  (0xFDF0 ≤ c.toNat && c.toNat ≤ 0xFFFD) || 0x10000 ≤ c.toNat

/-- An ident-start code point: a letter, a non-ASCII ident code point, or U+005F LOW LINE. -/
def isIdentStart (c : Char) : Bool := isLetter c || isNonAsciiIdent c || c.toNat == 95

/-- An ident code point: an ident-start code point, a digit, or U+002D HYPHEN-MINUS. -/
def isIdent (c : Char) : Bool := isIdentStart c || isDigit c || c.toNat == 45

/-- A non-printable code point: U+0000 to U+0008, U+000B, U+000E to U+001F, or U+007F. -/
def isNonPrintable (c : Char) : Bool :=
  c.toNat ≤ 8 || c.toNat == 11 || (14 ≤ c.toNat && c.toNat ≤ 31) || c.toNat == 127

/-- A newline: U+000A LINE FEED. Preprocessing has turned the others into it. -/
def isNewline (c : Char) : Bool := c.toNat == 10

/-- Whitespace: a newline, U+0009 CHARACTER TABULATION, or U+0020 SPACE. -/
def isWhitespace (c : Char) : Bool := isNewline c || c.toNat == 9 || c.toNat == 32

/-- The number that a hex digit stands for. -/
def hexDigitValue (c : Char) : Nat :=
  if isDigit c then c.toNat - 48 else if c.toNat ≤ 70 then c.toNat - 55 else c.toNat - 87

/-- Hex digits interpreted as a hexadecimal number. -/
def hexValue (digits : List Char) : Nat := digits.foldl (fun n d => 16 * n + hexDigitValue d) 0

/-- What is left when a run is dropped from the front of a list is no longer than the list. -/
theorem length_dropWhile_le (p : Char → Bool) (l : List Char) :
    (l.dropWhile p).length ≤ l.length :=
  (List.dropWhile_sublist p).length_le

/-! ## The checks that consume nothing -/

/-- `starts-with-a-valid-escape`: check if two code points are a valid escape. The first is a
reverse solidus and the second is not a newline. The EOF code point is not a newline, so a
reverse solidus at the end of the input starts a valid escape. -/
def areValidEscape (c₁ c₂ : Option Char) : Bool :=
  c₁ == some '\\' && !c₂.any isNewline

/-- `would-start-an-identifier`: check if three code points would start an ident sequence. -/
def wouldStartIdentSequence (c₁ c₂ c₃ : Option Char) : Bool :=
  if c₁ = some '-' then c₂.any isIdentStart || c₂ == some '-' || areValidEscape c₂ c₃
  else if c₁.any isIdentStart then true
  else if c₁ = some '\\' then areValidEscape c₁ c₂
  else false

/-- `starts-with-a-number`: check if three code points would start a number. -/
def wouldStartNumber (c₁ c₂ c₃ : Option Char) : Bool :=
  if c₁ = some '+' ∨ c₁ = some '-' then c₂.any isDigit || (c₂ == some '.' && c₃.any isDigit)
  else if c₁ = some '.' then c₂.any isDigit
  else c₁.any isDigit

/-- A digit starts a number. -/
theorem wouldStartNumber_of_isDigit (c : Char) (c₂ c₃ : Option Char) (h : isDigit c = true) :
    wouldStartNumber (some c) c₂ c₃ = true := by
  have h₁ : c ≠ '+' := by rintro rfl; exact absurd h (by decide)
  have h₂ : c ≠ '-' := by rintro rfl; exact absurd h (by decide)
  have h₃ : c ≠ '.' := by rintro rfl; exact absurd h (by decide)
  simp only [wouldStartNumber, Option.some.injEq, h₁, h₂, h₃, or_self, if_false, Option.any_some, h]

/-- `starts-a-unicode-range`: check if three code points would start a unicode-range. -/
def wouldStartUnicodeRange (c₁ c₂ c₃ : Option Char) : Bool :=
  (c₁ == some 'U' || c₁ == some 'u') && c₂ == some '+' && (c₃ == some '?' || c₃.any isHexDigit)

/-! ## Comments -/

/-- The inside of a comment: every code point up to and including the first `*/`, or up to the
end of the input. What is returned is what follows. -/
def skipComment : List Char → List Char
  | [] => []
  | [_] => []
  | c :: d :: rest => if c = '*' ∧ d = '/' then rest else skipComment (d :: rest)

theorem skipComment_length_le (input : List Char) :
    (skipComment input).length ≤ input.length := by
  fun_induction skipComment input <;> grind

/-- `consume-comment`: consume comments. While the next two input code points are `/*`, consume
them and the comment they open. A comment that the end of the input closes is a parse error;
nothing is returned for it. -/
def consumeComments (input : List Char) : List Char :=
  match input with
  | [] => []
  | [c] => [c]
  | c :: d :: rest => if c = '/' ∧ d = '*' then consumeComments (skipComment rest) else c :: d :: rest
termination_by input.length
decreasing_by
  have := skipComment_length_le rest
  grind

theorem consumeComments_length_le (input : List Char) :
    (consumeComments input).length ≤ input.length := by
  fun_induction consumeComments input <;> grind [skipComment_length_le]

/-! ## Escapes and names -/

/-- The code point of an escape's hexadecimal number: U+FFFD where the number is zero, is for a
surrogate, or is greater than the maximum allowed code point. -/
def codePointOfHex (n : Nat) : Char :=
  if n = 0 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) ∨ 0x10FFFF < n then '�' else Char.ofNat n

/-- `consume-escaped-code-point`: consume an escaped code point. The reverse solidus has been
consumed. A hex digit: consume as many hex digits as possible, but no more than five more; if
the next input code point is whitespace, consume it as well; return the code point of the
number. The end of the input: a parse error, and U+FFFD. Anything else: that code point. -/
def consumeEscapedCodePoint : List Char → Char × List Char
  | [] => ('�', [])
  | c :: rest =>
    if isHexDigit c then
      let more := (rest.take 5).takeWhile isHexDigit
      let rest₁ := rest.drop more.length
      (codePointOfHex (hexValue (c :: more)), if rest₁[0]?.any isWhitespace then rest₁.drop 1 else rest₁)
    else (c, rest)

theorem consumeEscapedCodePoint_length_le (input : List Char) :
    (consumeEscapedCodePoint input).2.length ≤ input.length := by
  fun_cases consumeEscapedCodePoint input <;> grind

/-- `consume-name`: consume an ident sequence. An ident code point is appended to the result.
Where the stream starts with a valid escape, consume an escaped code point and append it.
Anything else is left in the input, and the result is returned. The check that the code points
would start an ident sequence is the caller's. -/
def consumeIdentSequence (input : List Char) : List Char × List Char :=
  match input with
  | [] => ([], [])
  | c :: rest =>
    if isIdent c then
      (c :: (consumeIdentSequence rest).1, (consumeIdentSequence rest).2)
    else if areValidEscape (some c) rest[0]? then
      ((consumeEscapedCodePoint rest).1 :: (consumeIdentSequence (consumeEscapedCodePoint rest).2).1,
        (consumeIdentSequence (consumeEscapedCodePoint rest).2).2)
    else ([], c :: rest)
termination_by input.length
decreasing_by
  all_goals
    have := consumeEscapedCodePoint_length_le rest
    grind

theorem consumeIdentSequence_length_le (input : List Char) :
    (consumeIdentSequence input).2.length ≤ input.length := by
  fun_induction consumeIdentSequence input <;> grind [consumeEscapedCodePoint_length_le]

/-- An ident sequence that starts with an ident code point or a valid escape is not empty: what
follows it is shorter than the input. -/
theorem consumeIdentSequence_length_lt (c : Char) (rest : List Char)
    (h : isIdent c = true ∨ areValidEscape (some c) rest[0]? = true) :
    (consumeIdentSequence (c :: rest)).2.length < (c :: rest).length := by
  have h₁ := consumeIdentSequence_length_le rest
  have h₂ := consumeIdentSequence_length_le (consumeEscapedCodePoint rest).2
  have h₃ := consumeEscapedCodePoint_length_le rest
  rw [consumeIdentSequence]
  grind

/-! ## Numbers -/

/-- The base-10 number that a number part writes: the digits before the full stop and the
digits after it, with the sign of its sign character. -/
def decimal (negative : Bool) (whole fraction : List Char) : Rat :=
  let magnitude : Rat :=
    (Nat.ofDigitChars 10 (whole ++ fraction) 0 : Rat) / ((10 ^ fraction.length : Nat) : Rat)
  if negative then -magnitude else magnitude

/-- A value multiplied by ten to the power of an exponent, given as its sign and its digits. -/
def scaleByTen (value : Rat) (negative : Bool) (exponent : Nat) : Rat :=
  if negative then value / ((10 ^ exponent : Nat) : Rat) else value * ((10 ^ exponent : Nat) : Rat)

/-- Step 2 of `consume-number`: a plus sign or a hyphen-minus is consumed and is the sign
character. -/
def consumeSign (input : List Char) : Option Sign × List Char :=
  if input[0]? = some '+' then (some .plus, input.drop 1)
  else if input[0]? = some '-' then (some .minus, input.drop 1)
  else (none, input)

/-- Steps 3, 4.2 and 5.3 of `consume-number`: while the next input code point is a digit,
consume it. -/
def consumeDigits (input : List Char) : List Char × List Char :=
  (input.takeWhile isDigit, input.dropWhile isDigit)

/-- Step 4 of `consume-number`: where the next two input code points are a full stop followed
by a digit, consume the full stop and the digits. `none` where there is no such part. -/
def consumeFraction (input : List Char) : Option (List Char) × List Char :=
  if input[0]? = some '.' ∧ input[1]?.any isDigit = true then
    (some (consumeDigits (input.drop 1)).1, (consumeDigits (input.drop 1)).2)
  else (none, input)

/-- Step 5 of `consume-number`: where the next two or three input code points are `E` or `e`,
then a hyphen-minus or a plus sign or neither, then a digit, consume the letter, the sign and
the digits. The result is whether the exponent is less than nothing, and its digits. -/
def consumeExponent (input : List Char) : Option (Bool × List Char) × List Char :=
  if input[0]? = some 'E' ∨ input[0]? = some 'e' then
    if input[1]?.any isDigit = true then
      (some (false, (consumeDigits (input.drop 1)).1), (consumeDigits (input.drop 1)).2)
    else if (input[1]? = some '-' ∨ input[1]? = some '+') ∧ input[2]?.any isDigit = true then
      (some (decide (input[1]? = some '-'), (consumeDigits (input.drop 2)).1),
        (consumeDigits (input.drop 2)).2)
    else (none, input)
  else (none, input)

/-- `consume-number`: consume a number. It returns a numeric value, a type that is "integer" or
"number", and a sign character or none.

1. The type is "integer"; the number part and the exponent part are empty.
2. A sign is consumed and is the sign character (`consumeSign`).
3. Digits are consumed into the number part.
4. A full stop followed by a digit: both and the digits after are consumed into the number
   part, and the type is "number" (`consumeFraction`).
5. An exponent is consumed into the exponent part, and the type is "number"
   (`consumeExponent`).
6. The value is the number part interpreted as a base-10 number (`decimal`), multiplied by ten
   to the power of the exponent part where there is one (`scaleByTen`).

The standard does not say more of "interpreting as a base-10 number" than those words. The
reading here is exact: the value is a rational number, and no digit is lost. The check that the
code points would start a number is the caller's. -/
def consumeNumber (input : List Char) : (Rat × NumberFlag × Option Sign) × List Char :=
  let sign := consumeSign input
  let whole := consumeDigits sign.2
  let fraction := consumeFraction whole.2
  let exponent := consumeExponent fraction.2
  let value := decimal (sign.1 == some .minus) whole.1 (fraction.1.getD [])
  ((match exponent.1 with
      | some (negative, digits) => scaleByTen value negative (Nat.ofDigitChars 10 digits 0)
      | none => value,
    if fraction.1.isSome || exponent.1.isSome then .number else .integer,
    sign.1),
   exponent.2)

theorem consumeSign_length_le (input : List Char) :
    (consumeSign input).2.length ≤ input.length := by
  fun_cases consumeSign input <;> grind

theorem consumeDigits_length_le (input : List Char) :
    (consumeDigits input).2.length ≤ input.length :=
  length_dropWhile_le isDigit input

theorem consumeFraction_length_le (input : List Char) :
    (consumeFraction input).2.length ≤ input.length := by
  have := consumeDigits_length_le (input.drop 1)
  fun_cases consumeFraction input <;> grind

theorem consumeExponent_length_le (input : List Char) :
    (consumeExponent input).2.length ≤ input.length := by
  have := consumeDigits_length_le (input.drop 1)
  have := consumeDigits_length_le (input.drop 2)
  fun_cases consumeExponent input <;> grind

theorem consumeNumber_length_le (input : List Char) :
    (consumeNumber input).2.length ≤ input.length := by
  have h₁ := consumeSign_length_le input
  have h₂ := consumeDigits_length_le (consumeSign input).2
  have h₃ := consumeFraction_length_le (consumeDigits (consumeSign input).2).2
  have h₄ := consumeExponent_length_le (consumeFraction (consumeDigits (consumeSign input).2).2).2
  simp only [consumeNumber]
  omega

/-- A number is not empty where the code points would start one: what follows it is shorter
than the input. -/
theorem consumeNumber_length_lt (c : Char) (rest : List Char)
    (h : wouldStartNumber (some c) rest[0]? rest[1]? = true) :
    (consumeNumber (c :: rest)).2.length < (c :: rest).length := by
  have h₂ := consumeDigits_length_le (consumeSign (c :: rest)).2
  have h₃ := consumeFraction_length_le (consumeDigits (consumeSign (c :: rest)).2).2
  have h₄ :=
    consumeExponent_length_le (consumeFraction (consumeDigits (consumeSign (c :: rest)).2).2).2
  have h₅ := consumeDigits_length_le rest
  have h₆ := consumeDigits_length_le (rest.drop 1)
  simp only [consumeNumber]
  simp only [wouldStartNumber] at h
  by_cases hs : c = '+' ∨ c = '-'
  · have : (consumeSign (c :: rest)).2 = rest := by
      rcases hs with rfl | rfl <;> rfl
    grind
  · have hsign : (consumeSign (c :: rest)).2 = c :: rest := by
      simp only [consumeSign, List.getElem?_cons_zero, Option.some.injEq]
      grind
    by_cases hd : isDigit c = true
    · have : (consumeDigits (c :: rest)).2 = (consumeDigits rest).2 := by
        simp only [consumeDigits, List.dropWhile_cons, hd, if_true]
      grind
    · have hdot : c = '.' := by grind
      subst hdot
      have hw : (consumeDigits ('.' :: rest)).2 = '.' :: rest := by
        simp only [consumeDigits, List.dropWhile_cons]
        rfl
      have hf : (consumeFraction ('.' :: rest)).2 = (consumeDigits rest).2 := by
        simp only [consumeFraction, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop_succ_cons,
          List.drop_zero]
        grind
      grind

/-! ## The tokens that take more than one code point -/

/-- The value of a string: `none` where the string is a bad string. -/
def consumeStringValue (ending : Char) (input : List Char) : Option (List Char) × List Char :=
  match input with
  | [] => (some [], [])  -- the end of the input: a parse error; the string token is returned
  | c :: rest =>
    if c = ending then (some [], rest)
    else if isNewline c then (none, c :: rest)  -- a parse error; the newline is reconsumed
    else if c = '\\' then
      match rest with
      | [] => (some [], [])  -- nothing to do; the end of the input then returns the string token
      | d :: rest' =>
        if isNewline d then consumeStringValue ending rest'
        else
          ((consumeStringValue ending (consumeEscapedCodePoint (d :: rest')).2).1.map
              ((consumeEscapedCodePoint (d :: rest')).1 :: ·),
            (consumeStringValue ending (consumeEscapedCodePoint (d :: rest')).2).2)
    else ((consumeStringValue ending rest).1.map (c :: ·), (consumeStringValue ending rest).2)
termination_by input.length
decreasing_by
  all_goals grind [consumeEscapedCodePoint_length_le]

/-- `consume-string-token`: consume a string token, with the ending code point given. The
opening quotation mark has been consumed. Code points are consumed one at a time:

- the ending code point: return the string token;
- the end of the input: a parse error; return the string token;
- a newline: a parse error; reconsume it and return a bad string token;
- a reverse solidus: at the end of the input, nothing; before a newline, consume the newline;
  otherwise consume an escaped code point and append it to the value;
- anything else: append it to the value. -/
def consumeStringToken (ending : Char) (input : List Char) : Token × List Char :=
  match (consumeStringValue ending input).1 with
  | some value => (.string value, (consumeStringValue ending input).2)
  | none => (.badString, (consumeStringValue ending input).2)

theorem consumeStringValue_length_le (ending : Char) (input : List Char) :
    (consumeStringValue ending input).2.length ≤ input.length := by
  fun_induction consumeStringValue ending input <;> grind [consumeEscapedCodePoint_length_le]

theorem consumeStringToken_length_le (ending : Char) (input : List Char) :
    (consumeStringToken ending input).2.length ≤ input.length := by
  have := consumeStringValue_length_le ending input
  fun_cases consumeStringToken ending input <;> grind

/-- `consume-remnants-of-bad-url`: consume the remnants of a bad url. Code points are consumed
one at a time: a right parenthesis or the end of the input returns; a valid escape is consumed,
so that an escaped right parenthesis does not end the bad url; anything else is dropped. -/
def consumeRemnantsOfBadUrl (input : List Char) : List Char :=
  match input with
  | [] => []
  | c :: rest =>
    if c = ')' then rest
    else if areValidEscape (some c) rest[0]? then
      consumeRemnantsOfBadUrl (consumeEscapedCodePoint rest).2
    else consumeRemnantsOfBadUrl rest
termination_by input.length
decreasing_by
  all_goals
    have := consumeEscapedCodePoint_length_le rest
    grind

theorem consumeRemnantsOfBadUrl_length_le (input : List Char) :
    (consumeRemnantsOfBadUrl input).length ≤ input.length := by
  fun_induction consumeRemnantsOfBadUrl input <;> grind [consumeEscapedCodePoint_length_le]

/-- The value of a url after its leading whitespace: `none` where the url is a bad url. -/
def consumeUrlValue (input : List Char) : Option (List Char) × List Char :=
  match input with
  | [] => (some [], [])  -- the end of the input: a parse error; the url token is returned
  | c :: rest =>
    if c = ')' then (some [], rest)
    else if isWhitespace c then
      match rest.dropWhile isWhitespace with
      | [] => (some [], [])  -- the end of the input: a parse error; the url token is returned
      | d :: rest' =>
        if d = ')' then (some [], rest') else (none, consumeRemnantsOfBadUrl (d :: rest'))
    else if c = '"' ∨ c = '\'' ∨ c = '(' ∨ isNonPrintable c = true then
      (none, consumeRemnantsOfBadUrl rest)  -- a parse error
    else if c = '\\' then
      if areValidEscape (some c) rest[0]? then
        ((consumeUrlValue (consumeEscapedCodePoint rest).2).1.map
            ((consumeEscapedCodePoint rest).1 :: ·),
          (consumeUrlValue (consumeEscapedCodePoint rest).2).2)
      else (none, consumeRemnantsOfBadUrl rest)  -- a parse error
    else ((consumeUrlValue rest).1.map (c :: ·), (consumeUrlValue rest).2)
termination_by input.length
decreasing_by
  all_goals
    have := consumeEscapedCodePoint_length_le rest
    grind

/-- `consume-url-token`: consume a url token. The `url(` has been consumed, and the value is not
quoted.

1. The url token starts with an empty value.
2. Consume as much whitespace as possible.
3. Code points are consumed one at a time:
   - a right parenthesis: return the url token;
   - the end of the input: a parse error; return the url token;
   - whitespace: consume as much whitespace as possible; a right parenthesis or the end of the
     input is consumed and the url token returned (the end is a parse error); otherwise consume
     the remnants of a bad url and return a bad url token;
   - a quotation mark, an apostrophe, a left parenthesis, a non-printable code point: a parse
     error; consume the remnants of a bad url and return a bad url token;
   - a reverse solidus: a valid escape is consumed and appended to the value; otherwise a parse
     error, the remnants of a bad url, and a bad url token;
   - anything else: append it to the value. -/
def consumeUrlToken (input : List Char) : Token × List Char :=
  match (consumeUrlValue (input.dropWhile isWhitespace)).1 with
  | some value => (.url value, (consumeUrlValue (input.dropWhile isWhitespace)).2)
  | none => (.badUrl, (consumeUrlValue (input.dropWhile isWhitespace)).2)

theorem consumeUrlValue_length_le (input : List Char) :
    (consumeUrlValue input).2.length ≤ input.length := by
  fun_induction consumeUrlValue input <;>
    grind [consumeEscapedCodePoint_length_le, consumeRemnantsOfBadUrl_length_le,
      length_dropWhile_le]

theorem consumeUrlToken_length_le (input : List Char) :
    (consumeUrlToken input).2.length ≤ input.length := by
  have := consumeUrlValue_length_le (input.dropWhile isWhitespace)
  have := length_dropWhile_le isWhitespace input
  fun_cases consumeUrlToken input <;> grind

/-- Whether a name is an ASCII case-insensitive match for "url". -/
def isUrlName (name : List Char) : Bool :=
  match name with
  | [u, r, l] => (u = 'u' ∨ u = 'U') ∧ (r = 'r' ∨ r = 'R') ∧ (l = 'l' ∨ l = 'L')
  | _ => false

/-- In `consume-ident-like-token`: while the next two input code points are whitespace, consume
the next input code point. One whitespace is left for the next token. -/
def consumeUrlLeadingWhitespace : List Char → List Char
  | [] => []
  | [c] => [c]
  | c :: d :: rest =>
    if isWhitespace c = true ∧ isWhitespace d = true then consumeUrlLeadingWhitespace (d :: rest)
    else c :: d :: rest

theorem consumeUrlLeadingWhitespace_length_le (input : List Char) :
    (consumeUrlLeadingWhitespace input).length ≤ input.length := by
  fun_induction consumeUrlLeadingWhitespace input <;> grind

/-- `consume-ident-like-token`: consume an ident-like token. It returns an ident token, a
function token, a url token or a bad url token.

Consume an ident sequence, the string.

- The string matches "url" and the next input code point is a left parenthesis: consume it.
  While the next two input code points are whitespace, consume the next. If the next one or two
  input code points are a quotation mark or an apostrophe, or whitespace followed by one of
  them, return a function token. Otherwise consume a url token and return it.
- Otherwise the next input code point is a left parenthesis: consume it and return a function
  token.
- Otherwise return an ident token. -/
def consumeIdentLikeToken (input : List Char) : Token × List Char :=
  let name := consumeIdentSequence input
  if name.2[0]? = some '(' then
    if isUrlName name.1 = true then
      let rest := consumeUrlLeadingWhitespace (name.2.drop 1)
      if rest[0]? = some '"' ∨ rest[0]? = some '\'' ∨
          (rest[0]?.any isWhitespace = true ∧ (rest[1]? = some '"' ∨ rest[1]? = some '\'')) then
        (.function name.1, rest)
      else consumeUrlToken rest
    else (.function name.1, name.2.drop 1)
  else (.ident name.1, name.2)

theorem consumeIdentLikeToken_length_le (input : List Char) :
    (consumeIdentLikeToken input).2.length ≤ (consumeIdentSequence input).2.length := by
  have h₁ := consumeUrlLeadingWhitespace_length_le ((consumeIdentSequence input).2.drop 1)
  have h₂ := consumeUrlToken_length_le
    (consumeUrlLeadingWhitespace ((consumeIdentSequence input).2.drop 1))
  simp only [consumeIdentLikeToken]
  grind

/-- `consume-numeric-token`: consume a numeric token. It returns a number token, a percentage
token or a dimension token.

Consume a number.

- The next three input code points would start an ident sequence: consume an ident sequence;
  return a dimension token with the number's value, type and sign character, and that unit.
- Otherwise the next input code point is a percentage sign: consume it, and return a percentage
  token with the number's value and sign character.
- Otherwise return a number token with the number's value, type and sign character. -/
def consumeNumericToken (input : List Char) : Token × List Char :=
  let number := consumeNumber input
  let numeric : Numeric := { value := number.1.1, sign := number.1.2.2 }
  if wouldStartIdentSequence number.2[0]? number.2[1]? number.2[2]? = true then
    (.dimension numeric number.1.2.1 (consumeIdentSequence number.2).1,
      (consumeIdentSequence number.2).2)
  else if number.2[0]? = some '%' then (.percentage numeric, number.2.drop 1)
  else (.number numeric number.1.2.1, number.2)

theorem consumeNumericToken_length_le (input : List Char) :
    (consumeNumericToken input).2.length ≤ (consumeNumber input).2.length := by
  have := consumeIdentSequence_length_le (consumeNumber input).2
  simp only [consumeNumericToken]
  grind

/-- `consume-unicode-range-token`: consume a unicode-range token. The check that the code
points would start one is the caller's.

1. Consume the next two input code points and drop them.
2. Consume as many hex digits as possible, but no more than six. With fewer than six, consume
   as many question marks as possible, but no more than make six in all. These are the first
   segment.
3. The first segment has a question mark: the range starts at the segment with a zero for each
   question mark, and ends at the segment with an `F` for each.
4. Otherwise the range starts at the first segment.
5. The next two input code points are a hyphen-minus followed by a hex digit: consume the
   hyphen-minus and as many hex digits as possible, but no more than six; the range ends there.
6. Otherwise the range ends where it starts. -/
def consumeUnicodeRangeToken (input : List Char) : Token × List Char :=
  let s := input.drop 2
  let digits := (s.take 6).takeWhile isHexDigit
  let s₁ := s.drop digits.length
  let marks := (s₁.take (6 - digits.length)).takeWhile (· = '?')
  let s₂ := s₁.drop marks.length
  if marks.isEmpty then
    if s₂[0]? = some '-' ∧ s₂[1]?.any isHexDigit = true then
      let last := ((s₂.drop 1).take 6).takeWhile isHexDigit
      (.unicodeRange (hexValue digits) (hexValue last), (s₂.drop 1).drop last.length)
    else (.unicodeRange (hexValue digits) (hexValue digits), s₂)
  else
    (.unicodeRange (hexValue (digits ++ marks.map fun _ => '0'))
      (hexValue (digits ++ marks.map fun _ => 'F')), s₂)

theorem consumeUnicodeRangeToken_length_le (input : List Char) :
    (consumeUnicodeRangeToken input).2.length ≤ (input.drop 2).length := by
  simp only [consumeUnicodeRangeToken]
  grind

/-! ## Consume a token -/

/-- `consume-token`: consume a token. `none` is the standard's EOF token. Unicode ranges are
allowed only where a caller says so; the default is that they are not.

Consume comments. Consume the next input code point, and look at it, in the standard's order:

- whitespace: consume as much whitespace as possible; a whitespace token;
- a quotation mark: consume a string token;
- a number sign: where the next input code point is an ident code point or the next two are a
  valid escape, a hash token, of type "id" where the next three would start an ident sequence;
  otherwise a delimiter;
- an apostrophe: consume a string token;
- a left or right parenthesis: its token;
- a plus sign: a numeric token where the stream starts with a number; otherwise a delimiter;
- a comma: its token;
- a hyphen-minus: a numeric token where the stream starts with a number; otherwise a CDC token
  where `->` follows; otherwise an ident-like token where the stream starts with an ident
  sequence; otherwise a delimiter;
- a full stop: a numeric token where the stream starts with a number; otherwise a delimiter;
- a colon, a semicolon: its token;
- a less-than sign: a CDO token where `!--` follows; otherwise a delimiter;
- a commercial at: an at-keyword token where the next three input code points would start an
  ident sequence; otherwise a delimiter;
- a left square bracket: its token;
- a reverse solidus: an ident-like token where the stream starts with a valid escape; otherwise
  a parse error, and a delimiter;
- a right square bracket, a left or right curly bracket: its token;
- a digit: a numeric token;
- `U` or `u`: a unicode-range token where they are allowed and the stream would start one;
  otherwise an ident-like token;
- an ident-start code point: an ident-like token;
- the end of the input: the EOF token;
- anything else: a delimiter. -/
def consumeToken (input : List Char) (unicodeRangesAllowed : Bool := false) :
    Option (Token × List Char) :=
  match consumeComments input with
  | [] => none
  | c :: rest =>
    if isWhitespace c = true then some (.whitespace, rest.dropWhile isWhitespace)
    else if c = '"' then some (consumeStringToken c rest)
    else if c = '#' then
      if rest[0]?.any isIdent = true ∨ areValidEscape rest[0]? rest[1]? = true then
        some (.hash (consumeIdentSequence rest).1
          (if wouldStartIdentSequence rest[0]? rest[1]? rest[2]? = true then .id else .unrestricted),
          (consumeIdentSequence rest).2)
      else some (.delim c, rest)
    else if c = '\'' then some (consumeStringToken c rest)
    else if c = '(' then some (.openParen, rest)
    else if c = ')' then some (.closeParen, rest)
    else if c = '+' then
      if wouldStartNumber (some c) rest[0]? rest[1]? = true then some (consumeNumericToken (c :: rest))
      else some (.delim c, rest)
    else if c = ',' then some (.comma, rest)
    else if c = '-' then
      if wouldStartNumber (some c) rest[0]? rest[1]? = true then some (consumeNumericToken (c :: rest))
      else if rest[0]? = some '-' ∧ rest[1]? = some '>' then some (.cdc, rest.drop 2)
      else if wouldStartIdentSequence (some c) rest[0]? rest[1]? = true then
        some (consumeIdentLikeToken (c :: rest))
      else some (.delim c, rest)
    else if c = '.' then
      if wouldStartNumber (some c) rest[0]? rest[1]? = true then some (consumeNumericToken (c :: rest))
      else some (.delim c, rest)
    else if c = ':' then some (.colon, rest)
    else if c = ';' then some (.semicolon, rest)
    else if c = '<' then
      if rest[0]? = some '!' ∧ rest[1]? = some '-' ∧ rest[2]? = some '-' then some (.cdo, rest.drop 3)
      else some (.delim c, rest)
    else if c = '@' then
      if wouldStartIdentSequence rest[0]? rest[1]? rest[2]? = true then
        some (.atKeyword (consumeIdentSequence rest).1, (consumeIdentSequence rest).2)
      else some (.delim c, rest)
    else if c = '[' then some (.openSquare, rest)
    else if c = '\\' then
      if areValidEscape (some c) rest[0]? = true then some (consumeIdentLikeToken (c :: rest))
      else some (.delim c, rest)  -- a parse error
    else if c = ']' then some (.closeSquare, rest)
    else if c = '{' then some (.openCurly, rest)
    else if c = '}' then some (.closeCurly, rest)
    else if isDigit c = true then some (consumeNumericToken (c :: rest))
    else if c = 'U' ∨ c = 'u' then
      if unicodeRangesAllowed = true ∧ wouldStartUnicodeRange (some c) rest[0]? rest[1]? = true then
        some (consumeUnicodeRangeToken (c :: rest))
      else some (consumeIdentLikeToken (c :: rest))
    else if isIdentStart c = true then some (consumeIdentLikeToken (c :: rest))
    else some (.delim c, rest)

/-- **A token takes code points.** Where `consumeToken` returns a token, what follows it is
shorter than the input: so tokenizing ends, and a caller that consumes tokens one at a time
makes progress. -/
theorem consumeToken_length_lt {input : List Char} {allowed : Bool} {token : Token}
    {rest : List Char} (h : consumeToken input allowed = some (token, rest)) :
    rest.length < input.length := by
  have hc := consumeComments_length_le input
  unfold consumeToken at h
  split at h
  · cases h
  · rename_i c tail heq
    rw [heq] at hc
    have h₁ := length_dropWhile_le isWhitespace tail
    have h₂ := consumeStringToken_length_le c tail
    have h₃ := consumeIdentSequence_length_le tail
    have h₄ := consumeNumericToken_length_le (c :: tail)
    have h₅ : wouldStartNumber (some c) tail[0]? tail[1]? = true →
        (consumeNumber (c :: tail)).2.length < (c :: tail).length := consumeNumber_length_lt c tail
    have h₆ : isDigit c = true → wouldStartNumber (some c) tail[0]? tail[1]? = true :=
      wouldStartNumber_of_isDigit c _ _
    have h₇ := consumeIdentLikeToken_length_le (c :: tail)
    have h₈ : isIdent c = true ∨ areValidEscape (some c) tail[0]? = true →
        (consumeIdentSequence (c :: tail)).2.length < (c :: tail).length :=
      consumeIdentSequence_length_lt c tail
    have h₉ := consumeUnicodeRangeToken_length_le (c :: tail)
    have h₁₀ : isIdentStart c = true → isIdent c = true := by
      intro hi
      simp only [isIdent, hi, Bool.true_or]
    have h₁₁ : c = '-' ∨ c = 'U' ∨ c = 'u' → isIdent c = true := by
      rintro (rfl | rfl | rfl) <;> decide
    grind (splits := 40)

/-! ## Tokenization (`tokenization`) -/

/-- `tokenization`: to tokenize a stream of code points, repeatedly consume a token until the
end of the input, and collect the tokens. The input is taken as preprocessed. -/
def tokenize (input : List Char) : List Token :=
  match _h : consumeToken input with
  | none => []
  | some (token, rest) => token :: tokenize rest
termination_by input.length
decreasing_by exact consumeToken_length_lt (by assumption)

/-- Tokenizing at the end of the input gives no token. -/
theorem tokenize_of_none {input : List Char} (h : consumeToken input = none) :
    tokenize input = [] := by
  rw [tokenize]
  split
  · rfl
  · rename_i heq
    rw [h] at heq
    cases heq

/-- Tokenizing is the first token and then the tokens of what follows it. -/
theorem tokenize_of_some {input rest : List Char} {token : Token}
    (h : consumeToken input = some (token, rest)) : tokenize input = token :: tokenize rest := by
  rw [tokenize]
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
    rfl

/-- The tokens of a text: preprocessing, then tokenizing. -/
def tokenizeText (text : String) : List Token := tokenize (filterCodePoints text.toList)

end Whatwg.Css.Syntax
