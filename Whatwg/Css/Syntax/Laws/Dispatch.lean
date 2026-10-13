import Whatwg.Css.Syntax.Serialize

/-!
# Whatwg.Css.Syntax.Laws.Dispatch

Owner: what `consumeToken` does at each first code point (slice K2 of
`docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

These are the laws that the round trip of `Whatwg/Css/Syntax/Laws.lean` is built from, and a
parser's laws will want the same: a comment gives no token; a run of whitespace is one token;
a code point that `consumeToken` does not name is a digit, an ident-start code point or a
delimiter; and where the next three code points would start an ident sequence, the token is
an ident-like token.

Nothing here is about a writer. Every law is about the tokenizer of the sealed text as
`Whatwg/Css/Syntax/Tokenize.lean` reads it.
-/

namespace Whatwg.Css.Syntax

/-! ## Code points -/

theorem ne_of_toNat_ne {c d : Char} (h : c.toNat ≠ d.toNat) : c ≠ d := fun e => h (e ▸ rfl)

theorem eq_of_toNat_eq {c d : Char} (h : c.toNat = d.toNat) : c = d :=
  Char.ext (UInt32.toNat_inj.mp h)

/-- The code points that `consumeToken` names one at a time: the two quotation marks, the
number sign, the brackets, and the punctuation. -/
def isNamed (c : Char) : Bool :=
  c.toNat == 34 || c.toNat == 35 || c.toNat == 39 || c.toNat == 40 || c.toNat == 41 ||
  c.toNat == 43 || c.toNat == 44 || c.toNat == 45 || c.toNat == 46 || c.toNat == 58 ||
  c.toNat == 59 || c.toNat == 60 || c.toNat == 64 || c.toNat == 91 || c.toNat == 92 ||
  c.toNat == 93 || c.toNat == 123 || c.toNat == 125

theorem isIdentStart_facts {c : Char} (h : isIdentStart c = true) :
    isWhitespace c = false ∧ isDigit c = false ∧ isNamed c = false ∧ isIdent c = true ∧
      c.toNat ≠ 47 ∧ c.toNat ≠ 10 ∧ c.toNat ≠ 37 ∧ c.toNat ≠ 42 ∧ c.toNat ≠ 33 := by
  simp only [isIdentStart, isLetter, isNonAsciiIdent, isWhitespace, isNewline, isDigit, isNamed, isIdent,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at h ⊢
  omega

theorem isDigit_facts {c : Char} (h : isDigit c = true) :
    isWhitespace c = false ∧ isIdentStart c = false ∧ isNamed c = false ∧ isIdent c = true ∧
      isHexDigit c = true ∧ c.toNat ≠ 47 ∧ c.toNat ≠ 10 := by
  simp only [isIdentStart, isLetter, isNonAsciiIdent, isWhitespace, isNewline, isDigit, isNamed, isIdent,
    isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at h ⊢
  omega

theorem isWhitespace_facts {c : Char} (h : isWhitespace c = true) :
    isDigit c = false ∧ isIdentStart c = false ∧ isNamed c = false ∧ isIdent c = false ∧
      c.toNat ≠ 47 ∧ c.toNat ≠ 92 := by
  simp only [isIdentStart, isLetter, isNonAsciiIdent, isWhitespace, isNewline, isDigit, isNamed, isIdent,
    Bool.or_eq_true, beq_iff_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at h ⊢
  omega

/-! ## Comments -/

theorem consumeComments_cons_of_ne (c : Char) (rest : List Char) (h : c ≠ '/') :
    consumeComments (c :: rest) = c :: rest := by
  cases rest with
  | nil => rw [consumeComments]
  | cons d rest =>
    rw [consumeComments]
    simp only [h, false_and, if_false]

theorem consumeComments_solidus (rest : List Char) (h : rest[0]? ≠ some '*') :
    consumeComments ('/' :: rest) = '/' :: rest := by
  cases rest with
  | nil => rw [consumeComments]
  | cons d rest =>
    have hd : d ≠ '*' := fun e => h (by rw [e]; rfl)
    rw [consumeComments]
    simp only [hd, and_false, if_false]

/-- **A comment gives no token.** An empty comment before a text is consumed with it. -/
theorem consumeComments_comment (rest : List Char) :
    consumeComments ('/' :: '*' :: '*' :: '/' :: rest) = consumeComments rest := by
  rw [consumeComments]
  simp only [and_self, if_true]
  rfl

theorem consumeToken_comment (rest : List Char) (allowed : Bool) :
    consumeToken ('/' :: '*' :: '*' :: '/' :: rest) allowed = consumeToken rest allowed := by
  rw [consumeToken, consumeToken, consumeComments_comment]

/-- Two inputs with the same first token and the same rest have the same tokens. -/
theorem tokenize_congr {input input' : List Char}
    (h : consumeToken input = consumeToken input') : tokenize input = tokenize input' := by
  cases h' : consumeToken input' with
  | none => rw [tokenize_of_none (h.trans h'), tokenize_of_none h']
  | some p =>
    obtain ⟨token, rest⟩ := p
    rw [tokenize_of_some (h.trans h'), tokenize_of_some h']

/-- **A comment gives no token**, said of every token of a text. -/
theorem tokenize_comment (rest : List Char) :
    tokenize ('/' :: '*' :: '*' :: '/' :: rest) = tokenize rest :=
  tokenize_congr (consumeToken_comment rest false)

theorem tokenize_nil : tokenize [] = [] :=
  tokenize_of_none (by rw [consumeToken, consumeComments])

/-! ## The first code point -/

theorem consumeToken_whitespace (c : Char) (rest : List Char) (allowed : Bool)
    (h : isWhitespace c = true) :
    consumeToken (c :: rest) allowed = some (.whitespace, rest.dropWhile isWhitespace) := by
  have hs : c ≠ '/' := ne_of_toNat_ne (isWhitespace_facts h).2.2.2.2.1
  rw [consumeToken, consumeComments_cons_of_ne c rest hs]
  simp only [h, if_true]

/-- **A run of whitespace is one token.** A whitespace before a whitespace adds nothing. -/
theorem tokenize_whitespace_cons (c d : Char) (rest : List Char) (hc : isWhitespace c = true)
    (hd : isWhitespace d = true) : tokenize (c :: d :: rest) = tokenize (d :: rest) := by
  apply tokenize_congr
  rw [consumeToken_whitespace c _ false hc, consumeToken_whitespace d _ false hd]
  simp only [List.dropWhile_cons, hd, if_true]

/-- A code point that `consumeToken` does not name, and that is not whitespace or a solidus,
is a digit, a `U`, an ident-start code point or a delimiter. -/
theorem consumeToken_of_not_named (c : Char) (rest : List Char) (allowed : Bool)
    (hw : isWhitespace c = false) (hn : isNamed c = false) (hs : c ≠ '/') :
    consumeToken (c :: rest) allowed =
      if isDigit c = true then some (consumeNumericToken (c :: rest))
      else if c = 'U' ∨ c = 'u' then
        if allowed = true ∧ wouldStartUnicodeRange (some c) rest[0]? rest[1]? = true then
          some (consumeUnicodeRangeToken (c :: rest))
        else some (consumeIdentLikeToken (c :: rest))
      else if isIdentStart c = true then some (consumeIdentLikeToken (c :: rest))
      else some (.delim c, rest) := by
  have key : ∀ d : Char, isNamed d = true → c ≠ d := fun d hd e => by
    rw [e, hd] at hn
    cases hn
  rw [consumeToken, consumeComments_cons_of_ne c rest hs]
  simp only [hw, Bool.false_eq_true, if_false, key '"' (by decide), key '#' (by decide),
    key '\'' (by decide), key '(' (by decide), key ')' (by decide), key '+' (by decide),
    key ',' (by decide), key '-' (by decide), key '.' (by decide), key ':' (by decide),
    key ';' (by decide), key '<' (by decide), key '@' (by decide), key '[' (by decide),
    key '\\' (by decide), key ']' (by decide), key '{' (by decide), key '}' (by decide)]

theorem consumeToken_digit (c : Char) (rest : List Char) (allowed : Bool)
    (h : isDigit c = true) :
    consumeToken (c :: rest) allowed = some (consumeNumericToken (c :: rest)) := by
  obtain ⟨hw, -, hn, -, -, hs, -⟩ := isDigit_facts h
  rw [consumeToken_of_not_named c rest allowed hw hn (ne_of_toNat_ne hs)]
  simp only [h, if_true]

theorem consumeToken_identStart (c : Char) (rest : List Char) (h : isIdentStart c = true) :
    consumeToken (c :: rest) = some (consumeIdentLikeToken (c :: rest)) := by
  obtain ⟨hw, hd, hn, -, hs, -⟩ := isIdentStart_facts h
  rw [consumeToken_of_not_named c rest false hw hn (ne_of_toNat_ne hs)]
  simp only [hd, h, Bool.false_eq_true, if_false, false_and, if_true, ite_self]

end Whatwg.Css.Syntax
