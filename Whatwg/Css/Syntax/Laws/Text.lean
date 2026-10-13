import Whatwg.Css.Syntax.Laws.Token

/-!
# Whatwg.Css.Syntax.Laws.Text

Owner: the text of a token read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph
`CSS-PG-SYNTAX`).

- `Token.stops`: what the text after a token's text must be, so that the tokenizer ends the
  token where the writer ended it. For a delimiter it is the tokenizer's own check, negated: a
  number sign is not followed by a name, a plus sign does not start a number, and so on. It
  reads three code points at most.
- `tokenize_text`: **a token comes back.** The text of a writable token, before a text that
  stops it, tokenizes to the token and then the tokens of that text.

A delimiter that holds a reverse solidus and a bad string are written with a newline that the
tokenizer reads as whitespace; before whitespace it adds no token, and the law holds of them
as of the others.
-/

namespace Whatwg.Css.Syntax

namespace Token

/-- Whether a text after the token's text stops the token: the tokenizer, reading the two
together, gives the token and goes on at that text. -/
def stops : Token → List Char → Bool
  | .ident value, r =>
    nameStops r && !(r[0]? == some '(') && !(r[0]? == some '>' && value == ['-', '-'])
  | .function value, r => r[0]? == some '"' || !isUrlName value
  | .atKeyword _, r => nameStops r
  | .hash _ _, r => nameStops r
  | .dimension _ _ _, r => nameStops r && !(r[0]? == some '+' && r[1]?.any isDigit)
  | .number _ _, r =>
    !r[0]?.any isDigit && !(r[0]? == some '.' && r[1]?.any isDigit) &&
      !wouldStartIdentSequence r[0]? r[1]? r[2]? && !(r[0]? == some '%')
  | .delim c, r =>
    if c = '#' then nameStops r
    else if c = '+' then !wouldStartNumber (some '+') r[0]? r[1]?
    else if c = '-' then
      !wouldStartNumber (some '-') r[0]? r[1]? && !(r[0]? == some '-' && r[1]? == some '>') &&
        !wouldStartIdentSequence (some '-') r[0]? r[1]?
    else if c = '.' then !wouldStartNumber (some '.') r[0]? r[1]?
    else if c = '<' then !(r[0]? == some '!' && r[1]? == some '-' && r[2]? == some '-')
    else if c = '@' then !wouldStartIdentSequence r[0]? r[1]? r[2]?
    else if c = '\\' then r[0]?.any isWhitespace
    else if c = '/' then !(r[0]? == some '*')
    else true
  | .badString, r => r[0]?.any isWhitespace
  | .whitespace, r => !r[0]?.any isWhitespace
  | _, _ => true

end Token

theorem eq_false_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => cases h

theorem toNat_ne_of_ne {c d : Char} (h : c ≠ d) : c.toNat ≠ d.toNat := fun e => h (eq_of_toNat_eq e)

/-! ## Delimiters -/

theorem consumeToken_delim_numberSign (r : List Char) (hs : nameStops r = true) :
    consumeToken ('#' :: r) = some (.delim '#', r) := by
  obtain ⟨h₀, h₁⟩ := nameStops_facts hs
  rw [consumeToken_numberSign]
  simp only [h₀, h₁, Bool.false_eq_true, or_self, if_false]

theorem consumeToken_delim_plus (r : List Char)
    (hs : wouldStartNumber (some '+') r[0]? r[1]? = false) :
    consumeToken ('+' :: r) = some (.delim '+', r) := by
  rw [consumeToken_plus]
  simp only [hs, Bool.false_eq_true, if_false]

theorem consumeToken_delim_minus (r : List Char)
    (h₁ : wouldStartNumber (some '-') r[0]? r[1]? = false)
    (h₂ : ¬(r[0]? = some '-' ∧ r[1]? = some '>'))
    (h₃ : wouldStartIdentSequence (some '-') r[0]? r[1]? = false) :
    consumeToken ('-' :: r) = some (.delim '-', r) := by
  rw [consumeToken_minus]
  simp only [h₁, Bool.false_eq_true, if_false, h₂, h₃]

theorem consumeToken_delim_fullStop (r : List Char)
    (hs : wouldStartNumber (some '.') r[0]? r[1]? = false) :
    consumeToken ('.' :: r) = some (.delim '.', r) := by
  rw [consumeToken_fullStop]
  simp only [hs, Bool.false_eq_true, if_false]

theorem consumeToken_delim_lessThan (r : List Char)
    (hs : ¬(r[0]? = some '!' ∧ r[1]? = some '-' ∧ r[2]? = some '-')) :
    consumeToken ('<' :: r) = some (.delim '<', r) := by
  rw [consumeToken_lessThan]
  simp only [hs, if_false]

theorem consumeToken_delim_at (r : List Char)
    (hs : wouldStartIdentSequence r[0]? r[1]? r[2]? = false) :
    consumeToken ('@' :: r) = some (.delim '@', r) := by
  rw [consumeToken_at]
  simp only [hs, Bool.false_eq_true, if_false]

/-- A reverse solidus and a newline before whitespace: the delimiter, and the newline is part
of the whitespace that follows. -/
theorem tokenize_delim_reverseSolidus (r : List Char) (hs : r[0]?.any isWhitespace = true) :
    tokenize ('\\' :: '\n' :: r) = .delim '\\' :: tokenize r := by
  cases r with
  | nil => cases hs
  | cons w r =>
    have hw : isWhitespace w = true := hs
    have h : consumeToken ('\\' :: '\n' :: w :: r) = some (.delim '\\', '\n' :: w :: r) := by
      rw [consumeToken_reverseSolidus]
      rfl
    rw [tokenize_of_some h, tokenize_whitespace_cons '\n' w r (by decide) hw]

/-- A delimiter that `consumeToken` does not name. -/
theorem consumeToken_delim_other (c : Char) (r : List Char) (hd : isDelimiter c = true)
    (h₁ : c ≠ '#') (h₂ : c ≠ '+') (h₃ : c ≠ '-') (h₄ : c ≠ '.') (h₅ : c ≠ '<') (h₆ : c ≠ '@')
    (h₇ : c ≠ '\\') (h₈ : c ≠ '/') : consumeToken (c :: r) = some (.delim c, r) := by
  simp only [isDelimiter, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, d₁⟩, d₂⟩, d₃⟩, d₄⟩, d₅⟩, d₆⟩, d₇⟩, d₈⟩, d₉⟩, d₁₀⟩, d₁₁⟩, hdigit⟩, hstart⟩ := hd
  have hn : isNamed c = false := by
    have n₁ : c.toNat ≠ 35 := toNat_ne_of_ne h₁
    have n₂ : c.toNat ≠ 43 := toNat_ne_of_ne h₂
    have n₃ : c.toNat ≠ 45 := toNat_ne_of_ne h₃
    have n₄ : c.toNat ≠ 46 := toNat_ne_of_ne h₄
    have n₅ : c.toNat ≠ 60 := toNat_ne_of_ne h₅
    have n₆ : c.toNat ≠ 64 := toNat_ne_of_ne h₆
    have n₇ : c.toNat ≠ 92 := toNat_ne_of_ne h₇
    have m₁ : c.toNat ≠ 34 := toNat_ne_of_ne d₁
    have m₂ : c.toNat ≠ 39 := toNat_ne_of_ne d₂
    have m₃ : c.toNat ≠ 40 := toNat_ne_of_ne d₃
    have m₄ : c.toNat ≠ 41 := toNat_ne_of_ne d₄
    have m₅ : c.toNat ≠ 44 := toNat_ne_of_ne d₅
    have m₆ : c.toNat ≠ 58 := toNat_ne_of_ne d₆
    have m₇ : c.toNat ≠ 59 := toNat_ne_of_ne d₇
    have m₈ : c.toNat ≠ 91 := toNat_ne_of_ne d₈
    have m₉ : c.toNat ≠ 93 := toNat_ne_of_ne d₉
    have m₁₀ : c.toNat ≠ 123 := toNat_ne_of_ne d₁₀
    have m₁₁ : c.toNat ≠ 125 := toNat_ne_of_ne d₁₁
    simp only [isNamed, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    omega
  have hu : ¬(c = 'U' ∨ c = 'u') := by
    rintro (rfl | rfl) <;> exact absurd hstart (by decide)
  rw [consumeToken_of_not_named c r false hw hn h₈]
  simp only [hdigit, Bool.false_eq_true, if_false, hu, hstart]

/-! ## Bad strings and units -/

theorem consumeStringValue_newline (ending c : Char) (rest : List Char) (hc : isNewline c = true)
    (hne : c ≠ ending) : consumeStringValue ending (c :: rest) = (none, c :: rest) := by
  rw [consumeStringValue.eq_def]
  simp only [hne, if_false, hc, if_true]

/-- A quotation mark and a newline before whitespace: the bad string, and the newline is part
of the whitespace that follows. -/
theorem tokenize_badString (r : List Char) (hs : r[0]?.any isWhitespace = true) :
    tokenize ('"' :: '\n' :: r) = .badString :: tokenize r := by
  cases r with
  | nil => cases hs
  | cons w r =>
    have hw : isWhitespace w = true := hs
    have h : consumeToken ('"' :: '\n' :: w :: r) = some (.badString, '\n' :: w :: r) := by
      rw [consumeToken_quotationMark]
      simp only [consumeStringToken, consumeStringValue_newline '"' '\n' (w :: r) (by decide) (by decide)]
    rw [tokenize_of_some h, tokenize_whitespace_cons '\n' w r (by decide) hw]

theorem serializeUnit_of_isPlainIdentifier (unit : List Char) (hu : isPlainIdentifier unit = true)
    (hexp : readsAsExponent unit = false) : serializeUnit unit = unit := by
  cases unit with
  | nil => rfl
  | cons c rest =>
    rw [serializeUnit]
    simp only [hexp, Bool.false_eq_true, if_false]
    exact serializeIdentifier_of_isPlainIdentifier _ hu

/-! ## A token comes back -/

/-- **A token comes back.** The text of a writable token, before a text that stops it,
tokenizes to the token and then the tokens of that text. -/
theorem tokenize_text (a : Token) (r : List Char) (ha : a.writable = true)
    (hs : a.stops r = true) : tokenize (a.text ++ r) = a :: tokenize r := by
  cases a with
  | ident value =>
    simp only [Token.stops, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_imp, beq_iff_eq] at hs
    obtain ⟨⟨hr, hp⟩, hc⟩ := hs
    exact tokenize_of_some (consumeToken_identText value r ha hr hp (fun e h => hc h e))
  | function value =>
    have hu : isUrlName value = true → r[0]? = some '"' := by
      intro h
      simp only [Token.stops, h, Bool.not_true, Bool.or_false, beq_iff_eq] at hs
      exact hs
    refine tokenize_of_some ?_
    rw [Token.text, List.append_assoc]
    exact consumeToken_functionText value r ha hu
  | atKeyword value =>
    exact tokenize_of_some (consumeToken_atKeywordText value r ha hs)
  | hash value flag =>
    cases flag with
    | id =>
      exact tokenize_of_some (consumeToken_hashIdText value r ha hs)
    | unrestricted =>
      have hall : value.all isIdent = true := by
        simp only [Token.writable, isPlainRestrictedName, Bool.and_eq_true] at ha
        exact ha.1.2
      refine tokenize_of_some ?_
      rw [Token.text, serializeName_of_all_isIdent value hall]
      exact consumeToken_hashRestrictedText value r ha hs
  | string value =>
    refine tokenize_of_some ?_
    rw [Token.text, List.cons_append, List.append_assoc]
    exact consumeToken_stringText value r ha
  | badString => exact tokenize_badString r hs
  | url value => cases ha
  | badUrl => cases ha
  | delim c =>
    by_cases h₁ : c = '#'
    · subst h₁
      exact tokenize_of_some (consumeToken_delim_numberSign r hs)
    by_cases h₂ : c = '+'
    · subst h₂
      exact tokenize_of_some (consumeToken_delim_plus r (eq_false_of_not hs))
    by_cases h₃ : c = '-'
    · subst h₃
      have hs' : (!wouldStartNumber (some '-') r[0]? r[1]? && !(r[0]? == some '-' && r[1]? == some '>') &&
          !wouldStartIdentSequence (some '-') r[0]? r[1]?) = true := hs
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq,
        beq_eq_false_iff_ne, ne_eq] at hs'
      obtain ⟨⟨k₁, k₂⟩, k₃⟩ := hs'
      exact tokenize_of_some (consumeToken_delim_minus r k₁ (fun h => k₂ h.1 h.2) k₃)
    by_cases h₄ : c = '.'
    · subst h₄
      exact tokenize_of_some (consumeToken_delim_fullStop r (eq_false_of_not hs))
    by_cases h₅ : c = '<'
    · subst h₅
      have hs' : (!(r[0]? == some '!' && r[1]? == some '-' && r[2]? == some '-')) = true := hs
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, beq_iff_eq,
        beq_eq_false_iff_ne, ne_eq, and_imp] at hs'
      exact tokenize_of_some (consumeToken_delim_lessThan r (fun h => hs' h.1 h.2.1 h.2.2))
    by_cases h₆ : c = '@'
    · subst h₆
      exact tokenize_of_some (consumeToken_delim_at r (eq_false_of_not hs))
    by_cases h₇ : c = '\\'
    · subst h₇
      exact tokenize_delim_reverseSolidus r hs
    by_cases h₈ : c = '/'
    · subst h₈
      have hs' : (!(r[0]? == some '*')) = true := hs
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hs'
      exact tokenize_of_some (consumeToken_solidus r false hs')
    · refine tokenize_of_some ?_
      rw [Token.text, if_neg h₇]
      exact consumeToken_delim_other c r ha h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  | number n flag =>
    simp only [Token.stops, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq,
      beq_eq_false_iff_ne, ne_eq] at hs
    obtain ⟨⟨⟨k₁, k₂⟩, k₃⟩, k₄⟩ := hs
    refine tokenize_of_some ?_
    exact consumeToken_number n flag r ha k₁ (fun h => by rw [k₂ h.1] at h; exact absurd h.2 (by decide))
      k₃ k₄
  | percentage n =>
    refine tokenize_of_some ?_
    rw [Token.text, List.append_assoc]
    exact consumeToken_percentage n r ha
  | dimension n flag unit =>
    simp only [Token.writable, Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨hn, hu⟩, hexp⟩ := ha
    simp only [Token.stops, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq] at hs
    obtain ⟨hr, hp⟩ := hs
    refine tokenize_of_some ?_
    rw [Token.text, serializeUnit_of_isPlainIdentifier unit hu hexp, List.append_assoc]
    exact consumeToken_dimension n flag unit r hn hu hexp hr
      (fun h => by rw [hp h.1] at h; exact absurd h.2 (by decide))
  | unicodeRange start stop => cases ha
  | whitespace => exact tokenize_of_some (consumeToken_space r (eq_false_of_not hs))
  | cdo => exact tokenize_of_some (consumeToken_cdo r false)
  | cdc => exact tokenize_of_some (consumeToken_cdc r false)
  | colon => exact tokenize_of_some (consumeToken_colon r false)
  | semicolon => exact tokenize_of_some (consumeToken_semicolon r false)
  | comma => exact tokenize_of_some (consumeToken_comma r false)
  | openSquare => exact tokenize_of_some (consumeToken_openSquare r false)
  | closeSquare => exact tokenize_of_some (consumeToken_closeSquare r false)
  | openParen => exact tokenize_of_some (consumeToken_openParen r false)
  | closeParen => exact tokenize_of_some (consumeToken_closeParen r false)
  | openCurly => exact tokenize_of_some (consumeToken_openCurly r false)
  | closeCurly => exact tokenize_of_some (consumeToken_closeCurly r false)

end Whatwg.Css.Syntax
