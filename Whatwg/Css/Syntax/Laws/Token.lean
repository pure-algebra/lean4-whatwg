import Whatwg.Css.Syntax.Laws.Escape

/-!
# Whatwg.Css.Syntax.Laws.Token

Owner: one token read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph
`CSS-PG-SYNTAX`).

- `Token.stops`: what the text after a token's text must be, so that the tokenizer ends the
  token where the writer ended it. For a delimiter it is the tokenizer's own check, negated.
- `tokenize_text`: **a token comes back.** The text of a writable token, before a text that
  stops it, tokenizes to the token and then the tokens of that text.

One law for each kind of token is behind it (`consumeToken_identText` and the rest).
-/

namespace Whatwg.Css.Syntax

/-! ## The named code points, one law each (continued) -/

theorem consumeToken_plus (rest : List Char) (allowed : Bool) :
    consumeToken ('+' :: rest) allowed =
      if wouldStartNumber (some '+') rest[0]? rest[1]? = true then
        some (consumeNumericToken ('+' :: rest))
      else some (.delim '+', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '+' rest (by decide)]
  rfl

theorem consumeToken_fullStop (rest : List Char) (allowed : Bool) :
    consumeToken ('.' :: rest) allowed =
      if wouldStartNumber (some '.') rest[0]? rest[1]? = true then
        some (consumeNumericToken ('.' :: rest))
      else some (.delim '.', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '.' rest (by decide)]
  rfl

theorem consumeToken_lessThan (rest : List Char) (allowed : Bool) :
    consumeToken ('<' :: rest) allowed =
      if rest[0]? = some '!' ∧ rest[1]? = some '-' ∧ rest[2]? = some '-' then
        some (.cdo, rest.drop 3)
      else some (.delim '<', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '<' rest (by decide)]
  rfl

theorem consumeToken_solidus (rest : List Char) (allowed : Bool) (h : rest[0]? ≠ some '*') :
    consumeToken ('/' :: rest) allowed = some (.delim '/', rest) := by
  rw [consumeToken, consumeComments_solidus rest h]
  rfl

theorem consumeToken_colon (rest : List Char) (allowed : Bool) :
    consumeToken (':' :: rest) allowed = some (.colon, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne ':' rest (by decide)]
  rfl

theorem consumeToken_semicolon (rest : List Char) (allowed : Bool) :
    consumeToken (';' :: rest) allowed = some (.semicolon, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne ';' rest (by decide)]
  rfl

theorem consumeToken_comma (rest : List Char) (allowed : Bool) :
    consumeToken (',' :: rest) allowed = some (.comma, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne ',' rest (by decide)]
  rfl

theorem consumeToken_openSquare (rest : List Char) (allowed : Bool) :
    consumeToken ('[' :: rest) allowed = some (.openSquare, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '[' rest (by decide)]
  rfl

theorem consumeToken_closeSquare (rest : List Char) (allowed : Bool) :
    consumeToken (']' :: rest) allowed = some (.closeSquare, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne ']' rest (by decide)]
  rfl

theorem consumeToken_openParen (rest : List Char) (allowed : Bool) :
    consumeToken ('(' :: rest) allowed = some (.openParen, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '(' rest (by decide)]
  rfl

theorem consumeToken_closeParen (rest : List Char) (allowed : Bool) :
    consumeToken (')' :: rest) allowed = some (.closeParen, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne ')' rest (by decide)]
  rfl

theorem consumeToken_openCurly (rest : List Char) (allowed : Bool) :
    consumeToken ('{' :: rest) allowed = some (.openCurly, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '{' rest (by decide)]
  rfl

theorem consumeToken_closeCurly (rest : List Char) (allowed : Bool) :
    consumeToken ('}' :: rest) allowed = some (.closeCurly, rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '}' rest (by decide)]
  rfl

theorem consumeToken_cdo (rest : List Char) (allowed : Bool) :
    consumeToken ('<' :: '!' :: '-' :: '-' :: rest) allowed = some (.cdo, rest) := by
  rw [consumeToken_lessThan]
  rfl

theorem consumeToken_cdc (rest : List Char) (allowed : Bool) :
    consumeToken ('-' :: '-' :: '>' :: rest) allowed = some (.cdc, rest) := by
  rw [consumeToken_minus]
  rfl

/-! ## Names -/

theorem isPlainIdentifier_all {name : List Char} (h : isPlainIdentifier name = true) :
    name.all isIdent = true := by
  simp only [isPlainIdentifier, Bool.and_eq_true] at h
  exact h.1

theorem isNameValue_facts {name : List Char} (h : isNameValue name = true) :
    name ≠ [] ∧ (name.all fun c => c.toNat != 0) = true := by
  simp only [isNameValue, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun e => ?_, h.2⟩
  rw [e] at h
  exact absurd h.1 (by decide)

theorem consumeIdentLikeToken_ident (name rest : List Char) (hn : isNameValue name = true)
    (hr : nameStops rest = true) (hp : rest[0]? ≠ some '(') :
    consumeIdentLikeToken (serializeIdentifier name ++ rest) = (.ident name, rest) := by
  simp only [consumeIdentLikeToken,
    consumeIdentSequence_serializeIdentifier name rest (isNameValue_facts hn).2 hr, hp, if_false]

/-- **An identifier comes back.** -/
theorem consumeToken_identText (name rest : List Char) (hn : isNameValue name = true)
    (hr : nameStops rest = true) (hp : rest[0]? ≠ some '(')
    (hc : name = ['-', '-'] → rest[0]? ≠ some '>') :
    consumeToken (serializeIdentifier name ++ rest) = some (.ident name, rest) := by
  obtain ⟨hne, hall⟩ := isNameValue_facts hn
  rw [consumeToken_of_wouldStart _ (wouldStart_serializeIdentifier name rest hne hall)
    (not_cdc_serializeIdentifier name rest hne hall hc), consumeIdentLikeToken_ident name rest hn hr hp]

theorem consumeUrlLeadingWhitespace_quotationMark (rest : List Char) :
    consumeUrlLeadingWhitespace ('"' :: rest) = '"' :: rest := by
  cases rest with
  | nil => rfl
  | cons d rest =>
    rw [consumeUrlLeadingWhitespace]
    simp only [show isWhitespace '"' = false from rfl, Bool.false_eq_true, false_and, if_false]

/-- **A function token comes back.** One named `url` is followed by a quotation mark. -/
theorem consumeToken_functionText (name rest : List Char) (hn : isNameValue name = true)
    (hu : isUrlName name = true → rest[0]? = some '"') :
    consumeToken (serializeIdentifier name ++ '(' :: rest) = some (.function name, rest) := by
  obtain ⟨hne, hall⟩ := isNameValue_facts hn
  have hstop : nameStops ('(' :: rest) = true := rfl
  have hcdc : name = ['-', '-'] → ('(' :: rest)[0]? ≠ some '>' :=
    fun _ e => absurd (Option.some.inj e) (by decide)
  have hseq := consumeIdentSequence_serializeIdentifier name ('(' :: rest) hall hstop
  rw [consumeToken_of_wouldStart _ (wouldStart_serializeIdentifier name _ hne hall)
    (not_cdc_serializeIdentifier name _ hne hall hcdc)]
  by_cases hurl : isUrlName name = true
  · have h₀ := hu hurl
    cases rest with
    | nil => cases h₀
    | cons q rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h₀
      subst h₀
      simp only [consumeIdentLikeToken, hseq, List.getElem?_cons_zero, if_true, hurl, List.drop_succ_cons,
        List.drop_zero, consumeUrlLeadingWhitespace_quotationMark, true_or]
  · simp only [consumeIdentLikeToken, hseq, List.getElem?_cons_zero, if_true, hurl, Bool.false_eq_true,
      if_false, List.drop_succ_cons, List.drop_zero]

/-- **An at-keyword comes back.** -/
theorem consumeToken_atKeywordText (name rest : List Char) (hn : isNameValue name = true)
    (hr : nameStops rest = true) :
    consumeToken ('@' :: (serializeIdentifier name ++ rest)) = some (.atKeyword name, rest) := by
  obtain ⟨hne, hall⟩ := isNameValue_facts hn
  rw [consumeToken_at]
  simp only [wouldStart_serializeIdentifier name rest hne hall, if_true,
    consumeIdentSequence_serializeIdentifier name rest hall hr]

/-- **A hash token of type "id" comes back.** -/
theorem consumeToken_hashIdText (name rest : List Char) (hn : isNameValue name = true)
    (hr : nameStops rest = true) :
    consumeToken ('#' :: (serializeIdentifier name ++ rest)) = some (.hash name .id, rest) := by
  obtain ⟨hne, hall⟩ := isNameValue_facts hn
  have hw := wouldStart_serializeIdentifier name rest hne hall
  rw [consumeToken_numberSign]
  simp only [isIdent_or_escape_of_wouldStart hw, if_true, hw,
    consumeIdentSequence_serializeIdentifier name rest hall hr]

theorem nameStops_facts {rest : List Char} (h : nameStops rest = true) :
    rest[0]?.any isIdent = false ∧ areValidEscape rest[0]? rest[1]? = false := by
  simp only [nameStops, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

/-- A name that does not start as an identifier does, before a text that does not go on it,
would not start an ident sequence. -/
theorem wouldStart_of_isPlainRestrictedName (name rest : List Char)
    (hn : isPlainRestrictedName name = true) (hr : nameStops rest = true) :
    wouldStartIdentSequence (name ++ rest)[0]? (name ++ rest)[1]? (name ++ rest)[2]? = false := by
  simp only [isPlainRestrictedName, Bool.and_eq_true, Bool.not_eq_true'] at hn
  obtain ⟨⟨-, hall⟩, hstart⟩ := hn
  obtain ⟨hr₀, hr₁⟩ := nameStops_facts hr
  rw [Bool.eq_false_iff]
  intro hw
  cases name with
  | nil =>
    rw [List.nil_append] at hw
    rcases isIdent_or_escape_of_wouldStart hw with h | h
    · rw [hr₀] at h
      cases h
    · rw [hr₁] at h
      cases h
  | cons c tail =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [startsIdent, List.getElem?_cons_zero, List.getElem?_cons_succ] at hstart
    simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ] at hw
    rcases wouldStartIdentSequence_cases hw with ⟨hc, h₂⟩ | hc | ⟨hc, -⟩
    · obtain rfl := Option.some.inj hc
      cases tail with
      | nil =>
        rw [List.nil_append] at h₂
        have hident : rest[0]?.any isIdent = true := by
          rcases h₂ with h₂ | h₂ | h₂
          · cases hrest : rest[0]? with
            | none => rw [hrest] at h₂; cases h₂
            | some x =>
              rw [hrest] at h₂
              exact (isIdentStart_facts h₂).2.2.2.1
          · rw [h₂]
            rfl
          · rw [hr₁] at h₂
            cases h₂
        rw [hr₀] at hident
        cases hident
      | cons d tail' =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.any_some,
          Option.some.injEq] at h₂
        have : wouldStartIdentSequence (some '-') (some d) tail'[0]? = true := by
          rcases h₂ with h₂ | h₂ | h₂
          · simp only [wouldStartIdentSequence, if_true, Option.any_some, h₂, Bool.true_or]
          · subst h₂
            rfl
          · have hd := Option.some.inj (areValidEscape_first h₂)
            subst hd
            exact absurd hall.2.1 (by decide)
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hstart
        rw [hstart] at this
        cases this
    · rw [wouldStartIdentSequence_of_isIdentStart c _ _ hc] at hstart
      cases hstart
    · obtain rfl := Option.some.inj hc
      exact absurd hall.1 (by decide)

/-- **A hash token of type "unrestricted" comes back.** -/
theorem consumeToken_hashRestrictedText (name rest : List Char)
    (hn : isPlainRestrictedName name = true) (hr : nameStops rest = true) :
    consumeToken ('#' :: (name ++ rest)) = some (.hash name .unrestricted, rest) := by
  have hw := wouldStart_of_isPlainRestrictedName name rest hn hr
  simp only [isPlainRestrictedName, Bool.and_eq_true, Bool.not_eq_true'] at hn
  obtain ⟨⟨hne, hall⟩, -⟩ := hn
  have hfirst : (name ++ rest)[0]?.any isIdent = true := by
    cases name with
    | nil => cases hne
    | cons c tail =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp only [List.cons_append, List.getElem?_cons_zero, Option.any_some, hall.1]
  rw [consumeToken_numberSign]
  simp only [hfirst, true_or, if_true, hw, Bool.false_eq_true, if_false,
    consumeIdentSequence_append name rest hall hr]

/-! ## Strings -/

/-- **A string token comes back.** -/
theorem consumeToken_stringText (value rest : List Char)
    (hv : (value.all fun c => c.toNat != 0) = true) :
    consumeToken ('"' :: (serializeStringValue value ++ '"' :: rest)) = some (.string value, rest) := by
  rw [consumeToken_quotationMark]
  simp only [consumeStringToken, consumeStringValue_text value rest hv]

/-! ## Numbers -/

theorem wouldStartNumber_sign_digit (s d : Char) (c₃ : Option Char) (hs : s = '+' ∨ s = '-')
    (hd : isDigit d = true) : wouldStartNumber (some s) (some d) c₃ = true := by
  simp only [wouldStartNumber, Option.some.injEq, hs, if_true, Option.any_some, hd, Bool.true_or]

/-- The text of a number starts with its sign character and a digit. -/
theorem Numeric.text_cons (n : Numeric) (flag : NumberFlag) :
    ∃ d tail, n.text flag = signText n.sign ++ d :: tail ∧ isDigit d = true := by
  obtain ⟨d, digits, hdigits, hd, -⟩ := toDigits_cons
    (n.value.num.natAbs * (10 ^ n.places flag / n.value.den) / 10 ^ n.places flag)
  exact ⟨d, _, by simp only [Numeric.text, hdigits, List.cons_append]; rfl, hd⟩

/-- The text of a number starts a numeric token. -/
theorem consumeToken_numberText (n : Numeric) (flag : NumberFlag) (tail : List Char) :
    consumeToken (n.text flag ++ tail) = some (consumeNumericToken (n.text flag ++ tail)) := by
  obtain ⟨d, rest, htext, hd⟩ := n.text_cons flag
  rw [htext]
  cases n.sign with
  | none => exact consumeToken_digit d _ false hd
  | some s =>
    cases s with
    | plus =>
      simp only [signText, List.cons_append, List.nil_append]
      rw [consumeToken_plus]
      simp only [List.getElem?_cons_zero, wouldStartNumber_sign_digit '+' d _ (Or.inl rfl) hd, if_true]
    | minus =>
      simp only [signText, List.cons_append, List.nil_append]
      rw [consumeToken_minus]
      simp only [List.getElem?_cons_zero, wouldStartNumber_sign_digit '-' d _ (Or.inr rfl) hd, if_true]

/-- **A number token comes back.** -/
theorem consumeToken_number (n : Numeric) (flag : NumberFlag) (rest : List Char)
    (hn : n.writable flag = true) (h₁ : rest[0]?.any isDigit = false)
    (h₂ : ¬(rest[0]? = some '.' ∧ rest[1]?.any isDigit = true))
    (h₃ : wouldStartIdentSequence rest[0]? rest[1]? rest[2]? = false) (h₄ : rest[0]? ≠ some '%') :
    consumeToken (n.text flag ++ rest) = some (.number n flag, rest) := by
  have hE : rest[0]? ≠ some 'E' := fun e => by
    have := wouldStartIdentSequence_of_isIdentStart 'E' rest[1]? rest[2]? (by decide)
    rw [← e, h₃] at this
    cases this
  have he : rest[0]? ≠ some 'e' := fun e => by
    have := wouldStartIdentSequence_of_isIdentStart 'e' rest[1]? rest[2]? (by decide)
    rw [← e, h₃] at this
    cases this
  rw [consumeToken_numberText]
  simp only [consumeNumericToken, consumeNumber_text n flag rest hn h₁ h₂ (consumeExponent_none rest ⟨hE, he⟩),
    h₃, Bool.false_eq_true, if_false, h₄]

/-- **A percentage token comes back.** -/
theorem consumeToken_percentage (n : Numeric) (rest : List Char)
    (hn : n.writable n.percentageFlag = true) :
    consumeToken (n.text n.percentageFlag ++ '%' :: rest) = some (.percentage n, rest) := by
  have he : consumeExponent ('%' :: rest) = (none, '%' :: rest) :=
    consumeExponent_none _ ⟨fun e => absurd (Option.some.inj e) (by decide),
      fun e => absurd (Option.some.inj e) (by decide)⟩
  have h₂ : ¬(('%' :: rest)[0]? = some '.' ∧ ('%' :: rest)[1]?.any isDigit = true) :=
    fun h => absurd (Option.some.inj h.1) (by decide)
  have hw : wouldStartIdentSequence (some '%') rest[0]? rest[1]? = false := rfl
  rw [consumeToken_numberText]
  simp only [consumeNumericToken, consumeNumber_text n _ ('%' :: rest) hn rfl h₂ he, List.getElem?_cons_zero,
    List.getElem?_cons_succ, hw, Bool.false_eq_true, if_false, if_true, List.drop_succ_cons, List.drop_zero]

/-- A unit that would not be read as an exponent starts no exponent, before a text that does
not go on it and does not start with a plus sign and a digit. -/
theorem consumeExponent_unit (unit rest : List Char) (hall : unit.all isIdent = true)
    (hexp : readsAsExponent unit = false) (hr : nameStops rest = true)
    (hp : ¬(rest[0]? = some '+' ∧ rest[1]?.any isDigit = true)) :
    consumeExponent (unit ++ rest) = (none, unit ++ rest) := by
  obtain ⟨hr₀, -⟩ := nameStops_facts hr
  have hrd : rest[0]?.any isDigit = false := by
    cases hrest : rest[0]? with
    | none => rfl
    | some x =>
      rw [hrest] at hr₀
      simp only [Option.any_some] at hr₀ ⊢
      cases hx : isDigit x with
      | false => rfl
      | true =>
        rw [(isDigit_facts hx).2.2.2.1] at hr₀
        cases hr₀
  have hrm : rest[0]? ≠ some '-' := fun e => by
    rw [e] at hr₀
    cases hr₀
  by_cases he : (unit ++ rest)[0]? = some 'E' ∨ (unit ++ rest)[0]? = some 'e'
  · cases unit with
    | nil =>
      rw [List.nil_append] at he
      rcases he with he | he <;> rw [he] at hr₀ <;> cases hr₀
    | cons c tail =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hc : c = 'E' ∨ c = 'e' := by
        simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at he
        exact he
      have hce : (some c == some 'e' || some c == some 'E') = true := by
        rcases hc with rfl | rfl <;> rfl
      simp only [readsAsExponent, List.getElem?_cons_zero, List.getElem?_cons_succ, hce, Bool.true_and,
        Bool.or_eq_false_iff, Bool.and_eq_false_imp, beq_iff_eq] at hexp
      obtain ⟨hx₁, hx₂⟩ := hexp
      cases tail with
      | nil =>
        have hA : ¬(rest[0]?.any isDigit = true) := by
          rw [hrd]
          exact Bool.false_ne_true
        have hB : ¬((rest[0]? = some '-' ∨ rest[0]? = some '+') ∧ rest[1]?.any isDigit = true) := by
          rintro ⟨h | h, hd⟩
          · exact hrm h
          · exact hp ⟨h, hd⟩
        simp only [consumeExponent, List.cons_append, List.nil_append, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.some.injEq, hc, if_true, hA, Bool.false_eq_true, if_false, hB]
      | cons x tail' =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.any_some, Option.some.injEq]
          at hx₁ hx₂
        have hxp : x ≠ '+' := by
          rintro rfl
          exact absurd hall.2.1 (by decide)
        have hB : ¬((x = '-' ∨ x = '+') ∧ (tail' ++ rest)[0]?.any isDigit = true) := by
          rintro ⟨h | h, hd⟩
          · cases tail' with
            | nil =>
              rw [List.nil_append, hrd] at hd
              cases hd
            | cons y tail'' =>
              rw [List.cons_append, List.getElem?_cons_zero] at hd
              have := hx₂ h
              rw [List.getElem?_cons_zero] at this
              rw [this] at hd
              cases hd
          · exact hxp h
        simp only [consumeExponent, List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq, hc, if_true, Option.any_some, hx₁, Bool.false_eq_true, if_false, hB]
  · exact consumeExponent_none _ ⟨fun e => he (Or.inl e), fun e => he (Or.inr e)⟩

/-- **A dimension token comes back.** -/
theorem consumeToken_dimension (n : Numeric) (flag : NumberFlag) (unit rest : List Char)
    (hn : n.writable flag = true) (hu : isPlainIdentifier unit = true)
    (hexp : readsAsExponent unit = false) (hr : nameStops rest = true)
    (hp : ¬(rest[0]? = some '+' ∧ rest[1]?.any isDigit = true)) :
    consumeToken (n.text flag ++ (unit ++ rest)) = some (.dimension n flag unit, rest) := by
  have hall := isPlainIdentifier_all hu
  have hw := wouldStart_of_isPlainIdentifier unit rest hu
  have hfirst : (unit ++ rest)[0]?.any isDigit = false ∧ (unit ++ rest)[0]? ≠ some '.' := by
    obtain ⟨c, tail, rfl, -, hc | ⟨rfl, -⟩⟩ := isPlainIdentifier_shape hu
    · refine ⟨?_, ?_⟩
      · simp only [List.cons_append, List.getElem?_cons_zero, Option.any_some, (isIdentStart_facts hc).2.1]
      · intro e
        simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at e
        subst e
        exact absurd hc (by decide)
    · exact ⟨rfl, fun e => absurd (Option.some.inj e) (by decide)⟩
  have h₂ : ¬((unit ++ rest)[0]? = some '.' ∧ (unit ++ rest)[1]?.any isDigit = true) :=
    fun h => hfirst.2 h.1
  rw [consumeToken_numberText]
  simp only [consumeNumericToken,
    consumeNumber_text n flag (unit ++ rest) hn hfirst.1 h₂ (consumeExponent_unit unit rest hall hexp hr hp),
    hw, if_true, consumeIdentSequence_append unit rest hall hr]

/-! ## Whitespace -/

theorem consumeToken_space (rest : List Char) (h : rest[0]?.any isWhitespace = false) :
    consumeToken (' ' :: rest) = some (.whitespace, rest) := by
  have hdrop : rest.dropWhile isWhitespace = rest := by
    cases rest with
    | nil => rfl
    | cons c rest =>
      simp only [List.getElem?_cons_zero, Option.any_some] at h
      simp only [List.dropWhile_cons, h, Bool.false_eq_true, if_false]
  rw [consumeToken_whitespace ' ' rest false (by decide), hdrop]

end Whatwg.Css.Syntax
