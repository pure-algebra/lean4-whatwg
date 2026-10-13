import Whatwg.Css.Syntax.Laws.Dispatch

/-!
# Whatwg.Css.Syntax.Laws.Name

Owner: names read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

A name is the value of an identifier, of a function, of an at-keyword, of a hash token, and
the unit of a dimension. The laws here say that a name written with no escape is consumed
whole by `consumeIdentSequence`, and that the tokenizer's checks on the code points before it
answer as the writer needs.

- `nameStops`: what may follow a name, so that the name ends where the writer ended it.
- `consumeIdentSequence_append`: the name comes back.
- `consumeToken_of_wouldStart`: where the next three code points would start an ident sequence
  and are not `-->`, the token is an ident-like token. This one is about the tokenizer alone.
-/

namespace Whatwg.Css.Syntax

theorem isIdent_facts {c : Char} (h : isIdent c = true) :
    c.toNat ≠ 0 ∧ isControl c = false ∧ isWhitespace c = false ∧ c.toNat ≠ 92 ∧ c.toNat ≠ 47 ∧
      c.toNat ≠ 40 ∧ c.toNat ≠ 62 ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 37 ∧ c.toNat ≠ 10 ∧ c.toNat ≠ 42 ∧
      c.toNat ≠ 33 := by
  simp only [isIdentStart, isLetter, isNonAsciiIdent, isWhitespace, isNewline, isDigit, isIdent, isControl,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at h ⊢
  omega

/-! ## The named code points, one law each -/

theorem consumeToken_minus (rest : List Char) (allowed : Bool) :
    consumeToken ('-' :: rest) allowed =
      if wouldStartNumber (some '-') rest[0]? rest[1]? = true then
        some (consumeNumericToken ('-' :: rest))
      else if rest[0]? = some '-' ∧ rest[1]? = some '>' then some (.cdc, rest.drop 2)
      else if wouldStartIdentSequence (some '-') rest[0]? rest[1]? = true then
        some (consumeIdentLikeToken ('-' :: rest))
      else some (.delim '-', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '-' rest (by decide)]
  rfl

theorem consumeToken_reverseSolidus (rest : List Char) (allowed : Bool) :
    consumeToken ('\\' :: rest) allowed =
      if areValidEscape (some '\\') rest[0]? = true then some (consumeIdentLikeToken ('\\' :: rest))
      else some (.delim '\\', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '\\' rest (by decide)]
  rfl

theorem consumeToken_at (rest : List Char) (allowed : Bool) :
    consumeToken ('@' :: rest) allowed =
      if wouldStartIdentSequence rest[0]? rest[1]? rest[2]? = true then
        some (.atKeyword (consumeIdentSequence rest).1, (consumeIdentSequence rest).2)
      else some (.delim '@', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '@' rest (by decide)]
  rfl

theorem consumeToken_numberSign (rest : List Char) (allowed : Bool) :
    consumeToken ('#' :: rest) allowed =
      if rest[0]?.any isIdent = true ∨ areValidEscape rest[0]? rest[1]? = true then
        some (.hash (consumeIdentSequence rest).1
          (if wouldStartIdentSequence rest[0]? rest[1]? rest[2]? = true then .id else .unrestricted),
          (consumeIdentSequence rest).2)
      else some (.delim '#', rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '#' rest (by decide)]
  rfl

/-! ## The checks -/

theorem wouldStartIdentSequence_none (c₂ c₃ : Option Char) :
    wouldStartIdentSequence none c₂ c₃ = false := rfl

theorem wouldStartIdentSequence_of_isIdentStart (c : Char) (c₂ c₃ : Option Char)
    (h : isIdentStart c = true) : wouldStartIdentSequence (some c) c₂ c₃ = true := by
  have hne : c ≠ '-' := by rintro rfl; exact absurd h (by decide)
  simp only [wouldStartIdentSequence, Option.some.injEq, hne, if_false, Option.any_some, h, if_true]

/-- What the check says of the three code points it is true of. -/
theorem wouldStartIdentSequence_cases {c₁ c₂ c₃ : Option Char}
    (h : wouldStartIdentSequence c₁ c₂ c₃ = true) :
    (c₁ = some '-' ∧
        (c₂.any isIdentStart = true ∨ c₂ = some '-' ∨ areValidEscape c₂ c₃ = true)) ∨
      c₁.any isIdentStart = true ∨ (c₁ = some '\\' ∧ areValidEscape c₁ c₂ = true) := by
  unfold wouldStartIdentSequence at h
  grind

theorem areValidEscape_first {c₁ c₂ : Option Char} (h : areValidEscape c₁ c₂ = true) :
    c₁ = some '\\' := by
  unfold areValidEscape at h
  grind

/-- Where three code points would start an ident sequence, the first is an ident code point or
the first two are a valid escape: a number sign before them starts a hash token. -/
theorem isIdent_or_escape_of_wouldStart {c₁ c₂ c₃ : Option Char}
    (h : wouldStartIdentSequence c₁ c₂ c₃ = true) :
    c₁.any isIdent = true ∨ areValidEscape c₁ c₂ = true := by
  rcases wouldStartIdentSequence_cases h with ⟨rfl, -⟩ | h | ⟨-, h⟩
  · exact Or.inl (by decide)
  · left
    cases c₁ with
    | none => cases h
    | some c => exact (isIdentStart_facts h).2.2.2.1
  · exact Or.inr h

/-- After a hyphen-minus, code points that would go on an ident sequence do not start a
number. -/
theorem wouldStartNumber_minus_of_wouldStart {c₂ c₃ : Option Char}
    (h : wouldStartIdentSequence (some '-') c₂ c₃ = true) :
    wouldStartNumber (some '-') c₂ c₃ = false := by
  have key : ∀ x : Char, isIdentStart x = true ∨ x = '-' ∨ x = '\\' →
      isDigit x = false ∧ x ≠ '.' := by
    rintro x (hx | rfl | rfl)
    · exact ⟨(isIdentStart_facts hx).2.1, by rintro rfl; exact absurd hx (by decide)⟩
    · exact ⟨by decide, by decide⟩
    · exact ⟨by decide, by decide⟩
  rcases wouldStartIdentSequence_cases h with ⟨-, h⟩ | h | ⟨h, -⟩
  · cases c₂ with
    | none => rfl
    | some x =>
      have hx : isIdentStart x = true ∨ x = '-' ∨ x = '\\' := by
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (Option.some.inj h))
        · exact Or.inr (Or.inr (Option.some.inj (areValidEscape_first h)))
      obtain ⟨hd, hdot⟩ := key x hx
      simp only [wouldStartNumber, Option.some.injEq, Char.reduceEq, or_true, if_true, Option.any_some, hd,
        Bool.false_or, Bool.and_eq_false_imp, beq_iff_eq]
      intro e
      exact absurd e hdot
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **Where the next three code points would start an ident sequence and are not `-->`, the
token is an ident-like token.** -/
theorem consumeToken_of_wouldStart (input : List Char)
    (h : wouldStartIdentSequence input[0]? input[1]? input[2]? = true)
    (hcdc : ¬(input[0]? = some '-' ∧ input[1]? = some '-' ∧ input[2]? = some '>')) :
    consumeToken input = some (consumeIdentLikeToken input) := by
  cases input with
  | nil => cases h
  | cons c rest =>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at h hcdc
    rcases wouldStartIdentSequence_cases h with ⟨hc, -⟩ | hc | ⟨hc, hv⟩
    · obtain rfl := Option.some.inj hc
      rw [consumeToken_minus, wouldStartNumber_minus_of_wouldStart h]
      have hcdc' : ¬(rest[0]? = some '-' ∧ rest[1]? = some '>') := fun e => hcdc ⟨rfl, e⟩
      simp only [Bool.false_eq_true, if_false, hcdc', h, if_true]
    · exact consumeToken_identStart c rest hc
    · obtain rfl := Option.some.inj hc
      rw [consumeToken_reverseSolidus]
      simp only [hv, if_true]

/-! ## A name with no escape -/

/-- What may follow a name: not an ident code point, and not a valid escape. -/
def nameStops (rest : List Char) : Bool :=
  !rest[0]?.any isIdent && !areValidEscape rest[0]? rest[1]?

theorem consumeIdentSequence_of_nameStops (rest : List Char) (h : nameStops rest = true) :
    consumeIdentSequence rest = ([], rest) := by
  cases rest with
  | nil => rw [consumeIdentSequence]
  | cons c rest =>
    simp only [nameStops, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.any_some,
      Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [consumeIdentSequence]
    simp only [h.1, h.2, Bool.false_eq_true, if_false]

/-- **A name of ident code points comes back**: before a text that does not go on the name,
`consumeIdentSequence` returns the name and that text. -/
theorem consumeIdentSequence_append (name rest : List Char) (hn : name.all isIdent = true)
    (hr : nameStops rest = true) : consumeIdentSequence (name ++ rest) = (name, rest) := by
  induction name with
  | nil => exact consumeIdentSequence_of_nameStops rest hr
  | cons c name ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    rw [List.cons_append, consumeIdentSequence]
    simp only [hn.1, if_true, ih hn.2]

/-- The two shapes of a plain identifier: it starts with an ident-start code point, or with a
hyphen-minus and then a hyphen-minus or an ident-start code point. -/
theorem isPlainIdentifier_shape {name : List Char} (h : isPlainIdentifier name = true) :
    ∃ c tail, name = c :: tail ∧ tail.all isIdent = true ∧
      (isIdentStart c = true ∨
        (c = '-' ∧ ∃ d tail', tail = d :: tail' ∧ (isIdentStart d = true ∨ d = '-'))) := by
  simp only [isPlainIdentifier, Bool.and_eq_true, startsIdent] at h
  obtain ⟨hall, hstart⟩ := h
  cases name with
  | nil => cases hstart
  | cons c tail =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    refine ⟨c, tail, rfl, hall.2, ?_⟩
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at hstart
    rcases wouldStartIdentSequence_cases hstart with ⟨hc, h₂⟩ | hc | ⟨hc, -⟩
    · obtain rfl := Option.some.inj hc
      right
      refine ⟨rfl, ?_⟩
      cases tail with
      | nil =>
        rcases h₂ with h₂ | h₂ | h₂
        · cases h₂
        · cases h₂
        · cases h₂
      | cons d tail' =>
        simp only [List.all_cons, Bool.and_eq_true] at hall
        refine ⟨d, tail', rfl, ?_⟩
        simp only [List.getElem?_cons_zero, Option.any_some, Option.some.injEq] at h₂
        rcases h₂ with h₂ | h₂ | h₂
        · exact Or.inl h₂
        · exact Or.inr h₂
        · have hd := Option.some.inj (areValidEscape_first h₂)
          subst hd
          exact absurd hall.2.1 (by decide)
    · exact Or.inl hc
    · obtain rfl := Option.some.inj hc
      exact absurd hall.1 (by decide)

/-- The code points before a plain identifier and what follows it would start an ident
sequence. -/
theorem wouldStart_of_isPlainIdentifier (name rest : List Char)
    (h : isPlainIdentifier name = true) :
    wouldStartIdentSequence (name ++ rest)[0]? (name ++ rest)[1]? (name ++ rest)[2]? = true := by
  obtain ⟨c, tail, rfl, -, hc | ⟨rfl, d, tail', rfl, hd⟩⟩ := isPlainIdentifier_shape h
  · exact wouldStartIdentSequence_of_isIdentStart c _ _ hc
  · simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, wouldStartIdentSequence,
      if_true, Option.any_some, Bool.or_eq_true, beq_iff_eq, Option.some.injEq]
    rcases hd with hd | hd
    · exact Or.inl (Or.inl hd)
    · exact Or.inl (Or.inr hd)

/-- A plain identifier and what follows it are not `-->`, unless the identifier is two
hyphen-minus and a greater-than sign follows. -/
theorem not_cdc_of_isPlainIdentifier (name rest : List Char) (h : isPlainIdentifier name = true)
    (hr : name = ['-', '-'] → rest[0]? ≠ some '>') :
    ¬((name ++ rest)[0]? = some '-' ∧ (name ++ rest)[1]? = some '-' ∧
      (name ++ rest)[2]? = some '>') := by
  obtain ⟨c, tail, rfl, hall, -⟩ := isPlainIdentifier_shape h
  rintro ⟨h₀, h₁, h₂⟩
  cases tail with
  | nil =>
    simp only [isPlainIdentifier, startsIdent, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, Bool.and_eq_true] at h
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, Option.some.injEq] at h₀
    subst h₀
    exact absurd h.2 (by decide)
  | cons d tail' =>
    cases tail' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at h₀ h₁ h₂
      subst h₀ h₁
      exact hr rfl h₂
    | cons e tail'' =>
      simp only [List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at h₂
      simp only [List.all_cons, Bool.and_eq_true] at hall
      subst h₂
      exact absurd hall.2.1 (by decide)

theorem serializeNameCodePoint_of_isIdent (c : Char) (h : isIdent c = true) :
    serializeNameCodePoint c = [c] := by
  obtain ⟨h₀, h₁, -⟩ := isIdent_facts h
  simp only [serializeNameCodePoint, h₀, if_false, h₁, Bool.false_eq_true, h, if_true]

theorem serializeName_of_all_isIdent (name : List Char) (h : name.all isIdent = true) :
    serializeName name = name := by
  induction name with
  | nil => rfl
  | cons c name ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [serializeName, serializeNameCodePoint_of_isIdent c h.1, ih h.2, List.cons_append,
      List.nil_append]

/-- **A plain identifier is written as it is.** -/
theorem serializeIdentifier_of_isPlainIdentifier (name : List Char)
    (h : isPlainIdentifier name = true) : serializeIdentifier name = name := by
  obtain ⟨c, tail, rfl, hall, hshape⟩ := isPlainIdentifier_shape h
  have hc : isIdent c = true := by
    simp only [isPlainIdentifier, List.all_cons, Bool.and_eq_true] at h
    exact h.1.1
  have hcd : isDigit c = false := by
    rcases hshape with hc' | ⟨rfl, -⟩
    · exact (isIdentStart_facts hc').2.1
    · decide
  cases tail with
  | nil =>
    have hne : c ≠ '-' := by
      rcases hshape with hc' | ⟨-, d, tail', htail, -⟩
      · rintro rfl
        exact absurd hc' (by decide)
      · cases htail
    simp only [serializeIdentifier, hne, if_false, hcd, Bool.false_eq_true,
      serializeNameCodePoint_of_isIdent c hc]
  | cons d tail' =>
    have hd : ¬(c = '-' ∧ isDigit d = true) := by
      rintro ⟨rfl, hd⟩
      rcases hshape with hc' | ⟨-, d', tail'', htail, hd'⟩
      · exact absurd hc' (by decide)
      · obtain ⟨rfl, -⟩ := List.cons.inj htail
        rcases hd' with hd' | rfl
        · rw [(isIdentStart_facts hd').2.1] at hd
          cases hd
        · exact absurd hd (by decide)
    simp only [serializeIdentifier, hcd, Bool.false_eq_true, if_false, hd,
      serializeNameCodePoint_of_isIdent c hc, serializeName_of_all_isIdent (d :: tail') hall,
      List.cons_append, List.nil_append]

end Whatwg.Css.Syntax
