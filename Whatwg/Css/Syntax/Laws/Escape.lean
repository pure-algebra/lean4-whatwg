import Whatwg.Css.Syntax.Laws.String

/-!
# Whatwg.Css.Syntax.Laws.Escape

Owner: names with escapes read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph
`CSS-PG-SYNTAX`).

CSSOM's "serialize an identifier" writes any name: a code point that the tokenizer does not
take in a name is escaped, and so is a digit or a hyphen-minus where it would not start an
identifier. The laws here say that such a text is read back as the name, whatever the name
holds but U+0000.

- `consumeIdentSequence_serializeName`, `consumeIdentSequence_serializeIdentifier`: **the name
  comes back.**
- `serializeIdentifier_shape`: the four ways the text of an identifier starts.
- `wouldStart_serializeIdentifier`: the text would start an ident sequence.
- `not_cdc_serializeIdentifier`: the text and what follows it are not `-->`, unless the name is
  two hyphen-minus before a greater-than sign.
-/

namespace Whatwg.Css.Syntax

theorem isNewline_of_isHexDigit {c : Char} (h : isHexDigit c = true) : isNewline c = false := by
  simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isNewline, beq_eq_false_iff_ne, ne_eq]
  omega

theorem isHexDigit_of_not_isIdent {c : Char} (h : isIdent c = false) : isHexDigit c = false := by
  simp only [isIdent, isIdentStart, isLetter, isNonAsciiIdent, isDigit, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq] at h
  simp only [isHexDigit, isDigit, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem isNewline_of_not_isControl {c : Char} (h : isControl c = false) : isNewline c = false := by
  simp only [isControl, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, ne_eq] at h
  simp only [isNewline, beq_eq_false_iff_ne, ne_eq]
  omega

theorem isIdentStart_of_isIdent {c : Char} (h : isIdent c = true) (h₁ : isDigit c = false)
    (h₂ : c ≠ '-') : isIdentStart c = true := by
  simp only [isIdent, h₁, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact h
  · exact absurd (eq_of_toNat_eq h) h₂

/-! ## The text of one code point -/

/-- An escape as a code point is a reverse solidus, a hex digit, and a text that reads back as
the code point. -/
theorem escapeAsCodePoint_shape (c : Char) (hc : c.toNat ≠ 0) :
    ∃ x tl, escapeAsCodePoint c = '\\' :: x :: tl ∧ isHexDigit x = true ∧
      ∀ rest, consumeEscapedCodePoint (x :: tl ++ rest) = (c, rest) := by
  obtain ⟨hall, -⟩ := hex_toDigits c.toNat
  cases hd : Nat.toDigits 16 c.toNat with
  | nil => exact absurd hd Nat.toDigits_ne_nil
  | cons d more =>
    rw [hd] at hall
    refine ⟨d, more ++ [' '], ?_, hall d List.mem_cons_self, fun rest => ?_⟩
    · rw [escapeAsCodePoint, hd]
      rfl
    · have := consumeEscapedCodePoint_hex c rest hc
      rw [hd] at this
      rw [List.cons_append, List.append_assoc]
      exact this

/-- One code point of a name is written as itself, where it is an ident code point, or as an
escape that reads back as it. -/
theorem serializeNameCodePoint_shape (c : Char) (hc : c.toNat ≠ 0) :
    (isIdent c = true ∧ serializeNameCodePoint c = [c]) ∨
      ∃ x tl, serializeNameCodePoint c = '\\' :: x :: tl ∧ isNewline x = false ∧
        ∀ rest, consumeEscapedCodePoint (x :: tl ++ rest) = (c, rest) := by
  by_cases hcontrol : isControl c = true
  · right
    obtain ⟨x, tl, htext, hx, hcons⟩ := escapeAsCodePoint_shape c hc
    refine ⟨x, tl, ?_, isNewline_of_isHexDigit hx, hcons⟩
    rw [serializeNameCodePoint, if_neg hc, if_pos hcontrol, htext]
  · by_cases hident : isIdent c = true
    · left
      refine ⟨hident, ?_⟩
      rw [serializeNameCodePoint, if_neg hc, if_neg hcontrol, if_pos hident]
    · right
      refine ⟨c, [], ?_, isNewline_of_not_isControl (Bool.eq_false_iff.mpr hcontrol), fun rest => ?_⟩
      · rw [serializeNameCodePoint, if_neg hc, if_neg hcontrol, if_neg hident]
        rfl
      · exact consumeEscapedCodePoint_of_not_hex c rest
          (isHexDigit_of_not_isIdent (Bool.eq_false_iff.mpr hident))

/-! ## The name comes back -/

theorem consumeIdentSequence_ident (c : Char) (rest : List Char) (h : isIdent c = true) :
    consumeIdentSequence (c :: rest) =
      (c :: (consumeIdentSequence rest).1, (consumeIdentSequence rest).2) := by
  rw [consumeIdentSequence]
  simp only [h, if_true]

theorem consumeIdentSequence_escaped (x : Char) (tl rest : List Char) (c : Char)
    (hx : isNewline x = false) (he : consumeEscapedCodePoint (x :: tl ++ rest) = (c, rest)) :
    consumeIdentSequence ('\\' :: x :: tl ++ rest) =
      (c :: (consumeIdentSequence rest).1, (consumeIdentSequence rest).2) := by
  have hv : areValidEscape (some '\\') (some x) = true := by
    show (!isNewline x) = true
    rw [hx]
    rfl
  rw [List.cons_append] at he
  rw [List.cons_append, List.cons_append, consumeIdentSequence]
  simp only [show isIdent '\\' = false from rfl, Bool.false_eq_true, if_false, List.getElem?_cons_zero, hv,
    if_true, he]

theorem consumeIdentSequence_nameCodePoint (c : Char) (rest : List Char) (hc : c.toNat ≠ 0) :
    consumeIdentSequence (serializeNameCodePoint c ++ rest) =
      (c :: (consumeIdentSequence rest).1, (consumeIdentSequence rest).2) := by
  rcases serializeNameCodePoint_shape c hc with ⟨hi, ht⟩ | ⟨x, tl, ht, hx, he⟩
  · rw [ht]
    exact consumeIdentSequence_ident c rest hi
  · rw [ht]
    exact consumeIdentSequence_escaped x tl rest c hx (he rest)

theorem consumeIdentSequence_escapeAsCodePoint (c : Char) (rest : List Char) (hc : c.toNat ≠ 0) :
    consumeIdentSequence (escapeAsCodePoint c ++ rest) =
      (c :: (consumeIdentSequence rest).1, (consumeIdentSequence rest).2) := by
  obtain ⟨x, tl, ht, hx, he⟩ := escapeAsCodePoint_shape c hc
  rw [ht]
  exact consumeIdentSequence_escaped x tl rest c (isNewline_of_isHexDigit hx) (he rest)

/-- **A name comes back, whatever it holds but U+0000**: the text that `serializeName` writes,
before a text that does not go on the name. -/
theorem consumeIdentSequence_serializeName (name rest : List Char)
    (hn : (name.all fun c => c.toNat != 0) = true) (hr : nameStops rest = true) :
    consumeIdentSequence (serializeName name ++ rest) = (name, rest) := by
  induction name with
  | nil => exact consumeIdentSequence_of_nameStops rest hr
  | cons c name ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    rw [serializeName, List.append_assoc, consumeIdentSequence_nameCodePoint c _ hn.1, ih hn.2]

/-- **An identifier comes back, whatever it holds but U+0000**: the text that CSSOM's
"serialize an identifier" writes, before a text that does not go on the name. -/
theorem consumeIdentSequence_serializeIdentifier (name rest : List Char)
    (hn : (name.all fun c => c.toNat != 0) = true) (hr : nameStops rest = true) :
    consumeIdentSequence (serializeIdentifier name ++ rest) = (name, rest) := by
  have base := consumeIdentSequence_of_nameStops rest hr
  cases name with
  | nil => exact base
  | cons c tail =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨hc, htail⟩ := hn
    cases tail with
    | nil =>
      rw [serializeIdentifier]
      by_cases h₁ : c = '-'
      · subst h₁
        rw [if_pos rfl]
        exact (consumeIdentSequence_escaped '-' [] rest '-' rfl
          (consumeEscapedCodePoint_of_not_hex '-' rest rfl)).trans (by rw [base])
      · rw [if_neg h₁]
        by_cases h₂ : isDigit c = true
        · rw [if_pos h₂, consumeIdentSequence_escapeAsCodePoint c rest hc, base]
        · rw [if_neg h₂, consumeIdentSequence_nameCodePoint c rest hc, base]
    | cons d tail' =>
      have hname := consumeIdentSequence_serializeName (d :: tail') rest htail hr
      rw [serializeIdentifier]
      by_cases h₂ : isDigit c = true
      · rw [if_pos h₂, List.append_assoc, consumeIdentSequence_escapeAsCodePoint c _ hc, hname]
      · rw [if_neg h₂]
        by_cases h₃ : c = '-' ∧ isDigit d = true
        · rw [if_pos h₃]
          obtain ⟨rfl, -⟩ := h₃
          simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at htail
          rw [List.cons_append, List.append_assoc, consumeIdentSequence_ident '-' _ rfl,
            consumeIdentSequence_escapeAsCodePoint d _ htail.1,
            consumeIdentSequence_serializeName tail' rest htail.2 hr]
        · rw [if_neg h₃, List.append_assoc, consumeIdentSequence_nameCodePoint c _ hc, hname]

/-! ## How the text of an identifier starts -/

/-- The text of a name and what follows it start with a greater-than sign only where the name
is empty and what follows starts with one: a greater-than sign in a name is escaped. -/
theorem serializeName_head_greaterThan (tail rest : List Char)
    (hn : (tail.all fun c => c.toNat != 0) = true)
    (h : (serializeName tail ++ rest)[0]? = some '>') : tail = [] ∧ rest[0]? = some '>' := by
  cases tail with
  | nil => exact ⟨rfl, h⟩
  | cons e tail' =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    rw [serializeName, List.append_assoc] at h
    rcases serializeNameCodePoint_shape e hn.1 with ⟨hi, ht⟩ | ⟨x, tl, ht, -, -⟩
    · rw [ht] at h
      obtain rfl : e = '>' := Option.some.inj h
      exact absurd hi (by decide)
    · rw [ht] at h
      exact absurd (Option.some.inj h) (by decide)

/-- **The four ways the text of an identifier starts**: with an ident-start code point; with
an escape; with a hyphen-minus and then an ident-start code point or a hyphen-minus; with a
hyphen-minus and then an escape. After two hyphen-minus a greater-than sign comes only where
the identifier is those two and the sign is in what follows. -/
theorem serializeIdentifier_shape (name rest : List Char) (hne : name ≠ [])
    (hn : (name.all fun c => c.toNat != 0) = true) :
    (∃ c X, serializeIdentifier name ++ rest = c :: X ∧ isIdentStart c = true) ∨
    (∃ x X, serializeIdentifier name ++ rest = '\\' :: x :: X ∧ isNewline x = false) ∨
    (∃ d X, serializeIdentifier name ++ rest = '-' :: d :: X ∧ (isIdentStart d = true ∨ d = '-') ∧
      (d = '-' → X[0]? = some '>' → name = ['-', '-'] ∧ rest[0]? = some '>')) ∨
    (∃ x X, serializeIdentifier name ++ rest = '-' :: '\\' :: x :: X ∧ isNewline x = false) := by
  cases name with
  | nil => exact absurd rfl hne
  | cons c tail =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨hc, htail⟩ := hn
    cases tail with
    | nil =>
      by_cases h₁ : c = '-'
      · subst h₁
        exact Or.inr (Or.inl ⟨'-', rest, rfl, rfl⟩)
      by_cases h₂ : isDigit c = true
      · obtain ⟨x, tl, htext, hx, -⟩ := escapeAsCodePoint_shape c hc
        have ht : serializeIdentifier [c] = '\\' :: x :: tl := by
          rw [serializeIdentifier, if_neg h₁, if_pos h₂, htext]
        exact Or.inr (Or.inl ⟨x, tl ++ rest, congrArg (· ++ rest) ht, isNewline_of_isHexDigit hx⟩)
      · have ht : serializeIdentifier [c] = serializeNameCodePoint c := by
          rw [serializeIdentifier, if_neg h₁, if_neg h₂]
        rcases serializeNameCodePoint_shape c hc with ⟨hi, htc⟩ | ⟨x, tl, htc, hx, -⟩
        · rw [htc] at ht
          exact Or.inl ⟨c, rest, congrArg (· ++ rest) ht,
            isIdentStart_of_isIdent hi (Bool.eq_false_iff.mpr h₂) h₁⟩
        · rw [htc] at ht
          exact Or.inr (Or.inl ⟨x, tl ++ rest, congrArg (· ++ rest) ht, hx⟩)
    | cons d tail' =>
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at htail
      obtain ⟨hd, htail'⟩ := htail
      by_cases h₂ : isDigit c = true
      · obtain ⟨x, tl, htext, hx, -⟩ := escapeAsCodePoint_shape c hc
        have ht : serializeIdentifier (c :: d :: tail') =
            ('\\' :: x :: tl) ++ serializeName (d :: tail') := by
          rw [serializeIdentifier, if_pos h₂, htext]
        exact Or.inr (Or.inl ⟨x, tl ++ serializeName (d :: tail') ++ rest, congrArg (· ++ rest) ht,
          isNewline_of_isHexDigit hx⟩)
      by_cases h₃ : c = '-' ∧ isDigit d = true
      · obtain ⟨x, tl, htext, hx, -⟩ := escapeAsCodePoint_shape d hd
        have ht : serializeIdentifier (c :: d :: tail') =
            c :: (('\\' :: x :: tl) ++ serializeName tail') := by
          rw [serializeIdentifier, if_neg h₂, if_pos h₃, htext]
        obtain ⟨rfl, -⟩ := h₃
        exact Or.inr (Or.inr (Or.inr ⟨x, tl ++ serializeName tail' ++ rest, congrArg (· ++ rest) ht,
          isNewline_of_isHexDigit hx⟩))
      · have ht : serializeIdentifier (c :: d :: tail') =
            serializeNameCodePoint c ++ (serializeNameCodePoint d ++ serializeName tail') := by
          rw [serializeIdentifier, if_neg h₂, if_neg h₃]
          rfl
        rcases serializeNameCodePoint_shape c hc with ⟨hi, htc⟩ | ⟨x, tl, htc, hx, -⟩
        · rw [htc] at ht
          by_cases hstart : isIdentStart c = true
          · exact Or.inl ⟨c, serializeNameCodePoint d ++ serializeName tail' ++ rest,
              congrArg (· ++ rest) ht, hstart⟩
          · have hminus : c = '-' := by
              cases hm : decide (c = '-') with
              | true => exact of_decide_eq_true hm
              | false =>
                exact absurd (isIdentStart_of_isIdent hi (Bool.eq_false_iff.mpr h₂)
                  (of_decide_eq_false hm)) hstart
            subst hminus
            have hdd : isDigit d = false := Bool.eq_false_iff.mpr (fun h => h₃ ⟨rfl, h⟩)
            rcases serializeNameCodePoint_shape d hd with ⟨hid, htd⟩ | ⟨x, tl, htd, hx, -⟩
            · rw [htd] at ht
              refine Or.inr (Or.inr (Or.inl ⟨d, serializeName tail' ++ rest,
                congrArg (· ++ rest) ht, ?_, ?_⟩))
              · cases hm : decide (d = '-') with
                | true => exact Or.inr (of_decide_eq_true hm)
                | false => exact Or.inl (isIdentStart_of_isIdent hid hdd (of_decide_eq_false hm))
              · intro hdm hgt
                obtain ⟨rfl, hrest⟩ := serializeName_head_greaterThan tail' rest htail' hgt
                rw [hdm]
                exact ⟨rfl, hrest⟩
            · rw [htd] at ht
              exact Or.inr (Or.inr (Or.inr ⟨x, tl ++ serializeName tail' ++ rest,
                congrArg (· ++ rest) ht, hx⟩))
        · rw [htc] at ht
          exact Or.inr (Or.inl ⟨x, tl ++ (serializeNameCodePoint d ++ serializeName tail') ++ rest,
            congrArg (· ++ rest) ht, hx⟩)

/-- The text of an identifier would start an ident sequence. -/
theorem wouldStart_serializeIdentifier (name rest : List Char) (hne : name ≠ [])
    (hn : (name.all fun c => c.toNat != 0) = true) :
    wouldStartIdentSequence (serializeIdentifier name ++ rest)[0]?
      (serializeIdentifier name ++ rest)[1]? (serializeIdentifier name ++ rest)[2]? = true := by
  rcases serializeIdentifier_shape name rest hne hn with
    ⟨c, X, hT, hc⟩ | ⟨x, X, hT, hx⟩ | ⟨d, X, hT, hd, -⟩ | ⟨x, X, hT, hx⟩
  · rw [hT]
    exact wouldStartIdentSequence_of_isIdentStart c _ _ hc
  · rw [hT]
    show (!isNewline x) = true
    rw [hx]
    rfl
  · rw [hT]
    show wouldStartIdentSequence (some '-') (some d) X[0]? = true
    rcases hd with hd | rfl
    · simp only [wouldStartIdentSequence, if_true, Option.any_some, hd, Bool.true_or]
    · rfl
  · rw [hT]
    show (!isNewline x) = true
    rw [hx]
    rfl

/-- The text of an identifier and what follows it are not `-->`, unless the identifier is two
hyphen-minus and a greater-than sign follows. -/
theorem not_cdc_serializeIdentifier (name rest : List Char) (hne : name ≠ [])
    (hn : (name.all fun c => c.toNat != 0) = true)
    (hr : name = ['-', '-'] → rest[0]? ≠ some '>') :
    ¬((serializeIdentifier name ++ rest)[0]? = some '-' ∧
      (serializeIdentifier name ++ rest)[1]? = some '-' ∧
      (serializeIdentifier name ++ rest)[2]? = some '>') := by
  rintro ⟨h₀, h₁, h₂⟩
  rcases serializeIdentifier_shape name rest hne hn with
    ⟨c, X, hT, hc⟩ | ⟨x, X, hT, -⟩ | ⟨d, X, hT, -, hgt⟩ | ⟨x, X, hT, -⟩
  · rw [hT] at h₀
    obtain rfl : c = '-' := Option.some.inj h₀
    exact absurd hc (by decide)
  · rw [hT] at h₀
    exact absurd (Option.some.inj h₀) (by decide)
  · rw [hT] at h₁ h₂
    obtain ⟨hname, hrest⟩ := hgt (Option.some.inj h₁) h₂
    exact hr hname hrest
  · rw [hT] at h₁
    exact absurd (Option.some.inj h₁) (by decide)

/-- The first code point of the text of an identifier: an ident-start code point, a
hyphen-minus or a reverse solidus. -/
theorem serializeIdentifier_lead (name rest : List Char) (hne : name ≠ [])
    (hn : (name.all fun c => c.toNat != 0) = true) :
    ∃ c X, serializeIdentifier name ++ rest = c :: X ∧
      (isIdentStart c = true ∨ c = '-' ∨ c = '\\') := by
  rcases serializeIdentifier_shape name rest hne hn with
    ⟨c, X, hT, hc⟩ | ⟨x, X, hT, -⟩ | ⟨d, X, hT, -, -⟩ | ⟨x, X, hT, -⟩
  · exact ⟨c, X, hT, Or.inl hc⟩
  · exact ⟨'\\', x :: X, hT, Or.inr (Or.inr rfl)⟩
  · exact ⟨'-', d :: X, hT, Or.inr (Or.inl rfl)⟩
  · exact ⟨'-', '\\' :: x :: X, hT, Or.inr (Or.inl rfl)⟩

end Whatwg.Css.Syntax
