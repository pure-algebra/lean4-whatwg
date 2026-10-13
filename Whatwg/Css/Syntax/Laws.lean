import Whatwg.Css.Syntax.Laws.Text

/-!
# Whatwg.Css.Syntax.Laws

Owner: the round trip of serialization (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; ruling CS-7;
proof graph `CSS-PG-SYNTAX`).

The section `serialization` of CSS Syntax Module Level 3 asks one thing of a writer: "The only
requirement for serialization is that it must "round-trip" with parsing", "except for
consecutive `<whitespace-token>`s, which may be collapsed into a single token". This module
proves it of `serialize`, at the tokens:

- `tokenize_serialize`: **the tokens of what the writer wrote are the tokens it was given**,
  with each run of whitespace tokens as one. For every list that is `Writable`.
- `tokenize_serialize_eq`: with no two whitespace tokens next to each other, they are the same
  list.

How it is built. `tokenize_text` (`Whatwg/Css/Syntax/Laws/Text.lean`) reads one token back
before a text that stops it. `stops_text` says that the text of the next token stops the one
before, where the pair needs no comment: this is where the table of `serialization-tables` is
used, cell by cell, and where the two pairs of `extraPairs` showed that they are needed.
`stops_comment` says that a comment stops every token that a comment may follow.

What is not claimed. The law is about `tokenize`, the reading of the sealed text in
`Whatwg/Css/Syntax/Tokenize.lean`, and about tokens: a parser's tree is slice K4. A token
outside `Token.writable` (a unit that needs an escape, a url, a unicode-range) is not covered.
-/

namespace Whatwg.Css.Syntax

/-! ## What the first code point of a text says -/

theorem marked_absurd {a b : Token} {P : Prop} (h : needsComment a b = false)
    (h' : needsComment a b = true) : P := by
  rw [h] at h'
  cases h'

theorem some_beq_some_false {c d : Char} (h : c ≠ d) : (some c == some d) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
  exact h

theorem isDelimiter_facts {d : Char} (h : isDelimiter d = true) :
    isWhitespace d = false ∧ isDigit d = false ∧ isIdentStart d = false ∧ d ≠ '(' ∧
      (d ≠ '-' → isIdent d = false) := by
  simp only [isDelimiter, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, -⟩, -⟩, d₃⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hdigit⟩, hstart⟩ := h
  refine ⟨hw, hdigit, hstart, d₃, fun hm => ?_⟩
  have := toNat_ne_of_ne hm
  simp only [isIdent, hstart, hdigit, Bool.or_self, Bool.false_or, beq_eq_false_iff_ne, ne_eq]
  exact this

theorem nameStops_cons (c : Char) (X : List Char) (h₁ : isIdent c = false) (h₂ : c ≠ '\\') :
    nameStops (c :: X) = true := by
  show (!isIdent c && !areValidEscape (some c) X[0]?) = true
  simp only [h₁, areValidEscape, some_beq_some_false h₂, Bool.false_and, Bool.not_false, Bool.and_self]

theorem wouldStartIdentSequence_cons_false (c : Char) (c₂ c₃ : Option Char)
    (h₁ : isIdentStart c = false) (h₂ : c ≠ '-') (h₃ : c ≠ '\\') :
    wouldStartIdentSequence (some c) c₂ c₃ = false := by
  simp only [wouldStartIdentSequence, Option.some.injEq, h₂, if_false, Option.any_some, h₁,
    Bool.false_eq_true, h₃]

theorem wouldStartNumber_sign_false (s c : Char) (c₃ : Option Char) (hs : s = '+' ∨ s = '-')
    (h₁ : isDigit c = false) (h₂ : c ≠ '.') : wouldStartNumber (some s) (some c) c₃ = false := by
  simp only [wouldStartNumber, Option.some.injEq, hs, if_true, Option.any_some, h₁,
    some_beq_some_false h₂, Bool.false_and, Bool.or_self]

/-- The first code points of the text of a number and what follows it: a digit, a plus sign,
or a hyphen-minus and a digit. -/
theorem number_lead (n : Numeric) (flag : NumberFlag) (r : List Char) :
    ∃ c X, n.text flag ++ r = c :: X ∧
      (isDigit c = true ∨ c = '+' ∨ (c = '-' ∧ ∃ d Y, X = d :: Y ∧ isDigit d = true)) := by
  obtain ⟨d, tail, htext, hd⟩ := n.text_cons flag
  rw [htext]
  cases n.sign with
  | none => exact ⟨d, tail ++ r, rfl, Or.inl hd⟩
  | some s =>
    cases s with
    | plus => exact ⟨'+', d :: tail ++ r, rfl, Or.inr (Or.inl rfl)⟩
    | minus => exact ⟨'-', d :: tail ++ r, rfl, Or.inr (Or.inr ⟨rfl, d, tail ++ r, rfl, hd⟩)⟩

/-! ## The text of the next token stops the one before -/

theorem stops_ident_text (v : List Char) (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.ident v) b = false) : (Token.ident v).stops (b.text ++ r) = true := by
  cases b with
  | ident _ | function _ | url _ | badUrl | number _ _ | percentage _ | dimension _ _ _ | cdc
    | openParen => exact marked_absurd hc rfl
  | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma | openSquare
    | closeSquare | closeParen | openCurly | closeCurly => rfl
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · have hm : d ≠ '-' := by
        rintro rfl
        exact marked_absurd hc rfl
      obtain ⟨-, -, -, hp, hi⟩ := isDelimiter_facts hb
      have hn := nameStops_cons d r (hi hm) h₀
      rw [Token.text, if_neg h₀]
      show (nameStops (d :: r) && !(some d == some '(') && !(some d == some '>' && v == ['-', '-'])) = true
      rw [hn, some_beq_some_false hp]
      by_cases hgt : d = '>'
      · subst hgt
        have hv : (v == ['-', '-']) = false := by
          cases hv : v == ['-', '-'] with
          | false => rfl
          | true =>
            rw [eq_of_beq hv] at hc
            exact marked_absurd hc rfl
        rw [hv]
        rfl
      · rw [some_beq_some_false hgt]
        rfl

theorem stops_name_text (a b : Token) (r : List Char) (hb : b.writable = true)
    (ha : (∃ v, a = .atKeyword v) ∨ (∃ v f, a = .hash v f) ∨ a = .delim '#')
    (hc : needsComment a b = false) : nameStops (b.text ++ r) = true := by
  rcases ha with ⟨v, rfl⟩ | ⟨v, f, rfl⟩ | rfl
  all_goals
    cases b with
    | ident _ | function _ | url _ | badUrl | number _ _ | percentage _ | dimension _ _ _ | cdc =>
      exact marked_absurd hc rfl
    | unicodeRange _ _ => cases hb
    | hash _ flag => cases flag <;> rfl
    | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma | openSquare
      | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
    | delim d =>
      by_cases h₀ : d = '\\'
      · subst h₀
        rfl
      · have hm : d ≠ '-' := by
          rintro rfl
          exact marked_absurd hc rfl
        rw [Token.text, if_neg h₀]
        exact nameStops_cons d r ((isDelimiter_facts hb).2.2.2.2 hm) h₀

theorem stops_dimension_text (n : Numeric) (f : NumberFlag) (u : List Char) (b : Token)
    (r : List Char) (hb : b.writable = true) (hc : needsComment (.dimension n f u) b = false)
    (hbr : ∀ c, b = .delim c → b.stops r = true) :
    (Token.dimension n f u).stops (b.text ++ r) = true := by
  cases b with
  | ident _ | function _ | url _ | badUrl | number _ _ | percentage _ | dimension _ _ _ | cdc =>
    exact marked_absurd hc rfl
  | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma | openSquare
    | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · have hm : d ≠ '-' := by
        rintro rfl
        exact marked_absurd hc rfl
      have hn := nameStops_cons d r ((isDelimiter_facts hb).2.2.2.2 hm) h₀
      rw [Token.text, if_neg h₀]
      show (nameStops (d :: r) && !(some d == some '+' && r[0]?.any isDigit)) = true
      rw [hn]
      by_cases hplus : d = '+'
      · subst hplus
        have h : (r[0]?.any isDigit || (r[0]? == some '.' && r[1]?.any isDigit)) = false :=
          eq_false_of_not (hbr '+' rfl)
        rw [Bool.or_eq_false_iff] at h
        rw [h.1]
        rfl
      · rw [some_beq_some_false hplus]
        rfl

theorem stops_number_text (n : Numeric) (f : NumberFlag) (b : Token) (r : List Char)
    (hb : b.writable = true) (hc : needsComment (.number n f) b = false)
    (hbr : ∀ c, b = .delim c → b.stops r = true) :
    (Token.number n f).stops (b.text ++ r) = true := by
  cases b with
  | ident _ | function _ | url _ | badUrl | number _ _ | percentage _ | dimension _ _ _ | cdc =>
    exact marked_absurd hc rfl
  | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma | openSquare
    | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    by_cases h₁ : d = '%'
    · subst h₁
      exact marked_absurd hc rfl
    by_cases h₂ : d = '.'
    · subst h₂
      have h : r[0]?.any isDigit = false := eq_false_of_not (hbr '.' rfl)
      show (!false && !(true && r[0]?.any isDigit) &&
        !wouldStartIdentSequence (some '.') r[0]? r[1]? && !false) = true
      rw [h]
      rfl
    by_cases h₃ : d = '-'
    · subst h₃
      have h : (!wouldStartNumber (some '-') r[0]? r[1]? && !(r[0]? == some '-' && r[1]? == some '>') &&
          !wouldStartIdentSequence (some '-') r[0]? r[1]?) = true := hbr '-' rfl
      rw [Bool.and_eq_true] at h
      show (!false && !(false && r[0]?.any isDigit) &&
        !wouldStartIdentSequence (some '-') r[0]? r[1]? && !false) = true
      rw [eq_false_of_not h.2]
      rfl
    · obtain ⟨-, hdigit, hstart, -, -⟩ := isDelimiter_facts hb
      rw [Token.text, if_neg h₀]
      show (!isDigit d && !(some d == some '.' && r[0]?.any isDigit) &&
        !wouldStartIdentSequence (some d) r[0]? r[1]? && !(some d == some '%')) = true
      rw [hdigit, some_beq_some_false h₂, wouldStartIdentSequence_cons_false d _ _ hstart h₃ h₀,
        some_beq_some_false h₁]
      rfl

theorem stops_plus_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '+') b = false) (hbr : ∀ c, b = .delim c → b.stops r = true) :
    (Token.delim '+').stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), isDigit c = false → c ≠ '.' →
      (Token.delim '+').stops (c :: X) = true := by
    intro c X h₁ h₂
    show (!wouldStartNumber (some '+') (some c) X[0]?) = true
    rw [wouldStartNumber_sign_false '+' c _ (Or.inl rfl) h₁ h₂]
    rfl
  have lead : ∀ (name s : List Char), isNameValue name = true →
      (Token.delim '+').stops (serializeIdentifier name ++ s) = true := by
    intro name s hn
    obtain ⟨c, X, hT, hcl | rfl | rfl⟩ :=
      serializeIdentifier_lead name s (isNameValue_facts hn).1 (isNameValue_facts hn).2
    · rw [hT]
      exact key c X (isIdentStart_facts hcl).2.1 (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  cases b with
  | number _ _ | percentage _ | dimension _ _ _ => exact marked_absurd hc rfl
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | cdc | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | ident name => exact lead name r hb
  | function name =>
    rw [Token.text, List.append_assoc]
    exact lead name _ hb
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    by_cases h₂ : d = '.'
    · subst h₂
      have h : r[0]?.any isDigit = false := eq_false_of_not (hbr '.' rfl)
      show (!(false || (true && r[0]?.any isDigit))) = true
      rw [h]
      rfl
    · rw [Token.text, if_neg h₀]
      exact key d r (isDelimiter_facts hb).2.1 h₂

theorem wouldStartIdentSequence_minus_false (d : Char) (c₃ : Option Char)
    (h₁ : isIdentStart d = false) (h₂ : d ≠ '-') (h₃ : d ≠ '\\') :
    wouldStartIdentSequence (some '-') (some d) c₃ = false := by
  simp only [wouldStartIdentSequence, if_true, Option.any_some, h₁, some_beq_some_false h₂,
    areValidEscape, some_beq_some_false h₃, Bool.false_and, Bool.or_self]

theorem stops_minus_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '-') b = false) (hbr : ∀ c, b = .delim c → b.stops r = true) :
    (Token.delim '-').stops (b.text ++ r) = true := by
  cases b with
  | ident _ | function _ | url _ | badUrl | number _ _ | percentage _ | dimension _ _ _ | cdc =>
    exact marked_absurd hc rfl
  | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma | openSquare
    | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    by_cases h₃ : d = '-'
    · subst h₃
      exact marked_absurd hc rfl
    by_cases h₂ : d = '.'
    · subst h₂
      have h : r[0]?.any isDigit = false := eq_false_of_not (hbr '.' rfl)
      show (!(false || (true && r[0]?.any isDigit)) && !(false && r[0]? == some '>') &&
        !wouldStartIdentSequence (some '-') (some '.') r[0]?) = true
      rw [h]
      rfl
    · obtain ⟨-, hdigit, hstart, -, -⟩ := isDelimiter_facts hb
      rw [Token.text, if_neg h₀]
      show (!wouldStartNumber (some '-') (some d) r[0]? && !(some d == some '-' && r[0]? == some '>') &&
        !wouldStartIdentSequence (some '-') (some d) r[0]?) = true
      rw [wouldStartNumber_sign_false '-' d _ (Or.inr rfl) hdigit h₂, some_beq_some_false h₃,
        wouldStartIdentSequence_minus_false d _ hstart h₃ h₀]
      rfl

theorem stops_fullStop_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '.') b = false) : (Token.delim '.').stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), isDigit c = false →
      (Token.delim '.').stops (c :: X) = true := by
    intro c X h₁
    show (!isDigit c) = true
    rw [h₁]
    rfl
  have lead : ∀ (name s : List Char), isNameValue name = true →
      (Token.delim '.').stops (serializeIdentifier name ++ s) = true := by
    intro name s hn
    obtain ⟨c, X, hT, hcl | rfl | rfl⟩ :=
      serializeIdentifier_lead name s (isNameValue_facts hn).1 (isNameValue_facts hn).2
    · rw [hT]
      exact key c X (isIdentStart_facts hcl).2.1
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  cases b with
  | number _ _ | percentage _ | dimension _ _ _ => exact marked_absurd hc rfl
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | cdc | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | ident name => exact lead name r hb
  | function name =>
    rw [Token.text, List.append_assoc]
    exact lead name _ hb
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · rw [Token.text, if_neg h₀]
      exact key d r (isDelimiter_facts hb).2.1

theorem stops_solidus_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '/') b = false) : (Token.delim '/').stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), c ≠ '*' → (Token.delim '/').stops (c :: X) = true := by
    intro c X h
    show (!(some c == some '*')) = true
    rw [some_beq_some_false h]
    rfl
  have lead : ∀ (name s : List Char), isNameValue name = true →
      (Token.delim '/').stops (serializeIdentifier name ++ s) = true := by
    intro name s hn
    obtain ⟨c, X, hT, hcl | rfl | rfl⟩ :=
      serializeIdentifier_lead name s (isNameValue_facts hn).1 (isNameValue_facts hn).2
    · rw [hT]
      exact key c X (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  have number : ∀ (n : Numeric) (f : NumberFlag) (s : List Char),
      (Token.delim '/').stops (n.text f ++ s) = true := by
    intro n f s
    obtain ⟨c, X, hT, hcl | rfl | ⟨rfl, -⟩⟩ := number_lead n f s
    · rw [hT]
      exact key c X (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  cases b with
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | cdc | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | ident name => exact lead name r hb
  | function name =>
    rw [Token.text, List.append_assoc]
    exact lead name _ hb
  | number n f => exact number n f r
  | percentage n =>
    rw [Token.text, List.append_assoc]
    exact number n _ _
  | dimension n f u =>
    rw [Token.text, List.append_assoc]
    exact number n f _
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · have hm : d ≠ '*' := by
        rintro rfl
        exact marked_absurd hc rfl
      rw [Token.text, if_neg h₀]
      exact key d r hm

theorem stops_lessThan_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '<') b = false) : (Token.delim '<').stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), c ≠ '!' → (Token.delim '<').stops (c :: X) = true := by
    intro c X h
    show (!(some c == some '!' && X[0]? == some '-' && X[1]? == some '-')) = true
    rw [some_beq_some_false h]
    rfl
  have lead : ∀ (name s : List Char), isNameValue name = true →
      (Token.delim '<').stops (serializeIdentifier name ++ s) = true := by
    intro name s hn
    obtain ⟨c, X, hT, hcl | rfl | rfl⟩ :=
      serializeIdentifier_lead name s (isNameValue_facts hn).1 (isNameValue_facts hn).2
    · rw [hT]
      exact key c X (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  have number : ∀ (n : Numeric) (f : NumberFlag) (s : List Char),
      (Token.delim '<').stops (n.text f ++ s) = true := by
    intro n f s
    obtain ⟨c, X, hT, hcl | rfl | ⟨rfl, -⟩⟩ := number_lead n f s
    · rw [hT]
      exact key c X (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  cases b with
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | cdc | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | ident name => exact lead name r hb
  | function name =>
    rw [Token.text, List.append_assoc]
    exact lead name _ hb
  | number n f => exact number n f r
  | percentage n =>
    rw [Token.text, List.append_assoc]
    exact number n _ _
  | dimension n f u =>
    rw [Token.text, List.append_assoc]
    exact number n f _
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · have hm : d ≠ '!' := by
        rintro rfl
        exact marked_absurd hc rfl
      rw [Token.text, if_neg h₀]
      exact key d r hm

theorem stops_at_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hc : needsComment (.delim '@') b = false) : (Token.delim '@').stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), isIdentStart c = false → c ≠ '-' → c ≠ '\\' →
      (Token.delim '@').stops (c :: X) = true := by
    intro c X h₁ h₂ h₃
    show (!wouldStartIdentSequence (some c) X[0]? X[1]?) = true
    rw [wouldStartIdentSequence_cons_false c _ _ h₁ h₂ h₃]
    rfl
  have number : ∀ (n : Numeric) (f : NumberFlag) (s : List Char),
      (Token.delim '@').stops (n.text f ++ s) = true := by
    intro n f s
    obtain ⟨c, X, hT, hcl | rfl | ⟨rfl, d, Y, rfl, hd⟩⟩ := number_lead n f s
    · rw [hT]
      exact key c X (isDigit_facts hcl).2.1 (by rintro rfl; exact absurd hcl (by decide))
        (by rintro rfl; exact absurd hcl (by decide))
    · rw [hT]
      rfl
    · rw [hT]
      show (!wouldStartIdentSequence (some '-') (some d) Y[0]?) = true
      rw [wouldStartIdentSequence_minus_false d _ (isDigit_facts hd).2.1
        (by rintro rfl; exact absurd hd (by decide)) (by rintro rfl; exact absurd hd (by decide))]
      rfl
  cases b with
  | ident _ | function _ | cdc => exact marked_absurd hc rfl
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | whitespace | cdo | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | number n f => exact number n f r
  | percentage n =>
    rw [Token.text, List.append_assoc]
    exact number n _ _
  | dimension n f u =>
    rw [Token.text, List.append_assoc]
    exact number n f _
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · have hm : d ≠ '-' := by
        rintro rfl
        exact marked_absurd hc rfl
      rw [Token.text, if_neg h₀]
      exact key d r (isDelimiter_facts hb).2.2.1 hm h₀

theorem stops_whitespace_text (b : Token) (r : List Char) (hb : b.writable = true)
    (hne : b ≠ .whitespace) : Token.whitespace.stops (b.text ++ r) = true := by
  have key : ∀ (c : Char) (X : List Char), isWhitespace c = false →
      Token.whitespace.stops (c :: X) = true := by
    intro c X h
    show (!isWhitespace c) = true
    rw [h]
    rfl
  have lead : ∀ (name s : List Char), isNameValue name = true →
      Token.whitespace.stops (serializeIdentifier name ++ s) = true := by
    intro name s hn
    obtain ⟨c, X, hT, hcl | rfl | rfl⟩ :=
      serializeIdentifier_lead name s (isNameValue_facts hn).1 (isNameValue_facts hn).2
    · rw [hT]
      exact key c X (isIdentStart_facts hcl).1
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  have number : ∀ (n : Numeric) (f : NumberFlag) (s : List Char),
      Token.whitespace.stops (n.text f ++ s) = true := by
    intro n f s
    obtain ⟨c, X, hT, hcl | rfl | ⟨rfl, -⟩⟩ := number_lead n f s
    · rw [hT]
      exact key c X (isDigit_facts hcl).1
    · rw [hT]
      rfl
    · rw [hT]
      rfl
  cases b with
  | url _ | badUrl | unicodeRange _ _ => cases hb
  | whitespace => exact absurd rfl hne
  | hash _ flag => cases flag <;> rfl
  | atKeyword _ | string _ | badString | cdo | cdc | colon | semicolon | comma
    | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl
  | ident name => exact lead name r hb
  | function name =>
    rw [Token.text, List.append_assoc]
    exact lead name _ hb
  | number n f => exact number n f r
  | percentage n =>
    rw [Token.text, List.append_assoc]
    exact number n _ _
  | dimension n f u =>
    rw [Token.text, List.append_assoc]
    exact number n f _
  | delim d =>
    by_cases h₀ : d = '\\'
    · subst h₀
      rfl
    · rw [Token.text, if_neg h₀]
      exact key d r (isDelimiter_facts hb).1

theorem stops_function_text (v : List Char) (b : Token) (r : List Char)
    (hab : (Token.function v).mayPrecede b = true) :
    (Token.function v).stops (b.text ++ r) = true := by
  cases hurl : isUrlName v with
  | false => simp only [Token.stops, hurl, Bool.not_false, Bool.or_true]
  | true =>
    cases b with
    | string value => rfl
    | _ => simp only [Token.mayPrecede, hurl, Bool.not_true, Bool.or_self, Bool.false_eq_true] at hab

theorem stops_delim_text (c : Char) (b : Token) (r : List Char) (hb : b.writable = true)
    (hab : (Token.delim c).mayPrecede b = true) (hc : needsComment (.delim c) b = false)
    (hbr : ∀ d, b = .delim d → b.stops r = true) : (Token.delim c).stops (b.text ++ r) = true := by
  by_cases h₁ : c = '#'
  · subst h₁
    exact stops_name_text _ b r hb (Or.inr (Or.inr rfl)) hc
  by_cases h₂ : c = '+'
  · subst h₂
    exact stops_plus_text b r hb hc hbr
  by_cases h₃ : c = '-'
  · subst h₃
    exact stops_minus_text b r hb hc hbr
  by_cases h₄ : c = '.'
  · subst h₄
    exact stops_fullStop_text b r hb hc
  by_cases h₅ : c = '<'
  · subst h₅
    exact stops_lessThan_text b r hb hc
  by_cases h₆ : c = '@'
  · subst h₆
    exact stops_at_text b r hb hc
  by_cases h₇ : c = '\\'
  · subst h₇
    have hw : (b == Token.whitespace) = true := hab
    rw [eq_of_beq hw]
    rfl
  by_cases h₈ : c = '/'
  · subst h₈
    exact stops_solidus_text b r hb hc
  · simp only [Token.stops, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, if_false]

/-- **The text of the next token stops the one before**, where the pair needs no comment. This
is the table of `serialization-tables` at work: for each row, the tokens that its cells leave
unmarked start with a code point that does not go on the row's token. Two delimiters look one
token further: a hyphen-minus after a number and a full stop after a number or a sign are
stopped by what stops them. -/
theorem stops_text (a b : Token) (r : List Char) (hb : b.writable = true)
    (hab : a.mayPrecede b = true) (hc : needsComment a b = false)
    (hne : ¬(a = .whitespace ∧ b = .whitespace)) (hbr : ∀ c, b = .delim c → b.stops r = true) :
    a.stops (b.text ++ r) = true := by
  cases a with
  | ident v => exact stops_ident_text v b r hb hc
  | function v => exact stops_function_text v b r hab
  | atKeyword v => exact stops_name_text _ b r hb (Or.inl ⟨v, rfl⟩) hc
  | hash v f => exact stops_name_text _ b r hb (Or.inr (Or.inl ⟨v, f, rfl⟩)) hc
  | badString =>
    have hw : (b == Token.whitespace) = true := hab
    rw [eq_of_beq hw]
    rfl
  | delim c => exact stops_delim_text c b r hb hab hc hbr
  | number n f => exact stops_number_text n f b r hb hc hbr
  | dimension n f u => exact stops_dimension_text n f u b r hb hc hbr
  | whitespace => exact stops_whitespace_text b r hb (fun h => hne ⟨rfl, h⟩)
  | string _ | url _ | badUrl | percentage _ | unicodeRange _ _ | cdo | cdc | colon | semicolon
    | comma | openSquare | closeSquare | openParen | closeParen | openCurly | closeCurly => rfl

/-- **A comment stops every token that a comment may follow.** -/
theorem stops_comment (a b : Token) (r : List Char) (hc : needsComment a b = true) :
    a.stops ('/' :: '*' :: '*' :: '/' :: r) = true := by
  cases a with
  | function v => exact marked_absurd (a := .function v) (b := b) rfl hc
  | badString => exact marked_absurd (a := .badString) (b := b) rfl hc
  | delim c =>
    by_cases h₇ : c = '\\'
    · subst h₇
      exact marked_absurd (a := .delim '\\') (b := b) rfl hc
    · simp only [Token.stops, h₇, if_false]
      (repeat' split) <;> rfl
  | _ => rfl

/-- A token that may end a list is stopped by the end of the text. -/
theorem stops_nil (a : Token) (he : a.mayEnd = true) : a.stops [] = true := by
  cases a with
  | function v =>
    show (false || !isUrlName v) = true
    rw [Bool.false_or]
    exact he
  | badString => cases he
  | delim c =>
    have hc : c ≠ '\\' := by
      simp only [Token.mayEnd, bne_iff_ne, ne_eq] at he
      exact he
    simp only [Token.stops, hc, if_false]
    (repeat' split) <;> rfl
  | _ => rfl

/-! ## The round trip -/

theorem writable_of_writableAfter {a : Token} {rest : List Token}
    (h : writableAfter a rest = true) : a.writable = true := by
  cases rest with
  | nil =>
    simp only [writableAfter, Bool.and_eq_true] at h
    exact h.1
  | cons b rest =>
    simp only [writableAfter, Bool.and_eq_true] at h
    exact h.1.1

/-- What is written after a token stops it, unless the token and the next are both
whitespace. -/
theorem stops_serializeAfter (rest : List Token) :
    ∀ a : Token, writableAfter a rest = true →
      (a = .whitespace → rest.head? ≠ some .whitespace) →
      a.stops (serializeAfter a rest) = true := by
  induction rest with
  | nil =>
    intro a hw _
    simp only [writableAfter, Bool.and_eq_true] at hw
    exact stops_nil a hw.2
  | cons b rest ih =>
    intro a hw hne
    simp only [writableAfter, Bool.and_eq_true] at hw
    obtain ⟨⟨-, hab⟩, hrest⟩ := hw
    have hb := writable_of_writableAfter hrest
    rw [serializeAfter, separator]
    by_cases hc : needsComment a b = true
    · rw [if_pos hc]
      exact stops_comment a b _ hc
    · rw [if_neg hc, List.nil_append]
      refine stops_text a b _ hb hab (Bool.eq_false_iff.mpr hc) (fun h => hne h.1 ?_) ?_
      · rw [h.2]
        rfl
      · intro c hbc
        exact ih b hrest (fun hws => by rw [hbc] at hws; cases hws)

theorem tokenize_serializeAfter (rest : List Token) :
    ∀ a : Token, writableAfter a rest = true →
      tokenize (a.text ++ serializeAfter a rest) = collapse (a :: rest) := by
  induction rest with
  | nil =>
    intro a hw
    have hs := stops_serializeAfter [] a hw (fun _ h => by cases h)
    rw [tokenize_text a _ (writable_of_writableAfter hw) hs, serializeAfter, tokenize_nil]
    rfl
  | cons b rest ih =>
    intro a hw
    have hw' := hw
    simp only [writableAfter, Bool.and_eq_true] at hw'
    obtain ⟨⟨ha, -⟩, hrest⟩ := hw'
    by_cases hws : a = .whitespace ∧ b = .whitespace
    · obtain ⟨rfl, rfl⟩ := hws
      have hcol : collapse (.whitespace :: .whitespace :: rest) = collapse (.whitespace :: rest) := by
        rw [collapse]
        simp only [and_self, if_true]
      rw [hcol, ← ih .whitespace hrest]
      exact tokenize_whitespace_cons ' ' ' ' _ (by decide) (by decide)
    · have hs := stops_serializeAfter (b :: rest) a hw (fun h₁ h₂ => hws ⟨h₁, Option.some.inj h₂⟩)
      have htail : tokenize (serializeAfter a (b :: rest)) = collapse (b :: rest) := by
        rw [serializeAfter, separator]
        by_cases hc : needsComment a b = true
        · rw [if_pos hc]
          exact (tokenize_comment _).trans (ih b hrest)
        · rw [if_neg hc, List.nil_append]
          exact ih b hrest
      have hcol : collapse (a :: b :: rest) = a :: collapse (b :: rest) := by
        rw [collapse]
        simp only [hws, if_false]
      rw [tokenize_text a _ ha hs, htail, hcol]

/-- **The round trip of serialization.** The tokens of what the writer wrote are the tokens it
was given, with each run of whitespace tokens as one: for every list of writable tokens. This
is the requirement of the section `serialization` of CSS Syntax Module Level 3, at the tokens,
for the tokenizer of `Whatwg/Css/Syntax/Tokenize.lean`. -/
theorem tokenize_serialize (tokens : List Token) (h : Writable tokens = true) :
    tokenize (serialize tokens) = collapse tokens := by
  cases tokens with
  | nil => exact tokenize_nil
  | cons a rest => exact tokenize_serializeAfter rest a h

theorem collapse_of_noWhitespaceRun (tokens : List Token) (h : noWhitespaceRun tokens = true) :
    collapse tokens = tokens := by
  induction tokens with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      simp only [noWhitespaceRun, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
        beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at h
      have hws : ¬(a = .whitespace ∧ b = .whitespace) := fun hab => h.1 hab.1 hab.2
      rw [collapse]
      simp only [hws, if_false, ih h.2]

/-- **The round trip, with no run of whitespace**: a list of writable tokens in which no two
whitespace tokens are next to each other is the list of tokens of its own text. -/
theorem tokenize_serialize_eq (tokens : List Token) (h : Writable tokens = true)
    (hrun : noWhitespaceRun tokens = true) : tokenize (serialize tokens) = tokens := by
  rw [tokenize_serialize tokens h, collapse_of_noWhitespaceRun tokens hrun]

end Whatwg.Css.Syntax
