import Whatwg.Css.Syntax.Readable

/-!
# Whatwg.Css.Syntax.Readable.Append

Owner: the premise of the parser's round trip over two rows of rules in a row (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entry W14 of `docs/research/2026-10-12-whatwg-requests.md`).

A stylesheet is put together from parts: the faces, the rules of a look, the rules of a page.
`Stylesheet.writableLines` of `Whatwg/Css/Syntax/Readable.lean` is the premise under which the
lines of a stylesheet parse to it (`parseStylesheetText_lines`). This module says that the
premise of the whole is the premises of the parts, so a caller that has checked each part has
checked their row.

- `filterCodePoints_eq_self_iff`: **a text is its own preprocessing exactly when it has no
  carriage return, no form feed and no U+0000** (`isFiltered`).
- `Rule.linesText_append`: the lines of two rows of rules are the lines of each, with a line
  feed between.
- `Stylesheet.writableLines_append`: **two rows of rules in a row are `writableLines` exactly
  when each is.**

The laws of preprocessing depend on `propext` and `Quot.sound` at most. The two laws of rows
of rules also depend on `Classical.choice`, as the writer of tokens does.
-/

namespace Whatwg.Css.Syntax

/-- A code point that preprocessing leaves as it is: no carriage return, no form feed and no
U+0000. -/
def isFiltered (c : Char) : Bool := c != '\r' && c != '\x0c' && c != '\x00'

/-- Preprocessing leaves a code point as it is exactly when it is none of the three. -/
theorem filterCodePoint_eq_self_iff (c : Char) : filterCodePoint c = c ↔ isFiltered c = true := by
  unfold filterCodePoint isFiltered
  by_cases h₁ : c = '\r'
  · subst h₁
    decide
  · by_cases h₂ : c = '\x0c'
    · subst h₂
      decide
    · by_cases h₃ : c = '\x00'
      · subst h₃
        decide
      · have hor : ¬(c = '\r' ∨ c = '\x0c') := fun h => h.elim h₁ h₂
        rw [if_neg hor, if_neg h₃, bne_iff_ne.mpr h₁, bne_iff_ne.mpr h₂, bne_iff_ne.mpr h₃]
        exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **A text is its own preprocessing exactly when it has no carriage return, no form feed and
no U+0000.** -/
theorem filterCodePoints_eq_self_iff : ∀ text : List Char,
    filterCodePoints text = text ↔ text.all isFiltered = true
  | [] => by
    rw [filterCodePoints]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | [c] => by
    rw [filterCodePoints, List.all_cons, List.all_nil, Bool.and_true,
      ← filterCodePoint_eq_self_iff]
    exact ⟨fun h => (List.cons.inj h).1, fun h => congrArg (· :: []) h⟩
  | c :: d :: rest => by
    have ih := filterCodePoints_eq_self_iff (d :: rest)
    rw [filterCodePoints]
    by_cases h : c = '\r' ∧ d = '\n'
    · rw [if_pos h]
      obtain ⟨rfl, rfl⟩ := h
      constructor
      · intro heq
        exact absurd (List.cons.inj heq).1 (by decide)
      · intro hall
        rw [List.all_cons] at hall
        exact Bool.noConfusion (show false = true from hall)
    · rw [if_neg h, List.all_cons, Bool.and_eq_true, ← ih, ← filterCodePoint_eq_self_iff]
      constructor
      · intro heq
        exact ⟨(List.cons.inj heq).1, (List.cons.inj heq).2⟩
      · rintro ⟨h₁, h₂⟩
        rw [h₁, h₂]

/-- Whether a text is its own preprocessing, as the test that `Stylesheet.writableLines`
computes: the same as having none of the three code points. -/
theorem filterCodePoints_beq (text : List Char) :
    (filterCodePoints text == text) = text.all isFiltered := by
  rw [Bool.eq_iff_iff, beq_iff_eq]
  exact filterCodePoints_eq_self_iff text

/-- **The lines of two rows of rules are the lines of each, with a line feed between.** -/
theorem Rule.linesText_append : ∀ (a b : List Rule), a ≠ [] → b ≠ [] →
    Rule.linesText (a ++ b) = Rule.linesText a ++ '\n' :: Rule.linesText b
  | [], _, h, _ => absurd rfl h
  | [_], [], _, h => absurd rfl h
  | [r], s :: rest, _, _ => by
    rw [List.singleton_append, Rule.linesText, Rule.linesText]
  | r :: r' :: more, b, _, hb => by
    rw [List.cons_append, List.cons_append, Rule.linesText, ← List.cons_append,
      Rule.linesText_append (r' :: more) b (List.cons_ne_nil _ _) hb, Rule.linesText,
      List.append_assoc]
    rfl

/-- Six tests in two rows of three are the same six in three rows of two. -/
theorem and_rows : ∀ p q r s t u : Bool,
    ((p && q) && (r && s) && (t && u)) = ((p && r && t) && (q && s && u)) := by
  decide

/-- **Two rows of rules in a row are `writableLines` exactly when each is.** So the premise of
the parser's round trip is checked part by part. -/
theorem Stylesheet.writableLines_append (a b : List Rule) :
    Stylesheet.writableLines ⟨a ++ b⟩ =
      (Stylesheet.writableLines ⟨a⟩ && Stylesheet.writableLines ⟨b⟩) := by
  cases a with
  | nil => rfl
  | cons r more =>
    cases b with
    | nil =>
      rw [List.append_nil]
      exact (Bool.and_true _).symm
    | cons s rest =>
      unfold Stylesheet.writableLines Stylesheet.readable
      rw [filterCodePoints_beq, filterCodePoints_beq, filterCodePoints_beq,
        Rule.linesText_append (r :: more) (s :: rest) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _),
        List.all_append, List.all_append, List.all_append, List.all_cons (a := '\n')]
      show (_ && _ && (_ && (true && _)) && (_ && _)) = _
      rw [Bool.true_and]
      exact and_rows _ _ _ _ _ _

end Whatwg.Css.Syntax
