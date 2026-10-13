import Whatwg.Css.Syntax.Parse.Laws

/-!
# Whatwg.Css.Syntax.Parse.Lines

Owner: the round trip of a stylesheet written with a line for each rule (slice K4 of
`docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

`Stylesheet.lines` writes each rule on a line of its own, with a line feed where
`Stylesheet.text` has a space. `tokenize_serialize` speaks of the text of one list of tokens, and
a line feed is the text of no token. This module carries the round trip of tokens one step
further and closes the law for the lines.

- `tokenize_serialize_append`: **the tokens of a text come back before more text**, where that
  text stops the last token. `tokenize_serialize` is the case of no more text.
- `tokenize_newline_cons`: a line feed before a text that is not white space is one whitespace
  token.
- `Stylesheet.lines_toList`: the code points of `Stylesheet.lines` are those of
  `Rule.linesText`, a function on lists that the kernel runs; the premise is stated on it, so
  that `decide` closes it.
- `tokenize_linesText`: the tokens of the lines are the tokens of the stylesheet.
- `parseStylesheetText_lines`: **parsing the lines of a stylesheet gives the stylesheet**, where
  it is `Stylesheet.writableLines`.

A readable rule at the top of a stylesheet ends with a semicolon or a right curly bracket, and
any text stops those two tokens (`Rule.tokens_shape`). So the line feed after a rule ends the
rule's last token, whatever the next line holds.
-/

namespace Whatwg.Css.Syntax

/-! ## The round trip of tokens before more text -/

/-- What is written after a token, and then a text that stops the last token, stops the
token. -/
theorem stops_serializeAfter_append (R : List Char) (rest : List Token) :
    ∀ a : Token, writableAfter a rest = true → noWhitespaceRun (a :: rest) = true →
      (∀ l, (a :: rest).getLast? = some l → l.stops R = true) →
      a.stops (serializeAfter a rest ++ R) = true := by
  induction rest with
  | nil =>
    intro a _ _ hlast
    rw [serializeAfter, List.nil_append]
    exact hlast a rfl
  | cons b rest ih =>
    intro a hw hrun hlast
    simp only [writableAfter, Bool.and_eq_true] at hw
    obtain ⟨⟨-, hab⟩, hrest⟩ := hw
    have hb := writable_of_writableAfter hrest
    rw [noWhitespaceRun, Bool.and_eq_true] at hrun
    have hne : ¬(a = .whitespace ∧ b = .whitespace) := fun hboth => by
      obtain ⟨ha, hb'⟩ := hboth
      subst ha
      subst hb'
      exact absurd hrun.1 (by decide)
    have ihb := ih b hrest hrun.2 fun l hl => hlast l (by rw [List.getLast?_cons_cons]; exact hl)
    rw [serializeAfter, separator, List.append_assoc, List.append_assoc]
    by_cases hc : needsComment a b = true
    · rw [if_pos hc]
      exact stops_comment a b _ hc
    · rw [if_neg hc, List.nil_append]
      exact stops_text a b _ hb hab (Bool.eq_false_iff.mpr hc) hne (fun _ _ => ihb)

/-- The text of a token and what is written after it, before a text that stops the last token:
the tokens, and then the tokens of that text. -/
theorem tokenize_serializeAfter_append (R : List Char) (rest : List Token) :
    ∀ a : Token, writableAfter a rest = true → noWhitespaceRun (a :: rest) = true →
      (∀ l, (a :: rest).getLast? = some l → l.stops R = true) →
      tokenize (a.text ++ (serializeAfter a rest ++ R)) = a :: (rest ++ tokenize R) := by
  induction rest with
  | nil =>
    intro a hw _ hlast
    rw [serializeAfter, List.nil_append,
      tokenize_text a R (writable_of_writableAfter hw) (hlast a rfl), List.nil_append]
  | cons b rest ih =>
    intro a hw hrun hlast
    have hs := stops_serializeAfter_append R (b :: rest) a hw hrun hlast
    have hw' := hw
    simp only [writableAfter, Bool.and_eq_true] at hw'
    obtain ⟨⟨ha, -⟩, hrest⟩ := hw'
    rw [noWhitespaceRun, Bool.and_eq_true] at hrun
    have ihb := ih b hrest hrun.2 fun l hl => hlast l (by rw [List.getLast?_cons_cons]; exact hl)
    rw [tokenize_text a _ ha hs, serializeAfter, separator, List.append_assoc, List.append_assoc]
    by_cases hc : needsComment a b = true
    · rw [if_pos hc]
      exact congrArg (a :: ·) ((tokenize_comment _).trans ihb)
    · rw [if_neg hc, List.nil_append, ihb]
      rfl

/-- **The tokens of a text come back before more text**, where that text stops the last token:
for every list of writable tokens with no two whitespace tokens together. With no more text this
is `tokenize_serialize_eq`. -/
theorem tokenize_serialize_append {tokens : List Token} (hw : Writable tokens = true)
    (hrun : noWhitespaceRun tokens = true) (R : List Char)
    (hlast : ∀ l, tokens.getLast? = some l → l.stops R = true) :
    tokenize (serialize tokens ++ R) = tokens ++ tokenize R := by
  cases tokens with
  | nil => rw [serialize, List.nil_append, List.nil_append]
  | cons a rest =>
    rw [serialize, List.append_assoc]
    exact tokenize_serializeAfter_append R rest a hw hrun hlast

/-- A line feed before a text that is not white space is one whitespace token. -/
theorem tokenize_newline_cons (Z : List Char) (hZ : Z[0]?.any isWhitespace = false) :
    tokenize ('\n' :: Z) = .whitespace :: tokenize Z := by
  have hdrop : Z.dropWhile isWhitespace = Z := by
    cases Z with
    | nil => rfl
    | cons c tl =>
      have hc : isWhitespace c = false := hZ
      exact List.dropWhile_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)
  rw [tokenize_of_some (consumeToken_whitespace '\n' Z false (by decide)), hdrop]

/-! ## The tokens of a rule -/

theorem getLast?_append_singleton {α : Type} (l : List α) (a : α) :
    (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_append]
  rfl

theorem getLast?_append_pair {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).getLast? = some b := by
  rw [List.getLast?_append]
  rfl

/-- A block opens with a left curly bracket and ends with a right curly bracket. -/
theorem blockShape (inner : List Token) :
    (∃ after, (if inner.isEmpty = true then [Token.openCurly, Token.whitespace, Token.closeCurly]
        else Token.openCurly :: Token.whitespace ::
          (inner ++ [Token.whitespace, Token.closeCurly])) = Token.openCurly :: after) ∧
      (if inner.isEmpty = true then [Token.openCurly, Token.whitespace, Token.closeCurly]
        else Token.openCurly :: Token.whitespace ::
          (inner ++ [Token.whitespace, Token.closeCurly])).getLast? = some Token.closeCurly := by
  cases inner with
  | nil => exact ⟨⟨_, rfl⟩, rfl⟩
  | cons a l =>
    exact ⟨⟨_, rfl⟩,
      getLast?_append_pair (Token.openCurly :: Token.whitespace :: a :: l) Token.whitespace
        Token.closeCurly⟩

theorem blockTokens_shape (D R : List Token) :
    (∃ after, blockTokens D R = .openCurly :: after) ∧
      (blockTokens D R).getLast? = some .closeCurly :=
  blockShape _

/-- **A readable rule at the top of a stylesheet opens with a token that is not white space, and
ends with a semicolon or a right curly bracket.** -/
theorem Rule.tokens_shape {r : Rule} (h : r.readable false = true) :
    (∃ b tl, r.tokens = b :: tl ∧ b ≠ .whitespace) ∧
      (r.tokens.getLast? = some .semicolon ∨ r.tokens.getLast? = some .closeCurly) := by
  cases r with
  | statement name prelude =>
    refine ⟨⟨.atKeyword name, _, by rw [Rule.tokens], fun e => by cases e⟩, Or.inl ?_⟩
    rw [Rule.tokens]
    exact getLast?_append_singleton (Token.atKeyword name :: Component.tokensAll prelude)
      Token.semicolon
  | blockAt name prelude ds rs =>
    refine ⟨⟨.atKeyword name, _, by rw [Rule.tokens], fun e => by cases e⟩, Or.inr ?_⟩
    rw [Rule.tokens]
    show ((Token.atKeyword name :: Component.tokensAll prelude) ++ blockTokens _ _).getLast? = _
    rw [List.getLast?_append, (blockTokens_shape _ _).2]
    rfl
  | qualified prelude ds rs =>
    obtain ⟨-, hopens, -⟩ := Rule.readable_qualified h
    obtain ⟨after, hafter⟩ := (blockTokens_shape (Declaration.tokensAll ds) (Rule.tokensAll rs)).1
    obtain ⟨token, tail, htok, hs, -⟩ := qualified_head_top hopens after
    refine ⟨⟨token, tail, by rw [Rule.tokens, hafter, htok], fun e => hs (Or.inl e)⟩, Or.inr ?_⟩
    rw [Rule.tokens, List.getLast?_append, (blockTokens_shape _ _).2]
    rfl
  | nested ds =>
    rw [Rule.readable] at h
    cases h

/-! ## The lines of a stylesheet -/

theorem Rule.text_toList (r : Rule) : r.text.toList = serialize r.tokens := by
  unfold Rule.text
  exact String.toList_ofList

/-- **The code points of `Stylesheet.lines` are those of `Rule.linesText`.** -/
theorem lines_toList : ∀ (rules : List Rule),
    ("\n".intercalate (rules.map Rule.text)).toList = Rule.linesText rules
  | [] => by
    rw [List.map_nil, String.intercalate_nil, Rule.linesText]
    rfl
  | [r] => by
    rw [List.map_cons, List.map_nil, String.intercalate_singleton, Rule.linesText,
      Rule.text_toList]
  | r :: s :: rest => by
    have ih := lines_toList (s :: rest)
    rw [List.map_cons, List.map_cons, String.intercalate_cons_cons, ← List.map_cons,
      String.toList_append, String.toList_append, Rule.text_toList, ih, Rule.linesText,
      List.append_assoc]
    rfl

theorem Stylesheet.lines_toList (s : Stylesheet) : s.lines.toList = Rule.linesText s.rules :=
  Whatwg.Css.Syntax.lines_toList s.rules

/-- The lines of rules open with the text of the first rule. -/
theorem Rule.linesText_cons (r : Rule) (rest : List Rule) :
    ∃ tail, Rule.linesText (r :: rest) = serialize r.tokens ++ tail := by
  cases rest with
  | nil => exact ⟨[], by rw [Rule.linesText, List.append_nil]⟩
  | cons s more => exact ⟨'\n' :: Rule.linesText (s :: more), by rw [Rule.linesText]⟩

/-- **The tokens of the lines of a row of rules are the tokens of the row**: each rule's tokens,
and a whitespace token for each line feed. -/
theorem tokenize_linesText : ∀ (rules : List Rule), rules.all (Rule.readable false) = true →
    rules.all (fun r => Writable r.tokens && noWhitespaceRun r.tokens) = true →
    tokenize (Rule.linesText rules) = Rule.tokensAll rules
  | [], _, _ => by
    rw [Rule.linesText, Rule.tokensAll]
    exact tokenize_nil
  | [r], _, hw => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at hw
    rw [Rule.linesText, Rule.tokensAll_singleton, tokenize_serialize_eq r.tokens hw.1.1 hw.1.2]
  | r :: s :: rest, hr, hw => by
    rw [List.all_cons, Bool.and_eq_true] at hr
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at hw
    have ih := tokenize_linesText (s :: rest) hr.2 hw.2
    have hlast := (Rule.tokens_shape hr.1).2
    have hs := hr.2
    rw [List.all_cons, Bool.and_eq_true] at hs
    have hws := hw.2
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at hws
    obtain ⟨b, tl, htok, hb⟩ := (Rule.tokens_shape hs.1).1
    obtain ⟨tail, htail⟩ := Rule.linesText_cons s rest
    have hfirst : (Rule.linesText (s :: rest))[0]?.any isWhitespace = false := by
      have hbw : b.writable = true := writable_of_writableAfter (by
        have h := hws.1.1
        rw [htok] at h
        exact h)
      have hstops := stops_whitespace_text b (serializeAfter b tl ++ tail) hbw hb
      rw [htail, htok, serialize, List.append_assoc]
      exact eq_false_of_not hstops
    have hstop : ∀ l, r.tokens.getLast? = some l →
        l.stops ('\n' :: Rule.linesText (s :: rest)) = true := by
      intro l hl
      rcases hlast with h | h
      · rw [h] at hl
        cases hl
        rfl
      · rw [h] at hl
        cases hl
        rfl
    rw [Rule.linesText, tokenize_serialize_append hw.1.1 hw.1.2 _ hstop,
      tokenize_newline_cons _ hfirst, ih, Rule.tokensAll_cons_cons,
      Rule.gap_of_not_nested (Rule.not_nested_of_readable_top hr.1)]
    rfl

/-- **Parsing the lines of a stylesheet gives the stylesheet**, where it is
`Stylesheet.writableLines`. A caller that writes a stylesheet with a line for each rule holds
the same proof as one that writes it on one line. -/
theorem parseStylesheetText_lines (s : Stylesheet) (h : s.writableLines = true) :
    parseStylesheetText s.lines = s := by
  unfold Stylesheet.writableLines at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hw, hpre⟩, hread⟩ := h
  show parseStylesheet (tokenize (filterCodePoints s.lines.toList)) = s
  rw [Stylesheet.lines_toList, hpre, tokenize_linesText s.rules hread hw]
  exact parseStylesheet_tokens s hread

end Whatwg.Css.Syntax
