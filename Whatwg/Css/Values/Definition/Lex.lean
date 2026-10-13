import Whatwg.Css.Values.Definition

/-!
# Whatwg.Css.Values.Definition.Lex

Owner: the first half of the round trip of the Value Definition Syntax (slice K3 of
`docs/CSS-PACKAGE-PLAN.md`; ruling CS-4): cutting a printed text into lexemes gives the
lexemes that were printed.

- `Lexeme.ok`: a lexeme the printer writes for a tree with `wf`.
- `lexOne_text`: the reader takes a printed lexeme whole, when what follows it is the end, a
  space or a multiplier.
- `lex_render`: the lexemes of a rendered list are the list.

What this module does not claim: anything about a text the printer did not write. `lex` skips
white space that `render` never writes, and no law here speaks of it.
-/

namespace Whatwg.Css.Values

/-! ## Runs of characters -/

/-- A run of characters of a class, followed by one that is not of it, is taken whole. -/
theorem takeWhile_append_stop {p : Char → Bool} {w rest : List Char}
    (hw : ∀ c ∈ w, p c = true) (hr : ∀ c t, rest = c :: t → p c = false) :
    (w ++ rest).takeWhile p = w := by
  induction w with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c t =>
      simp only [List.nil_append, List.takeWhile_cons, hr c t rfl, Bool.false_eq_true, if_false]
  | cons a w ih =>
    simp only [List.cons_append, List.takeWhile_cons, hw a List.mem_cons_self, if_true]
    rw [ih (fun c hc => hw c (List.mem_cons_of_mem a hc))]

/-- What is left after such a run is what followed it. -/
theorem dropWhile_append_stop {p : Char → Bool} {w rest : List Char}
    (hw : ∀ c ∈ w, p c = true) (hr : ∀ c t, rest = c :: t → p c = false) :
    (w ++ rest).dropWhile p = rest := by
  induction w with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c t =>
      simp only [List.nil_append, List.dropWhile_cons, hr c t rfl, Bool.false_eq_true, if_false]
  | cons a w ih =>
    simp only [List.cons_append, List.dropWhile_cons, hw a List.mem_cons_self, if_true]
    exact ih (fun c hc => hw c (List.mem_cons_of_mem a hc))

/-- A run of characters of a class is taken whole. -/
theorem takeWhile_all {p : Char → Bool} {w : List Char} (hw : ∀ c ∈ w, p c = true) :
    w.takeWhile p = w := by
  have h := takeWhile_append_stop (rest := []) hw (fun _ _ h => nomatch h)
  rwa [List.append_nil] at h

/-- Nothing is left after a run of characters of a class. -/
theorem dropWhile_all {p : Char → Bool} {w : List Char} (hw : ∀ c ∈ w, p c = true) :
    w.dropWhile p = [] := by
  have h := dropWhile_append_stop (rest := []) hw (fun _ _ h => nomatch h)
  rwa [List.append_nil] at h

/-- A character of a class is not one the class leaves out. -/
theorem bne_of_class {p : Char → Bool} {c : Char} (h : p c = true) (x : Char)
    (hx : p x = false) : (c != x) = true :=
  bne_iff_ne.mpr fun e => by
    rw [e, hx] at h
    exact Bool.noConfusion h

/-- The same, as a test that fails. -/
theorem beq_of_class {p : Char → Bool} {c : Char} (h : p c = true) (x : Char)
    (hx : p x = false) : (c == x) = false :=
  beq_eq_false_iff_ne.mpr fun e => by
    rw [e, hx] at h
    exact Bool.noConfusion h

/-- A character of a class is not of a class that shares none with it at that character. -/
theorem isStart_isWord {c : Char} (h : isStart c = true) : isWord c = true := by
  simp only [isStart, Bool.and_eq_true] at h
  exact h.1

theorem isStart_not_digit {c : Char} (h : isStart c = true) : c.isDigit = false := by
  simp only [isStart, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem isUnit_not_digit {c : Char} (h : isUnit c = true) : c.isDigit = false := by
  simp only [isUnit, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

/-- The characters of a name: the first opens one, and each is of `isWord`. -/
theorem isNameChars_cons {s : List Char} (h : isNameChars s = true) :
    ∃ c t, s = c :: t ∧ isStart c = true ∧ ∀ x ∈ c :: t, isWord x = true := by
  cases s with
  | nil => exact Bool.noConfusion h
  | cons c t =>
    simp only [isNameChars, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨c, t, rfl, h.1, fun x hx => ?_⟩
    cases hx with
    | head => exact isStart_isWord h.1
    | tail _ hx => exact h.2 x hx

/-! ## What may follow a printed lexeme -/

/-- The characters that follow a lexeme in a rendered text: a space, or the first character
of a multiplier. -/
def boundary : List Char := [' ', '*', '+', '?', '!', '#', '{']

/-- The text is the end, or opens with a space or with a multiplier. -/
def Stops (rest : List Char) : Prop := ∀ c t, rest = c :: t → c ∈ boundary

theorem Stops.nil : Stops [] := fun _ _ h => nomatch h

/-- A test that fails on every boundary character fails at the head of such a text. -/
theorem Stops.fails {rest : List Char} (hs : Stops rest) (p : Char → Bool)
    (hp : ∀ c ∈ boundary, p c = false) : ∀ c t, rest = c :: t → p c = false :=
  fun c t h => hp c (hs c t h)

/-- Such a text does not open with a character that is no boundary. -/
theorem Stops.head_ne {rest : List Char} (hs : Stops rest) (x : Char)
    (hx : ∀ c ∈ boundary, (c == x) = false) : (rest.head? == some x) = false := by
  cases rest with
  | nil => rfl
  | cons c t =>
    have h := hx c (hs c t rfl)
    simp only [List.head?_cons, Option.some_beq_some, h]

/-! ## Numbers -/

theorem natText_isDigit (n : Nat) : ∀ c ∈ natText n, c.isDigit = true :=
  fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem natText_isEmpty (n : Nat) : (natText n).isEmpty = false := by
  cases h : natText n with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons _ _ => rfl

theorem readNat_natText (n : Nat) : readNat (natText n) = n := Nat.ofDigitChars_ten_toDigits

/-- A repeat is read from what the printer writes between its braces. -/
theorem readRepeat_body (r : Repeat) : readRepeat r.body = some r := by
  cases r with
  | exactly a =>
    simp only [Repeat.body, readRepeat, takeWhile_all (natText_isDigit a),
      dropWhile_all (natText_isDigit a), natText_isEmpty, Bool.false_eq_true, if_false,
      readNat_natText]
  | between a b =>
    have ht : (natText a ++ ',' :: natText b).takeWhile Char.isDigit = natText a :=
      takeWhile_append_stop (natText_isDigit a) (fun c t h => by cases h; rfl)
    have hd : (natText a ++ ',' :: natText b).dropWhile Char.isDigit = ',' :: natText b :=
      dropWhile_append_stop (natText_isDigit a) (fun c t h => by cases h; rfl)
    simp only [Repeat.body, readRepeat, ht, hd, natText_isEmpty, Bool.false_eq_true, if_false,
      List.all_eq_true.mpr (natText_isDigit b), if_true, readNat_natText]
  | atLeast a =>
    have ht : (natText a ++ [',']).takeWhile Char.isDigit = natText a :=
      takeWhile_append_stop (natText_isDigit a) (fun c t h => by cases h; rfl)
    have hd : (natText a ++ [',']).dropWhile Char.isDigit = [','] :=
      dropWhile_append_stop (natText_isDigit a) (fun c t h => by cases h; rfl)
    simp only [Repeat.body, readRepeat, ht, hd, natText_isEmpty, Bool.false_eq_true, if_false,
      List.isEmpty_nil, if_true, readNat_natText]

/-- No character between the braces of a repeat closes them. -/
theorem Repeat.body_no_close (r : Repeat) : ∀ c ∈ r.body, (c != '}') = true := by
  have hdigit : ∀ n, ∀ c ∈ natText n, (c != '}') = true :=
    fun n c h => bne_of_class (natText_isDigit n c h) '}' (by decide)
  cases r with
  | exactly a => exact hdigit a
  | between a b =>
    intro c hc
    simp only [Repeat.body, List.mem_append, List.mem_cons] at hc
    rcases hc with h | h | h
    · exact hdigit a c h
    · rw [h]; decide
    · exact hdigit b c h
  | atLeast a =>
    intro c hc
    simp only [Repeat.body, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h
    · exact hdigit a c h
    · rw [h]; decide

/-! ## A bound and a range -/

/-- A character of a printed bound: a digit, a character of a unit, `-` or `∞`. -/
def isBoundChar (c : Char) : Bool := c.isDigit || isUnit c || c == '-' || c == '∞'

theorem intText_chars (v : Int) : ∀ c ∈ intText v, isBoundChar c = true := by
  cases v with
  | ofNat n =>
    intro c hc
    simp only [isBoundChar, natText_isDigit n c hc, Bool.true_or]
  | negSucc n =>
    intro c hc
    simp only [intText, List.mem_cons] at hc
    rcases hc with h | h
    · rw [h]; decide
    · simp only [isBoundChar, natText_isDigit (n + 1) c h, Bool.true_or]

theorem Bound.text_chars (b : Bound) (h : b.wf = true) : ∀ c ∈ b.text, isBoundChar c = true := by
  cases b with
  | negInfinity => decide
  | infinity => decide
  | finite v u =>
    intro c hc
    simp only [Bound.text, List.mem_append] at hc
    rcases hc with hc | hc
    · exact intText_chars v c hc
    · simp only [Bound.wf, List.all_eq_true] at h
      simp only [isBoundChar, h c hc, Bool.true_or, Bool.or_true]

/-- Digits and a unit are read as the number and the unit. -/
theorem readMagnitude_text (n : Nat) (u : String) (hu : u.toList.all isUnit = true) :
    readMagnitude (natText n ++ u.toList) = some (n, u) := by
  have hstop : ∀ c t, u.toList = c :: t → c.isDigit = false := fun c t h =>
    isUnit_not_digit (List.all_eq_true.mp hu c (h ▸ List.mem_cons_self))
  simp only [readMagnitude, takeWhile_append_stop (natText_isDigit n) hstop,
    dropWhile_append_stop (natText_isDigit n) hstop, natText_isEmpty, hu, Bool.not_true,
    Bool.or_self, Bool.false_eq_true, if_false, readNat_natText, String.ofList_toList]

/-- A bound is read from what the printer writes for it. -/
theorem readBound_text (b : Bound) (h : b.wf = true) : readBound b.text = some b := by
  cases b with
  | negInfinity => rfl
  | infinity => rfl
  | finite v u =>
    have hu : u.toList.all isUnit = true := h
    cases v with
    | ofNat n =>
      have hm := readMagnitude_text n u hu
      show readBound (natText n ++ u.toList) = _
      cases hn : natText n with
      | nil => exact absurd hn Nat.toDigits_ne_nil
      | cons d ds =>
        have hd : d.isDigit = true := natText_isDigit n d (hn ▸ List.mem_cons_self)
        rw [hn] at hm
        simp only [List.cons_append] at hm ⊢
        simp only [readBound, hd, if_true, hm, Option.map_some]
    | negSucc n =>
      have hm := readMagnitude_text (n + 1) u hu
      show readBound ('-' :: (natText (n + 1) ++ u.toList)) = _
      cases hn : natText (n + 1) with
      | nil => exact absurd hn Nat.toDigits_ne_nil
      | cons d ds =>
        have hd : d.isDigit = true := natText_isDigit (n + 1) d (hn ▸ List.mem_cons_self)
        have hne : (d == '∞') = false := beq_of_class hd '∞' (by decide)
        rw [hn] at hm
        simp only [List.cons_append] at hm ⊢
        have hlist : ((d :: (ds ++ u.toList)) == ['∞']) = false := by
          simp only [List.cons_beq_cons, hne, Bool.false_and]
        have h1 : ('-' : Char).isDigit = false := by decide
        have h2 : (('-' : Char) == '∞') = false := by decide
        have h3 : (('-' : Char) == '-') = true := by decide
        simp only [readBound, h1, h2, h3, hlist, hm, Bool.false_eq_true, if_false, if_true,
          Option.map_some]
        rfl

/-- The shape of a printed range. -/
theorem Range.text_eq (r : Range) :
    r.text = '[' :: (r.min.text ++ ',' :: (r.max.text ++ [']'])) := by
  simp only [Range.text, List.cons_append, List.append_assoc]

/-- A range is read from what the printer writes for it. -/
theorem readRange_text (r : Range) (h : r.wf = true) : readRange r.text = some r := by
  simp only [Range.wf, Bool.and_eq_true] at h
  have hlo : ∀ c ∈ r.min.text, (c != ',') = true := fun c hc =>
    bne_of_class (Bound.text_chars r.min h.1 c hc) ',' (by decide)
  have hhi : ∀ c ∈ r.max.text, (c != ']') = true := fun c hc =>
    bne_of_class (Bound.text_chars r.max h.2 c hc) ']' (by decide)
  have hstop1 : ∀ c t, (',' :: (r.max.text ++ [']'])) = c :: t → (c != ',') = false :=
    fun c t e => by cases e; decide
  have hstop2 : ∀ c t, [']'] = c :: t → (c != ']') = false := fun c t e => by cases e; decide
  rw [Range.text_eq]
  simp only [readRange, dropWhile_append_stop hlo hstop1, takeWhile_append_stop hlo hstop1,
    dropWhile_append_stop hhi hstop2, takeWhile_append_stop hhi hstop2,
    readBound_text r.min h.1, readBound_text r.max h.2, rangeOf]
  rfl

/-- No character of a printed range is white space or closes the angle brackets. -/
theorem Range.text_chars (r : Range) (h : r.wf = true) :
    ∀ c ∈ r.text, isSpace c = false ∧ (c != '>') = true := by
  simp only [Range.wf, Bool.and_eq_true] at h
  have hb : ∀ c, isBoundChar c = true → isSpace c = false ∧ (c != '>') = true := fun c hc => by
    refine ⟨?_, bne_of_class hc '>' (by decide)⟩
    simp only [isSpace, Bool.or_eq_false_iff]
    exact ⟨⟨⟨⟨beq_of_class hc ' ' (by decide), beq_of_class hc '\t' (by decide)⟩,
      beq_of_class hc '\n' (by decide)⟩, beq_of_class hc '\r' (by decide)⟩,
      beq_of_class hc '\x0c' (by decide)⟩
  intro c hc
  rw [Range.text_eq] at hc
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
  rcases hc with e | hc | e | hc | e
  · rw [e]; decide
  · exact hb c (Bound.text_chars r.min h.1 c hc)
  · rw [e]; decide
  · exact hb c (Bound.text_chars r.max h.2 c hc)
  · rw [e]; decide

/-! ## A name in angle brackets -/

/-- A name is its characters: the first opens one, and each is of `isWord`. -/
theorem name_chars {n : String} (h : isName n = true) :
    ∃ c t, n = String.ofList (c :: t) ∧ isStart c = true ∧ (∀ x ∈ c :: t, isWord x = true) ∧
      isNameChars (c :: t) = true := by
  obtain ⟨c, t, hn, hc, hw⟩ := isNameChars_cons h
  refine ⟨c, t, ?_, hc, hw, ?_⟩
  · rw [← hn, String.ofList_toList]
  · rw [← hn]; exact h

/-- What follows `<` is read to the next `>`. -/
theorem lexAngle_of {content : List Char} (hc : ∀ c ∈ content, (c != '>') = true)
    {t : Lexeme} (ht : readAngle content = some t) (rest : List Char) :
    lexAngle (content ++ '>' :: rest) = some (t, rest) := by
  have hstop : ∀ c u, ('>' :: rest) = c :: u → (c != '>') = false :=
    fun c u e => by cases e; decide
  simp only [lexAngle, dropWhile_append_stop hc hstop, takeWhile_append_stop hc hstop, ht,
    Option.map_some]

/-- A character of a name does not close the angle brackets. -/
theorem word_ne_close {c : Char} (h : isWord c = true) : (c != '>') = true :=
  bne_of_class h '>' (by decide)

theorem readAngle_property {c : Char} {t : List Char} (hname : isNameChars (c :: t) = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) :
    readAngle ('\'' :: (c :: (t ++ ['\'']))) =
      some (.atom (.property (String.ofList (c :: t)))) := by
  have hstop : ∀ x u, ['\''] = x :: u → isWord x = false := fun x u e => by cases e; decide
  have ht : (c :: (t ++ ['\''])).takeWhile isWord = c :: t := takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ ['\''])).dropWhile isWord = ['\''] := dropWhile_append_stop hw hstop
  have hq : (('\'' : Char) == '\'') = true := by decide
  have hl : ((['\''] : List Char) == ['\'']) = true := by decide
  simp only [readAngle, hq, if_true, ht, hd, hname, hl, Bool.and_self]

theorem readAngle_type {c : Char} {t : List Char} (hc : isStart c = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) (hf : ((c :: t) != functionToken) = true) :
    readAngle (c :: t) = some (.atom (.type (String.ofList (c :: t)) none)) := by
  have hq : (c == '\'') = false := beq_of_class hc '\'' (by decide)
  have ht : (c :: t).takeWhile isWord = c :: t := takeWhile_all hw
  have hd : (c :: t).dropWhile isWord = [] := dropWhile_all hw
  have hf' : ((c :: t) == functionToken) = false := by
    simp only [bne, Bool.not_eq_true'] at hf
    exact hf
  simp only [readAngle, hq, hc, ht, hd, hf', Bool.false_eq_true, if_false, Bool.not_true,
    List.filter_nil, List.isEmpty_nil, if_true]

theorem readAngle_functionType {c : Char} {t : List Char} (hc : isStart c = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) :
    readAngle (c :: (t ++ ['(', ')'])) =
      some (.atom (.functionType (String.ofList (c :: t)))) := by
  have hq : (c == '\'') = false := beq_of_class hc '\'' (by decide)
  have hstop : ∀ x u, ['(', ')'] = x :: u → isWord x = false := fun x u e => by cases e; decide
  have ht : (c :: (t ++ ['(', ')'])).takeWhile isWord = c :: t := takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ ['(', ')'])).dropWhile isWord = ['(', ')'] :=
    dropWhile_append_stop hw hstop
  have hfil : (['(', ')'] : List Char).filter (fun x => !isSpace x) = ['(', ')'] := by decide
  have hbeq : ((['(', ')'] : List Char) == ['(', ')']) = true := by decide
  simp only [readAngle, hq, hc, ht, hd, hfil, hbeq, Bool.false_eq_true, if_false, Bool.not_true,
    List.isEmpty_cons, if_true]

theorem readAngle_ranged {c : Char} {t : List Char} (hc : isStart c = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) (r : Range) (hr : r.wf = true) :
    readAngle (c :: (t ++ ' ' :: r.text)) =
      some (.atom (.type (String.ofList (c :: t)) (some r))) := by
  have hq : (c == '\'') = false := beq_of_class hc '\'' (by decide)
  have hstop : ∀ x u, (' ' :: r.text) = x :: u → isWord x = false :=
    fun x u e => by cases e; decide
  have ht : (c :: (t ++ ' ' :: r.text)).takeWhile isWord = c :: t :=
    takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ ' ' :: r.text)).dropWhile isWord = ' ' :: r.text :=
    dropWhile_append_stop hw hstop
  have hsp : isSpace ' ' = true := by decide
  have hfil : (' ' :: r.text).filter (fun x => !isSpace x) = r.text := by
    rw [List.filter_cons, hsp]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    exact List.filter_eq_self.mpr fun x hx => by
      rw [(Range.text_chars r hr x hx).1]
      rfl
  have hne : r.text.isEmpty = false := by rw [Range.text_eq]; rfl
  have hpar : (r.text == ['(', ')']) = false := by
    have h : (('[' : Char) == '(') = false := by decide
    rw [Range.text_eq]
    simp only [List.cons_beq_cons, h, Bool.false_and]
  simp only [readAngle, hq, hc, ht, hd, hfil, hne, hpar, Bool.false_eq_true, if_false,
    Bool.not_true, readRange_text r hr, Option.map_some]

/-! ## One printed lexeme -/

/-- A lexeme the printer writes for a tree with `wf`: an atom and an enclosure the reader can
give, a mark of `&&`, `||` or `|`, and a multiplier other than `#{A,B}`, which is two. -/
def Lexeme.ok : Lexeme → Bool
  | .atom a => a.wf
  | .op c => c != .seq
  | .mult (.hash (some _)) => false
  | .mult _ => true
  | .enter e => e.wf
  | .leave _ => true

/-- After `{`, a text that is the end, a space or a multiplier is no repeat. -/
theorem readRepeat_stops {rest : List Char} (hs : Stops rest) :
    readRepeat (rest.takeWhile (· != '}')) = none := by
  cases rest with
  | nil => rfl
  | cons c u =>
    have hb := hs c u rfl
    have hc : (c != '}') = true := by
      revert hb
      exact (by decide : ∀ c ∈ boundary, (c != '}') = true) c
    have hd : c.isDigit = false := by
      revert hb
      exact (by decide : ∀ c ∈ boundary, c.isDigit = false) c
    simp only [List.takeWhile_cons, hc, if_true, readRepeat, hd, Bool.false_eq_true, if_false,
      List.isEmpty_nil]

theorem lexOne_keyword {c : Char} {t rest : List Char} (hc : isStart c = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) (hs : Stops rest) :
    lexOne (c :: (t ++ rest)) = some (.atom (.keyword (String.ofList (c :: t))), rest) := by
  have hstop := hs.fails isWord (by decide)
  have ht : (c :: (t ++ rest)).takeWhile isWord = c :: t := takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ rest)).dropWhile isWord = rest := dropWhile_append_stop hw hstop
  simp only [lexOne, hc, if_true, lexWord, ht, hd, hs.head_ne '(' (by decide),
    Bool.false_eq_true, if_false]

theorem lexOne_function {c : Char} {t : List Char} (rest : List Char) (hc : isStart c = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) :
    lexOne (c :: (t ++ '(' :: rest)) =
      some (.enter (.function (String.ofList (c :: t))), rest) := by
  have hstop : ∀ x u, ('(' :: rest) = x :: u → isWord x = false :=
    fun x u e => by cases e; decide
  have ht : (c :: (t ++ '(' :: rest)).takeWhile isWord = c :: t := takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ '(' :: rest)).dropWhile isWord = '(' :: rest :=
    dropWhile_append_stop hw hstop
  simp only [lexOne, hc, if_true, lexWord, ht, hd, List.head?_cons, BEq.rfl, List.tail_cons]

theorem lexOne_atKeyword {c : Char} {t rest : List Char} (hname : isNameChars (c :: t) = true)
    (hw : ∀ x ∈ c :: t, isWord x = true) (hs : Stops rest) :
    lexOne ('@' :: (c :: (t ++ rest))) =
      some (.atom (.atKeyword (String.ofList (c :: t))), rest) := by
  have hstop := hs.fails isWord (by decide)
  have ht : (c :: (t ++ rest)).takeWhile isWord = c :: t := takeWhile_append_stop hw hstop
  have hd : (c :: (t ++ rest)).dropWhile isWord = rest := dropWhile_append_stop hw hstop
  have h1 : isStart '@' = false := by decide
  have h2 : (('@' : Char) == '@') = true := by decide
  simp only [lexOne, h1, h2, Bool.false_eq_true, if_false, if_true, lexAt, ht, hd, hname]

/-- After `<`, the text is read by `lexAngle`. -/
theorem lexOne_angle (s : List Char) : lexOne ('<' :: s) = lexAngle s := by
  have h1 : isStart '<' = false := by decide
  have h2 : (('<' : Char) == '@') = false := by decide
  have h3 : (('<' : Char) == '<') = true := by decide
  simp only [lexOne, h1, h2, h3, Bool.false_eq_true, if_false, if_true]

/-- After `{`, the text is read by `lexBrace`. -/
theorem lexOne_brace (s : List Char) : lexOne ('{' :: s) = lexBrace s := by
  have h1 : isStart '{' = false := by decide
  have h2 : (('{' : Char) == '@') = false := by decide
  have h3 : (('{' : Char) == '<') = false := by decide
  have h4 : (('{' : Char) == '\'') = false := by decide
  have h5 : (('{' : Char) == '|') = false := by decide
  have h6 : (('{' : Char) == '&') = false := by decide
  have h7 : (('{' : Char) == '{') = true := by decide
  simp only [lexOne, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, if_false, if_true]

/-- After `|`, the text is read by `lexBar`. -/
theorem lexOne_bar (s : List Char) : lexOne ('|' :: s) = lexBar s := by
  have h1 : isStart '|' = false := by decide
  have h2 : (('|' : Char) == '@') = false := by decide
  have h3 : (('|' : Char) == '<') = false := by decide
  have h4 : (('|' : Char) == '\'') = false := by decide
  have h5 : (('|' : Char) == '|') = true := by decide
  simp only [lexOne, h1, h2, h3, h4, h5, Bool.false_eq_true, if_false, if_true]

/-- After a quote, the text is read by `lexQuoted`. -/
theorem lexOne_quote (s : List Char) : lexOne ('\'' :: s) = lexQuoted s := by
  have h1 : isStart '\'' = false := by decide
  have h2 : (('\'' : Char) == '@') = false := by decide
  have h3 : (('\'' : Char) == '<') = false := by decide
  have h4 : (('\'' : Char) == '\'') = true := by decide
  simp only [lexOne, h1, h2, h3, h4, Bool.false_eq_true, if_false, if_true]

/-- A character that opens no longer lexeme is read by `single`. -/
theorem lexOne_single (c : Char) (s : List Char) (h1 : isStart c = false)
    (h2 : (c == '@') = false) (h3 : (c == '<') = false) (h4 : (c == '\'') = false)
    (h5 : (c == '|') = false) (h6 : (c == '&') = false) (h7 : (c == '{') = false) :
    lexOne (c :: s) = (single c).map fun t => (t, s) := by
  simp only [lexOne, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, if_false]

/-- The reader takes a printed lexeme whole, when what follows it is the end, a space or a
multiplier: that is what `render` writes after a lexeme. -/
theorem lexOne_text (t : Lexeme) (ht : t.ok = true) {rest : List Char} (hs : Stops rest) :
    lexOne (t.text ++ rest) = some (t, rest) := by
  cases t with
  | atom a =>
    cases a with
    | keyword n =>
      obtain ⟨c, u, rfl, hc, hw, _⟩ := name_chars (show isName n = true from ht)
      simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append]
      exact lexOne_keyword hc hw hs
    | atKeyword n =>
      obtain ⟨c, u, rfl, hc, hw, hname⟩ := name_chars (show isName n = true from ht)
      simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append]
      exact lexOne_atKeyword hname hw hs
    | literal c =>
      have h : (c == '/' || c == ',' || c == ':' || c == ';') = true := ht
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((rfl | rfl) | rfl) | rfl <;> rfl
    | quoted q =>
      have hq : ∀ x ∈ q.toList, (x != '\'') = true := List.all_eq_true.mp ht
      have hstop : ∀ x u, ('\'' :: rest) = x :: u → (x != '\'') = false :=
        fun x u e => by cases e; decide
      simp only [Lexeme.text, Atom.text, List.cons_append, List.append_assoc, List.nil_append,
        lexOne_quote, lexQuoted, dropWhile_append_stop hq hstop, takeWhile_append_stop hq hstop,
        String.ofList_toList]
    | type n r =>
      cases r with
      | none =>
        have h : (isName n && n.toList != functionToken) = true := ht
        simp only [Bool.and_eq_true] at h
        obtain ⟨c, u, rfl, hc, hw, _⟩ := name_chars h.1
        have hf := h.2
        simp only [String.toList_ofList] at hf
        simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append,
          List.append_assoc, List.nil_append, lexOne_angle]
        exact lexAngle_of (fun x hx => word_ne_close (hw x hx)) (readAngle_type hc hw hf) rest
      | some r =>
        have h : (isName n && r.wf) = true := ht
        simp only [Bool.and_eq_true] at h
        obtain ⟨c, u, rfl, hc, hw, _⟩ := name_chars h.1
        have hchars : ∀ x ∈ c :: (u ++ ' ' :: r.text), (x != '>') = true := fun x hx => by
          have hx' : x ∈ (c :: u) ++ ' ' :: r.text := hx
          simp only [List.mem_append, List.mem_cons (a := x) (b := ' ')] at hx'
          rcases hx' with hx' | hx' | hx'
          · exact word_ne_close (hw x hx')
          · rw [hx']; decide
          · exact (Range.text_chars r h.2 x hx').2
        have key := lexAngle_of hchars (readAngle_ranged hc hw r h.2) rest
        simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append,
          List.append_assoc, List.nil_append, lexOne_angle]
        simpa only [List.cons_append, List.append_assoc] using key
    | functionType n =>
      obtain ⟨c, u, rfl, hc, hw, _⟩ := name_chars (show isName n = true from ht)
      have hchars : ∀ x ∈ c :: (u ++ ['(', ')']), (x != '>') = true := fun x hx => by
        have hx' : x ∈ (c :: u) ++ ['(', ')'] := hx
        simp only [List.mem_append, List.mem_cons (a := x) (b := '('),
          List.mem_cons (a := x) (b := ')'), List.not_mem_nil, or_false] at hx'
        rcases hx' with hx' | hx' | hx'
        · exact word_ne_close (hw x hx')
        · rw [hx']; decide
        · rw [hx']; decide
      have key := lexAngle_of hchars (readAngle_functionType hc hw) rest
      simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append,
        List.append_assoc, List.nil_append, lexOne_angle]
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using key
    | property n =>
      obtain ⟨c, u, rfl, hc, hw, hname⟩ := name_chars (show isName n = true from ht)
      have hchars : ∀ x ∈ '\'' :: (c :: (u ++ ['\''])), (x != '>') = true := fun x hx => by
        have hx' : x ∈ '\'' :: ((c :: u) ++ ['\'']) := hx
        simp only [List.mem_append, List.mem_cons (a := x) (b := '\''), List.not_mem_nil,
          or_false] at hx'
        rcases hx' with hx' | hx' | hx'
        · rw [hx']; decide
        · exact word_ne_close (hw x hx')
        · rw [hx']; decide
      have key := lexAngle_of hchars (readAngle_property hname hw) rest
      simp only [Lexeme.text, Atom.text, String.toList_ofList, List.cons_append,
        List.append_assoc, List.nil_append, lexOne_angle]
      simpa only [List.cons_append, List.append_assoc, List.nil_append] using key
  | op c =>
    cases c with
    | seq => exact Bool.noConfusion ht
    | all => rfl
    | any => rfl
    | one =>
      simp only [Lexeme.text, List.cons_append, List.nil_append, lexOne_bar, lexBar,
        hs.head_ne '|' (by decide), Bool.false_eq_true, if_false]
  | mult m =>
    cases m with
    | star => rfl
    | plus => rfl
    | opt => rfl
    | req => rfl
    | hash r =>
      cases r with
      | none => rfl
      | some r => exact Bool.noConfusion ht
    | times r =>
      have hstop : ∀ x u, ('}' :: rest) = x :: u → (x != '}') = false :=
        fun x u e => by cases e; decide
      simp only [Lexeme.text, Multiplier.text, List.cons_append, List.append_assoc,
        List.nil_append, lexOne_brace, lexBrace,
        takeWhile_append_stop (Repeat.body_no_close r) hstop,
        dropWhile_append_stop (Repeat.body_no_close r) hstop, readRepeat_body,
        List.head?_cons, BEq.rfl, if_true, List.tail_cons]
  | enter e =>
    cases e with
    | brackets => rfl
    | parens => rfl
    | braces =>
      simp only [Lexeme.text, List.cons_append, List.nil_append, lexOne_brace, lexBrace,
        readRepeat_stops hs]
    | function n =>
      obtain ⟨c, u, rfl, hc, hw, _⟩ := name_chars (show isName n = true from ht)
      simp only [Lexeme.text, String.toList_ofList, List.cons_append, List.append_assoc,
        List.nil_append]
      exact lexOne_function rest hc hw
    | anyFunction =>
      have key := lexAngle_of (content := functionToken) (by decide)
        (t := .enter .anyFunction) (by decide) rest
      simp only [Lexeme.text, List.cons_append, List.append_assoc, List.nil_append,
        lexOne_angle]
      exact key
  | leave c =>
    cases c with
    | square => rfl
    | paren => rfl
    | curly => rfl

/-! ## A rendered list -/

/-- A multiplier opens with a boundary character. -/
theorem Multiplier.text_stops (m : Multiplier) (rest : List Char) : Stops (m.text ++ rest) := by
  intro c t h
  cases m with
  | star => cases h; decide
  | plus => cases h; decide
  | opt => cases h; decide
  | req => cases h; decide
  | times r => cases h; decide
  | hash r =>
    cases r with
    | none => cases h; decide
    | some r => cases h; decide

/-- What `render` writes after a lexeme is the end, a space or a multiplier. -/
theorem stops_gap (ts : List Lexeme) : Stops (gap ts ++ render ts) := by
  cases ts with
  | nil => exact Stops.nil
  | cons u us =>
    cases u with
    | mult m =>
      show Stops ([] ++ (m.text ++ gap us ++ render us))
      rw [List.nil_append, List.append_assoc]
      exact Multiplier.text_stops m _
    | atom a => intro c t h; cases h; decide
    | op o => intro c t h; cases h; decide
    | enter e => intro c t h; cases h; decide
    | leave l => intro c t h; cases h; decide

/-- A space is no lexeme. -/
theorem lexOne_space (s : List Char) : lexOne (' ' :: s) = none := rfl

/-- The lexemes of a rendered list are the list, with fuel for every character. -/
theorem lexGo_render : ∀ (ts : List Lexeme), (∀ t ∈ ts, t.ok = true) →
    ∀ fuel, (render ts).length ≤ fuel → lexGo fuel (render ts) = some ts
  | [], _, fuel, _ => by cases fuel <;> rfl
  | t :: ts, hok, fuel, hfuel => by
    have hone := lexOne_text t (hok t List.mem_cons_self) (stops_gap ts)
    have ih := lexGo_render ts (fun u hu => hok u (List.mem_cons_of_mem t hu))
    have hrender : render (t :: ts) = t.text ++ (gap ts ++ render ts) := by
      simp only [render, List.append_assoc]
    rw [hrender] at hfuel ⊢
    cases htext : t.text with
    | nil =>
      have hnil := lexOne_text t (hok t List.mem_cons_self) Stops.nil
      rw [htext] at hnil
      exact nomatch hnil
    | cons c cs =>
      rw [htext] at hone hfuel
      rw [List.cons_append] at hone
      cases fuel with
      | zero => simp only [List.length_append, List.length_cons] at hfuel; omega
      | succ fuel =>
        have hlen : (gap ts ++ render ts).length ≤ fuel := by
          simp only [List.length_append, List.length_cons] at hfuel ⊢
          omega
        have hrest : lexGo fuel (gap ts ++ render ts) = some ts := by
          cases ts with
          | nil => cases fuel <;> rfl
          | cons u us =>
            cases hm : u.isMult with
            | true =>
              simp only [gap, hm, if_true, List.nil_append] at hlen ⊢
              exact ih fuel hlen
            | false =>
              simp only [gap, hm, Bool.false_eq_true, if_false, List.cons_append,
                List.nil_append, List.length_cons] at hlen ⊢
              cases fuel with
              | zero => omega
              | succ fuel =>
                have hsp : isSpace ' ' = true := by decide
                simp only [lexGo, lexOne_space, hsp, if_true]
                exact ih fuel (by omega)
        show lexGo (fuel + 1) (c :: (cs ++ (gap ts ++ render ts))) = some (t :: ts)
        simp only [lexGo, hone, hrest, Option.map_some]

/-- Cutting a rendered text into lexemes gives the lexemes that were rendered. -/
theorem lex_render (ts : List Lexeme) (hok : ∀ t ∈ ts, t.ok = true) :
    lex (render ts) = some ts :=
  lexGo_render ts hok _ (Nat.le_refl _)

end Whatwg.Css.Values
