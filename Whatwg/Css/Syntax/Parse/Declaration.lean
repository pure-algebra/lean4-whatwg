import Whatwg.Css.Syntax.Parse.Component

/-!
# Whatwg.Css.Syntax.Parse.Declaration

Owner: the round trip of parsing at declarations (slice K4 of `docs/CSS-PACKAGE-PLAN.md`; proof
graph `CSS-PG-SYNTAX`).

- `consumeDeclaration_tokens`: **consuming the tokens of a readable declaration gives the
  declaration**, before white space and a token that ends its value.
- `parseDeclaration_tokens`: parsing the tokens of a readable declaration gives it.
- `consumeStyleAttribute_tokensAll`, `parseStyleAttribute_tokensAll`: **parsing a row of readable
  declarations gives the row.** This is what a `style` attribute holds.

How it is built. The writer puts white space after the colon, and ` !important` after the value
of a flagged declaration; white space may follow before the token that ends the value. The
parser gathers all of it as the value. `takeImportant_written` and
`takeImportant_append_whitespace` say what step 6 of `consume a declaration` then takes, and
`dropTrailingWhitespace_append_whitespace` what step 7 drops.
-/

namespace Whatwg.Css.Syntax

/-! ## White space in a row -/

/-- A component value that is white space is the whitespace token. -/
theorem Component.eq_whitespace {c : Component} (h : c.isWhitespace = true) :
    c = .token .whitespace :=
  Decidable.byContradiction fun hc => by
    rw [Component.isWhitespace.eq_2 c hc] at h
    cases h

theorem Component.tokensAll_replicate_whitespace (k : Nat) :
    Component.tokensAll (List.replicate k (.token .whitespace)) =
      List.replicate k .whitespace := by
  induction k with
  | zero => exact Component.tokensAll_nil
  | succ k ih =>
    rw [List.replicate_succ, Component.tokensAll_cons, ih, Component.tokens,
      List.singleton_append, List.replicate_succ]

theorem mem_replicate_whitespace {k : Nat} (c : Component)
    (h : c ∈ List.replicate k (Component.token .whitespace)) : c.isWhitespace = true := by
  rw [(List.mem_replicate.mp h).2]
  rfl

theorem dropWhile_replicate_whitespace (k : Nat) :
    (List.replicate k (Component.token .whitespace)).dropWhile Component.isWhitespace = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.dropWhile_cons_of_pos rfl, ih]

/-- "Discard whitespace" over the tokens of a row drops the white space the row opens with. -/
theorem discardWhitespace_tokensAll (value : List Component) {rest : List Token}
    (hrest : discardWhitespace rest = rest) :
    discardWhitespace (Component.tokensAll value ++ rest) =
      Component.tokensAll (value.dropWhile Component.isWhitespace) ++ rest := by
  induction value with
  | nil =>
    rw [Component.tokensAll_nil, List.nil_append, List.dropWhile_nil, Component.tokensAll_nil,
      List.nil_append, hrest]
  | cons c more ih =>
    cases hc : c.isWhitespace with
    | true =>
      have hw := Component.eq_whitespace hc
      subst hw
      rw [List.dropWhile_cons_of_pos hc, Component.tokensAll_cons, Component.tokens,
        List.singleton_append, List.cons_append]
      exact ih
    | false =>
      rw [List.dropWhile_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)]
      exact discardWhitespace_of_head
        (by rw [Component.tokensAll_cons, List.append_assoc]
            exact Component.head?_tokens_append c _)
        (Component.head_ne_whitespace hc)

/-- A token that ends the value of a declaration is not white space. -/
theorem discardWhitespace_of_stopsAt {nested : Bool} {rest : List Token}
    (h : stopsAt (endsList (some .semicolon) nested) rest = true) :
    discardWhitespace rest = rest := by
  cases rest with
  | nil => rfl
  | cons t tl =>
    refine discardWhitespace_of_head rfl fun e => ?_
    subst e
    have h' : endsList (some .semicolon) nested .whitespace = true := h
    cases nested <;> exact absurd h' (by decide)

theorem discardWhitespace_replicate (k : Nat) {rest : List Token}
    (hrest : discardWhitespace rest = rest) :
    discardWhitespace (List.replicate k .whitespace ++ rest) = rest := by
  induction k with
  | zero => exact hrest
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    exact ih

theorem Component.readableAll_dropWhile {ends : Token → Bool} (p : Component → Bool)
    {value : List Component} (h : Component.readableAll ends value = true) :
    Component.readableAll ends (value.dropWhile p) = true := by
  induction value with
  | nil => exact h
  | cons c more ih =>
    cases hp : p c with
    | true =>
      rw [List.dropWhile_cons_of_pos hp]
      exact ih (Component.readableAll_cons h).2.2
    | false =>
      rw [List.dropWhile_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      exact h

theorem Component.readableAll_replicate_whitespace {ends : Token → Bool}
    (h : ends .whitespace = false) (k : Nat) :
    Component.readableAll ends (List.replicate k (.token .whitespace)) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, Component.readableAll, ih, Component.head, h]
    rfl

/-! ## Steps 6 and 7 of `consume a declaration` -/

/-- Step 7 drops the white space that was appended to a value. -/
theorem dropTrailingWhitespace_append_whitespace (value w : List Component)
    (hw : ∀ c ∈ w, c.isWhitespace = true) :
    dropTrailingWhitespace (value ++ w) = dropTrailingWhitespace value := by
  unfold dropTrailingWhitespace
  rw [List.reverse_append,
    List.dropWhile_append_of_pos fun c hc => hw c (List.mem_reverse.mp hc)]

/-- Step 7 leaves a value that does not end with white space. -/
theorem dropTrailingWhitespace_of_getLast {value : List Component}
    (h : value.getLast?.any Component.isWhitespace = false) :
    dropTrailingWhitespace value = value := by
  unfold dropTrailingWhitespace
  have hd : value.reverse.dropWhile Component.isWhitespace = value.reverse := by
    rw [← List.head?_reverse] at h
    cases hr : value.reverse with
    | nil => rfl
    | cons a l =>
      rw [hr] at h
      have ha : a.isWhitespace = false := h
      exact List.dropWhile_cons_of_neg (by rw [ha]; exact Bool.false_ne_true)
  rw [hd, List.reverse_reverse]

/-- Step 6 takes nothing from a value that does not end with `!important`, whatever white space
follows it. -/
theorem takeImportant_append_whitespace {value : List Component}
    (h : (takeImportant value).2 = false) (w : List Component)
    (hw : ∀ c ∈ w, c.isWhitespace = true) : takeImportant (value ++ w) = (value ++ w, false) := by
  have hE : (value ++ w).reverse.dropWhile Component.isWhitespace =
      value.reverse.dropWhile Component.isWhitespace := by
    rw [List.reverse_append,
      List.dropWhile_append_of_pos fun c hc => hw c (List.mem_reverse.mp hc)]
  unfold takeImportant at h ⊢
  rw [hE]
  cases hs : importantSuffix (value.reverse.dropWhile Component.isWhitespace) with
  | none => rfl
  | some p =>
    obtain ⟨between, front⟩ := p
    rw [hs] at h
    cases h

/-- Step 6 takes the `!` and the `important` that the writer put after a value, between white
space, and leaves the white space. -/
theorem takeImportant_written (value p w : List Component)
    (hw : ∀ c ∈ w, c.isWhitespace = true) :
    takeImportant (value ++ (p ++ (.token (.delim '!') :: .token (.ident "important".toList) :: w))) =
      (value ++ (p ++ w), true) := by
  have hrev : (value ++ (p ++ (Component.token (.delim '!') ::
        Component.token (.ident "important".toList) :: w))).reverse =
      w.reverse ++ (Component.token (.ident "important".toList) :: Component.token (.delim '!') ::
        (p.reverse ++ value.reverse)) := by
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]
  have hw' : ∀ c ∈ w.reverse, c.isWhitespace = true := fun c hc => hw c (List.mem_reverse.mp hc)
  unfold takeImportant
  rw [hrev, List.dropWhile_append_of_pos hw', List.dropWhile_cons_of_neg (by decide),
    List.takeWhile_append_of_pos hw', List.takeWhile_cons_of_neg (by decide),
    show importantSuffix (Component.token (.ident "important".toList) ::
        Component.token (.delim '!') :: (p.reverse ++ value.reverse)) =
      some ([], p.reverse ++ value.reverse) from by
        rw [importantSuffix, List.dropWhile_cons_of_neg (by decide),
          List.takeWhile_cons_of_neg (by decide)]
        rfl]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_nil, List.append_nil,
    List.nil_append, List.append_assoc]

/-! ## The round trip at a declaration -/

/-- What the writer puts after the value of a declaration that is flagged: white space, `!` and
`important`. -/
def importantMark (important : Bool) : List Component :=
  if important then
    [.token .whitespace, .token (.delim '!'), .token (.ident "important".toList)]
  else []

theorem Component.tokensAll_importantMark (important : Bool) :
    Component.tokensAll (importantMark important) =
      if important then [Token.whitespace, Token.delim '!', Token.ident "important".toList]
      else [] := by
  cases important <;> rfl

theorem Component.readableAll_importantMark (nested important : Bool) :
    Component.readableAll (endsList (some .semicolon) nested) (importantMark important) = true := by
  cases nested <;> cases important <;> decide

/-- The tokens of a declaration, before white space, are its name, a colon, white space, and the
tokens of one row: the value, the mark of the flag, and the white space. -/
theorem Declaration.tokens_append (d : Declaration) (k : Nat) (rest : List Token) :
    d.tokens ++ (List.replicate k .whitespace ++ rest) =
      .ident d.name :: .colon :: .whitespace ::
        (Component.tokensAll (d.value ++ (importantMark d.important ++
          List.replicate k (.token .whitespace))) ++ rest) := by
  unfold Declaration.tokens
  rw [Component.tokensAll_append, Component.tokensAll_append, Component.tokensAll_importantMark,
    Component.tokensAll_replicate_whitespace]
  simp only [List.cons_append, List.append_assoc]

/-- What steps 6 and 7 make of the row that the parser gathers for a written declaration: the
flag, and the value. -/
theorem takeImportant_row (value : List Component) (important : Bool) (k : Nat)
    (hhead : value.head?.any Component.isWhitespace = false)
    (hlast : value.getLast?.any Component.isWhitespace = false)
    (himp : important = true ∨ (takeImportant value).2 = false) :
    (takeImportant ((value ++ (importantMark important ++
        List.replicate k (Component.token .whitespace))).dropWhile Component.isWhitespace)).2 = important ∧
    dropTrailingWhitespace (takeImportant ((value ++ (importantMark important ++
        List.replicate k (Component.token .whitespace))).dropWhile Component.isWhitespace)).1 = value := by
  have hrep : ∀ c ∈ List.replicate k (Component.token .whitespace), c.isWhitespace = true :=
    fun c hc => mem_replicate_whitespace c hc
  cases important with
  | false =>
    have hno : (takeImportant value).2 = false := by
      rcases himp with h | h
      · cases h
      · exact h
    cases value with
    | nil =>
      have hU : ([] ++ (importantMark false ++ List.replicate k (Component.token .whitespace))).dropWhile
          Component.isWhitespace = [] := dropWhile_replicate_whitespace k
      rw [hU]
      exact ⟨rfl, rfl⟩
    | cons c v =>
      have hc : c.isWhitespace = false := hhead
      have hU : (c :: v ++ (importantMark false ++ List.replicate k (Component.token .whitespace))).dropWhile
          Component.isWhitespace = (c :: v) ++ List.replicate k (Component.token .whitespace) :=
        List.dropWhile_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)
      rw [hU, takeImportant_append_whitespace hno _ hrep]
      exact ⟨rfl, by
        rw [dropTrailingWhitespace_append_whitespace _ _ hrep,
          dropTrailingWhitespace_of_getLast hlast]⟩
  | true =>
    cases value with
    | nil =>
      have hU : ([] ++ (importantMark true ++ List.replicate k (Component.token .whitespace))).dropWhile
          Component.isWhitespace =
          [] ++ ([] ++ (Component.token (.delim '!') :: Component.token (.ident "important".toList) ::
            List.replicate k (Component.token .whitespace))) := by
        show (Component.token .whitespace :: Component.token (.delim '!') ::
          Component.token (.ident "important".toList) ::
            List.replicate k (Component.token .whitespace)).dropWhile Component.isWhitespace = _
        rw [List.dropWhile_cons_of_pos rfl, List.dropWhile_cons_of_neg (by decide)]
        rfl
      rw [hU, takeImportant_written [] [] _ hrep]
      exact ⟨rfl, dropTrailingWhitespace_append_whitespace [] _ hrep⟩
    | cons c v =>
      have hc : c.isWhitespace = false := hhead
      have hU : (c :: v ++ (importantMark true ++ List.replicate k (Component.token .whitespace))).dropWhile
          Component.isWhitespace =
          (c :: v) ++ ([Component.token .whitespace] ++ (Component.token (.delim '!') ::
            Component.token (.ident "important".toList) ::
              List.replicate k (Component.token .whitespace))) :=
        List.dropWhile_cons_of_neg (by rw [hc]; exact Bool.false_ne_true)
      have hone : ∀ x ∈ [Component.token .whitespace], x.isWhitespace = true := fun x hx => by
        rw [List.mem_singleton.mp hx]
        rfl
      rw [hU, takeImportant_written (c :: v) [Component.token .whitespace] _ hrep]
      refine ⟨rfl, ?_⟩
      rw [dropTrailingWhitespace_append_whitespace _ _ (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hone x hx
          · exact hrep x hx),
        dropTrailingWhitespace_of_getLast hlast]

/-- `consume a declaration` at an ident token and a colon, with the steps laid out. -/
theorem consumeDeclaration_of_colon (nested : Bool) (name : List Char) (afterColon : List Token) :
    consumeDeclaration nested (.ident name :: .colon :: afterColon) =
      (if isCustomPropertyName name = false ∧ blockAmongOthers (dropTrailingWhitespace
          (takeImportant (consumeListOfComponentValues (some .semicolon) nested
            (discardWhitespace afterColon)).1).1) = true then none
        else some { name := name,
                    value := dropTrailingWhitespace (takeImportant (consumeListOfComponentValues
                      (some .semicolon) nested (discardWhitespace afterColon)).1).1,
                    important := (takeImportant (consumeListOfComponentValues (some .semicolon)
                      nested (discardWhitespace afterColon)).1).2 },
        (consumeListOfComponentValues (some .semicolon) nested (discardWhitespace afterColon)).2) :=
  rfl

/-- **Consuming the tokens of a readable declaration gives the declaration**, before white space
and a list that stops its value: the end of the input, a semicolon, and in a block a right curly
bracket. The white space is taken and the list is left. -/
theorem consumeDeclaration_tokens {nested : Bool} {d : Declaration}
    (h : d.readable nested = true) (k : Nat) {rest : List Token}
    (hrest : stopsAt (endsList (some .semicolon) nested) rest = true) :
    consumeDeclaration nested (d.tokens ++ (List.replicate k .whitespace ++ rest)) =
      (some d, rest) := by
  unfold Declaration.readable at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hvalue, hhead⟩, hlast⟩, himp⟩, hblock⟩ := h
  have hrow : Component.readableAll (endsList (some .semicolon) nested)
      (d.value ++ (importantMark d.important ++ List.replicate k (.token .whitespace))) = true :=
    Component.readableAll_append hvalue (Component.readableAll_append
      (Component.readableAll_importantMark nested d.important)
      (Component.readableAll_replicate_whitespace (by cases nested <;> rfl) k))
  have hgather : consumeListOfComponentValues (some .semicolon) nested
      (discardWhitespace (.whitespace :: (Component.tokensAll (d.value ++
        (importantMark d.important ++ List.replicate k (.token .whitespace))) ++ rest))) =
      ((d.value ++ (importantMark d.important ++
        List.replicate k (Component.token .whitespace))).dropWhile Component.isWhitespace, rest) := by
    show consumeListOfComponentValues (some .semicolon) nested
      (discardWhitespace (Component.tokensAll (d.value ++
        (importantMark d.important ++ List.replicate k (.token .whitespace))) ++ rest)) = _
    rw [discardWhitespace_tokensAll _ (discardWhitespace_of_stopsAt hrest)]
    exact consumeListOfComponentValues_tokensAll
      (Component.readableAll_dropWhile _ hrow) hrest
  have hsteps := takeImportant_row d.value d.important k hhead hlast himp
  have hnot : ¬(isCustomPropertyName d.name = false ∧ blockAmongOthers d.value = true) := by
    intro hboth
    rcases hblock with hb | hb
    · rw [hboth.1] at hb
      cases hb
    · rw [hboth.2] at hb
      cases hb
  rw [Declaration.tokens_append, consumeDeclaration_of_colon, hgather]
  dsimp only
  rw [hsteps.1, hsteps.2, if_neg hnot]

/-- **Parsing the tokens of a readable declaration gives the declaration.** -/
theorem parseDeclaration_tokens {d : Declaration} (h : d.readable false = true) :
    parseDeclaration d.tokens = some d := by
  have hd := consumeDeclaration_tokens h 0 (rest := []) rfl
  rw [List.replicate_zero, List.append_nil, List.append_nil] at hd
  show (consumeDeclaration false (discardWhitespace d.tokens)).1 = some d
  rw [show discardWhitespace d.tokens = d.tokens from rfl, hd]

/-! ## The round trip at a row of declarations -/

theorem consumeStyleAttribute_nil : consumeStyleAttribute [] = [] := by
  rw [consumeStyleAttribute]

/-- A semicolon or white space before declarations is discarded. -/
theorem consumeStyleAttribute_discard {token : Token} (rest : List Token)
    (h : token = .whitespace ∨ token = .semicolon) :
    consumeStyleAttribute (token :: rest) = consumeStyleAttribute rest := by
  rw [consumeStyleAttribute, if_pos h]

/-- At an ident token a declaration is consumed, and appended where one is returned. -/
theorem consumeStyleAttribute_ident (name : List Char) (rest : List Token) :
    consumeStyleAttribute (.ident name :: rest) =
      (consumeDeclaration false (.ident name :: rest)).1.toList ++
        consumeStyleAttribute (consumeDeclaration false (.ident name :: rest)).2 := by
  rw [consumeStyleAttribute, if_neg (fun h => by rcases h with h | h <;> cases h)]
  rfl

/-- **Parsing a row of readable declarations gives the row.** The tokens are those of
`Declaration.tokensAll`: a semicolon and white space between two declarations. -/
theorem consumeStyleAttribute_tokensAll : ∀ (ds : List Declaration),
    ds.all (Declaration.readable false) = true →
    consumeStyleAttribute (Declaration.tokensAll ds) = ds
  | [], _ => by rw [Declaration.tokensAll, consumeStyleAttribute_nil]
  | [d], h => by
    have hd : d.readable false = true := by
      rw [List.all_cons, Bool.and_eq_true] at h
      exact h.1
    have hread := consumeDeclaration_tokens hd 0 (rest := []) rfl
    rw [List.replicate_zero, List.append_nil, List.append_nil] at hread
    rw [Declaration.tokensAll]
    show consumeStyleAttribute (.ident d.name :: _) = _
    rw [consumeStyleAttribute_ident]
    show (consumeDeclaration false d.tokens).1.toList ++
      consumeStyleAttribute (consumeDeclaration false d.tokens).2 = _
    rw [hread, consumeStyleAttribute_nil]
    rfl
  | d :: e :: rest, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have ih := consumeStyleAttribute_tokensAll (e :: rest) h.2
    have hread := consumeDeclaration_tokens h.1 0
      (rest := .semicolon :: .whitespace :: Declaration.tokensAll (e :: rest)) rfl
    rw [List.replicate_zero, List.nil_append] at hread
    rw [Declaration.tokensAll]
    show consumeStyleAttribute (.ident d.name :: _) = _
    rw [consumeStyleAttribute_ident]
    show (consumeDeclaration false (d.tokens ++ _)).1.toList ++
      consumeStyleAttribute (consumeDeclaration false (d.tokens ++ _)).2 = _
    rw [hread, consumeStyleAttribute_discard _ (Or.inr rfl),
      consumeStyleAttribute_discard _ (Or.inl rfl), ih]
    rfl

/-- **Parsing the tokens of a row of readable declarations gives the row**: what the writer
wrote into a `style` attribute comes back. -/
theorem parseStyleAttribute_tokensAll (ds : List Declaration)
    (h : ds.all (Declaration.readable false) = true) :
    parseStyleAttribute (Declaration.tokensAll ds) = ds :=
  consumeStyleAttribute_tokensAll ds h

end Whatwg.Css.Syntax
