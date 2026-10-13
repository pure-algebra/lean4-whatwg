import Whatwg.Css.Syntax.Parse.Step

/-!
# Whatwg.Css.Syntax.Parse.Rule

Owner: the round trip of parsing at one rule, given the round trip of its block (slice K4 of
`docs/CSS-PACKAGE-PLAN.md`; proof graph `CSS-PG-SYNTAX`).

A rule holds rules. The law of a rule therefore rests on the law of its child rules, and this
module proves each step with that law as a hypothesis (`hcore`, and the block it gives). The
module `Whatwg/Css/Syntax/Parse/Laws.lean` closes the circle by recursion on the tree.

- `consumeBlockContents_declarations`: a row of readable declarations in a block is gathered into
  one list, before whatever follows it.
- `consumeBlock_written`: a written block is read back as its declarations and its child rules.
- `consumeAtRule_statement`, `consumeAtRule_blockAt`, `consumeQualifiedRule_written`: a written
  rule is read back.
- `consumeDeclaration_fst_of_prelude`: **in a block, the tokens of a readable qualified rule are
  not a declaration.** `consume a block's contents` reads them as a declaration first; step 8 of
  `consume a declaration` returns nothing, because the value would hold the rule's block beside
  another value, and the tokens are read again as a rule.
- `qualified_head_nested`, `qualified_head_top`: the first token of a readable qualified rule is
  one at which the parser starts a qualified rule.
-/

namespace Whatwg.Css.Syntax

/-! ## Lists -/

/-- Dropping a run from a list stops at an item that is not of the run. -/
theorem dropWhile_append_cons {α : Type} (p : α → Bool) (l : List α) (b : α) (r : List α)
    (hb : p b = false) : (l ++ b :: r).dropWhile p = l.dropWhile p ++ b :: r := by
  induction l with
  | nil => exact List.dropWhile_cons_of_neg (by rw [hb]; exact Bool.false_ne_true)
  | cons a l ih =>
    cases ha : p a with
    | true => rw [List.cons_append, List.dropWhile_cons_of_pos ha, List.dropWhile_cons_of_pos ha, ih]
    | false =>
      have hna : ¬p a = true := by rw [ha]; exact Bool.false_ne_true
      rw [List.cons_append, List.dropWhile_cons_of_neg hna, List.dropWhile_cons_of_neg hna,
        List.cons_append]

/-- A list that holds an item is not empty. -/
theorem isEmpty_append_cons {α : Type} (l : List α) (a : α) (r : List α) :
    (l ++ a :: r).isEmpty = false := by
  cases l <;> rfl

/-- What is not of a run is found after the run. -/
theorem filter_not_dropWhile {α : Type} (p : α → Bool) (l : List α) :
    (l.dropWhile p).filter (fun a => !p a) = l.filter (fun a => !p a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases ha : p a with
    | true =>
      rw [List.dropWhile_cons_of_pos ha, ih,
        List.filter_cons_of_neg (by rw [ha]; exact Bool.false_ne_true)]
    | false => rw [List.dropWhile_cons_of_neg (by rw [ha]; exact Bool.false_ne_true)]

/-- A list that is not all of a run has an item after the run. -/
theorem dropWhile_of_all_false {α : Type} (p : α → Bool) {l : List α} (h : l.all p = false) :
    ∃ c rest, l.dropWhile p = c :: rest ∧ p c = false := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    cases ha : p a with
    | true =>
      rw [List.all_cons, ha, Bool.true_and] at h
      rw [List.dropWhile_cons_of_pos ha]
      exact ih h
    | false =>
      exact ⟨a, l, List.dropWhile_cons_of_neg (by rw [ha]; exact Bool.false_ne_true), ha⟩

/-! ## Component values -/

/-- A block in curly brackets is not white space. -/
theorem Component.not_whitespace_of_curly {B : Component} (h : B.isCurlyBlock = true) :
    B.isWhitespace = false := by
  cases B with
  | token t => cases h
  | function name value => rfl
  | block bracket value => rfl

/-- A component value whose first token is a preserved token is that token. -/
theorem Component.eq_token_of_head {c : Component} {t : Token} (h : c.head = t)
    (ht : t.preserved = true) : c = .token t := by
  cases c with
  | token t' =>
    rw [Component.head] at h
    rw [h]
  | function name value =>
    rw [Component.head] at h
    subst h
    cases ht
  | block bracket value =>
    rw [Component.head] at h
    subst h
    cases bracket <;> cases ht

/-- A row that is readable up to some tokens is readable up to fewer. -/
theorem Component.readableAll_mono {ends ends' : Token → Bool}
    (hsub : ∀ t, ends t = false → ends' t = false) {value : List Component}
    (h : Component.readableAll ends value = true) : Component.readableAll ends' value = true := by
  induction value with
  | nil => rfl
  | cons c rest ih =>
    have hc := Component.readableAll_cons h
    rw [Component.readableAll, hsub _ hc.1, hc.2.1, ih hc.2.2]
    rfl

/-- A token that does not end a prelude does not end a list of component values. -/
theorem endsList_of_endsPrelude {stop : Option Token} {nested : Bool} (t : Token)
    (h : endsPrelude stop nested t = false) : endsList stop nested t = false := by
  rw [endsPrelude, Bool.or_eq_false_iff] at h
  exact h.2

/-! ## Step 6 and step 7 of `consume a declaration`, over a value that holds a block -/

/-- Where a value read backwards ends with `important` and `!`: what it opens with. -/
theorem importantSuffix_eq_some {l between front : List Component}
    (h : importantSuffix l = some (between, front)) :
    ∃ name before c, l = .token (.ident name) :: before ∧
      before.dropWhile Component.isWhitespace = .token (.delim c) :: front := by
  unfold importantSuffix at h
  split at h
  · rename_i name before
    split at h
    · rename_i c front' heq
      split at h
      · cases h
        exact ⟨name, before, c, rfl, heq⟩
      · cases h
    · cases h
  · cases h

/-- Step 6 takes nothing from before a block in curly brackets, nor the block. -/
theorem takeImportant_block (p junk : List Component) {B : Component}
    (hB : B.isCurlyBlock = true) : ∃ junk', (takeImportant (p ++ B :: junk)).1 = p ++ B :: junk' := by
  have hws := Component.not_whitespace_of_curly hB
  have hrev : (p ++ B :: junk).reverse.dropWhile Component.isWhitespace =
      junk.reverse.dropWhile Component.isWhitespace ++ B :: p.reverse := by
    rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact dropWhile_append_cons _ _ _ _ hws
  unfold takeImportant
  rw [hrev]
  cases hs : importantSuffix (junk.reverse.dropWhile Component.isWhitespace ++ B :: p.reverse) with
  | none => exact ⟨junk, rfl⟩
  | some pair =>
    obtain ⟨between, front⟩ := pair
    obtain ⟨name, before, c, hl, hbefore⟩ := importantSuffix_eq_some hs
    cases hJ : junk.reverse.dropWhile Component.isWhitespace with
    | nil =>
      rw [hJ, List.nil_append] at hl
      have hBeq := (List.cons.inj hl).1
      subst hBeq
      cases hB
    | cons j J' =>
      rw [hJ, List.cons_append] at hl
      have hb : before = J' ++ B :: p.reverse := (List.cons.inj hl).2.symm
      subst hb
      rw [dropWhile_append_cons _ _ _ _ hws] at hbefore
      cases hJ' : J'.dropWhile Component.isWhitespace with
      | nil =>
        rw [hJ', List.nil_append] at hbefore
        have hBeq := (List.cons.inj hbefore).1
        subst hBeq
        cases hB
      | cons x xs =>
        rw [hJ', List.cons_append] at hbefore
        have hf : front = xs ++ B :: p.reverse := (List.cons.inj hbefore).2.symm
        subst hf
        exact ⟨xs.reverse ++ (between.reverse ++
            ((p ++ B :: junk).reverse.takeWhile Component.isWhitespace).reverse), by
          simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse,
            List.append_assoc, List.cons_append, List.nil_append]⟩

/-- Step 7 drops nothing from before a component value that is not white space, nor that
value. -/
theorem dropTrailingWhitespace_block (p junk : List Component) {B : Component}
    (hws : B.isWhitespace = false) :
    ∃ junk', dropTrailingWhitespace (p ++ B :: junk) = p ++ B :: junk' := by
  refine ⟨(junk.reverse.dropWhile Component.isWhitespace).reverse, ?_⟩
  unfold dropTrailingWhitespace
  rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
    dropWhile_append_cons _ _ _ _ hws]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse, List.append_assoc,
    List.singleton_append]

/-- A value that holds a block in curly brackets after another value that is not white space is
one that step 8 refuses. -/
theorem blockAmongOthers_of_block {c : Component} (p junk : List Component) {B : Component}
    (hc : c.isWhitespace = false) (hB : B.isCurlyBlock = true) :
    blockAmongOthers (c :: p ++ B :: junk) = true := by
  have hws := Component.not_whitespace_of_curly hB
  have hf : (c :: p ++ B :: junk).filter (fun c => !c.isWhitespace) =
      c :: (p.filter (fun c => !c.isWhitespace) ++ B :: junk.filter (fun c => !c.isWhitespace)) := by
    rw [List.cons_append, List.filter_cons_of_pos (by rw [hc]; rfl), List.filter_append,
      List.filter_cons_of_pos (by rw [hws]; rfl)]
  unfold blockAmongOthers
  rw [hf, List.any_cons, List.any_append, List.any_cons, hB, Bool.true_or, Bool.or_true,
    Bool.or_true, Bool.true_and, decide_eq_true_eq, List.length_cons, List.length_append,
    List.length_cons]
  omega

/-! ## A rule's tokens are not a declaration -/

/-- A declaration starts with an ident token: at any other token nothing is returned. -/
theorem consumeDeclaration_fst_of_head {nested : Bool} {input : List Token} {token : Token}
    (hh : input.head? = some token) (ht : ∀ name, token ≠ .ident name) :
    (consumeDeclaration nested input).1 = none := by
  unfold consumeDeclaration
  split
  · rename_i name rest
    exact absurd (Option.some.inj hh).symm (ht name)
  · rfl

/-- A declaration has a colon after its name: before any other token nothing is returned. -/
theorem consumeDeclaration_fst_of_not_colon {nested : Bool} {input rest : List Token}
    {name : List Char} (hi : input = .ident name :: rest)
    (h : ∀ after, discardWhitespace rest ≠ .colon :: after) :
    (consumeDeclaration nested input).1 = none := by
  unfold consumeDeclaration
  split
  · rename_i name' rest'
    cases hi
    split
    · rename_i afterColon heq
      exact absurd heq (h afterColon)
    · rfl
  · rfl

/-- Step 8 of `consume a declaration`: nothing is returned for a name that is not a custom
property's and a value that holds a block in curly brackets beside another value. -/
theorem consumeDeclaration_fst_of_block {nested : Bool} {input rest afterColon : List Token}
    {name : List Char} (hi : input = .ident name :: rest)
    (hcolon : discardWhitespace rest = .colon :: afterColon)
    (hname : isCustomPropertyName name = false)
    (hvalue : blockAmongOthers (dropTrailingWhitespace (takeImportant
      (consumeListOfComponentValues (some .semicolon) nested
        (discardWhitespace afterColon)).1).1) = true) :
    (consumeDeclaration nested input).1 = none := by
  unfold consumeDeclaration
  split
  · rename_i name' rest'
    cases hi
    split
    · rename_i afterColon' heq
      rw [hcolon] at heq
      cases heq
      exact if_pos ⟨hname, hvalue⟩
    · rfl
  · rfl

/-- **In a block, the tokens of a readable qualified rule are not a declaration.** The prelude
is readable up to a semicolon and a right curly bracket, does not start as a custom property
does, and is not an identifier and a colon alone. Whatever follows the left curly bracket,
`consume a declaration` returns nothing: the tokens do not start with an identifier and a colon,
or the value they would give holds the rule's block beside another value. -/
theorem consumeDeclaration_fst_of_prelude {prelude : List Component}
    (hread : Component.readableAll (endsPrelude (some .semicolon) true) prelude = true)
    (hcustom : startsAsCustomProperty prelude = false) (hlike : declarationLike prelude = false)
    (Y : List Token) :
    (consumeDeclaration true (Component.tokensAll prelude ++ .openCurly :: Y)).1 = none := by
  cases prelude with
  | nil =>
    rw [Component.tokensAll_nil, List.nil_append]
    exact consumeDeclaration_fst_of_head (token := .openCurly) rfl (fun name h => by cases h)
  | cons c p' =>
    have hhead : (Component.tokensAll (c :: p') ++ Token.openCurly :: Y).head? = some c.head := by
      rw [Component.tokensAll_cons, List.append_assoc]
      exact Component.head?_tokens_append c _
    by_cases hident : ∃ name, c = .token (.ident name)
    · obtain ⟨name, rfl⟩ := hident
      have htok : Component.tokensAll (.token (.ident name) :: p') ++ Token.openCurly :: Y =
          .ident name :: (Component.tokensAll p' ++ .openCurly :: Y) := by
        rw [Component.tokensAll_cons, Component.tokens, List.singleton_append, List.cons_append]
      have hdw : discardWhitespace (Component.tokensAll p' ++ Token.openCurly :: Y) =
          Component.tokensAll (p'.dropWhile Component.isWhitespace) ++ .openCurly :: Y :=
        discardWhitespace_tokensAll p' rfl
      cases hp2 : p'.dropWhile Component.isWhitespace with
      | nil =>
        rw [hp2, Component.tokensAll_nil, List.nil_append] at hdw
        exact consumeDeclaration_fst_of_not_colon htok (fun after h => by
          rw [hdw] at h
          cases h)
      | cons c2 p3 =>
        rw [hp2] at hdw
        by_cases hcolon : c2 = .token .colon
        · subst hcolon
          -- the prelude is an identifier, a colon, and more
          have hall : p3.all Component.isWhitespace = false := by
            have hl := hlike
            rw [declarationLike, hp2] at hl
            exact hl
          obtain ⟨c4, p5, hp4, hc4⟩ := dropWhile_of_all_false Component.isWhitespace hall
          have hname : isCustomPropertyName name = false := by
            have hc := hcustom
            have hfilter : (Component.token (.ident name) :: p').filter (fun c => !c.isWhitespace) =
                .token (.ident name) :: .token .colon :: p3.filter (fun c => !c.isWhitespace) := by
              rw [List.filter_cons_of_pos rfl, ← filter_not_dropWhile Component.isWhitespace p', hp2,
                List.filter_cons_of_pos rfl]
            rw [startsAsCustomProperty, hfilter] at hc
            exact hc
          have hrest := Component.readableAll_mono (ends' := endsList (some .semicolon) true)
            endsList_of_endsPrelude hread
          have h3 : Component.readableAll (endsList (some .semicolon) true) p3 = true := by
            have h1 := (Component.readableAll_cons hrest).2.2
            have h2 := Component.readableAll_dropWhile Component.isWhitespace h1
            rw [hp2] at h2
            exact (Component.readableAll_cons h2).2.2
          have h4 : Component.readableAll (endsList (some .semicolon) true) (c4 :: p5) = true := by
            have := Component.readableAll_dropWhile Component.isWhitespace h3
            rw [hp4] at this
            exact this
          have hcolonTokens : discardWhitespace (Component.tokensAll p' ++ Token.openCurly :: Y) =
              .colon :: (Component.tokensAll p3 ++ .openCurly :: Y) := by
            rw [hdw, Component.tokensAll_cons, Component.tokens, List.singleton_append,
              List.cons_append]
          have hafter : discardWhitespace (Component.tokensAll p3 ++ Token.openCurly :: Y) =
              Component.tokensAll (c4 :: p5) ++ .openCurly :: Y := by
            rw [discardWhitespace_tokensAll p3 rfl, hp4]
          have hblock : consumeUntil (endsList (some .semicolon) true) (Token.openCurly :: Y) =
              (.block .curly (consumeUntil (· == Token.closeCurly) Y).1 ::
                (consumeUntil (endsList (some .semicolon) true)
                  ((consumeUntil (· == Token.closeCurly) Y).2.drop 1)).1,
                (consumeUntil (endsList (some .semicolon) true)
                  ((consumeUntil (· == Token.closeCurly) Y).2.drop 1)).2) :=
            consumeUntil_step (c := .block .curly (consumeUntil (· == Token.closeCurly) Y).1)
              (by rw [consumeComponentValue_cons]
                  exact congrArg some (consumeComponentValueSized_opening .curly Y))
              (fun t ht => by
                cases ht
                rfl)
          have hvalue : (consumeListOfComponentValues (some .semicolon) true
              (discardWhitespace (Component.tokensAll p3 ++ Token.openCurly :: Y))).1 =
              (c4 :: p5) ++ .block .curly (consumeUntil (· == Token.closeCurly) Y).1 ::
                (consumeUntil (endsList (some .semicolon) true)
                  ((consumeUntil (· == Token.closeCurly) Y).2.drop 1)).1 := by
            rw [hafter]
            show (consumeUntil (endsList (some .semicolon) true)
              (Component.tokensAll (c4 :: p5) ++ Token.openCurly :: Y)).1 = _
            rw [Component.readAll _ _ h4, hblock]
          refine consumeDeclaration_fst_of_block htok hcolonTokens hname ?_
          rw [hvalue]
          obtain ⟨j1, hj1⟩ := takeImportant_block (c4 :: p5)
            (consumeUntil (endsList (some .semicolon) true)
              ((consumeUntil (· == Token.closeCurly) Y).2.drop 1)).1
            (B := .block .curly (consumeUntil (· == Token.closeCurly) Y).1) rfl
          obtain ⟨j2, hj2⟩ := dropTrailingWhitespace_block (c4 :: p5) j1
            (B := .block .curly (consumeUntil (· == Token.closeCurly) Y).1) rfl
          rw [hj1, hj2]
          exact blockAmongOthers_of_block p5 j2 hc4 rfl
        · refine consumeDeclaration_fst_of_not_colon htok (fun after h => ?_)
          rw [hdw, Component.tokensAll_cons, List.append_assoc] at h
          have hh := Component.head?_tokens_append c2 (Component.tokensAll p3 ++ Token.openCurly :: Y)
          rw [h] at hh
          exact hcolon (Component.eq_token_of_head (Option.some.inj hh).symm rfl)
    · exact consumeDeclaration_fst_of_head hhead
        (fun name h => hident ⟨name, Component.eq_token_of_head h rfl⟩)

/-! ## The first token of a qualified rule -/

/-- In a block, a readable qualified rule opens with a token at which `consume a block's
contents` reads a declaration or a qualified rule. -/
theorem qualified_head_nested {prelude : List Component}
    (hread : Component.readableAll (endsPrelude (some .semicolon) true) prelude = true)
    (hopens : preludeOpens true prelude = true) (W : List Token) :
    ∃ token tail, Component.tokensAll prelude ++ .openCurly :: W = token :: tail ∧
      ¬(token = .whitespace ∨ token = .semicolon) ∧ token ≠ .closeCurly ∧
      token.atKeyword? = none := by
  cases prelude with
  | nil =>
    refine ⟨.openCurly, W, by rw [Component.tokensAll_nil, List.nil_append], ?_, ?_, rfl⟩
    · intro h
      rcases h with h | h <;> cases h
    · intro h
      cases h
  | cons c p =>
    have hhead : (Component.tokensAll (c :: p) ++ Token.openCurly :: W).head? = some c.head := by
      rw [Component.tokensAll_cons, List.append_assoc]
      exact Component.head?_tokens_append c _
    obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
    have hends := (Component.readableAll_cons hread).1
    simp only [endsPrelude, endsList, Option.any_some, Bool.true_and, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at hends
    simp only [preludeOpens, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
      Bool.true_or] at hopens
    refine ⟨c.head, tail, htail, ?_, hends.2.2, hopens.1.2⟩
    intro h
    rcases h with h | h
    · exact Component.head_ne_whitespace hopens.1.1 h
    · exact hends.2.1 h.symm

/-- At the top of a stylesheet, a readable qualified rule opens with a token at which `consume
a stylesheet's contents` reads a qualified rule. -/
theorem qualified_head_top {prelude : List Component}
    (hopens : preludeOpens false prelude = true) (W : List Token) :
    ∃ token tail, Component.tokensAll prelude ++ .openCurly :: W = token :: tail ∧
      ¬(token = .whitespace ∨ token = .cdo ∨ token = .cdc) ∧ token.atKeyword? = none := by
  cases prelude with
  | nil =>
    refine ⟨.openCurly, W, by rw [Component.tokensAll_nil, List.nil_append], ?_, rfl⟩
    intro h
    rcases h with h | h | h <;> cases h
  | cons c p =>
    have hhead : (Component.tokensAll (c :: p) ++ Token.openCurly :: W).head? = some c.head := by
      rw [Component.tokensAll_cons, List.append_assoc]
      exact Component.head?_tokens_append c _
    obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp hhead
    simp only [preludeOpens, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
      Bool.false_or, bne_iff_ne, ne_eq] at hopens
    refine ⟨c.head, tail, htail, ?_, hopens.1.2⟩
    intro h
    rcases h with h | h | h
    · exact Component.head_ne_whitespace hopens.1.1 h
    · exact hopens.2.1 h
    · exact hopens.2.2 h

/-! ## Declarations in a block -/

/-- Where a block's contents end: the end of the input, or a right curly bracket. -/
theorem consumeBlockContents_end {T : List Token} (hT : T = [] ∨ ∃ X, T = .closeCurly :: X) :
    consumeBlockContents T = ([], T) := by
  rcases hT with rfl | ⟨X, rfl⟩
  · exact consumeBlockContents_nil
  · exact consumeBlockContents_closeCurly X

theorem stopsAt_end {T : List Token} (hT : T = [] ∨ ∃ X, T = .closeCurly :: X) :
    stopsAt (endsList (some .semicolon) true) T = true := by
  rcases hT with rfl | ⟨X, rfl⟩ <;> rfl

/-- White space before a block's contents is discarded. -/
theorem consumeBlockContents_replicate (k : Nat) (T : List Token) :
    consumeBlockContents (List.replicate k .whitespace ++ T) = consumeBlockContents T := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, consumeBlockContents_discard _ (Or.inl rfl), ih]

/-- A declaration that is read at the head of a block's contents joins the declarations after
it. -/
theorem consumeBlockContents_of_declaration {input after : List Token} {d : Declaration}
    (hd : consumeDeclaration true input = (some d, after)) {name : List Char} {tail : List Token}
    (hi : input = .ident name :: tail) :
    consumeBlockContents input =
      (Rule.consDeclaration d (consumeBlockContents after).1, (consumeBlockContents after).2) := by
  subst hi
  rw [consumeBlockContents_declaration (fun h => by rcases h with h | h <;> cases h)
    (fun h => by cases h) rfl (congrArg Prod.fst hd), hd]

/-- **A row of readable declarations in a block is gathered, each joining the declarations after
it**, before white space and a list that stops a declaration's value. -/
theorem consumeBlockContents_declarations : ∀ (ds : List Declaration),
    ds.all (Declaration.readable true) = true → ∀ (k : Nat) (rest : List Token),
    stopsAt (endsList (some .semicolon) true) rest = true →
    consumeBlockContents (Declaration.tokensAll ds ++ (List.replicate k .whitespace ++ rest)) =
      (ds.foldr Rule.consDeclaration (consumeBlockContents rest).1, (consumeBlockContents rest).2)
  | [], _, k, rest, _ => by
    rw [Declaration.tokensAll, List.nil_append, consumeBlockContents_replicate]
    rfl
  | [d], h, k, rest, hrest => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [Declaration.tokensAll,
      consumeBlockContents_of_declaration (consumeDeclaration_tokens h.1 k hrest) rfl]
    rfl
  | d :: e :: more, h, k, rest, hrest => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have ih := consumeBlockContents_declarations (e :: more) h.2 k rest hrest
    have hread := consumeDeclaration_tokens h.1 0
      (rest := .semicolon :: .whitespace ::
        (Declaration.tokensAll (e :: more) ++ (List.replicate k .whitespace ++ rest))) rfl
    rw [List.replicate_zero, List.nil_append] at hread
    rw [Declaration.tokensAll, List.append_assoc, List.cons_append, List.cons_append,
      consumeBlockContents_of_declaration hread rfl,
      consumeBlockContents_discard _ (Or.inr rfl), consumeBlockContents_discard _ (Or.inl rfl), ih]
    rfl

/-- Declarations before a rule are one list of declarations before it. -/
theorem foldr_consDeclaration {ds : List Declaration} {items : List Rule} (hds : ds ≠ [])
    (hitems : items.head?.any Rule.isNested = false) :
    ds.foldr Rule.consDeclaration items = .nested ds :: items := by
  induction ds with
  | nil => exact absurd rfl hds
  | cons d rest ih =>
    cases rest with
    | nil =>
      exact Rule.consDeclaration.eq_2 d items fun dd rr e => by
        subst e
        cases hitems
    | cons e more =>
      rw [List.foldr_cons, ih (fun h => by cases h)]
      rfl

theorem Rule.splitBlock_of_not_nested {rs : List Rule}
    (h : rs.head?.any Rule.isNested = false) : Rule.splitBlock rs = ([], rs) :=
  Rule.splitBlock.eq_2 rs fun dd rr e => by
    subst e
    cases h

/-! ## A block, an at-rule, a qualified rule -/

theorem Declaration.tokensAll_isEmpty (ds : List Declaration) :
    (Declaration.tokensAll ds).isEmpty = ds.isEmpty := by
  cases ds with
  | nil => rfl
  | cons d rest => cases rest <;> rfl

/-- **A written block is read back as its declarations and its child rules**, given that its
child rules are read back in a block (`hcore`). The tokens of the block open with a left curly
bracket, and what follows that bracket is read by `consume a block` to the end of the block. -/
theorem consumeBlock_written {ds : List Declaration} {rs : List Rule}
    (hds : ds.all (Declaration.readable true) = true)
    (hhead : rs.head?.any Rule.isNested = false)
    (hcore : ∀ (k : Nat) (T : List Token), (T = [] ∨ ∃ X, T = .closeCurly :: X) →
      consumeBlockContents (Rule.tokensAll rs ++ (List.replicate k .whitespace ++ T)) = (rs, T)) :
    ∃ after, blockTokens (Declaration.tokensAll ds) (Rule.tokensAll rs) = .openCurly :: after ∧
      ∀ X, Rule.splitBlock (consumeBlock (after ++ X)).1 = (ds, rs) ∧
        (consumeBlock (after ++ X)).2 = X := by
  have hrs : (Rule.tokensAll rs).isEmpty = rs.isEmpty := by
    cases hR : Rule.tokensAll rs with
    | nil =>
      have h0 := hcore 0 [] (Or.inl rfl)
      rw [hR, List.replicate_zero, List.nil_append, List.nil_append,
        consumeBlockContents_nil] at h0
      rw [← (Prod.mk.inj h0).1]
      rfl
    | cons t tl =>
      cases rs with
      | nil =>
        rw [Rule.tokensAll] at hR
        cases hR
      | cons r more => rfl
  have h1 : ∀ X, consumeBlockContents (Rule.tokensAll rs ++ Token.whitespace :: Token.closeCurly :: X) =
      (rs, Token.closeCurly :: X) := fun X => hcore 1 (.closeCurly :: X) (Or.inr ⟨X, rfl⟩)
  cases ds with
  | nil =>
    cases rs with
    | nil =>
      refine ⟨[.whitespace, .closeCurly], by rw [Rule.tokensAll]; rfl, fun X => ?_⟩
      rw [consumeBlock_eq]
      show Rule.splitBlock (consumeBlockContents (Token.whitespace :: Token.closeCurly :: X)).1 = _ ∧
        (consumeBlockContents (Token.whitespace :: Token.closeCurly :: X)).2.drop 1 = X
      rw [consumeBlockContents_discard _ (Or.inl rfl), consumeBlockContents_closeCurly]
      exact ⟨rfl, rfl⟩
    | cons r more =>
      refine ⟨.whitespace :: (Rule.tokensAll (r :: more) ++ [.whitespace, .closeCurly]), ?_,
        fun X => ?_⟩
      · unfold blockTokens
        simp only [Declaration.tokensAll_isEmpty, hrs, List.isEmpty_nil, List.isEmpty_cons,
          if_true, Bool.false_eq_true, if_false]
      · rw [consumeBlock_eq]
        show Rule.splitBlock (consumeBlockContents (Token.whitespace ::
            ((Rule.tokensAll (r :: more) ++ [Token.whitespace, Token.closeCurly]) ++ X))).1 = _ ∧
          (consumeBlockContents (Token.whitespace ::
            ((Rule.tokensAll (r :: more) ++ [Token.whitespace, Token.closeCurly]) ++ X))).2.drop 1 = X
        rw [consumeBlockContents_discard _ (Or.inl rfl), List.append_assoc]
        show Rule.splitBlock (consumeBlockContents (Rule.tokensAll (r :: more) ++
            Token.whitespace :: Token.closeCurly :: X)).1 = _ ∧
          (consumeBlockContents (Rule.tokensAll (r :: more) ++
            Token.whitespace :: Token.closeCurly :: X)).2.drop 1 = X
        rw [h1 X]
        exact ⟨Rule.splitBlock_of_not_nested hhead, rfl⟩
  | cons d ds' =>
    have hne : (d :: ds') ≠ [] := fun h => by cases h
    cases rs with
    | nil =>
      refine ⟨.whitespace :: (Declaration.tokensAll (d :: ds') ++ [.whitespace, .closeCurly]), ?_,
        fun X => ?_⟩
      · unfold blockTokens
        rw [Rule.tokensAll]
        simp only [Declaration.tokensAll_isEmpty, List.isEmpty_nil, List.isEmpty_cons,
          if_true, Bool.false_eq_true, if_false]
      · have hdr := consumeBlockContents_declarations (d :: ds') hds 1 (.closeCurly :: X) rfl
        rw [consumeBlockContents_closeCurly, foldr_consDeclaration hne rfl] at hdr
        rw [consumeBlock_eq]
        show Rule.splitBlock (consumeBlockContents (Token.whitespace ::
            ((Declaration.tokensAll (d :: ds') ++ [Token.whitespace, Token.closeCurly]) ++ X))).1 = _ ∧
          (consumeBlockContents (Token.whitespace ::
            ((Declaration.tokensAll (d :: ds') ++ [Token.whitespace, Token.closeCurly]) ++ X))).2.drop 1 = X
        rw [consumeBlockContents_discard _ (Or.inl rfl), List.append_assoc]
        show Rule.splitBlock (consumeBlockContents (Declaration.tokensAll (d :: ds') ++
            (List.replicate 1 Token.whitespace ++ Token.closeCurly :: X))).1 = _ ∧
          (consumeBlockContents (Declaration.tokensAll (d :: ds') ++
            (List.replicate 1 Token.whitespace ++ Token.closeCurly :: X))).2.drop 1 = X
        rw [hdr]
        exact ⟨rfl, rfl⟩
    | cons r more =>
      refine ⟨.whitespace :: ((Declaration.tokensAll (d :: ds') ++ .semicolon :: .whitespace ::
          Rule.tokensAll (r :: more)) ++ [.whitespace, .closeCurly]), ?_, fun X => ?_⟩
      · unfold blockTokens
        simp only [Declaration.tokensAll_isEmpty, hrs, List.isEmpty_cons, Bool.false_eq_true,
          if_false, isEmpty_append_cons]
      · have hdr := consumeBlockContents_declarations (d :: ds') hds 0
          (.semicolon :: .whitespace ::
            (Rule.tokensAll (r :: more) ++ Token.whitespace :: Token.closeCurly :: X)) rfl
        rw [consumeBlockContents_discard _ (Or.inr rfl), consumeBlockContents_discard _ (Or.inl rfl),
          h1 X, foldr_consDeclaration hne hhead, List.replicate_zero, List.nil_append] at hdr
        rw [consumeBlock_eq]
        show Rule.splitBlock (consumeBlockContents (Token.whitespace ::
            (((Declaration.tokensAll (d :: ds') ++ Token.semicolon :: Token.whitespace ::
              Rule.tokensAll (r :: more)) ++ [Token.whitespace, Token.closeCurly]) ++ X))).1 = _ ∧
          (consumeBlockContents (Token.whitespace ::
            (((Declaration.tokensAll (d :: ds') ++ Token.semicolon :: Token.whitespace ::
              Rule.tokensAll (r :: more)) ++ [Token.whitespace, Token.closeCurly]) ++ X))).2.drop 1 = X
        rw [consumeBlockContents_discard _ (Or.inl rfl), List.append_assoc, List.append_assoc]
        show Rule.splitBlock (consumeBlockContents (Declaration.tokensAll (d :: ds') ++
            (Token.semicolon :: Token.whitespace ::
              (Rule.tokensAll (r :: more) ++ Token.whitespace :: Token.closeCurly :: X)))).1 = _ ∧
          (consumeBlockContents (Declaration.tokensAll (d :: ds') ++
            (Token.semicolon :: Token.whitespace ::
              (Rule.tokensAll (r :: more) ++ Token.whitespace :: Token.closeCurly :: X)))).2.drop 1 = X
        rw [hdr]
        exact ⟨rfl, rfl⟩

/-- **A written statement at-rule is read back**: its prelude, and the semicolon that ends
it. -/
theorem consumeAtRule_statement {nested : Bool} {prelude : List Component}
    (h : Component.readableAll (endsPrelude (some .semicolon) nested) prelude = true)
    (name : List Char) (X : List Token) :
    consumeAtRule name nested (Component.tokensAll prelude ++ .semicolon :: X) =
      (.statement name prelude, X) := by
  have hp := consumeUntil_tokensAll h (rest := Token.semicolon :: X) (by cases nested <;> rfl)
  rw [consumeAtRule_eq, hp]
  rfl

/-- **A written block at-rule is read back**, given that its block is. -/
theorem consumeAtRule_blockAt {nested : Bool} {prelude : List Component}
    (h : Component.readableAll (endsPrelude (some .semicolon) nested) prelude = true)
    (name : List Char) {ds : List Declaration} {rs : List Rule} {after : List Token}
    (hblock : ∀ X, Rule.splitBlock (consumeBlock (after ++ X)).1 = (ds, rs) ∧
      (consumeBlock (after ++ X)).2 = X) (X : List Token) :
    consumeAtRule name nested (Component.tokensAll prelude ++ .openCurly :: (after ++ X)) =
      (.blockAt name prelude ds rs, X) := by
  have hp := consumeUntil_tokensAll h (rest := Token.openCurly :: (after ++ X)) rfl
  rw [consumeAtRule_eq, hp]
  show (Rule.blockAt name prelude (Rule.splitBlock (consumeBlock (after ++ X)).1).1
    (Rule.splitBlock (consumeBlock (after ++ X)).1).2, (consumeBlock (after ++ X)).2) = _
  rw [(hblock X).1, (hblock X).2]

/-- **A written qualified rule is read back**, given that its block is. -/
theorem consumeQualifiedRule_written {stop : Option Token} {nested : Bool}
    {prelude : List Component}
    (h : Component.readableAll (endsPrelude stop nested) prelude = true)
    (hcustom : startsAsCustomProperty prelude = false)
    {ds : List Declaration} {rs : List Rule} {after : List Token}
    (hblock : ∀ X, Rule.splitBlock (consumeBlock (after ++ X)).1 = (ds, rs) ∧
      (consumeBlock (after ++ X)).2 = X) (X : List Token) :
    consumeQualifiedRule stop nested (Component.tokensAll prelude ++ .openCurly :: (after ++ X)) =
      (some (.qualified prelude ds rs), X) := by
  have hp := consumeUntil_tokensAll h (rest := Token.openCurly :: (after ++ X)) rfl
  rw [consumeQualifiedRule_eq, hp]
  show (if startsAsCustomProperty prelude = true then _ else
    (some (Rule.qualified prelude (Rule.splitBlock (consumeBlock (after ++ X)).1).1
      (Rule.splitBlock (consumeBlock (after ++ X)).1).2), (consumeBlock (after ++ X)).2)) = _
  rw [if_neg (by rw [hcustom]; exact Bool.false_ne_true), (hblock X).1, (hblock X).2]

end Whatwg.Css.Syntax
