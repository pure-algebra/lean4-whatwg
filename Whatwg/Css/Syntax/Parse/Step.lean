import Whatwg.Css.Syntax.Parse.Declaration

/-!
# Whatwg.Css.Syntax.Parse.Step

Owner: how the algorithms that read rules step (slice K4 of `docs/CSS-PACKAGE-PLAN.md`; proof
graph `CSS-PG-SYNTAX`).

`consumeAtRule`, `consumeQualifiedRule`, `consumeBlock` and `consumeBlockContents` call each
other, and `Whatwg/Css/Syntax/Parse.lean` defines them with the proof that each ends. This module
states each as the standard states it, one equation for each case of its `process`, with no word
of that proof. The laws of `Whatwg/Css/Syntax/Parse/Rule.lean` are built on these equations, and
a caller who reasons about the parser reads them here.

- `consumeBlock_eq`: a block is its contents, and one token discarded.
- `consumeAtRule_eq`, `consumeQualifiedRule_eq`: the prelude, and then the token that ended it.
- `consumeBlockContents_nil`, `_discard`, `_closeCurly`, `_atKeyword`, `_declaration`, `_rule`:
  the five cases of `consume a block's contents`.
- `consumeStylesheetContents_nil`, `_discard`, `_atKeyword`, `_rule`: the cases of `consume a
  stylesheet's contents`.
-/

namespace Whatwg.Css.Syntax

/-- `consume-block`: the contents, and then "discard a token". -/
theorem consumeBlock_eq (input : List Token) :
    consumeBlock input =
      ((consumeBlockContents input).1, (consumeBlockContents input).2.drop 1) := by
  unfold consumeBlock consumeBlockContents
  rw [consumeBlockSized]

/-- `consume-at-rule`: the prelude is gathered, and the token that ended it decides the rest. -/
theorem consumeAtRule_eq (name : List Char) (nested : Bool) (input : List Token) :
    consumeAtRule name nested input =
      match (consumeUntil (endsPrelude (some .semicolon) nested) input).2 with
      | [] => (.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1, [])
      | token :: rest =>
        if token = .semicolon then
          (.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1, rest)
        else if token = .openCurly then
          (.blockAt name (consumeUntil (endsPrelude (some .semicolon) nested) input).1
            (Rule.splitBlock (consumeBlock rest).1).1 (Rule.splitBlock (consumeBlock rest).1).2,
            (consumeBlock rest).2)
        else
          (.statement name (consumeUntil (endsPrelude (some .semicolon) nested) input).1,
            token :: rest) := by
  unfold consumeAtRule consumeBlock
  rw [consumeAtRuleSized]
  split
  · rename_i heq
    simp only [heq]
  · rename_i token rest heq
    simp only [heq]
    split
    · rfl
    · split <;> rfl

/-- `consume-qualified-rule`: the prelude is gathered, and the token that ended it decides the
rest. -/
theorem consumeQualifiedRule_eq (stop : Option Token) (nested : Bool) (input : List Token) :
    consumeQualifiedRule stop nested input =
      match (consumeUntil (endsPrelude stop nested) input).2 with
      | [] => (none, [])
      | token :: rest =>
        if token = .openCurly then
          if startsAsCustomProperty (consumeUntil (endsPrelude stop nested) input).1 = true then
            if nested = true then (none, consumeRemnantsOfBadDeclaration true (token :: rest))
            else (none, (consumeBlock rest).2)
          else
            (some (.qualified (consumeUntil (endsPrelude stop nested) input).1
              (Rule.splitBlock (consumeBlock rest).1).1 (Rule.splitBlock (consumeBlock rest).1).2),
              (consumeBlock rest).2)
        else (none, token :: rest) := by
  unfold consumeQualifiedRule consumeBlock
  rw [consumeQualifiedRuleSized]
  split
  · rename_i heq
    simp only [heq]
  · rename_i token rest heq
    simp only [heq]
    split
    · split
      · split <;> rfl
      · rfl
    · rfl

/-- `consume-block-contents` at the end of the input. -/
theorem consumeBlockContents_nil : consumeBlockContents [] = ([], []) := by
  unfold consumeBlockContents
  rw [consumeBlockContentsSized]

/-- `consume-block-contents` at a whitespace token or a semicolon: discard a token. -/
theorem consumeBlockContents_discard {token : Token} (rest : List Token)
    (h : token = .whitespace ∨ token = .semicolon) :
    consumeBlockContents (token :: rest) = consumeBlockContents rest := by
  unfold consumeBlockContents
  rw [consumeBlockContentsSized, dif_pos h]

/-- `consume-block-contents` at a right curly bracket: return, and the token stays. -/
theorem consumeBlockContents_closeCurly (rest : List Token) :
    consumeBlockContents (.closeCurly :: rest) = ([], .closeCurly :: rest) := by
  unfold consumeBlockContents
  rw [consumeBlockContentsSized, dif_neg (fun h => by rcases h with h | h <;> cases h), dif_pos rfl]

/-- `consume-block-contents` at an at-keyword token: an at-rule, and the contents after it. -/
theorem consumeBlockContents_atKeyword (name : List Char) (rest : List Token) :
    consumeBlockContents (.atKeyword name :: rest) =
      ((consumeAtRule name true rest).1 :: (consumeBlockContents (consumeAtRule name true rest).2).1,
        (consumeBlockContents (consumeAtRule name true rest).2).2) := by
  unfold consumeBlockContents consumeAtRule
  rw [consumeBlockContentsSized, dif_neg (fun h => by rcases h with h | h <;> cases h),
    dif_neg (fun h => by cases h)]
  rfl

/-- `consume-block-contents` at any other token, where a declaration is returned: it joins the
declarations of the contents after it. -/
theorem consumeBlockContents_declaration {token : Token} {rest : List Token} {d : Declaration}
    (hs : ¬(token = .whitespace ∨ token = .semicolon)) (hc : token ≠ .closeCurly)
    (hk : token.atKeyword? = none) (hd : (consumeDeclaration true (token :: rest)).1 = some d) :
    consumeBlockContents (token :: rest) =
      (Rule.consDeclaration d (consumeBlockContents (consumeDeclaration true (token :: rest)).2).1,
        (consumeBlockContents (consumeDeclaration true (token :: rest)).2).2) := by
  unfold consumeBlockContents
  rw [consumeBlockContentsSized, dif_neg hs, dif_neg hc]
  split
  · rename_i heq
    rw [hk] at heq
    cases heq
  · split
    · rename_i d' heq
      rw [hd] at heq
      cases heq
      rfl
    · rename_i heq
      rw [hd] at heq
      cases heq

/-- `consume-block-contents` at any other token, where no declaration is returned: the same
tokens are read as a qualified rule, with a semicolon as the stop token. -/
theorem consumeBlockContents_rule {token : Token} {rest : List Token}
    (hs : ¬(token = .whitespace ∨ token = .semicolon)) (hc : token ≠ .closeCurly)
    (hk : token.atKeyword? = none) (hd : (consumeDeclaration true (token :: rest)).1 = none) :
    consumeBlockContents (token :: rest) =
      ((consumeQualifiedRule (some .semicolon) true (token :: rest)).1.toList ++
          (consumeBlockContents (consumeQualifiedRule (some .semicolon) true (token :: rest)).2).1,
        (consumeBlockContents (consumeQualifiedRule (some .semicolon) true (token :: rest)).2).2) := by
  unfold consumeBlockContents consumeQualifiedRule
  rw [consumeBlockContentsSized, dif_neg hs, dif_neg hc]
  split
  · rename_i heq
    rw [hk] at heq
    cases heq
  · split
    · rename_i d' heq
      rw [hd] at heq
      cases heq
    · rfl

/-- `consume-stylesheet-contents` at the end of the input. -/
theorem consumeStylesheetContents_nil : consumeStylesheetContents [] = [] := by
  rw [consumeStylesheetContents]

/-- `consume-stylesheet-contents` at a whitespace, a CDO or a CDC token: discard a token. -/
theorem consumeStylesheetContents_discard {token : Token} (rest : List Token)
    (h : token = .whitespace ∨ token = .cdo ∨ token = .cdc) :
    consumeStylesheetContents (token :: rest) = consumeStylesheetContents rest := by
  rw [consumeStylesheetContents, if_pos h]

/-- `consume-stylesheet-contents` at an at-keyword token: an at-rule, and the contents after
it. -/
theorem consumeStylesheetContents_atKeyword (name : List Char) (rest : List Token) :
    consumeStylesheetContents (.atKeyword name :: rest) =
      (consumeAtRule name false rest).1 ::
        consumeStylesheetContents (consumeAtRule name false rest).2 := by
  rw [consumeStylesheetContents,
    if_neg (fun h => by rcases h with h | h | h <;> cases h)]
  rfl

/-- `consume-stylesheet-contents` at any other token: a qualified rule where one is returned,
and the contents after it. -/
theorem consumeStylesheetContents_rule {token : Token} (rest : List Token)
    (hs : ¬(token = .whitespace ∨ token = .cdo ∨ token = .cdc)) (hk : token.atKeyword? = none) :
    consumeStylesheetContents (token :: rest) =
      (consumeQualifiedRule none false (token :: rest)).1.toList ++
        consumeStylesheetContents (consumeQualifiedRule none false (token :: rest)).2 := by
  rw [consumeStylesheetContents, if_neg hs]
  split
  · rename_i heq
    rw [hk] at heq
    cases heq
  · rfl

end Whatwg.Css.Syntax
