import Whatwg.Css.Syntax.Laws
import Whatwg.Css.Syntax.Parse.Rule

/-!
# Whatwg.Css.Syntax.Parse.Laws

Owner: the round trip of parsing (slice K4 of `docs/CSS-PACKAGE-PLAN.md`; rulings CS-7 and CS-9;
proof graph `CSS-PG-SYNTAX`).

The section `serialization` of CSS Syntax Module Level 3 asks of a writer that what it writes
parses back to what it was given. `Whatwg/Css/Syntax/Laws.lean` proves it at the tokens. This
module proves it at the tree: the parser of `Whatwg/Css/Syntax/Parse.lean` reads back the tree
that `Whatwg/Css/Syntax/Write.lean` wrote.

- `parseStylesheet_tokens`: **parsing the tokens of a readable stylesheet gives the
  stylesheet.**
- `parseStylesheetText_text`: **parsing the text of a stylesheet gives the stylesheet**, where
  it is `Stylesheet.writable`. This joins `tokenize_serialize` and the law above.
- `Rule.read`, `Rule.readAll`, `parseBlockContents_tokensAll`: the same for a rule in a block
  and for the child rules of a block.
- `Rule.read_top`, `consumeStylesheetContents_tokensAll`, `parseRule_tokens`: the same for a
  rule and a row of rules at the top of a stylesheet, and for one rule alone.
- `parseStyleAttributeText_textAll`, `parseComponentValuesText_textAll`: the text of a row of
  declarations and of a row of component values, read back.

The laws at a component value and at a declaration are in `Parse/Component.lean` and
`Parse/Declaration.lean`. Each premise is a test that computes (`Whatwg/Css/Syntax/Readable.lean`).

What is not claimed. The laws are about this parser, a reading of the sealed text; a browser is
not asked. They are about what the package writes: a text that another writer wrote is parsed,
and no law says that writing its tree gives the same text back. The law for
`Stylesheet.lines` is in `Parse/Lines.lean`.
-/

namespace Whatwg.Css.Syntax

/-! ## The tokens of a row of rules -/

theorem Rule.tokensAll_singleton (r : Rule) : Rule.tokensAll [r] = r.tokens := by
  rw [Rule.tokensAll]

theorem Rule.tokensAll_cons_cons (r s : Rule) (rest : List Rule) :
    Rule.tokensAll (r :: s :: rest) = r.tokens ++ (Rule.gap r ++ Rule.tokensAll (s :: rest)) := by
  rw [Rule.tokensAll]

theorem Rule.eq_nested_of_isNested {r : Rule} (h : r.isNested = true) : ∃ ds, r = .nested ds := by
  cases r with
  | nested ds => exact ⟨ds, rfl⟩
  | statement name prelude => cases h
  | blockAt name prelude ds rs => cases h
  | qualified prelude ds rs => cases h

/-- White space stands after a rule that is not a nested declarations rule. -/
theorem Rule.gap_of_not_nested {r : Rule} (h : r.isNested = false) : Rule.gap r = [.whitespace] := by
  cases r with
  | nested ds => cases h
  | statement name prelude => rfl
  | blockAt name prelude ds rs => rfl
  | qualified prelude ds rs => rfl

/-- What the test of a block at-rule holds. -/
theorem Rule.readable_blockAt {nested : Bool} {name : List Char} {prelude : List Component}
    {ds : List Declaration} {rs : List Rule}
    (h : Rule.readable nested (.blockAt name prelude ds rs) = true) :
    Component.readableAll (endsPrelude (some .semicolon) nested) prelude = true ∧
      ds.all (Declaration.readable true) = true ∧ rs.head?.any Rule.isNested = false ∧
      Rule.readableAll rs = true := by
  rw [Rule.readable] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- What the test of a qualified rule holds. -/
theorem Rule.readable_qualified {nested : Bool} {prelude : List Component}
    {ds : List Declaration} {rs : List Rule}
    (h : Rule.readable nested (.qualified prelude ds rs) = true) :
    Component.readableAll (endsPrelude (stopOf nested) nested) prelude = true ∧
      preludeOpens nested prelude = true ∧ startsAsCustomProperty prelude = false ∧
      (nested = true → declarationLike prelude = false) ∧
      ds.all (Declaration.readable true) = true ∧ rs.head?.any Rule.isNested = false ∧
      Rule.readableAll rs = true := by
  rw [Rule.readable] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## The round trip in a block -/

mutual

/-- **A readable rule in a block is read back**, and the contents after it are read on. The
rule is an at-rule or a qualified rule; a nested declarations rule joins what follows it, and
`Rule.readAll` has its law. -/
theorem Rule.read : ∀ (r : Rule), Rule.readable true r = true → r.isNested = false →
    ∀ (Z : List Token), consumeBlockContents (r.tokens ++ Z) =
      (r :: (consumeBlockContents Z).1, (consumeBlockContents Z).2)
  | .statement name prelude, h, _, Z => by
    rw [Rule.readable] at h
    rw [Rule.tokens, List.cons_append, List.append_assoc, List.singleton_append,
      consumeBlockContents_atKeyword, consumeAtRule_statement h name Z]
  | .blockAt name prelude ds rs, h, _, Z => by
    obtain ⟨hprelude, hds, hhead, hrs⟩ := Rule.readable_blockAt h
    obtain ⟨after, hafter, hblock⟩ :=
      consumeBlock_written hds hhead (fun k T hT => Rule.readAll rs hrs k T hT)
    rw [Rule.tokens, hafter, List.cons_append, List.append_assoc, List.cons_append,
      consumeBlockContents_atKeyword, consumeAtRule_blockAt hprelude name hblock Z]
  | .qualified prelude ds rs, h, _, Z => by
    obtain ⟨hprelude, hopens, hcustom, hlike, hds, hhead, hrs⟩ := Rule.readable_qualified h
    obtain ⟨after, hafter, hblock⟩ :=
      consumeBlock_written hds hhead (fun k T hT => Rule.readAll rs hrs k T hT)
    obtain ⟨token, tail, htok, hs, hc, hk⟩ := qualified_head_nested hprelude hopens (after ++ Z)
    have hd := consumeDeclaration_fst_of_prelude hprelude hcustom (hlike rfl) (after ++ Z)
    have hq := consumeQualifiedRule_written (stop := some .semicolon) (nested := true) hprelude
      hcustom hblock Z
    rw [htok] at hd hq
    rw [Rule.tokens, hafter, List.append_assoc, List.cons_append, htok,
      consumeBlockContents_rule hs hc hk hd, hq]
    rfl
  | .nested ds, _, hn, _ => by cases hn

/-- **The child rules of a block are read back**, where they are readable: before white space
and the end of the block, which is a right curly bracket or the end of the input. -/
theorem Rule.readAll : ∀ (rs : List Rule), Rule.readableAll rs = true →
    ∀ (k : Nat) (T : List Token), (T = [] ∨ ∃ X, T = .closeCurly :: X) →
    consumeBlockContents (Rule.tokensAll rs ++ (List.replicate k .whitespace ++ T)) = (rs, T)
  | [], _, k, T, hT => by
    rw [Rule.tokensAll, List.nil_append, consumeBlockContents_replicate,
      consumeBlockContents_end hT]
  | r :: more, h, k, T, hT => by
    rw [Rule.readableAll] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hr, hadj⟩, hmore⟩ := h
    have ih := Rule.readAll more hmore k T hT
    cases hn : r.isNested with
    | false =>
      have hstep := Rule.read r hr hn
      cases more with
      | nil =>
        rw [Rule.tokensAll_singleton, hstep, consumeBlockContents_replicate,
          consumeBlockContents_end hT]
      | cons s rest =>
        rw [Rule.tokensAll_cons_cons, List.append_assoc, List.append_assoc, hstep,
          Rule.gap_of_not_nested hn, List.singleton_append,
          consumeBlockContents_discard _ (Or.inl rfl), ih]
    | true =>
      obtain ⟨ds, rfl⟩ := Rule.eq_nested_of_isNested hn
      rw [Rule.readable] at hr
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.true_and] at hr
      have hne : ds ≠ [] := fun e => by
        subst e
        cases hr.1
      cases more with
      | nil =>
        rw [Rule.tokensAll_singleton, Rule.tokens,
          consumeBlockContents_declarations ds hr.2 k T (stopsAt_end hT),
          consumeBlockContents_end hT, foldr_consDeclaration hne rfl]
      | cons s rest =>
        have hs : (s :: rest).head?.any Rule.isNested = false := hadj
        have hdr := consumeBlockContents_declarations ds hr.2 0
          (.semicolon :: .whitespace ::
            (Rule.tokensAll (s :: rest) ++ (List.replicate k .whitespace ++ T))) rfl
        rw [List.replicate_zero, List.nil_append, consumeBlockContents_discard _ (Or.inr rfl),
          consumeBlockContents_discard _ (Or.inl rfl), ih, foldr_consDeclaration hne hs] at hdr
        rw [Rule.tokensAll_cons_cons, List.append_assoc, List.append_assoc, Rule.tokens, Rule.gap]
        exact hdr

end

/-- **Parsing the tokens of the child rules of a block gives them**, where they are readable.
This is `parse a block's contents` after the writer of `Rule.tokensAll`. -/
theorem parseBlockContents_tokensAll (rs : List Rule) (h : Rule.readableAll rs = true) :
    parseBlockContents (Rule.tokensAll rs) = rs := by
  have hread := Rule.readAll rs h 0 [] (Or.inl rfl)
  rw [List.replicate_zero, List.append_nil, List.append_nil] at hread
  show (consumeBlockContents (Rule.tokensAll rs)).1 = rs
  rw [hread]

/-- **A written block is read back as its declarations and its child rules**, where both are
readable and the first child rule is not a nested declarations rule. -/
theorem consumeBlock_tokens {ds : List Declaration} {rs : List Rule}
    (hds : ds.all (Declaration.readable true) = true)
    (hhead : rs.head?.any Rule.isNested = false) (hrs : Rule.readableAll rs = true) :
    ∃ after, blockTokens (Declaration.tokensAll ds) (Rule.tokensAll rs) = .openCurly :: after ∧
      ∀ X, Rule.splitBlock (consumeBlock (after ++ X)).1 = (ds, rs) ∧
        (consumeBlock (after ++ X)).2 = X :=
  consumeBlock_written hds hhead (Rule.readAll rs hrs)

/-- **A readable qualified rule is read back by `consume a qualified rule`**, in a block with a
semicolon as the stop token and at the top of a stylesheet with none. -/
theorem consumeQualifiedRule_tokens {nested : Bool} {prelude : List Component}
    {ds : List Declaration} {rs : List Rule}
    (h : Rule.readable nested (.qualified prelude ds rs) = true) (X : List Token) :
    consumeQualifiedRule (stopOf nested) nested ((Rule.qualified prelude ds rs).tokens ++ X) =
      (some (.qualified prelude ds rs), X) := by
  obtain ⟨hprelude, _, hcustom, _, hds, hhead, hrs⟩ := Rule.readable_qualified h
  obtain ⟨after, hafter, hblock⟩ := consumeBlock_tokens hds hhead hrs
  rw [Rule.tokens, hafter, List.append_assoc, List.cons_append]
  exact consumeQualifiedRule_written hprelude hcustom hblock X

/-! ## The round trip at the top of a stylesheet -/

/-- At the top of a stylesheet a readable rule is not a nested declarations rule. -/
theorem Rule.not_nested_of_readable_top {r : Rule} (h : r.readable false = true) :
    r.isNested = false := by
  cases r with
  | nested ds =>
    rw [Rule.readable] at h
    cases h
  | statement name prelude => rfl
  | blockAt name prelude ds rs => rfl
  | qualified prelude ds rs => rfl

/-- **A readable rule at the top of a stylesheet is read back**, and the contents after it are
read on. -/
theorem Rule.read_top (r : Rule) (h : r.readable false = true) (Z : List Token) :
    consumeStylesheetContents (r.tokens ++ Z) = r :: consumeStylesheetContents Z := by
  cases r with
  | statement name prelude =>
    rw [Rule.readable] at h
    rw [Rule.tokens, List.cons_append, List.append_assoc, List.singleton_append,
      consumeStylesheetContents_atKeyword, consumeAtRule_statement h name Z]
  | blockAt name prelude ds rs =>
    obtain ⟨hprelude, hds, hhead, hrs⟩ := Rule.readable_blockAt h
    obtain ⟨after, hafter, hblock⟩ := consumeBlock_tokens hds hhead hrs
    rw [Rule.tokens, hafter, List.cons_append, List.append_assoc, List.cons_append,
      consumeStylesheetContents_atKeyword, consumeAtRule_blockAt hprelude name hblock Z]
  | qualified prelude ds rs =>
    obtain ⟨hprelude, hopens, hcustom, _, hds, hhead, hrs⟩ := Rule.readable_qualified h
    obtain ⟨after, hafter, hblock⟩ := consumeBlock_tokens hds hhead hrs
    obtain ⟨token, tail, htok, hs, hk⟩ := qualified_head_top hopens (after ++ Z)
    have hq := consumeQualifiedRule_written (stop := none) (nested := false) hprelude hcustom
      hblock Z
    rw [htok] at hq
    rw [Rule.tokens, hafter, List.append_assoc, List.cons_append, htok,
      consumeStylesheetContents_rule tail hs hk, hq]
    rfl
  | nested ds =>
    rw [Rule.readable] at h
    cases h

/-- **A row of readable rules at the top of a stylesheet is read back.** The tokens are those
of `Rule.tokensAll`: white space between two rules. -/
theorem consumeStylesheetContents_tokensAll : ∀ (rules : List Rule),
    rules.all (Rule.readable false) = true →
    consumeStylesheetContents (Rule.tokensAll rules) = rules
  | [], _ => by rw [Rule.tokensAll, consumeStylesheetContents_nil]
  | [r], h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have hread := Rule.read_top r h.1 []
    rw [List.append_nil, consumeStylesheetContents_nil] at hread
    rw [Rule.tokensAll_singleton, hread]
  | r :: s :: rest, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have ih := consumeStylesheetContents_tokensAll (s :: rest) h.2
    rw [Rule.tokensAll_cons_cons, Rule.read_top r h.1,
      Rule.gap_of_not_nested (Rule.not_nested_of_readable_top h.1), List.singleton_append,
      consumeStylesheetContents_discard _ (Or.inl rfl), ih]

/-- **Parsing the tokens of a readable stylesheet gives the stylesheet.** The round trip that
the section `serialization` of CSS Syntax Module Level 3 requires, at the tree: what
`Stylesheet.tokens` writes, `parseStylesheet` reads back. -/
theorem parseStylesheet_tokens (s : Stylesheet) (h : s.readable = true) :
    parseStylesheet s.tokens = s := by
  show Stylesheet.mk (consumeStylesheetContents (Rule.tokensAll s.rules)) = s
  rw [consumeStylesheetContents_tokensAll s.rules h]

/-- `parse-rule` at an at-keyword token. -/
theorem parseRule_atKeyword (name : List Char) (rest : List Token) :
    parseRule (.atKeyword name :: rest) =
      if (discardWhitespace (consumeAtRule name false rest).2).isEmpty = true then
        some (consumeAtRule name false rest).1
      else none :=
  rfl

/-- `parse-rule` at a token that starts a qualified rule. -/
theorem parseRule_of_qualified {token : Token} (rest : List Token) (hne : token ≠ .whitespace)
    (hk : token.atKeyword? = none) :
    parseRule (token :: rest) =
      if (discardWhitespace (consumeQualifiedRule none false (token :: rest)).2).isEmpty = true then
        (consumeQualifiedRule none false (token :: rest)).1
      else none := by
  unfold parseRule
  rw [discardWhitespace_of_head rfl hne]
  simp only [hk]

/-- **Parsing the tokens of one readable rule gives the rule.** This is `parse a rule` after the
writer of `Rule.tokens`. -/
theorem parseRule_tokens (r : Rule) (h : r.readable false = true) : parseRule r.tokens = some r := by
  cases r with
  | statement name prelude =>
    rw [Rule.readable] at h
    have hread := consumeAtRule_statement h name []
    rw [Rule.tokens, parseRule_atKeyword, hread]
    rfl
  | blockAt name prelude ds rs =>
    obtain ⟨hprelude, hds, hhead, hrs⟩ := Rule.readable_blockAt h
    obtain ⟨after, hafter, hblock⟩ := consumeBlock_tokens hds hhead hrs
    have hread := consumeAtRule_blockAt hprelude name hblock []
    rw [List.append_nil] at hread
    rw [Rule.tokens, hafter, parseRule_atKeyword, hread]
    rfl
  | qualified prelude ds rs =>
    obtain ⟨hprelude, hopens, hcustom, _, hds, hhead, hrs⟩ := Rule.readable_qualified h
    obtain ⟨after, hafter, hblock⟩ := consumeBlock_tokens hds hhead hrs
    obtain ⟨token, tail, htok, hs, hk⟩ := qualified_head_top hopens after
    have hq := consumeQualifiedRule_written (stop := none) (nested := false) hprelude hcustom
      hblock []
    rw [List.append_nil, htok] at hq
    rw [Rule.tokens, hafter, htok, parseRule_of_qualified tail (fun e => hs (Or.inl e)) hk, hq]
    rfl
  | nested ds =>
    rw [Rule.readable] at h
    cases h

/-! ## The round trip through text -/

/-- **The tokens of a text come back from the text**, where they pass `writableText`:
`tokenize_serialize` with the preprocessing of `tokenizeText`. -/
theorem tokenizeText_serialize {tokens : List Token} (h : writableText tokens = true) :
    tokenizeText (String.ofList (serialize tokens)) = tokens := by
  unfold writableText at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold tokenizeText
  rw [String.toList_ofList, h.2, tokenize_serialize_eq tokens h.1.1 h.1.2]

/-- **Parsing the text of a stylesheet gives the stylesheet**, where it is
`Stylesheet.writable`. A caller checks that with `#guard` or `decide`, writes the stylesheet with
`Stylesheet.text`, and holds a proof that the parser of CSS Syntax Module Level 3, as this
package reads it, gives the same stylesheet from the text. -/
theorem parseStylesheetText_text (s : Stylesheet) (h : s.writable = true) :
    parseStylesheetText s.text = s := by
  unfold Stylesheet.writable at h
  rw [Bool.and_eq_true] at h
  show parseStylesheet (tokenizeText (String.ofList (serialize s.tokens))) = s
  rw [tokenizeText_serialize h.1, parseStylesheet_tokens s h.2]

/-- **Parsing the text of a row of declarations gives the row**: what the writer wrote into a
`style` attribute comes back. -/
theorem parseStyleAttributeText_textAll (ds : List Declaration)
    (hw : writableText (Declaration.tokensAll ds) = true)
    (h : ds.all (Declaration.readable false) = true) :
    parseStyleAttributeText (Declaration.textAll ds) = ds := by
  show parseStyleAttribute (tokenizeText (String.ofList (serialize (Declaration.tokensAll ds)))) = ds
  rw [tokenizeText_serialize hw, parseStyleAttribute_tokensAll ds h]

/-- **Parsing the text of a row of component values gives the row.** -/
theorem parseComponentValuesText_textAll (value : List Component)
    (hw : writableText (Component.tokensAll value) = true)
    (h : Component.readableAll (fun _ => false) value = true) :
    parseComponentValuesText (Component.textAll value) = value := by
  show parseComponentValues (tokenizeText (String.ofList (serialize (Component.tokensAll value)))) =
    value
  rw [tokenizeText_serialize hw, parseComponentValues_tokensAll value h]

end Whatwg.Css.Syntax
