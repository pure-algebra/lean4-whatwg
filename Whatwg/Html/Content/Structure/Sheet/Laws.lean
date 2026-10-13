import Whatwg.Html.Content.Structure.Sheet
import Whatwg.Html.Content.Structure.Selector.Laws
import Whatwg.Css.Syntax.Readable.Append
import Whatwg.Css.Syntax.Parse.Lines
import Whatwg.Css.Syntax.Located

/-!
# Whatwg.Html.Content.Structure.Sheet.Laws

Owner: what a typed sheet satisfies (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entry W14 of
`docs/research/2026-10-12-whatwg-requests.md`).

- **No style rule without a fact.** `Sheet.styleRules_stylesheet`: the style rules of the tree
  of a sheet, at any depth, are the rules of `Sheet.sources`, in order. `Sheet.rule_of_source`:
  the rule of a source is the rule under the selector of its facts with typed declarations, or
  the root's rule with definitions. `Sheet.facts_eq_sources`: the facts of a sheet are those of
  its sources. So every qualified rule of the tree draws a fact at least or defines tokens, and
  the type has no third thing.
- **A look's rule.** `Decl.carries_iff`: a declaration names a property that carries a colour
  or a family exactly when it is not a plain one. `Paint.quiet_value`: a paint has no comment in
  its text.
- **Two sheets in a row.** `Sheet.stylesheet_append`, `Sheet.facts_append`,
  `Sheet.sources_append`, `Sheet.located_append`, `Sheet.unused_append`: the tree, the facts,
  the sources, the located declarations and the unused facts of `a ++ b` are those of `a` and
  then those of `b`. `Sheet.text_append`: the text is the two texts with a line break between.
- **A sheet over another vocabulary.** `Sheet.stylesheet_map`: where `f` keeps the place of
  every fact, the tree does not change. `Sheet.stylesheet_inl`, `Sheet.stylesheet_inr`: a sheet
  put into the sum of two vocabularies has the tree it had. `Sheet.facts_map`: its facts are the
  images of its facts.
- **Against pages.** `Sheet.occurs_of_mem_unused`: a fact that `Sheet.unused` answers is shown
  by no tree given, and it is a fact of the sheet (`Sheet.mem_facts_of_mem_unused`).
  `Sheet.mem_undrawn_iff`: a fact is undrawn exactly when it is in the list and no entry draws
  it.
- **The round trip.** `Sheet.parse_text`: the text of a writable sheet parses to its tree, by
  `parseStylesheetText_lines` of `Whatwg/Css/Syntax/Parse/Lines.lean`. `Sheet.writable_append`:
  two sheets in a row are writable exactly when each is, so the premise is checked part by part.

What is not proved. That a sheet whose names are plain is writable: the laws of the selector
give `Writable` of a prelude, and the parser's premise asks more (`Rule.readable`), of the
prelude and of every value. A caller computes `Sheet.writable` of its sheet, by `decide` with
the kernel or in a guard.

`Sheet.parse_text` depends on what the parser's law depends on. The other laws depend on
`propext` and `Quot.sound`, and on `Classical.choice` where a builder takes a `String`.
-/

namespace Whatwg.Html.Content.Structure

open Whatwg.Html (RawNode)
open Whatwg.Css.Syntax

variable {φ ψ : Type} {τ : Kind → Type}

/-! ## A look's rule -/

/-- **A declaration names a property that carries a colour or a family exactly when it is not
a plain one.** So the value of such a property is built from a paint or a family token. -/
theorem Decl.carries_iff (d : Decl τ) : carries d.property = true ↔ d.isPlain = false := by
  cases d with
  | colour property paint known =>
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    show (takesColour property || property == "font-family" || property == "font" ||
      untypedCarriers.contains property || isOddName property.toList) = true
    rw [known]
    rfl
  | line property width style paint known =>
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    have hline : lineProperties.contains property = true := known
    show ((colourProperties.contains property || lineProperties.contains property) ||
      property == "font-family" || property == "font" || untypedCarriers.contains property ||
      isOddName property.toList) = true
    rw [hline, Bool.or_true]
    rfl
  | noLine property known =>
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    have hline : lineProperties.contains property = true := known
    show ((colourProperties.contains property || lineProperties.contains property) ||
      property == "font-family" || property == "font" || untypedCarriers.contains property ||
      isOddName property.toList) = true
    rw [hline, Bool.or_true]
    rfl
  | family face => exact ⟨fun _ => rfl, fun _ => (by decide : carries "font-family" = true)⟩
  | font before face => exact ⟨fun _ => rfl, fun _ => (by decide : carries "font" = true)⟩
  | plain name value free =>
    exact ⟨fun h => Bool.noConfusion (free.symm.trans h), fun h => Bool.noConfusion h⟩

/-- A reference to a token has no comment in its text. -/
theorem Look.quiet_var [Look τ] {kind : Kind} (token : τ kind) :
    (Look.var token).quiet = true :=
  (Component.quiet_var _ []).trans rfl

/-- A share has no comment in its text. -/
theorem Share.quiet_value [Look τ] : ∀ share : Share τ, Value.quiet share.value = true
  | .percent _ => rfl
  | .tone token => by
    show Value.quiet [Component.calc (.mul (.leaf (Look.var token)) (.leaf (.percent 100)))] = true
    rw [Value.quiet_singleton, Component.quiet_calc]
    show ((Look.var token).quiet && (Component.percent 100).quiet) = true
    rw [Look.quiet_var]
    rfl

/-- **A paint has no comment in its text**, whatever the names of its tokens. -/
theorem Paint.quiet_value [Look τ] : ∀ paint : Paint τ, Value.quiet paint.value = true
  | .token colour => (Value.quiet_singleton _).trans (Look.quiet_var colour)
  | .current => rfl
  | .inherit => rfl
  | .clear => rfl
  | .mix a share b => by
    show Value.quiet [Component.call "color-mix" (Value.list
      [[.ident "in", .space, .ident "srgb"], a.value ++ Component.space :: share.value, b.value])] = true
    rw [Value.quiet_singleton, Component.quiet_call, Value.quiet_list]
    show (Value.quiet [.ident "in", .space, .ident "srgb"] &&
      (Value.quiet (a.value ++ Component.space :: share.value) && (Value.quiet b.value && true))) = true
    rw [Value.quiet_append_space, Paint.quiet_value a, Share.quiet_value, Paint.quiet_value b,
      Value.quiet_cons_space]
    rfl

/-! ## Entries in a row -/

/-- The rules of entries in a row are the rule of each. -/
theorem Entry.rules_eq_map [Vocabulary φ] [Look τ] : ∀ entries : List (Entry φ τ),
    Entry.rules entries = entries.map Entry.rule
  | [] => by rw [Entry.rules, List.map_nil]
  | entry :: rest => by rw [Entry.rules, Entry.rules_eq_map rest, List.map_cons]

theorem Entry.rules_append [Vocabulary φ] [Look τ] (a b : List (Entry φ τ)) :
    Entry.rules (a ++ b) = Entry.rules a ++ Entry.rules b := by
  rw [Entry.rules_eq_map, Entry.rules_eq_map, Entry.rules_eq_map, List.map_append]

theorem Entry.factsAll_append (a b : List (Entry φ τ)) :
    Entry.factsAll (a ++ b) = Entry.factsAll a ++ Entry.factsAll b := by
  induction a with
  | nil => rw [List.nil_append, Entry.factsAll, List.nil_append]
  | cons entry rest ih =>
    rw [List.cons_append, Entry.factsAll, Entry.factsAll, ih, List.append_assoc]

theorem Entry.sourcesAll_append [Vocabulary φ] [Look τ] (a b : List (Entry φ τ)) :
    Entry.sourcesAll (a ++ b) = Entry.sourcesAll a ++ Entry.sourcesAll b := by
  induction a with
  | nil => rw [List.nil_append, Entry.sourcesAll, List.nil_append]
  | cons entry rest ih =>
    rw [List.cons_append, Entry.sourcesAll, Entry.sourcesAll, ih, List.append_assoc]

theorem styleRulesAll_append (a b : List Rule) :
    styleRulesAll (a ++ b) = styleRulesAll a ++ styleRulesAll b := by
  induction a with
  | nil => rw [List.nil_append, styleRulesAll, List.nil_append]
  | cons rule rest ih =>
    rw [List.cons_append, styleRulesAll, styleRulesAll, ih, List.append_assoc]

/-! ## No style rule without a fact -/

mutual

/-- The style rules of an entry's rule are the rules of its sources. -/
theorem Entry.styleRules_rule [Vocabulary φ] [Look τ] : ∀ entry : Entry φ τ,
    styleRules entry.rule = entry.sources.map (·.2)
  | .draw fact declarations aspect also => by
    rw [Entry.sources, Entry.rule]
    show styleRules (Rule.qualified _ _ []) = _
    rw [styleRules, styleRulesAll]
    rfl
  | .media query entries => by
    rw [Entry.sources, Entry.rule]
    show styleRules (Rule.blockAt _ _ [] (Entry.rules entries)) = _
    rw [styleRules]
    exact Entry.styleRulesAll_rules entries
  | .face descriptors => by
    rw [Entry.sources, Entry.rule]
    show styleRules (Rule.blockAt _ _ descriptors []) = _
    rw [styleRules, styleRulesAll]
    rfl
  | .define definitions => by
    rw [Entry.sources, Entry.rule]
    show styleRules (Rule.qualified _ _ []) = _
    rw [styleRules, styleRulesAll]
    rfl

/-- The same of entries in a row. -/
theorem Entry.styleRulesAll_rules [Vocabulary φ] [Look τ] : ∀ entries : List (Entry φ τ),
    styleRulesAll (Entry.rules entries) = (Entry.sourcesAll entries).map (·.2)
  | [] => by
    rw [Entry.rules, Entry.sourcesAll, styleRulesAll]
    rfl
  | entry :: rest => by
    rw [Entry.rules, styleRulesAll, Entry.sourcesAll, List.map_append,
      Entry.styleRules_rule entry, Entry.styleRulesAll_rules rest]

end

/-- What the rule of a source is: the rule under the selector of its facts, with typed
declarations; or the root's rule, with definitions. -/
def Source.Rules (τ : Kind → Type) [Vocabulary φ] [Look τ] (source : Source φ) (rule : Rule) :
    Prop :=
  match source with
  | .facts fact also aspect =>
    ∃ declarations : List (Decl τ),
      rule = Css.Rule.style (selectorAll ((fact :: also).map Vocabulary.place) aspect)
        (declarations.map Decl.declaration)
  | .tokens =>
    ∃ definitions : List (Definition τ),
      rule = Css.Rule.style Prelude.root (definitions.map Definition.declaration)

mutual

theorem Entry.rule_of_source [Vocabulary φ] [Look τ] : ∀ (entry : Entry φ τ)
    (pair : Source φ × Rule), pair ∈ entry.sources → Source.Rules τ pair.1 pair.2
  | .draw fact declarations aspect also, pair, h => by
    rw [Entry.sources] at h
    cases List.mem_singleton.mp h
    exact ⟨declarations, by rw [Entry.rule]⟩
  | .media _ entries, pair, h => by
    rw [Entry.sources] at h
    exact Entry.rule_of_sourceAll entries pair h
  | .face _, pair, h => by
    rw [Entry.sources] at h
    exact nomatch h
  | .define definitions, pair, h => by
    rw [Entry.sources] at h
    cases List.mem_singleton.mp h
    exact ⟨definitions, by rw [Entry.rule]⟩

theorem Entry.rule_of_sourceAll [Vocabulary φ] [Look τ] : ∀ (entries : List (Entry φ τ))
    (pair : Source φ × Rule), pair ∈ Entry.sourcesAll entries → Source.Rules τ pair.1 pair.2
  | [], pair, h => by
    rw [Entry.sourcesAll] at h
    exact nomatch h
  | entry :: rest, pair, h => by
    rw [Entry.sourcesAll] at h
    rcases List.mem_append.mp h with h | h
    · exact Entry.rule_of_source entry pair h
    · exact Entry.rule_of_sourceAll rest pair h

end

mutual

theorem Entry.facts_eq_sources [Vocabulary φ] [Look τ] : ∀ entry : Entry φ τ,
    entry.facts = entry.sources.flatMap (·.1.drawn)
  | .draw fact declarations aspect also => by
    rw [Entry.sources, Entry.facts, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  | .media _ entries => by
    rw [Entry.sources, Entry.facts]
    exact Entry.factsAll_eq_sources entries
  | .face _ => by
    rw [Entry.sources, Entry.facts]
    rfl
  | .define definitions => by
    rw [Entry.sources, Entry.facts, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

theorem Entry.factsAll_eq_sources [Vocabulary φ] [Look τ] : ∀ entries : List (Entry φ τ),
    Entry.factsAll entries = (Entry.sourcesAll entries).flatMap (·.1.drawn)
  | [] => by
    rw [Entry.sourcesAll, Entry.factsAll]
    rfl
  | entry :: rest => by
    rw [Entry.sourcesAll, Entry.factsAll, List.flatMap_append, Entry.facts_eq_sources entry,
      Entry.factsAll_eq_sources rest]

end

/-! ## A sheet over another vocabulary -/

mutual

/-- Where a function keeps the place of every fact, an entry over the other vocabulary has the
rule it had. -/
theorem Entry.rule_map [Vocabulary φ] [Vocabulary ψ] [Look τ] (f : φ → ψ)
    (hf : ∀ fact, Vocabulary.place (f fact) = Vocabulary.place fact) : ∀ entry : Entry φ τ,
    (entry.map f).rule = entry.rule
  | .draw fact declarations aspect also => by
    have hplaces : (f fact :: also.map f).map Vocabulary.place =
        (fact :: also).map Vocabulary.place := by
      rw [List.map_cons, List.map_cons, hf, List.map_map]
      exact congrArg (Vocabulary.place fact :: ·) (List.map_congr_left fun x _ => hf x)
    rw [Entry.map, Entry.rule, Entry.rule, hplaces]
  | .media query entries => by
    rw [Entry.map, Entry.rule, Entry.rule, Entry.rules_mapAll f hf entries]
  | .face descriptors => by rw [Entry.map, Entry.rule, Entry.rule]
  | .define definitions => by rw [Entry.map, Entry.rule, Entry.rule]

theorem Entry.rules_mapAll [Vocabulary φ] [Vocabulary ψ] [Look τ] (f : φ → ψ)
    (hf : ∀ fact, Vocabulary.place (f fact) = Vocabulary.place fact) :
    ∀ entries : List (Entry φ τ), Entry.rules (Entry.mapAll f entries) = Entry.rules entries
  | [] => by rw [Entry.mapAll, Entry.rules, Entry.rules]
  | entry :: rest => by
    rw [Entry.mapAll, Entry.rules, Entry.rules, Entry.rule_map f hf entry,
      Entry.rules_mapAll f hf rest]

end

mutual

theorem Entry.facts_map (f : φ → ψ) : ∀ entry : Entry φ τ, (entry.map f).facts = entry.facts.map f
  | .draw fact declarations aspect also => by rw [Entry.map, Entry.facts, Entry.facts, List.map_cons]
  | .media query entries => by
    rw [Entry.map, Entry.facts, Entry.facts, Entry.factsAll_mapAll f entries]
  | .face descriptors => by rw [Entry.map, Entry.facts, Entry.facts, List.map_nil]
  | .define definitions => by rw [Entry.map, Entry.facts, Entry.facts, List.map_nil]

theorem Entry.factsAll_mapAll (f : φ → ψ) : ∀ entries : List (Entry φ τ),
    Entry.factsAll (Entry.mapAll f entries) = (Entry.factsAll entries).map f
  | [] => by rw [Entry.mapAll, Entry.factsAll, Entry.factsAll, List.map_nil]
  | entry :: rest => by
    rw [Entry.mapAll, Entry.factsAll, Entry.factsAll, List.map_append, Entry.facts_map f entry,
      Entry.factsAll_mapAll f rest]

end

/-! ## The text of two rows of lines -/

/-- Two rows of texts joined with a separator are the two joined, with the separator between. -/
theorem intercalate_append (sep : String) : ∀ (xs ys : List String), xs ≠ [] → ys ≠ [] →
    sep.intercalate (xs ++ ys) = sep.intercalate xs ++ sep ++ sep.intercalate ys
  | [], _, h, _ => absurd rfl h
  | [_], [], _, h => absurd rfl h
  | [x], y :: ys, _, _ => by
    rw [List.singleton_append, String.intercalate_cons_cons, String.intercalate_singleton]
  | x :: x' :: xs, ys, _, hy => by
    rw [List.cons_append, List.cons_append, String.intercalate_cons_cons, ← List.cons_append,
      intercalate_append sep (x' :: xs) ys (List.cons_ne_nil _ _) hy,
      String.intercalate_cons_cons]
    simp only [String.append_assoc]

namespace Sheet

/-! ## The laws of a sheet -/

/-- The tree of a sheet has one rule for each entry, in order. -/
theorem rules_stylesheet [Vocabulary φ] [Look τ] (s : Sheet φ τ) :
    s.stylesheet.rules = List.map Entry.rule s :=
  Entry.rules_eq_map s

/-- **The style rules of a sheet's tree, at any depth, are the rules of its sources**: each has
its facts, or defines tokens on the root. -/
theorem styleRules_stylesheet [Vocabulary φ] [Look τ] (s : Sheet φ τ) :
    styleRulesAll s.stylesheet.rules = s.sources.map (·.2) :=
  Entry.styleRulesAll_rules s

/-- **The rule of a source**: the rule under the selector of its facts, or the root's rule. -/
theorem rule_of_source [Vocabulary φ] [Look τ] (s : Sheet φ τ) {pair : Source φ × Rule}
    (h : pair ∈ s.sources) : Source.Rules τ pair.1 pair.2 :=
  Entry.rule_of_sourceAll s pair h

/-- **The facts of a sheet are the facts of its sources.** -/
theorem facts_eq_sources [Vocabulary φ] [Look τ] (s : Sheet φ τ) :
    s.facts = s.sources.flatMap (·.1.drawn) :=
  Entry.factsAll_eq_sources s

/-- **Two sheets in a row: the tree is the two trees in a row.** -/
theorem stylesheet_append [Vocabulary φ] [Look τ] (a b : Sheet φ τ) :
    Sheet.stylesheet (a ++ b) = ⟨a.stylesheet.rules ++ b.stylesheet.rules⟩ :=
  congrArg Stylesheet.mk (Entry.rules_append a b)

/-- Two sheets in a row draw the facts of the first and then those of the second. -/
theorem facts_append (a b : Sheet φ τ) : Sheet.facts (a ++ b) = a.facts ++ b.facts :=
  Entry.factsAll_append a b

theorem sources_append [Vocabulary φ] [Look τ] (a b : Sheet φ τ) :
    Sheet.sources (a ++ b) = a.sources ++ b.sources :=
  Entry.sourcesAll_append a b

/-- The declarations of two sheets in a row, each with the rules it stands under, are those of
the first and then those of the second. -/
theorem located_append [Vocabulary φ] [Look τ] (a b : Sheet φ τ) :
    (Sheet.stylesheet (a ++ b)).located = a.stylesheet.located ++ b.stylesheet.located := by
  rw [stylesheet_append]
  exact Stylesheet.located_append _ _

/-- A sheet with an entry has a line of text. -/
theorem texts_ne_nil [Vocabulary φ] [Look τ] {s : Sheet φ τ} (hs : s ≠ []) :
    s.stylesheet.rules.map Rule.text ≠ [] := by
  cases s with
  | nil => exact absurd rfl hs
  | cons entry rest =>
    intro hnil
    rw [rules_stylesheet, List.map_cons, List.map_cons] at hnil
    exact nomatch hnil

/-- **The text of two sheets in a row is the two texts, with a line break between.** -/
theorem text_append [Vocabulary φ] [Look τ] {a b : Sheet φ τ} (ha : a ≠ []) (hb : b ≠ []) :
    Sheet.text (a ++ b) = a.text ++ "\n" ++ b.text := by
  show "\n".intercalate ((Sheet.stylesheet (a ++ b)).rules.map Rule.text) = _
  rw [stylesheet_append, List.map_append,
    intercalate_append "\n" _ _ (texts_ne_nil ha) (texts_ne_nil hb)]
  rfl

/-- **A sheet over another vocabulary has the tree it had**, where the function keeps the place
of every fact. -/
theorem stylesheet_map [Vocabulary φ] [Vocabulary ψ] [Look τ] (f : φ → ψ)
    (hf : ∀ fact, Vocabulary.place (f fact) = Vocabulary.place fact) (s : Sheet φ τ) :
    (s.map f).stylesheet = s.stylesheet :=
  congrArg Stylesheet.mk (Entry.rules_mapAll f hf s)

/-- **A sheet put into the sum of its vocabulary and another has the tree it had.** -/
theorem stylesheet_inl [Vocabulary φ] [Vocabulary ψ] [Look τ] (s : Sheet φ τ) :
    (s.inl : Sheet (φ ⊕ ψ) τ).stylesheet = s.stylesheet :=
  stylesheet_map Sum.inl (fun _ => rfl) s

/-- The same on the other side of the sum. -/
theorem stylesheet_inr [Vocabulary φ] [Vocabulary ψ] [Look τ] (s : Sheet ψ τ) :
    (s.inr : Sheet (φ ⊕ ψ) τ).stylesheet = s.stylesheet :=
  stylesheet_map Sum.inr (fun _ => rfl) s

/-- A sheet over another vocabulary draws the images of its facts. -/
theorem facts_map (f : φ → ψ) (s : Sheet φ τ) : (s.map f).facts = s.facts.map f :=
  Entry.factsAll_mapAll f s

/-- The unused facts of two sheets in a row are those of the first and then those of the
second. -/
theorem unused_append [Vocabulary φ] (a b : Sheet φ τ) (trees : List RawNode) :
    Sheet.unused (a ++ b) trees = a.unused trees ++ b.unused trees := by
  unfold Sheet.unused Structure.unused
  rw [facts_append, List.filter_append]

/-- A fact that `Sheet.unused` answers is a fact of the sheet. -/
theorem mem_facts_of_mem_unused [Vocabulary φ] {s : Sheet φ τ} {trees : List RawNode} {fact : φ}
    (h : fact ∈ s.unused trees) : fact ∈ s.facts :=
  (List.mem_filter.mp h).1

/-- **A fact that `Sheet.unused` answers is shown by no tree given**: its rule draws nothing on
those pages. -/
theorem occurs_of_mem_unused [Vocabulary φ] {s : Sheet φ τ} {trees : List RawNode} {fact : φ}
    (h : fact ∈ s.unused trees) {tree : RawNode} (htree : tree ∈ trees) :
    occurs (Vocabulary.place fact) tree = false :=
  Structure.occurs_of_mem_unused h htree

/-- **A fact is undrawn exactly when it is in the list and no entry draws it.** -/
theorem mem_undrawn_iff [DecidableEq φ] {all : List φ} {s : Sheet φ τ} {fact : φ} :
    fact ∈ Sheet.undrawn all s ↔ fact ∈ all ∧ fact ∉ s.facts := by
  unfold Sheet.undrawn
  rw [List.mem_filter]
  constructor
  · rintro ⟨hall, hnot⟩
    refine ⟨hall, fun hmem => ?_⟩
    rw [List.contains_iff_mem.mpr hmem] at hnot
    exact Bool.noConfusion hnot
  · rintro ⟨hall, hnot⟩
    refine ⟨hall, ?_⟩
    cases hc : s.facts.contains fact with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hnot

/-- **Two sheets in a row are writable exactly when each is.** -/
theorem writable_append [Vocabulary φ] [Look τ] (a b : Sheet φ τ) :
    Sheet.writable (a ++ b) = (a.writable && b.writable) := by
  show (Sheet.stylesheet (a ++ b)).writableLines = _
  rw [stylesheet_append]
  exact Stylesheet.writableLines_append _ _

/-- **The text of a writable sheet parses to its tree.** A caller that computes
`Sheet.writable` of its sheet holds a proof that the parser of CSS reads back what the sheet
prints. -/
theorem parse_text [Vocabulary φ] [Look τ] (s : Sheet φ τ) (h : s.writable = true) :
    parseStylesheetText s.text = s.stylesheet :=
  parseStylesheetText_lines s.stylesheet h

end Sheet

end Whatwg.Html.Content.Structure
