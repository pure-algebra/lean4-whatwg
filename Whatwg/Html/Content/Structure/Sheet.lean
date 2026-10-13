import Whatwg.Html.Content.Structure.Selector
import Whatwg.Html.Content.Structure.Look
import Whatwg.Html.Node.Css
import Whatwg.Css.Syntax.Readable

/-!
# Whatwg.Html.Content.Structure.Sheet

Owner: a stylesheet as typed data whose every style rule names the structural fact it draws
(slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entry W14 of
`docs/research/2026-10-12-whatwg-requests.md`).

A stylesheet written as text says what each rule draws in a comment, and a comment is checked by
a reader. Here a rule is a value that holds the fact, and its selector is computed from the
fact. A rule that names no fact is not a value of the type.

- `Entry φ τ`: one entry of a sheet over a vocabulary of facts `φ`
  (`Whatwg/Html/Content/Structure.lean`) and a look's tokens `τ`
  (`Whatwg/Html/Content/Structure/Look.lean`). It has four constructors, and each says what it
  is:
  - `draw fact declarations aspect also`: **a style rule**. It draws a fact, and the facts of
    `also` where one block draws several. `aspect` is what the rule adds that no tree holds: a
    state, or a part of the element's box (`Aspect` of the selector's module).
  - `media query entries`: entries under a condition.
  - `face descriptors`: a face (`@font-face`). It draws no fact, and says so by its name. A
    family is written here as a text, since a face is where a family is defined.
  - `define definitions`: tokens defined on the root from other tokens (`:root`). It draws no
    fact either.
- `Sheet φ τ`: entries in a row. Two sheets in a row are `a ++ b`.
- `Sheet.stylesheet`: **the tree of a sheet**, one rule for each entry, by the builders of
  `Whatwg/Html/Node/Css.lean`. `Sheet.text` is its text, one rule a line
  (`Stylesheet.lines`).
- `Sheet.facts`: the facts that a sheet draws, in order, those under a condition too.
  `Sheet.sources`: each style rule of the tree, at any depth, with what it stands for: its
  facts, or the root's tokens.
- `Sheet.unused s trees`: the facts of the sheet that none of the trees shows: rules that draw
  nothing on those pages. `Sheet.undrawn all s`: the facts of a list that no entry draws.
- `Sheet.map f`: the same sheet over another vocabulary. `Sheet.inl` and `Sheet.inr` put a sheet
  over one vocabulary into the sum of two.
- `Sheet.writable`: a test that computes, the premise of the parser's round trip
  (`Stylesheet.writableLines` of `Whatwg/Css/Syntax/Readable.lean`).

```
def sheet : Sheet (Fact ⊕ PageFact) Token :=
  [.define [.colour .quiet (.mix (.token .ink) (.percent 64) (.token .ground))],
   .draw (.inl .tableHead) [.family .label, .line "border-bottom" (Look.var .rule) "solid" (.token .line)],
   .draw (.inr .key) [.colour "color" (.token .ink)] { state := some "hover" },
   .media (Prelude.ofText "print") [.draw (.inl .region) [.plain "overflow" [.ident "visible"]]]]
```

The laws are in `Whatwg/Html/Content/Structure/Sheet/Laws.lean`: every style rule of the tree
has a source (`Sheet.styleRules_stylesheet`), two sheets in a row give the two trees in a row,
a sheet over the sum of two vocabularies has the tree it had, and the text of a writable sheet
parses to its tree (`Sheet.parse_text`).

What this module does not claim.

- That a selector selects the elements of its fact in a browser: see the header of
  `Whatwg/Html/Content/Structure/Selector.lean`.
- That a sheet is writable: `Sheet.writable` computes it for one sheet, and no theorem gives it
  for every sheet whose names are plain.
- Anything of the cascade: two entries may draw one fact, and which declaration a browser
  shows is not read here.
- The descriptors of a face and the query of a condition are the tree's own values, with no
  type of their own.
-/

namespace Whatwg.Html.Content.Structure

open Whatwg.Html (RawNode)
open Whatwg.Css.Syntax (Component Value Prelude Declaration Rule Stylesheet)

/-- **One entry of a sheet** over a vocabulary of facts and a look's tokens. -/
inductive Entry (φ : Type) (τ : Kind → Type) where
  /-- A style rule: the fact it draws, its declarations, what it adds that no tree holds, and
  the other facts that the same block draws. -/
  | draw (fact : φ) (declarations : List (Decl τ)) (aspect : Aspect := {}) (also : List φ := [])
  /-- Entries under a condition: `@media query { … }`. -/
  | media (query : Prelude) (entries : List (Entry φ τ))
  /-- A face: `@font-face { … }`. It draws no fact. -/
  | face (descriptors : List Declaration)
  /-- Tokens defined on the root: `:root { --name: value; … }`. It draws no fact. -/
  | define (definitions : List (Definition τ))

/-- **A sheet**: entries in a row. -/
abbrev Sheet (φ : Type) (τ : Kind → Type) : Type := List (Entry φ τ)

variable {φ ψ : Type} {τ : Kind → Type}

/-! ## The tree of a sheet -/

mutual

/-- The rule of an entry. -/
def Entry.rule [Vocabulary φ] [Look τ] : Entry φ τ → Rule
  | .draw fact declarations aspect also =>
    Css.Rule.style (selectorAll ((fact :: also).map Vocabulary.place) aspect)
      (declarations.map Decl.declaration)
  | .media query entries => Css.Rule.media query (Entry.rules entries)
  | .face descriptors => Css.Rule.at "font-face" [] descriptors []
  | .define definitions => Css.Rule.style Prelude.root (definitions.map Definition.declaration)

/-- The rules of entries in a row: one for each. -/
def Entry.rules [Vocabulary φ] [Look τ] : List (Entry φ τ) → List Rule
  | [] => []
  | entry :: rest => entry.rule :: Entry.rules rest

end

namespace Sheet

/-- **The tree of a sheet**: one rule for each entry. -/
def stylesheet [Vocabulary φ] [Look τ] (s : Sheet φ τ) : Stylesheet := ⟨Entry.rules s⟩

/-- **The text of a sheet**, one rule a line. -/
def text [Vocabulary φ] [Look τ] (s : Sheet φ τ) : String := s.stylesheet.lines

/-- **Whether the parser reads the sheet back from its text**: the tree of the sheet is
`Stylesheet.writableLines`. -/
def writable [Vocabulary φ] [Look τ] (s : Sheet φ τ) : Bool := s.stylesheet.writableLines

end Sheet

/-! ## The facts of a sheet -/

mutual

/-- The facts that an entry draws. -/
def Entry.facts : Entry φ τ → List φ
  | .draw fact _ _ also => fact :: also
  | .media _ entries => Entry.factsAll entries
  | .face _ => []
  | .define _ => []

/-- The facts that entries in a row draw. -/
def Entry.factsAll : List (Entry φ τ) → List φ
  | [] => []
  | entry :: rest => entry.facts ++ Entry.factsAll rest

end

/-- What a style rule of a sheet's tree stands for. -/
inductive Source (φ : Type) where
  /-- The rule draws these facts: one at least. -/
  | facts (fact : φ) (also : List φ) (aspect : Aspect)
  /-- The rule defines tokens on the root. -/
  | tokens

/-- The facts of a source. -/
def Source.drawn : Source φ → List φ
  | .facts fact also _ => fact :: also
  | .tokens => []

mutual

/-- The style rules of an entry's rule, at any depth, each with what it stands for. -/
def Entry.sources [Vocabulary φ] [Look τ] : Entry φ τ → List (Source φ × Rule)
  | .draw fact declarations aspect also =>
    [(.facts fact also aspect, (Entry.draw fact declarations aspect also).rule)]
  | .media _ entries => Entry.sourcesAll entries
  | .face _ => []
  | .define definitions => [(.tokens, (Entry.define (φ := φ) definitions).rule)]

/-- The same of entries in a row. -/
def Entry.sourcesAll [Vocabulary φ] [Look τ] : List (Entry φ τ) → List (Source φ × Rule)
  | [] => []
  | entry :: rest => entry.sources ++ Entry.sourcesAll rest

end

mutual

/-- The style rules of a rule of the tree, at any depth and in the order they stand: the rule
itself where it is a qualified rule, and those inside it. -/
def styleRules : Rule → List Rule
  | .qualified prelude declarations rules =>
    .qualified prelude declarations rules :: styleRulesAll rules
  | .blockAt _ _ _ rules => styleRulesAll rules
  | .statement _ _ => []
  | .nested _ => []

/-- The style rules of rules in a row. -/
def styleRulesAll : List Rule → List Rule
  | [] => []
  | rule :: rest => styleRules rule ++ styleRulesAll rest

end

namespace Sheet

/-- **The facts that a sheet draws**, in the order of its rules, those under a condition too. A
fact that two rules draw stands twice. -/
def facts (s : Sheet φ τ) : List φ := Entry.factsAll s

/-- **Each style rule of the sheet's tree, at any depth, with what it stands for.** -/
def sources [Vocabulary φ] [Look τ] (s : Sheet φ τ) : List (Source φ × Rule) := Entry.sourcesAll s

/-- **The facts of a sheet that none of the trees shows**: its rules that draw nothing on those
pages. -/
def unused [Vocabulary φ] (s : Sheet φ τ) (trees : List RawNode) : List φ :=
  Structure.unused s.facts trees

/-- **The facts of a list that no entry of the sheet draws.** With every fact of a vocabulary
as the list, it is what the sheet leaves undrawn. -/
def undrawn [DecidableEq φ] (all : List φ) (s : Sheet φ τ) : List φ :=
  all.filter fun fact => !s.facts.contains fact

end Sheet

/-! ## A sheet over another vocabulary -/

mutual

/-- The same entry over another vocabulary. -/
def Entry.map (f : φ → ψ) : Entry φ τ → Entry ψ τ
  | .draw fact declarations aspect also => .draw (f fact) declarations aspect (also.map f)
  | .media query entries => .media query (Entry.mapAll f entries)
  | .face descriptors => .face descriptors
  | .define definitions => .define definitions

/-- The same entries over another vocabulary. -/
def Entry.mapAll (f : φ → ψ) : List (Entry φ τ) → List (Entry ψ τ)
  | [] => []
  | entry :: rest => entry.map f :: Entry.mapAll f rest

end

namespace Sheet

/-- **The same sheet over another vocabulary.** -/
def map (f : φ → ψ) (s : Sheet φ τ) : Sheet ψ τ := Entry.mapAll f s

/-- A sheet over a vocabulary, in the sum of that vocabulary and another. -/
def inl (s : Sheet φ τ) : Sheet (φ ⊕ ψ) τ := s.map .inl

/-- A sheet over a vocabulary, in the sum of another and that vocabulary. -/
def inr (s : Sheet ψ τ) : Sheet (φ ⊕ ψ) τ := s.map .inr

end Sheet

end Whatwg.Html.Content.Structure
