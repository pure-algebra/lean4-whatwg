import Whatwg.Css.Syntax.Tree

/-!
# Whatwg.Css.Syntax.Located

Owner: every declaration of a stylesheet with the rules it stands under (slice K4 of
`docs/CSS-PACKAGE-PLAN.md`; entry W5 of `docs/research/2026-10-12-whatwg-requests.md`).

A check on a stylesheet refuses a declaration by where it stands: a literal family is allowed in
`@font-face` and nowhere else. This module gives the fold that such a check needs, over the tree
of `Whatwg/Css/Syntax/Tree.lean`, so that a caller writes no fold of its own.

- `Scope`: a rule that a declaration stands under, an at-rule by its name and prelude or a
  qualified rule by its prelude.
- `Located`: a declaration and its path, the rules above it from the outermost in.
- `Stylesheet.located`: **the declarations of a stylesheet, in the order they stand, each with
  its path.** `Rule.located` and `Rule.locatedAll` are the same for a rule and a row of rules
  under a path.
- `Located.underAtRule`: whether an at-rule of a name is on the path.

Laws. `Rule.locatedAll_append`: the fold of two rows is the two folds, one after the other.
`Rule.located_under`: a path given to the fold is put before every path it gives, and changes
nothing else; so a rule's declarations are located the same wherever the rule stands.

What it gives and does not. A statement at-rule has no declaration. A nested declarations rule
adds no scope: its declarations stand under the rules around it. The fold reads the tree and no
text; it asks nothing of the tree, readable or not. The name of an at-rule is compared code
point for code point.
-/

namespace Whatwg.Css.Syntax

/-- A rule that a declaration stands under. -/
inductive Scope where
  | atRule (name : List Char) (prelude : List Component)
  | qualified (prelude : List Component)
  deriving Inhabited

/-- The name of the at-rule, where the scope is one. -/
def Scope.atRuleName? : Scope → Option (List Char)
  | .atRule name _ => some name
  | .qualified _ => none

/-- A declaration and the rules it stands under, the outermost first. -/
structure Located where
  path : List Scope
  declaration : Declaration
  deriving Inhabited

namespace Located

/-- The same declaration under more rules: `outer` before its path. -/
def under (outer : List Scope) (l : Located) : Located := { l with path := outer ++ l.path }

/-- Whether an at-rule of this name is on the path. -/
def underAtRule (l : Located) (name : String) : Bool :=
  l.path.any fun scope => scope.atRuleName? == some name.toList

end Located

mutual

/-- The declarations of a rule and of the rules inside it, in the order they stand, each with
its path under `path`. -/
def Rule.located (path : List Scope) : Rule → List Located
  | .statement _ _ => []
  | .blockAt name prelude declarations rules =>
    declarations.map (Located.mk (path ++ [.atRule name prelude])) ++
      Rule.locatedAll (path ++ [.atRule name prelude]) rules
  | .qualified prelude declarations rules =>
    declarations.map (Located.mk (path ++ [.qualified prelude])) ++
      Rule.locatedAll (path ++ [.qualified prelude]) rules
  | .nested declarations => declarations.map (Located.mk path)

/-- The declarations of a row of rules, in the order they stand, each with its path under
`path`. -/
def Rule.locatedAll (path : List Scope) : List Rule → List Located
  | [] => []
  | r :: rest => Rule.located path r ++ Rule.locatedAll path rest

end

/-- **The declarations of a stylesheet, in the order they stand, each with the rules it stands
under.** -/
def Stylesheet.located (s : Stylesheet) : List Located := Rule.locatedAll [] s.rules

/-- **The fold of two rows of rules is the two folds, one after the other.** -/
theorem Rule.locatedAll_append (path : List Scope) (a b : List Rule) :
    Rule.locatedAll path (a ++ b) = Rule.locatedAll path a ++ Rule.locatedAll path b := by
  induction a with
  | nil => rw [List.nil_append, Rule.locatedAll, List.nil_append]
  | cons r rest ih =>
    rw [List.cons_append, Rule.locatedAll, Rule.locatedAll, ih, List.append_assoc]

theorem Located.map_under_mk (outer path : List Scope) (declarations : List Declaration) :
    (declarations.map (Located.mk path)).map (Located.under outer) =
      declarations.map (Located.mk (outer ++ path)) := by
  rw [List.map_map]
  rfl

mutual

/-- **A path given to the fold is put before every path it gives, and changes nothing else.** -/
theorem Rule.located_under (outer path : List Scope) : ∀ (r : Rule),
    Rule.located (outer ++ path) r = (Rule.located path r).map (Located.under outer)
  | .statement _ _ => by
    rw [Rule.located, Rule.located]
    rfl
  | .blockAt name prelude declarations rules => by
    rw [Rule.located, Rule.located, List.map_append, Located.map_under_mk, List.append_assoc,
      Rule.locatedAll_under outer (path ++ [Scope.atRule name prelude]) rules]
  | .qualified prelude declarations rules => by
    rw [Rule.located, Rule.located, List.map_append, Located.map_under_mk, List.append_assoc,
      Rule.locatedAll_under outer (path ++ [Scope.qualified prelude]) rules]
  | .nested declarations => by
    rw [Rule.located, Rule.located, Located.map_under_mk]

/-- The same for a row of rules. -/
theorem Rule.locatedAll_under (outer path : List Scope) : ∀ (rules : List Rule),
    Rule.locatedAll (outer ++ path) rules = (Rule.locatedAll path rules).map (Located.under outer)
  | [] => by
    rw [Rule.locatedAll, Rule.locatedAll]
    rfl
  | r :: rest => by
    rw [Rule.locatedAll, Rule.locatedAll, List.map_append, Rule.located_under outer path r,
      Rule.locatedAll_under outer path rest]

end

/-- The fold of a stylesheet made of two rows of rules is the two folds, one after the other. -/
theorem Stylesheet.located_append (a b : List Rule) :
    Stylesheet.located ⟨a ++ b⟩ = Stylesheet.located ⟨a⟩ ++ Stylesheet.located ⟨b⟩ :=
  Rule.locatedAll_append [] a b

end Whatwg.Css.Syntax
