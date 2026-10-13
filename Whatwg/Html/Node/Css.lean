import Whatwg.Css.Syntax.Build

/-!
# Whatwg.Html.Node.Css

Owner: the declarations and the rules that the picture kit writes, on the one tree of CSS
(slice S17 of `docs/SVG-PACKAGE-PLAN.md`; on the tree of `Whatwg/Css/Syntax/Tree.lean` since
slice S22, ruling CS-9 of `docs/CSS-PACKAGE-PLAN.md`).

Until slice S22 this module had a tree of its own: a declaration, a rule and a sheet whose
every name, value and prelude was a `String`. The library of CSS has the tree that the
standard's parser gives, with values as component values. There were two trees of one sort, and
a sheet written here was read back by nothing. Now there is one: a declaration here is
`Whatwg.Css.Syntax.Declaration`, a rule is `Whatwg.Css.Syntax.Rule`, and a sheet is a list of
rules. What the kit writes prints through the writer of that tree
(`Whatwg/Css/Syntax/Write.lean`). The tokenizer reads the text back to the tokens of the tree
where they are writable (`tokenize_serialize` of `Whatwg/Css/Syntax/Laws.lean`), and the parser
of slice K4 reads those tokens back to the tree.

- `Css.Decl`: one declaration: its name, its value as component values, and whether it is
  `!important`. A pair of two texts is still a declaration that is not: `("cursor",
  "pointer")`. Its value is the text read by the tokenizer and the parser (`Value.ofText`).
  `.of "opacity" [.thousandths 250]` is a declaration of a built value
  (`Whatwg/Css/Syntax/Build.lean`), and nothing is read. `Css.Decls`: declarations in a row.
  `Decls.css` writes them.
- `Decl.key`: what tells one declaration of a block from another when the block is read: its
  name and its importance. CSS reads the name of a property with no regard to the case of its
  ASCII letters, and the name of a custom property as it is written, so `Opacity` and `opacity`
  are one key, and `--t` and `--T` are two (`nameKey`).
- `Decls.value? ds name important`: what a row says of a name among its declarations of one
  importance: the later of two is the one read. `Decls.shown? ds name`: what a browser shows of
  the name: the important declaration where the row has one. Both give component values;
  `Value.text` is their text.
- `Decls.once ds`: the same row with each key once. `Decls.merge own more`: two rows as one.
  Where both say a name with one importance, the second row's value stands.
- `Css.Rule`: a rule. `Rule.style` is a qualified rule: a style rule under a selector, or a
  keyframe under `from` or `to`. `Rule.at` is an at-rule that ends in a block,
  `Rule.atStatement` one that ends in a semicolon, and `Rule.keyframes`, `Rule.frames` and
  `Rule.media` are the at-rules that a motion and a look need. A selector and a query are
  component values, built (`Prelude.class`, `Prelude.attr`, `Prelude.feature`) or read from a
  text (`Prelude.ofText`). `Rule.prelude`, `Rule.name?`, `Rule.decls` and `Rule.rules` read a
  rule back. `Css.Sheet`: rules in a row. `Sheet.css` writes them, one rule a line, and
  `Sheet.decls?` reads the declarations under a selector.
- `Decls.writable` and `Decls.quiet`, `Sheet.writable` and `Sheet.quiet`: tests that compute.
  The tokens of the row or of the sheet are `Writable`, the premise under which the tokenizer
  reads the text back to them (`tokenize_serialize` of `Whatwg/Css/Syntax/Laws.lean`); and they
  are `Quiet`, so the text holds no comment. Neither says that the parser reads the tree back:
  a value with a semicolon at its top passes both.

```
let own : Css.Decls := [("cursor", "pointer"), ("opacity", "0.5")]
own.merge [.of "opacity" [.int 0]]                             -- cursor: pointer; opacity: 0
Css.Rule.style (Prelude.class "e4-text") [("fill", "var(--e4-color-ink)")]
Css.Rule.style (.ofText ".e4-text") [.of "fill" [.var "e4-color-ink"]]   -- the same rule
Css.Rule.media (Prelude.feature "prefers-reduced-motion" [.ident "reduce"])
  [.style (Prelude.class "e4-view") [.of "opacity" [.int 1]]]
```

Where the white space of a rule is. The parser keeps the white space of a prelude, so it
belongs to the tree: the prelude of `.a { }` ends with a whitespace token, and the prelude of
`@media (…) { }` starts and ends with one. The three builders of this module put those tokens
(`Rule.style`, `Rule.at`, `Rule.atStatement`), and they are the only places here that name a
constructor of `Whatwg.Css.Syntax.Rule` to build a rule. The four readers and `Sheet.decls?`
are the only places that take one apart. So a change to what a block holds is a change to
those eight definitions, and to no caller. A caller gives a prelude with no white space at its
ends, and `Rule.prelude` gives it back so.

What the laws say. A merged row has each key once (`Decls.merge_nodup`), and it says of every
name what the two rows in a row say: the second row's value, and the first row's where the
second has none (`Decls.value?_merge`, `Decls.shown?_merge`). `Decls.once` changes no reading
(`Decls.value?_once`, `Decls.shown?_once`) and leaves a row that has each key once as it is
(`Decls.once_of_nodup`). A rule read back has the declarations and the child rules it was built
with (`Rule.decls_style`, `Rule.rules_style`, `Rule.decls_at`, `Rule.rules_at`). Two trees are
told apart by `==` and `=` (`Whatwg.Css.Syntax.Rule.beq_iff` of
`Whatwg/Css/Syntax/Write.lean`), so a test compares a sheet with `==`.

What this module does not claim. That a value is a value of its property: `("opacity",
"blue")` is a declaration, and `Whatwg/Css/Values/Admits.lean` is what judges a value against
the grammar of a property. That a text is read as its writer meant: a text with a semicolon or
a closing brace at its top is read as component values all the same, and written back it ends
its declaration early. That a selector selects anything. A declaration is told from another by
its key alone, so a shorthand and its longhand are two names here: `animation` and
`animation-delay` both stay in a merged row, in their order. That an important declaration
stands over one that is not, whatever their order, is how a browser reads a block, from memory:
`shown?` reads so, and `once` keeps both for the browser to weigh. That property names are read
with no regard to case, and custom property names as written, is the sealed text of CSS Syntax
3 and of CSS Variables 1 under `vendor/w3c-csswg-drafts-50337328/`; a vendor prefix and an
escape in a name are not folded here.

This module imports the builders, and with them the tokenizer and the writer of tokens; it
imported nothing until slice S22. The laws of `once` and of `merge` that read no name
(`Decls.mem_of_mem_once`, `Decls.once_nodup`, `Decls.once_of_nodup`, `Decls.once_ne_nil`,
`Decls.merge_nodup`, `Decls.merge_nil`, `Decls.nil_merge`) and the two laws of `Rule.style`
depend on `propext` and `Quot.sound` at most. `Decls.value?` and `Decls.shown?` take a name as
a `String`, and `String.toList` of core reaches `Classical.choice`. So they and their laws
(`Decls.value?_eq_none`, `Decls.value?_append`, `Decls.value?_once`, `Decls.shown?_once`,
`Decls.value?_merge`, `Decls.shown?_merge`) depend on it too, as do the builders of a rule that
take a name, the writers of text, and the pair of two texts, which also runs the tokenizer.
Until slice S22 a name was compared as a `String` and no law here reached that axiom. No
declaration here reaches any other.
-/

namespace Whatwg.Html.Css

open Whatwg.Css.Syntax (Component Value Prelude Declaration)

/-- One declaration of CSS: a name, a value as component values, and whether it is
`!important`. It is the declaration of the tree that the parser of CSS gives. -/
abbrev Decl : Type := Whatwg.Css.Syntax.Declaration

/-- A name and the text of a value are a declaration that is not important. The pair is the one
place where a text reads as a value with nothing said: a pair of two texts is put together
before it is read, so `("stroke", "var(--e4-" ++ role ++ ")")` is the value of the whole
text. -/
instance : Coe (String × String) Decl := ⟨fun p => .of p.1 (Value.ofText p.2)⟩

/-- Whether a name is that of a custom property: it starts with two hyphen-minus. -/
def isCustom : List Char → Bool
  | '-' :: '-' :: _ => true
  | _ => false

/-- **The name of a property as CSS tells it from another.** The name of a property is read
with no regard to the case of its ASCII letters, so it is put in lower case; the name of a
custom property is read as it is written. -/
def nameKey (name : List Char) : List Char := if isCustom name then name else name.map Char.toLower

namespace Decl

/-- The text of one declaration: `name: value`, with `!important` where it is. -/
def css (d : Decl) : String := d.text

/-- What tells one declaration of a block from another when the block is read: its name, as
`nameKey` reads it, and its importance. Of two declarations with one key the later is the one
read. -/
def key (d : Decl) : List Char × Bool := (nameKey d.name, d.important)

end Decl

/-- Declarations in a row: what a `style` attribute holds, and what a block holds. -/
abbrev Decls : Type := List Decl

namespace Decls

/-- The text of a row of declarations, with `; ` between two and nothing after the last. -/
def css (ds : Decls) : String := Declaration.textAll ds

/-- **Whether a writer may write the row**: its tokens are `Writable`, the premise under which
the tokenizer reads the text back to them (`tokenize_serialize` of
`Whatwg/Css/Syntax/Laws.lean`). A caller checks its own declarations so, once, in a guard. -/
def writable (ds : Decls) : Bool := Whatwg.Css.Syntax.Writable (Declaration.tokensAll ds)

/-- **Whether the text of the row holds no comment**: its tokens are `Quiet`. -/
def quiet (ds : Decls) : Bool := Whatwg.Css.Syntax.Quiet (Declaration.tokensAll ds)

/-- **What a row of declarations says of a name**, among its declarations of one importance:
the value of the last of them, and nothing where the row has none. The name is read as
`nameKey` reads it. -/
def value? (ds : Decls) (name : String) (important : Bool := false) : Option Value :=
  match ds with
  | [] => none
  | d :: rest =>
    (value? rest name important).or
      (if d.key = (nameKey name.toList, important) then some d.value else none)

/-- **What a browser shows of a name in a row of declarations**: the last important declaration
of it, and the last one that is not where the row has no important one. -/
def shown? (ds : Decls) (name : String) : Option Value :=
  (value? ds name true).or (value? ds name false)

/-- **A row with each key once**: of the declarations of one name and one importance the last
is kept, at its place. The row says of every name what it said (`value?_once`). -/
def once : Decls → Decls
  | [] => []
  | d :: rest => if rest.any (fun e => e.key == d.key) then once rest else d :: once rest

/-- **Two rows of declarations as one**, each key once. Where both rows say a name, the value
of the second stands: a thing's own style is `own`, and what a motion puts on the thing is
`more`. -/
def merge (own more : Decls) : Decls := once (own ++ more)

/-! ### What a row says -/

/-- A row says nothing of a name with an importance exactly when it has no such declaration. -/
theorem value?_eq_none {ds : Decls} {name : String} {important : Bool} :
    value? ds name important = none ↔ ∀ d ∈ ds, d.key ≠ (nameKey name.toList, important) := by
  induction ds with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons d rest ih =>
    show (value? rest name important).or
      (if d.key = (nameKey name.toList, important) then some d.value else none) = none ↔ _
    constructor
    · intro h e he
      cases hr : value? rest name important with
      | some v =>
        rw [hr] at h
        exact nomatch h
      | none =>
        rw [hr] at h
        have h' : (if d.key = (nameKey name.toList, important) then some d.value else none) =
            none := h
        rcases List.mem_cons.mp he with e1 | e2
        · intro hp
          rw [e1] at hp
          rw [if_pos hp] at h'
          exact nomatch h'
        · exact ih.mp hr e e2
    · intro h
      rw [ih.mpr fun e he => h e (List.mem_cons_of_mem d he)]
      exact if_neg (h d List.mem_cons_self)

/-- **Two rows in a row say what the second says, and what the first says where the second says
nothing.** -/
theorem value?_append (a b : Decls) (name : String) (important : Bool) :
    value? (a ++ b) name important = (value? b name important).or (value? a name important) := by
  induction a with
  | nil =>
    show value? b name important = (value? b name important).or none
    cases value? b name important <;> rfl
  | cons d rest ih =>
    show (value? (rest ++ b) name important).or _ =
      (value? b name important).or ((value? rest name important).or _)
    rw [ih]
    cases value? b name important <;> rfl

/-! ### Each key once -/

/-- A declaration that `once` keeps is a declaration of the row. -/
theorem mem_of_mem_once {ds : Decls} {d : Decl} : d ∈ once ds → d ∈ ds := by
  induction ds with
  | nil => exact id
  | cons e rest ih =>
    intro h
    rw [once] at h
    split at h
    · exact List.mem_cons_of_mem e (ih h)
    · rcases List.mem_cons.mp h with e1 | e2
      · exact e1 ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem e (ih e2)

/-- **`once` leaves each key once.** A `style` attribute written from it says no declaration
that another of the row replaces. -/
theorem once_nodup (ds : Decls) : ((once ds).map Decl.key).Nodup := by
  induction ds with
  | nil => exact List.nodup_nil
  | cons d rest ih =>
    rw [once]
    split
    · exact ih
    · rename_i hno
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hin => hno ?_, ih⟩
      obtain ⟨e, he, hp⟩ := List.mem_map.mp hin
      exact List.any_eq_true.mpr ⟨e, mem_of_mem_once he, beq_iff_eq.mpr hp⟩

/-- **`once` changes no reading**: the row says of every name what it said. -/
theorem value?_once (ds : Decls) (name : String) (important : Bool) :
    value? (once ds) name important = value? ds name important := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    rw [once]
    split
    · rename_i hany
      rw [ih]
      show value? rest name important = (value? rest name important).or
        (if d.key = (nameKey name.toList, important) then some d.value else none)
      cases hr : value? rest name important with
      | some v => rfl
      | none =>
        obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hany
        have hne : d.key ≠ (nameKey name.toList, important) := fun h =>
          value?_eq_none.mp hr e he ((beq_iff_eq.mp hp).trans h)
        exact (if_neg hne).symm
    · show (value? (once rest) name important).or _ = (value? rest name important).or _
      rw [ih]

/-- `once` changes nothing that a browser shows. -/
theorem shown?_once (ds : Decls) (name : String) : shown? (once ds) name = shown? ds name := by
  rw [shown?, shown?, value?_once, value?_once]

/-- A row that says each key once is kept as it is. -/
theorem once_of_nodup : ∀ {ds : Decls}, (ds.map Decl.key).Nodup → once ds = ds
  | [], _ => rfl
  | d :: rest, h => by
    have h' : d.key ∉ rest.map Decl.key ∧ (rest.map Decl.key).Nodup := List.nodup_cons.mp h
    rw [once, once_of_nodup h'.2]
    exact if_neg fun hany => by
      obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hany
      exact h'.1 (List.mem_map.mpr ⟨e, he, beq_iff_eq.mp hp⟩)

/-- A row that is not empty is not empty with each key once: its last declaration is kept. -/
theorem once_ne_nil : ∀ {ds : Decls}, ds ≠ [] → once ds ≠ []
  | [], h => absurd rfl h
  | d :: rest, _ => by
    rw [once]
    split
    · rename_i hany
      refine once_ne_nil fun e => ?_
      rw [e] at hany
      exact Bool.noConfusion hany
    · exact List.cons_ne_nil _ _

/-! ### Two rows as one -/

/-- **A merged row has each key once.** A thing with a style of its own and a motion has one
`style` attribute, and no declaration in it is replaced by another. -/
theorem merge_nodup (own more : Decls) : ((merge own more).map Decl.key).Nodup :=
  once_nodup (own ++ more)

/-- **What a merged row says of a name**: what the second row says, and what the first says
where the second says nothing. So a motion's declaration of a property stands over the thing's
own, and the thing's own stands wherever the motion has none. -/
theorem value?_merge (own more : Decls) (name : String) (important : Bool) :
    value? (merge own more) name important =
      (value? more name important).or (value? own name important) :=
  (value?_once (own ++ more) name important).trans (value?_append own more name important)

/-- **What a browser shows of a name in a merged row**: an important declaration of either row
before one that is not, and among those of one importance the second row's before the
first's. -/
theorem shown?_merge (own more : Decls) (name : String) :
    shown? (merge own more) name =
      ((value? more name true).or (value? own name true)).or
        ((value? more name false).or (value? own name false)) := by
  rw [shown?, value?_merge, value?_merge]

/-- A row merged with nothing is the row with each key once. -/
theorem merge_nil (own : Decls) : merge own [] = once own := by
  rw [merge, List.append_nil]

/-- Nothing merged with a row is the row with each key once. -/
theorem nil_merge (more : Decls) : merge [] more = once more := rfl

end Decls

/-! ## Rules -/

/-- A rule of a style sheet: the rule of the tree that the parser of CSS gives. -/
abbrev Rule : Type := Whatwg.Css.Syntax.Rule

namespace Rule

/-- **A qualified rule**: `selector { declarations; rules }`. A style rule under its selector,
and a keyframe under `from`, `to` or a per cent. The white space before the brace is the
prelude's, and is put here. -/
def style (selector : Prelude) (decls : Decls) (rules : List Rule := []) : Rule :=
  .qualified (selector ++ [.space]) decls rules

/-- **An at-rule that ends in a block**: `@name prelude { declarations; rules }`. The white
space on both sides of the prelude is the prelude's, and is put here. -/
def «at» (name : String) (prelude : Prelude) (decls : Decls) (rules : List Rule) : Rule :=
  .blockAt name.toList (.space :: (if prelude.isEmpty then [] else prelude ++ [.space])) decls rules

/-- **An at-rule that ends in a semicolon**, as `@import` does: `@name prelude;`. -/
def atStatement (name : String) (prelude : Prelude) : Rule :=
  .statement name.toList (if prelude.isEmpty then [] else .space :: prelude)

/-- `@keyframes name { selector { … } … }`: a keyframe for each selector, in the order
given. -/
def frames (name : String) (keyframes : List (Prelude × Decls)) : Rule :=
  .at "keyframes" [.ident name] [] (keyframes.map fun k => style k.1 k.2)

/-- `@keyframes name { from { … } to { … } }`: the declarations at the start and at the end of
an animation. -/
def keyframes (name : String) (start stop : Decls) : Rule :=
  frames name [(Prelude.from, start), (Prelude.to, stop)]

/-- `@media query { … }`: rules that hold only where the query does. -/
def media (query : Prelude) (rules : List Rule) : Rule := .at "media" query [] rules

/-- **The prelude of a rule**, with no white space at its two ends: what a builder of this
module was given. A nested declarations rule has none. -/
def prelude : Rule → Prelude
  | .qualified p _ _ => Value.trim p
  | .blockAt _ p _ _ => Value.trim p
  | .statement _ p => Value.trim p
  | .nested _ => []

/-- The name of an at-rule, and nothing for a rule that is none. -/
def name? : Rule → Option String
  | .blockAt n _ _ _ => some (String.ofList n)
  | .statement n _ => some (String.ofList n)
  | _ => none

/-- The declarations of a rule's block. -/
def decls : Rule → Decls
  | .qualified _ ds _ => ds
  | .blockAt _ _ ds _ => ds
  | .nested ds => ds
  | .statement _ _ => []

/-- The child rules of a rule's block. -/
def rules : Rule → List Rule
  | .qualified _ _ rs => rs
  | .blockAt _ _ _ rs => rs
  | _ => []

/-- The text of a rule, on one line. -/
def css (r : Rule) : String := r.text

/-- A style rule holds the declarations it was built with. -/
theorem decls_style (selector : Prelude) (ds : Decls) (rs : List Rule) :
    (style selector ds rs).decls = ds := rfl

/-- A style rule holds the child rules it was built with. -/
theorem rules_style (selector : Prelude) (ds : Decls) (rs : List Rule) :
    (style selector ds rs).rules = rs := rfl

/-- An at-rule holds the declarations it was built with. -/
theorem decls_at (name : String) (p : Prelude) (ds : Decls) (rs : List Rule) :
    (Rule.at name p ds rs).decls = ds := rfl

/-- An at-rule holds the child rules it was built with. -/
theorem rules_at (name : String) (p : Prelude) (ds : Decls) (rs : List Rule) :
    (Rule.at name p ds rs).rules = rs := rfl

end Rule

/-- Rules in a row: a style sheet. -/
abbrev Sheet : Type := List Rule

namespace Sheet

/-- The sheet as the stylesheet of the tree. -/
def stylesheet (rules : Sheet) : Whatwg.Css.Syntax.Stylesheet := ⟨rules⟩

/-- The text of a sheet: one rule a line. -/
def css (rules : Sheet) : String := (stylesheet rules).lines

/-- **Whether a writer may write the sheet**: its tokens are `Writable`. -/
def writable (rules : Sheet) : Bool := Whatwg.Css.Syntax.Writable (stylesheet rules).tokens

/-- **Whether the text of the sheet holds no comment**: its tokens are `Quiet`. -/
def quiet (rules : Sheet) : Bool := Whatwg.Css.Syntax.Quiet (stylesheet rules).tokens

/-- **The declarations of the first style rule of a sheet under a selector**, and nothing where
the sheet has none. The rules inside an at-rule are not looked at. -/
def decls? (rules : Sheet) (selector : Prelude) : Option Decls :=
  rules.findSome? fun r =>
    match r with
    | .qualified _ ds _ => if r.prelude = selector then some ds else none
    | _ => none

end Sheet

end Whatwg.Html.Css
