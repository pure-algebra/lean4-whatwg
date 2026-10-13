
/-!
# Whatwg.Html.Node.Css

Owner: declarations and rules of CSS as data (slice S17 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Html/Node/SvgMotion.lean` writes the motion of a step as CSS. Until slice S17 it wrote
text: the `style` of a thing was one string, and so was the sheet. A caller whose thing had a
style of its own could not put the two together, and a test could read a sheet only as
characters. This module is the data that the writer now gives, and the text of it.

The shapes are those of the module of CSS that gives the grammar of a sheet, at its level 3,
as its editor's draft under `vendor/w3c-csswg-drafts-50337328/` says what parsing gives. A
sheet has a list of rules. A rule is an at-rule or a qualified rule. A declaration has a name,
a value and an important flag. A qualified rule has a prelude, a list of declarations and a
list of child rules. An at-rule has a name and a prelude; one that ends in a block also has a
list of declarations and a list of child rules, and one that ends in a semicolon has neither.
A value and a prelude are lists of component values there, and text here. A reader of that
grammar, when one is written (the consumer's ask W5 of
`docs/research/2026-10-12-whatwg-requests.md`), gives a tree of these types, and nothing here
is renamed for it.

- `Css.Decl`: one declaration, its name, its value as text, and whether it is `!important`. A
  pair of a name and a value is a declaration that is not: `("cursor", "pointer")`.
  `Css.Decls`: declarations in a row, what a `style` attribute holds and what a block holds.
  `Decls.css` writes them.
- `Decls.value? ds name important`: what a row says of a name among its declarations of one
  importance: the later of two is the one read. `Decls.shown? ds name`: what a browser shows of
  the name: the important declaration where the row has one.
- `Decls.once ds`: the same row with each name once for each importance. `Decls.merge own more`:
  two rows as one. Where both say a name with one importance, the second row's value stands.
- `Css.Rule`: a rule of a sheet. `Rule.qualified prelude decls rules` is a qualified rule: a
  style rule under a selector, or a keyframe under `from` or `to`. `Rule.at name prelude decls
  rules` is an at-rule that ends in a block, and `Rule.statement name prelude` one that ends in
  a semicolon. `Rule.style`, `Rule.keyframes` and `Rule.media` write the three rules that a
  motion and a look need. `Css.Sheet`: rules in a row. `Sheet.css` writes them, one rule a
  line.

```
let own : Css.Decls := [("cursor", "pointer"), ("opacity", "0.5")]
own.merge [("opacity", "0")]                                   -- cursor: pointer; opacity: 0
Css.Rule.style ".e4-text" [("fill", "var(--e4-color-ink)")]
Css.Rule.media "(prefers-reduced-motion: reduce)" [.style ".e4-view" [("opacity", "1")]]
```

What the laws say. A merged row has each name once for each importance (`Decls.merge_nodup`),
and it says of every name what the two rows in a row say: the second row's value, and the
first row's where the second has none (`Decls.value?_merge`, `Decls.shown?_merge`).
`Decls.once` changes no reading (`Decls.value?_once`, `Decls.shown?_once`) and leaves a row that
has each name once as it is (`Decls.once_of_nodup`). Two rules are told apart
(`Rule.beq_iff`), so a test compares a sheet with `==`.

What this module does not claim. It is no grammar of CSS, and it reads nothing: no reader of
CSS is written in this repository (debt D119). A name, a value and a prelude are text that the
caller writes by rule: a value that is no value of its property is written as it is. A
declaration is told from another by its name and its importance alone, so a shorthand and its
longhand are two names here: `animation` and `animation-delay` both stay in a merged row, in
their order. That an important declaration stands over one that is not, whatever their order,
is how a browser reads a block, from memory: `shown?` reads so, and `once` keeps both for the
browser to weigh. The writer puts the declarations of a block before its child rules. What a
block may hold is the rule's own to say, and nothing here says it: a keyframe with a child
rule is written as any other.

This module imports nothing. Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Html.Css

/-- One declaration of CSS: a name, a value as text, and whether it is `!important`. -/
structure Decl where
  /-- The name of the property, as CSS writes it: `opacity`, `stroke-dashoffset`, `--t`. -/
  name : String
  /-- The value, as CSS writes it. -/
  value : String
  /-- Whether the declaration is `!important`: it then stands over one that is not, in its own
  block and in a `style` attribute. -/
  important : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A name and a value are a declaration that is not important. -/
instance : Coe (String × String) Decl := ⟨fun p => { name := p.1, value := p.2 }⟩

namespace Decl

/-- The text of one declaration: `name: value`, with `!important` where it is. -/
def css (d : Decl) : String :=
  d.name ++ ": " ++ d.value ++ (if d.important then " !important" else "")

/-- What tells one declaration of a block from another when the block is read: its name and
its importance. Of two declarations with one key the later is the one read. -/
def key (d : Decl) : String × Bool := (d.name, d.important)

end Decl

/-- Declarations in a row: what a `style` attribute holds, and what a block holds. -/
abbrev Decls : Type := List Decl

namespace Decls

/-- The text of a row of declarations, with `; ` between two and nothing after the last. -/
def css (ds : Decls) : String := "; ".intercalate (ds.map Decl.css)

/-- **What a row of declarations says of a name**, among its declarations of one importance:
the value of the last of them, and nothing where the row has none. -/
def value? (ds : Decls) (name : String) (important : Bool := false) : Option String :=
  match ds with
  | [] => none
  | d :: rest =>
    (value? rest name important).or (if d.key = (name, important) then some d.value else none)

/-- **What a browser shows of a name in a row of declarations**: the last important declaration
of it, and the last one that is not where the row has no important one. -/
def shown? (ds : Decls) (name : String) : Option String :=
  (value? ds name true).or (value? ds name false)

/-- **A row with each name once for each importance**: of the declarations of one name and one
importance the last is kept, at its place. The row says of every name what it said
(`value?_once`). -/
def once : Decls → Decls
  | [] => []
  | d :: rest => if rest.any (fun e => e.key == d.key) then once rest else d :: once rest

/-- **Two rows of declarations as one**, each name once for each importance. Where both rows
say a name, the value of the second stands: a thing's own style is `own`, and what a motion
puts on the thing is `more`. -/
def merge (own more : Decls) : Decls := once (own ++ more)

/-! ### What a row says -/

/-- A row says nothing of a name with an importance exactly when it has no such declaration. -/
theorem value?_eq_none {ds : Decls} {name : String} {important : Bool} :
    value? ds name important = none ↔ ∀ d ∈ ds, d.key ≠ (name, important) := by
  induction ds with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons d rest ih =>
    show (value? rest name important).or
      (if d.key = (name, important) then some d.value else none) = none ↔ _
    constructor
    · intro h e he
      cases hr : value? rest name important with
      | some v =>
        rw [hr] at h
        exact nomatch h
      | none =>
        rw [hr] at h
        have h' : (if d.key = (name, important) then some d.value else none) = none := h
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

/-! ### Each name once -/

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

/-- **`once` leaves each name once for each importance.** A `style` attribute written from it
says no declaration that another of the row replaces. -/
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
        (if d.key = (name, important) then some d.value else none)
      cases hr : value? rest name important with
      | some v => rfl
      | none =>
        obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hany
        have hne : d.key ≠ (name, important) := fun h =>
          value?_eq_none.mp hr e he ((beq_iff_eq.mp hp).trans h)
        exact (if_neg hne).symm
    · show (value? (once rest) name important).or _ = (value? rest name important).or _
      rw [ih]

/-- `once` changes nothing that a browser shows. -/
theorem shown?_once (ds : Decls) (name : String) : shown? (once ds) name = shown? ds name := by
  rw [shown?, shown?, value?_once, value?_once]

/-- A row that says each name once for each importance is kept as it is. -/
theorem once_of_nodup : ∀ {ds : Decls}, (ds.map Decl.key).Nodup → once ds = ds
  | [], _ => rfl
  | d :: rest, h => by
    have h' : d.key ∉ rest.map Decl.key ∧ (rest.map Decl.key).Nodup := List.nodup_cons.mp h
    rw [once, once_of_nodup h'.2]
    exact if_neg fun hany => by
      obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hany
      exact h'.1 (List.mem_map.mpr ⟨e, he, beq_iff_eq.mp hp⟩)

/-! ### Two rows as one -/

/-- **A merged row has each name once for each importance.** A thing with a style of its own
and a motion has one `style` attribute, and no declaration in it is replaced by another. -/
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

/-- A row merged with nothing is the row with each name once. -/
theorem merge_nil (own : Decls) : merge own [] = once own := by
  rw [merge, List.append_nil]

/-- Nothing merged with a row is the row with each name once. -/
theorem nil_merge (more : Decls) : merge [] more = once more := rfl

end Decls

/-! ## Rules -/

/-- A rule of a style sheet: a qualified rule, or an at-rule of one of its two kinds. -/
inductive Rule where
  /-- A qualified rule: a prelude, declarations and child rules. The prelude of a style rule is
  its selector, and the prelude of a keyframe is `from`, `to` or a per cent. -/
  | qualified (prelude : String) (decls : Decls) (rules : List Rule)
  /-- An at-rule that ends in a block: `@name prelude { … }`, with declarations and child
  rules. `@media (…) { … }` has the name `media`, its query for a prelude, and child rules.
  `@keyframes m-0 { … }` has the name `keyframes`, the name of the animation for a prelude, and
  its keyframes for child rules. -/
  | «at» (name prelude : String) (decls : Decls) (rules : List Rule)
  /-- An at-rule that ends in a semicolon, as `@import` does: `@name prelude;`. -/
  | statement (name prelude : String)

/-- What stands between the braces of a block: its declarations, and then its child rules. -/
def inside (decls rules : String) : String :=
  if decls.isEmpty then rules else if rules.isEmpty then decls else decls ++ "; " ++ rules

/-- A block, from what stands between its braces. -/
def braces (inner : String) : String := if inner.isEmpty then " { }" else " { " ++ inner ++ " }"

/-- The start of an at-rule: `@name`, and its prelude where it has one. -/
def atHead (name prelude : String) : String :=
  "@" ++ name ++ (if prelude.isEmpty then "" else " " ++ prelude)

mutual

/-- The text of a rule, on one line. -/
def Rule.css : Rule → String
  | .qualified prelude decls rules => prelude ++ braces (inside decls.css (Rule.cssAll rules))
  | .at name prelude decls rules =>
    atHead name prelude ++ braces (inside decls.css (Rule.cssAll rules))
  | .statement name prelude => atHead name prelude ++ ";"

/-- The text of the child rules of a block, with a space between two. -/
def Rule.cssAll : List Rule → String
  | [] => ""
  | [r] => r.css
  | r :: s :: rest => r.css ++ " " ++ Rule.cssAll (s :: rest)

end

namespace Rule

/-- `selector { … }`: a qualified rule with declarations and no child rule. -/
def style (selector : String) (decls : Decls) : Rule := .qualified selector decls []

/-- `@keyframes name { from { … } to { … } }`: the declarations at the start and at the end of
an animation. -/
def keyframes (name : String) (start stop : Decls) : Rule :=
  .at "keyframes" name [] [.qualified "from" start [], .qualified "to" stop []]

/-- `@media query { … }`: rules that hold only where the query does. -/
def media (query : String) (rules : List Rule) : Rule := .at "media" query [] rules

end Rule

/-- Rules in a row: a style sheet. -/
abbrev Sheet : Type := List Rule

/-- The text of a sheet: one rule a line. -/
def Sheet.css (rules : Sheet) : String := "\n".intercalate (rules.map Rule.css)

/-! ### Telling two rules apart

A rule holds rules, and for such a type Lean derives no test of equality that the kernel can
unfold. The test is written here, with its law. -/

mutual

/-- Whether two rules are one rule. -/
def Rule.beq : Rule → Rule → Bool
  | .qualified p ds rs, .qualified p' ds' rs' => p == p' && ds == ds' && Rule.beqAll rs rs'
  | .at n p ds rs, .at n' p' ds' rs' => n == n' && p == p' && ds == ds' && Rule.beqAll rs rs'
  | .statement n p, .statement n' p' => n == n' && p == p'
  | .qualified _ _ _, .at _ _ _ _ => false
  | .qualified _ _ _, .statement _ _ => false
  | .at _ _ _ _, .qualified _ _ _ => false
  | .at _ _ _ _, .statement _ _ => false
  | .statement _ _, .qualified _ _ _ => false
  | .statement _ _, .at _ _ _ _ => false

/-- Whether two rows of rules are one row. -/
def Rule.beqAll : List Rule → List Rule → Bool
  | [], [] => true
  | r :: rs, r' :: rs' => Rule.beq r r' && Rule.beqAll rs rs'
  | [], _ :: _ => false
  | _ :: _, [] => false

end

mutual

/-- The test of two rules answers yes exactly when they are one rule. -/
theorem Rule.beq_iff : ∀ a b : Rule, Rule.beq a b = true ↔ a = b
  | .qualified p ds rs, .qualified p' ds' rs' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.qualified.injEq,
      Rule.beqAll_iff rs rs', and_assoc]
  | .at n p ds rs, .at n' p' ds' rs' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.at.injEq, Rule.beqAll_iff rs rs',
      and_assoc]
  | .statement n p, .statement n' p' => by
    simp only [Rule.beq, Bool.and_eq_true, beq_iff_eq, Rule.statement.injEq]
  | .qualified _ _ _, .at _ _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .qualified _ _ _, .statement _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .at _ _ _ _, .qualified _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .at _ _ _ _, .statement _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .statement _ _, .qualified _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]
  | .statement _ _, .at _ _ _ _ => by simp only [Rule.beq, Bool.false_eq_true, reduceCtorEq]

/-- The test of two rows of rules answers yes exactly when they are one row. -/
theorem Rule.beqAll_iff : ∀ a b : List Rule, Rule.beqAll a b = true ↔ a = b
  | [], [] => by simp only [Rule.beqAll]
  | r :: rs, r' :: rs' => by
    simp only [Rule.beqAll, Bool.and_eq_true, Rule.beq_iff r r', Rule.beqAll_iff rs rs',
      List.cons.injEq]
  | [], _ :: _ => by simp only [Rule.beqAll, Bool.false_eq_true, reduceCtorEq]
  | _ :: _, [] => by simp only [Rule.beqAll, Bool.false_eq_true, reduceCtorEq]

end

instance : DecidableEq Rule := fun a b => decidable_of_iff _ (Rule.beq_iff a b)

instance : Inhabited Rule := ⟨.qualified "" [] []⟩

/-! ### Showing a rule -/

mutual

/-- A rule as it is written in Lean. -/
def Rule.repr : Rule → Nat → Std.Format
  | .qualified prelude decls rules, prec =>
    Repr.addAppParen (.group (.nest 2 ("Whatwg.Html.Css.Rule.qualified" ++ .line ++
      reprArg prelude ++ .line ++ reprArg decls ++ .line ++ "[" ++ Rule.reprAll rules ++ "]")))
      prec
  | .at name prelude decls rules, prec =>
    Repr.addAppParen (.group (.nest 2 ("Whatwg.Html.Css.Rule.at" ++ .line ++ reprArg name ++
      .line ++ reprArg prelude ++ .line ++ reprArg decls ++ .line ++ "[" ++
      Rule.reprAll rules ++ "]"))) prec
  | .statement name prelude, prec =>
    Repr.addAppParen (.group (.nest 2 ("Whatwg.Html.Css.Rule.statement" ++ .line ++
      reprArg name ++ .line ++ reprArg prelude))) prec

/-- A row of rules as it is written in Lean, between its brackets. -/
def Rule.reprAll : List Rule → Std.Format
  | [] => ""
  | [r] => Rule.repr r 0
  | r :: s :: rest => Rule.repr r 0 ++ "," ++ .line ++ Rule.reprAll (s :: rest)

end

instance : Repr Rule := ⟨Rule.repr⟩

end Whatwg.Html.Css
