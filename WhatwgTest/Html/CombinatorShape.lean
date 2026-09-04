import Lean
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.CombinatorShape

The drift check for `Whatwg/Html/Node/Combinators.lean`, which is produced
from the schema rows by hand and not by the emitter, so `lake exe tyxmlschema`
says nothing about it. This file inspects the compiled environment instead:
for every row of `Whatwg.Html.Schema.elements` the combinator
`Whatwg.Html.E.<name>` must exist and return `Element tag inner`, where `tag`
is the row's tag and `inner` is the row's content set (`notag` where the row
carries none), or a bound variable exactly when the row is transparent; and
for every row of `Whatwg.Html.Schema.attributeCtors` that is not a prefix
the helper `Whatwg.Html.A.<name>` must exist, take a `String` unless the
attribute is boolean, and build a pair whose tag is the row's attribute. A schema change that the hand-maintained file
does not follow fails this file with every disagreeing row listed, never a
truncated list.

What this does not check: the children parameter, the labelled arguments of
`html_sigs.mli`, and the attribute set each `_ha` auto-parameter names; those
are the documented simplifications of the combinator module and the
constructions of `WhatwgTest/Html/Builders.lean` exercise them.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.CombinatorShape

open Lean Meta Elab Command
open Whatwg.Html.Schema

/-- The constructor index of the constructor constant an expression is, or
`none` when it is anything else. -/
def ctorIdxOf? (e : Expr) : MetaM (Option Nat) := do
  let some n := e.constName? | return none
  match (← getEnv).find? n with
  | some (.ctorInfo c) => return some c.cidx
  | _ => return none

/-- The result row of a combinator's type: the tag's constructor index, and
either the content set's constructor index or `none` when the set is a bound
variable of the type. `none` altogether when the type does not end in
`Element _ _`. -/
def resultRow? (type : Expr) : MetaM (Option (Nat × Option Nat)) :=
  forallTelescope type fun _ body => do
    unless body.getAppFn.isConstOf ``Whatwg.Html.Element do return none
    match body.getAppArgs with
    | #[tagE, innerE] =>
      let some t ← ctorIdxOf? tagE | return none
      if innerE.isFVar then return some (t, none)
      let some c ← ctorIdxOf? innerE | return none
      return some (t, some c)
    | _ => return none

/-- Every element row of `rows` whose combinator is missing or returns the
wrong row. Takes the rows as a parameter so that a planted wrong row can be
shown to fail. -/
def elementFailures (rows : List Element) : MetaM (List String) := do
  let mut failures : List String := []
  for e in rows do
    let n := `Whatwg.Html.E ++ Name.mkSimple e.name
    match (← getEnv).find? n with
    | none => failures := failures ++ ["no combinator " ++ toString n ++ " for element row " ++ e.name]
    | some info =>
      match ← resultRow? info.type with
      | none => failures := failures ++ [toString n ++ " does not return an Element"]
      | some (t, c) =>
        if t != e.tag.ctorIdx then
          failures := failures ++ [toString n ++ " returns the wrong tag"]
        let expected := e.content.ctorIdx
        match c with
        | none =>
          unless e.transparent do
            failures := failures ++ [toString n ++ " is polymorphic in its content set but its row is not transparent"]
        | some c =>
          if e.transparent then
            failures := failures ++ [toString n ++ " fixes its content set but its row is transparent"]
          else if c != expected then
            failures := failures ++ [toString n ++ " returns the wrong content set"]
  return failures

/-- Every attribute row of `rows` whose helper is missing, has the wrong type,
or builds the wrong tag. -/
def attributeFailures (rows : List AttrCtor) : MetaM (List String) := do
  let mut failures : List String := []
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Attr) (mkConst ``String)
  let valuedT ← mkArrow (mkConst ``String) pairT
  for a in rows do
    if a.isPrefix then continue
    let n := `Whatwg.Html.A ++ Name.mkSimple a.name
    let expectedT := if a.kind == .boolean then pairT else valuedT
    match (← getEnv).find? n with
    | none => failures := failures ++ ["no helper " ++ toString n ++ " for attribute row " ++ a.name]
    | some info =>
      unless ← isDefEq info.type expectedT do
        failures := failures ++ [toString n ++ " does not have the shape its kind fixes"]
      let some v := info.value? | failures := failures ++ [toString n ++ " has no body"]; continue
      let built ← lambdaTelescope v fun _ body => do
        match body.getAppArgs with
        | #[_, _, fst, _] => ctorIdxOf? fst
        | _ => return none
      if built != some a.tag.ctorIdx then
        failures := failures ++ [toString n ++ " builds the wrong attribute tag"]
  return failures

run_cmd liftTermElabM do
  let failures := (← elementFailures elements) ++ (← attributeFailures attributeCtors)
  unless failures.isEmpty do
    throwError ("combinator shape: " ++ toString failures.length ++
      " rows disagree with the schema:\n" ++ String.intercalate "\n" failures)

end WhatwgTest.Html.CombinatorShape
