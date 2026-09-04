import Lean
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.CombinatorShape

The drift check for `Whatwg/Html/Node/Combinators.lean`, which is produced
from the schema rows by hand and not by the emitter, so `lake exe tyxmlschema`
says nothing about it. This file inspects the compiled environment instead:
for every row of `Whatwg.Html.Schema.elements` the combinator
`Whatwg.Html.E.<name>` must exist and return `Element tag ctx` with `tag` the
row's tag and `ctx` a bound variable; and
for every row of `Whatwg.Html.Schema.attributeCtors` that is not a prefix
the helper `Whatwg.Html.A.<name>` must exist and build an `AttrVal.of` of
the row's attribute. A schema change that the hand-maintained file
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

/-- The result of a combinator's type: the tag's constructor index, when the
type ends in `Element <tag> <ctx>` with the context a bound variable. -/
def resultTag? (type : Expr) : MetaM (Option Nat) :=
  forallTelescope type fun _ body => do
    unless body.getAppFn.isConstOf ``Whatwg.Html.Element do return none
    match body.getAppArgs with
    | #[tagE, ctxE] =>
      unless ctxE.isFVar do return none
      ctorIdxOf? tagE
    | _ => return none

/-- Every element row of `rows` whose combinator is missing or returns the
wrong tag, or is not polymorphic in its context. -/
def elementFailures (rows : List Element) : MetaM (List String) := do
  let mut failures : List String := []
  for e in rows do
    let n := `Whatwg.Html.E ++ Name.mkSimple e.name
    match (← getEnv).find? n with
    | none => failures := failures ++ ["no combinator " ++ toString n ++ " for element row " ++ e.name]
    | some info =>
      match ← resultTag? info.type with
      | none => failures := failures ++ [toString n ++ " does not return an Element polymorphic in its context"]
      | some t =>
        if t != e.tag.ctorIdx then
          failures := failures ++ [toString n ++ " returns the wrong tag"]
  return failures

/-- Every attribute row of `rows` whose helper is missing or does not return
an `AttrVal` of the row's attribute: the helper's body, under its binders,
must be `AttrVal.of <attr> _`. -/
def attributeFailures (rows : List AttrCtor) : MetaM (List String) := do
  let mut failures : List String := []
  for a in rows do
    if a.isPrefix then continue
    let n := `Whatwg.Html.A ++ Name.mkSimple a.name
    match (← getEnv).find? n with
    | none => failures := failures ++ ["no helper " ++ toString n ++ " for attribute row " ++ a.name]
    | some info =>
      let ok ← forallTelescope info.type fun _ body => pure (body.isConstOf ``Whatwg.Html.AttrVal)
      unless ok do failures := failures ++ [toString n ++ " does not return an AttrVal"]
      let some v := info.value? | failures := failures ++ [toString n ++ " has no body"]; continue
      let built ← lambdaTelescope v fun _ body => do
        if body.isAppOfArity ``Whatwg.Html.AttrVal.of 2 then ctorIdxOf? (body.getArg! 0) else return none
      if built != some a.tag.ctorIdx then
        failures := failures ++ [toString n ++ " builds the wrong attribute"]
  return failures

run_cmd liftTermElabM do
  let failures := (← elementFailures elements) ++ (← attributeFailures attributeCtors)
  unless failures.isEmpty do
    throwError ("combinator shape: " ++ toString failures.length ++
      " rows disagree with the schema:\n" ++ String.intercalate "\n" failures)

end WhatwgTest.Html.CombinatorShape
