import Lean
import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Admit

The `admits` tactic: the auto-parameter tactic of every combinator in
`Whatwg.Html.Node.Combinators`, discharging the two obligations of the typed
tree, `Whatwg.Html.Content.Admits set t` and `Whatwg.Html.AttrsAdmitted set
attrs`, without asking the elaborator to reduce anything.

## Why not `decide`

`decide` is correct here and was the H3 route, but every obligation costs the
elaborator a `whnf` of the admission function through the `Decidable`
instance, some six thousand heartbeats each, and there are two per element
node (`WhatwgTest/Html/DecideBenchmark.lean`). The obligations are closed
terms over a finite schema whose functions are compiled, so the tactic reads
the closed `set` and `t` back as values (a constructor constant is read by
its index through the `ofNat` that `deriving DecidableEq` generates, and
`childSet s t` is computed by the same resolver `childSet` unfolds to),
evaluates `Content.admits` or `AttrSet.contains` as an ordinary function,
and closes the goal with `Eq.refl true`. The kernel re-evaluates the
obligation when the declaration is added, so the compiled evaluation
decides only whether to mint the proof or to report; a disagreement between
the two would be a kernel error, never an accepted falsehood. No `evalExpr`
and no `unsafe`: nothing is interpreted.

## Diagnostics

On a false obligation the tactic names the element by its markup name and
the content set that excludes it by its TyXML name, with the transparent
payload already resolved, so `<div>` under `<p>` reports
`phrasing` and `<div>` under a link in a paragraph reports
`phrasing_without_interactive`; an attribute is blamed one at a time by
markup name against the element's attribute set. This is the error-message
surface `html!` (slice H5) reuses. When the goal is not of either shape, or
an argument is not closed (a bound variable in a theorem, an unassigned
metavariable), the tactic falls back to `decide`, so it is never weaker.
-/

namespace Whatwg.Html.Admit

open Lean Meta Elab Tactic
open Whatwg.Html.Schema

/-- The constructor index of a constructor constant of the enum `induct`;
`none` for any other expression. -/
def enumIdx? (induct : Name) (e : Expr) : MetaM (Option Nat) := do
  let some n := e.constName? | return none
  match (← getEnv).find? n with
  | some (.ctorInfo c) => return if c.induct == induct then some c.cidx else none
  | _ => return none

/-- A closed `Tag` as a value. -/
def tag? (e : Expr) : MetaM (Option Tag) :=
  return (← enumIdx? ``Tag e).map Tag.ofNat

/-- A closed `Attr` as a value. -/
def attr? (e : Expr) : MetaM (Option Attr) :=
  return (← enumIdx? ``Attr e).map Attr.ofNat

/-- A closed `AttrSet` as a value. -/
def attrSet? (e : Expr) : MetaM (Option AttrSet) :=
  return (← enumIdx? ``AttrSet e).map AttrSet.ofNat

/-- A closed content set as a value: a constructor, or `childSet s t` with
closed arguments, nested to `fuel` levels (a transparent element inside a
transparent element nests once per level). -/
def contentSet? : Nat → Expr → MetaM (Option ContentSet)
  | 0, _ => return none
  | fuel + 1, e => do
    if let some i ← enumIdx? ``ContentSet e then return some (ContentSet.ofNat i)
    if e.isAppOfArity ``Whatwg.Html.childSet 2 then
      let some s ← contentSet? fuel (e.getArg! 0) | return none
      let some t ← tag? (e.getArg! 1) | return none
      return some (childSet s t)
    return none

/-- The attribute tag one entry of an attribute list names: a pair literal
whose first component is a closed `Attr`, or an application of a helper
`Whatwg.Html.A.<name>`, read through `attributeCtors` by that name. -/
def attrOfEntry? (e : Expr) : MetaM (Option Attr) := do
  if e.isAppOfArity ``Prod.mk 4 then return ← attr? (e.getArg! 2)
  let some n := e.getAppFn.constName? | return none
  unless n.getPrefix == `Whatwg.Html.A do return none
  let some row := attributeCtors.find? (·.name == n.getString!) | return none
  return some row.tag

/-- A closed attribute list as the list of its tags, to `fuel` entries. -/
def attrList? : Nat → Expr → MetaM (Option (List Attr))
  | 0, _ => return none
  | fuel + 1, e => do
    if e.isAppOfArity ``List.nil 1 then return some []
    if e.isAppOfArity ``List.cons 3 then
      let some a ← attrOfEntry? (e.getArg! 1) | return none
      let some rest ← attrList? fuel (e.getArg! 2) | return none
      return some (a :: rest)
    return none

/-- `Eq.refl true`, the proof of every obligation this tactic accepts: both
obligations unfold to an equation with `true` that the kernel decides by
evaluation. -/
def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- What the markup calls a tag, with text spelled out. -/
def describe (t : Tag) : String :=
  if t == .pcdata then "text" else "<" ++ t.markupText ++ ">"

/-- The tactic: see the module docstring. -/
syntax (name := admitsTactic) "admits" : tactic

@[tactic admitsTactic] def evalAdmits : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``Whatwg.Html.Content.Admits 2 then
    if let some set ← contentSet? 32 (ty.getArg! 0) then
      if let some t ← tag? (ty.getArg! 1) then
        unless Content.admits set t do
          throwError (describe t ++ " is not admitted here: the content set `"
            ++ set.name ++ "` does not name it")
        goal.assign reflTrue
        replaceMainGoal []
        return
  if ty.isAppOfArity ``Whatwg.Html.AttrsAdmitted 2 then
    if let some set ← attrSet? (ty.getArg! 0) then
      if let some attrs ← attrList? 256 (ty.getArg! 1) then
        if let some a := attrs.find? (fun a => !set.contains a) then
          throwError ("attribute `" ++ a.markupName ++ "` is not admitted on this element: "
            ++ "the attribute set `" ++ set.name ++ "` does not name it")
        goal.assign reflTrue
        replaceMainGoal []
        return
  evalTactic (← `(tactic| decide))

end Whatwg.Html.Admit
