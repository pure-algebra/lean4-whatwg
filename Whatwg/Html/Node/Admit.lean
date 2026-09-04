import Lean
import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Admit

The `admits` tactic: the auto-parameter tactic of every combinator in
`Whatwg.Html.Node.Combinators`, discharging the two obligations of the typed
tree, `ctx.admits t = true`, `attrsOk t (rawAttrs attrs) = true` and
`seqOk (ctx.child t) t children = true`, without
asking the elaborator to reduce the obligation itself.

The obligations are closed terms over a finite schema whose functions are
compiled. The tactic reads the context back as a value (`whnf` to its
constructor, then each field), the tag as a constructor, the attribute
list as pairs of literals, evaluates `Ctx.admits` or `attrsOk` as ordinary
functions, and closes the goal with `Eq.refl true`. The kernel re-evaluates
the obligation when the declaration is added, so the compiled evaluation
decides only whether to mint the proof or to report. On a false obligation
the tactic names the element (or text, or attribute) and describes the
context in prose. When the goal is not of either shape, or is not closed,
it falls back to `decide`.
-/

namespace Whatwg.Html.Admit

open Lean Meta Elab Tactic
open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx)

def enumIdx? (induct : Name) (e : Expr) : MetaM (Option Nat) := do
  let some n := e.constName? | return none
  match (← getEnv).find? n with
  | some (.ctorInfo c) => return if c.induct == induct then some c.cidx else none
  | _ => return none

def tag? (e : Expr) : MetaM (Option Tag) := do
  return (← enumIdx? ``Tag (← whnf e)).map Tag.ofNat

def base? (e : Expr) : MetaM (Option Base) := do
  return (← enumIdx? ``Base (← whnf e)).map Base.ofNat

def bool? (e : Expr) : MetaM (Option Bool) := do
  let e ← whnf e
  if e.isConstOf ``Bool.true then return some true
  if e.isConstOf ``Bool.false then return some false
  return none

/-- A closed `Exclusions` as a value. -/
def excl? (e : Expr) : MetaM (Option Exclusions) := do
  let e ← whnf e
  unless e.isAppOfArity ``Exclusions.mk 15 do return none
  let args := e.getAppArgs
  let mut bs : Array Bool := #[]
  for a in args do
    let some b ← bool? a | return none
    bs := bs.push b
  return some (Exclusions.mk bs[0]! bs[1]! bs[2]! bs[3]! bs[4]! bs[5]! bs[6]! bs[7]! bs[8]! bs[9]!
    bs[10]! bs[11]! bs[12]! bs[13]! bs[14]!)

/-- A closed list as values, to `fuel` cells. -/
def list? {α} (elem : Expr → MetaM (Option α)) : Nat → Expr → MetaM (Option (List α))
  | 0, _ => return none
  | fuel + 1, e => do
    let e ← whnf e
    if e.isAppOfArity ``List.nil 1 then return some []
    if e.isAppOfArity ``List.cons 3 then
      let some x ← elem (e.getArg! 1) | return none
      let some rest ← list? elem fuel (e.getArg! 2) | return none
      return some (x :: rest)
    return none

/-- A closed context as a value. A `Ctx.child c t` application is read
without reducing it: the parent is read and the compiled `Ctx.child` applied,
so a context nested `d` deep costs `d` steps, not `d` reductions of fifteen
fields each. Anything else is reduced to its constructor. -/
def ctx? : Nat → Expr → MetaM (Option Ctx)
  | 0, _ => return none
  | fuel + 1, e => do
    let e ← instantiateMVars e
    if e.isAppOfArity ``Ctx.child 2 then
      let some c ← ctx? fuel (e.getArg! 0) | return none
      let some t ← tag? (e.getArg! 1) | return none
      return some (c.child t)
    let e ← whnf e
    if e.isAppOfArity ``Ctx.child 2 then
      let some c ← ctx? fuel (e.getArg! 0) | return none
      let some t ← tag? (e.getArg! 1) | return none
      return some (c.child t)
    unless e.isAppOfArity ``Ctx.mk 3 do return none
    let some b ← base? (e.getArg! 0) | return none
    let some x ← excl? (e.getArg! 1) | return none
    let some extra ← list? tag? 64 (e.getArg! 2) | return none
    return some { base := b, excl := x, extra }

/-- A closed character: a literal `Char.ofNat n`. -/
def char? (e : Expr) : MetaM (Option Char) := do
  let e ← whnf e
  if e.isAppOfArity ``Char.ofNat 1 then
    let n ← whnf (e.getArg! 0)
    match n with
    | .lit (.natVal v) => return some (Char.ofNat v)
    | _ => return none
  return none

/-- A closed string: a literal, or `String.mk` of a closed character list,
which is what a computed name such as `"data-" ++ suffix` reduces to. -/
def str? (e : Expr) : MetaM (Option String) := do
  let e ← whnf e
  match e with
  | .lit (.strVal v) => return some v
  | _ =>
    if e.isAppOfArity ``String.mk 1 then
      let some cs ← list? char? 4096 (e.getArg! 0) | return none
      return some (String.ofList cs)
    return none

/-- A closed raw attribute list as values. -/
def rawAttrs? (e : Expr) : MetaM (Option (List (String × String))) :=
  list? (fun p => do
    let p ← whnf p
    unless p.isAppOfArity ``Prod.mk 4 do return none
    let some n ← str? (p.getArg! 2) | return none
    let some v ← str? (p.getArg! 3) | return none
    return some (n, v)) 256 e

def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Bool) (mkConst ``Bool.true)

def describe (t : Tag) : String :=
  if t == .pcdata then "text" else "<" ++ t.markupText ++ ">"

/-- The tag a raw-node expression counts as in a sequence: `none` for a
comment or an unreadable node, `some none`... rather: `some (some t)` for
a tag, `some none` for a comment, `none` when the node cannot be read. -/
def rawTag? (e : Expr) : MetaM (Option (Option Tag)) := do
  let e ← whnf e
  if e.isAppOfArity ``Whatwg.Html.RawNode.element 3 then
    let some n ← str? (e.getArg! 0) | return none
    return some (Tag.ofName? n)
  if e.isAppOfArity ``Whatwg.Html.RawNode.text 1 || e.isAppOfArity ``Whatwg.Html.RawNode.entity 1 then
    return some (some .pcdata)
  if e.isAppOfArity ``Whatwg.Html.RawNode.comment 1 then return some none
  return none

/-- The tags of a closed child list, comments dropped, as `childTags` computes
them. -/
def childTags? (e : Expr) : MetaM (Option (List Tag)) := do
  let some xs ← list? rawTag? 4096 e | return none
  return some (xs.filterMap id)

/-- The message for a rejected admission. -/
def admitMessage (c : Ctx) (t : Tag) : String :=
  describe t ++ " is not admitted here: the context is " ++ c.describe

syntax (name := admitsTactic) "admits" : tactic

@[tactic admitsTactic] def evalAdmits : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``Eq 3 then
    let lhs := ty.getArg! 1
    if lhs.isAppOfArity ``Ctx.admits 2 then
      if let some c ← ctx? 4096 (lhs.getArg! 0) then
        if let some t ← tag? (lhs.getArg! 1) then
          unless c.admits t do throwError admitMessage c t
          goal.assign reflTrue
          replaceMainGoal []
          return
    if lhs.isAppOfArity ``Whatwg.Html.Content.seqOk 3 then
      if let some t ← tag? (lhs.getArg! 1) then
        if t.seq?.isNone then
          goal.assign reflTrue
          replaceMainGoal []
          return
        if let some c ← ctx? 4096 (lhs.getArg! 0) then
          if let some ts ← childTags? (lhs.getArg! 2) then
            -- rebuild a raw list with only the tags, which is all `seqOk` reads
            let raws := ts.map fun tg => if tg == .pcdata then Whatwg.Html.RawNode.text "" else
              Whatwg.Html.RawNode.element tg.markupText [] []
            if let some problem := Whatwg.Html.Content.seqProblem? c t raws then throwError problem
            goal.assign reflTrue
            replaceMainGoal []
            return
    if lhs.isAppOfArity ``Whatwg.Html.Content.attrsOk 2 then
      if let some t ← tag? (lhs.getArg! 0) then
        if let some attrs ← rawAttrs? (lhs.getArg! 1) then
          for (n, v) in attrs do
            if let some problem := Whatwg.Html.Content.attrProblem? t n v then
              throwError problem
          let names := attrs.map (·.1)
          if names.eraseDups.length != names.length then
            throwError ("an attribute is given twice on " ++ describe t)
          goal.assign reflTrue
          replaceMainGoal []
          return
  evalTactic (← `(tactic| decide))

end Whatwg.Html.Admit
