import Lean
import Whatwg.Html.Node.Typed
import Whatwg.Html.Content.Explain
import Whatwg.Html.Node.Splice

/-!
# Whatwg.Html.Node.Admit

The `admits` tactic: the auto-parameter tactic of every combinator in
`Whatwg.Html.Node.Combinators`, discharging the three obligations of the typed
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

Since slice S3e of `docs/SVG-PACKAGE-PLAN.md` the tactic also closes a whole
tree: a goal `validIn ctx n = true` or `validAll ctx ns = true` over a closed
raw tree, with SVG subtrees or without. It reads the tree back as a value and
evaluates the located refusal, `Whatwg.Html.Content.explain`. When the
refusal is absent it closes the goal with `Eq.refl true`. Otherwise it reports
the refusal: the node, its path and the reason. `explain_none_iff` says that
this report is complete: the tactic has something to say exactly when the
checker refuses.

Since the second round of slice S17 the tactic also closes an obligation whose
tree holds a part that is data (entries W8, W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`; the laws are those of
`Whatwg/Html/Node/Splice.lean`):

- A name that is computed from closed parts, `"aria-" ++ "label"`, is read as
  its text (`str?`).
- A value that is no closed string is left unread. The attribute must then
  pass `Content.attrFree`, the checker's test with the test of the value left
  out, and the kernel checks the obligation with the value free. An attribute
  whose value has a rule is refused with words, and so is an admission that
  reads such a value (`input` and its `type`).
- An attribute list that is not written out, `(f x).attrs`, is no obstacle to
  the admission of an element whose categories read no attribute
  (`Content.unconditional`): the proof is `Ctx.admitsWith_unread`.
- An attribute that may be absent, `A.opt make o`, is proved by cases on `o`:
  the two obligations are closed as above, the second with its value free.
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

/-- The two sides of an append of strings, in any of its three spellings. -/
def append? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.getArg! 4, e.getArg! 5)
  else if e.isAppOfArity ``Append.append 4 then some (e.getArg! 2, e.getArg! 3)
  else if e.isAppOfArity ``String.append 2 then some (e.getArg! 0, e.getArg! 1)
  else none

/-- A string made of closed parts, read one step at a time, to `fuel` steps: a
literal, or an append of two such strings. A step is a reduction that unfolds
no definition, or one definition unfolded. An append is so met before it is
unfolded: the normal form of a computed name such as `"aria-" ++ suffix` is
bytes, which `str?` does not read. -/
def strSteps? : Nat → Expr → MetaM (Option String)
  | 0, _ => return none
  | fuel + 1, e => do
    let e ← instantiateMVars e
    if let .lit (.strVal v) := e then return some v
    if let some (left, right) := append? e then
      let some left ← strSteps? fuel left | return none
      let some right ← strSteps? fuel right | return none
      return some (left ++ right)
    let reduced ← whnfCore e
    if reduced != e then return ← strSteps? fuel reduced
    let some unfolded ← unfoldDefinition? e | return none
    strSteps? fuel unfolded

/-- A closed string: a literal or an append of closed strings (`strSteps?`), or
`String.mk` of a closed character list. -/
def str? (e : Expr) : MetaM (Option String) := do
  if let some s ← strSteps? 64 e then return some s
  let e ← whnf e
  match e with
  | .lit (.strVal v) => return some v
  | _ =>
    if e.isAppOfArity ``String.mk 1 then
      let some cs ← list? char? 4096 (e.getArg! 0) | return none
      return some (String.ofList cs)
    return none

/-- A raw attribute list whose names are closed: each name, and each value that
is a closed string. A value that is none is `none`: data, such as an address
that a program computes. -/
def looseAttrs? (e : Expr) : MetaM (Option (List (String × Option String))) :=
  list? (fun p => do
    let p ← whnf p
    unless p.isAppOfArity ``Prod.mk 4 do return none
    let some n ← str? (p.getArg! 2) | return none
    return some (n, ← str? (p.getArg! 3))) 256 e

/-- A closed raw attribute list as values. -/
def rawAttrs? (e : Expr) : MetaM (Option (List (String × String))) := do
  let some attrs ← looseAttrs? e | return none
  return attrs.mapM fun attr => attr.2.map fun v => (attr.1, v)

/-- A closed raw node as a value, to `fuel` levels of nesting. -/
def rawNode? : Nat → Expr → MetaM (Option Whatwg.Html.RawNode)
  | 0, _ => return none
  | fuel + 1, e => do
    let e ← whnf e
    if e.isAppOfArity ``Whatwg.Html.RawNode.element 3 then
      let some name ← str? (e.getArg! 0) | return none
      let some attrs ← rawAttrs? (e.getArg! 1) | return none
      let some children ← list? (rawNode? fuel) 4096 (e.getArg! 2) | return none
      return some (.element name attrs children)
    if e.isAppOfArity ``Whatwg.Html.RawNode.text 1 then
      let some s ← str? (e.getArg! 0) | return none
      return some (.text s)
    if e.isAppOfArity ``Whatwg.Html.RawNode.entity 1 then
      let some s ← str? (e.getArg! 0) | return none
      return some (.entity s)
    if e.isAppOfArity ``Whatwg.Html.RawNode.comment 1 then
      let some s ← str? (e.getArg! 0) | return none
      return some (.comment s)
    return none

/-- A node in a few words, for a message. -/
def nodeWords : Whatwg.Html.RawNode → String
  | .element name _ _ => "<" ++ name ++ ">"
  | .text _ => "text"
  | .entity _ => "an entity"
  | .comment _ => "a comment"

/-- The message for a located refusal in a tree: the refused node, its path of child indices
from the root, and the reason. -/
def refusalMessage (root : Whatwg.Html.RawNode) (refusal : Whatwg.Html.Content.Refusal) : String :=
  let what := match root.at? refusal.path with
    | some node => nodeWords node
    | none => "a node"
  what ++ " at path " ++ toString refusal.path ++ ": " ++ refusal.reason.describe

def reflTrue : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Bool) (mkConst ``Bool.true)

def describe (t : Tag) : String :=
  if t == .pcdata then "text" else "<" ++ t.markupText ++ ">"

/-- The tag a raw-node expression counts as in a sequence: `some (some t)` for
a tag, `some none` for a comment, and `none` when the node cannot be read. -/
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

/-- Why the element does not take an attribute of this name, whatever its
value; `none` when it takes one. -/
def nameProblem? (t : Tag) (name : String) : Option String :=
  if Whatwg.Html.Content.isPrefixed name then none else
  match Attr.ofName? name with
  | none => some ("unknown attribute `" ++ name ++ "`")
  | some a =>
    match t.attribs? with
    | none => some ("<" ++ t.markupText ++ "> takes no attributes")
    | some set =>
      if set.contains a then none else Whatwg.Html.Content.attrProblem? t name ""

/-- Why an attribute list is refused on the element, where a value may be data
(`none`). A closed value is judged as the attribute index states it. A value
that is data is not read: its attribute must be one whose value the checker
does not read (`Content.attrFree`). Then a name that repeats. `none` when the
kernel can check the list with those values free. -/
def attrsProblem? (t : Tag) (attrs : List (String × Option String)) : Option String :=
  let each := attrs.findSome? fun attr =>
    match attr.2 with
    | some value => Whatwg.Html.Content.attrProblem? t attr.1 value
    | none =>
      if Whatwg.Html.Content.attrFree t attr.1 then none
      else some ((nameProblem? t attr.1).getD
        ("the value of `" ++ attr.1 ++ "` on " ++ describe t ++ " is no literal, and the " ++
          "checker reads the value of this attribute: write a literal, or case on the value"))
  each.orElse fun _ =>
    let names := attrs.map (·.1)
    if names.eraseDups.length != names.length then
      some ("an attribute is given twice on " ++ describe t)
    else none

/-- The attributes as a test that reads no data is given them: an empty text
where a value is data. -/
def blanks (attrs : List (String × Option String)) : List (String × String) :=
  attrs.map fun attr => (attr.1, attr.2.getD "")

/-- The attribute whose value a conditional category of the element reads,
when that value is data: the admission cannot then be evaluated. -/
def conditionReads? (t : Tag) (attrs : List (String × Option String)) : Option String :=
  [t.interactiveIf, t.flowIf, t.phrasingIf].findSome? fun condition =>
    match condition with
    | some (.attrNot name _) =>
      if attrs.any (fun attr => attr.1 == name && attr.2.isNone) then some name else none
    | _ => none

/-- The option of an attribute that may be absent, `A.opt make o`, somewhere in
the obligation, when `o` is not yet `none` or `some`. -/
def openOption? (e : Expr) : Option Expr :=
  (e.find? fun sub =>
    sub.isAppOfArity ``Whatwg.Html.A.opt 3 && !sub.hasLooseBVars &&
      !(sub.getArg! 2).isAppOf ``Option.none && !(sub.getArg! 2).isAppOf ``Option.some).map
    (·.getArg! 2)

syntax (name := admitsTactic) "admits" : tactic

/-- The tactic, to `fuel` attributes that may be absent in one obligation. -/
def admitsCore : Nat → TacticM Unit
  | 0 => do evalTactic (← `(tactic| decide))
  | fuel + 1 => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``Eq 3 then
    let lhs := ty.getArg! 1
    if lhs.isAppOfArity ``Whatwg.Html.Content.validIn 2 then
      if let some c ← ctx? 4096 (lhs.getArg! 0) then
        if let some node ← rawNode? 4096 (lhs.getArg! 1) then
          if let some refusal := Whatwg.Html.Content.explain c node then
            throwError refusalMessage node refusal
          goal.assign reflTrue
          replaceMainGoal []
          return
    if lhs.isAppOfArity ``Whatwg.Html.Content.validAll 2 then
      if let some c ← ctx? 4096 (lhs.getArg! 0) then
        if let some nodes ← list? (rawNode? 4096) 4096 (lhs.getArg! 1) then
          for node in nodes do
            if let some refusal := Whatwg.Html.Content.explain c node then
              throwError refusalMessage node refusal
          goal.assign reflTrue
          replaceMainGoal []
          return
    if lhs.isAppOfArity ``Ctx.admits 2 then
      if let some c ← ctx? 4096 (lhs.getArg! 0) then
        if let some t ← tag? (lhs.getArg! 1) then
          unless c.admits t do throwError admitMessage c t
          goal.assign reflTrue
          replaceMainGoal []
          return
    if lhs.isAppOfArity ``Ctx.admitsWith 3 then
      if let some c ← ctx? 4096 (lhs.getArg! 0) then
        if let some t ← tag? (lhs.getArg! 1) then
          if let some attrs ← looseAttrs? (lhs.getArg! 2) then
            if let some name := conditionReads? t attrs then
              throwError ("whether " ++ describe t ++ " is admitted here reads the value of `" ++
                name ++ "`, which is no literal: write a literal, or case on the value")
            unless c.admitsWith t (blanks attrs) do throwError admitMessage c t
            goal.assign reflTrue
            replaceMainGoal []
            return
          -- the attributes are not written out: `E.el e` for a variable `e`
          if Whatwg.Html.Content.unconditional t then
            unless c.admits t do throwError admitMessage c t
            goal.assign (mkAppN (mkConst ``Whatwg.Html.Content.Ctx.admitsWith_unread)
              #[lhs.getArg! 0, lhs.getArg! 1, lhs.getArg! 2, reflTrue, reflTrue])
            replaceMainGoal []
            return
    if lhs.isAppOfArity ``Whatwg.Html.Content.elementOk 4 then
      if let some t ← tag? (lhs.getArg! 1) then
        if let some attrs ← looseAttrs? (lhs.getArg! 2) then
          if let some problem := attrsProblem? t attrs then throwError problem
          if t.seq?.isNone then
            goal.assign reflTrue
            replaceMainGoal []
            return
          if let some c ← ctx? 4096 (lhs.getArg! 0) then
            if let some ts ← childTags? (lhs.getArg! 3) then
              let raws := ts.map fun tg => if tg == .pcdata then Whatwg.Html.RawNode.text "" else
                Whatwg.Html.RawNode.element tg.markupText [] []
              if let some problem := Whatwg.Html.Content.seqProblem? (c.child t) t raws then throwError problem
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
        if let some attrs ← looseAttrs? (lhs.getArg! 1) then
          if let some problem := attrsProblem? t attrs then throwError problem
          goal.assign reflTrue
          replaceMainGoal []
          return
  -- An attribute that may be absent: the obligation is proved for either case. The proof is
  -- `Option.casesOn` at the obligation with the option abstracted. It is built here and not by
  -- the tactics `generalize` and `cases`, which check the type of the abstracted obligation:
  -- that check would evaluate, in the elaborator, every proof the obligation holds.
  if let some option := openOption? ty then
    let optionType ← whnfR (← inferType option)
    if optionType.isAppOfArity ``Option 1 then
      let rest := (← getGoals).drop 1
      let α := optionType.getArg! 0
      let levels := optionType.getAppFn.constLevels!
      let body ← kabstract ty option
      let noneGoal ← mkFreshExprSyntheticOpaqueMVar
        (body.instantiate1 (mkApp (mkConst ``Option.none levels) α))
      let someType ← withLocalDeclD `value α fun value =>
        mkForallFVars #[value]
          (body.instantiate1 (mkApp2 (mkConst ``Option.some levels) α value))
      let someGoal ← mkFreshExprSyntheticOpaqueMVar someType
      goal.assign (mkAppN (mkConst ``Option.casesOn (Level.zero :: levels))
        #[α, mkLambda `option .default optionType body, option, noneGoal, someGoal])
      let (_, someInner) ← someGoal.mvarId!.intro `value
      for subgoal in [noneGoal.mvarId!, someInner] do
        setGoals [subgoal]
        subgoal.withContext (admitsCore fuel)
      setGoals rest
      return
  evalTactic (← `(tactic| decide))

@[tactic admitsTactic] def evalAdmits : Tactic := fun _ => admitsCore 8

end Whatwg.Html.Admit
