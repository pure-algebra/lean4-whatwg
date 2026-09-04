import Lean
import Whatwg.Html.Node.Admit
import Whatwg.Html.Node.Evidence

/-!
# Whatwg.Html.Syntax.Elaborator

`html!`, the markup surface over the typed tree (slice H5 of
`docs/HTML-PACKAGE-PLAN.md`; ruling R7 there says why this is an elaborator
and not a macro):

```lean
def page : Element .div .flow5 :=
  html! <div class="lead"><p>"Hello, " <em>"world"</em></p><br /></div>
```

Text is a string literal, `{e}` splices a `Child` term (or a `String` term in
an attribute value), a void element is written `<br />`, and a bare
attribute name is a presence attribute whose value is its own name, which is
what TyXML prints for `a_hidden ()`. The Lean keywords among the markup
names (`section`, `meta`, `class`, `for`, `open`) are accepted where an
element or attribute name is expected.

## What the elaborator does

The document is walked once at the meta level. The context of every
position is a `Whatwg.Html.Content.Ctx` value, computed by the same
compiled `Ctx.child` the checker uses, and every admission is decided by
the compiled `Ctx.admits`, so the diagnostic at a rejected token names the
element and describes the context (`<div>` under a link in a paragraph
reports "phrasing, excluding interactive content, a"). Attribute values
that are literals are checked against the attribute index's kinds by the
compiled `attrProblem?`. The term produced is `Element.ofRaw` at every
element: the raw children as a plain literal and the proof that they are
valid at `Ctx.child`, assembled from `Content.validAll_cons` and
`Element.valid` node by node, so the kernel checks each node once against
the literal and the compiler erases every proof. No `elabApp`, no
unification and no tactic runs per node.

## Memoization

Every leaf obligation is `Eq.refl true`, which the kernel checks by
evaluating the obligation. With `whatwg.html.memo` (the default) each
distinct admission and attribute obligation is minted once per module as
an auxiliary lemma through `Lean.Meta.mkAuxLemma`, and the root's validity
proof is one lemma, so that the compiled term holds a constant where the
proof tree was.

## The root's context

The root takes its context from the expected type, `Child ctx` or
`Element t ctx`, read through `whnf`; without one it takes `Ctx.document`
for `html`, `Ctx.flow` for flow content, `Ctx.phrasing` for phrasing
content, `Ctx.metadata` for metadata content, and `Ctx.flow` otherwise.

## What is not here

Attribute values are `String`; comments and entities have no markup form.

The walker recurses on a fuel that starts at 4096 levels of nesting, which
no well-formed document exhausts; the trust gate forbids `partial`.
-/

namespace Whatwg.Html.Syntax

open Lean Elab Term Meta
open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx)

register_option whatwg.html.memo : Bool := {
  defValue := true
  descr := "html!: mint one auxiliary lemma per distinct obligation and reuse it (true), or a fresh Eq.refl per node (false)"
}

/-! ## Syntax -/

declare_syntax_cat htmlName
/-- An element or attribute name. -/
syntax ident : htmlName
syntax "section" : htmlName
syntax "meta" : htmlName
syntax "class" : htmlName
syntax "for" : htmlName
syntax "open" : htmlName

declare_syntax_cat htmlAttr
/-- `name`, `name="literal"`, `name={term}`; dashes join names. -/
syntax (name := htmlAttrNode) htmlName ("-" htmlName)* ("=" (str <|> ("{" term "}")))? : htmlAttr

declare_syntax_cat htmlNode
/-- A self-closing element. -/
syntax (name := htmlVoid) "<" htmlName htmlAttr* "/>" : htmlNode
/-- An element with children. -/
syntax (name := htmlElem) "<" htmlName htmlAttr* ">" htmlNode* "</" htmlName ">" : htmlNode
/-- A text run. -/
syntax (name := htmlText) str : htmlNode
/-- A spliced `Child` term. -/
syntax (name := htmlSplice) "{" term "}" : htmlNode

/-- The markup term. -/
syntax (name := htmlTerm) "html!" htmlNode : term

/-! ## Expressions of schema values -/

/-- The string a name node spells. -/
def nameString (stx : Syntax) : String :=
  match stx[0] with
  | .ident _ _ n _ => n.eraseMacroScopes.toString
  | .atom _ v => v
  | _ => ""

def ctorExpr (induct : Name) (idx : Nat) : MetaM Expr := do
  let info ← getConstInfoInduct induct
  return mkConst info.ctors[idx]!

def tagExpr (t : Tag) : MetaM Expr := ctorExpr ``Tag t.ctorIdx
def baseExpr (b : Base) : MetaM Expr := ctorExpr ``Base b.ctorIdx
def attrExpr (a : Attr) : MetaM Expr := ctorExpr ``Attr a.ctorIdx
def boolExpr (b : Bool) : Expr := mkConst (if b then ``Bool.true else ``Bool.false)

def exclExpr (x : Exclusions) : Expr :=
  mkAppN (mkConst ``Exclusions.mk) (x.flags.toArray.map boolExpr)

/-- A context as a structure literal. -/
def ctxExpr (c : Ctx) : MetaM Expr := do
  let extra ← mkListLit (mkConst ``Tag) (← c.extra.mapM tagExpr)
  return mkApp3 (mkConst ``Ctx.mk) (← baseExpr c.base) (exclExpr c.excl) extra

/-- Elaborate a spliced term against a type and settle it. -/
def elabClosed (stx : Syntax) (type : Expr) : TermElabM Expr := do
  let e ← elabTermEnsuringType stx type
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- A proof of a closed obligation `lhs = true`: `Eq.refl true`, minted
once per distinct type when memoizing. -/
def proofOf (lhs : Expr) : TermElabM Expr := do
  let type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
  if whatwg.html.memo.get (← getOptions) then
    return Lean.mkConst (← mkAuxLemma [] type Admit.reflTrue)
  return Admit.reflTrue

def admitsProof (ctxE : Expr) (t : Tag) : TermElabM Expr := do
  proofOf (mkApp2 (mkConst ``Ctx.admits) ctxE (← tagExpr t))

/-! ## Attributes -/

structure AttrOut where
  tag : Attr
  markup : String
  value : Expr

/-- Elaborate the attributes of an element, blaming one token at a time, and
check every literal value against the index. -/
def elabAttrs (t : Tag) (stxs : Array Syntax) : TermElabM (Array AttrOut) := do
  let mut out : Array AttrOut := #[]
  let name := t.markupText
  for stx in stxs do
    let mut markup := nameString stx[1 - 1]
    for part in stx[1].getArgs do
      markup := markup ++ "-" ++ nameString part[1]
    if out.any (·.markup == markup) then
      throwErrorAt stx ("attribute `" ++ markup ++ "` is given twice on <" ++ name ++ ">")
    let a ← if Whatwg.Html.Content.hasPrefix "data-" markup then pure Attr.data_
      else if Whatwg.Html.Content.hasPrefix "aria-" markup then pure Attr.aria_
      else match Attr.ofName? markup with
        | some a => pure a
        | none => throwErrorAt stx ("unknown attribute `" ++ markup ++ "`")
    let opt := stx[2]
    let presence := opt.getNumArgs == 0
    let literal? : Option String := if presence then some "" else opt[1].isStrLit?
    match literal? with
    | some v =>
      if let some problem := Whatwg.Html.Content.attrProblem? t markup v then throwErrorAt stx problem
    | none =>
      if let some problem := Whatwg.Html.Content.attrProblem? t markup "" then
        -- a spliced value: only the admission of the name is checked
        if problem.startsWith ("attribute `" ++ markup ++ "` is not admitted") || problem.startsWith "unknown" then
          throwErrorAt stx problem
    let value ← if presence then pure (mkStrLit "") else
      let v := opt[1]
      match v.isStrLit? with
      | some s => pure (mkStrLit s)
      | none => elabClosed v[1] (mkConst ``String)
    out := out.push { tag := a, markup, value }
  return out

def attrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  let vals ← attrs.toList.mapM fun a => do
    return mkApp3 (mkConst ``AttrVal.mk) (← attrExpr a.tag) (mkStrLit a.markup) a.value
  mkListLit (mkConst ``AttrVal) vals

def rawAttrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
  let pairs := attrs.toList.map fun a =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
      (mkStrLit a.markup) a.value
  mkListLit pairT pairs

/-! ## The walk -/

structure Open where
  nameStx : Syntax
  tag : Tag
  attrs : Array Syntax
  kids : Array Syntax

def openOf (stx : Syntax) : TermElabM (Option Open) := do
  if stx.isOfKind ``htmlVoid then
    let name := nameString stx[1]
    let some tag := Tag.ofName? name | throwErrorAt stx[1] ("unknown element <" ++ name ++ ">")
    return some { nameStx := stx[1], tag, attrs := stx[2].getArgs, kids := #[] }
  if stx.isOfKind ``htmlElem then
    let name := nameString stx[1]
    let some tag := Tag.ofName? name | throwErrorAt stx[1] ("unknown element <" ++ name ++ ">")
    let closing := nameString stx[6]
    unless closing == name do
      throwErrorAt stx[6] ("closing tag </" ++ closing ++ "> does not match <" ++ name ++ ">")
    return some { nameStx := stx[1], tag, attrs := stx[2].getArgs, kids := stx[4].getArgs }
  return none

/-- Elaborate an element placed in the context `ctx` (as a value and as the
expression `ctxE`): the raw literal and a term of type `Element tag ctx`. -/
def elabElement : Nat → Open → Ctx → Expr → Bool → TermElabM (Expr × Expr)
  | 0, o, _, _, _ => throwErrorAt o.nameStx "html!: the document nests too deeply"
  | fuel + 1, o, ctx, ctxE, root => do
    let t := o.tag
    let name := t.markupText
    if t.isVoid && !o.kids.isEmpty then
      throwErrorAt o.nameStx ("<" ++ name ++ "> is a void element and takes no children")
    let tE ← tagExpr t
    let inner := ctx.child t
    let innerE := mkApp2 (mkConst ``Ctx.child) ctxE tE
    let rawT := Lean.mkConst ``RawNode
    let mut raws : Array Expr := #[]
    let mut steps : Array (Expr → Expr → Expr → Expr) := #[]
    for kid in o.kids do
      if kid.isOfKind ``htmlText then
        let some s := kid[0].isStrLit? | throwErrorAt kid "html!: malformed text"
        unless inner.admits .pcdata do
          throwErrorAt kid ("text is not admitted here: the context is " ++ inner.describe)
        let h ← admitsProof innerE .pcdata
        let raw := mkApp (mkConst ``RawNode.text) (mkStrLit s)
        raws := raws.push raw
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            mkApp3 (mkConst ``Whatwg.Html.Content.validIn_text) innerE (mkStrLit s) h, hrest]
      else if kid.isOfKind ``htmlSplice then
        let child ← elabClosed kid[1] (mkApp (mkConst ``Child) innerE)
        raws := raws.push (mkApp2 (mkConst ``Child.raw) innerE child)
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            mkApp2 (mkConst ``Child.valid) innerE child, hrest]
      else
        let some k ← openOf kid | throwErrorAt kid "html!: unsupported node"
        let c := k.tag
        unless inner.admits c do
          throwErrorAt k.nameStx (Admit.admitMessage inner c)
        let (raw, e) ← elabElement fuel k inner innerE false
        let h ← admitsProof innerE c
        raws := raws.push raw
        let cE ← tagExpr c
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            mkAppN (mkConst ``Element.valid) #[cE, innerE, e, h], hrest]
    let mut rest ← mkListLit rawT []
    let mut hc := mkApp (mkConst ``Whatwg.Html.Content.validAll_nil) innerE
    for i in [0:steps.size] do
      let j := steps.size - 1 - i
      hc := steps[j]! raws[j]! rest hc
      rest := mkApp3 (mkConst ``List.cons [Level.zero]) rawT raws[j]! rest
    let childrenE := rest
    let attrs ← elabAttrs t o.attrs
    let attrsE ← attrsTerm attrs
    let rawAttrsE ← rawAttrsTerm attrs
    let raw := mkApp3 (mkConst ``RawNode.element) (mkStrLit name) rawAttrsE childrenE
    let ha ← proofOf (mkApp2 (mkConst ``Whatwg.Html.Content.attrsOk) tE (mkApp (mkConst ``rawAttrs) attrsE))
    -- the ordered model, checked on the children's tags as written
    let kidTags := o.kids.toList.filterMap fun kid =>
      if kid.isOfKind ``htmlText then some (Whatwg.Html.RawNode.text "")
      else if kid.isOfKind ``htmlSplice then none
      else match Tag.ofName? (nameString kid[1]) with
        | some tg => some (Whatwg.Html.RawNode.element tg.markupText [] [])
        | none => none
    if o.kids.all (fun kid => !kid.isOfKind ``htmlSplice) then
      if let some problem := Whatwg.Html.Content.seqProblem? inner t kidTags then
        throwErrorAt o.nameStx problem
    let hs ← proofOf (mkApp3 (mkConst ``Whatwg.Html.Content.seqOk) innerE tE childrenE)
    let ht ← proofOf (mkApp2 (mkConst ``Option.isSome [Level.zero]) (mkConst ``String) (mkApp (mkConst ``Tag.markupName) tE))
    let evidence ← if root then do
        let type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
          (mkApp2 (mkConst ``Whatwg.Html.Content.validAll) innerE childrenE) (mkConst ``Bool.true)
        pure (Lean.mkConst (← mkAuxLemma [] type (← instantiateMVars hc)))
      else pure hc
    return (raw, mkAppN (mkConst ``Element.ofRaw) #[tE, ctxE, attrsE, childrenE, ha, hs, evidence, ht])

/-- The default context of a root, by the root's categories. -/
def defaultCtx (t : Tag) : Ctx :=
  if t == .html then Ctx.document
  else if Cats.flow t then Ctx.flow
  else if Cats.phrasing t then Ctx.phrasing
  else if Cats.metadata t then Ctx.metadata
  else Ctx.flow

@[term_elab htmlTerm] def elabHtml : TermElab := fun stx expectedType? => do
  let node := stx[1]
  let some o ← openOf node | throwErrorAt node "html!: the root must be an element"
  let fuel := 4096
  let t := o.tag
  let expectedType? ← tryPostponeIfHasMVars? expectedType?
  let expected := expectedType?.map fun e => e.consumeMData
  if let some e := expected then
    if e.isAppOfArity ``Child 1 then
      if let some ctx ← Admit.ctx? 4096 (e.getArg! 0) then
        unless ctx.admits t do throwErrorAt o.nameStx (Admit.admitMessage ctx t)
        let ctxE := e.getArg! 0
        let (_, elem) ← elabElement fuel o ctx ctxE true
        return mkApp4 (mkConst ``Child.of) (← tagExpr t) ctxE elem (← admitsProof ctxE t)
    if e.isAppOfArity ``Element 2 then
      if let some t' ← Admit.tag? (e.getArg! 0) then
        unless t' == t do
          throwErrorAt o.nameStx ("the expected type names <" ++ t'.markupText ++ "> but the root is <" ++ t.markupText ++ ">")
        if let some ctx ← Admit.ctx? 4096 (e.getArg! 1) then
          return (← elabElement fuel o ctx (e.getArg! 1) true).2
  let ctx := defaultCtx t
  return (← elabElement fuel o ctx (← ctxExpr ctx) true).2

end Whatwg.Html.Syntax
