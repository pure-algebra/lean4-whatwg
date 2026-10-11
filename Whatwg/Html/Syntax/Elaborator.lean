import Lean
import Std.Data.HashMap
import Whatwg.Html.Content.Values
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
evaluating the obligation. The root's validity proof is one auxiliary lemma,
so that the compiled term holds a constant where the proof tree was. No
lemma is minted per leaf: the kernel's own cache already shares identical
obligations within a declaration once the children's contexts are emitted as
reduced literals, and a lemma per distinct obligation cost more kernel time
and never shared across declarations (performance review §7). That route sat
behind an option `whatwg.html.memo`, off by default, until the package
merged with the trust gate, which refuses the `opaque` a registered option
declares; `WhatwgTest/Html/MarkupBenchmark.lean` keeps its measurement.

## The closing tag

A closing tag is the two tokens `<` and `/`, written `</p>` as in markup.
The grammar declares no `</` token, because the trust gate's token rule
refuses a token that ends in `/`. The opening `<` and its name are parsed
atomically, so that a child list stops at the `<` of a closing tag.

## The root's context

The root takes its context from the expected type, `Child ctx` or
`Element t ctx`, read through `whnf`; without one it takes `Ctx.document`
for `html`, `Ctx.flow` for flow content, `Ctx.phrasing` for phrasing
content, `Ctx.metadata` for metadata content, and `Ctx.flow` otherwise.

## SVG

Since slice S3e of `docs/SVG-PACKAGE-PLAN.md` an `svg` element may stand
where the context admits it, as a child or as the root:

```lean
def figure : Element .p Ctx.flow :=
  html! <p><svg viewBox="0 0 10 10"><rect x="1" "xml:space"="preserve" /></svg></p>
```

The typed tree has no SVG element, so the subtree below `svg` is built as one
raw literal, and one obligation says that it is valid where it stands. The
kernel checks that obligation by evaluating the checker once over the
subtree. Before that the elaborator evaluates the located refusal,
`Whatwg.Html.Content.explainAt`, and reports it at the token of the refused
node, with the reason the library gives.

A name is kept exactly as written: `viewBox` is not `viewbox`. A name that is
no Lean identifier is a string literal: `"xml:space"`, and `"in"`, `"from"`,
`"by"` and `"end"`, which are Lean keywords. `<rect />` is an element with no
child. A spliced attribute value, `x={e}`, is admitted on an SVG element: the
checker reads no SVG value. On an HTML element below `foreignObject` a value
is a literal, and no child is spliced inside an SVG subtree.

A literal value of an SVG attribute that has a grammar (`d`, `points`,
`viewBox` and the three transform attributes) is run through that grammar
when the tree is built, and a bad one is refused at the attribute's token.
That run is the elaborator's and not an obligation of the tree: the kernel
cannot open a long `String` at a bearable cost
(`Whatwg/Html/Content/Values.lean`). A spliced value is not run.

## What is not here

Attribute values are `String`; comments and entities have no markup form.

The walker recurses on a fuel that starts at 4096 levels of nesting, which
no well-formed document exhausts; the trust gate forbids `partial`.
-/

namespace Whatwg.Html.Syntax

open Lean Elab Term Meta
open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx)

/-! ## Syntax -/

declare_syntax_cat htmlName
/-- An element or attribute name. -/
syntax ident : htmlName
syntax "section" : htmlName
syntax "meta" : htmlName
syntax "class" : htmlName
syntax "for" : htmlName
syntax "open" : htmlName
/-- A name that is no Lean identifier, such as `"xml:space`" or `"in`". -/
syntax str : htmlName

declare_syntax_cat htmlAttr
/-- `name`, `name="literal"`, `name={term}`; dashes join names. -/
syntax (name := htmlAttrNode) htmlName ("-" htmlName)* ("=" (str <|> ("{" term "}")))? : htmlAttr

declare_syntax_cat htmlNode
/-- A self-closing element. -/
syntax (name := htmlVoid) atomic("<" htmlName) htmlAttr* "/>" : htmlNode
/-- An element with children. The closing tag is `<`, `/`, the name and `>`. -/
syntax (name := htmlElem) atomic("<" htmlName) htmlAttr* ">" htmlNode* "<" "/" htmlName ">" : htmlNode
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
  | other => (other.isStrLit?).getD ""

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

/-- The literals of the contexts a document has met, so that each distinct
context is built once and every obligation at that context shares the one
expression (a literal is some twenty nodes; a document meets few distinct
contexts). -/
abbrev CtxCache := IO.Ref (Std.HashMap Ctx Expr)

def ctxExprCached (cache : CtxCache) (c : Ctx) : MetaM Expr := do
  match (← cache.get).get? c with
  | some e => return e
  | none =>
    let e ← ctxExpr c
    cache.modify (·.insert c e)
    return e

/-- Elaborate a spliced term against a type and settle it. -/
def elabClosed (stx : Syntax) (type : Expr) : TermElabM Expr := do
  let e ← elabTermEnsuringType stx type
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- A proof of a closed obligation `lhs = true`: `Eq.refl true`, which the
kernel checks against the obligation where the term is used. The obligation
is taken and not read, so that each caller still states what it proves. -/
def proofOf (_lhs : Expr) : TermElabM Expr :=
  pure Admit.reflTrue

def admitsProof (ctxE : Expr) (t : Tag) : TermElabM Expr := do
  proofOf (mkApp2 (mkConst ``Ctx.admits) ctxE (← tagExpr t))

/-- The admission of an element with its attributes. -/
def admitsWithProof (ctxE : Expr) (t : Tag) (attrsE : Expr) : TermElabM Expr := do
  proofOf (mkApp3 (mkConst ``Ctx.admitsWith) ctxE (← tagExpr t) (mkApp (mkConst ``rawAttrs) attrsE))

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

/-! ## A foreign subtree -/

/-- A foreign subtree as built from markup: each node as a value, as an expression, and with
the token that names it. A spliced attribute value is the empty string in the value. -/
inductive Built where
  | node (raw : RawNode) (expr : Expr) (stx : Syntax) (kids : List Built)

namespace Built

def raw : Built → RawNode
  | .node r _ _ _ => r

def expr : Built → Expr
  | .node _ e _ _ => e

def stx : Built → Syntax
  | .node _ _ s _ => s

/-- The built node at a path of child indices. -/
def at? : Built → List Nat → Option Built
  | built, [] => some built
  | .node _ _ _ kids, index :: rest =>
    match kids[index]? with
    | some kid => kid.at? rest
    | none => none

end Built

/-- The name token, the attributes and the children of an element of markup. -/
def markupParts (stx : Syntax) : TermElabM (Option (Syntax × Array Syntax × Array Syntax)) := do
  if stx.isOfKind ``htmlVoid then
    return some (stx[1], stx[2].getArgs, #[])
  if stx.isOfKind ``htmlElem then
    let name := nameString stx[1]
    let closing := nameString stx[7]
    unless closing == name do
      throwErrorAt stx[7] ("closing tag </" ++ closing ++ "> does not match <" ++ name ++ ">")
    return some (stx[1], stx[2].getArgs, stx[4].getArgs)
  return none

/-- The name of an element of markup that no HTML element has and a foreign element of the
standard's category lists has: `svg`, or `math`. -/
def foreignName? (stx : Syntax) : Option String :=
  if stx.isOfKind ``htmlVoid || stx.isOfKind ``htmlElem then
    let name := nameString stx[1]
    if (Tag.ofName? name).isNone && (Tag.ofForeignName? name).isSome then some name else none
  else none

/-- The attributes of the element `element` in a foreign subtree: the pairs as values and as an
expression. `isSvg` says that the element is an SVG element. On one, a spliced value is
admitted, and a literal value is run through its attribute's grammar here
(`Whatwg.Svg.Value.valueOkByName`) and refused at the attribute's token, with the offset at
which no reading continues. That run is the elaborator's: the tree's obligation does not read
an SVG value (`Whatwg/Html/Content/Values.lean`). -/
def foreignAttrs (isSvg : Bool) (element : String) (stxs : Array Syntax) :
    TermElabM (List (String × String) × Expr) := do
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
  let mut values : Array (String × String) := #[]
  let mut exprs : Array Expr := #[]
  for stx in stxs do
    let mut markup := nameString stx[0]
    for part in stx[1].getArgs do
      markup := markup ++ "-" ++ nameString part[1]
    let opt := stx[2]
    let literal? : Option String :=
      if opt.getNumArgs == 0 then some "" else opt[1].isStrLit?
    let (value, valueE) ← match literal? with
      | some s =>
        if isSvg && !Whatwg.Svg.Value.valueOkByName element.toList markup.toList s.toList then
          throwErrorAt stx (Whatwg.Html.Content.Reason.describe
            (.attribute markup (Whatwg.Html.Content.valueFault element markup s)))
        pure (s, mkStrLit s)
      | none =>
        if isSvg then pure ("", ← elabClosed opt[1][1] (mkConst ``String))
        else throwErrorAt stx ("html!: the value of `" ++ markup ++
          "` is spliced on an HTML element inside an SVG subtree; write it as a literal")
    values := values.push (markup, value)
    exprs := exprs.push (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String)
      (mkConst ``String) (mkStrLit markup) valueE)
  return (values.toList, ← mkListLit pairT exprs.toList)

/-- Build a node of a foreign subtree that stands at the position `pos`. Names are kept as
written, and the position moves by the seam's own transition. -/
def foreignNode : Nat → Whatwg.Html.Content.Pos → Syntax → TermElabM Built
  | 0, _, stx => throwErrorAt stx "html!: the document nests too deeply"
  | fuel + 1, pos, stx => do
    if stx.isOfKind ``htmlText then
      let some s := stx[0].isStrLit? | throwErrorAt stx "html!: malformed text"
      return .node (.text s) (mkApp (mkConst ``RawNode.text) (mkStrLit s)) stx []
    if stx.isOfKind ``htmlSplice then
      throwErrorAt stx "html!: a spliced child is not supported inside an SVG subtree"
    let some (nameStx, attrStxs, kidStxs) ← markupParts stx
      | throwErrorAt stx "html!: unsupported node"
    let name := nameString nameStx
    -- an SVG element: any element at an SVG position, and the foreign root at an HTML one
    let isSvg := pos.ns == .svg || (Tag.ofName? name).isNone
    let (attrs, attrsE) ← foreignAttrs isSvg name attrStxs
    let inner := pos.child name
    let mut kids : Array Built := #[]
    for kid in kidStxs do
      kids := kids.push (← foreignNode fuel inner kid)
    let childrenE ← mkListLit (mkConst ``RawNode) (kids.toList.map Built.expr)
    return .node (.element name attrs (kids.toList.map Built.raw))
      (mkApp3 (mkConst ``RawNode.element) (mkStrLit name) attrsE childrenE) nameStx kids.toList

/-- Build the foreign subtree at an HTML position and refuse it where the checker does: at
the token of the refused node, with the library's reason. -/
def foreignChild (fuel : Nat) (ctx : Ctx) (stx : Syntax) : TermElabM Built := do
  let built ← foreignNode fuel (.html ctx) stx
  if let some refusal := Whatwg.Html.Content.explainAt (.html ctx) built.raw then
    let culprit := (built.at? refusal.path).getD built
    throwErrorAt culprit.stx
      (Admit.nodeWords culprit.raw ++ ": " ++ refusal.reason.describe ++
        (if refusal.path.isEmpty then " (the context is " ++ ctx.describe ++ ")" else ""))
  return built

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
    let closing := nameString stx[7]
    unless closing == name do
      throwErrorAt stx[7] ("closing tag </" ++ closing ++ "> does not match <" ++ name ++ ">")
    return some { nameStx := stx[1], tag, attrs := stx[2].getArgs, kids := stx[4].getArgs }
  return none

/-- The raw attributes, as values, of an element's attribute list. -/
def rawAttrValues (attrs : Array AttrOut) : List (String × String) :=
  attrs.toList.filterMap fun a => match a.value with
    | .lit (.strVal v) => some (a.markup, v)
    | _ => some (a.markup, "")

/-- Elaborate an element placed in the context `ctx` (as a value and as the
expression `ctxE`): the raw literal and a term of type `Element tag ctx`. -/
def elabElement (cache : CtxCache) : Nat → Open → Ctx → Expr → Bool → TermElabM (Expr × Expr × Array AttrOut)
  | 0, o, _, _, _ => throwErrorAt o.nameStx "html!: the document nests too deeply"
  | fuel + 1, o, ctx, ctxE, root => do
    let t := o.tag
    let name := t.markupText
    if t.isVoid && !o.kids.isEmpty then
      throwErrorAt o.nameStx ("<" ++ name ++ "> is a void element and takes no children")
    let tE ← tagExpr t
    let attrs ← elabAttrs t o.attrs
    let attrsE ← attrsTerm attrs
    let inner := ctx.child t
    -- the children's context as a reduced literal, not a `Ctx.child` chain:
    -- identical positions then share one obligation type (performance review §3)
    let innerE ← ctxExprCached cache inner
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
      else if (foreignName? kid).isSome then
        -- an `svg` subtree: one raw literal, and one obligation the kernel evaluates
        let built ← foreignChild fuel inner kid
        raws := raws.push built.expr
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            Admit.reflTrue, hrest]
      else
        let some k ← openOf kid | throwErrorAt kid "html!: unsupported node"
        let c := k.tag
        let (raw, e, kattrs) ← elabElement cache fuel k inner innerE false
        unless inner.admitsWith c (rawAttrValues kattrs) do
          throwErrorAt k.nameStx (Admit.admitMessage inner c)
        let h ← admitsWithProof innerE c (← attrsTerm kattrs)
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
    let rawAttrsE ← rawAttrsTerm attrs
    let raw := mkApp3 (mkConst ``RawNode.element) (mkStrLit name) rawAttrsE childrenE

    -- the ordered model, checked on the children's tags as written
    let kidTags := o.kids.toList.filterMap fun kid =>
      if kid.isOfKind ``htmlText then some (Whatwg.Html.RawNode.text "")
      else if kid.isOfKind ``htmlSplice then none
      else match Tag.ofName? (nameString kid[1]) with
        | some tg => some (Whatwg.Html.RawNode.element tg.markupText [] [])
        | none => (foreignName? kid).map fun name => Whatwg.Html.RawNode.element name [] []
    if o.kids.all (fun kid => !kid.isOfKind ``htmlSplice) then
      if let some problem := Whatwg.Html.Content.seqProblem? inner t kidTags then
        throwErrorAt o.nameStx problem
    let ho ← proofOf (mkApp4 (mkConst ``Whatwg.Html.Content.elementOk) ctxE tE (mkApp (mkConst ``rawAttrs) attrsE) childrenE)
    let ht ← proofOf (mkApp2 (mkConst ``Option.isSome [Level.zero]) (mkConst ``String) (mkApp (mkConst ``Tag.markupName) tE))
    let evidence ← if root then do
        let type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
          (mkApp2 (mkConst ``Whatwg.Html.Content.validAll) innerE childrenE) (mkConst ``Bool.true)
        pure (Lean.mkConst (← mkAuxLemma [] type (← instantiateMVars hc)))
      else pure hc
    return (raw, mkAppN (mkConst ``Element.ofRaw) #[tE, ctxE, attrsE, childrenE, ho, evidence, ht], attrs)

/-- The default context of a root, by the root's categories. -/
def defaultCtx (t : Tag) : Ctx :=
  if t == .html then Ctx.document
  else if Cats.flow t then Ctx.flow
  else if Cats.phrasing t then Ctx.phrasing
  else if Cats.metadata t then Ctx.metadata
  else Ctx.flow

@[term_elab htmlTerm] def elabHtml : TermElab := fun stx expectedType? => do
  let node := stx[1]
  let fuel := 4096
  let cache : CtxCache ← IO.mkRef {}
  let expectedType? ← tryPostponeIfHasMVars? expectedType?
  let expected := expectedType?.map fun e => e.consumeMData
  if (foreignName? node).isSome then
    -- a foreign root is a `Child` of its context: the expected one, or flow content
    let mut ctx := Ctx.flow
    let mut ctxE ← ctxExprCached cache Ctx.flow
    if let some e := expected then
      if e.isAppOfArity ``Child 1 then
        if let some c ← Admit.ctx? 4096 (e.getArg! 0) then
          ctx := c
          ctxE := e.getArg! 0
    let built ← foreignChild fuel ctx node
    return mkApp3 (mkConst ``Child.mk) ctxE built.expr Admit.reflTrue
  let some o ← openOf node | throwErrorAt node "html!: the root must be an element"
  let t := o.tag
  if let some e := expected then
    if e.isAppOfArity ``Child 1 then
      if let some ctx ← Admit.ctx? 4096 (e.getArg! 0) then
        let ctxE := e.getArg! 0
        let (_, elem, rattrs) ← elabElement cache fuel o ctx ctxE true
        unless ctx.admitsWith t (rawAttrValues rattrs) do throwErrorAt o.nameStx (Admit.admitMessage ctx t)
        return mkApp4 (mkConst ``Child.of) (← tagExpr t) ctxE elem (← admitsWithProof ctxE t (← attrsTerm rattrs))
    if e.isAppOfArity ``Element 2 then
      if let some t' ← Admit.tag? (e.getArg! 0) then
        unless t' == t do
          throwErrorAt o.nameStx ("the expected type names <" ++ t'.markupText ++ "> but the root is <" ++ t.markupText ++ ">")
        if let some ctx ← Admit.ctx? 4096 (e.getArg! 1) then
          return (← elabElement cache fuel o ctx (e.getArg! 1) true).2.1
  let ctx := defaultCtx t
  return (← elabElement cache fuel o ctx (← ctxExprCached cache ctx) true).2.1

end Whatwg.Html.Syntax
