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
position is a `ContentSet` value, resolved through the same compiled
`childSet` the typed tree's index unfolds to, and every admission is decided
by the compiled `Content.admits`, so the diagnostic at a rejected token can
name the element and the resolved set (`<div>` under a link in a paragraph
reports `phrasing_without_interactive`). The term produced is
`Element.ofRaw` at every element: the raw children as a plain literal, and
the evidence for them, `Erasure t inner children` of
`Whatwg.Html.Node.Evidence`, as a proposition built from `Child.of` and
`Child.text` with their admission proofs. The kernel checks the evidence
against the literal; the compiler erases it and compiles the literal. No
`elabApp`, no unification and no tactic runs per node, which is where the
combinators spend their budget (`WhatwgTest/Html/DecideBenchmark.lean`),
and no typed call is left for the compiler to inline, which is where a
combinator-built document spends the rest.

## Memoization

Every proof is `Eq.refl true`, which the kernel checks by evaluating the
obligation. With `whatwg.html.memo` (the default) each distinct admission
`Content.Admits set t` and each distinct attribute obligation is minted once
per module as an auxiliary lemma through `Lean.Meta.mkAuxLemma`, which caches
by type, so the kernel's work is bounded by the number of distinct
obligations a document uses, at most the size of the schema, and not by the
document. With the option off, every node carries a fresh `Eq.refl true`.
The benchmark measures both and finds them within a few thousand
heartbeats of each other on five hundred nodes, because the kernel's own
`whnf` cache already makes a repeated obligation, and a repeated
`childSet set t` resolution, free within one declaration; the lemma route
keeps that across the declarations of a module.

## The labelled forms

The standard admits `source` and `track` first under `audio` and `video`,
and `area` under `map`, outside any content set. `html!` admits those
children by the generated table `Whatwg.Html.Schema.labelledChild`: the
child is elaborated against its own content set and placed as an element,
not as an admitted `Child`. Their position among the siblings is kept as
written.
Where one markup name had two rows there would be a choice to make; at
this pin every name has one row.

## Cost

Elaboration and kernel checking cost about two hundred heartbeats per node
(`WhatwgTest/Html/MarkupBenchmark.lean`: 501 nodes at 114 thousand, under
the default budget of 200 thousand), sixty times less than the combinators.
A *computable* document additionally pays Lean's compiler for the raw
literal, about a thousand heartbeats per constructor application, so a
`def` of more than roughly a hundred and fifty nodes needs
`set_option maxHeartbeats`; a `noncomputable def`, or a document only
reasoned about, does not.

## What is not here

Attribute values are `String`, as in the combinators, and a literal value
is checked against the kind the standard's attribute index gives it (a
boolean attribute is written bare, a keyword attribute takes one of its
keywords, an integer attribute digits); a spliced value is not checked.
The prefixed attributes `data-*` and `aria-*` cannot be represented in
`Attr × String` and are rejected with a message saying so; comments and
entities have no markup form. Each is a later slice.

The walker recurses on a fuel that starts at the number of syntax nodes,
which no well-formed document exhausts; the trust gate forbids `partial`.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)

namespace Syntax

open Lean Elab Term Meta
open Whatwg.Html.Schema

register_option whatwg.html.memo : Bool := {
  defValue := true
  descr := "html!: mint one auxiliary lemma per distinct admission obligation and reuse it (true), or a fresh Eq.refl per node (false)"
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

/-! ## Schema lookups, at the meta level -/

/-- The string a name node spells. -/
def nameString (stx : Syntax) : String :=
  match stx[0] with
  | .ident _ _ n _ => n.eraseMacroScopes.toString
  | .atom _ v => v
  | _ => ""

/-- The arity of a labelled child (`labelledChild`): required, and may
repeat. At this pin every labelled child is optional and may repeat. -/
def labelledArity (_parent _child : Tag) : Bool × Bool := (false, true)

/-- The element rows with a name: one at this pin. -/
def elementRows (markup : String) : List Schema.Element :=
  elements.filter (·.name == markup)

/-- The constructor constant at an index of an enum. -/
def ctorExpr (induct : Name) (idx : Nat) : MetaM Expr := do
  let info ← getConstInfoInduct induct
  return mkConst info.ctors[idx]!

def tagExpr (t : Tag) : MetaM Expr := ctorExpr ``Tag t.ctorIdx
def setExpr (s : ContentSet) : MetaM Expr := ctorExpr ``ContentSet s.ctorIdx
def attrExpr (a : Attr) : MetaM Expr := ctorExpr ``Attr a.ctorIdx
def attrSetExpr (s : AttrSet) : MetaM Expr := ctorExpr ``AttrSet s.ctorIdx

/-- Elaborate a spliced term against a type and settle it, so that it can
enter a lemma: no pending instance or postponed problem may remain. -/
def elabClosed (stx : Syntax) (type : Expr) : TermElabM Expr := do
  let e ← elabTermEnsuringType stx type
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- A proof of a closed obligation, as the module docstring describes:
`Eq.refl true`, minted once per distinct type when memoizing. -/
def proofOf (type : Expr) : TermElabM Expr := do
  if whatwg.html.memo.get (← getOptions) then
    return mkConst (← mkAuxLemma [] type Admit.reflTrue)
  return Admit.reflTrue

def admitsProof (set : ContentSet) (t : Tag) : TermElabM Expr := do
  proofOf (mkApp2 (mkConst ``Content.Admits) (← setExpr set) (← tagExpr t))

/-! ## Attributes -/

/-- One elaborated attribute: its row and its value term. -/
structure AttrOut where
  tag : Attr
  markup : String
  value : Expr

/-- The index rows of an attribute that apply to an element: the rows
naming it, else the global rows. -/
def rowsFor (a : Attr) (t : Tag) : List AttrRow :=
  let named := attributeRows.filter fun r => r.attr == a && r.elements.contains t
  if named.isEmpty then attributeRows.filter fun r => r.attr == a && r.global else named

/-- Digits only, at least one. -/
def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- Check a literal value against the kind its index row gives it; `none`
when it conforms, else the message. A spliced value is not checked. -/
def valueProblem (a : Attr) (t : Tag) (markup value : String) (presence : Bool) : Option String :=
  match rowsFor a t with
  | [] => none
  | row :: _ =>
    match row.kind with
    | .boolean =>
      if presence || value.isEmpty || value == markup then none
      else some ("attribute `" ++ markup ++ "` is a boolean attribute: write it bare, or with the empty string or its own name as its value")
    | .keywords false =>
      if row.keywords.contains value || (row.allowEmpty && value.isEmpty) then none
      else some ("attribute `" ++ markup ++ "` on <" ++ t.markupText ++ "> takes one of "
        ++ ", ".intercalate (row.keywords.map fun k => "`" ++ k ++ "`")
        ++ (if row.allowEmpty then ", or the empty string" else "") ++ ", not `" ++ value ++ "`")
    | .integer =>
      if presence then some ("attribute `" ++ markup ++ "` takes a value")
      else if isDigits value || (value.startsWith "-" && isDigits (String.ofList (value.toList.drop 1))) then none
      else some ("attribute `" ++ markup ++ "` takes a valid integer, not `" ++ value ++ "`")
    | .nonNegInteger =>
      if presence then some ("attribute `" ++ markup ++ "` takes a value")
      else if isDigits value then none
      else some ("attribute `" ++ markup ++ "` takes a valid non-negative integer, not `" ++ value ++ "`")
    | .float => if presence then some ("attribute `" ++ markup ++ "` takes a value") else none
    | _ => none

/-- Elaborate the attributes of an element against its attribute set,
blaming one token at a time, and check every literal value against the
kind its index row gives it. -/
def elabAttrs (t : Tag) (elementName : String) (set : AttrSet) (stxs : Array Syntax) :
    TermElabM (Array AttrOut) := do
  let mut out : Array AttrOut := #[]
  for stx in stxs do
    let mut markup := nameString stx[1 - 1]
    for part in stx[1].getArgs do
      markup := markup ++ "-" ++ nameString part[1]
    if out.any (·.markup == markup) then
      throwErrorAt stx ("attribute `" ++ markup ++ "` is given twice on <" ++ elementName ++ ">")
    if let some pre := attributeCtors.find? (fun c => c.isPrefix && markup.startsWith c.markup) then
      throwErrorAt stx ("attribute `" ++ markup ++ "`: the prefixed attributes `" ++ pre.markup
        ++ "*` are not representable in `Attr × String` at this pin")
    let some row := attributeCtors.find? (fun c => !c.isPrefix && c.markup == markup)
      | throwErrorAt stx ("unknown attribute `" ++ markup ++ "`")
    unless set.contains row.tag do
      throwErrorAt stx ("attribute `" ++ markup ++ "` is not admitted on <" ++ elementName
        ++ ">: the attribute set `" ++ set.name ++ "` does not name it")
    let opt := stx[2]
    let presence := opt.getNumArgs == 0
    let literal? : Option String := if presence then some "" else opt[1].isStrLit?
    if let some v := literal? then
      if let some problem := valueProblem row.tag t markup v presence then
        throwErrorAt stx problem
    let value ← if presence then pure (mkStrLit "") else
      let v := opt[1]
      match v.isStrLit? with
      | some s => pure (mkStrLit s)
      | none => elabClosed v[1] (mkConst ``String)
    out := out.push { tag := row.tag, markup, value }
  return out

/-! ## The walk -/

/-- The term of an attribute list, typed. -/
def attrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Attr) (mkConst ``String)
  let pairs ← attrs.toList.mapM fun a => do
    return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Attr) (mkConst ``String)
      (← attrExpr a.tag) a.value
  mkListLit pairT pairs

/-- The term of an attribute list, raw: markup names, as `Element.toRaw`
spells them. -/
def rawAttrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
  let pairs := attrs.toList.map fun a =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
      (mkStrLit a.tag.markupName) a.value
  mkListLit pairT pairs

/-- The pieces of an element node: its name token, its row, attributes,
children, and whether it was self-closing. -/
structure Open where
  nameStx : Syntax
  rows : List Schema.Element
  attrs : Array Syntax
  kids : Array Syntax

/-- Read an element node, checking its closing tag. -/
def openOf (stx : Syntax) : TermElabM (Option Open) := do
  if stx.isOfKind ``htmlVoid then
    let name := nameString stx[1]
    let rows := elementRows name
    if rows.isEmpty then throwErrorAt stx[1] ("unknown element <" ++ name ++ ">")
    return some { nameStx := stx[1], rows, attrs := stx[2].getArgs, kids := #[] }
  if stx.isOfKind ``htmlElem then
    let name := nameString stx[1]
    let rows := elementRows name
    if rows.isEmpty then throwErrorAt stx[1] ("unknown element <" ++ name ++ ">")
    let closing := nameString stx[6]
    unless closing == name do
      throwErrorAt stx[6] ("closing tag </" ++ closing ++ "> does not match <" ++ name ++ ">")
    return some { nameStx := stx[1], rows, attrs := stx[2].getArgs, kids := stx[4].getArgs }
  return none

/-- The row of an element: the first with its name (one at this pin). -/
def chooseRow (o : Open) (_expected? : Option ContentSet) : Schema.Element :=
  o.rows.head!

/-- Elaborate an element whose children are checked against `inner`: the
raw literal of the element and a term of type `Element row.tag inner`. -/
def elabElement : Nat → Open → Schema.Element → ContentSet → Bool → TermElabM (Expr × Expr)
  | 0, o, _, _, _ => throwErrorAt o.nameStx "html!: the document nests too deeply"
  | fuel + 1, o, row, inner, root => do
    let t := row.tag
    let name := row.name
    if t.isVoid && !o.kids.isEmpty then
      throwErrorAt o.nameStx ("<" ++ name ++ "> is a void element and takes no children")
    let innerE ← setExpr inner
    let tE ← tagExpr t
    let rawT := Lean.mkConst ``RawNode
    -- children, front to back; the evidence is assembled back to front
    let mut raws : Array Expr := #[]
    let mut steps : Array (Expr → Expr → Expr) := #[]
    let mut seen : List Tag := []
    for kid in o.kids do
      if kid.isOfKind ``htmlText then
        let some s := kid[0].isStrLit? | throwErrorAt kid "html!: malformed text"
        unless Content.admits inner .pcdata do
          throwErrorAt kid ("text is not admitted here: the content set `" ++ inner.name
            ++ "` does not name it")
        let child := mkApp3 (mkConst ``Child.text) innerE (mkStrLit s) (← admitsProof inner .pcdata)
        raws := raws.push (mkApp (mkConst ``RawNode.text) (mkStrLit s))
        steps := steps.push fun rest h => mkAppN (mkConst ``Erasure.child) #[tE, innerE, child, rest, h]
      else if kid.isOfKind ``htmlSplice then
        let child ← elabClosed kid[1] (mkApp (mkConst ``Child) innerE)
        raws := raws.push (mkApp2 (mkConst ``Child.raw) innerE child)
        steps := steps.push fun rest h => mkAppN (mkConst ``Erasure.child) #[tE, innerE, child, rest, h]
      else
        let some k ← openOf kid | throwErrorAt kid "html!: unsupported node"
        let krow := chooseRow k none
        let c := krow.tag
        if labelledChild t c then
          let (_, many) := labelledArity t c
          if !many && seen.contains c then
            throwErrorAt k.nameStx ("<" ++ name ++ "> takes at most one <" ++ krow.name ++ ">")
          seen := c :: seen
          let own := c.content?.getD .nothing
          let (raw, e) ← elabElement fuel k krow own false
          let cE ← tagExpr c
          raws := raws.push raw
          steps := steps.push fun rest h =>
            mkAppN (mkConst ``Erasure.labelled) #[tE, innerE, cE, Admit.reflTrue, e, rest, h]
        else
          unless Content.admits inner c do
            throwErrorAt k.nameStx (Admit.describe c ++ " is not admitted here: the content set `"
              ++ inner.name ++ "` does not name it")
          let (raw, e) ← elabElement fuel k krow (childSet inner c) false
          let child := mkApp4 (mkConst ``Child.of) innerE (← tagExpr c) e (← admitsProof inner c)
          raws := raws.push raw
          steps := steps.push fun rest h => mkAppN (mkConst ``Erasure.child) #[tE, innerE, child, rest, h]
    for c in Tag.all do
      if labelledChild t c && (labelledArity t c).1 && !seen.contains c then
        throwErrorAt o.nameStx ("<" ++ name ++ "> requires a <" ++ c.markupText ++ "> child")
    -- the evidence, back to front, each step indexed by the literal tail it extends
    let mut rest ← mkListLit rawT []
    let mut h := mkApp2 (mkConst ``Erasure.nil) tE innerE
    for i in [0:steps.size] do
      let j := steps.size - 1 - i
      h := steps[j]! rest h
      rest := mkApp3 (mkConst ``List.cons [Level.zero]) rawT raws[j]! rest
    let childrenE := rest
    let attrs ← elabAttrs t name row.attribs o.attrs
    let attrsE ← attrsTerm attrs
    let rawAttrsE ← rawAttrsTerm attrs
    let raw := mkApp3 (mkConst ``RawNode.element) (mkStrLit name) rawAttrsE childrenE
    let setE ← attrSetExpr row.attribs
    let proof ← proofOf (mkApp2 (mkConst ``AttrsAdmitted) setE attrsE)
    -- at the root the evidence becomes one lemma, so that the compiled term
    -- holds a constant where the proof tree was (see the module docstring)
    let evidence ← if root then do
        let type := mkApp3 (mkConst ``Erasure) tE innerE childrenE
        pure (Lean.mkConst (← mkAuxLemma [] type (← instantiateMVars h)))
      else pure h
    return (raw, mkAppN (mkConst ``Element.ofRaw) #[tE, innerE, setE, attrsE, childrenE, proof, evidence])

/-- The root: its context comes from the expected type, `Child set` or
`Element t inner`; without one a non-transparent root takes its own content
set and a transparent root is an error. -/
@[term_elab htmlTerm] def elabHtml : TermElab := fun stx expectedType? => do
  let node := stx[1]
  let some o ← openOf node | throwErrorAt node "html!: the root must be an element"
  let fuel := 4096
  let expectedType? ← tryPostponeIfHasMVars? expectedType?
  let expected := expectedType?.map fun e => e.consumeMData
  if let some e := expected then
    if e.isAppOfArity ``Child 1 then
      if let some set ← Admit.contentSet? 32 (e.getArg! 0) then
        let row := chooseRow o none
        let t := row.tag
        unless Content.admits set t do
          throwErrorAt o.nameStx (Admit.describe t ++ " is not admitted here: the content set `"
            ++ set.name ++ "` does not name it")
        let (_, elem) ← elabElement fuel o row (childSet set t) true
        return mkApp4 (mkConst ``Child.of) (← setExpr set) (← tagExpr t) elem (← admitsProof set t)
    if e.isAppOfArity ``Element 2 then
      if let some t' ← Admit.tag? (e.getArg! 0) then
        if let some inner ← Admit.contentSet? 32 (e.getArg! 1) then
          let row := chooseRow o (some inner)
          let t := row.tag
          unless t' == t do
            throwErrorAt o.nameStx ("the expected type names <" ++ t'.markupText ++ "> but the root is <"
              ++ row.name ++ ">")
          let own := row.content
          unless row.transparent || inner == own do
            throwErrorAt o.nameStx ("the content set of <" ++ row.name ++ "> is `" ++ own.name
              ++ "`, not `" ++ inner.name ++ "`")
          return (← elabElement fuel o row inner true).2
  let row := chooseRow o none
  if row.transparent then
    throwErrorAt o.nameStx ("<" ++ row.name
      ++ "> is transparent and needs its context: annotate the expected type as `Child set` or `Element ."
      ++ row.name ++ " inner`")
  return (← elabElement fuel o row row.content true).2

end Syntax
end Whatwg.Html
