import Lean
import Std.Data.HashMap
import Whatwg.Html.Content.Values
import Whatwg.Html.Node.Admit
import Whatwg.Html.Node.Evidence
import Whatwg.Html.Node.SvgValid

/-!
# Whatwg.Html.Syntax.Elaborator

`html!`, the markup surface over the typed tree (slice H5 of
`docs/HTML-PACKAGE-PLAN.md`; ruling R7 there says why this is an elaborator
and not a macro):

```lean
def page : Element .div Ctx.flow :=
  html! <div class="lead"><p>"Hello, " <em>"world"</em></p><br /></div>
```

Text is a string literal, `{e}` splices a `Child` term (or, in an attribute
value, a `String` term on an HTML element and a term of the attribute's type
on an SVG element), a void element is written `<br />`, and a bare
attribute name is a presence attribute whose value is the empty string. The
Lean keywords among the markup
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
so that the compiled term holds a constant where the proof tree was. A proof
that names a local variable, through a spliced term, is no lemma of its own
and stays in the term. No lemma is minted per leaf: the kernel's own cache
already shares identical obligations within a declaration once the children's
contexts are emitted as reduced literals, and a lemma per distinct obligation
cost more kernel time and never shared across declarations (performance
review §7). That route sat behind an option `whatwg.html.memo`, off by
default, until the package merged with the trust gate, which refuses the
`opaque` a registered option declares; `WhatwgTest/Html/MarkupBenchmark.lean`
keeps its measurement.

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

Since slice S5 the subtree below `svg` is a typed tree, `SvgNode` of
`Whatwg/Html/Node/Svg.lean` (ruling SV-34; point G4 of
`docs/research/2026-10-11-svg-seat-guidance-3.md`). The elaborator builds it
in three steps:

1. It reads the markup of the subtree as a raw tree, a value at the meta
   level, with the token of each node.
2. It evaluates the located refusal of the checker,
   `Whatwg.Html.Content.explainAt`, on that tree. A refusal is reported at the
   token of the refused node, with the reason the library gives.
3. It builds the tree the checker admits from the constructors of `SvgNode`.
   The term of the subtree is `SvgNode.toRaw e`, and its validity where it
   stands is the law of structure of `Whatwg/Html/Node/SvgValid.lean`:
   `SvgNode.validIn_of_okIn` at one obligation, `SvgNode.okIn ctx e = true`.
   The kernel checks the obligation by evaluating `okIn` once over the typed
   tree. That test reads tags and keys: it decodes no name, and it opens no
   value. Before slice S6 the obligation was the checker's own run over the
   written names, which took the kernel about fifty times as long
   (`WhatwgTest/Html/SvgBenchmark.lean`).

What the typed tree `e` holds:

- An element is `SvgNode.element t attrs children`, at its tag `t` of the SVG
  schema.
- An attribute of the schema is `SvgAttr.attr a v`, where `v` has the type
  `Whatwg.Svg.Value.AttrValue t a`. Where the table `kindOf` gives the
  attribute a kind on the element, a literal value is read by the kind's
  grammar when the tree is built (`readValue`), and `v` is the term of the
  value read: constructors and numbers, never the literal. A literal that the
  grammar refuses is an error at the attribute's token, with the offset at
  which no reading continues. Where the attribute has no kind, `v` is the
  string.
- A spliced value, `d={e}`, is a term of the attribute's type: a `PathData`
  at `d`, and a `String` at `class`. A `String` at `d` is a type error.
- `data-*` is `SvgAttr.data`. `xmlns` and `xmlns:xlink` with their values are
  `SvgAttr.xmlns` and `SvgAttr.xmlnsXlink`.
- Text is `SvgNode.text`.
- An HTML element below `foreignObject`, `title` or `desc` is
  `SvgNode.raw r h`. `r` is the raw literal of the HTML subtree, and `h` says
  that its values pass wherever it stands. The structure of `r` is the
  checker's, run over its names inside the one evaluation of `okIn`. The
  kernel checks `h` by one more evaluation, which reads names alone unless
  the HTML subtree holds an `svg`
  of its own. Such an `svg` is a part of the raw literal, and the kernel reads
  each of its literal values with its grammar: that case is rare, and a long
  value there is slow (`Whatwg/Html/Content/Values.lean`). A value below an
  HTML element is a literal, and none is spliced there. An `svg` that stands
  directly below an integration point is a typed element again.

So the values of a tree that `html!` builds are right by their types. The law
is `SvgNode.valuesOk_toRaw`: the raw tree of every typed tree passes the value
judgment `valuesOk`, and the law evaluates nothing. The read of a literal is
how the elaborator makes the typed value, and no claim about the tree rests on
that run: the tree holds the value read, and never the literal.

The raw tree spells a typed value as its grammar prints it, in the grammar's
one spelling: the literal `d="M 10 20 L 40 180"` prints as `M10,20L40,180`.
The elaborator does not claim that the print of the value read is the literal
that the author wrote. The reader takes many spellings, and the printer writes
one.

A name is kept exactly as written: `viewBox` is not `viewbox`. A name that is
no Lean identifier is a string literal: `"xml:space"`, and `"in"`, `"from"`,
`"by"` and `"end"`, which are Lean keywords. `<rect />` is an element with no
child. No child is spliced inside an SVG subtree.

## Parts that are data

Since the second round of slice S17 (entries W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`; the laws are those of
`Whatwg/Html/Node/Splice.lean`) the type of a spliced term says what it is.
No form of markup is new.

- A spliced child `{e}` is a `Child` of the position, a `List` of them, or an
  `Option` of one. The term is elaborated before its type is fixed, and the
  head of its type decides. A list stands among the written children: its raw
  nodes are appended there, valid by `validAll_children` and
  `Content.validAll_append`. A list that is spliced last is the rest itself, so
  `<ol>{items}</ol>` holds what `E.ol items` holds. A child that may be absent
  is the list of none or one.
- A spliced attribute value `name={e}` is a `String`, or an `Option String` for
  an attribute that may be absent: the attribute list then holds the segment
  `A.opt (fun value => ⟨attr, name, value⟩) e`, and each obligation that reads
  the list is proved for either case, by `Option.casesOn` with `Eq.refl true`
  in each (`proofOf`). The admission is tested in each case when the term is
  built. A spliced value, absent or not, is refused with words where the
  checker reads the value of the attribute (`Content.attrFree`): the kernel
  checks the obligation with the value free.
- With the expected type `Element ?t ctx`, where the tag is not yet known, the
  position is taken from the type and the tag is the root's:
  `E.el (html! <td>…</td>)`.
- Under an element with an ordered model, a spliced child that shows its
  element, `{E.el e}` with `e : Element t ctx`, is read as that element, and
  the model is checked when the term is built. Where a splice does not show
  it, as a variable or a list does not, the kernel is left to evaluate the
  model, as before.

## What is not here

A spliced HTML attribute value is a `String` or an `Option String`; comments
and entities have no markup form. No list and no absent child is shown to an
ordered model.

The walker recurses on a fuel that starts at 4096 levels of nesting, which
no well-formed document exhausts; the trust gate forbids `partial`.
-/

namespace Whatwg.Html.Syntax

open Lean Elab Term Meta
open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx)
open Whatwg.Svg.Value (ValueKind kindOf)

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

/-- A proof of an obligation `lhs = true`. A closed obligation is `Eq.refl true`,
which the kernel checks against the obligation where the term is used: the
obligation is then taken and not read, so that each caller still states what it
proves. An obligation that holds attributes that may be absent is proved for
either case of each of their options, `options`, each a term of type
`Option String`: by `Option.casesOn` at the obligation with the option
abstracted, and `Eq.refl true` in each case. -/
def proofOf (lhs : Expr) : (options : List Expr := []) → MetaM Expr
  | [] => pure Admit.reflTrue
  | option :: rest => do
    let stringT := Lean.mkConst ``String
    let optionT := mkApp (mkConst ``Option [Level.zero]) stringT
    let body ← kabstract lhs option
    let motive := mkLambda `option .default optionT
      (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) body (mkConst ``Bool.true))
    let absent ← proofOf (body.instantiate1 (mkApp (mkConst ``Option.none [Level.zero]) stringT)) rest
    let present ← withLocalDeclD `value stringT fun value => do
      let case ← proofOf
        (body.instantiate1 (mkApp2 (mkConst ``Option.some [Level.zero]) stringT value)) rest
      mkLambdaFVars #[value] case
    return mkAppN (mkConst ``Option.casesOn [Level.zero, Level.zero])
      #[stringT, motive, option, absent, present]

def admitsProof (ctxE : Expr) (t : Tag) : TermElabM Expr := do
  proofOf (mkApp2 (mkConst ``Ctx.admits) ctxE (← tagExpr t))

/-- The admission of an element with its attributes, some of which may be absent. -/
def admitsWithProof (ctxE : Expr) (t : Tag) (attrsE : Expr) (options : List Expr := []) :
    TermElabM Expr := do
  proofOf (mkApp3 (mkConst ``Ctx.admitsWith) ctxE (← tagExpr t) (mkApp (mkConst ``rawAttrs) attrsE))
    options

/-! ## Attributes -/

structure AttrOut where
  tag : Attr
  markup : String
  value : Expr
  /-- The attribute may be absent: `value` is then a term of type `Option String`. -/
  optional : Bool := false

/-- The options of the attributes that may be absent. -/
def optionsOf (attrs : Array AttrOut) : List Expr :=
  (attrs.toList.filter (·.optional)).map (·.value)

/-- Elaborate a spliced attribute value and settle it: a `String`, or an
`Option String` for an attribute that may be absent. The second answer says
which, and the type of the term decides it. -/
def elabAttrValue (stx : Syntax) : TermElabM (Expr × Bool) := do
  let value ← elabTerm stx (← mkFreshTypeMVar)
  let type ← whnfR (← instantiateMVars (← inferType value))
  let optional := type.isAppOfArity ``Option 1
  let wanted := if optional then mkApp (mkConst ``Option [Level.zero]) (mkConst ``String)
    else mkConst ``String
  let value ← ensureHasType wanted value
  synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars value, optional)

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
    let (value, optional) ← if presence then pure (mkStrLit "", false) else
      let v := opt[1]
      match v.isStrLit? with
      | some s => pure (mkStrLit s, false)
      | none => elabAttrValue v[1]
    if literal?.isNone && !Whatwg.Html.Content.attrFree t markup then
      -- the kernel checks the obligation with the value free, which it can do only where the
      -- checker reads no value of the attribute
      throwErrorAt stx ("the value of `" ++ markup ++ "` on <" ++ name ++ "> is spliced, and the " ++
        "checker reads the value of this attribute: write a literal")
    out := out.push { tag := a, markup, value, optional }
  return out

/-- The attribute list as a term. An attribute that is always there is a cell
of the list. One that may be absent is the segment
`A.opt (fun value => ⟨attr, name, value⟩) option`, appended before the rest. -/
def attrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  let attrT := Lean.mkConst ``AttrVal
  attrs.foldrM (init := ← mkListLit attrT []) fun a rest => do
    let attrE ← attrExpr a.tag
    if a.optional then
      let make := mkLambda `value .default (mkConst ``String)
        (mkApp3 (mkConst ``AttrVal.mk) attrE (mkStrLit a.markup) (mkBVar 0))
      mkAppM ``HAppend.hAppend
        #[mkApp3 (mkConst ``Whatwg.Html.A.opt) (mkConst ``String) make a.value, rest]
    else
      return mkApp3 (mkConst ``List.cons [Level.zero]) attrT
        (mkApp3 (mkConst ``AttrVal.mk) attrE (mkStrLit a.markup) a.value) rest

/-- The raw attribute list as a term: a literal list of pairs, or `rawAttrs` of
the attribute list when an attribute may be absent. -/
def rawAttrsTerm (attrs : Array AttrOut) : MetaM Expr := do
  if attrs.any (·.optional) then
    return mkApp (mkConst ``rawAttrs) (← attrsTerm attrs)
  let pairT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
  let pairs := attrs.toList.map fun a =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``String)
      (mkStrLit a.markup) a.value
  mkListLit pairT pairs

/-! ## Terms of SVG values

The typed tree of an SVG subtree holds each value as a term: constructors and numbers.
`Lean.ToExpr` writes a value as its term. It is derived here for the carrier of each kind of
`Whatwg.Svg.Value.ValueKind` and for the types a carrier is made of, so that all meta code of
the markup term stays in this module. A new kind is its carrier's derivation and one line of
`kindToExpr`.

`kindToExpr` answers the instance of a kind, which holds two things: the term of a value, for a
literal that the grammar read, and the term of the carrier, the type that a spliced value is
elaborated against. Lean asks that a definition of class type be instance-reducible, so it is
marked so. -/

deriving instance Lean.ToExpr for Whatwg.Svg.Value.Magnitude
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Decimal
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Point
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Arc
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Command
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Path
deriving instance Lean.ToExpr for Whatwg.Svg.Value.PathData
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Points
deriving instance Lean.ToExpr for Whatwg.Svg.Value.ViewBox
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Transform
deriving instance Lean.ToExpr for Whatwg.Svg.Value.LengthUnit
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Length
deriving instance Lean.ToExpr for Whatwg.Svg.Value.Extent
deriving instance Lean.ToExpr for Whatwg.Svg.Value.AutoExtent
deriving instance Lean.ToExpr for Whatwg.Svg.Value.LengthList
deriving instance Lean.ToExpr for Whatwg.Svg.Value.NumberList

/-- How a value of a kind is written as a term, with the term of its type: one line for each
kind. -/
@[instance_reducible] def kindToExpr : (k : ValueKind) → ToExpr k.carrier
  | .pathData => inferInstanceAs (ToExpr Whatwg.Svg.Value.PathData)
  | .points => inferInstanceAs (ToExpr Whatwg.Svg.Value.Points)
  | .viewBox => inferInstanceAs (ToExpr Whatwg.Svg.Value.ViewBox)
  | .transformList => inferInstanceAs (ToExpr Whatwg.Svg.Value.TransformList)
  | .length => inferInstanceAs (ToExpr Whatwg.Svg.Value.Length)
  | .extent => inferInstanceAs (ToExpr Whatwg.Svg.Value.Extent)
  | .autoExtent => inferInstanceAs (ToExpr Whatwg.Svg.Value.AutoExtent)
  | .lengthList => inferInstanceAs (ToExpr Whatwg.Svg.Value.LengthList)
  | .numberList => inferInstanceAs (ToExpr Whatwg.Svg.Value.NumberList)

/-- How a value of an attribute's type is written as a term: by its kind, and text as a string
literal. -/
@[instance_reducible] def valueToExpr : (o : Option ValueKind) → ToExpr (ValueKind.typeOf o)
  | some k => kindToExpr k
  | none => inferInstanceAs (ToExpr String)

/-- The constructor of an element of the SVG schema. -/
def svgTagExpr (t : Whatwg.Svg.Schema.Tag) : MetaM Expr :=
  ctorExpr ``Whatwg.Svg.Schema.Tag t.ctorIdx

/-- The constructor of an attribute of the SVG schema. -/
def svgAttrExpr (a : Whatwg.Svg.Schema.Attr) : MetaM Expr :=
  ctorExpr ``Whatwg.Svg.Schema.Attr a.ctorIdx

mutual

/-- The literal of a raw node whose every value is a literal. -/
def rawLit : RawNode → Expr
  | .element name attrs children =>
    mkApp3 (mkConst ``RawNode.element) (mkStrLit name) (toExpr attrs) (rawLitAll children)
  | .text content => mkApp (mkConst ``RawNode.text) (mkStrLit content)
  | .entity name => mkApp (mkConst ``RawNode.entity) (mkStrLit name)
  | .comment content => mkApp (mkConst ``RawNode.comment) (mkStrLit content)

/-- The literal of a raw forest. -/
def rawLitAll : List RawNode → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``RawNode)
  | node :: rest =>
    mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``RawNode) (rawLit node) (rawLitAll rest)

end

/-! ## A foreign subtree

An `svg` subtree is built in three steps. `foreignNode` reads the markup as a raw tree, a value
at the meta level. `foreignTree` evaluates the located refusal of the checker on that tree.
`typedNode` builds the tree the checker admits as a term of `SvgNode`. -/

/-- An attribute of an element of a foreign subtree, as markup writes it. -/
structure MarkupAttr where
  /-- The attribute's syntax: a refusal of its value is reported here. -/
  stx : Syntax
  /-- The name, exactly as written. -/
  name : String
  /-- The literal value, which is the empty string for a bare name; `none` for a spliced
  value. -/
  literal? : Option String
  /-- The term of a spliced value. -/
  splice : Syntax

/-- A foreign subtree as read from markup: each node as a value, with the token that names it,
its attributes as written, and its children. A spliced attribute value is the empty string in
the value. `typed` says that the node is built as a node of `SvgNode`: an SVG element with no
HTML element above it in the subtree, or a text below one. Any other node is a part of a raw
literal. -/
inductive Built where
  | node (raw : RawNode) (stx : Syntax) (attrs : Array MarkupAttr) (kids : List Built)
      (typed : Bool)

namespace Built

/-- The node as a value. -/
def raw : Built → RawNode
  | .node r _ _ _ _ => r

/-- The token that names the node. -/
def stx : Built → Syntax
  | .node _ s _ _ _ => s

/-- The node's attributes, as written. -/
def attrs : Built → Array MarkupAttr
  | .node _ _ a _ _ => a

/-- The node's children. -/
def kids : Built → List Built
  | .node _ _ _ k _ => k

/-- The node is built as a node of `SvgNode`. -/
def typed : Built → Bool
  | .node _ _ _ _ t => t

/-- The built node at a path of child indices. -/
def at? : Built → List Nat → Option Built
  | built, [] => some built
  | .node _ _ _ kids _, index :: rest =>
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

/-- The attributes of an element of a foreign subtree, as written. A value may be spliced on
an element that is built as a typed node (`typed`), and on no other: the kernel evaluates the
values of a raw literal. `isSvg` says that the element is an SVG element, for the message. -/
def foreignAttrs (typed isSvg : Bool) (stxs : Array Syntax) : TermElabM (Array MarkupAttr) := do
  let mut out : Array MarkupAttr := #[]
  for stx in stxs do
    let mut name := nameString stx[0]
    for part in stx[1].getArgs do
      name := name ++ "-" ++ nameString part[1]
    let opt := stx[2]
    let literal? : Option String :=
      if opt.getNumArgs == 0 then some "" else opt[1].isStrLit?
    if literal?.isNone && !typed then
      throwErrorAt stx ("html!: the value of `" ++ name ++ "` is spliced " ++
        (if isSvg then "below" else "on") ++
        " an HTML element inside an SVG subtree; write it as a literal")
    out := out.push { stx, name, literal?, splice := opt[1][1] }
  return out

/-- Read a node of a foreign subtree that stands at the position `pos`. Names are kept as
written, and the position moves by the seam's own transition. `typed` says that no HTML element
stands above the node in the subtree. No value is judged here. -/
def foreignNode : Nat → Bool → Whatwg.Html.Content.Pos → Syntax → TermElabM Built
  | 0, _, _, stx => throwErrorAt stx "html!: the document nests too deeply"
  | fuel + 1, typed, pos, stx => do
    if stx.isOfKind ``htmlText then
      let some s := stx[0].isStrLit? | throwErrorAt stx "html!: malformed text"
      return .node (.text s) stx #[] [] typed
    if stx.isOfKind ``htmlSplice then
      throwErrorAt stx "html!: a spliced child is not supported inside an SVG subtree"
    let some (nameStx, attrStxs, kidStxs) ← markupParts stx
      | throwErrorAt stx "html!: unsupported node"
    let name := nameString nameStx
    -- an SVG element: any element at an SVG position, and the foreign root at an HTML one
    let isSvg := pos.ns == .svg || (Tag.ofName? name).isNone
    let typed := typed && isSvg
    let attrs ← foreignAttrs typed isSvg attrStxs
    let inner := pos.child name
    let mut kids : Array Built := #[]
    for kid in kidStxs do
      kids := kids.push (← foreignNode fuel typed inner kid)
    return .node
      (.element name (attrs.toList.map fun a => (a.name, a.literal?.getD ""))
        (kids.toList.map Built.raw))
      nameStx attrs kids.toList typed

/-- The name of a custom data attribute without its prefix `data-`. -/
def dataKey? (name : String) : Option String :=
  if Whatwg.Html.Content.hasPrefix "data-" name then some (String.ofList (name.toList.drop 5))
  else none

/-- The typed attribute of the SVG element `t`, as a term of `SvgAttr t`. `element` is the
element's name. A literal value of an attribute of the schema is read as a value of the
attribute's type on the element (`readValue`): by its grammar where the table
`Whatwg.Svg.Value.kindOf` gives it a kind, and as the string where it gives none. A literal
that the grammar refuses is an error at the attribute's token, with the offset at which no
reading continues. A spliced value is a term of the attribute's type. -/
def typedAttr (t : Whatwg.Svg.Schema.Tag) (tE : Expr) (element : String) (attr : MarkupAttr) :
    TermElabM Expr := do
  if let some key := dataKey? attr.name then
    let value ← match attr.literal? with
      | some s => pure (mkStrLit s)
      | none => elabClosed attr.splice (mkConst ``String)
    return mkApp3 (mkConst ``SvgAttr.data) tE (mkStrLit key) value
  if attr.name == "xmlns" && attr.literal? == some svgNamespace then
    return mkApp (mkConst ``SvgAttr.xmlns) tE
  if attr.name == "xmlns:xlink" && attr.literal? == some xlinkNamespace then
    return mkApp (mkConst ``SvgAttr.xmlnsXlink) tE
  let some a := Whatwg.Svg.Schema.Attr.ofChars? attr.name.toList
    | throwErrorAt attr.stx ("html!: `" ++ attr.name ++ "` is no attribute of the SVG schema")
  let kind := kindOf t a
  let value ← match attr.literal? with
    | some s =>
      match readValue kind s with
      | some v => pure ((valueToExpr kind).toExpr v)
      | none => throwErrorAt attr.stx (Whatwg.Html.Content.Reason.describe
          (.attribute attr.name (Whatwg.Html.Content.valueFault element attr.name s)))
    | none => elabClosed attr.splice (valueToExpr kind).toTypeExpr
  return mkApp3 (mkConst ``SvgAttr.attr) tE (← svgAttrExpr a) value

/-- Refuse a raw subtree that holds a value its grammar refuses, at the attribute's token: the
located refusal of the value judgment, `Whatwg.Html.Content.explainValuesAt`, in both
namespaces. The kernel evaluates the same judgment for the premise of `SvgNode.raw`. -/
def refuseRawValues (built : Built) : TermElabM Unit := do
  let refusal? := (Whatwg.Html.Content.explainValuesAt .html built.raw).orElse fun _ =>
    Whatwg.Html.Content.explainValuesAt .svg built.raw
  if let some refusal := refusal? then
    let culprit := (built.at? refusal.path).getD built
    let token := match refusal.reason with
      | .attribute name _ => ((culprit.attrs.find? (·.name == name)).map (·.stx)).getD culprit.stx
      | _ => culprit.stx
    throwErrorAt token refusal.reason.describe

/-- The typed term of a node of a foreign subtree that the checker admits: a term of `SvgNode`.
An SVG element is `SvgNode.element` at its tag of the schema, with its typed attributes and
its children. A text is `SvgNode.text`. An HTML element, which stands below an integration
point, is `SvgNode.raw`: the raw literal of its subtree, and the premise that the subtree's
values pass, which the kernel evaluates. -/
def typedNode : Nat → Built → TermElabM Expr
  | 0, built => throwErrorAt built.stx "html!: the document nests too deeply"
  | fuel + 1, built => do
    match built.raw with
    | .text content => return mkApp (mkConst ``SvgNode.text) (mkStrLit content)
    | .entity name => return mkApp (mkConst ``SvgNode.entity) (mkStrLit name)
    | .comment content => return mkApp (mkConst ``SvgNode.comment) (mkStrLit content)
    | .element name _ _ =>
      unless built.typed do
        refuseRawValues built
        return mkApp2 (mkConst ``SvgNode.raw) (rawLit built.raw) Admit.reflTrue
      let some t := Whatwg.Svg.Schema.Tag.ofChars? name.toList
        | throwErrorAt built.stx ("html!: <" ++ name ++ "> is no element of the SVG schema")
      let tE ← svgTagExpr t
      let mut attrs : Array Expr := #[]
      for attr in built.attrs do
        attrs := attrs.push (← typedAttr t tE name attr)
      let mut kids : Array Expr := #[]
      for kid in built.kids do
        kids := kids.push (← typedNode fuel kid)
      return mkApp3 (mkConst ``SvgNode.element) tE
        (← mkListLit (mkApp (mkConst ``SvgAttr) tE) attrs.toList)
        (← mkListLit (mkConst ``SvgNode) kids.toList)

/-- Build the foreign subtree at an HTML position. The markup is read as a raw tree and refused
where the checker refuses it: at the token of the refused node, with the library's reason. The
tree the checker admits is built as a typed tree, and the result is its term `e`, of type
`SvgNode`. Its raw tree is `SvgNode.toRaw e`, and `foreignValid` proves it valid. -/
def foreignTree (fuel : Nat) (ctx : Ctx) (stx : Syntax) : TermElabM Expr := do
  let built ← foreignNode fuel true (.html ctx) stx
  if let some refusal := Whatwg.Html.Content.explainAt (.html ctx) built.raw then
    let culprit := (built.at? refusal.path).getD built
    throwErrorAt culprit.stx
      (Admit.nodeWords culprit.raw ++ ": " ++ refusal.reason.describe ++
        (if refusal.path.isEmpty then " (the context is " ++ ctx.describe ++ ")" else ""))
  typedNode fuel built

/-- The proof that the raw tree of the typed tree `e` is valid at the context `ctxE`: the law
of structure, `SvgNode.validIn_of_okIn`, at `Eq.refl true`. The kernel checks it by evaluating
`SvgNode.okIn` once over the typed tree, which reads tags and keys and no name. -/
def foreignValid (ctxE e : Expr) : Expr :=
  mkApp3 (mkConst ``SvgNode.validIn_of_okIn) ctxE e Admit.reflTrue

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

/-- The raw attributes of an element in each case of its attributes that may be
absent: every list that leaves some of them out. An admission is tested in each. -/
def rawAttrCases (attrs : Array AttrOut) : List (List (String × String)) :=
  attrs.toList.foldr (fun a cases =>
    let value := match a.value with
      | .lit (.strVal v) => v
      | _ => ""
    let present := cases.map fun rest => (a.markup, value) :: rest
    if a.optional then present ++ cases else present) [[]]

/-- What a spliced term is, by its type. -/
inductive Spliced where
  /-- One child. -/
  | child (term : Expr)
  /-- A list of children: a term of type `List (Child ctx)`. A child that may be
  absent, `Option (Child ctx)`, is its list. -/
  | list (term : Expr)

/-- Elaborate a spliced child and settle it: a `Child` of the position, a list
of them, or one that may be absent. The term is elaborated before its type is
fixed, and the head of its type decides which: `List`, `Option`, or else a
child. `childT` is the type of a child of the position. -/
def elabSplice (stx : Syntax) (childT : Expr) : TermElabM Spliced := do
  let term ← elabTerm stx (← mkFreshTypeMVar)
  let type ← whnfR (← instantiateMVars (← inferType term))
  let settle (wanted : Expr) : TermElabM Expr := do
    let term ← ensureHasType wanted term
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars term
  if type.isAppOfArity ``List 1 then
    return .list (← settle (mkApp (mkConst ``List [Level.zero]) childT))
  if type.isAppOfArity ``Option 1 then
    let term ← settle (mkApp (mkConst ``Option [Level.zero]) childT)
    return .list (mkApp2 (mkConst ``Option.toList [Level.zero]) childT term)
  return .child (← settle childT)

/-- The node that a spliced child counts as in an ordered model, when its raw
node shows it: an HTML element by its name, or a text. `none` when the term
does not show it, as a variable does not. A `let` is read through. -/
def splicedNode? (raw : Expr) : MetaM (Option RawNode) := do
  let raw ← withConfig (fun config => { config with zetaDelta := true }) (whnf raw)
  if raw.isAppOfArity ``RawNode.element 3 then
    let some name ← Admit.str? (raw.getArg! 0) | return none
    let some tag := Tag.ofName? name | return none
    return some (.element tag.markupText [] [])
  if raw.isAppOfArity ``RawNode.text 1 || raw.isAppOfArity ``RawNode.entity 1 then
    return some (.text "")
  return none

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
    let childT := mkApp (mkConst ``Child) innerE
    -- one entry for each child as written: a raw node, or the raw nodes of a spliced list
    let mut raws : Array Expr := #[]
    let mut lists : Array Bool := #[]
    -- for a spliced list, the proof that its raw nodes alone are valid
    let mut alone : Array (Option Expr) := #[]
    let mut steps : Array (Expr → Expr → Expr → Expr) := #[]
    -- what each child counts as in an ordered model; `none` where a splice does not show it
    let mut seen : Array (Option RawNode) := #[]
    for kid in o.kids do
      alone := alone.push none
      if kid.isOfKind ``htmlText then
        let some s := kid[0].isStrLit? | throwErrorAt kid "html!: malformed text"
        unless inner.admits .pcdata do
          throwErrorAt kid ("text is not admitted here: the context is " ++ inner.describe)
        let h ← admitsProof innerE .pcdata
        let raw := mkApp (mkConst ``RawNode.text) (mkStrLit s)
        raws := raws.push raw
        lists := lists.push false
        seen := seen.push (some (.text ""))
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            mkApp3 (mkConst ``Whatwg.Html.Content.validIn_text) innerE (mkStrLit s) h, hrest]
      else if kid.isOfKind ``htmlSplice then
        match ← elabSplice kid[1] childT with
        | .child child =>
          let raw := mkApp2 (mkConst ``Child.raw) innerE child
          raws := raws.push raw
          lists := lists.push false
          seen := seen.push (← if t.seq?.isSome then splicedNode? raw else pure none)
          steps := steps.push fun n rest hrest =>
            mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
              mkApp2 (mkConst ``Child.valid) innerE child, hrest]
        | .list children =>
          -- the raw nodes of the list, appended before the rest: valid by `validAll_children`
          let valid := mkApp2 (mkConst ``Whatwg.Html.validAll_children) innerE children
          raws := raws.push (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) childT rawT
            (mkApp (mkConst ``Child.raw) innerE) children)
          lists := lists.push true
          alone := alone.set! (alone.size - 1) (some valid)
          seen := seen.push none
          steps := steps.push fun n rest hrest =>
            mkAppN (mkConst ``Whatwg.Html.Content.validAll_append) #[innerE, n, rest, valid, hrest]
      else if (foreignName? kid).isSome then
        -- an `svg` subtree: the raw tree of a typed tree, valid by the law of structure
        let tree ← foreignTree fuel inner kid
        raws := raws.push (mkApp (mkConst ``SvgNode.toRaw) tree)
        lists := lists.push false
        seen := seen.push ((foreignName? kid).map fun name => .element name [] [])
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            foreignValid innerE tree, hrest]
      else
        let some k ← openOf kid | throwErrorAt kid "html!: unsupported node"
        let c := k.tag
        let (raw, e, kattrs) ← elabElement cache fuel k inner innerE false
        unless (rawAttrCases kattrs).all (inner.admitsWith c ·) do
          throwErrorAt k.nameStx (Admit.admitMessage inner c)
        let h ← admitsWithProof innerE c (← attrsTerm kattrs) (optionsOf kattrs)
        raws := raws.push raw
        lists := lists.push false
        seen := seen.push (some (.element c.markupText [] []))
        let cE ← tagExpr c
        steps := steps.push fun n rest hrest =>
          mkAppN (mkConst ``Whatwg.Html.Content.validAll_cons) #[innerE, n, rest,
            mkAppN (mkConst ``Element.valid) #[cE, innerE, e, h], hrest]
    let mut rest ← mkListLit rawT []
    let mut hc := mkApp (mkConst ``Whatwg.Html.Content.validAll_nil) innerE
    for i in [0:steps.size] do
      let j := steps.size - 1 - i
      if let (0, some valid) := (i, alone[j]!) then
        -- a list that is spliced last is the rest itself: `<ol>{items}</ol>` holds the raw
        -- nodes of `items` and nothing appended, as `E.ol items` does
        hc := valid
        rest := raws[j]!
      else
        hc := steps[j]! raws[j]! rest hc
        rest ← if lists[j]! then mkAppM ``HAppend.hAppend #[raws[j]!, rest]
          else pure (mkApp3 (mkConst ``List.cons [Level.zero]) rawT raws[j]! rest)
    let childrenE := rest
    let rawAttrsE ← rawAttrsTerm attrs
    let raw := mkApp3 (mkConst ``RawNode.element) (mkStrLit name) rawAttrsE childrenE

    -- The ordered model, checked on the children as written, and on a spliced child that
    -- shows its element. Where one does not show it, the kernel is left to evaluate the model.
    if seen.all (·.isSome) then
      if let some problem := Whatwg.Html.Content.seqProblem? inner t (seen.toList.filterMap id) then
        throwErrorAt o.nameStx problem
    let ho ← proofOf (mkApp4 (mkConst ``Whatwg.Html.Content.elementOk) ctxE tE (mkApp (mkConst ``rawAttrs) attrsE) childrenE)
      (optionsOf attrs)
    let ht ← proofOf (mkApp2 (mkConst ``Option.isSome [Level.zero]) (mkConst ``String) (mkApp (mkConst ``Tag.markupName) tE))
    let evidence ← if root then do
        let type := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
          (mkApp2 (mkConst ``Whatwg.Html.Content.validAll) innerE childrenE) (mkConst ``Bool.true)
        let proof ← instantiateMVars hc
        -- a proof that names a local variable, through a spliced term, is no lemma of its own
        if type.hasFVar || proof.hasFVar then pure proof
        else pure (Lean.mkConst (← mkAuxLemma [] type proof))
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
  -- An expected type that is not yet known is waited for. One that is still not known in full
  -- when nothing more can wait is read as far as it goes: `Element ?t ctx` names the position.
  let expectedType? ← expectedType?.mapM fun type => do
    let type ← instantiateMVars type
    if type.hasExprMVar then tryPostpone
    pure type
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
    let tree ← foreignTree fuel ctx node
    return mkApp3 (mkConst ``Child.mk) ctxE (mkApp (mkConst ``SvgNode.toRaw) tree)
      (foreignValid ctxE tree)
  let some o ← openOf node | throwErrorAt node "html!: the root must be an element"
  let t := o.tag
  if let some e := expected then
    if e.isAppOfArity ``Child 1 then
      if let some ctx ← Admit.ctx? 4096 (e.getArg! 0) then
        let ctxE := e.getArg! 0
        let (_, elem, rattrs) ← elabElement cache fuel o ctx ctxE true
        unless (rawAttrCases rattrs).all (ctx.admitsWith t ·) do
          throwErrorAt o.nameStx (Admit.admitMessage ctx t)
        return mkApp4 (mkConst ``Child.of) (← tagExpr t) ctxE elem
          (← admitsWithProof ctxE t (← attrsTerm rattrs) (optionsOf rattrs))
    if e.isAppOfArity ``Element 2 then
      let named? ← Admit.tag? (e.getArg! 0)
      if let some t' := named? then
        unless t' == t do
          throwErrorAt o.nameStx ("the expected type names <" ++ t'.markupText ++ "> but the root is <" ++ t.markupText ++ ">")
      -- A tag that the expected type does not yet name is the root's: the context is taken
      -- from the type, and the term's own type then names the tag (`E.el (html! …)`).
      if named?.isSome || (← instantiateMVars (e.getArg! 0)).isMVar then
        if let some ctx ← Admit.ctx? 4096 (e.getArg! 1) then
          return (← elabElement cache fuel o ctx (e.getArg! 1) true).2.1
  let ctx := defaultCtx t
  return (← elabElement cache fuel o ctx (← ctxExprCached cache ctx) true).2.1

end Whatwg.Html.Syntax
