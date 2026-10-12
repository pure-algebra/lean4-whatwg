import Whatwg.Html.Content.Values

/-!
# Whatwg.Html.Node.Svg

Owner: the typed SVG node (slice S5 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-34; point G4 of
`docs/research/2026-10-11-svg-seat-guidance-3.md`). An `SvgNode` is an SVG subtree whose
element is a tag of the schema and whose attribute holds a value of its type: the carrier of
its kind where the table of `Whatwg/Svg/Value/Attribute.lean` gives the attribute a kind on
the element, and text otherwise. `RawNode` is unchanged, and `SvgNode.toRaw` writes a typed
tree as one: each typed value prints by its grammar.

So a typed tree's values are right by their types. `SvgNode.valuesOk_toRaw` is the connector:
the raw tree of every typed tree passes the value judgment `valuesOk`. It is the grammar's
`check_print` at each attribute and the judgment's own unfolding at each node, and it
evaluates no text. The kernel never opens a value: a tree that a program builds, with numbers
it computes, has the law for nothing, and a tree that `html!` builds holds constructors and
numbers where the markup held a literal.

The structure of the tree is still the checker's. `validIn` of `toRaw` judges it, and it reads
names alone, so its evaluation forces no value.

What a typed node holds:

- `SvgNode.element t attrs children`: an SVG element. `t` is a tag of the schema, so a name of
  no schema is no term.
- `SvgAttr.attr a value`: an attribute of the schema, with a value of `AttrValue t a`. For `d`
  on any element that is a `PathData`, and for `class` it is a `String`.
- `SvgAttr.data key value`: a custom data attribute, `data-<key>`.
- `SvgAttr.xmlns` and `SvgAttr.xmlnsXlink`: the two namespace declarations, whose values the
  HTML Standard fixes (ruling SV-12).
- `SvgNode.text`, `entity` and `comment`: as in a raw tree.
- `SvgNode.raw node h`: a raw subtree, for the HTML content below `foreignObject`, `title` and
  `desc`. `h` says that the subtree's values pass wherever it stands, which holds by one
  evaluation of names when it holds no SVG value.

`readValue` reads a text as a value of an attribute's type, and `readValue_valueTextOf` is its
retraction (V1 at the type). The elaborator of `html!` and the reader of a raw tree
(`Whatwg/Html/Node/SvgRead.lean`) both read with it.

What this module does not claim: that a typed tree is valid. A typed tree may put an element
where the content model refuses it, name an attribute its element does not take, or repeat a
name: `validIn` judges that. Nor does it claim that an attribute with no kind holds a good
value: such an attribute holds text, as before.
-/

namespace Whatwg.Html

open Whatwg.Svg.Value (ValueKind kindOf AttrValue valueOkByName)
open Whatwg.Html.Content (Ns valuesAt valuesAllAt valuesOk explainValues svgValuesOk valueText)

/-! ## The text of a value -/

/-- The text of a value of an attribute's type: a typed value prints by its kind's grammar,
and text is itself. -/
def valueTextOf : (o : Option ValueKind) → ValueKind.typeOf o → String
  | some k, v => valueText k.grammar v
  | none, s => s

/-- Read a text as a value of an attribute's type: by the kind's grammar, and text as it is. -/
def readValue : (o : Option ValueKind) → String → Option (ValueKind.typeOf o)
  | some k, s => k.grammar.read s.toList
  | none, s => some s

/-- Node V1 at the type of a value: the text of a value reads back as the value. -/
theorem readValue_valueTextOf : ∀ (o : Option ValueKind) (v : ValueKind.typeOf o),
    readValue o (valueTextOf o v) = some v
  | some k, v => by
    show k.grammar.read (valueText k.grammar v).toList = some v
    rw [Content.toList_valueText]
    exact k.grammar.read_print v
  | none, _ => rfl


/-! ## An attribute -/

/-- The SVG namespace: the one value of `xmlns` on an SVG element. -/
def svgNamespace : String := "http://www.w3.org/2000/svg"

/-- The XLink namespace: the one value of `xmlns:xlink` on an SVG element. -/
def xlinkNamespace : String := "http://www.w3.org/1999/xlink"

/-- An attribute of the SVG element `t`. -/
inductive SvgAttr (t : Whatwg.Svg.Schema.Tag) where
  /-- An attribute of the schema, with a value of its type on this element: the carrier of its
  kind, or text where the table gives it none. -/
  | attr (a : Whatwg.Svg.Schema.Attr) (value : AttrValue t a)
  /-- A custom data attribute, `data-<key>`. -/
  | data (key value : String)
  /-- `xmlns`, with the SVG namespace. -/
  | xmlns
  /-- `xmlns:xlink`, with the XLink namespace. -/
  | xmlnsXlink

namespace SvgAttr

variable {t : Whatwg.Svg.Schema.Tag}

/-- The name and the text of an attribute, as a raw tree holds them. -/
def toPair : SvgAttr t → String × String
  | .attr a value => (a.name, valueTextOf (kindOf t a) value)
  | .data key value => ("data-" ++ key, value)
  | .xmlns => ("xmlns", svgNamespace)
  | .xmlnsXlink => ("xmlns:xlink", xlinkNamespace)

/-- The value of a typed attribute passes the check of its name on its element. -/
theorem valueOk_toPair (p : SvgAttr t) :
    valueOkByName t.name.toList p.toPair.1.toList p.toPair.2.toList = true := by
  have htag : t.name.toList = t.chars := String.toList_ofList
  cases p with
  | attr a value =>
    have hname : a.name.toList = a.chars := String.toList_ofList
    show valueOkByName t.name.toList a.name.toList (valueTextOf (kindOf t a) value).toList = true
    rw [htag, hname, Whatwg.Svg.Value.valueOkByName_chars, Whatwg.Svg.Value.valueOk]
    revert value
    show ∀ value : ValueKind.typeOf (kindOf t a), _
    generalize kindOf t a = o
    intro value
    cases o with
    | none => rfl
    | some k => exact Content.check_valueText k.grammar value
  | data key value =>
    show valueOkByName t.name.toList ("data-" ++ key).toList value.toList = true
    have hname : ("data-" ++ key).toList = 'd' :: 'a' :: 't' :: 'a' :: '-' :: key.toList := by
      rw [String.toList_append]
      rfl
    rw [htag, hname, valueOkByName, Whatwg.Svg.Schema.Tag.ofChars?_chars,
      Whatwg.Svg.Value.Attr.ofChars?_data]
  | xmlns =>
    show valueOkByName t.name.toList "xmlns".toList svgNamespace.toList = true
    have hname : Whatwg.Svg.Schema.Attr.ofChars? "xmlns".toList = none := by decide +kernel
    rw [htag, valueOkByName, Whatwg.Svg.Schema.Tag.ofChars?_chars, hname]
  | xmlnsXlink =>
    show valueOkByName t.name.toList "xmlns:xlink".toList xlinkNamespace.toList = true
    have hname : Whatwg.Svg.Schema.Attr.ofChars? "xmlns:xlink".toList = none := by decide +kernel
    rw [htag, valueOkByName, Whatwg.Svg.Schema.Tag.ofChars?_chars, hname]

/-- The values of a typed attribute list pass the checks of their names on their element. -/
theorem svgValuesOk_toPairs : ∀ attrs : List (SvgAttr t),
    svgValuesOk t.name (attrs.map toPair) = true
  | [] => rfl
  | first :: rest => by
    rw [List.map_cons, Content.svgValuesOk_cons, valueOk_toPair first, svgValuesOk_toPairs rest]
    rfl

end SvgAttr

/-! ## A node -/

/-- The values of a raw subtree pass wherever it stands: as HTML content and as SVG content. A
subtree with no SVG value passes by one evaluation of its names. -/
def RawNode.valuesAnywhere (node : RawNode) : Bool := valuesAt .html node && valuesAt .svg node

/-- A node of an SVG subtree whose values are typed. -/
inductive SvgNode where
  /-- An SVG element: a tag of the schema, its typed attributes and its children. -/
  | element (t : Whatwg.Svg.Schema.Tag) (attrs : List (SvgAttr t)) (children : List SvgNode)
  /-- Character data. -/
  | text (content : String)
  /-- A named character reference. -/
  | entity (name : String)
  /-- A comment. -/
  | comment (content : String)
  /-- A raw subtree whose values pass wherever it stands: the HTML content below an
  integration point. -/
  | raw (node : RawNode) (h : node.valuesAnywhere = true)

namespace SvgNode

mutual

/-- The raw tree of a typed tree: each name as the schema writes it, and each typed value as
its grammar prints it. -/
def toRaw : SvgNode → RawNode
  | .element t attrs children => .element t.name (attrs.map SvgAttr.toPair) (toRawAll children)
  | .text content => .text content
  | .entity name => .entity name
  | .comment content => .comment content
  | .raw node _ => node

/-- The raw trees of a typed forest. -/
def toRawAll : List SvgNode → List RawNode
  | [] => []
  | node :: rest => node.toRaw :: toRawAll rest

end

theorem toRawAll_eq_map (nodes : List SvgNode) : toRawAll nodes = nodes.map toRaw := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => rw [toRawAll, List.map_cons, ih]

mutual

/-- The connector, at a namespace: every value of the raw tree of a typed tree is of its
grammar, wherever the tree stands. The law evaluates no text: a typed value passes by its
grammar's `check_print`. -/
theorem valuesAt_toRaw (ns : Ns) : ∀ node : SvgNode, valuesAt ns node.toRaw = true
  | .element t attrs children => by
    rw [toRaw, Content.valuesAt_element, valuesAllAt_toRawAll (ns.step t.name) children,
      Bool.and_true, Ns.valuesOk]
    cases ns.ofElement t.name with
    | html => rfl
    | svg => exact SvgAttr.svgValuesOk_toPairs attrs
  | .text content => Content.valuesAt_text ns content
  | .entity name => by
    rw [toRaw]
    simp only [valuesAt, Walk.run, Content.valuesWalk]
  | .comment content => by
    rw [toRaw]
    simp only [valuesAt, Walk.run, Content.valuesWalk]
  | .raw node h => by
    rw [toRaw]
    simp only [RawNode.valuesAnywhere, Bool.and_eq_true] at h
    cases ns with
    | html => exact h.1
    | svg => exact h.2

/-- The connector over a forest. -/
theorem valuesAllAt_toRawAll (ns : Ns) : ∀ nodes : List SvgNode,
    valuesAllAt ns (toRawAll nodes) = true
  | [] => Content.valuesAllAt_nil ns
  | node :: rest => by
    rw [toRawAll, Content.valuesAllAt_cons, valuesAt_toRaw ns node, valuesAllAt_toRawAll ns rest]
    rfl

end

/-- Node V7, the connector: every value of the raw tree of a typed tree is of its grammar.
One law for every tree, and no evaluation. -/
theorem valuesOk_toRaw (node : SvgNode) : valuesOk node.toRaw = true := valuesAt_toRaw .html node

/-- The raw tree of a typed tree has no refused value. -/
theorem explainValues_toRaw (node : SvgNode) : explainValues node.toRaw = none :=
  (Content.explainValues_none_iff _).mpr (valuesOk_toRaw node)

end SvgNode

end Whatwg.Html
