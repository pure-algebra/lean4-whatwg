import Whatwg.Html.Node.Svg

/-!
# Whatwg.Html.Node.SvgRead

Owner: the reader of a typed SVG tree (slice S5 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-34;
node P4 of the plan's section 6; point G4 of
`docs/research/2026-10-11-svg-seat-guidance-3.md`). `SvgNode.ofRaw?` reads a raw tree as a
typed one. It reads each name by the schema's name table and each value by the grammar of its
attribute on its element, with `readValue`. A name of no schema refuses the tree, and so does
a value that its grammar refuses.

What the reader does at a node that stands in the namespace `ns`:

- An element that is an SVG element there (`Ns.ofElement`) is read as `SvgNode.element`. Its
  name is a tag of the schema. Each attribute is read by `SvgAttr.ofPair?`, and the children
  are read in the namespace `Ns.step` gives.
- An element that is HTML content there, such as a paragraph below `foreignObject`, is kept
  whole, as `SvgNode.raw`, when its values pass wherever it stands
  (`RawNode.valuesAnywhere`), and it is refused otherwise.
- Text, an entity and a comment are the same constructors.

What `SvgAttr.ofPair?` reads, on the element `t`:

- a name of the schema, as `SvgAttr.attr`, with the value that `readValue` reads at the kind
  the table gives the attribute on `t`;
- a name that opens with `data-`, as `SvgAttr.data`, with what follows `data-` as its key;
- `xmlns` with the SVG namespace and `xmlns:xlink` with the XLink namespace, as the two
  declarations. Either name with another value is refused.

The three tests meet no common name: no attribute of the schema is named `xmlns` or
`xmlns:xlink`, and none opens with `data-` (`Attr.ofChars?_data`). The reader tests the schema
first, so the retraction at a schema attribute is the name table's own.

What is proved:

- `SvgAttr.ofPair?_toPair` (node P4 at an attribute): the pair of a typed attribute reads back
  as the attribute.
- `SvgNode.ofRaw?_toRaw` (node P4, the retraction): the raw tree of a typed tree reads back as
  the tree, for a tree in the placement `SvgNode.placed`. Each typed value reads back by its
  grammar's retraction (V1, `readValue_valueTextOf`), and no text is evaluated.
- `SvgNode.placed_of_ofRaw?`: every tree the reader gives is so placed. So the premise of the
  retraction is what the reader produces, and `SvgNode.ofRaw?_toRaw_of_ofRaw?` follows: the
  raw tree of a reading reads as the same typed tree.
- `SvgNode.valuesAt_of_ofRaw?`: a raw tree that reads has values of their grammars, by the
  value judgment `valuesAt`. `isSome_readValue` is its step at one value: a text reads as a
  value exactly when it passes the table's check.

What this module does not claim: that a tree which reads is valid. `validIn` judges the
structure, and the reader accepts an element where the content model refuses it, an attribute
that its element does not take, and a name that repeats. Nor that reading and writing a raw
tree gives the same raw tree back: the reader keeps a value and not its spelling, so `M 10 20`
reads and prints as `M10,20`. Nor where a value is refused: `Content.explainValues` of the raw
tree names the node, the attribute and the offset.
-/

namespace Whatwg.Html

open Whatwg.Svg.Value (kindOf valueOk valueOkByName)
open Whatwg.Html.Content (Ns valuesAt valuesAllAt svgValuesOk)

/-! ## A value -/

/-- A text reads as a value of the attribute `a` on the element `t` exactly when it passes the
table's check. -/
theorem isSome_readValue (t : Whatwg.Svg.Schema.Tag) (a : Whatwg.Svg.Schema.Attr) (s : String) :
    (readValue (kindOf t a) s).isSome = valueOk t a s.toList := by
  rw [valueOk]
  generalize kindOf t a = o
  cases o with
  | none => rfl
  | some k => rfl

/-! ## An attribute -/

namespace SvgAttr

variable {t : Whatwg.Svg.Schema.Tag}

/-- Read a name and a text as an attribute of the SVG element `t`. A name of the schema holds
the value that its kind's grammar reads. A name that opens with `data-` is a custom data
attribute. `xmlns` and `xmlns:xlink` hold their one value. Any other name is refused, and so
is a value that its grammar or its declaration refuses. -/
def ofPair? (t : Whatwg.Svg.Schema.Tag) (name value : String) : Option (SvgAttr t) :=
  match Whatwg.Svg.Schema.Attr.ofChars? name.toList with
  | some a => (readValue (kindOf t a) value).map (attr a)
  | none =>
    match name.toList with
    | 'd' :: 'a' :: 't' :: 'a' :: '-' :: key => some (data (String.ofList key) value)
    | _ =>
      if name = "xmlns" then
        if value = svgNamespace then some xmlns else none
      else if name = "xmlns:xlink" then
        if value = xlinkNamespace then some xmlnsXlink else none
      else none

/-- Node P4 at an attribute: the pair of a typed attribute reads back as the attribute. -/
theorem ofPair?_toPair (p : SvgAttr t) : ofPair? t p.toPair.1 p.toPair.2 = some p := by
  cases p with
  | attr a value =>
    show ofPair? t a.name (valueTextOf (kindOf t a) value) = some (attr a value)
    have hname : a.name.toList = a.chars := String.toList_ofList
    rw [ofPair?, hname, Whatwg.Svg.Schema.Attr.ofChars?_chars]
    show (readValue (kindOf t a) (valueTextOf (kindOf t a) value)).map (attr a) = _
    rw [readValue_valueTextOf]
    rfl
  | data key value =>
    show ofPair? t ("data-" ++ key) value = some (data key value)
    have hname : ("data-" ++ key).toList = 'd' :: 'a' :: 't' :: 'a' :: '-' :: key.toList := by
      rw [String.toList_append]
      rfl
    rw [ofPair?, hname, Whatwg.Svg.Value.Attr.ofChars?_data]
    show some (data (String.ofList key.toList) value) = _
    rw [String.ofList_toList]
  | xmlns =>
    show ofPair? t "xmlns" svgNamespace = some xmlns
    have hname := SvgAttr.ofChars?_xmlns
    rw [ofPair?, hname]
    show (if "xmlns" = "xmlns" then
      if svgNamespace = svgNamespace then some xmlns else none else _) = _
    rw [if_pos rfl, if_pos rfl]
  | xmlnsXlink =>
    show ofPair? t "xmlns:xlink" xlinkNamespace = some xmlnsXlink
    have hname := SvgAttr.ofChars?_xmlnsXlink
    have hne : ¬ ("xmlns:xlink" : String) = "xmlns" := by decide
    rw [ofPair?, hname]
    show (if "xmlns:xlink" = "xmlns" then _ else
      if "xmlns:xlink" = "xmlns:xlink" then
        if xlinkNamespace = xlinkNamespace then some xmlnsXlink else none else _) = _
    rw [if_neg hne, if_pos rfl, if_pos rfl]

/-- An attribute that reads has a value that passes the check of its name on its element. -/
theorem valueOk_of_ofPair? {name value : String} {p : SvgAttr t}
    (h : ofPair? t name value = some p) :
    valueOkByName t.chars name.toList value.toList = true := by
  rw [valueOkByName, Whatwg.Svg.Schema.Tag.ofChars?_chars]
  cases ha : Whatwg.Svg.Schema.Attr.ofChars? name.toList with
  | none => rfl
  | some a =>
    show valueOk t a value.toList = true
    rw [ofPair?, ha] at h
    have hmap : (readValue (kindOf t a) value).map (attr a) = some p := h
    rw [← isSome_readValue]
    cases hv : readValue (kindOf t a) value with
    | none =>
      rw [hv] at hmap
      exact nomatch hmap
    | some v => rfl

/-- Read each pair of a list as an attribute of the SVG element `t`. A pair that is refused
refuses the list. -/
def ofPairs? (t : Whatwg.Svg.Schema.Tag) : List (String × String) → Option (List (SvgAttr t))
  | [] => some []
  | pair :: rest =>
    match ofPair? t pair.1 pair.2, ofPairs? t rest with
    | some p, some ps => some (p :: ps)
    | _, _ => none

/-- The pairs of a typed attribute list read back as the list. -/
theorem ofPairs?_toPairs : ∀ attrs : List (SvgAttr t), ofPairs? t (attrs.map toPair) = some attrs
  | [] => rfl
  | first :: rest => by
    rw [List.map_cons, ofPairs?, ofPair?_toPair first, ofPairs?_toPairs rest]

/-- An attribute list that reads on an element has values that pass the checks of their names
on it. -/
theorem svgValuesOk_of_ofPairs? {element : String}
    (helement : Whatwg.Svg.Schema.Tag.ofChars? element.toList = some t) :
    ∀ (pairs : List (String × String)) (attrs : List (SvgAttr t)),
      ofPairs? t pairs = some attrs → svgValuesOk element pairs = true
  | [], _, _ => rfl
  | pair :: rest, attrs, h => by
    rw [ofPairs?] at h
    cases hp : ofPair? t pair.1 pair.2 with
    | none =>
      rw [hp] at h
      exact nomatch h
    | some p =>
      cases hps : ofPairs? t rest with
      | none =>
        rw [hp, hps] at h
        exact nomatch h
      | some ps =>
        rw [Content.svgValuesOk_cons, ← Whatwg.Svg.Schema.Tag.ofChars?_exact helement,
          valueOk_of_ofPair? hp, svgValuesOk_of_ofPairs? helement rest ps hps]
        rfl

end SvgAttr

/-! ## A node -/

namespace SvgNode

mutual

/-- Read a raw tree that stands in the namespace `ns` as a typed tree. An SVG element is read
by the schema: its name as a tag, each attribute with its attribute's grammar, and its children
in the namespace below it. An element that is HTML content there is kept whole when its values
pass wherever it stands. -/
def ofRaw? (ns : Ns) : RawNode → Option SvgNode
  | .element name attrs children =>
    match ns.ofElement name with
    | .svg =>
      match Whatwg.Svg.Schema.Tag.ofChars? name.toList with
      | some t =>
        match SvgAttr.ofPairs? t attrs, ofRawAll? (ns.step name) children with
        | some attrs, some children => some (.element t attrs children)
        | _, _ => none
      | none => none
    | .html =>
      if h : (RawNode.element name attrs children).valuesAnywhere = true then
        some (.raw (.element name attrs children) h)
      else none
  | .text content => some (.text content)
  | .entity name => some (.entity name)
  | .comment content => some (.comment content)

/-- The same over a forest. A node that is refused refuses the forest. -/
def ofRawAll? (ns : Ns) : List RawNode → Option (List SvgNode)
  | [] => some []
  | node :: rest =>
    match ofRaw? ns node, ofRawAll? ns rest with
    | some node, some rest => some (node :: rest)
    | _, _ => none

end

mutual

/-- The typed tree stands as the reader places a tree in the namespace `ns`: an element is an
SVG element there, and a raw subtree is an element that is HTML content there. -/
def placed (ns : Ns) : SvgNode → Bool
  | .element t _ children => ns.ofElement t.name == .svg && placedAll (ns.step t.name) children
  | .text _ => true
  | .entity _ => true
  | .comment _ => true
  | .raw (.element name _ _) _ => ns.ofElement name == .html
  | .raw (.text _) _ => false
  | .raw (.entity _) _ => false
  | .raw (.comment _) _ => false

/-- The same over a forest: each tree is placed in the namespace `ns`. -/
def placedAll (ns : Ns) : List SvgNode → Bool
  | [] => true
  | node :: rest => placed ns node && placedAll ns rest

end

mutual

/-- Node P4, the retraction: the raw tree of a placed typed tree reads back as the tree. Each
typed value reads back by its grammar's retraction (V1); no text is evaluated. -/
theorem ofRaw?_toRaw (ns : Ns) : ∀ node : SvgNode, node.placed ns = true →
    ofRaw? ns node.toRaw = some node
  | .element t attrs children, h => by
    rw [placed, Bool.and_eq_true, beq_iff_eq] at h
    have hname : t.name.toList = t.chars := String.toList_ofList
    rw [toRaw, ofRaw?]
    simp only [h.1, hname, Whatwg.Svg.Schema.Tag.ofChars?_chars, SvgAttr.ofPairs?_toPairs,
      ofRawAll?_toRawAll (ns.step t.name) children h.2]
  | .text content, _ => by rw [toRaw, ofRaw?]
  | .entity name, _ => by rw [toRaw, ofRaw?]
  | .comment content, _ => by rw [toRaw, ofRaw?]
  | .raw (.element name attrs children) hv, h => by
    rw [placed, beq_iff_eq] at h
    rw [toRaw, ofRaw?]
    simp only [h, dif_pos hv]
  | .raw (.text content) _, h => by
    rw [placed] at h
    exact nomatch h
  | .raw (.entity name) _, h => by
    rw [placed] at h
    exact nomatch h
  | .raw (.comment content) _, h => by
    rw [placed] at h
    exact nomatch h

/-- The retraction over a forest. -/
theorem ofRawAll?_toRawAll (ns : Ns) : ∀ nodes : List SvgNode, placedAll ns nodes = true →
    ofRawAll? ns (toRawAll nodes) = some nodes
  | [], _ => by rw [toRawAll, ofRawAll?]
  | node :: rest, h => by
    rw [placedAll, Bool.and_eq_true] at h
    rw [toRawAll, ofRawAll?, ofRaw?_toRaw ns node h.1, ofRawAll?_toRawAll ns rest h.2]

end

/-! ## What a reading says of the raw tree -/

/-- An element that reads is one of two: an SVG element whose name, attributes and children
read, or HTML content whose values pass wherever it stands. -/
theorem ofRaw?_element_eq_some {ns : Ns} {name : String} {attrs : List (String × String)}
    {children : List RawNode} {node : SvgNode}
    (h : ofRaw? ns (.element name attrs children) = some node) :
    (ns.ofElement name = .svg ∧
      ∃ (t : Whatwg.Svg.Schema.Tag) (typed : List (SvgAttr t)) (nodes : List SvgNode),
        Whatwg.Svg.Schema.Tag.ofChars? name.toList = some t ∧
        SvgAttr.ofPairs? t attrs = some typed ∧
        ofRawAll? (ns.step name) children = some nodes ∧ node = .element t typed nodes) ∨
    (ns.ofElement name = .html ∧
      ∃ hv : (RawNode.element name attrs children).valuesAnywhere = true,
        node = .raw (.element name attrs children) hv) := by
  rw [ofRaw?] at h
  cases hns : ns.ofElement name with
  | svg =>
    simp only [hns] at h
    cases ht : Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | none =>
      rw [ht] at h
      exact nomatch h
    | some t =>
      simp only [ht] at h
      cases hattrs : SvgAttr.ofPairs? t attrs with
      | none =>
        rw [hattrs] at h
        exact nomatch h
      | some typed =>
        cases hchildren : ofRawAll? (ns.step name) children with
        | none =>
          rw [hattrs, hchildren] at h
          exact nomatch h
        | some nodes =>
          rw [hattrs, hchildren] at h
          exact .inl ⟨rfl, t, typed, nodes, rfl, hattrs, rfl, (Option.some.inj h).symm⟩
  | html =>
    simp only [hns] at h
    obtain hv | hv := Bool.eq_false_or_eq_true (RawNode.element name attrs children).valuesAnywhere
    · rw [dif_pos hv] at h
      exact .inr ⟨rfl, hv, (Option.some.inj h).symm⟩
    · rw [dif_neg (by rw [hv]; exact Bool.false_ne_true)] at h
      exact nomatch h

/-- A forest that reads has a first tree that reads and a rest that reads. -/
theorem ofRawAll?_cons_eq_some {ns : Ns} {r : RawNode} {rest : List RawNode}
    {nodes : List SvgNode} (h : ofRawAll? ns (r :: rest) = some nodes) :
    ∃ (node : SvgNode) (others : List SvgNode),
      ofRaw? ns r = some node ∧ ofRawAll? ns rest = some others ∧ nodes = node :: others := by
  rw [ofRawAll?] at h
  cases hr : ofRaw? ns r with
  | none =>
    rw [hr] at h
    exact nomatch h
  | some node =>
    cases hrest : ofRawAll? ns rest with
    | none =>
      rw [hr, hrest] at h
      exact nomatch h
    | some others =>
      rw [hr, hrest] at h
      exact ⟨node, others, rfl, rfl, (Option.some.inj h).symm⟩

mutual

/-- A raw tree that reads as a typed tree has values of their grammars. -/
theorem valuesAt_of_ofRaw? (ns : Ns) : ∀ (r : RawNode) (node : SvgNode),
    ofRaw? ns r = some node → valuesAt ns r = true
  | .element name attrs children, _, h => by
    obtain ⟨hns, t, typed, nodes, ht, hattrs, hchildren, _⟩ | ⟨_, hv, _⟩ :=
      ofRaw?_element_eq_some h
    · rw [Content.valuesAt_element, Ns.valuesOk, hns]
      show (svgValuesOk name attrs && valuesAllAt (ns.step name) children) = true
      rw [SvgAttr.svgValuesOk_of_ofPairs? ht attrs typed hattrs,
        valuesAllAt_of_ofRawAll? (ns.step name) children nodes hchildren]
      rfl
    · simp only [RawNode.valuesAnywhere, Bool.and_eq_true] at hv
      cases ns with
      | html => exact hv.1
      | svg => exact hv.2
  | .text content, _, _ => Content.valuesAt_text ns content
  | .entity name, _, _ => by simp only [valuesAt, Walk.run, Content.valuesWalk]
  | .comment content, _, _ => by simp only [valuesAt, Walk.run, Content.valuesWalk]

/-- The same over a forest. -/
theorem valuesAllAt_of_ofRawAll? (ns : Ns) : ∀ (rs : List RawNode) (nodes : List SvgNode),
    ofRawAll? ns rs = some nodes → valuesAllAt ns rs = true
  | [], _, _ => Content.valuesAllAt_nil ns
  | r :: rest, _, h => by
    obtain ⟨node, others, hr, hrest, _⟩ := ofRawAll?_cons_eq_some h
    rw [Content.valuesAllAt_cons, valuesAt_of_ofRaw? ns r node hr,
      valuesAllAt_of_ofRawAll? ns rest others hrest]
    rfl

end

mutual

/-- A tree that the reader gives is placed in the namespace it was read in. So the premise of
the retraction is what the reader produces. -/
theorem placed_of_ofRaw? (ns : Ns) : ∀ (r : RawNode) (node : SvgNode),
    ofRaw? ns r = some node → node.placed ns = true
  | .element name attrs children, _, h => by
    obtain ⟨hns, t, typed, nodes, ht, _, hchildren, hnode⟩ | ⟨hns, hv, hnode⟩ :=
      ofRaw?_element_eq_some h
    · have hname : t.name = name := by
        rw [Whatwg.Svg.Schema.Tag.name, Whatwg.Svg.Schema.Tag.ofChars?_exact ht,
          String.ofList_toList]
      rw [hnode, placed, hname, hns,
        placedAll_of_ofRawAll? (ns.step name) children nodes hchildren]
      rfl
    · rw [hnode, placed, hns]
      rfl
  | .text content, _, h => by
    rw [ofRaw?] at h
    rw [← Option.some.inj h, placed]
  | .entity name, _, h => by
    rw [ofRaw?] at h
    rw [← Option.some.inj h, placed]
  | .comment content, _, h => by
    rw [ofRaw?] at h
    rw [← Option.some.inj h, placed]

/-- The same over a forest. -/
theorem placedAll_of_ofRawAll? (ns : Ns) : ∀ (rs : List RawNode) (nodes : List SvgNode),
    ofRawAll? ns rs = some nodes → placedAll ns nodes = true
  | [], _, h => by
    rw [ofRawAll?] at h
    rw [← Option.some.inj h, placedAll]
  | r :: rest, _, h => by
    obtain ⟨node, others, hr, hrest, hnodes⟩ := ofRawAll?_cons_eq_some h
    rw [hnodes, placedAll, placed_of_ofRaw? ns r node hr,
      placedAll_of_ofRawAll? ns rest others hrest]
    rfl

end

/-- A reading is a fixed point of writing and reading: the raw tree of a tree that the reader
gives reads as that tree. -/
theorem ofRaw?_toRaw_of_ofRaw? (ns : Ns) (r : RawNode) (node : SvgNode)
    (h : ofRaw? ns r = some node) : ofRaw? ns node.toRaw = some node :=
  ofRaw?_toRaw ns node (placed_of_ofRaw? ns r node h)

end SvgNode

end Whatwg.Html
