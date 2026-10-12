import Whatwg.Html.Content.Explain

/-!
# Whatwg.Html.Content.Values

Owner: the judgment of the attribute values of an SVG subtree (slices S4b to S5 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-30). `valuesOk` says that each value of an SVG
attribute in the tree is of the attribute's grammar, where the table of
`Whatwg/Svg/Value/Attribute.lean` gives the attribute a kind on its element: `d`, `points`,
`viewBox`, the three transform attributes, the four coordinates of `line`, and the nine
geometry properties on the elements they apply to.

The judgment is an algebra of the walk (`Whatwg/Html/Node/Walk.lean`), beside the checker
`check` and the refusal `explainWalk`. Its state is the namespace alone: a value's grammar
depends on the names of the element and of the attribute, and on nothing of the content model.
`explainValues` is its located refusal: the path of the element, the attribute, and the offset
in the value at which no reading of the grammar continues (`AttrFault.valueAt`).
`explainValues_none_iff` says that the refusal is absent exactly when the judgment holds: the
walk's fusion law at `Option.isNone`, as for the checker.

## Why this is not a part of `validIn`

`validIn` reads no SVG value, as before slice S4. The reason is a cost, and it is measured. A
value grammar reads characters, and a tree holds a `String`. The kernel opens a `String`
through its UTF-8 bytes: `String.toList` decodes them by a recursion on a proof of
well-foundedness. On this toolchain a literal of 433 characters takes the kernel 14 seconds to
open, and one of 1,855 characters fails with "deep recursion". The grammar's own reader takes
under a second on the first and three on the second, on a list of characters. The proofs of
this package that a tree is valid are evaluations of `validIn` by the kernel (`html!`,
`admits`). If `validIn` opened each `d`, a page with one icon would not elaborate.

So the value judgment is separate, and one route reaches it without opening a `String`: the
value is typed.

- `valueText` writes a typed value, and `check_valueText` says that the text passes the
  grammar's check. It is a theorem of the grammar's retraction and of `String.toList_ofList`,
  and it evaluates nothing. `valueOkByName_valueText` is the same law under the names a tree
  holds, for every kind of the table.
- The typed SVG node of `Whatwg/Html/Node/Svg.lean` holds every value at its type, and its
  connector `SvgNode.valuesOk_toRaw` is this judgment for the raw tree of every typed tree
  (slice S5, ruling SV-34). A program builds a typed tree, and `html!` builds one too: it
  reads a literal value with its grammar when it elaborates the markup and refuses a bad one
  at the attribute's token, with the offset.

`valuesOk` itself evaluates in the kernel where the values are short. It is the judgment of a
raw tree that no one typed: one that a caller reads from text. `SvgNode.ofRaw?` of
`Whatwg/Html/Node/SvgRead.lean` reads such a tree as a typed one.

What this module does not claim: that a tree `validIn` admits has values of their grammars;
that an attribute with no kind here has a good value; or anything of an HTML attribute's
value, which `attrOk` judges inside `validIn`.
-/

namespace Whatwg.Html.Content

open Whatwg.Html (RawNode Walk)
open Whatwg.Svg.Value (Grammar ValueKind kindOf valueOkByName explainValueByName)

/-! ## One element -/

/-- The namespace of an element, from the namespace it stands in and its name: an element of
an SVG subtree is an SVG element, and so is `svg` in HTML. -/
def Ns.ofElement : Ns → String → Ns
  | .svg, _ => .svg
  | .html, name => Ns.step .html name

/-- Each value of an SVG element's attributes is of its attribute's grammar on that element. -/
def svgValuesOk (element : String) (attrs : List (String × String)) : Bool :=
  attrs.all fun attr => valueOkByName element.toList attr.1.toList attr.2.toList

/-- The value test of one element. An HTML element passes: `attrOk` judges its values. -/
def Ns.valuesOk (ns : Ns) (name : String) (attrs : List (String × String)) : Bool :=
  match ns.ofElement name with
  | .svg => svgValuesOk name attrs
  | .html => true

/-- In an SVG subtree every element is an SVG element. -/
theorem Ns.valuesOk_svg (name : String) (attrs : List (String × String)) :
    Ns.valuesOk .svg name attrs = svgValuesOk name attrs := rfl

theorem svgValuesOk_nil (element : String) : svgValuesOk element [] = true := rfl

theorem svgValuesOk_cons (element : String) (attr : String × String)
    (rest : List (String × String)) :
    svgValuesOk element (attr :: rest) =
      (valueOkByName element.toList attr.1.toList attr.2.toList && svgValuesOk element rest) :=
  rfl

/-! ## The judgment -/

/-- The value judgment as an algebra of the walk: an element's own values, and its children's
results. -/
def valuesWalk : Walk Ns Bool where
  step := Ns.step
  element := fun ns name attrs _ results => ns.valuesOk name attrs && results.all id
  text := fun _ _ => true
  entity := fun _ _ => true
  comment := fun _ _ => true

/-- Each SVG value of the subtree is of its grammar, for a node that stands in `ns`. -/
def valuesAt (ns : Ns) (n : RawNode) : Bool := valuesWalk.run ns n

/-- The same over a forest. -/
def valuesAllAt (ns : Ns) (nodes : List RawNode) : Bool := (valuesWalk.runAll ns nodes).all id

/-- Each SVG value of the tree is of its grammar, where the package holds the grammar. -/
def valuesOk (n : RawNode) : Bool := valuesAt .html n

theorem valuesAt_element (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    valuesAt ns (.element name attrs children) =
      (ns.valuesOk name attrs && valuesAllAt (ns.step name) children) := by
  simp only [valuesAt, valuesAllAt, Walk.run_element, valuesWalk]

theorem valuesAllAt_nil (ns : Ns) : valuesAllAt ns [] = true := by
  simp only [valuesAllAt, Walk.runAll_nil, List.all_nil]

theorem valuesAllAt_cons (ns : Ns) (n : RawNode) (rest : List RawNode) :
    valuesAllAt ns (n :: rest) = (valuesAt ns n && valuesAllAt ns rest) := by
  simp only [valuesAllAt, valuesAt, Walk.runAll_cons, List.all_cons, id]

theorem valuesAt_text (ns : Ns) (content : String) : valuesAt ns (.text content) = true := by
  simp only [valuesAt, Walk.run, valuesWalk]

/-! ## The located refusal -/

/-- What is wrong with a value that its grammar refuses: the offset at which no reading
continues. A description for a message: `valueOkByName` decides, and no law reads the fault. -/
def valueFault (element name value : String) : AttrFault :=
  match explainValueByName element.toList name.toList value.toList with
  | some offset => .valueAt offset
  | none => .value

/-- The first value of an SVG element's attribute list that its grammar refuses. -/
def svgValuesReason? (element : String) (attrs : List (String × String)) : Option Reason :=
  firstFault (fun name value => valueOkByName element.toList name.toList value.toList)
    (valueFault element) attrs

theorem isNone_svgValuesReason? (element : String) (attrs : List (String × String)) :
    (svgValuesReason? element attrs).isNone = svgValuesOk element attrs :=
  isNone_firstFault _ _ attrs

/-- Why the value test of one element fails; `none` when it holds. -/
def Ns.valuesReason? (ns : Ns) (name : String) (attrs : List (String × String)) :
    Option Reason :=
  match ns.ofElement name with
  | .svg => svgValuesReason? name attrs
  | .html => none

theorem Ns.isNone_valuesReason? (ns : Ns) (name : String) (attrs : List (String × String)) :
    (ns.valuesReason? name attrs).isNone = ns.valuesOk name attrs := by
  simp only [Ns.valuesReason?, Ns.valuesOk]
  cases ns.ofElement name with
  | html => rfl
  | svg => exact isNone_svgValuesReason? name attrs

/-- The located refusal of the value judgment as an algebra of the walk. -/
def explainValuesWalk : Walk Ns (Option Refusal) where
  step := Ns.step
  element := fun ns name attrs _ results =>
    (here (ns.valuesReason? name attrs)).orElse fun _ => firstRefusal 0 results
  text := fun _ _ => none
  entity := fun _ _ => none
  comment := fun _ _ => none

/-- The first value in the subtree that its grammar refuses, and where. -/
def explainValuesAt (ns : Ns) (n : RawNode) : Option Refusal := explainValuesWalk.run ns n

/-- The first value in the tree that its grammar refuses, and where; `none` when each value is
of its grammar. -/
def explainValues (n : RawNode) : Option Refusal := explainValuesAt .html n

/-- The refusal is absent exactly when the judgment holds: the walk's fusion law at
`Option.isNone`. -/
theorem isNone_explainValuesAt (ns : Ns) (n : RawNode) :
    (explainValuesAt ns n).isNone = valuesAt ns n :=
  Walk.fusion explainValuesWalk valuesWalk Option.isNone (fun _ _ => rfl)
    (fun ns name attrs children results => by
      simp only [explainValuesWalk, valuesWalk, isNone_orElse, isNone_here,
        Ns.isNone_valuesReason?, isNone_firstRefusal])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ns n

/-- The located refusal of a value is complete against the value judgment. -/
theorem explainValues_none_iff (n : RawNode) : explainValues n = none ↔ valuesOk n = true := by
  rw [← Option.isNone_iff_eq_none, explainValues, isNone_explainValuesAt]
  exact Iff.rfl

/-! ## The text of a typed value -/

/-- The text of a typed value, as an attribute value: the `String` face of a grammar's
printer. -/
def valueText {α : Type} (g : Grammar α) (v : α) : String := String.ofList (g.print v)

theorem toList_valueText {α : Type} (g : Grammar α) (v : α) :
    (valueText g v).toList = g.print v := String.toList_ofList

/-- The text of a typed value passes its grammar's check. No evaluation opens the text: the
law is the grammar's retraction. -/
theorem check_valueText {α : Type} (g : Grammar α) (v : α) :
    g.check (valueText g v).toList = true := by
  rw [toList_valueText]
  exact g.check_print v

/-- Node V5: an attribute admits the text of each typed value of its kind, on an element where
the table gives it that kind. The two names are a tree's, and each is read by one evaluation of
a short name; the value's text is never opened. -/
theorem valueOkByName_valueText {t : Whatwg.Svg.Schema.Tag} {a : Whatwg.Svg.Schema.Attr}
    {k : ValueKind} (hkind : kindOf t a = some k) (element name : String)
    (helement : Whatwg.Svg.Schema.Tag.ofChars? element.toList = some t)
    (hname : Whatwg.Svg.Schema.Attr.ofChars? name.toList = some a) (v : k.carrier) :
    valueOkByName element.toList name.toList (valueText k.grammar v).toList = true := by
  rw [valueOkByName, helement, hname, toList_valueText]
  exact Whatwg.Svg.Value.valueOk_print hkind v

end Whatwg.Html.Content