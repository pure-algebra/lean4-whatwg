import Whatwg.Html.Content.Explain

/-!
# Whatwg.Html.Content.Values

Owner: the judgment of the attribute values of an SVG subtree (slices S4b and S4c of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-30). `valuesOk` says that each value of an SVG
attribute in the tree is of the attribute's grammar, where `Whatwg.Svg.Value.valueOk` holds
one: `d`, `points`, `viewBox` and the three transform attributes.

The judgment is an algebra of the walk (`Whatwg/Html/Node/Walk.lean`), beside the checker
`check` and the refusal `explainWalk`. Its state is the namespace alone: a value's grammar
depends on the attribute's name and on nothing of the content model. `explainValues` is its
located refusal, and `explainValues_none_iff` says that the refusal is absent exactly when the
judgment holds: the walk's fusion law at `Option.isNone`, as for the checker.

## Why this is not a part of `validIn`

`validIn` reads no SVG value, as before slice S4. The reason is a cost, and it is measured. A
value grammar reads characters, and a tree holds a `String`. The kernel opens a `String`
through its UTF-8 bytes: `String.toList` decodes them by a recursion on a proof of
well-foundedness. On this toolchain a literal of 433 characters takes the kernel 14 seconds to
open, and one of 1,855 characters fails with "deep recursion". The grammar's own reader takes
under a second on the first and three on the second, on a list of characters. The proofs of
this package that a tree is valid are evaluations of `validIn` by the kernel (`html!`,
`admits`). If `validIn` opened each `d`, a page with one icon would not elaborate.

So the value judgment is separate, and it has two routes that never open a long `String`:

- A value that a program builds is typed. `valueText` writes it, and `check_valueText` says
  that the text passes the grammar's check. It is a theorem of the grammar's retraction and of
  `String.toList_ofList`, and it evaluates nothing.
- A value that an author writes in `html!` is a literal. The elaborator runs the check on it
  when it builds the tree, and refuses a bad value at the attribute's token. That run is not a
  proof, and the tree's type does not carry it.

`valuesOk` itself evaluates in the kernel where the values are short.

What this module does not claim: that a tree `validIn` admits has values of their grammars;
that an attribute with no grammar here has a good value; or anything of an HTML attribute's
value, which `attrOk` judges inside `validIn`.
-/

namespace Whatwg.Html.Content

open Whatwg.Html (RawNode Walk)
open Whatwg.Svg.Value (Grammar valueOkByName)

/-! ## One element -/

/-- The namespace of an element, from the namespace it stands in and its name: an element of
an SVG subtree is an SVG element, and so is `svg` in HTML. -/
def Ns.ofElement : Ns → String → Ns
  | .svg, _ => .svg
  | .html, name => Ns.step .html name

/-- Each value of an SVG element's attributes is of its attribute's grammar. -/
def svgValuesOk (attrs : List (String × String)) : Bool :=
  attrs.all fun attr => valueOkByName attr.1.toList attr.2.toList

/-- The value test of one element. An HTML element passes: `attrOk` judges its values. -/
def Ns.valuesOk (ns : Ns) (name : String) (attrs : List (String × String)) : Bool :=
  match ns.ofElement name with
  | .svg => svgValuesOk attrs
  | .html => true

/-- In an SVG subtree every element is an SVG element. -/
theorem Ns.valuesOk_svg (name : String) (attrs : List (String × String)) :
    Ns.valuesOk .svg name attrs = svgValuesOk attrs := rfl

theorem svgValuesOk_nil : svgValuesOk [] = true := rfl

theorem svgValuesOk_cons (attr : String × String) (rest : List (String × String)) :
    svgValuesOk (attr :: rest) =
      (valueOkByName attr.1.toList attr.2.toList && svgValuesOk rest) := rfl

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

/-- The first value of an SVG attribute list that its grammar refuses. -/
def svgValuesReason? (attrs : List (String × String)) : Option Reason :=
  firstFault (fun name value => valueOkByName name.toList value.toList) (fun _ _ => .value) attrs

theorem isNone_svgValuesReason? (attrs : List (String × String)) :
    (svgValuesReason? attrs).isNone = svgValuesOk attrs :=
  isNone_firstFault _ _ attrs

/-- Why the value test of one element fails; `none` when it holds. -/
def Ns.valuesReason? (ns : Ns) (name : String) (attrs : List (String × String)) :
    Option Reason :=
  match ns.ofElement name with
  | .svg => svgValuesReason? attrs
  | .html => none

theorem Ns.isNone_valuesReason? (ns : Ns) (name : String) (attrs : List (String × String)) :
    (ns.valuesReason? name attrs).isNone = ns.valuesOk name attrs := by
  simp only [Ns.valuesReason?, Ns.valuesOk]
  cases ns.ofElement name with
  | html => rfl
  | svg => exact isNone_svgValuesReason? attrs

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

/-- An attribute whose grammar is `g` admits the text of each typed value of `g`. -/
theorem valueOkByName_valueText {α : Type} {g : Grammar α} {a : Whatwg.Svg.Schema.Attr}
    (hgrammar : ∀ text, Whatwg.Svg.Value.valueOk a text = g.check text) (name : String)
    (hname : Whatwg.Svg.Schema.Attr.ofChars? name.toList = some a) (v : α) :
    valueOkByName name.toList (valueText g v).toList = true := by
  simp only [valueOkByName, hname, hgrammar, check_valueText]

/-! ## The six attributes

The text of a typed value is admitted under its attribute's name. Each law is
`valueOkByName_valueText` at one name. -/

open Whatwg.Svg.Value

/-- `d` admits the text of typed path data. -/
theorem valueOkByName_d (p : PathData) :
    valueOkByName "d".toList (valueText PathData.grammar p).toList = true :=
  valueOkByName_valueText (a := .d) (fun _ => rfl) "d" (by decide +kernel) p

/-- `points` admits the text of typed points. -/
theorem valueOkByName_points (p : Points) :
    valueOkByName "points".toList (valueText Points.grammar p).toList = true :=
  valueOkByName_valueText (a := .points) (fun _ => rfl) "points" (by decide +kernel) p

/-- `viewBox` admits the text of a typed rectangle. -/
theorem valueOkByName_viewBox (v : ViewBox) :
    valueOkByName "viewBox".toList (valueText ViewBox.grammar v).toList = true :=
  valueOkByName_valueText (a := .viewBox) (fun _ => rfl) "viewBox" (by decide +kernel) v

/-- `transform` admits the text of a typed transform list. -/
theorem valueOkByName_transform (ts : TransformList) :
    valueOkByName "transform".toList (valueText TransformList.grammar ts).toList = true :=
  valueOkByName_valueText (a := .transform) (fun _ => rfl) "transform" (by decide +kernel) ts

/-- `gradientTransform` admits the text of a typed transform list. -/
theorem valueOkByName_gradientTransform (ts : TransformList) :
    valueOkByName "gradientTransform".toList (valueText TransformList.grammar ts).toList = true :=
  valueOkByName_valueText (a := .gradientTransform) (fun _ => rfl) "gradientTransform" (by decide +kernel) ts

/-- `patternTransform` admits the text of a typed transform list. -/
theorem valueOkByName_patternTransform (ts : TransformList) :
    valueOkByName "patternTransform".toList (valueText TransformList.grammar ts).toList = true :=
  valueOkByName_valueText (a := .patternTransform) (fun _ => rfl) "patternTransform" (by decide +kernel) ts

end Whatwg.Html.Content
