import Whatwg.Html.Node.SvgRead
import Whatwg.Html.Print.Render

/-!
# WhatwgTest.Html.SvgRead

Readers, controls and finite evaluations of the reader of a typed SVG tree (slice S5 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-34; node P4 of the plan's section 6):
`Whatwg/Html/Node/SvgRead.lean`.

A finite evaluation reads a raw tree and prints the typed tree it gives, so each value shows in
its grammar's spelling. A control is a raw tree the reader refuses, or a typed tree outside the
premise of the retraction. A reader applies a law of the module at a real carrier: the
retraction at a typed tree built from constructors, for every value it holds.

What this battery does not claim: that the reader parses markup. It reads a `RawNode`, and the
decoder of `Whatwg/Html/Print/Render.lean` is the one that reads characters. Nor that a tree
which reads is valid: one line shows a tree that reads and that `validIn` refuses.
-/

namespace WhatwgTest.Html.SvgRead

open Whatwg.Html
open Whatwg.Html.Content (Ns Ctx validIn valuesOk)
open Whatwg.Svg.Value (PathData TransformList Length kindOf valueOk)

/-- An element node. -/
def el (name : String) (attrs : List (String × String) := []) (children : List RawNode := []) :
    RawNode :=
  .element name attrs children

/-- An `svg` element with no attribute. -/
def svg (children : List RawNode := []) : RawNode := el "svg" [] children

/-- The reading of a raw tree that stands in HTML, printed: the markup of its typed tree. -/
def reprint (r : RawNode) : Option String :=
  (SvgNode.ofRaw? .html r).map fun node => Print.render node.toRaw

/-! ## A picture reads, and its values print in their grammars' spellings -/

/-- A raw picture with a value of each kind, as an author may spell them: a `viewBox`, a
`transform`, a `d`, the lengths of `line`, a `class`, a custom data attribute and `xmlns`. -/
def picture : RawNode :=
  el "svg" [("xmlns", svgNamespace), ("viewBox", "0 0 24 24"), ("class", "icon"),
      ("data-kind", "demo")]
    [el "g" [("transform", "translate(1 2)  rotate(45)")]
      [el "path" [("d", "M 10 20 L 30 40 z")],
        el "line" [("x1", "0"), ("y1", "1.5em"), ("x2", "50%"), ("y2", " 10PX ")]]]

-- The picture reads. Its typed tree prints each typed value as its grammar spells it: the
-- transform with a comma, the path with no space, and the length in lower case with no white
-- space. The text of `class`, the data attribute and `xmlns` are as they were.
#guard reprint picture == some ("<svg xmlns=\"http://www.w3.org/2000/svg\" " ++
  "viewBox=\"0 0 24 24\" class=\"icon\" data-kind=\"demo\">" ++
  "<g transform=\"translate(1,2) rotate(45)\"><path d=\"M10,20L30,40z\"></path>" ++
  "<line x1=\"0\" y1=\"1.5em\" x2=\"50%\" y2=\"10px\"></line></g></svg>")

-- Control of what the module does not claim: reading and writing does not give the raw tree
-- back. The reader keeps a value and not its spelling.
#guard reprint picture != some (Print.render picture)
#guard reprint (svg [el "path" [("d", "M 10 20")]]) == some "<svg><path d=\"M10,20\"></path></svg>"

-- Reader of the fixed point: whatever the picture reads as, the raw tree of that reading
-- reads as the same typed tree.
example (node : SvgNode) (h : SvgNode.ofRaw? .html picture = some node) :
    SvgNode.ofRaw? .html node.toRaw = some node :=
  SvgNode.ofRaw?_toRaw_of_ofRaw? .html picture node h

-- Reader of `valuesAt_of_ofRaw?`: a reading of the picture gives the value judgment of the
-- picture itself, with no second run of a grammar.
example (node : SvgNode) (h : SvgNode.ofRaw? .html picture = some node) :
    valuesOk picture = true :=
  SvgNode.valuesAt_of_ofRaw? .html picture node h

/-! ## What the reader refuses -/

-- Control: a value that its grammar refuses refuses the tree. The path's last command has an
-- odd coordinate.
#guard (SvgNode.ofRaw? .html (svg [el "path" [("d", "M 10 20 L 40")]])).isNone
#guard (SvgNode.ofRaw? .html (svg [el "path" [("d", "M 10 20 L 40 50")]])).isSome

-- Controls: a name of no SVG element is refused, and names are compared exactly. An HTML
-- element is no SVG element in an SVG subtree.
#guard (SvgNode.ofRaw? .html (svg [el "blob"])).isNone
#guard (SvgNode.ofRaw? .html (svg [el "clippath"])).isNone
#guard (SvgNode.ofRaw? .html (svg [el "clipPath"])).isSome
#guard (SvgNode.ofRaw? .html (svg [el "div"])).isNone

-- Control: a name of no attribute of the schema is refused.
#guard (SvgNode.ofRaw? .html (svg [el "path" [("bogus", "1")]])).isNone
#guard (SvgNode.ofRaw? .html (svg [el "path" [("viewbox", "0 0 1 1")]])).isNone

-- Controls: `xmlns` and `xmlns:xlink` hold their one value each. Another value is refused,
-- and so is the other declaration's value.
#guard (SvgNode.ofRaw? .html (el "svg" [("xmlns", "http://www.w3.org/1999/xhtml")])).isNone
#guard (SvgNode.ofRaw? .html (el "svg" [("xmlns:xlink", svgNamespace)])).isNone
#guard (SvgNode.ofRaw? .html
  (el "svg" [("xmlns", svgNamespace), ("xmlns:xlink", xlinkNamespace)])).isSome

-- Control of what the module does not claim: the reader judges no structure. `rect` takes no
-- `d`, and the tree reads with the path typed. `validIn` refuses it.
#guard (SvgNode.ofRaw? .html (svg [el "rect" [("d", "M 0 0")]])).isSome &&
  !validIn Ctx.flow (svg [el "rect" [("d", "M 0 0")]])

-- The same for a name that repeats: the reader keeps both attributes, and `validIn` refuses
-- the element.
#guard (SvgNode.ofRaw? .html (svg [el "path" [("d", "M 0 0"), ("d", "M 1 1")]])).isSome &&
  !validIn Ctx.flow (svg [el "path" [("d", "M 0 0"), ("d", "M 1 1")]])

/-! ## One attribute -/

-- A custom data attribute's key is what follows `data-`, and its value is any text.
#guard match SvgAttr.ofPair? .path "data-kind" "M" with
  | some (.data "kind" "M") => true
  | _ => false

-- The table keys `x1` by the element. On `line` it is a length, and a text that is no length
-- is refused. On `linearGradient` it has no kind, and it holds the text.
#guard (SvgAttr.ofPair? .line "x1" "ten").isNone
#guard match SvgAttr.ofPair? .linearGradient "x1" "ten" with
  | some (.attr .x1 _) => true
  | _ => false

-- Reader of `ofPair?_toPair` at the kind the table keys by the element: the pair of every
-- typed length of `x1` on `line` reads back as the attribute.
example (l : Length) :
    SvgAttr.ofPair? .line (SvgAttr.attr (t := .line) .x1 l).toPair.1
      (SvgAttr.attr (t := .line) .x1 l).toPair.2 = some (.attr .x1 l) :=
  SvgAttr.ofPair?_toPair _

-- Reader of `isSome_readValue` at `d` on `path`: a text that passes the table's check reads.
example (s : String) (h : valueOk .path .d s.toList = true) :
    (readValue (kindOf .path .d) s).isSome = true :=
  (isSome_readValue .path .d s).trans h

/-! ## HTML content below an integration point -/

/-- A paragraph below `foreignObject`. -/
def foreign : RawNode :=
  svg [el "foreignObject" [] [el "p" [("class", "note")] [.text "hi", el "b" [] [.text "!"]]]]

-- The paragraph is HTML content there. The reader keeps it whole, as a raw subtree, and the
-- typed tree prints as the raw tree did.
#guard match SvgNode.ofRaw? .html foreign with
  | some (.element .svg [] [.element .foreignObject [] [.raw (.element "p" _ _) _]]) => true
  | _ => false
#guard reprint foreign == some (Print.render foreign)

/-- An `svg` below `foreignObject`. -/
def nested : RawNode := svg [el "foreignObject" [] [svg [el "path" [("d", "M 1 2")]]]]

-- An `svg` below `foreignObject` is an SVG element again, and it is read typed.
#guard match SvgNode.ofRaw? .html nested with
  | some (.element .svg [] [.element .foreignObject []
      [.element .svg [] [.element .path [.attr .d _] []]]]) => true
  | _ => false

-- Control: a raw subtree is kept only when its values pass. A bad path in an `svg` inside the
-- paragraph refuses the tree.
#guard (SvgNode.ofRaw? .html
  (svg [el "foreignObject" [] [el "p" [] [svg [el "path" [("d", "x")]]]]])).isNone

/-! ## The retraction -/

-- Reader of the retraction (P4) at one element, for every path: the law, and no evaluation of
-- a value. In an SVG subtree every element is placed, so the premise is `rfl`.
example (p : PathData) :
    SvgNode.ofRaw? .svg (SvgNode.element .path [.attr .d p] []).toRaw =
      some (.element .path [.attr .d p] []) :=
  SvgNode.ofRaw?_toRaw .svg _ rfl

/-- A typed picture for any path, transform list and length, with a namespace declaration, a
custom data attribute, a text attribute and HTML content below `foreignObject`. -/
def drawing (p : PathData) (ts : TransformList) (l : Length) : SvgNode :=
  .element .svg [.xmlns, .data "kind" "demo"]
    [.element .g [.attr .transform ts]
      [.element .path [.attr .d p, .attr .class "mark"] [],
        .element .line [.attr .x1 l] []],
      .element .foreignObject [] [.raw (.element "p" [] [.text "note"]) (by decide)]]

-- Reader of the retraction at a tree that stands in HTML, for every value it holds. The
-- premise is the placement, and it reads names alone: `svg` enters SVG, `g` stays there,
-- `foreignObject` returns to HTML, and `p` is HTML content there.
example (p : PathData) (ts : TransformList) (l : Length) :
    SvgNode.ofRaw? .html (drawing p ts l).toRaw = some (drawing p ts l) := by
  have hroot : Ns.ofElement .html Whatwg.Svg.Schema.Tag.svg.name = .svg := by decide +kernel
  have hsvg : Ns.step .html Whatwg.Svg.Schema.Tag.svg.name = .svg := by decide +kernel
  have hg : Ns.step .svg Whatwg.Svg.Schema.Tag.g.name = .svg := by decide +kernel
  have hforeign : Ns.step .svg Whatwg.Svg.Schema.Tag.foreignObject.name = .html := by
    decide +kernel
  have hp : Ns.ofElement .html "p" = .html := by decide +kernel
  apply SvgNode.ofRaw?_toRaw
  simp only [drawing, SvgNode.placed, SvgNode.placedAll, hroot, hsvg, hg, hforeign, hp]
  rfl

/-! ## The premise of the retraction -/

/-- A typed `g` alone. -/
def loose : SvgNode := .element .g [] []

-- Control of the premise `placed`: in HTML, `g` is no SVG element, so the typed `g` is not
-- placed there. Its raw tree reads as HTML content, kept raw, and not as the typed element.
#guard !loose.placed .html && loose.placed .svg
#guard match SvgNode.ofRaw? .html loose.toRaw with
  | some (.raw (.element "g" [] []) _) => true
  | _ => false

-- The same as a law: the raw tree of the typed `g` does not read back as it in HTML.
example : SvgNode.ofRaw? .html loose.toRaw ≠ some loose := by
  have hns : Ns.ofElement .html Whatwg.Svg.Schema.Tag.g.name = .html := by decide +kernel
  intro h
  obtain ⟨hsvg, _⟩ | ⟨_, _, hnode⟩ := SvgNode.ofRaw?_element_eq_some h
  · rw [hns] at hsvg
    exact nomatch hsvg
  · exact nomatch hnode

-- Control: a raw subtree that is no element is not placed. The reader gives a text node as
-- `SvgNode.text`, never as `SvgNode.raw`.
#guard !(SvgNode.raw (.text "x") (by decide)).placed .svg
#guard match SvgNode.ofRaw? .svg (SvgNode.raw (.text "x") (by decide)).toRaw with
  | some (.text "x") => true
  | _ => false

end WhatwgTest.Html.SvgRead
