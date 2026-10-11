import Whatwg.Html

/-!
# WhatwgTest.Html.Svg

Readers, controls and finite evaluations of the seam (slice S3b of `docs/SVG-PACKAGE-PLAN.md`):
`Whatwg/Html/Svg.lean` and the checker of `Whatwg/Html/Content/Valid.lean`. Each line builds a
small tree and evaluates `validIn`, or applies a law of the seam at a real position.

A reader applies a law at a carrier: `Pos.child_ns`, `Pos.excl_le_child`, `validIn_element_eq`,
`validIn_svg`, `restore_tag`. A control is a tree the checker refuses, beside the tree it
accepts. The picture at the end has the elements and attributes that lean4-effect4's picture
writer emits today (`tools/Tools/View/Output.lean`, read at `707b9a01`).

What this battery does not claim: that a browser parses a printed tree back to the tree. No
parser exists in this package (ruling HP-8). The printer is slice S3d.
-/

namespace WhatwgTest.Html.Svg

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Schema (Tag)

/-- An element node. -/
def el (name : String) (attrs : List (String × String) := []) (children : List RawNode := []) :
    RawNode :=
  .element name attrs children

/-- An `svg` element with no attribute. -/
def svg (children : List RawNode := []) : RawNode := el "svg" [] children

/-! ## Where `svg` stands -/

-- `svg` is flow, phrasing, embedded and palpable content: it stands in a paragraph, in a
-- figure and in a table cell.
#guard validIn Ctx.flow (el "p" [] [svg])
#guard validIn Ctx.phrasing svg
#guard validIn Ctx.flow (el "figure" [] [svg, el "figcaption" [] [.text "A chart"]])
#guard validIn Ctx.flow (el "table" [] [el "tbody" [] [el "tr" [] [el "td" [] [svg]]]])

-- Controls: it stands in no `head`, and in no list outside an item.
#guard !validIn Ctx.metadata svg
#guard !validIn Ctx.flow (el "ul" [] [svg])

-- Control: a foreign child takes its place in an ordered model. The sequence of `figure`
-- has one `figcaption`, first or last.
#guard !validIn Ctx.flow (el "figure" [] [svg, el "figcaption" [] [.text "x"], svg])

-- Control: `math` is a foreign tag of the category lists, and MathML is not modelled.
#guard Tag.ofForeignName? "math" == some .math
#guard !validIn Ctx.flow (el "math")

-- Controls: a name is compared exactly, and a name of no schema is refused at every position.
#guard !validIn Ctx.flow (el "SVG")
#guard !validIn Ctx.flow (svg [el "clippath"])
#guard !validIn Ctx.flow (svg [el "metadata" [] [el "x"]])
#guard validIn Ctx.flow (svg [el "metadata" [] [.text "t", el "rect"]])

/-! ## Inside the SVG subtree -/

-- Control: an HTML element is no SVG element.
#guard !validIn Ctx.flow (svg [el "div"])

-- Character data stands where the SVG model admits it: in `text` and `style`, not in `svg`.
#guard validIn Ctx.flow (svg [el "text" [] [.text "x", el "tspan" [] [.text "y"]]])
#guard validIn Ctx.flow (svg [el "style" [] [.text "@keyframes k { to { opacity: 1 } }"]])
#guard !validIn Ctx.flow (svg [.text "x"])
#guard !validIn Ctx.flow (svg [el "rect" [] [.text "x"]])

-- A comment stands anywhere in an SVG subtree.
#guard validIn Ctx.flow (svg [.comment "c", el "style" [] [.comment "c"]])

-- `a` reads the outer model, removes `a` from its own, and excludes no descendant.
#guard validIn Ctx.flow (svg [el "a" [] [el "rect"]])
#guard !validIn Ctx.flow (svg [el "a" [] [el "a"]])
#guard validIn Ctx.flow (svg [el "a" [] [el "g" [] [el "a"]]])
#guard validIn Ctx.flow (svg [el "switch" [] [el "a" [] [el "defs"]]])
#guard !validIn Ctx.flow (svg [el "switch" [] [el "defs"]])

-- The counts: a lighting filter takes exactly one light source.
#guard validIn Ctx.flow (svg [el "filter" [] [el "feDiffuseLighting" [] [el "fePointLight"]]])
#guard !validIn Ctx.flow (svg [el "filter" [] [el "feDiffuseLighting"]])
#guard !validIn Ctx.flow
  (svg [el "filter" [] [el "feDiffuseLighting" [] [el "fePointLight", el "feSpotLight"]]])

/-! ## The integration points -/

-- Below `foreignObject` the children are flow content; below `title` and `desc`, phrasing.
#guard validIn Ctx.flow (svg [el "foreignObject" [] [el "div" [] [.text "x"]]])
#guard validIn Ctx.flow (svg [el "title" [] [.text "A chart", el "em" [] [.text "x"]]])
#guard validIn Ctx.flow (svg [el "desc" [] [.text "What it shows"]])
#guard !validIn Ctx.flow (svg [el "title" [] [el "div"]])
#guard !validIn Ctx.flow (svg [el "desc" [] [el "div"]])

-- Control: an SVG element is no HTML element below an integration point, and `svg` is.
#guard !validIn Ctx.flow (svg [el "foreignObject" [] [el "rect"]])
#guard validIn Ctx.flow (svg [el "foreignObject" [] [el "div" [] [svg [el "rect"]]]])

-- The HTML exclusions pass through the SVG subtree: an `a` excludes an `a` below it.
#guard validIn Ctx.flow (el "div" [] [svg [el "foreignObject" [] [el "a" [("href", "v")]]]])
#guard !validIn Ctx.flow
  (el "a" [("href", "u")] [svg [el "foreignObject" [] [el "a" [("href", "v")]]]])
#guard ((Pos.html Ctx.flow).child "a" |>.child "svg" |>.child "foreignObject").excl.a

-- Reader of X1: the exclusions at `svg` hold those of the position that holds it.
example : ((Pos.html Ctx.flow).child "a").excl.le
    (((Pos.html Ctx.flow).child "a").child "svg").excl = true :=
  Pos.excl_le_child _ "svg"

-- Reader of T2: the namespace along a path is the namespace automaton's.
example : (((Pos.html Ctx.flow).child "svg").child "foreignObject").ns = Ns.html := by
  rw [Pos.child_ns, Pos.child_ns]
  decide

example : (((Pos.html Ctx.flow).child "svg").child "g").ns = Ns.svg := by
  rw [Pos.child_ns, Pos.child_ns]
  decide

-- Controls of the automaton: an HTML element named `title` enters no SVG, and `desc` returns.
#guard Ns.step .html "title" == .html && Ns.step .svg "desc" == .html && Ns.step .svg "a" == .svg

/-! ## Attributes -/

-- An SVG element takes its schema's attributes, a custom data attribute, and the two
-- namespace declarations with their exact values.
#guard validIn Ctx.flow
  (el "svg" [("viewBox", "0 0 1 1"), ("xmlns", "http://www.w3.org/2000/svg"),
    ("xmlns:xlink", "http://www.w3.org/1999/xlink"), ("data-look", "x"), ("role", "img"),
    ("aria-label", "l")])

-- Controls: a name in another case, another namespace, and a repeated name.
#guard !validIn Ctx.flow (el "svg" [("viewbox", "0 0 1 1")])
#guard !validIn Ctx.flow (el "svg" [("xmlns", "http://www.w3.org/1999/xhtml")])
#guard !validIn Ctx.flow (el "svg" [("class", "a"), ("class", "b")])

-- Control: an HTML attribute that SVG does not give the element.
#guard !validIn Ctx.flow (svg [el "rect" [("href", "u")]])

-- Readers of N2: the tree construction restores a name from its lower-case form.
example : restore Whatwg.Html.Schema.Foreign.svgTagNames "clippath".toList = "clipPath".toList :=
  restore_tag .clipPath

example : restore Whatwg.Html.Schema.Foreign.svgAttrNames "viewbox".toList = "viewBox".toList :=
  restore_attr .viewBox

/-! ## The equations that bound the change -/

-- Reader of C1: at an HTML element name the checker is the conjunction it was.
example (children : List RawNode) :
    validIn Ctx.flow (el "div" [] children) =
      (Ctx.flow.admitsWith .div [] && attrsOk .div [] && seqOk (Ctx.flow.child .div) .div children &&
        validAll (Ctx.flow.child .div) children) :=
  validIn_element_eq Ctx.flow (by decide) [] children

-- Reader of C2: a name that is no HTML element and not `svg` is refused, whatever it holds.
example (children : List RawNode) : validIn Ctx.flow (el "math" [] children) = false :=
  validIn_unknown Ctx.flow (by decide) (by decide) [] children

/-! ## The consumer's picture -/

/-- A picture with the shape that the consumer's writer emits: a described root, a style with
an animation, a clip path, and marks with a key. -/
def picture : RawNode :=
  el "svg"
    [("class", "figure"), ("viewBox", "0 0 320 200"), ("width", "320"), ("height", "200"),
     ("role", "img"), ("aria-label", "A chart"), ("data-look", "plain")]
    [el "title" [] [.text "A chart"],
     el "desc" [] [.text "Two bars and a label"],
     el "style" [] [.text ".mark { animation: rise 1s } @keyframes rise { from { opacity: 0 } }"],
     el "defs" [] [el "clipPath" [("id", "plot")] [el "rect" [("x", "0"), ("y", "0"), ("width", "320"), ("height", "200")]]],
     el "g" [("class", "marks"), ("clip-path", "url(#plot)")]
       [el "rect" [("class", "mark"), ("x", "10"), ("y", "20"), ("width", "30"), ("height", "160"),
          ("fill", "var(--ink)"), ("fill-opacity", "0.8"), ("data-key", "a")],
        el "path" [("class", "mark"), ("d", "M 10 20 L 40 180"), ("fill", "none"),
          ("stroke", "currentColor"), ("stroke-width", "1.5"), ("data-key", "b")],
        el "text" [("class", "label"), ("x", "10"), ("y", "195"), ("font-size", "12"),
          ("transform", "scale(1)"), ("xml:space", "preserve")] [.text "a  b"]]]

-- The picture stands in a figure, in a paragraph and alone in flow content.
#guard validIn Ctx.flow (el "figure" [] [picture, el "figcaption" [] [.text "Figure 1"]])
#guard validIn Ctx.flow (el "p" [] [picture])
#guard validIn Ctx.flow picture

end WhatwgTest.Html.Svg
