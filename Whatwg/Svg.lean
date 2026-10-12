import Whatwg.Svg.Data.Universe
import Whatwg.Svg.Data.Mask
import Whatwg.Svg.Data.NameTable
import Whatwg.Svg.Schema.Tags
import Whatwg.Svg.Schema.Categories
import Whatwg.Svg.Schema.Attributes
import Whatwg.Svg.Schema.ContentModel
import Whatwg.Svg.Schema.Readings
import Whatwg.Svg.Schema.Universe
import Whatwg.Svg.Content.Context
import Whatwg.Svg.Value.Grammar
import Whatwg.Svg.Value.Grammar.Laws
import Whatwg.Svg.Value.Greedy
import Whatwg.Svg.Value.Deterministic
import Whatwg.Svg.Value.Refusal
import Whatwg.Svg.Value.Number
import Whatwg.Svg.Value.Cohort
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Value.Length
import Whatwg.Svg.Value.Extent
import Whatwg.Svg.Value.Lists
import Whatwg.Svg.Value.Attribute
import Whatwg.Svg.Geometry.Arith
import Whatwg.Svg.Geometry.Arith.Laws
import Whatwg.Svg.Geometry.Arith.Same
import Whatwg.Svg.Geometry.Order
import Whatwg.Svg.Geometry.Convert
import Whatwg.Svg.Geometry.Cursor
import Whatwg.Svg.Geometry.Pen
import Whatwg.Svg.Geometry.Pen.Laws
import Whatwg.Svg.Geometry.Affine
import Whatwg.Svg.Geometry.Affine.Laws
import Whatwg.Svg.Geometry.Vec
import Whatwg.Svg.Geometry.Rational
import Whatwg.Svg.Geometry.Rational.Laws
import Whatwg.Svg.Geometry.Cubic
import Whatwg.Svg.Geometry.Cubic.Laws
import Whatwg.Svg.Geometry.Box
import Whatwg.Svg.Geometry.Affine.Map
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Outline.Laws
import Whatwg.Svg.Geometry.Root
import Whatwg.Svg.Geometry.Root.Laws
import Whatwg.Svg.Geometry.Write
import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Geometry.Smooth
import Whatwg.Svg.Geometry.Near
import Whatwg.Svg.Geometry.Noise
import Whatwg.Svg.Geometry.Stroke
import Whatwg.Svg.Geometry.Stroke.Laws
import Whatwg.Svg.Scene.Moves
import Whatwg.Svg.Scene.Join
import Whatwg.Svg.Scene.Join.Laws
import Whatwg.Svg.Scene.Motion
import Whatwg.Svg.Scene.Motion.Laws
import Whatwg.Svg.Geometry.Grid
import Whatwg.Svg.Geometry.Easing

/-!
# Whatwg.Svg

SVG 2 for inline use: the elements, categories, content models and attributes of the W3C
standard, as the schema an HTML tree's SVG subtree is checked against. The plan is
`docs/SVG-PACKAGE-PLAN.md`. The authority is SVG 2 at the pin `vendor/w3c-svgwg-47e645ef/`
(`SPEC-MANIFEST.md`).

The library has five layers:

- `Whatwg.Svg.Data` names no schema: a finite universe, a set as a mask over it, and a name
  table with its two laws;
- `Whatwg.Svg.Schema.Tags`, `Categories`, `Attributes` and `ContentModel` are generated from
  the pin's definitions files by `lake exe whatwg_svgdefinitions`, which fails on a byte of
  drift. `Readings` is authored: it reads the four content models that the definitions state
  as a sentence. `Universe` is authored: it says what the generated data is an instance of;
- `Whatwg.Svg.Content.Context` is the position in an SVG subtree, its transition, and the
  judgments of one node;
- `Whatwg.Svg.Value.Grammar` is the one description that reads and prints an attribute value,
  with its retraction and the soundness of its reader proved once (slice S4a). Each grammar is
  one value of it: `Number` (the number and the separators), `Path`, `Points`, `ViewBox`,
  `Transform`, `Length` and `Extent` (slices S4b to S5). `Cohort` holds the law of a number's
  canonical value. `Greedy` states the reader's rule as a relation and proves the reader
  against it. `Deterministic` proves that the reader of a deterministic description accepts
  exactly the language of its expression, and `Refusal` gives a refused value the offset at
  which no reading continues. `Attribute` is the table that says which grammar judges which
  attribute on which element, and gives the type of an attribute's value.
- `Whatwg.Svg.Geometry` is what a program computes with, on those typed values (slice S10).
  It is under the repository's ordinary axiom ceiling, so that it can use the arithmetic of
  Lean's core library; the four layers above stay under the strict one. `Arith` is the exact
  sum, difference and product of the numbers, with the rounded quotients, `Order` their order,
  and `Convert` a number where a typed value stands. `Cursor` is what a path means for the
  point it has reached, by the path chapter, and `Pen` builds a path call by call. `Affine` is
  what a transform does to a point, in the order that CSS Transforms gives a list, with the
  view that is moved and scaled.

  Since slice S11 the geometry itself is exact: it computes in `Rat`, the rational numbers of
  core, and a number is rounded once, where it is written. `Vec` is a point and `Rational` the
  number that a typed value denotes, with the three roundings that write one. `Cubic` is one
  cubic Bézier segment, with the point at a parameter, the part between two parameters, and
  its velocity; `Box` a box, with the theorem that the box of a segment's four points holds
  the segment; `Affine.Map` an affine map with its inverse, the exact rotations, the map of a
  view box onto a viewport, and a segment under a map; `Outline` a box with round corners, a
  frame and an ellipse as segments; `Root` a square root to a number of places, and the
  normal of a segment. `Write` turns segments
  into a `Path` and a box into a `ViewBox`. `Shape` is the curves of d3-shape through a list
  of points, as segments: each form in d3's three ways, from end to end, open and closed.

  Since slice S12: `Smooth` says that the splines have no corner at a joint, and `Near` what
  the one rounding does to a curve. `Noise` is value noise with its bands, and `Stroke` a
  line as a filled outline whose width changes along it, with a collar, an arrowhead and a
  reveal. `Grid` is the seam between whole units and exact numbers: rounding commutes with a
  move by a whole count. `Easing` says what an easing of the layer below means exactly.
- `Whatwg.Svg.Scene` is what a picture is made of, with no rational number in it (slice
  S12), under the strict ceiling: a program that keeps its own proofs to that ceiling can
  neither call the geometry nor cite a law of it. `Moves` is things that move, and the law
  that a stored result stands for a computation that moves with its input. `Join` is the
  join of two lists by key. `Motion` is motion as data: easings in the two forms that CSS
  writes exactly, transitions, and the tracks of a step, with the law that a step's last
  moment is the next picture.

The library imports no module of `Whatwg.Html` (ruling SV-6). The seam that admits `svg` in an
HTML tree is in `Whatwg.Html`, and so is the judgment of the values of a tree.
`generated/svg-dangling.tsv` lists the names the definitions cite and never declare.
-/
