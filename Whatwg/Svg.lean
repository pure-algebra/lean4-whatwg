import Whatwg.Svg.Data.Universe
import Whatwg.Svg.Data.Mask
import Whatwg.Svg.Data.Mask.Laws
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
import Whatwg.Svg.Value.Bank
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
import Whatwg.Svg.Scene.Tree
import Whatwg.Svg.Scene.Tree.Edit
import Whatwg.Svg.Scene.Between
import Whatwg.Svg.Scene.Branch
import Whatwg.Svg.Scene.Score
import Whatwg.Svg.Scene.Plan
import Whatwg.Svg.Scene.Row
import Whatwg.Svg.Scene.Scale
import Whatwg.Svg.Scene.Metrics
import Whatwg.Svg.Scene.Label
import Whatwg.Svg.Scene.Cross
import Whatwg.Svg.Scene.Stage
import Whatwg.Svg.Scene.Frame
import Whatwg.Svg.Scene.Together
import Whatwg.Svg.Scene.Resume
import Whatwg.Svg.Scene.Strip
import Whatwg.Svg.Scene.Step
import Whatwg.Svg.Scene.Step.Laws
import Whatwg.Svg.Scene.Vector
import Whatwg.Svg.Scene.Machine
import Whatwg.Svg.Scene.Layers
import Whatwg.Svg.Scene.Extent
import Whatwg.Svg.Scene.Layout
import Whatwg.Svg.Scene.Ease
import Whatwg.Svg.Scene.Timeline
import Whatwg.Svg.Geometry.Monotone
import Whatwg.Svg.Geometry.Monotone.Laws
import Whatwg.Svg.Geometry.Ease
import Whatwg.Svg.Geometry.Grid
import Whatwg.Svg.Geometry.Easing
import Whatwg.Svg.Geometry.Stack
import Whatwg.Svg.Geometry.Moment
import Whatwg.Svg.Geometry.Spring
import Whatwg.Svg.Geometry.Spring.Laws
import Whatwg.Svg.Geometry.Spring.Resume
import Whatwg.Svg.Geometry.Spring.Follow

/-!
# Whatwg.Svg

SVG 2 for inline use: the elements, categories, content models and attributes of the W3C
standard, as the schema an HTML tree's SVG subtree is checked against. The plan is
`docs/SVG-PACKAGE-PLAN.md`. The authority is SVG 2 at the pin `vendor/w3c-svgwg-47e645ef/`
(`SPEC-MANIFEST.md`).

The library has five layers:

- `Whatwg.Svg.Data` names no schema: a finite universe, a set as a mask over it, and a name
  table with its two laws. `Mask.Laws` registers the laws of membership in the bank
  `Whatwg.Mask`, in a module of its own so that `Mask` imports no proof search;
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
  attribute on which element, and gives the type of an attribute's value. `Bank` registers the
  rules of totality in the bank `Whatwg.Syn`, in a module of its own so that no grammar imports
  proof search.
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
  Since slice S13: `Stack` is intervals in a row, each as long as its weight, with the ports
  at which the branches of a node leave it side by side. Since slice S15: `Moment` is a motion
  at every rational time, in exact numbers: what `Between` says of the whole moments holds
  between them, and the whole-number reading is within a unit and a thousandth of the travel
  of the exact one.
- `Whatwg.Svg.Scene` is what a picture is made of, with no rational number in it (slice
  S12), under the strict ceiling: a program that keeps its own proofs to that ceiling can
  neither call the geometry nor cite a law of it. `Moves` is things that move, and the law
  that a stored result stands for a computation that moves with its input. `Join` is the
  join of two lists by key. `Motion` is motion as data: easings in the two forms that CSS
  writes exactly, transitions, and the tracks of a step, with the law that a step's last
  moment is the next picture. Since slice S13 a track can change a shape, so that an edge stays
  joined to two things that move differently, and `Tree` places the nodes of a tree: each over
  the middle of its leaves, with the law that two subtrees of one node do not interleave.
  `Between` says what holds at every moment of a step: a gap that both pictures have is a gap
  of every moment between them, for things that take one timing and an easing in range.
  `Branch` is the width of each branch of a fork, with the law that the branches together
  carry what the trunk carries. `Score` puts tracks in order in time, with the law that a thing
  does not appear before what it comes from.

  Since slice S14: `Plan` is the motion of a join as one value, what a kept thing does, how a
  new thing enters and how an old one leaves, with the law that the step's last moment is the
  new picture. `Row` is a row whose lengths change: its edges move, so it tiles, keeps its
  length and keeps its gaps at every moment. `Scale` is a quantity as a length, with the values
  that the rounding ties. `Metrics` is what a host says of a face, and the width of a text as
  two bounds. `Label` fits a label to a room, and never shows two labels that differ as one
  text.

  Since slice S15: `Frame` is what a thing looks like at a moment, the reader of a motion: a
  later track of one property wins, as it does in CSS. `Stage` is a step in stages, where the
  kept things come to rest before the first new thing appears and each level of new things is
  done before the next begins. `Cross` says where two lines cross, with the laws that the
  crossings of a layered picture are the inversions of its order and that a step which keeps
  the order creates no crossing on the way.

  Since slice S16: `Together` is the law of a whole step that lean4-effect4's check of a look
  buys: kept things that take one timing with an easing in range keep, where they stand at
  every moment, each relation that their places have in both pictures. `Resume` is a step that
  is interrupted and resumes from where each thing is seen, with the law that nothing jumps.
  `Tree.Edit` says what an edit of a tree does to the placement of the nodes it did not touch:
  each is as it was, stretched, or shifted, and the shifted ones move as one. `Strip` is a
  sequence in the room of a word: lanes of states over the steps of a run, where one more step
  changes no earlier box.

The library imports no module of `Whatwg.Html` (ruling SV-6). The seam that admits `svg` in an
HTML tree is in `Whatwg.Html`, and so is the judgment of the values of a tree.
`generated/svg-dangling.tsv` lists the names the definitions cite and never declare.
-/
