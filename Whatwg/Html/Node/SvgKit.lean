import Whatwg.Html.Content.Valid
import Whatwg.Html.Content.Explain
import Whatwg.Html.Node.SvgBuild
import Whatwg.Html.Node.SvgPaint
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgNest
import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Render
import Whatwg.Html.Print.Picture
import Whatwg.Html.Print.Xml
import Whatwg.Svg.Geometry.Affine
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Stroke
import Whatwg.Svg.Geometry.Stack
import Whatwg.Svg.Geometry.Moment
import Whatwg.Svg.Scene.Stage
import Whatwg.Svg.Scene.Frame
import Whatwg.Svg.Scene.Row
import Whatwg.Svg.Scene.Label
import Whatwg.Svg.Scene.Scale
import Whatwg.Svg.Scene.Cross
import Whatwg.Svg.Scene.Tree
import Whatwg.Svg.Scene.Branch
import Whatwg.Html.Node.SvgLit
import Whatwg.Html.Node.SvgKeyword
import Whatwg.Html.Node.SvgDefs

/-!
# Whatwg.Html.Node.SvgKit

Owner: the one import of a program that draws pictures (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-91). A port began with four to eleven imports, each of a
module of definitions that its writer had to know the place of. This module imports them, and
declares nothing:

```
import Whatwg.Html.Node.SvgKit

open Whatwg.Html Whatwg.Html.Content Whatwg.Svg.Value Whatwg.Svg.Scene
```

What it brings: the node and its checker, the constructors, the paints, the keywords, the
definitions that are referred to, the literals, exact geometry with its outlines, curves and
strokes, the scene with its motion, and the three printers. The list of the scene and of the
printers is that of `workshop/Closure.lean`, which says what lean4-effect4's view imports, with
the tree and the shares of a branch, which the probes and the stroke port name.

It reaches Lean alone: no module of proof search is in its closure, so a program that imports
it links none. The laws that a proof cites are in the law modules beside the definitions
(`Whatwg/Html/Node/SvgDefs/Laws.lean`, `Whatwg/Svg/Geometry/Stroke/Laws.lean` and their like),
and a file of proofs imports those it cites.

The four namespaces of the `open` are those of the standards that the kit models. One namespace
that holds every name again was tried and is not here: `export` gives a type a second name and
not the names under it, so `SvgNode.okAt` and `Cubic.roundRect` would stay out of reach, and a
module that writes second names needs an entry of the trust gate's list.

What this module does not claim: that the list is the whole kit. `Whatwg/Html.lean` and
`Whatwg/Svg.lean` import every module, the law modules and the markup term among them.
-/
