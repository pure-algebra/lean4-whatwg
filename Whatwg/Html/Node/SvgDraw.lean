import Whatwg.Html.Node.SvgBuild
import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Outline

/-!
# Whatwg.Html.Node.SvgDraw

Owner: the elements of a picture from exact geometry (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-53). The constructors of
`Whatwg/Html/Node/SvgBuild.lean` take typed values, which are spellings. A program that lays
out a picture has numbers: points, boxes and cubic segments in `Rat`
(`Whatwg/Svg/Geometry/`). A constructor here takes those, and writes each coordinate once, at
a number of places that is three unless the caller says otherwise:

```
Svg.cubics edge [.fill .none, .stroke ink]            -- a chain of segments, open
Svg.loops (Cubic.ring box 6 1) [.fillRule true]       -- closed outlines, one `d`
Svg.curve .catmullRom points [.fill .none]            -- a curve through points
Svg.box b [.fill ground]                              -- `rect` of a box
Svg.dot p 2                                           -- `circle` at a point
Svg.label p "text"                                    -- `text` at a point
Svg.segment a b                                       -- `line` between two points
```

Each is a definition that unfolds to a constructor of `SvgBuild`, so a tree built with it is
proved as before: unfold it, and evaluate.

What this module does not claim: an element for an elliptical arc given by its centre.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value

namespace Svg

/-- `path` of a list of cubic segments, open: a chain is one subpath. -/
def cubics (segments : List Cubic) (more : List (SvgAttr .path) := []) (places : Nat := 3) :
    SvgNode :=
  path (.ofCubics segments places) more

/-- `path` of several closed outlines, each a subpath that ends in a closepath. -/
def loops (outlines : List (List Cubic)) (more : List (SvgAttr .path) := [])
    (places : Nat := 3) : SvgNode :=
  path (.ofLoops outlines places) more

/-- `path` of a curve through a list of points. -/
def curve (form : Curve) (points : List Vec) (more : List (SvgAttr .path) := [])
    (places : Nat := 3) : SvgNode :=
  path (Shape.line form points places) more

/-- `rect` of a box. A box of negative width or height is written with none. -/
def box (b : Box) (more : List (SvgAttr .rect) := []) (places : Nat := 3) : SvgNode :=
  rect (.ofRat b.x0 places) (.ofRat b.y0 places) (.ofRat b.width places) (.ofRat b.height places)
    more

/-- `circle` at a point. -/
def dot (center : Vec) (r : Rat) (more : List (SvgAttr .circle) := []) (places : Nat := 3) :
    SvgNode :=
  circle (.ofRat center.x places) (.ofRat center.y places) (.ofRat r places) more

/-- `line` between two points. -/
def segment (a b : Vec) (more : List (SvgAttr .line) := []) (places : Nat := 3) : SvgNode :=
  line (.ofRat a.x places) (.ofRat a.y places) (.ofRat b.x places) (.ofRat b.y places) more

/-- `text` at a point, with its character data. -/
def label (place : Vec) (content : String) (more : List (SvgAttr .text) := [])
    (places : Nat := 3) : SvgNode :=
  text (.ofRat place.x places) (.ofRat place.y places) content more

end Svg

end Whatwg.Html
