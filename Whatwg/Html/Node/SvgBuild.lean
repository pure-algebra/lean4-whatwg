import Whatwg.Html.Node.SvgValid
import Whatwg.Html.Node.SvgPaint
import Whatwg.Svg.Geometry.Convert

/-!
# Whatwg.Html.Node.SvgBuild

Owner: the constructors a program writes a picture with (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-47). `SvgNode.element` takes a tag, a list of attributes
and the children, and a caller writes the geometry of each element as attributes by name. A
constructor here takes that geometry by position, with the type the table of kinds gives it on
that element, and a list of further attributes:

```
Svg.rect 0 0 30 20 [.fill .none, .stroke (Rgb.ofNat 0x14110d)]
Svg.path d [.strokeWidth 2]
Svg.text 4 14 "label"
```

- `Svg.svg`, `g`, `defs`, `clipPath`, `rect`, `circle`, `ellipse`, `line`, `path`, `polyline`,
  `polygon`, `text` and `image` are the elements.
- `Svg.clipped` is a clip path and the group it clips, with one identifier written in both.
- `Svg.Frame` is the outer `svg` of a picture: a size in pixels, a ratio of user units to a
  pixel, and margins. `Frame.svg` writes `width`, `height` and `viewBox`, and `Frame.inner` the
  group inside the margins.

Each constructor is a definition that unfolds to `SvgNode.element`, so every law of
`Whatwg/Html/Node/SvgValid.lean` reads it, and a tree built with it is proved as before. The
laws at the end say when a frame and a clipped group pass, with their children free.

What a frame means, by the chapter Coordinate Systems of SVG 2 (sealed at
`vendor/w3c-svgwg-47e645ef/master/coords.html`): the `viewBox` is mapped onto the viewport of
`width` by `height`. `Frame.aspect` says that the two have one aspect ratio, so the default
`preserveAspectRatio`, which scales uniformly, fills the viewport and moves nothing: one pixel
is `ratio` user units on both axes. That reading is of a frame whose ratio and sizes are
positive: the chapter says that a view box of no width or no height disables rendering, and a
ratio of zero writes one.

What this module does not claim: the mapping itself as a transform, which divides; or that a
caller's further attributes are taken by the element, which `SvgAttr.allOk` judges.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Html.Content (Ctx Pos)
open Whatwg.Svg.Value

namespace Svg

/-! ## Elements -/

/-- `svg`, with the namespace declaration first. -/
def svg (more : List (SvgAttr .svg)) (children : List SvgNode) : SvgNode :=
  .element .svg (.xmlns :: more) children

/-- `g`: a group. -/
def g (more : List (SvgAttr .g)) (children : List SvgNode) : SvgNode := .element .g more children

/-- `defs`: elements that are referenced and not drawn. -/
def defs (children : List SvgNode) : SvgNode := .element .defs [] children

/-- `clipPath`, by its identifier and the shapes that clip. -/
def clipPath (id : String) (children : List SvgNode) : SvgNode :=
  .element .clipPath [.ident id] children

/-- `rect`, by its corner and its size. -/
def rect (x y : Length) (width height : AutoExtent) (more : List (SvgAttr .rect) := []) :
    SvgNode :=
  .element .rect ([.attr .x x, .attr .y y, .attr .width width, .attr .height height] ++ more) []

/-- `circle`, by its centre and its radius. -/
def circle (cx cy : Length) (r : Extent) (more : List (SvgAttr .circle) := []) : SvgNode :=
  .element .circle ([.attr .cx cx, .attr .cy cy, .attr .r r] ++ more) []

/-- `ellipse`, by its centre and its two radii. -/
def ellipse (cx cy : Length) (rx ry : AutoExtent) (more : List (SvgAttr .ellipse) := []) :
    SvgNode :=
  .element .ellipse ([.attr .cx cx, .attr .cy cy, .attr .rx rx, .attr .ry ry] ++ more) []

/-- `line`, by its two ends. -/
def line (x1 y1 x2 y2 : Length) (more : List (SvgAttr .line) := []) : SvgNode :=
  .element .line ([.attr .x1 x1, .attr .y1 y1, .attr .x2 x2, .attr .y2 y2] ++ more) []

/-- `path`, by its path data. -/
def path (d : Path) (more : List (SvgAttr .path) := []) : SvgNode :=
  .element .path (.attr .d (.path d) :: more) []

/-- `polyline`, by its points. -/
def polyline (points : Points) (more : List (SvgAttr .polyline) := []) : SvgNode :=
  .element .polyline (.attr .points points :: more) []

/-- `polygon`, by its points. -/
def polygon (points : Points) (more : List (SvgAttr .polygon) := []) : SvgNode :=
  .element .polygon (.attr .points points :: more) []

/-- `text` at a place, with its character data. -/
def text (x y : Length) (content : String) (more : List (SvgAttr .text) := []) : SvgNode :=
  .element .text ([.attr .x (LengthList.single x), .attr .y (LengthList.single y)] ++ more)
    [.text content]

/-- `image`, by its corner, its size and the address of its resource. -/
def image (x y : Length) (width height : AutoExtent) (href : String)
    (more : List (SvgAttr .image) := []) : SvgNode :=
  .element .image
    ([.attr .x x, .attr .y y, .attr .width width, .attr .height height, .attr .href href] ++ more)
    []

/-- A clip path and the group it clips: the identifier is written once here, in the `id` of
the one and the `clip-path` of the other. -/
def clipped (id : String) (clip children : List SvgNode) : List SvgNode :=
  [clipPath id clip, g [.clipPath id] children]

/-! ## The frame of a picture -/

/-- The outer `svg` of a picture: its size in pixels, the number of user units to a pixel, and
the margins inside it, in pixels. -/
structure Frame where
  /-- The width of the viewport, in pixels. -/
  width : Nat
  /-- The height of the viewport, in pixels. -/
  height : Nat
  /-- User units to a pixel. -/
  ratio : Nat := 1
  /-- The margin above the inner group, in pixels. -/
  top : Nat := 0
  /-- The margin to its right. -/
  right : Nat := 0
  /-- The margin below it. -/
  bottom : Nat := 0
  /-- The margin to its left. -/
  left : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Frame

/-- The width of the view box, in user units. -/
def userWidth (f : Frame) : Nat := f.ratio * f.width

/-- The height of the view box, in user units. -/
def userHeight (f : Frame) : Nat := f.ratio * f.height

/-- The view box: from the origin, the size in user units. -/
def viewBox (f : Frame) : ViewBox := .ofSize f.userWidth f.userHeight

/-- The width inside the margins, in user units. -/
def innerWidth (f : Frame) : Nat := f.ratio * (f.width - f.left - f.right)

/-- The height inside the margins, in user units. -/
def innerHeight (f : Frame) : Nat := f.ratio * (f.height - f.top - f.bottom)

/-- The three attributes of the frame: `width`, `height` and `viewBox`. -/
def attrs (f : Frame) : List (SvgAttr .svg) :=
  [.attr .width (.user (.ofNat f.width)), .attr .height (.user (.ofNat f.height)),
    .attr .viewBox f.viewBox]

/-- The `svg` of a frame: the namespace, the caller's attributes, then the frame's own. -/
def svg (f : Frame) (more : List (SvgAttr .svg)) (children : List SvgNode) : SvgNode :=
  Svg.svg (more ++ f.attrs) children

/-- The group inside the margins: its origin is the corner where the left and the top margin
end. -/
def inner (f : Frame) (children : List SvgNode) : SvgNode :=
  Svg.g
    [.attr .transform
      [.translate (.ofInt (Int.ofNat (f.ratio * f.left)))
        (some (.ofInt (Int.ofNat (f.ratio * f.top))))]]
    children

end Frame

end Svg

/-! ## Laws -/

namespace Svg

/-- The view box of a frame has the aspect ratio of its viewport: the default
`preserveAspectRatio` scales it by one factor and leaves no band. -/
theorem Frame.aspect (f : Frame) : f.userWidth * f.height = f.userHeight * f.width := by
  rw [Frame.userWidth, Frame.userHeight, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm f.width]

/-- The margins and the inner width make the width, when the margins fit. -/
theorem Frame.inner_add_margins (f : Frame) (h : f.left + f.right ≤ f.width) :
    f.ratio * f.left + f.innerWidth + f.ratio * f.right = f.userWidth := by
  rw [Frame.innerWidth, Frame.userWidth, ← Nat.mul_add, ← Nat.mul_add]
  congr 1
  omega

/-- The margins and the inner height make the height, when the margins fit. -/
theorem Frame.inner_add_margins_height (f : Frame) (h : f.top + f.bottom ≤ f.height) :
    f.ratio * f.top + f.innerHeight + f.ratio * f.bottom = f.userHeight := by
  rw [Frame.innerHeight, Frame.userHeight, ← Nat.mul_add, ← Nat.mul_add]
  congr 1
  omega

/-- The structure of a frame's `svg`: it stands where `svg` is admitted, its attributes are
taken, and its children pass below it. -/
theorem Frame.okIn_svg (ctx : Ctx) (f : Frame) (more : List (SvgAttr .svg))
    (children : List SvgNode) :
    (f.svg more children).okIn ctx =
      (ctx.admits .svg && SvgAttr.allOk (.xmlns :: (more ++ f.attrs)) &&
        SvgNode.okAllAt (Pos.belowSvg ctx) children) :=
  SvgNode.okIn_svg ctx _ children

/-- A frame passes where `svg` is admitted when its attributes are taken and its children
pass. For further attributes that are written out, the second premise is one evaluation:
`by conv => lhs; whnf`. -/
theorem Frame.okIn_of {ctx : Ctx} (hctx : ctx.admits .svg = true) (f : Frame)
    {more : List (SvgAttr .svg)} (hm : SvgAttr.allOk (.xmlns :: (more ++ f.attrs)) = true)
    {children : List SvgNode} (h : SvgNode.okAllAt (Pos.belowSvg ctx) children = true) :
    (f.svg more children).okIn ctx = true := by
  rw [Frame.okIn_svg, hctx, hm, h]
  rfl

/-- A frame with no further attribute passes when its children do. -/
theorem Frame.okIn_svg_nil (ctx : Ctx) (hctx : ctx.admits .svg = true) (f : Frame)
    (children : List SvgNode) (h : SvgNode.okAllAt (Pos.belowSvg ctx) children = true) :
    (f.svg [] children).okIn ctx = true := by
  rw [Frame.okIn_svg, hctx, h]
  conv => lhs; whnf

/-- The inner group of a frame passes among the marks when its children do. -/
theorem Frame.okAt_inner (x : Exclusions) (f : Frame) (children : List SvgNode)
    (h : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    (f.inner children).okAt (Pos.inSvg x) = true := by
  rw [Frame.inner, Svg.g, SvgNode.okAt_inSvg_g, h]
  conv => lhs; whnf

/-- A group passes among the marks when its attributes are taken and its children pass. -/
theorem okAt_g (x : Exclusions) (more : List (SvgAttr .g)) (children : List SvgNode) :
    (Svg.g more children).okAt (Pos.inSvg x) =
      (SvgAttr.allOk more && SvgNode.okAllAt (Pos.inSvg x) children) :=
  SvgNode.okAt_inSvg_g x more children

end Svg

end Whatwg.Html
