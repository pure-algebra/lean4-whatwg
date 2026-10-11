import Whatwg.Svg

/-!
# WhatwgTest.Svg.Context

Finite evaluations and controls of the SVG position and of one node's judgments (slice S3a of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Content/Context.lean`. Each line walks a path from
outside an `svg`, or judges one attribute or one list of children.

The lines on `a` are controls of the seat's two readings of its sentence: `a` reads the outer
model through a `switch`, and it removes `a` from its own model without excluding a descendant.

What this battery does not claim: that a tree is valid. The walk and the seam are slice S3b.
A line here applies the transition and one judgment, and reads no tree.
-/

namespace WhatwgTest.Svg.Context

open Whatwg.Svg.Schema
open Whatwg.Svg.Content

/-- The position below a path of elements, from outside an outermost `svg`. -/
def below (path : List Tag) : Ctx := path.foldl Ctx.child Ctx.outside

-- An `svg` takes shapes, groups and descriptions, and no character data.
#guard [Tag.g, .rect, .path, .text, .clipPath, .defs, .style, .title, .desc, .svg].all (below [.svg]).admits
#guard !(below [.svg]).admitsText

-- Controls: outside an `svg` nothing stands, and a filter primitive is no child of `svg`.
#guard !Ctx.outside.admits .svg && !Ctx.outside.admitsText
#guard !(below [.svg]).admits .feBlend

-- Text content: `text` takes character data and `tspan`; `style` takes character data alone.
#guard (below [.svg, .text]).admitsText && (below [.svg, .text]).admits .tspan
#guard (below [.svg, .style]).admitsText && Tag.all.all fun t => !(below [.svg, .style]).admits t

-- `a` is transparent: below `svg` it takes what `svg` takes, and its own descriptive content.
#guard [Tag.rect, .g, .text, .title, .desc, .metadata].all (below [.svg, .a]).admits
#guard !(below [.svg, .a]).admitsText

-- `a` inherits the text bit too: inside `text` it takes character data.
#guard (below [.svg, .text, .a]).admitsText && (below [.svg, .text, .a]).admits .tspan

-- Control: `a` removes `a` from its own model.
#guard !(below [.svg, .a]).admits .a

-- The removal is no descendant exclusion: a `g` inside the `a` takes an `a` again.
#guard (below [.svg, .a, .g]).admits .a

-- Through a `switch`, `a` reads the model of the nearest ancestor that is no `switch`.
#guard (below [.svg, .switch]).admits .a
#guard [Tag.defs, .style, .clipPath].all fun t =>
  !(below [.svg, .switch]).admits t && (below [.svg, .switch, .a]).admits t
#guard (below [.svg, .switch, .switch, .a]).model == (below [.svg, .a]).model

-- Control: through a `switch` inside an `a`, the nearest such ancestor is that `a`.
#guard !(below [.svg, .a, .switch, .a]).admits .a
#guard (below [.svg, .a, .switch, .a]).model == (below [.svg, .a]).model

-- The counts: exactly one light source, and at most one `mpath`, in any order.
#guard boundsOk .feDiffuseLighting [.title, .fePointLight, .script]
#guard !boundsOk .feDiffuseLighting [.title]
#guard !boundsOk .feSpecularLighting [.fePointLight, .feSpotLight]
#guard boundsOk .animateMotion [] && boundsOk .animateMotion [.mpath]
#guard !boundsOk .animateMotion [.mpath, .desc, .mpath]

-- Control: an element whose model states no count takes any number of each child.
#guard boundsOk .g (List.replicate 40 .rect)

-- The consumer's picture: each attribute it writes is an attribute of its element
-- (`tools/Tools/View/Output.lean` of lean4-effect4, read at `707b9a01`).
#guard ["class", "width", "height", "viewBox", "data-look", "role", "aria-label"].all
  fun name => attrOk .svg name.toList
#guard ["class", "x", "y", "width", "height", "fill", "fill-opacity", "pointer-events", "data-key"].all
  fun name => attrOk .rect name.toList
#guard ["class", "d", "fill", "stroke", "stroke-width", "fill-rule", "fill-opacity"].all
  fun name => attrOk .path name.toList
#guard ["class", "x", "y", "font-family", "font-style", "font-weight", "font-size", "fill",
    "transform", "xml:space"].all fun name => attrOk .text name.toList
#guard attrOk .clipPath "id".toList && attrOk .g "clip-path".toList && attrOk .title "id".toList

-- Controls: a custom data attribute needs a character after `data-`, and no upper-case letter.
#guard !attrOk .rect "data-".toList && !attrOk .rect "data-Key".toList && !attrOk .rect "data".toList

-- Control: `xmlns` is in no definitions file. The seam admits it at slice S3b (ruling SV-12).
#guard !attrOk .svg "xmlns".toList

-- Controls: an attribute belongs to the elements that the definitions give it to.
#guard !attrOk .rect "d".toList && !attrOk .clipPath "role".toList
#guard attrOk .svg "playbackorder".toList && !attrOk .g "playbackorder".toList
#guard !attrOk .rect "viewbox".toList && !attrOk .clipPath "externalResourcesRequired".toList

-- An attribute that an entry of its own lists for an element is that element's, though the
-- element's entry does not cite it: `href` on the four animation elements.
#guard [Tag.animate, .animateMotion, .animateTransform, .set].all fun tag => attrOk tag "href".toList

end WhatwgTest.Svg.Context
