import Whatwg.Svg.Geometry.Box

/-!
# Whatwg.Svg.Geometry.Outline

Owner: the closed outlines that a picture is made of, as lists of cubic segments (slice S11
of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-55): a box, a box with round corners, a frame, an
ellipse. SVG has an element for a rectangle and one for an ellipse; a program asks for the
outline instead when it must compute with it: to cut a hole into a shape, to draw part of it,
to move a mark along it, or to draw it by hand with a line of varying width.

Each outline of a box whose `x0` is no more than its `x1` and whose `y0` no more than its
`y1` runs clockwise as a screen shows it, where `y` grows downwards, and each is a chain that
ends where it starts (`Cubic.Closed`). A normal of `Whatwg/Svg/Geometry/Root.lean` points to
the right of the direction of travel, so into such an outline. A quarter of a circle is one
cubic (`Cubic.corner`), which is within three parts in ten thousand of the circle at the
default `kappa`; a caller that wants another roundness passes its own.

The laws of `Whatwg/Svg/Geometry/Outline/Laws.lean` say that each outline is closed, that it
stays in its box, and that the outline of a moved box is the outline, moved.

What this module does not claim: an exact circle, which no cubic is; the outline of an
elliptical arc of the path chapter.
-/

namespace Whatwg.Svg.Value

namespace Cubic

/-- The four sides of a box, from its least corner: across, down, back and up. -/
def rect (b : Box) : List Cubic :=
  [line ⟨b.x0, b.y0⟩ ⟨b.x1, b.y0⟩, line ⟨b.x1, b.y0⟩ ⟨b.x1, b.y1⟩, line ⟨b.x1, b.y1⟩ ⟨b.x0, b.y1⟩,
    line ⟨b.x0, b.y1⟩ ⟨b.x0, b.y0⟩]

/-- The radius of a corner that fits a box: no less than zero, and no more than half the
shorter side. -/
def fitRadius (b : Box) (r : Rat) : Rat := max 0 (min r (min (b.width / 2) (b.height / 2)))

/-- **A box with round corners**: four sides and four quarter turns of radius `r`. It starts
on the side of least `y`, where the corner of least `x` and `y` ends, and that corner is its
last segment. The radius is fitted to the box (`fitRadius`). -/
def roundRect (b : Box) (r : Rat) (k : Rat := kappa) : List Cubic :=
  [line ⟨b.x0 + fitRadius b r, b.y0⟩ ⟨b.x1 - fitRadius b r, b.y0⟩,
    corner ⟨b.x1 - fitRadius b r, b.y0⟩ ⟨b.x1, b.y0⟩ ⟨b.x1, b.y0 + fitRadius b r⟩ k,
    line ⟨b.x1, b.y0 + fitRadius b r⟩ ⟨b.x1, b.y1 - fitRadius b r⟩,
    corner ⟨b.x1, b.y1 - fitRadius b r⟩ ⟨b.x1, b.y1⟩ ⟨b.x1 - fitRadius b r, b.y1⟩ k,
    line ⟨b.x1 - fitRadius b r, b.y1⟩ ⟨b.x0 + fitRadius b r, b.y1⟩,
    corner ⟨b.x0 + fitRadius b r, b.y1⟩ ⟨b.x0, b.y1⟩ ⟨b.x0, b.y1 - fitRadius b r⟩ k,
    line ⟨b.x0, b.y1 - fitRadius b r⟩ ⟨b.x0, b.y0 + fitRadius b r⟩,
    corner ⟨b.x0, b.y0 + fitRadius b r⟩ ⟨b.x0, b.y0⟩ ⟨b.x0 + fitRadius b r, b.y0⟩ k]

/-- **A frame with round corners**: the box, and the box `thickness` inside it. Filled by the
even-odd rule it is a frame that thick. A thickness of half the shorter side or more leaves no
hole, and the frame is the box alone; a thickness below zero is zero. -/
def ring (b : Box) (r thickness : Rat) (k : Rat := kappa) : List (List Cubic) :=
  if min b.width b.height ≤ 2 * max 0 thickness then [roundRect b r k]
  else [roundRect b r k, roundRect (b.pad (-(max 0 thickness))) (r - max 0 thickness) k]

/-- **An ellipse**, nearly: four quarter turns about a centre, from its point of greatest
`x`. -/
def ellipse (center : Vec) (rx ry : Rat) (k : Rat := kappa) : List Cubic :=
  [corner ⟨center.x + rx, center.y⟩ ⟨center.x + rx, center.y + ry⟩ ⟨center.x, center.y + ry⟩ k,
    corner ⟨center.x, center.y + ry⟩ ⟨center.x - rx, center.y + ry⟩ ⟨center.x - rx, center.y⟩ k,
    corner ⟨center.x - rx, center.y⟩ ⟨center.x - rx, center.y - ry⟩ ⟨center.x, center.y - ry⟩ k,
    corner ⟨center.x, center.y - ry⟩ ⟨center.x + rx, center.y - ry⟩ ⟨center.x + rx, center.y⟩ k]

/-- A circle, nearly. -/
def circle (center : Vec) (r : Rat) (k : Rat := kappa) : List Cubic := ellipse center r r k

end Cubic

end Whatwg.Svg.Value
