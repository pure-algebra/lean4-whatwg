/-!
# Whatwg.Html.Svg

Owner: the seam, the rules by which an HTML tree holds SVG content. The HTML Standard owns
them: where `svg` stands, where the namespace changes, and how a foreign element is written.
SVG 2 owns the elements themselves, and they are the library `Whatwg.Svg`, beside this one
(ruling HP-9 of `docs/HTML-PACKAGE-PLAN.md`; `docs/SVG-PACKAGE-PLAN.md`).

Anchors in the pinned `source`: the section "SVG" of the embedded content chapter, the
definition of an HTML integration point, and the fragment serialization algorithm.

This module declares nothing yet. Slice S3 of `docs/SVG-PACKAGE-PLAN.md` opens it. Until then
`Whatwg.Html.Content.validIn` refuses `svg`, as it refuses every name that is not an HTML
element.
-/
