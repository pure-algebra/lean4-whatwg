import Whatwg.Svg

/-!
# WhatwgTest.Svg.Schema

Finite evaluations and controls over the generated SVG schema (slice S2 of
`docs/SVG-PACKAGE-PLAN.md`). The generator is `WhatwgGates/SvgDefinitionsEmit.lean`, and
`lake exe whatwg_svgdefinitions` checks its outputs for drift. This battery checks the
generated tables against each other, from inside Lean:

- the censuses hold the counts the gate prints, and each name table is injective on its census;
- each name lookup inverts its name table over the whole census;
- each content model's children are recomputed here from its categories and its elements;
- every element and attribute that the consumer's picture writes is in the schema where the
  picture writes it (`tools/Tools/View/Output.lean` of lean4-effect4, read at `707b9a01`).

What this battery does not claim: that the schema is the content model of SVG 2. The schema
says what the definitions files say. It states no law: the round trips are evaluated over the
census here, and slice S3 proves them where the checker consumes them.
-/

namespace WhatwgTest.Svg.Schema

open Whatwg.Svg.Schema

-- The censuses: the counts that `lake exe whatwg_svgdefinitions` prints.
#guard Tag.all.length == 63
#guard Category.all.length == 17
#guard Attr.all.length == 321
#guard AttrCategory.all.length == 16

-- Each name table is injective on its census, so no census lists a constructor twice.
#guard (Tag.all.map Tag.name).eraseDups.length == 63
#guard (Category.all.map Category.name).eraseDups.length == 17
#guard (Attr.all.map Attr.name).eraseDups.length == 321
#guard (AttrCategory.all.map AttrCategory.name).eraseDups.length == 16

-- Each lookup inverts its name table, over the whole census.
#guard Tag.all.all fun tag => Tag.ofChars? tag.name.toList == some tag
#guard Attr.all.all fun attr => Attr.ofChars? attr.name.toList == some attr

-- Controls: a name is compared exactly, and an HTML element is no SVG element.
#guard Tag.ofChars? "clippath".toList == none
#guard Tag.ofChars? "div".toList == none
#guard Attr.ofChars? "viewbox".toList == none
#guard Attr.ofChars? "xml:space".toList == some .xml_space

-- The kinds: 4 elements take any content, 2 take text, 3 take text and elements.
#guard (Tag.all.filter fun tag => tag.model.kind == .any) == [.desc, .foreignObject, .metadata, .title]
#guard (Tag.all.filter fun tag => tag.model.kind == .text) == [.script, .style]
#guard (Tag.all.filter fun tag => tag.model.kind == .textOrAnyOf) == [.text, .textPath, .tspan]
#guard (Tag.all.filter fun tag => tag.model.kind == .anyOf).length == 54

-- Resolution, recomputed: a model's children are the members of its categories and its
-- elements, in the census's order.
#guard Tag.all.all fun tag =>
  let model := tag.model
  model.children == Tag.all.filter fun child =>
    model.categories.any (·.members.contains child) || model.elements.contains child

-- A model that names no child has no child: the two text kinds and the four `any` kinds.
#guard Tag.all.all fun tag =>
  tag.model.kind == .anyOf || tag.model.kind == .textOrAnyOf || tag.model.children.isEmpty

-- The four sentences arrive as their readings (`Whatwg.Svg.Schema.Readings`).
#guard Tag.all.filter Tag.modelIsRead == [.a, .feDiffuseLighting, .feSpecularLighting, .animateMotion]
#guard Tag.a.model.inherits && Tag.a.model.excluded == [.a] && Tag.a.model.through == [.switch]
#guard Tag.feDiffuseLighting.model.bounds ==
  [{ tags := [.feDistantLight, .fePointLight, .feSpotLight], atLeast := 1, atMost := 1 }]
#guard Tag.feSpecularLighting.model.bounds == Tag.feDiffuseLighting.model.bounds
#guard Tag.animateMotion.model.bounds == [{ tags := [.mpath], atLeast := 0, atMost := 1 }]

-- Control: only a read sentence sets `inherits`, `through`, `excluded` and `bounds`.
#guard Tag.all.all fun tag =>
  tag.modelIsRead ||
    (!tag.model.inherits && tag.model.through.isEmpty && tag.model.excluded.isEmpty &&
      tag.model.bounds.isEmpty)

-- Each entry's digest is a SHA-256 in hexadecimal, and no two entries share one.
#guard Tag.all.all fun tag => tag.digest.length == 64
#guard (Tag.all.map Tag.digest).eraseDups.length == 63

/-- The schema gives the element an attribute of this name: among its own attributes, or in
one of its attribute categories. Slice S3 owns the admission of an attribute; this is the
schema's part of it. -/
def hasAttr (tag : Tag) (name : String) : Bool :=
  match Attr.ofChars? name.toList with
  | some attr => tag.ownAttrs.contains attr || tag.attrCategories.any (·.members.contains attr)
  | none => false

-- The consumer's picture: each element it writes may stand where it writes it.
#guard [Tag.g, .rect, .path, .text, .clipPath, .defs, .style, .title, .desc].all
  Tag.svg.model.children.contains
#guard [Tag.g, .rect, .path, .text, .clipPath].all Tag.g.model.children.contains
#guard Tag.clipPath.model.children.contains .rect
#guard Tag.text.model.kind == .textOrAnyOf

-- The consumer's picture: each attribute it writes is an attribute of its element.
#guard ["class", "width", "height", "viewBox"].all (hasAttr .svg)
#guard ["class", "x", "y", "width", "height", "fill", "fill-opacity", "pointer-events"].all
  (hasAttr .rect)
#guard ["class", "d", "fill", "stroke", "stroke-width", "fill-rule", "fill-opacity"].all
  (hasAttr .path)
#guard ["class", "x", "y", "font-family", "font-style", "font-weight", "font-size", "fill",
    "transform", "xml:space"].all (hasAttr .text)
#guard hasAttr .clipPath "id" && hasAttr .g "clip-path"
#guard hasAttr .svg "role" && hasAttr .svg "aria-label" && hasAttr .title "id"

-- Controls: two things the picture writes are in no definitions file. The seam admits them at
-- slice S3: `xmlns` by ruling SV-12, and `data-*` by the rule of `master/struct.html`.
#guard !hasAttr .svg "xmlns"
#guard !hasAttr .rect "data-key"

-- Controls: a dangling name is in no set (ruling SV-3; `generated/svg-dangling.tsv`).
#guard !hasAttr .clipPath "externalResourcesRequired"
#guard Attr.ofChars? "kerning".toList == none
#guard !(AttrCategory.all.map AttrCategory.name).contains "style"
#guard !(AttrCategory.all.map AttrCategory.name).contains "document element event"

-- Controls: an attribute belongs to the elements that the definitions give it to.
#guard !hasAttr .rect "d"
#guard !hasAttr .clipPath "role"
#guard hasAttr .svg "playbackorder" && !hasAttr .g "playbackorder"

-- An attribute that an entry of its own lists for an element is that element's, though the
-- element's entry does not cite it: `href` on the four animation elements.
#guard [Tag.animate, .animateMotion, .animateTransform, .set].all fun tag => hasAttr tag "href"

-- Two entries declare the category `presentation`; the schema has one, with both lists.
#guard (AttrCategory.all.filter fun c => c.name == "presentation").length == 1
#guard AttrCategory.presentation.members.contains .transform
#guard AttrCategory.presentation.members.contains .color_interpolation_filters

end WhatwgTest.Svg.Schema
