import Whatwg.Svg

/-!
# WhatwgTest.Svg.Schema

Finite evaluations and controls over the generated SVG schema (slices S2 and S3a of
`docs/SVG-PACKAGE-PLAN.md`). The generator is `WhatwgGates/SvgDefinitionsEmit.lean`, and
`lake exe whatwg_svgdefinitions` checks its outputs for drift. This battery checks the
generated tables against each other, from inside Lean:

- the censuses hold the counts the gate prints, and each spelling is injective on its census;
- each kind of content model has the elements the definitions give it;
- the four read sentences arrive as their readings;
- a dangling name is in no set.

Since slice S3a each set is a mask, and `Mask.toList` reads one back. The round trip of each
name table and the resolution of each set are theorems of
`Whatwg/Svg/Schema/Universe.lean`, so no line here evaluates them again. The judgments of one
node are in `WhatwgTest/Svg/Context.lean`.

What this battery does not claim: that the schema is the content model of SVG 2. The schema
says what the definitions files say.
-/
namespace WhatwgTest.Svg.Schema

open Whatwg.Svg.Schema
open Whatwg.Svg.Data

-- The censuses: the counts that `lake exe whatwg_svgdefinitions` prints.
#guard Tag.all.length == 63
#guard Category.all.length == 17
#guard Attr.all.length == 321
#guard AttrCategory.all.length == 16

-- Each spelling is injective on its census, so no census lists a constructor twice.
#guard (Tag.all.map Tag.chars).eraseDups.length == 63
#guard (Category.all.map Category.name).eraseDups.length == 17
#guard (Attr.all.map Attr.chars).eraseDups.length == 321
#guard (AttrCategory.all.map AttrCategory.name).eraseDups.length == 16

-- Controls: a name is compared exactly, and an HTML element is no SVG element.
#guard Tag.ofChars? "clippath".toList == none
#guard Tag.ofChars? "div".toList == none
#guard Attr.ofChars? "viewbox".toList == none
#guard Attr.ofChars? "xml:space".toList == some .xml_space

-- Control: `read` keeps a guess only if it spells the input. A table whose guess is wrong
-- everywhere reads nothing, and a table whose guess is right reads its own spelling.
#guard (NameTable.mk Tag.chars fun _ => some Tag.svg).read "rect".toList == none
#guard (NameTable.mk Tag.chars fun _ => some Tag.svg).read "svg".toList == some .svg
#guard !(NameTable.mk Tag.chars fun _ => some Tag.svg).covers

-- A mask reads back in the census's order, and a bit above the census names no value.
#guard (Mask.ofList [Tag.svg, .a, .rect]).toList == [.a, .rect, .svg]
#guard (⟨2 ^ 63⟩ : Mask Tag).toList == []
#guard (Mask.ofList Tag.all : Mask Tag) == ⟨2 ^ 63 - 1⟩

-- The kinds: 4 elements take any content, 2 take text, 3 take text and elements.
#guard (Tag.all.filter fun tag => tag.model.kind == .any) == [.desc, .foreignObject, .metadata, .title]
#guard (Tag.all.filter fun tag => tag.model.kind == .text) == [.script, .style]
#guard (Tag.all.filter fun tag => tag.model.kind == .textOrAnyOf) == [.text, .textPath, .tspan]
#guard (Tag.all.filter fun tag => tag.model.kind == .anyOf).length == 54

-- A kind that names no element states none: the two text kinds and the four `any` kinds.
#guard Tag.all.all fun tag =>
  tag.model.kind == .anyOf || tag.model.kind == .textOrAnyOf ||
    (tag.model.categories == ⟨0⟩ && tag.model.elements == ⟨0⟩)

-- The four sentences arrive as their readings (`Whatwg.Svg.Schema.Readings`).
#guard Tag.all.filter Tag.modelIsRead == [.a, .feDiffuseLighting, .feSpecularLighting, .animateMotion]
#guard Tag.a.model.inherits && Tag.a.model.excluded.toList == [.a] && handsOn.toList == [.switch]
#guard Tag.a.model.tags.toList == [.desc, .metadata, .title] && !Tag.a.model.text
#guard Tag.feDiffuseLighting.model.bounds.map (fun b => (b.tags.toList, b.atLeast, b.atMost)) ==
  [([.feDistantLight, .fePointLight, .feSpotLight], 1, 1)]
#guard Tag.feSpecularLighting.model.bounds == Tag.feDiffuseLighting.model.bounds
#guard Tag.animateMotion.model.bounds.map (fun b => (b.tags.toList, b.atLeast, b.atMost)) ==
  [([.mpath], 0, 1)]

-- Control: only a read sentence sets `inherits`, `excluded` and `bounds`.
#guard Tag.all.all fun tag =>
  tag.modelIsRead ||
    (!tag.model.inherits && tag.model.excluded == ⟨0⟩ && tag.model.bounds.isEmpty)

-- Each entry's digest is a SHA-256 in hexadecimal, and no two entries share one.
#guard Tag.all.all fun tag => tag.digest.length == 64
#guard (Tag.all.map Tag.digest).eraseDups.length == 63

-- The consumer's picture: each element it writes is in the model of the element that holds it
-- (`tools/Tools/View/Output.lean` of lean4-effect4, read at `707b9a01`).
#guard [Tag.g, .rect, .path, .text, .clipPath, .defs, .style, .title, .desc].all Tag.svg.model.tags.mem
#guard [Tag.g, .rect, .path, .text, .clipPath].all Tag.g.model.tags.mem
#guard Tag.clipPath.model.tags.mem .rect
#guard Tag.text.model.kind == .textOrAnyOf

-- Controls: a dangling name is in no set (ruling SV-3; `generated/svg-dangling.tsv`).
#guard Attr.ofChars? "externalResourcesRequired".toList == none
#guard Attr.ofChars? "kerning".toList == none
#guard !(AttrCategory.all.map AttrCategory.name).contains "style"
#guard !(AttrCategory.all.map AttrCategory.name).contains "document element event"

-- Two entries declare the category `presentation`; the schema has one, with both lists.
#guard (AttrCategory.all.filter fun c => c.name == "presentation").length == 1
#guard AttrCategory.presentation.members.mem .transform
#guard AttrCategory.presentation.members.mem .color_interpolation_filters

end WhatwgTest.Svg.Schema