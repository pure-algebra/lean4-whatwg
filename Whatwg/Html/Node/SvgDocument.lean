import Whatwg.Html.Content.Document.Laws
import Whatwg.Html.Node.SvgBuild

/-!
# Whatwg.Html.Node.SvgDocument

Owner: the seam between the check across a document (`Whatwg/Html/Content/Document.lean`) and
the typed SVG tree (`Whatwg/Html/Node/Svg.lean`). The check reads a raw tree: names and texts.
A picture is built typed, and `SvgNode.toRaw` writes it. This module says what the check reads
from what a typed tree writes, so that a law about the identifiers of a picture is proved on
the typed tree and holds of the page:

- `SvgAttr.identOf?_toPair`: the check reads an identifier from a typed attribute exactly when
  its key is `id`, and reads its text. `identOf?_ident` and `linksOf_clipPath` are the two
  helpers of `Whatwg/Html/Node/SvgPaint.lean` that write an identifier and a reference.
- `SvgNode.namesAt_toRaw_element` and `linksAt_toRaw_element`: the identifiers and the
  references of a typed element that stands in SVG are those of its attributes, as written,
  then those of its children. `namesAt_toRaw_svg` and `linksAt_toRaw_svg` are the same for the
  outer `svg`, which stands in HTML.
- `Svg.namesAllAt_clipped` and `Svg.linksAllAt_clipped`: a clipped group defines its identifier
  once and refers to it once, around what its two lists define and refer to.
  `Svg.closedAll_clipped` is the consequence: a clipped group is closed when its identifier is
  fresh and what it holds is closed.

What this module does not claim: the references of every typed attribute by its key. A builder
that writes `fill`, `mask`, `filter`, a marker or `href` reads them with
`Document.urlTarget?_url` and `Document.fragmentOf?_hash`, as `linksOf_clipPath` does here.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Html.Content (Ns integrationBase)
open Whatwg.Html.Content.Document

namespace SvgAttr

variable {t : Tag}

/-- The check reads an identifier from a typed attribute exactly when its key is `id`. -/
theorem identOf?_toPair (p : SvgAttr t) :
    identOf? p.toPair = if p.key = .attr .id then some p.toPair.2 else none := by
  have hname : (Key.attr .id).name = "id" := by decide +kernel
  rw [identOf?, toPair_fst]
  split
  · next h =>
    rw [if_pos (Key.name_injective ((eq_of_beq h).trans hname.symm))]
  · next h =>
    have hkey : p.key ≠ .attr .id := fun hkey => h (by rw [hkey, hname]; exact beq_self_eq_true _)
    rw [if_neg hkey]

/-- `SvgAttr.ident` gives its element that identifier. -/
theorem identOf?_ident (id : String) : identOf? (SvgAttr.ident (t := t) id).toPair = some id := by
  rw [identOf?_toPair, if_pos (show (SvgAttr.ident (t := t) id).key = Key.attr .id from rfl)]
  rfl

/-- `SvgAttr.clipPath` gives its element no identifier. -/
theorem identOf?_clipPath (id : String) :
    identOf? (SvgAttr.clipPath (t := t) id).toPair = none := by
  rw [identOf?_toPair, if_neg (by exact nofun)]

/-- `SvgAttr.ident` makes no reference. -/
theorem linksOf_ident (element id : String) :
    linksOf .svg element (SvgAttr.ident (t := t) id).toPair = [] := by
  have hname : Whatwg.Svg.Schema.Attr.id.name = "id" := by decide +kernel
  show svgLinks element (Whatwg.Svg.Schema.Attr.id.name, id) = []
  rw [hname]
  rfl

/-- `SvgAttr.clipPath` refers to its identifier, as `url(#id)`. -/
theorem linksOf_clipPath (element id : String) :
    linksOf .svg element (SvgAttr.clipPath (t := t) id).toPair =
      [⟨element, "clip-path", .svgUrl, id⟩] := by
  have hname : Whatwg.Svg.Schema.Attr.clip_path.name = "clip-path" := by decide +kernel
  show svgLinks element (Whatwg.Svg.Schema.Attr.clip_path.name, urlRef id) = _
  rw [hname]
  show ((urlTarget? (urlRef id)).toList.map fun target =>
    (⟨element, "clip-path", .svgUrl, target⟩ : Ref)) = _
  rw [urlRef, urlTarget?_url]
  rfl

end SvgAttr

namespace SvgNode

/-- **The identifiers of a typed element that stands in SVG** are those its attributes write,
then those of its children. -/
theorem namesAt_toRaw_element (t : Tag) (attrs : List (SvgAttr t)) (children : List SvgNode) :
    namesAt .svg (SvgNode.element t attrs children).toRaw =
      (attrs.map SvgAttr.toPair).filterMap identOf? ++
        namesAllAt (Ns.svg.step t.name) (toRawAll children) := by
  rw [toRaw, namesAt_element]
  rfl

/-- **The references of a typed element that stands in SVG** are those its attributes write,
then those of its children. -/
theorem linksAt_toRaw_element (t : Tag) (attrs : List (SvgAttr t)) (children : List SvgNode) :
    linksAt .svg (SvgNode.element t attrs children).toRaw =
      (attrs.map SvgAttr.toPair).flatMap (linksOf .svg t.name) ++
        linksAllAt (Ns.svg.step t.name) (toRawAll children) := by
  rw [toRaw, linksAt_element]
  rfl

/-- The outer `svg` is an SVG element, and its children stand in SVG. -/
theorem ofElement_svg_name : Ns.html.ofElement Tag.svg.name = .svg := by decide +kernel

theorem step_svg_name : Ns.html.step Tag.svg.name = .svg := by decide +kernel

/-- The identifiers of a picture: those its `svg` writes, then those of its marks. -/
theorem namesAt_toRaw_svg (attrs : List (SvgAttr .svg)) (children : List SvgNode) :
    namesAt .html (SvgNode.element .svg attrs children).toRaw =
      (attrs.map SvgAttr.toPair).filterMap identOf? ++ namesAllAt .svg (toRawAll children) := by
  rw [toRaw, namesAt_element, ofElement_svg_name, step_svg_name]
  rfl

/-- The references of a picture: those its `svg` writes, then those of its marks. -/
theorem linksAt_toRaw_svg (attrs : List (SvgAttr .svg)) (children : List SvgNode) :
    linksAt .html (SvgNode.element .svg attrs children).toRaw =
      (attrs.map SvgAttr.toPair).flatMap (linksOf .svg Tag.svg.name) ++
        linksAllAt .svg (toRawAll children) := by
  rw [toRaw, linksAt_element, ofElement_svg_name, step_svg_name]
  rfl

/-- **A picture whose `svg` writes no identifier and no reference is closed when its marks
are**, taken together. -/
theorem closed_svg {attrs : List (SvgAttr .svg)} {children : List SvgNode}
    (hids : (attrs.map SvgAttr.toPair).filterMap identOf? = [])
    (hlinks : (attrs.map SvgAttr.toPair).flatMap (linksOf .svg Tag.svg.name) = [])
    (hmarks : ClosedAll .svg (toRawAll children)) :
    Closed .html (SvgNode.element .svg attrs children).toRaw := by
  rw [Closed, namesAt_toRaw_svg, linksAt_toRaw_svg, hids, hlinks, List.nil_append,
    List.nil_append]
  exact hmarks

/-- Such a picture defines what its marks define. -/
theorem namesAt_toRaw_svg_of {attrs : List (SvgAttr .svg)} {children : List SvgNode}
    (hids : (attrs.map SvgAttr.toPair).filterMap identOf? = []) :
    namesAt .html (SvgNode.element .svg attrs children).toRaw =
      namesAllAt .svg (toRawAll children) := by
  rw [namesAt_toRaw_svg, hids, List.nil_append]

/-- The children of an element that is no integration point stand in SVG. -/
theorem step_name_of_plain {t : Tag} (h : integrationBase t = none) : Ns.svg.step t.name = .svg := by
  have hname := Content.isIntegrationName_of_tag (ofChars?_name t)
  rw [h, Option.isSome_none] at hname
  rw [Ns.step, hname, if_neg Bool.false_ne_true]

end SvgNode

namespace Svg

open SvgNode (toRawAll)

/-- **A clipped group defines its identifier once**, before what its clip and its marks
define. -/
theorem namesAllAt_clipped (id : String) (clip children : List SvgNode) :
    namesAllAt .svg (toRawAll (clipped id clip children)) =
      id :: (namesAllAt .svg (toRawAll clip) ++ namesAllAt .svg (toRawAll children)) := by
  rw [clipped, toRawAll, toRawAll, toRawAll, namesAllAt_cons, namesAllAt_cons, clipPath, g,
    SvgNode.namesAt_toRaw_element, SvgNode.namesAt_toRaw_element,
    SvgNode.step_name_of_plain (t := .clipPath) rfl, SvgNode.step_name_of_plain (t := .g) rfl,
    List.map_cons, List.map_nil, List.filterMap_cons_some (SvgAttr.identOf?_ident id),
    List.map_cons, List.map_nil, List.filterMap_cons_none (SvgAttr.identOf?_clipPath id)]
  show id :: (namesAllAt .svg (toRawAll clip) ++ (namesAllAt .svg (toRawAll children) ++ [])) = _
  rw [List.append_nil]

/-- **A clipped group refers to its identifier once**, between what its clip and its marks
refer to. -/
theorem linksAllAt_clipped (id : String) (clip children : List SvgNode) :
    linksAllAt .svg (toRawAll (clipped id clip children)) =
      linksAllAt .svg (toRawAll clip) ++
        ⟨Tag.g.name, "clip-path", .svgUrl, id⟩ :: linksAllAt .svg (toRawAll children) := by
  rw [clipped, toRawAll, toRawAll, toRawAll, linksAllAt_cons, linksAllAt_cons, clipPath, g,
    SvgNode.linksAt_toRaw_element, SvgNode.linksAt_toRaw_element,
    SvgNode.step_name_of_plain (t := .clipPath) rfl, SvgNode.step_name_of_plain (t := .g) rfl,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, SvgAttr.linksOf_ident,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, SvgAttr.linksOf_clipPath]
  show linksAllAt .svg (toRawAll clip) ++
    (⟨Tag.g.name, "clip-path", .svgUrl, id⟩ :: (linksAllAt .svg (toRawAll children) ++ [])) = _
  rw [List.append_nil]

/-- **A clipped group is closed when its identifier is fresh and what it holds is closed**: the
clip and the marks, taken together. The group's own reference names the identifier it
defines. -/
theorem closedAll_clipped {id : String} {clip children : List SvgNode}
    (hfresh : id ∉ namesAllAt .svg (toRawAll clip) ++ namesAllAt .svg (toRawAll children))
    (hheld : ClosedAll .svg (toRawAll clip ++ toRawAll children)) :
    ClosedAll .svg (toRawAll (clipped id clip children)) := by
  rw [ClosedAll, namesAllAt_append, linksAllAt_append] at hheld
  rw [ClosedAll, namesAllAt_clipped, linksAllAt_clipped]
  refine ⟨List.nodup_cons.mpr ⟨hfresh, hheld.1⟩, fun r hr => ?_⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact (hheld.2 r (List.mem_append_left _ hr)).mono fun x hx => List.mem_cons_of_mem _ hx
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl List.mem_cons_self
    · exact (hheld.2 r (List.mem_append_right _ hr)).mono fun x hx => List.mem_cons_of_mem _ hx

end Svg

end Whatwg.Html
