import Whatwg.Html.Node.SvgBuild

/-!
# Whatwg.Html.Node.SvgFigure

Owner: a picture in a `figure`, with the caption that names it (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`; entry W4 of `docs/research/2026-10-12-whatwg-requests.md`, the HTML
side).

A picture that stands in a page as an image has a name for a reader who does not see it. This
module writes the usual form: the picture and its caption in a `figure`, where the `svg` has
`role="img"` and an `aria-labelledby` that holds the `id` of the `figcaption`.

```
Svg.figure "plan-graph" picture [E.txt "The plan's graph"]
-- <figure><svg … role="img" aria-labelledby="plan-graph">…</svg>
--   <figcaption id="plan-graph">The plan's graph</figcaption></figure>
```

- `SvgNode.namedBy id` puts the two attributes on the root of a picture. It serves a picture
  named by its own `title` child too: the identifier is then that child's.
- `Svg.figure id picture caption` is the typed element. The identifier is written once, here,
  and goes to both places.
- `Svg.figureRaw` is the same tree as a raw node, for a picture that is data: a fold puts it
  among its nodes, and the checked admission of `Whatwg/Html/Node/Check.lean` judges it with
  the rest. `Svg.figure_toRaw` says that the two are one tree.

What the premises are. A typed figure takes two facts about its picture: it is an `svg`
element (`SvgNode.isSvg`, which `rfl` proves of a picture built with `Svg.svg` or
`Svg.Frame.svg`), and with its two attributes it passes where the children of the figure stand
(`SvgNode.okIn`, one evaluation over tags and keys for a closed picture). For a picture with
free parts, `SvgNode.okIn_namedBy_of` and `Svg.Frame.okIn_namedBy` are the laws of
`Whatwg/Html/Node/SvgBuild.lean` with the two attributes, and `Ctx.admits_svg_child_figure`
says that a figure admits a picture wherever the figure stands. The caption is typed children
of a `figcaption`, so nothing is owed for it.

Where the identifier is written, for a check of a whole page: `Svg.figure_toRaw` and
`SvgNode.toRaw_namedBy` state the raw tree. The `figcaption` holds the pair `("id", id)`, and
the `svg` the pair `("aria-labelledby", id)`.

What this module does not claim. That the identifier stands once in its page, or that it is a
good identifier: one with a space would name two elements in `aria-labelledby`. Those are rules
of a whole page (entry W2). Nor that `img` is the right role for every picture: the role is an
argument, and a picture that holds links may want another.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Exclusions)
open Whatwg.Html.Content (Ctx Pos validIn validAll)

/-! ## The picture's two attributes -/

namespace SvgNode

/-- What makes a picture one thing with a name: `role`, and `aria-labelledby` with the
identifier of the element that holds the name. -/
def naming {t : Whatwg.Svg.Schema.Tag} (id : String) (role : String := "img") : List (SvgAttr t) :=
  [.attr .role role, .attr .aria_labelledby id]

/-- The picture, named by the element `id`: the two attributes after those of its root. A node
that is no element is itself. -/
def namedBy (id : String) (role : String := "img") : SvgNode → SvgNode
  | .element t attrs children => .element t (attrs ++ naming id role) children
  | node => node

/-- The node is an `svg` element: the root of a picture, which may stand in HTML content. -/
def isSvg : SvgNode → Bool
  | .element .svg _ _ => true
  | _ => false

/-- The raw tree of a named picture: its own pairs, then `role` and `aria-labelledby`. A check
of a whole page reads the identifier here. -/
theorem toRaw_namedBy (id role : String) (attrs : List (SvgAttr .svg)) (children : List SvgNode) :
    ((SvgNode.element .svg attrs children).namedBy id role).toRaw =
      .element "svg" (attrs.map SvgAttr.toPair ++ [("role", role), ("aria-labelledby", id)])
        (toRawAll children) := by
  rw [namedBy, toRaw, List.map_append]
  rfl

/-- The structure of a named picture: `okIn_svg`, with the two attributes in its list. -/
theorem okIn_namedBy (ctx : Ctx) (id role : String) (attrs : List (SvgAttr .svg))
    (children : List SvgNode) :
    ((SvgNode.element .svg attrs children).namedBy id role).okIn ctx =
      (ctx.admits .svg && SvgAttr.allOk (attrs ++ naming id role) &&
        okAllAt (Pos.belowSvg ctx) children) :=
  okIn_svg ctx _ children

/-- A named picture passes where `svg` is admitted when its attributes with the two are taken
and its children pass. For attributes that are written out, the second premise is one
evaluation: `by conv => lhs; whnf`. -/
theorem okIn_namedBy_of {ctx : Ctx} (hctx : ctx.admits .svg = true) (id role : String)
    {attrs : List (SvgAttr .svg)} (hm : SvgAttr.allOk (attrs ++ naming id role) = true)
    {children : List SvgNode} (h : okAllAt (Pos.belowSvg ctx) children = true) :
    ((SvgNode.element .svg attrs children).namedBy id role).okIn ctx = true := by
  rw [okIn_namedBy, hctx, hm, h]
  rfl

end SvgNode

/-- A frame's picture, named, passes where `svg` is admitted when its attributes are taken and
its children pass: `Svg.Frame.okIn_of` with the two attributes. -/
theorem Svg.Frame.okIn_namedBy {ctx : Ctx} (hctx : ctx.admits .svg = true) (f : Svg.Frame)
    (id role : String) {more : List (SvgAttr .svg)}
    (hm : SvgAttr.allOk (.xmlns :: (more ++ f.attrs) ++ SvgNode.naming id role) = true)
    {children : List SvgNode} (h : SvgNode.okAllAt (Pos.belowSvg ctx) children = true) :
    ((f.svg more children).namedBy id role).okIn ctx = true :=
  SvgNode.okIn_namedBy_of hctx id role hm h

/-! ## Where a figure's children stand -/

namespace Content.Ctx

/-- No exclusion that an ancestor hands down refuses `svg`. -/
theorem excluded_svg (x : Exclusions) : Ctx.excluded x .svg = false := by
  have hits : Ctx.hits .svg = [false, false, false, false, false, false, false, false, false,
      false, false, false, false, false, false] := by decide
  rw [Ctx.excluded_eq_spec, Ctx.excludedSpec, hits]
  cases x
  simp only [Exclusions.flags, List.zip_cons_cons, List.zip_nil_right, List.any_cons,
    List.any_nil, Bool.and_false, Bool.or_false]

/-- No exclusion that an ancestor hands down refuses `figcaption`, whatever its attributes. -/
theorem excludedWith_figcaption (x : Exclusions) (attrs : List (String × String)) :
    Ctx.excludedWith x .figcaption attrs = false := by
  have hits : Ctx.hitsWith .figcaption attrs = [false, false, false, false, false, false, false,
      false, false, false, false, false, false, false, false] := rfl
  rw [Ctx.excludedWith_eq_spec, Ctx.excludedWithSpec, hits]
  cases x
  simp only [Exclusions.flags, List.zip_cons_cons, List.zip_nil_right, List.any_cons,
    List.any_nil, Bool.and_false, Bool.or_false]

/-- A figure admits a picture among its children, wherever the figure stands. -/
theorem admits_svg_child_figure (ctx : Ctx) : (ctx.child .figure).admits .svg = true := by
  rw [Ctx.admits, excluded_svg]
  rfl

/-- A figure admits a `figcaption` among its children, wherever the figure stands. -/
theorem admitsWith_figcaption_child_figure (ctx : Ctx) (attrs : List (String × String)) :
    (ctx.child .figure).admitsWith .figcaption attrs = true := by
  rw [Ctx.admitsWith, excludedWith_figcaption]
  rfl

end Content.Ctx

/-! ## An attribute whose value is not read

The identifier of a caption is data. The checker's test of an attribute reads the value only
where the attribute index gives the attribute a kind with a rule: a boolean attribute, a closed
list of keywords, an integer. `attrFree` is the rest of that test, which reads no value, so
one evaluation of it answers for every value. -/

namespace Content

open Whatwg.Html.Schema (Tag Attr)

/-- The checker reads no value of the attribute on the element: no row of the index applies,
or the row's kind is one that takes any text. -/
def valueFree (a : Attr) (t : Tag) : Bool :=
  match rowsFor a t with
  | [] => true
  | row :: _ =>
    match row.kind with
    | .boolean => false
    | .keywords false => false
    | .integer => false
    | .nonNegInteger => false
    | _ => true

theorem valueOk_of_valueFree {a : Attr} {t : Tag} (h : valueFree a t = true)
    (markup value : String) : valueOk a t markup value = true := by
  unfold valueFree at h
  unfold valueOk
  cases hrows : rowsFor a t with
  | nil => rfl
  | cons row rest =>
    rw [hrows] at h
    dsimp only at h ⊢
    revert h
    cases row.kind with
    | boolean => exact fun h => Bool.noConfusion h
    | keywords isOpen =>
      cases isOpen with
      | false => exact fun h => Bool.noConfusion h
      | true => exact fun _ => rfl
    | integer => exact fun h => Bool.noConfusion h
    | nonNegInteger => exact fun h => Bool.noConfusion h
    | float => exact fun _ => rfl
    | url => exact fun _ => rfl
    | text => exact fun _ => rfl
    | namePrefix => exact fun _ => rfl
/-- The element takes the attribute of this name with any value: `attrOk` with the value's
test replaced by `valueFree`. The test is closed, so one evaluation answers it. -/
def attrFree (t : Tag) (name : String) : Bool :=
  isPrefixed name ||
  match Attr.ofName? name with
  | some a =>
    (match t.attribs? with
      | some set => set.contains a
      | none => false) && valueFree a t
  | none => false

/-- An attribute that passes `attrFree` is admitted with every value. -/
theorem attrOk_of_attrFree {t : Tag} {name : String} (h : attrFree t name = true)
    (value : String) : attrOk t name value = true := by
  unfold attrFree at h
  unfold attrOk
  cases hprefix : isPrefixed name with
  | true => rfl
  | false =>
    rw [hprefix, Bool.false_or] at h
    rw [Bool.false_or]
    cases hname : Attr.ofName? name with
    | none =>
      rw [hname] at h
      exact Bool.noConfusion h
    | some a =>
      rw [hname] at h
      dsimp only at h ⊢
      rw [Bool.and_eq_true] at h
      rw [valueOk_of_valueFree h.2, Bool.and_true]
      cases hset : t.attribs? with
      | none =>
        rw [hset] at h
        exact Bool.noConfusion h.1
      | some set =>
        rw [hset] at h
        exact h.1

/-- One attribute that passes `attrFree` is a good attribute list, whatever its value. -/
theorem attrsOk_single {t : Tag} {name : String} (h : attrFree t name = true) (value : String) :
    attrsOk t [(name, value)] = true := by
  rw [attrsOk, List.all_cons, List.all_nil, Bool.and_true, attrOk_of_attrFree h value,
    Bool.true_and]
  rfl

end Content

/-! ## The figure -/

namespace Svg

/-- A `figcaption` takes an `id`, whatever the identifier is. -/
theorem attrsOk_figcaption_id (id : String) :
    Content.attrsOk .figcaption (rawAttrs [AttrVal.of .id id]) = true :=
  Content.attrsOk_single (t := .figcaption) (name := "id") (by decide +kernel) id

/-- The children of a figure that are a picture and then a caption follow the figure's model,
wherever the figure stands. -/
theorem seqOk_figure (ctx : Ctx) {children : List RawNode}
    (h : Content.childTags children = [.svg, .figcaption]) :
    Content.seqOk (ctx.child .figure) .figure children = true := by
  have hbase : (ctx.child .figure).base = .flow_with_figcaption := rfl
  unfold Content.seqOk
  rw [h, hbase]
  decide +kernel

/-- The caption of a figure as a typed element: a `figcaption` with the identifier that the
picture names. -/
def caption {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .figcaption))) :
    Element .figcaption (ctx.child .figure) :=
  Element.ofChildren content [AttrVal.of .id id]
    (by rw [Content.elementOk, attrsOk_figcaption_id, Content.seqOk_of_none _ _ rfl]; rfl)

/-- A picture in a `figure`, with the caption that names it. The identifier is written once
here: it is the `id` of the `figcaption` and the `aria-labelledby` of the picture. The picture
is an `svg` element, and with the two attributes it passes where the figure's children stand:
for a closed picture both premises are found by evaluation. `attrs` are the figure's own. -/
def figure {ctx : Ctx} (id : String) (picture : SvgNode)
    (content : List (Child ((ctx.child .figure).child .figcaption)))
    (attrs : List AttrVal := []) (role : String := "img")
    (hpicture : (picture.namedBy id role).okIn (ctx.child .figure) = true := by decide +kernel)
    (hsvg : picture.isSvg = true := by rfl)
    (hattrs : Content.attrsOk .figure (rawAttrs attrs) = true := by decide) :
    Element .figure ctx :=
  have hname : Schema.Tag.ofName? Whatwg.Svg.Schema.Tag.svg.name = none := by decide +kernel
  have hforeign : Schema.Tag.ofForeignName? Whatwg.Svg.Schema.Tag.svg.name = some .svg := by
    decide +kernel
  have htags : Content.childTags
      [(picture.namedBy id role).toRaw, (caption (ctx := ctx) id content).toRaw] =
        [.svg, .figcaption] := by
    match picture, hsvg with
    | .element .svg svgAttrs children, _ =>
      rw [SvgNode.namedBy, SvgNode.toRaw, Content.childTags, List.filterMap_cons,
        Content.RawNode.tag?, hname, hforeign]
      rfl
  ⟨attrs, [(picture.namedBy id role).toRaw, (caption id content).toRaw], hattrs,
    seqOk_figure ctx htags,
    Content.validAll_cons _ _ _ (SvgNode.validIn_of_okIn hpicture)
      (Content.validAll_cons _ _ _
        ((caption id content).valid (Content.Ctx.admitsWith_figcaption_child_figure ctx _))
        (Content.validAll_nil _)),
    by decide⟩

/-- The same figure as a raw tree, for a picture that is data: the picture named by the
caption, then the caption with its identifier. A fold puts this node among its nodes, and the
checker judges it where it stands. -/
def figureRaw (id : String) (picture : SvgNode) (content : List RawNode)
    (attrs : List (String × String) := []) (role : String := "img") : RawNode :=
  .element "figure" attrs
    [(picture.namedBy id role).toRaw, .element "figcaption" [("id", id)] content]

/-- The typed figure writes the raw one: the two are one tree. A check of a whole page reads
the identifier there: the pair `("id", id)` of the `figcaption`. -/
theorem figure_toRaw {ctx : Ctx} (id : String) (picture : SvgNode)
    (content : List (Child ((ctx.child .figure).child .figcaption))) (attrs : List AttrVal)
    (role : String) (hpicture : (picture.namedBy id role).okIn (ctx.child .figure) = true)
    (hsvg : picture.isSvg = true) (hattrs : Content.attrsOk .figure (rawAttrs attrs) = true) :
    (figure id picture content attrs role hpicture hsvg hattrs).toRaw =
      figureRaw id picture (content.map Child.raw) (rawAttrs attrs) role := rfl

end Svg

end Whatwg.Html
