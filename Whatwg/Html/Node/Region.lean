import Whatwg.Html.Node.Splice

/-!
# Whatwg.Html.Node.Region

Owner: the scrollable region, and the figure that holds one (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`, its second round; entry W13 of
`docs/research/2026-10-12-whatwg-requests.md`).

A table or a picture that is wider than its page scrolls inside a box. A reader with a keyboard
must be able to reach the box, and a reader with a screen reader to know what it is. The usual
form is a `div` with `tabindex="0"`, `role="region"` and a name: `aria-label` with the words, or
`aria-labelledby` with the `id` of the element that holds them.

```
region (.label "Table: Claim, Status") [table] (some "scroll")
-- <div class="scroll" role="region" tabindex="0" aria-label="Table: Claim, Status">…</div>
```

- `region name children` is the typed element, and `Region.child` places it. `regionRaw` is the
  same tree as a raw node, for a fold of data. `region_toRaw` says that the two are one tree.
- `Region.figure id content caption` is a `figure` whose content stands in a region that the
  caption names. The identifiers are made from one stem, written once: the figure is `id`, its
  caption `id-caption`, its words `id-words`.
- `Region.figureRaw` is that figure as a raw node, and it also takes the figure in words: a
  `details` below the region, which the figure names in `aria-describedby`.

What is proved once. The attributes of a region are good for every name and every class
(`Region.attrsOk`), and a region is admitted with them wherever a `div` is
(`Region.admitsWith`). A figure admits a `div` and a `figcaption` among its children under
every ancestor (`Ctx.admits_div_child_figure`, `Ctx.admits_figcaption_child_figure`), and a
region and then a caption follow its ordered model. So `Region.figure` owes nothing but its
typed children, wherever a figure may stand.

What this module does not claim. That a region is no interactive content: the HTML Standard
says that `tabindex` can make any element interactive content, and the content model of this
package does not read that sentence, so a region inside a link passes here. That an identifier
stands once in its page (entry W2). And the figure in words has no typed form: a `details` is
interactive content, so its place depends on what stands above the figure, and its ordered
model reads its children. A fold writes it as a raw node, and the checker judges it there.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

/-! ## Where a child is admitted under every ancestor -/

namespace Content.Ctx

/-- The answer of `hits` at a tag that no exclusion can refuse. -/
def noHits : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false]

/-- A tag that no flag hits is excluded by no exclusions. -/
theorem excluded_of_noHits {tag : Tag} (h : hits tag = noHits) (x : Exclusions) :
    excluded x tag = false := by
  rw [excluded_eq_spec, excludedSpec, h]
  cases x
  simp only [Exclusions.flags, noHits, List.zip_cons_cons, List.zip_nil_right, List.any_cons,
    List.any_nil, Bool.and_false, Bool.or_false]

/-- The children of an element that is not transparent take a tag that the element names,
when no exclusion can refuse the tag: whatever stands above the element. -/
theorem admits_child_of_noHits {parent tag : Tag} (ctx : Ctx)
    (hopaque : parent.isTransparent = false)
    (hnamed : (parent.ownBase.contains tag || parent.labelled.contains tag) = true)
    (hhits : hits tag = noHits) : (ctx.child parent).admits tag = true := by
  rw [admits, excluded_of_noHits hhits]
  simp only [child, hopaque, Bool.false_eq_true, ↓reduceIte, hnamed, Bool.not_false, Bool.and_self]

/-- A figure admits a `div` among its children, wherever the figure stands. -/
theorem admits_div_child_figure (ctx : Ctx) : (ctx.child .figure).admits .div = true :=
  admits_child_of_noHits ctx (by decide) (by decide) (by decide)

/-- A figure admits a `figcaption` among its children, wherever the figure stands. -/
theorem admits_figcaption_child_figure (ctx : Ctx) :
    (ctx.child .figure).admits .figcaption = true :=
  admits_child_of_noHits ctx (by decide) (by decide) (by decide)

end Content.Ctx

/-! ## The region -/

namespace Region

/-- How a region is named: by its own words, or by the element that holds them. -/
inductive Name where
  /-- `aria-label`, with the words. -/
  | label (words : String)
  /-- `aria-labelledby`, with the identifier of the element that holds the words. -/
  | labelledBy (id : String)
  deriving DecidableEq, Repr, Inhabited

/-- The attribute that names a region. -/
def Name.attr : Name → AttrVal
  | .label words => ⟨.aria_, "aria-label", words⟩
  | .labelledBy id => ⟨.aria_, "aria-labelledby", id⟩

/-- The attribute `class`. -/
def classAttr (classes : String) : AttrVal := ⟨.«class», "class", classes⟩

/-- The attributes of a scrollable region: a class when one is given, `role="region"`,
`tabindex="0"`, and the name. -/
def attrs (name : Name) (className : Option String := none) : List AttrVal :=
  A.opt classAttr className ++ [⟨.role, "role", "region"⟩, ⟨.tabindex, "tabindex", "0"⟩, name.attr]

/-- A `div` takes the attributes of a region, for every name and every class. -/
theorem attrsOk (name : Name) (className : Option String) :
    Content.attrsOk .div (rawAttrs (attrs name className)) = true := by
  have hlabel := fun words => Content.attrOk_of_attrFree (t := .div) (name := "aria-label")
    (by decide +kernel) words
  have hlabelledby := fun id => Content.attrOk_of_attrFree (t := .div) (name := "aria-labelledby")
    (by decide +kernel) id
  have hclass := fun c => Content.attrOk_of_attrFree (t := .div) (name := "class")
    (by decide +kernel) c
  cases name <;> cases className <;>
    simp only [attrs, Name.attr, classAttr, A.opt, rawAttrs, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, Content.attrsOk, List.all_cons, List.all_nil, List.length_cons,
      List.length_nil, hlabel, hlabelledby, hclass, Bool.and_true, Bool.true_and] <;>
    decide +kernel

/-- A region is admitted with its attributes wherever a `div` is: no category of `div` reads
an attribute. -/
theorem admitsWith {ctx : Ctx} (h : ctx.admits .div = true) (name : Name)
    (className : Option String) : ctx.admitsWith .div (rawAttrs (attrs name className)) = true :=
  Content.Ctx.admitsWith_unread ctx .div _ (by decide) h

end Region

/-- A scrollable region: a `div` that takes the keyboard, is a landmark and has a name, around
content that may be wider than its page. -/
def region {ctx : Ctx} (name : Region.Name) (children : List (Child (ctx.child .div)))
    (className : Option String := none) : Element .div ctx :=
  Element.ofChildren children (Region.attrs name className)
    (by rw [Content.elementOk, Region.attrsOk, Content.seqOk_of_none _ _ rfl]; rfl)

/-- A region placed where a `div` may stand. -/
def Region.child {ctx : Ctx} (name : Region.Name) (children : List (Child (ctx.child .div)))
    (className : Option String := none) (h : ctx.admits .div = true := by decide) : Child ctx :=
  Child.of (region name children className) (Region.admitsWith h name className)

/-- The same region as a raw node, for a fold of data. -/
def regionRaw (name : Region.Name) (children : List RawNode) (className : Option String := none) :
    RawNode :=
  .element "div" (rawAttrs (Region.attrs name className)) children

/-- The typed region writes the raw one. -/
theorem region_toRaw {ctx : Ctx} (name : Region.Name) (children : List (Child (ctx.child .div)))
    (className : Option String) :
    (region name children className).toRaw = regionRaw name (children.map Child.raw) className :=
  rfl

/-! ## A figure around a region -/

namespace Region

/-- The identifier of a figure's caption, from the figure's. -/
def captionId (id : String) : String := id ++ "-caption"

/-- The identifier of a figure's words, from the figure's. -/
def wordsId (id : String) : String := id ++ "-words"

/-- A `figure` takes an `id`, and a class when one is given, whatever they are. -/
theorem attrsOk_figure (id : String) (className : Option String) :
    Content.attrsOk .figure (rawAttrs (⟨.id, "id", id⟩ :: A.opt classAttr className)) = true := by
  have hid := fun v => Content.attrOk_of_attrFree (t := .figure) (name := "id") (by decide +kernel) v
  have hclass := fun c => Content.attrOk_of_attrFree (t := .figure) (name := "class")
    (by decide +kernel) c
  cases className <;>
    simp only [classAttr, A.opt, rawAttrs, List.map_cons, List.map_nil, Content.attrsOk,
      List.all_cons, List.all_nil, List.length_cons, List.length_nil, hid, hclass, Bool.and_true,
      Bool.true_and] <;>
    decide +kernel

/-- A region and then a caption follow the ordered model of a figure, wherever it stands. -/
theorem seqOk_figure (ctx : Ctx) {children : List RawNode}
    (h : Content.childTags children = [.div, .figcaption]) :
    Content.seqOk (ctx.child .figure) .figure children = true := by
  have hbase : (ctx.child .figure).base = .flow_with_figcaption := rfl
  unfold Content.seqOk
  rw [h, hbase]
  decide +kernel

/-- The caption of a figure, with the identifier that its region names. -/
def caption {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .figcaption))) :
    Element .figcaption (ctx.child .figure) :=
  Element.ofChildren content [AttrVal.of .id (captionId id)]
    (by
      rw [Content.elementOk, Content.seqOk_of_none _ _ rfl]
      exact (congrArg (· && true)
        (Content.attrsOk_single (t := .figcaption) (name := "id") (by decide +kernel) _)).trans rfl)

/-- A figure whose content scrolls in a region that its caption names. The content is typed
children of the region: a picture placed with `Child.ofSvg`, or a table. The figure is `id`, and
its caption `id-caption`, which the region names in `aria-labelledby`: the stem is written once.
Nothing is owed: the figure is good wherever a figure may stand. -/
def figure {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (className regionClass : Option String := none) : Element .figure ctx :=
  let box := region (ctx := ctx.child .figure) (.labelledBy (captionId id)) content regionClass
  have htags : Content.childTags [box.toRaw, (caption (ctx := ctx) id captionContent).toRaw] =
      [.div, .figcaption] := rfl
  ⟨⟨.id, "id", id⟩ :: A.opt classAttr className,
    [box.toRaw, (caption id captionContent).toRaw], attrsOk_figure id className,
    seqOk_figure ctx htags,
    Content.validAll_cons _ _ _
      (box.valid (admitsWith (Content.Ctx.admits_div_child_figure ctx) _ regionClass))
      (Content.validAll_cons _ _ _
        ((caption id captionContent).valid
          (Content.Ctx.admitsWith_unread _ .figcaption _ (by decide)
            (Content.Ctx.admits_figcaption_child_figure ctx)))
        (Content.validAll_nil _)),
    by decide⟩

/-- The figure in words, as a raw node: a `details` with the identifier that the figure names,
a summary, and the words. -/
def wordsRaw (id summary : String) (body : List RawNode) : RawNode :=
  .element "details" [("id", wordsId id)] (.element "summary" [] [.text summary] :: body)

/-- The same figure as a raw node, for a fold of data, with the figure in words when there are
any: `words` is the text of the summary and the nodes below it. The words stand in a `details`
between the region and the caption, and the figure names them in `aria-describedby`. -/
def figureRaw (id : String) (content captionContent : List RawNode)
    (words : Option (String × List RawNode) := none) (className regionClass : Option String := none) :
    RawNode :=
  .element "figure"
    (rawAttrs (⟨.id, "id", id⟩ :: A.opt classAttr className) ++
      (match words with
        | some _ => [("aria-describedby", wordsId id)]
        | none => []))
    (regionRaw (.labelledBy (captionId id)) content regionClass ::
      ((match words with
        | some (summary, body) => [wordsRaw id summary body]
        | none => []) ++
      [.element "figcaption" [("id", captionId id)] captionContent]))

/-- The typed figure writes the raw one with no words. -/
theorem figure_toRaw {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (className regionClass : Option String) :
    (figure id content captionContent className regionClass).toRaw =
      figureRaw id (content.map Child.raw) (captionContent.map Child.raw) none className
        regionClass := by
  cases className <;> rfl

end Region

end Whatwg.Html
