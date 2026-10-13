import Whatwg.Html.Node.Region
import Whatwg.Html.Node.Run

/-!
# Whatwg.Html.Node.Region.Words

Owner: the figure in words, typed, and a figure whose words stand after it (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; what was left of entry W13 of
`docs/research/2026-10-12-whatwg-requests.md`; debt D139).

`Whatwg/Html/Node/Region.lean` gives a figure whose content scrolls in a region that its
caption names. A picture also has words: a `details` that says what the picture shows, for a
reader who does not see it. That module writes the words as a raw node, between the region and
the caption, because a `details` has an ordered content model and the typed tree could not take
a body that is data. `Whatwg/Html/Node/Run.lean` can, so here:

- `Region.words id summary body` is the words as a typed element: a `details` with the
  identifier `id-words`, its summary, and a body that is content of the base `flow`. Nothing is
  owed where it is used. `Region.wordsNode` is the same tree as a raw node, with a class, and
  `Region.words_toRaw` says that the two are one tree.
- `Region.described` is the figure of `Region.figure` that names its words in
  `aria-describedby` and holds none. `Region.describedRaw` is the same as a raw node.
- `Region.withWords` is the two in a row: the figure, with its caption beside its picture, and
  after it the words. `Region.withWordsRaw` is the same as raw nodes. This is the placement
  that entry W13 asks for.

The figure and its words are given together because each needs the other: the figure names
the identifier that only the words define.

What this module does not claim: what `Region.lean` does not. No sealed text states the rules
of `aria-describedby`; that a figure that names its words is announced with them is from
memory of WAI-ARIA, not checked (debt D138). And the pair is not shown to be closed in the
sense of `Content.Document.Closed`: the three identifiers come from one stem, and that they
differ from each other and from those of the content is checked on a page by
`Content.Document.errors`, not proved here.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

namespace Content.Ctx

/-- A `details` admits a `summary` among its children, wherever the `details` stands. -/
theorem admits_summary_child_details (ctx : Ctx) : (ctx.child .details).admits .summary = true :=
  admits_child_of_noHits ctx (by decide) (by decide) (by decide)

/-- A `summary` admits text, wherever it stands. -/
theorem admits_text_child_summary (ctx : Ctx) : (ctx.child .summary).admits .pcdata = true :=
  admits_child_of_noHits ctx (by decide) (by decide) (by decide)

end Content.Ctx

namespace Region

/-! ## The words -/

/-- A `details` takes an `id`, and a class when one is given, whatever they are. -/
theorem attrsOk_words (id : String) (className : Option String) :
    Content.attrsOk .details (rawAttrs (⟨.id, "id", id⟩ :: A.opt classAttr className)) = true := by
  have hid := fun v => Content.attrOk_of_attrFree (t := .details) (name := "id") (by decide +kernel) v
  have hclass := fun c => Content.attrOk_of_attrFree (t := .details) (name := "class")
    (by decide +kernel) c
  cases className <;>
    simp only [classAttr, A.opt, rawAttrs, List.map_cons, List.map_nil, Content.attrsOk,
      List.all_cons, List.all_nil, List.length_cons, List.length_nil, hid, hclass, Bool.and_true,
      Bool.true_and] <;>
    decide +kernel

/-- The summary of the words: a text. -/
def wordsSummary {ctx : Ctx} (text : String) : Element .summary (ctx.child .details) :=
  Element.ofChildren [Child.text text (Content.Ctx.admits_text_child_summary _)] []
    (by rw [Content.elementOk, Content.seqOk_of_none _ _ rfl]; rfl)

/-- **The figure in words**: a `details` with the identifier that the figure names, a summary,
and a body that is content of the base `flow`, typed at the position of that content. It may
stand wherever a `details` may, and owes nothing there. -/
def words {ctx : Ctx} (id summary : String)
    (body : List (Child ((ctx.child .details).rebase .flow))) (className : Option String := none) :
    Element .details ctx :=
  Element.ofRun
    ((Run.el (wordsSummary summary)
        (Content.Ctx.admitsWith_unread _ .summary _ (by decide)
          (Content.Ctx.admits_summary_child_details ctx))).append
      (Run.content .flow body))
    (⟨.id, "id", wordsId id⟩ :: A.opt classAttr className) (attrsOk_words (wordsId id) className)

/-- The words as a raw node, for a fold of data, with a class when one is given. -/
def wordsNode (id summary : String) (body : List RawNode) (className : Option String := none) :
    RawNode :=
  .element "details" (rawAttrs (⟨.id, "id", wordsId id⟩ :: A.opt classAttr className))
    (.element "summary" [] [.text summary] :: body)

/-- With no class, the node is the one that `Region.figureRaw` puts inside a figure. -/
theorem wordsNode_none (id summary : String) (body : List RawNode) :
    wordsNode id summary body none = wordsRaw id summary body := rfl

/-- The typed words write the raw ones. -/
theorem words_toRaw {ctx : Ctx} (id summary : String)
    (body : List (Child ((ctx.child .details).rebase .flow))) (className : Option String) :
    (words id summary body className).toRaw =
      wordsNode id summary (body.map Child.raw) className := rfl

/-! ## A figure that names its words -/

/-- The attribute by which a figure names its words. -/
def describedBy (id : String) : AttrVal := ⟨.aria_, "aria-describedby", wordsId id⟩

/-- A `figure` takes an `id`, a class when one is given, and `aria-describedby`. -/
theorem attrsOk_described (id : String) (className : Option String) :
    Content.attrsOk .figure
      (rawAttrs (⟨.id, "id", id⟩ :: A.opt classAttr className ++ [describedBy id])) = true := by
  have hid := fun v => Content.attrOk_of_attrFree (t := .figure) (name := "id") (by decide +kernel) v
  have hclass := fun c => Content.attrOk_of_attrFree (t := .figure) (name := "class")
    (by decide +kernel) c
  have hnames := fun v => Content.attrOk_of_attrFree (t := .figure) (name := "aria-describedby")
    (by decide +kernel) v
  cases className <;>
    simp only [describedBy, classAttr, A.opt, rawAttrs, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, Content.attrsOk, List.all_cons, List.all_nil, List.length_cons,
      List.length_nil, hid, hclass, hnames, Bool.and_true, Bool.true_and] <;>
    decide +kernel

/-- **The figure of `Region.figure`, naming its words**: its content scrolls in a region that
its caption names, and `aria-describedby` names the words, which stand elsewhere. The model of
`figure` is followed by a run of two children, for every position. -/
def described {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (className regionClass : Option String := none) : Element .figure ctx :=
  Element.ofRun
    ((Run.el (region (.labelledBy (captionId id)) content regionClass)
        (admitsWith (Content.Ctx.admits_div_child_figure ctx) _ regionClass)).append
      (Run.el (caption id captionContent)
        (Content.Ctx.admitsWith_unread _ .figcaption _ (by decide)
          (Content.Ctx.admits_figcaption_child_figure ctx))))
    (⟨.id, "id", id⟩ :: A.opt classAttr className ++ [describedBy id]) (attrsOk_described id className)

/-- The same figure as a raw node. -/
def describedRaw (id : String) (content captionContent : List RawNode)
    (className regionClass : Option String := none) : RawNode :=
  .element "figure"
    (rawAttrs (⟨.id, "id", id⟩ :: A.opt classAttr className) ++ [("aria-describedby", wordsId id)])
    [regionRaw (.labelledBy (captionId id)) content regionClass,
      .element "figcaption" [("id", captionId id)] captionContent]

/-- The typed figure writes the raw one. -/
theorem described_toRaw {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (className regionClass : Option String) :
    (described id content captionContent className regionClass).toRaw =
      describedRaw id (content.map Child.raw) (captionContent.map Child.raw) className regionClass := by
  cases className <;> rfl

/-! ## The figure, and after it its words -/

/-- **A figure and, after it, the figure in words**: two children in a row. The caption stays
beside the picture, and the figure names the words. Owed: that the position takes a `figure`
and a `details`. -/
def withWords {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (summary : String) (body : List (Child ((ctx.child .details).rebase .flow)))
    (className regionClass wordsClass : Option String := none)
    (hfigure : ctx.admits .figure = true := by admits)
    (hdetails : ctx.admits .details = true := by admits) : List (Child ctx) :=
  [Child.of (described id content captionContent className regionClass)
      (Content.Ctx.admitsWith_unread _ .figure _ (by decide) hfigure),
    Child.of (words id summary body wordsClass)
      (Content.Ctx.admitsWith_unread _ .details _ (by decide) hdetails)]

/-- The same two nodes as raw nodes, for a fold of data. -/
def withWordsRaw (id : String) (content captionContent : List RawNode) (summary : String)
    (body : List RawNode) (className regionClass wordsClass : Option String := none) : List RawNode :=
  [describedRaw id content captionContent className regionClass,
    wordsNode id summary body wordsClass]

/-- The typed pair writes the raw one. -/
theorem withWords_raw {ctx : Ctx} (id : String)
    (content : List (Child ((ctx.child .figure).child .div)))
    (captionContent : List (Child ((ctx.child .figure).child .figcaption)))
    (summary : String) (body : List (Child ((ctx.child .details).rebase .flow)))
    (className regionClass wordsClass : Option String) (hfigure : ctx.admits .figure = true)
    (hdetails : ctx.admits .details = true) :
    (withWords id content captionContent summary body className regionClass wordsClass hfigure
        hdetails).map Child.raw =
      withWordsRaw id (content.map Child.raw) (captionContent.map Child.raw) summary
        (body.map Child.raw) className regionClass wordsClass := by
  cases className <;> rfl

end Region

end Whatwg.Html
