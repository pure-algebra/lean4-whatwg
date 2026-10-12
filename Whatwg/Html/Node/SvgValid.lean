import Whatwg.Html.Node.SvgKeys
import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.SvgValid

Owner: the structure of a typed SVG tree, judged by its tags (slice S6 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-36). The checker `Content.validAt` judges a raw tree: it
decodes each name to its characters and looks it up. A typed tree already holds each element as
a tag of the schema and each attribute as its key. `SvgNode.okAt` judges a typed tree at a
position by those alone: the admission of the tag by a mask, the attribute list in one pass
over its keys (`SvgAttr.allOk`), the counts of the content model over the children's tags, and
every child at the position below.

`SvgNode.validAt_toRaw` is the law: the checker's verdict on the raw tree of a typed tree is
`okAt`'s verdict on the typed tree, at every position. So the structure of a typed tree is
decided with no name read. Three things follow. The kernel evaluates `okAt` on a picture of 300
elements in about a fiftieth of the time it takes the checker on the written names
(`WhatwgTest/Html/SvgBenchmark.lean`). A program checks a tree it built without writing a name.
And a tree whose numbers and texts are variables has its structure by one small evaluation,
because `okAt` forces no value.

How a test is proved. A closed test is `by decide +kernel`. A test with free values is
`by conv => lhs; whnf`, which reduces it to `true` or `false` and stops at no value. Where a
value picks the tree's shape, such as a key that is written only when it is not empty, split
on that value first: `cases key.isEmpty <;> conv => lhs; whnf`. A tree with a free list of
children is taken apart with the equations at the end of this module (`okIn_svg`, `okAt_g`,
`okAt_svg_element`, `okAllAt_cons`, `okAllAt_append`, `okAllAt_reverse`, `okAllAt_map`), and
what is left closed is evaluated the same way. `WhatwgTest/Html/SvgValid.lean` does each, and
`WhatwgTest/Html/SvgPicture.lean` a whole fold. A bare `rfl` closes many of these tests and
not all: the elaborator's unifier may unfold a shift by recursion on its amount, and give up
at the mask index of an attribute such as `fill`. When an evaluation ends in `false = true`,
`Content.explain ctx node.toRaw` at a closed instance names the node and the reason.

The tag type is `Whatwg.Svg.Schema.Tag`, and `Whatwg.Svg.Value.kindOf t a` says which type the
value of the attribute `a` has on the element `t`.

With `SvgNode.valuesOk_toRaw` a typed tree has both judgments without a text: its values by
their types, and its structure by `okAt`.

What `okAt` reads as text, and why:

- the key of a custom data attribute, which is a string: `SvgAttr.dataKeyOk`;
- a raw subtree, `SvgNode.raw`: the HTML content below `foreignObject`, `title` and `desc` is a
  raw tree, and the checker judges it;
- an element at an HTML position that is not `svg`. The checker reads its name as an HTML name
  there, so `okAt` hands that one node to the checker's own test.

`Child.ofSvg` places a typed tree in the typed HTML tree of `Whatwg/Html/Node/Typed.lean`: a
`Child ctx` whose raw node is the tree's and whose proof is the law.

What this module does not claim: a refusal's reason. `Content.explain` of the raw tree answers
the node and the reason. Nor anything about a value, which the type gives.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Html.Schema (Exclusions Base)
open Whatwg.Html.Content (Ctx Pos validAt validAllAt validIn integrationBase)

namespace Content

/-- The position of the children of an outermost `svg`, under the HTML exclusions `x`. A `g`
keeps it (`Pos.belowElement_g`), so the marks of a picture stand here at every depth of
grouping. It is reducible, so an equation of `SvgNode.okAt` at an SVG position rewrites at
it. -/
abbrev Pos.inSvg (x : Exclusions) : Pos := .svg (Whatwg.Svg.Content.Ctx.outside.child .svg) x

/-- The position of the children of an outermost `svg` that stands at the HTML position `c`:
`Pos.inSvg` under the exclusions that pass through the `svg`. -/
abbrev Pos.belowSvg (c : Ctx) : Pos := Pos.inSvg (c.child .svg).excl

/-- The position of the children of the SVG element `t` that stands at an SVG position: the
HTML position of an integration point, or the SVG position below the element. -/
def Pos.belowElement (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) (t : Tag) : Pos :=
  match integrationBase t with
  | some base => .html ⟨base, x, []⟩
  | none => .svg (c.child t) x

/-- Below an element that is no integration point the position stays in SVG. -/
theorem Pos.belowElement_of_none {t : Tag} (h : integrationBase t = none)
    (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x t = .svg (c.child t) x := by
  rw [Pos.belowElement, h]

/-- Below an integration point the position is the HTML position of its base. -/
theorem Pos.belowElement_of_some {t : Tag} {base : Base} (h : integrationBase t = some base)
    (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x t = .html ⟨base, x, []⟩ := by
  rw [Pos.belowElement, h]

/-- Below an element that is no integration point, does not inherit and does not hand on, the
position reads the element alone: it is the same wherever the element stands. -/
theorem Pos.belowElement_plain {t : Tag} (hb : integrationBase t = none)
    (hi : t.model.inherits = false) (hh : Whatwg.Svg.Schema.handsOn.mem t = false)
    (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x t = .svg (Whatwg.Svg.Content.Ctx.outside.child t) x := by
  rw [Pos.belowElement_of_none hb,
    Whatwg.Svg.Content.Ctx.child_eq_of_plain hi hh c Whatwg.Svg.Content.Ctx.outside]

/-- A group keeps the position of an outermost `svg`'s children, wherever the group stands:
what may stand among the marks of a picture may stand in a `g`, at every depth. -/
theorem Pos.belowElement_g (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x .g = Pos.inSvg x := by
  have h : Whatwg.Svg.Content.Ctx.outside.child .g = Whatwg.Svg.Content.Ctx.outside.child .svg := by
    decide +kernel
  rw [Pos.belowElement_plain rfl rfl (by decide +kernel), h]

/-- The foreign tag `svg` has no conditional category, so its admission reads no attribute. -/
theorem Ctx.admitsWith_svg (c : Ctx) (attrs : List (String × String)) :
    c.admitsWith .svg attrs = c.admits .svg := by
  have hbase : ∀ b : Base, Ctx.baseContainsWith b .svg attrs = b.contains .svg := by
    intro b
    cases b <;> rfl
  rw [Ctx.admitsWith, Ctx.admits, hbase]
  rfl

end Content

namespace SvgNode

/-! ## Names -/

theorem toList_name (t : Tag) : t.name.toList = t.chars := String.toList_ofList

/-- The name of a typed element reads back as its tag. -/
theorem ofChars?_name (t : Tag) : Tag.ofChars? t.name.toList = some t := by
  rw [toList_name, Tag.ofChars?_chars]

/-- The transition of the checker at the name of a typed element, at an SVG position. -/
theorem child_svg_name (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) (t : Tag) :
    (Pos.svg c x).child t.name = Pos.belowElement c x t := by
  rw [Pos.belowElement]
  cases hb : integrationBase t with
  | some base => exact Content.Pos.child_svg_integration (ofChars?_name t) hb
  | none => exact Content.Pos.child_svg_element (ofChars?_name t) hb

/-! ## The children's tags -/

/-- The SVG tag of a node, as a count of the content model reads it: an element's tag, and for
a raw subtree what the checker reads from its name. -/
def tag? : SvgNode → Option Tag
  | .element t _ _ => some t
  | .raw node _ => Content.RawNode.svgTag? node
  | _ => none

/-- The SVG tags of a forest. -/
def tags (nodes : List SvgNode) : List Tag := nodes.filterMap tag?

theorem svgTag?_toRaw : ∀ node : SvgNode, Content.RawNode.svgTag? node.toRaw = node.tag?
  | .element t _ _ => by
    rw [toRaw]
    exact ofChars?_name t
  | .text _ => rfl
  | .entity _ => rfl
  | .comment _ => rfl
  | .raw _ _ => rfl

/-- The tags that the checker counts in the raw forest are the tags of the typed forest. -/
theorem svgChildTags_toRawAll : ∀ nodes : List SvgNode,
    Content.svgChildTags (toRawAll nodes) = tags nodes
  | [] => rfl
  | node :: rest => by
    rw [toRawAll, Content.svgChildTags, List.filterMap_cons, svgTag?_toRaw, tags,
      List.filterMap_cons]
    have ih := svgChildTags_toRawAll rest
    rw [Content.svgChildTags, tags] at ih
    rw [ih]

theorem tags_append (nodes others : List SvgNode) :
    tags (nodes ++ others) = tags nodes ++ tags others := by
  rw [tags, tags, tags, List.filterMap_append]

/-! ## The structure of a typed tree -/

mutual

/-- The typed tree may stand at the position and its subtree is valid, judged by its tags and
its keys. At an SVG position: the position admits the tag, the attribute list passes
`SvgAttr.allOk`, the counts of the content model hold of the children's tags, and every child
passes at the position below. At an HTML position the element `svg` is the foreign root and is
judged the same way; any other element there is handed to the checker's own test of one node.
A raw subtree is the checker's. -/
def okAt : Pos → SvgNode → Bool
  | .svg c x, .element t attrs children =>
    c.admits t && SvgAttr.allOk attrs && Whatwg.Svg.Content.boundsOk t (tags children) &&
      okAllAt (Pos.belowElement c x t) children
  | .html c, .element t attrs children =>
    if t = .svg then
      c.admits .svg && SvgAttr.allOk attrs && Whatwg.Svg.Content.boundsOk t (tags children) &&
        okAllAt (Pos.belowSvg c) children
    else
      (Pos.html c).elementOk t.name (attrs.map SvgAttr.toPair) (toRawAll children) &&
        okAllAt ((Pos.html c).child t.name) children
  | p, .text _ => p.textOk
  | p, .entity _ => p.textOk
  | p, .comment _ => p.commentOk
  | p, .raw node _ => validAt p node

/-- Every tree of the forest passes at the position. -/
def okAllAt : Pos → List SvgNode → Bool
  | _, [] => true
  | p, node :: rest => okAt p node && okAllAt p rest

end

/-- The typed tree may stand at the HTML position `ctx` and its subtree is valid. -/
def okIn (ctx : Ctx) (node : SvgNode) : Bool := okAt (.html ctx) node

/-! ## The law -/

mutual

/-- Node V8, the law of structure: the checker's verdict on the raw tree of a typed tree is the
verdict of `okAt` on the typed tree, at every position. -/
theorem validAt_toRaw : ∀ (p : Pos) (node : SvgNode), validAt p node.toRaw = okAt p node
  | .svg c x, .element t attrs children => by
    rw [toRaw, Content.validAt_element, child_svg_name, validAllAt_toRawAll, okAt,
      Content.Pos.elementOk]
    simp only [ofChars?_name, Content.svgElementOk, SvgAttr.svgAttrsOk_toPairs,
      svgChildTags_toRawAll, Bool.and_assoc]
  | .html c, .element t attrs children => by
    rw [toRaw, Content.validAt_element, validAllAt_toRawAll, okAt]
    cases hd : decide (t = .svg) with
    | false =>
      rw [if_neg (of_decide_eq_false hd)]
    | true =>
      have ht : t = .svg := of_decide_eq_true hd
      subst ht
      have hname : Schema.Tag.ofName? Tag.svg.name = none := by decide +kernel
      have hforeign : Schema.Tag.ofForeignName? Tag.svg.name = some .svg := by decide +kernel
      rw [if_pos rfl, Content.Pos.child_html_svg hname hforeign, Content.Pos.elementOk]
      simp only [hname, hforeign, Content.Ctx.admitsWith_svg, Content.svgElementOk,
        SvgAttr.svgAttrsOk_toPairs, svgChildTags_toRawAll, Bool.and_assoc, Pos.belowSvg]
  | p, .text content => by rw [toRaw, Content.validAt_text, okAt]
  | p, .entity name => by rw [toRaw, Content.validAt_entity, okAt]
  | p, .comment content => by rw [toRaw, Content.validAt_comment, okAt]
  | p, .raw node h => by rw [toRaw, okAt]

/-- The law over a forest. -/
theorem validAllAt_toRawAll : ∀ (p : Pos) (nodes : List SvgNode),
    validAllAt p (toRawAll nodes) = okAllAt p nodes
  | p, [] => by rw [toRawAll, Content.validAllAt_nil, okAllAt]
  | p, node :: rest => by
    rw [toRawAll, Content.validAllAt_cons, validAt_toRaw p node, validAllAt_toRawAll p rest,
      okAllAt]

end

/-- The law at an HTML position: `validIn` of the raw tree is `okIn` of the typed tree. -/
theorem validIn_toRaw (ctx : Ctx) (node : SvgNode) : validIn ctx node.toRaw = node.okIn ctx :=
  validAt_toRaw (.html ctx) node

/-- A typed tree that passes `okIn` has a valid raw tree. -/
theorem validIn_of_okIn {ctx : Ctx} {node : SvgNode} (h : node.okIn ctx = true) :
    validIn ctx node.toRaw = true := by
  rw [validIn_toRaw, h]

/-! ## The test, case by case

The equations a proof about a tree with variable parts rewrites with. -/

theorem okAt_svg_element (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) (t : Tag)
    (attrs : List (SvgAttr t)) (children : List SvgNode) :
    okAt (.svg c x) (.element t attrs children) =
      (c.admits t && SvgAttr.allOk attrs && Whatwg.Svg.Content.boundsOk t (tags children) &&
        okAllAt (Pos.belowElement c x t) children) := by
  rw [okAt]

/-- The foreign root: `svg` at an HTML position. Its model states no count, so nothing is left
of its children but the test of each. -/
theorem okIn_svg (ctx : Ctx) (attrs : List (SvgAttr .svg)) (children : List SvgNode) :
    okIn ctx (.element .svg attrs children) =
      (ctx.admits .svg && SvgAttr.allOk attrs && okAllAt (Pos.belowSvg ctx) children) := by
  rw [okIn, okAt, if_pos rfl, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, Bool.and_true]

/-- A group at an SVG position: its admission, its attributes, and its children where the
marks of a picture stand, whatever stands around the group. -/
theorem okAt_g (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) (attrs : List (SvgAttr .g))
    (children : List SvgNode) :
    okAt (.svg c x) (.element .g attrs children) =
      (c.admits .g && SvgAttr.allOk attrs && okAllAt (Pos.inSvg x) children) := by
  rw [okAt_svg_element, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, Bool.and_true,
    Pos.belowElement_g]

/-- A group among the marks of a picture: its attributes, and its children among the marks. -/
theorem okAt_inSvg_g (x : Exclusions) (attrs : List (SvgAttr .g)) (children : List SvgNode) :
    okAt (Pos.inSvg x) (.element .g attrs children) =
      (SvgAttr.allOk attrs && okAllAt (Pos.inSvg x) children) := by
  have h : (Whatwg.Svg.Content.Ctx.outside.child .svg).admits .g = true := by decide +kernel
  rw [okAt_g, h, Bool.true_and]

theorem okAllAt_nil (p : Pos) : okAllAt p [] = true := by rw [okAllAt]

theorem okAllAt_cons (p : Pos) (node : SvgNode) (rest : List SvgNode) :
    okAllAt p (node :: rest) = (okAt p node && okAllAt p rest) := by rw [okAllAt]

theorem okAllAt_append (p : Pos) : ∀ nodes others : List SvgNode,
    okAllAt p (nodes ++ others) = (okAllAt p nodes && okAllAt p others)
  | [], others => by rw [List.nil_append, okAllAt_nil, Bool.true_and]
  | node :: rest, others => by
    rw [List.cons_append, okAllAt_cons, okAllAt_cons, okAllAt_append p rest others,
      Bool.and_assoc]

/-- A forest passes exactly when each of its trees does. -/
theorem okAllAt_iff (p : Pos) : ∀ nodes : List SvgNode,
    okAllAt p nodes = true ↔ ∀ node ∈ nodes, okAt p node = true
  | [] => by
    rw [okAllAt_nil]
    exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | node :: rest => by
    rw [okAllAt_cons, Bool.and_eq_true, okAllAt_iff p rest, List.forall_mem_cons]

/-- The test of a forest is `List.all` of the test of a tree, so every lemma of `List.all` is
a lemma of it. -/
theorem okAllAt_eq_all (p : Pos) : ∀ nodes : List SvgNode, okAllAt p nodes = nodes.all (okAt p)
  | [] => by rw [okAllAt_nil, List.all_nil]
  | node :: rest => by rw [okAllAt_cons, List.all_cons, okAllAt_eq_all p rest]

/-- The test of a forest does not read its order: a fold that gathers its nodes last first
loses nothing. -/
theorem okAllAt_reverse (p : Pos) (nodes : List SvgNode) :
    okAllAt p nodes.reverse = okAllAt p nodes := by
  rw [okAllAt_eq_all, okAllAt_eq_all, List.all_reverse]

/-- A forest made by a function of a list passes when the tree of each item does. -/
theorem okAllAt_map {α : Type} (p : Pos) (f : α → SvgNode) (items : List α) :
    okAllAt p (items.map f) = items.all fun item => (f item).okAt p := by
  rw [okAllAt_eq_all, List.all_map]
  rfl

/-- A forest of several nodes for each item of a list passes when the nodes of each do. -/
theorem okAllAt_flatMap {α : Type} (p : Pos) (f : α → List SvgNode) (items : List α) :
    okAllAt p (items.flatMap f) = items.all fun item => okAllAt p (f item) := by
  simp only [okAllAt_eq_all, List.all_flatMap]

end SvgNode

/-! ## A typed SVG tree in the typed HTML tree -/

/-- A typed SVG tree as a child of an HTML position: the raw node is the tree's, and its
validity is the law of structure. The premise is one evaluation over tags and keys. -/
def Child.ofSvg {ctx : Ctx} (node : SvgNode) (h : node.okIn ctx = true := by decide +kernel) :
    Child ctx :=
  ⟨node.toRaw, SvgNode.validIn_of_okIn h⟩

/-- A typed SVG tree that passes at a position, as a document of the checker. -/
def SvgNode.toDoc {ctx : Ctx} (node : SvgNode)
    (h : node.okIn ctx = true := by decide +kernel) : Content.Doc ctx :=
  ⟨node.toRaw, SvgNode.validIn_of_okIn h⟩

end Whatwg.Html
