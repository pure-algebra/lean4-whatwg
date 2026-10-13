import Whatwg.Html.Node.Splice
import Whatwg.Html.Node.Admit
import Whatwg.Html.Content.Monotone

/-!
# Whatwg.Html.Node.Run

Owner: the children of an element with an ordered content model, written in parts (slice S22
of `docs/SVG-PACKAGE-PLAN.md`; entry W9 of `docs/research/2026-10-12-whatwg-requests.md`; debt
D139). Thirteen elements read the tags of their children in order: `html`, `head`, `hgroup`,
`dl`, `figure`, `picture`, `table`, `select`, `optgroup`, `fieldset`, `details`, `audio` and
`video`. A combinator of such an element proves its model by evaluating it over the whole child
list, and an evaluation stops at a list that is a variable. So a `dl` of rows that are data, or
a `details` whose body is data, had no typed form.

A `Run ctx t a b` is a run of children of an element of tag `t` at the position `ctx`: nodes
that are valid where they stand, and that take the element's ordered model from the state `a`
to the state `b` (`Whatwg/Html/Content/Automaton.lean`). Runs are the paths of the model's
automaton:

```
abbrev InValue : Ctx := (InMain.child .dl).child .dd

def field {a : Seq} (row : String × List (Child InValue)) :
    Run InMain .dl a (Content.Seq.next .dl (Content.Seq.next .dl a .dt) .dd) :=
  (Run.el (E.dt [E.txt row.1])).append (Run.el (E.dd row.2))

def fields : List (String × List (Child InValue)) → Element .dl InMain      -- any number of rows
  | [] => E.dl []
  | row :: rest => Element.ofRun ((field row).append (Run.loop (rest.map field)))

def folded (summary : String) (body : List (Child ((InMain.child .details).rebase .flow))) :
    Element .details InMain :=
  Element.ofRun ((Run.el (E.summary [E.txt summary])).append (Run.content .flow body))
```

The first field leads the model of `dl` from its first state to a second one, and every field
leads from the second back to it: so the first is a run and the others a loop. These are the
definitions of `WhatwgTest/Html/Runs.lean`. A child may be written in markup: `Run.el (html! …)`
takes its position from its place in the run.

- `Run.nil` is no child, and `r.append q` two runs in a row: the second starts in the state
  where the first ends. `Run.append_assoc`, `Run.nil_append` and `Run.append_nil` say that runs
  compose as paths do, and `Run.append_nodes` that the children are the two lists in a row.
- `Run.el e` is one element, `Run.text s` a text, and `Run.child c tag` any child whose tag
  shows. Each ends in `Seq.next t a tag`, a closed state.
- `Run.loop rs` is any number of runs that each lead from a state back to it. The test that
  they do, `b = a`, is closed: it is evaluated once, for a list of any length.
- `Run.content b children` is children whose tags are not known: content of the base `b`,
  typed at `(ctx.child t).rebase b`. One closed test, `Content.takes t a b`, says that the
  element's own base is wider than `b` and that every tag of `b` leaves the state `a` fixed.
- `Run.check? nodes` is raw nodes as a run between two given states, when the checker accepts
  them and the model goes from the one state to the other: for data that enters at the run.
- `Element.ofRun r` closes a run from the model's first state into an element, when the last
  state is nullable. `Element.toRun` is the way back, and `Element.ofRun_toRun` says that every
  element of such a tag is a closed run: the form loses nothing.

A state is a closed term, so each obligation is closed whatever the position `ctx` is: a
builder written once for every position owes nothing where it is used.

What this module does not claim:

- A transparent element. `audio` and `video` read their children over the base of the position
  they stand in, and a state here is over the element's own base. `Element.ofRun` asks that the
  element not be transparent. Their combinators stay.
- That a loop is found. `Run.loop` asks `b = a` of two terms. A group that leads to a state with
  the same language and another term is refused; `Run.cast` takes a proof by another route.
- Anything of the attributes of the element: `Element.ofRun` owes them as a combinator does.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag Seq Base)
open Whatwg.Html.Content (Ctx validIn validAll modelTags keep)

/-! ## Content of a base under an element -/

namespace Content

/-- The same position with another base: the exclusions and the labelled children stay. The
position of children that are content of the base `b`, whatever else their parent admits. -/
def Ctx.rebase (c : Ctx) (b : Base) : Ctx := { c with base := b }

/-- Content of the base `b` may stand among the children of `t` while its model is in the state
`s`, and leaves the state there: the element is not transparent and has no labelled children,
its own base is wider than `b`, and the state absorbs every tag of `b`. A closed test. -/
def takes (t : Tag) (s : Seq) (b : Base) : Bool :=
  !t.isTransparent && t.labelled.isEmpty && Base.under b t.ownBase && Seq.absorbs t s b.contains

/-- Content of a narrower base may stand at the position: the law of a wider base, at a
position and its `rebase`. -/
theorem validAll_of_rebase {c : Ctx} {b : Base} (h : Base.under b c.base = true)
    (nodes : List RawNode) (hvalid : validAll (c.rebase b) nodes = true) : validAll c nodes = true :=
  validAll_of_under h c.excl c.extra nodes hvalid

/-- Where the position has no labelled children, the tags of content of the base `b` are tags
of `b`. -/
theorem base_contains_of_rebase {c : Ctx} {b : Base} (hextra : c.extra = []) {nodes : List RawNode}
    (hvalid : validAll (c.rebase b) nodes = true) : ∀ tag ∈ childTags nodes, b.contains tag = true := by
  have hplain : validAll ⟨b, c.excl, []⟩ nodes = true := by
    rw [← hextra]
    exact hvalid
  exact base_contains_of_validAll hplain

/-- Every list of a list of lists is valid, so the lists in a row are. -/
theorem validAll_flatten (ctx : Ctx) : ∀ lists : List (List RawNode),
    (∀ nodes ∈ lists, validAll ctx nodes = true) → validAll ctx lists.flatten = true
  | [], _ => validAll_nil ctx
  | nodes :: rest, h => by
    rw [List.flatten_cons]
    exact validAll_append ctx nodes rest.flatten (h nodes List.mem_cons_self)
      (validAll_flatten ctx rest fun later hlater => h later (List.mem_cons_of_mem nodes hlater))

end Content

/-- The tag that an erased element counts as in an ordered model is its own. -/
theorem Element.tag?_toRaw {t : Tag} {ctx : Ctx} (e : Element t ctx) :
    Content.RawNode.tag? e.toRaw = some t := by
  obtain ⟨m, hm⟩ : ∃ m, t.markupName = some m := by
    cases hn : t.markupName with
    | none => have ht := e.htag; rw [hn] at ht; exact Bool.noConfusion ht
    | some m => exact ⟨m, rfl⟩
  have hmt : t.markupText = m := by simp only [Schema.Tag.markupText, hm, Option.getD_some]
  have hread : Content.RawNode.tag? e.toRaw =
      (Tag.ofName? t.markupText).orElse fun _ => Tag.ofForeignName? t.markupText := rfl
  rw [hread, hmt, Content.ofName?_markupName t m hm]
  rfl

/-! ## A run -/

/-- A run of children of an element of tag `t` at the position `ctx`: nodes valid at the
position of its children, which take its ordered model from the state `a` to the state `b`. -/
structure Run (ctx : Ctx) (t : Tag) (a b : Seq) where
  /-- The children, erased. -/
  nodes : List RawNode
  /-- Each may stand among the children of the element. -/
  valid : validAll (ctx.child t) nodes = true
  /-- The model's state after them, from `a`, is `b`. -/
  steps : Content.Seq.after t.ownBase.contains a (modelTags t nodes) = b

namespace Run

variable {ctx : Ctx} {t : Tag} {a b c d : Seq}

/-- Two runs with the same nodes are one run: the proofs are no part of the value. -/
theorem ext {r q : Run ctx t a b} (h : r.nodes = q.nodes) : r = q := by
  cases r
  cases q
  cases h
  rfl

/-- No child: the model stays in its state. -/
def nil : Run ctx t a a :=
  ⟨[], Content.validAll_nil _, by rw [Content.modelTags_nil]; rfl⟩

/-- Two runs in a row. The second starts in the state where the first ends. -/
def append (r : Run ctx t a b) (q : Run ctx t b c) : Run ctx t a c :=
  ⟨r.nodes ++ q.nodes, Content.validAll_append _ _ _ r.valid q.valid, by
    rw [Content.modelTags_append, Content.Seq.after_append, r.steps, q.steps]⟩

/-- The same run, with its last state written another way. -/
def cast (r : Run ctx t a b) (h : b = c := by decide) : Run ctx t a c :=
  ⟨r.nodes, r.valid, r.steps.trans h⟩

/-- One child whose tag shows: the model reads it as `tag`. -/
def child (node : Child (ctx.child t)) (tag : Tag)
    (h : Content.RawNode.tag? node.raw = some tag := by rfl) :
    Run ctx t a (Content.Seq.next t a tag) :=
  ⟨[node.raw], Content.validAll_cons _ _ _ node.valid (Content.validAll_nil _), by
    rw [Content.modelTags_singleton h]
    rfl⟩

/-- One element. Its admission is owed as `E.el` owes it. -/
def el {tag : Tag} (e : Element tag (ctx.child t))
    (h : (ctx.child t).admitsWith tag (rawAttrs e.attrs) = true := by admits) :
    Run ctx t a (Content.Seq.next t a tag) :=
  child (Child.of e h) tag e.tag?_toRaw

/-- A text run, which a model reads as the tag `pcdata`. -/
def text (s : String) (h : (ctx.child t).admits .pcdata = true := by admits) :
    Run ctx t a (Content.Seq.next t a .pcdata) :=
  child (Child.text s h) .pcdata rfl

/-- Any number of runs that each lead from the state `a` back to it. The runs may end in a
state `b` written another way: the test `b = a` is closed, and one evaluation answers for a
list of any length. -/
def loop (runs : List (Run ctx t a b)) (h : b = a := by decide) : Run ctx t a a :=
  ⟨(runs.map Run.nodes).flatten,
    Content.validAll_flatten _ _ fun nodes hnodes => by
      obtain ⟨r, _, hr⟩ := List.mem_map.mp hnodes
      rw [← hr]
      exact r.valid,
    by
      rw [Content.modelTags_flatten]
      refine Content.Seq.after_flatten_of_fixed fun word hword => ?_
      obtain ⟨nodes, hnodes, hw⟩ := List.mem_map.mp hword
      obtain ⟨r, _, hr⟩ := List.mem_map.mp hnodes
      rw [← hw, ← hr, r.steps]
      exact h⟩

/-- Children whose tags are not known: content of the base `b`, typed at the position of the
element's children with that base. The model stays in its state. The test is closed. -/
def content (b : Base) (children : List (Child ((ctx.child t).rebase b)))
    (h : Content.takes t a b = true := by decide) : Run ctx t a a :=
  have hparts : ((t.isTransparent = false ∧ t.labelled.isEmpty = true) ∧
      Content.Base.under b t.ownBase = true) ∧ Content.Seq.absorbs t a b.contains = true := by
    simpa only [Content.takes, Bool.and_eq_true, Bool.not_eq_true'] using h
  have hextra : (ctx.child t).extra = [] := List.isEmpty_iff.mp hparts.1.1.2
  have hunder : Content.Base.under b (ctx.child t).base = true := by
    rw [Content.Ctx.child_base_of_not_transparent ctx hparts.1.1.1]
    exact hparts.1.2
  ⟨children.map Child.raw,
    Content.validAll_of_rebase hunder _ (validAll_children children),
    Content.Seq.after_keep_of_absorbs hparts.2
      (Content.base_contains_of_rebase hextra (validAll_children children))⟩

/-- Raw nodes as a run from the state `a` to the state `b`, when the checker accepts each
where the children stand and the model goes from `a` to `b` over them. -/
def check? (nodes : List RawNode) : Option (Run ctx t a b) :=
  if h : validAll (ctx.child t) nodes = true ∧
      Content.Seq.after t.ownBase.contains a (modelTags t nodes) = b then
    some ⟨nodes, h.1, h.2⟩
  else none

/-! ### Runs compose as paths -/

theorem nil_nodes : (nil : Run ctx t a a).nodes = [] := rfl

/-- The children of two runs in a row are the two lists in a row. -/
theorem append_nodes (r : Run ctx t a b) (q : Run ctx t b c) :
    (r.append q).nodes = r.nodes ++ q.nodes := rfl

theorem nil_append (r : Run ctx t a b) : nil.append r = r := ext rfl

theorem append_nil (r : Run ctx t a b) : r.append nil = r := ext (List.append_nil _)

theorem append_assoc (r : Run ctx t a b) (q : Run ctx t b c) (s : Run ctx t c d) :
    (r.append q).append s = r.append (q.append s) :=
  ext (List.append_assoc _ _ _)

theorem cast_nodes (r : Run ctx t a b) (h : b = c) : (r.cast h).nodes = r.nodes := rfl

theorem child_nodes (node : Child (ctx.child t)) (tag : Tag)
    (h : Content.RawNode.tag? node.raw = some tag) :
    (child (a := a) node tag h).nodes = [node.raw] := rfl

/-- The one child of `Run.el` is the erased element. -/
theorem el_nodes {tag : Tag} (e : Element tag (ctx.child t))
    (h : (ctx.child t).admitsWith tag (rawAttrs e.attrs) = true) :
    (el (a := a) e h).nodes = [e.toRaw] := rfl

theorem text_nodes (s : String) (h : (ctx.child t).admits .pcdata = true) :
    (text (ctx := ctx) (t := t) (a := a) s h).nodes = [RawNode.text s] := rfl

/-- The children of a loop are those of its runs, in a row. -/
theorem loop_nodes (runs : List (Run ctx t a b)) (h : b = a) :
    (loop runs h).nodes = (runs.map Run.nodes).flatten := rfl

/-- A loop of no run is no child, and a loop goes on with one more run. -/
theorem loop_nil (h : b = a) : loop ([] : List (Run ctx t a b)) h = nil := ext rfl

theorem loop_cons (r : Run ctx t a b) (runs : List (Run ctx t a b)) (h : b = a) :
    loop (r :: runs) h = (r.cast h).append (loop runs h) :=
  ext rfl

/-- The children of a run of content are the nodes of the children given. -/
theorem content_nodes (b : Base) (children : List (Child ((ctx.child t).rebase b)))
    (h : Content.takes t a b = true) :
    (content b children h).nodes = children.map Child.raw := rfl

/-- The run that `check?` answers holds the nodes given, and every run over those nodes is
the answer. -/
theorem check?_eq_some_iff {nodes : List RawNode} {r : Run ctx t a b} :
    check? nodes = some r ↔ r.nodes = nodes := by
  unfold check?
  constructor
  · intro h
    split at h
    · cases Option.some.inj h
      rfl
    · exact nomatch h
  · intro h
    subst h
    rw [dif_pos (And.intro r.valid r.steps)]

/-- `check?` answers exactly when the checker accepts the nodes and the model goes from the
one state to the other. -/
theorem isSome_check? (nodes : List RawNode) :
    (check? (ctx := ctx) (t := t) (a := a) (b := b) nodes).isSome = true ↔
      validAll (ctx.child t) nodes = true ∧
        Content.Seq.after t.ownBase.contains a (modelTags t nodes) = b := by
  unfold check?
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hsome => Bool.noConfusion hsome, fun hboth => absurd hboth h⟩

end Run

/-! ## An element from a run -/

/-- **An element whose children are a run** from the first state of its ordered model to a
state that is nullable. The attributes are owed as a combinator owes them; the three other
obligations are closed tests of the tag and of the last state. -/
def Element.ofRun {t : Tag} {ctx : Ctx} {b : Seq} (r : Run ctx t (Content.Seq.start t) b)
    (attrs : List AttrVal := [])
    (hattrs : Content.attrsOk t (rawAttrs attrs) = true := by admits)
    (hend : Content.Seq.nullable b = true := by decide)
    (hopaque : t.isTransparent = false := by decide)
    (ht : t.markupName.isSome = true := by decide) : Element t ctx :=
  ⟨attrs, r.nodes, hattrs,
    Content.seqOk_of_after _ t r.nodes (by
      rw [Content.Ctx.child_base_of_not_transparent ctx hopaque, r.steps]
      exact hend),
    r.valid, ht⟩

/-- The children of an element made of a run are the run's nodes. -/
theorem Element.ofRun_children {t : Tag} {ctx : Ctx} {b : Seq}
    (r : Run ctx t (Content.Seq.start t) b) (attrs : List AttrVal)
    (hattrs : Content.attrsOk t (rawAttrs attrs) = true) (hend : Content.Seq.nullable b = true)
    (hopaque : t.isTransparent = false) (ht : t.markupName.isSome = true) :
    (Element.ofRun r attrs hattrs hend hopaque ht).children = r.nodes := rfl

theorem Element.ofRun_toRaw {t : Tag} {ctx : Ctx} {b : Seq}
    (r : Run ctx t (Content.Seq.start t) b) (attrs : List AttrVal)
    (hattrs : Content.attrsOk t (rawAttrs attrs) = true) (hend : Content.Seq.nullable b = true)
    (hopaque : t.isTransparent = false) (ht : t.markupName.isSome = true) :
    (Element.ofRun r attrs hattrs hend hopaque ht).toRaw =
      .element t.markupText (rawAttrs attrs) r.nodes := rfl

/-- The children of an element, as a run from the first state of its model. -/
def Element.toRun {t : Tag} {ctx : Ctx} (e : Element t ctx) :
    Run ctx t (Content.Seq.start t)
      (Content.Seq.after t.ownBase.contains (Content.Seq.start t) (modelTags t e.children)) :=
  ⟨e.children, e.hchildren, rfl⟩

/-- The run of an element with an ordered model ends in a nullable state. -/
theorem Element.nullable_toRun {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (hseq : t.seq?.isSome = true) (hopaque : t.isTransparent = false) :
    Content.Seq.nullable
      (Content.Seq.after t.ownBase.contains (Content.Seq.start t) (modelTags t e.children)) = true := by
  have h := Content.after_of_seqOk hseq e.hseq
  rw [Content.Ctx.child_base_of_not_transparent ctx hopaque] at h
  exact h

/-- **Every element is its run, closed.** The form of `Element.ofRun` loses nothing. -/
theorem Element.ofRun_toRun {t : Tag} {ctx : Ctx} (e : Element t ctx)
    (hend : Content.Seq.nullable
      (Content.Seq.after t.ownBase.contains (Content.Seq.start t) (modelTags t e.children)) = true)
    (hopaque : t.isTransparent = false) :
    Element.ofRun e.toRun e.attrs e.hattrs hend hopaque e.htag = e := by
  cases e
  rfl

end Whatwg.Html
