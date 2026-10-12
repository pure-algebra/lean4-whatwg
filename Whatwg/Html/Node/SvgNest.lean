import Whatwg.Html.Node.SvgBuild

/-!
# Whatwg.Html.Node.SvgNest

Owner: the structure proofs that every writer of pictures would otherwise write for itself
(slice S10 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-48).

**A flat list of calls as a forest.** A drawing device is called in order: a mark, the start
of a group, more marks, the end of the group. In a tree the group holds its children.
`SvgNode.nest` makes the forest of such a list. `wrap` says what a group is: the nodes that
stand for a label and the marks drawn inside it, such as a clip path and the group it clips.
An end with no open group is dropped, and a group with no end is closed at the end of the
list, so the forest of every list is balanced.

`SvgNode.okAllAt_nest` is the theorem: the forest passes the structure test at a position when
each mark passes there and `wrap` keeps a passing list passing. A writer proves its marks one
by one and its wrapper once, and has the structure of every list of calls.

**A clipped group.** `Svg.okAllAt_clipped` says that `Svg.clipped` passes among the marks when
its clip path does and the children do.

**Attributes that are sometimes written.** `SvgAttr.allOk_of_sublist` says that an attribute
list which passes still passes with attributes left out, and `SvgAttr.allOk_of_keys_eq` that
the test reads the keys alone. So a writer with optional attributes proves the full list once,
by one evaluation, and has every choice of them.

What this module does not claim: anything about what a group draws. The test is the structure
test of `Whatwg/Html/Node/SvgValid.lean`.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Html.Content (Pos)

/-! ## Attributes that are sometimes written -/

namespace SvgAttr

variable {t : Tag}

/-- The test of an attribute list reads its keys alone: two lists with the same keys, in
order, pass together. -/
theorem allOk_of_keys_eq {a b : List (SvgAttr t)} (h : a.map key = b.map key)
    (hb : allOk b = true) : allOk a = true := by
  rw [allOk_iff] at hb ⊢
  refine ⟨fun p hp => ?_, h ▸ hb.2⟩
  have hk : p.key ∈ b.map key := h ▸ List.mem_map_of_mem hp
  obtain ⟨q, hq, hqk⟩ := List.mem_map.mp hk
  rw [← hqk]
  exact hb.1 q hq

/-- An attribute list that passes still passes with some of its attributes left out. -/
theorem allOk_of_sublist {a b : List (SvgAttr t)} (h : a.Sublist b) (hb : allOk b = true) :
    allOk a = true := by
  rw [allOk_iff] at hb ⊢
  exact ⟨fun p hp => hb.1 p (h.subset hp), (h.map key).nodup hb.2⟩

end SvgAttr

/-! ## A clipped group -/

/-- A clip path and the group it clips pass among the marks when the clip path passes and the
children do. -/
theorem Svg.okAllAt_clipped (x : Exclusions) (id : String) (clip children : List SvgNode)
    (hclip : (Svg.clipPath id clip).okAt (Pos.inSvg x) = true)
    (hc : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    SvgNode.okAllAt (Pos.inSvg x) (Svg.clipped id clip children) = true := by
  rw [Svg.clipped, SvgNode.okAllAt_cons, SvgNode.okAllAt_cons, SvgNode.okAllAt_nil, hclip,
    Svg.okAt_g, hc]
  conv => lhs; whnf

/-! ## A flat list of calls as a forest -/

namespace SvgNode

/-- One call of a flat drawing: a mark, the start of a group with its label, or the end of the
innermost open group. -/
inductive Flat (α : Type) where
  /-- A mark. -/
  | leaf (node : SvgNode)
  /-- The start of a group. -/
  | enter (label : α)
  /-- The end of the innermost open group. -/
  | leave

/-- The state of the fold: the marks at the depth of the innermost open group, last first,
and the open groups, innermost first, each with the marks that stood before it, last
first. -/
structure Nesting (α : Type) where
  marks : List SvgNode
  opened : List (α × List SvgNode)

variable {α : Type}

/-- Close a group around the marks drawn inside it. The result is last first. -/
def closeGroup (wrap : α → List SvgNode → List SvgNode) (o : α × List SvgNode)
    (inner : List SvgNode) : List SvgNode :=
  (wrap o.1 inner.reverse).reverse ++ o.2

/-- One call. An end with no open group is dropped. -/
def Nesting.step (wrap : α → List SvgNode → List SvgNode) (s : Nesting α) : Flat α → Nesting α
  | .leaf node => ⟨node :: s.marks, s.opened⟩
  | .enter label => ⟨[], (label, s.marks) :: s.opened⟩
  | .leave =>
    match s.opened with
    | [] => s
    | o :: rest => ⟨closeGroup wrap o s.marks, rest⟩

/-- Close every group that is still open. -/
def Nesting.finish (wrap : α → List SvgNode → List SvgNode) :
    List (α × List SvgNode) → List SvgNode → List SvgNode
  | [], marks => marks
  | o :: rest, marks => finish wrap rest (closeGroup wrap o marks)

/-- The marks of a state with every open group closed, in order. -/
def Nesting.result (wrap : α → List SvgNode → List SvgNode) (s : Nesting α) : List SvgNode :=
  (Nesting.finish wrap s.opened s.marks).reverse

/-- The forest of a flat list of calls, in order. `wrap` gives the nodes of a group from its
label and the marks drawn inside it. -/
def nest (wrap : α → List SvgNode → List SvgNode) (calls : List (Flat α)) : List SvgNode :=
  (calls.foldl (Nesting.step wrap) ⟨[], []⟩).result wrap

/-- The test of one call: a mark passes, and a start or an end has nothing to pass. -/
def Flat.okAt (p : Pos) : Flat α → Bool
  | .leaf node => node.okAt p
  | _ => true

/-- The invariant of the fold: the marks pass, and so do the marks before each open group. -/
def Nesting.Ok (p : Pos) (s : Nesting α) : Prop :=
  okAllAt p s.marks = true ∧ ∀ o ∈ s.opened, okAllAt p o.2 = true

theorem closeGroup_ok (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true)
    (o : α × List SvgNode) (inner : List SvgNode) (hi : okAllAt p inner = true)
    (ho : okAllAt p o.2 = true) : okAllAt p (closeGroup wrap o inner) = true := by
  rw [closeGroup, okAllAt_append, okAllAt_reverse,
    hw o.1 inner.reverse ((okAllAt_reverse p inner).trans hi), ho]
  rfl

/-- Each call keeps the invariant, when a mark passes. -/
theorem Nesting.step_ok (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true)
    (s : Nesting α) (c : Flat α) (hc : ∀ node, c = .leaf node → node.okAt p = true)
    (h : s.Ok p) : (s.step wrap c).Ok p := by
  cases c with
  | leaf node =>
    refine ⟨?_, h.2⟩
    show okAllAt p (node :: s.marks) = true
    rw [okAllAt_cons, hc node rfl, h.1]
    rfl
  | enter label =>
    refine ⟨okAllAt_nil p, fun o ho => ?_⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · exact h.1
    · exact h.2 o ho
  | leave =>
    obtain ⟨marks, opened⟩ := s
    cases opened with
    | nil => exact h
    | cons o rest =>
      exact ⟨closeGroup_ok p wrap hw o marks h.1 (h.2 o List.mem_cons_self),
        fun o' ho' => h.2 o' (List.mem_cons_of_mem _ ho')⟩

theorem Nesting.foldl_ok (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true) :
    ∀ (calls : List (Flat α)) (s : Nesting α),
      (∀ node, Flat.leaf node ∈ calls → node.okAt p = true) → s.Ok p →
      (calls.foldl (Nesting.step wrap) s).Ok p
  | [], _, _, h => h
  | c :: rest, s, hl, h =>
    foldl_ok p wrap hw rest _ (fun node hn => hl node (List.mem_cons_of_mem _ hn))
      (step_ok p wrap hw s c (fun node hn => hl node (hn ▸ List.mem_cons_self)) h)

theorem Nesting.finish_ok (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true) :
    ∀ (opened : List (α × List SvgNode)) (marks : List SvgNode),
      okAllAt p marks = true → (∀ o ∈ opened, okAllAt p o.2 = true) →
      okAllAt p (finish wrap opened marks) = true
  | [], _, h, _ => h
  | o :: rest, marks, h, hs =>
    finish_ok p wrap hw rest _ (closeGroup_ok p wrap hw o marks h (hs o List.mem_cons_self))
      (fun o' ho' => hs o' (List.mem_cons_of_mem _ ho'))

/-- The forest of every flat list of calls passes at a position, balanced or not, when each
mark passes there and the wrapper keeps a passing list passing. -/
theorem okAllAt_nest (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true)
    (calls : List (Flat α)) (hl : ∀ node, Flat.leaf node ∈ calls → node.okAt p = true) :
    okAllAt p (nest wrap calls) = true := by
  have h := Nesting.foldl_ok p wrap hw calls ⟨[], []⟩ hl ⟨okAllAt_nil p, fun _ ho => nomatch ho⟩
  rw [nest, Nesting.result, okAllAt_reverse]
  exact Nesting.finish_ok p wrap hw _ _ h.1 h.2

/-- The same for a list of calls of any type that is read as a mark, a start or an end: the
forest passes when each call that is a mark gives one that passes. -/
theorem okAllAt_nest_map {β : Type} (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true) (f : β → Flat α)
    (items : List β) (hf : ∀ item node, f item = .leaf node → node.okAt p = true) :
    okAllAt p (nest wrap (items.map f)) = true :=
  okAllAt_nest p wrap hw _ fun node hn => by
    obtain ⟨item, _, h⟩ := List.mem_map.mp hn
    exact hf item node h

/-- The same, with the premise as one test of each call: `Flat.okAt` is true of a start and of
an end, so a writer proves it by one case split on its own calls. -/
theorem okAllAt_nest_of_calls {β : Type} (p : Pos) (wrap : α → List SvgNode → List SvgNode)
    (hw : ∀ a kids, okAllAt p kids = true → okAllAt p (wrap a kids) = true) (f : β → Flat α)
    (items : List β) (hf : ∀ item, (f item).okAt p = true) :
    okAllAt p (nest wrap (items.map f)) = true :=
  okAllAt_nest_map p wrap hw f items fun item node h => by
    have hitem := hf item
    rw [h] at hitem
    exact hitem

/-- A list with no group is its marks. -/
theorem nest_leaves (wrap : α → List SvgNode → List SvgNode) (nodes : List SvgNode) :
    nest wrap (nodes.map Flat.leaf) = nodes := by
  have key : ∀ (rest : List SvgNode) (s : Nesting α),
      (rest.map Flat.leaf).foldl (Nesting.step wrap) s = ⟨rest.reverse ++ s.marks, s.opened⟩ := by
    intro rest
    induction rest with
    | nil => intro s; rfl
    | cons node rest ih =>
      intro s
      rw [List.map_cons, List.foldl_cons, ih, List.reverse_cons, List.append_assoc]
      rfl
  rw [nest, key nodes ⟨[], []⟩]
  show (nodes.reverse ++ []).reverse = nodes
  rw [List.append_nil, List.reverse_reverse]

end SvgNode

end Whatwg.Html
