import Whatwg.Html.Node.Typed
import Whatwg.Html.Content.Explain

/-!
# Whatwg.Html.Node.Check

Owner: the admission of a raw tree into the typed tree by the checker's own verdict (slice S17
of `docs/SVG-PACKAGE-PLAN.md`; entry W1 of `docs/research/2026-10-12-whatwg-requests.md`).

The typed tree of `Whatwg/Html/Node/Typed.lean` is built from parts whose validity is known
when a source file is compiled. A page also holds content that is data: a fold of a document,
a table of rows, a picture of a run. Such a tree is known only when the program runs. This
module admits it then, once: `validIn` is a Boolean, so a raw node that passes is a `Child`
with its proof, and from there on it is a part of the typed tree like any other.

```
def page (title : String) (content : List (Child mainCtx)) : Element .html Ctx.document := …
  -- the shell: written once, valid by construction

match Child.acceptAll (fold document) with      -- the data: checked once, where it enters
| .ok content => (page title content).renderDoc
| .error words => …                              -- `/section#intro/p[2]/div: <div> is not admitted here: …`
```

- `Child.check?` answers the child, or nothing. `Child.check` answers the child, or the located
  refusal that `Content.explain` gives. `Child.accept` answers the child, or that refusal in
  words (`Refusal.describeIn`).
- `Child.checkAll?`, `Child.checkAll` and `Child.acceptAll` do the same for a list of trees
  that stand at one position: every child, or the first refusal with its place in the list.
- `Ctx.below` names the position of the children of an element by the elements above it:
  `Ctx.document.below [.html, .body, .main]`.

What the laws give. A child that `check?` answers holds the node given, and `check?` answers
exactly when the checker accepts (`check?_eq_some_iff`, `isSome_check?`). The three forms
agree: `check` succeeds exactly when `check?` does, with the same child (`toOption_check`), and
its error is `explain`'s refusal (`check_eq_error_iff`). For a list, the raw nodes of the
children are the nodes given (`checkAll?_eq_some_iff`), so an element built from them with
`Element.ofChildren` or a combinator holds those nodes as its children; the list is the one
that `mapM` makes of `check?` (`checkAll?_eq_mapM`); and the error of `checkAll` is the refusal
of the first tree that the checker refuses (`checkAll_eq_error_iff`).

Where a checked list may go with no further proof. An element with no ordered model owes
nothing for its children (`Content.elementOk_of_seq_none`), so a combinator such as `E.main`
or `E.ul` takes a list that is a variable. An element with an ordered model (`html`, `head`,
`dl`, `figure`, `table`, `details` and seven more) reads the tags of its children, which a
`Child` does not show: there the whole element is checked as one raw node.

What this module does not claim: anything about a tree beyond the checker's verdict. A rule of
a whole page, such as an `id` that stands once, is not the content model's.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag)
open Whatwg.Html.Content (Ctx validIn validAll Refusal ListRefusal explain)

/-- The position of the children of the last element of a path of elements that starts at a
position: `Ctx.document.below [.html, .body, .main]` is where the children of `main` stand in
a page. -/
def Content.Ctx.below (c : Ctx) (path : List Tag) : Ctx := path.foldl Ctx.child c

theorem Content.Ctx.below_nil (c : Ctx) : c.below [] = c := rfl

/-- A path is walked one element at a time: `below` is the chain of `Ctx.child` that a position
written by hand is. -/
theorem Content.Ctx.below_cons (c : Ctx) (t : Tag) (path : List Tag) :
    c.below (t :: path) = (c.child t).below path := rfl

namespace Child

variable {ctx : Ctx}

/-- Two children with one raw node are one child: the proof is no part of the value. -/
theorem ext {a b : Child ctx} (h : a.raw = b.raw) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-! ## One tree -/

/-- A raw node as a child of the position, when the checker accepts it there. -/
def check? (node : RawNode) : Option (Child ctx) :=
  if h : validIn ctx node = true then some ⟨node, h⟩ else none

/-- The child that `check?` answers holds the node given, and every child of that node is the
answer. -/
theorem check?_eq_some_iff {node : RawNode} {c : Child ctx} :
    check? node = some c ↔ c.raw = node := by
  unfold check?
  constructor
  · intro h
    split at h
    · cases Option.some.inj h
      rfl
    · exact nomatch h
  · intro h
    subst h
    rw [dif_pos c.valid]

/-- A child checks back to itself. -/
theorem check?_raw (c : Child ctx) : check? c.raw = some c := check?_eq_some_iff.mpr rfl

/-- `check?` answers exactly when the checker accepts. -/
theorem isSome_check? (ctx : Ctx) (node : RawNode) :
    (check? (ctx := ctx) node).isSome = validIn ctx node := by
  unfold check?
  split
  · next h => rw [h]; rfl
  · next h => exact (Bool.eq_false_iff.mpr h).symm

theorem check?_eq_none_iff {node : RawNode} :
    check? (ctx := ctx) node = none ↔ validIn ctx node = false := by
  unfold check?
  split
  · next h => exact ⟨nofun, fun hf => absurd (h.symm.trans hf) Bool.noConfusion⟩
  · next h => exact ⟨fun _ => Bool.eq_false_iff.mpr h, fun _ => rfl⟩

/-- A raw node as a child of the position, or the located refusal of the checker: the node it
refuses first, and why. One walk of the tree answers either. -/
def check (node : RawNode) : Except Refusal (Child ctx) :=
  match h : explain ctx node with
  | none => .ok ⟨node, (Content.explain_none_iff ctx node).mp h⟩
  | some refusal => .error refusal

/-- The error of `check` is the refusal that `Content.explain` gives. -/
theorem check_eq_error_iff {node : RawNode} {r : Refusal} :
    check (ctx := ctx) node = .error r ↔ explain ctx node = some r := by
  unfold check
  split
  · next h => exact ⟨nofun, fun hr => nomatch h.symm.trans hr⟩
  · next refusal h =>
    exact ⟨fun hr => h.trans (congrArg some (Except.error.inj hr)),
      fun hr => congrArg _ (Option.some.inj (h.symm.trans hr))⟩

/-- The child that `check` answers holds the node given, and every child of that node is the
answer. -/
theorem check_eq_ok_iff {node : RawNode} {c : Child ctx} : check node = .ok c ↔ c.raw = node := by
  constructor
  · intro h
    unfold check at h
    split at h
    · cases Except.ok.inj h
      rfl
    · exact nomatch h
  · intro h
    subst h
    cases hc : check (ctx := ctx) c.raw with
    | ok d =>
      unfold check at hc
      split at hc
      · cases Except.ok.inj hc
        rfl
      · exact nomatch hc
    | error r =>
      have hnone := (Content.explain_none_iff ctx c.raw).mpr c.valid
      rw [check_eq_error_iff.mp hc] at hnone
      exact nomatch hnone

/-- `check` succeeds exactly when `check?` does, and with the same child. -/
theorem toOption_check (ctx : Ctx) (node : RawNode) :
    (check (ctx := ctx) node).toOption = check? node := by
  cases hc : check (ctx := ctx) node with
  | ok c =>
    have hraw := check_eq_ok_iff.mp hc
    subst hraw
    rw [check?_raw]
    rfl
  | error r =>
    cases hv : validIn ctx node with
    | false => exact (check?_eq_none_iff.mpr hv).symm
    | true =>
      have hok := (check_eq_ok_iff (c := ⟨node, hv⟩)).mpr rfl
      rw [hc] at hok
      exact nomatch hok

/-- A raw node as a child of the position, or its refusal in words, with the names along its
path: what a program that writes a page reports. -/
def accept (node : RawNode) : Except String (Child ctx) :=
  match check node with
  | .ok c => .ok c
  | .error refusal => .error (refusal.describeIn ctx node)

/-- `accept` succeeds exactly when `check` does, and with the same child. -/
theorem accept_eq_ok_iff {node : RawNode} {c : Child ctx} : accept node = .ok c ↔ c.raw = node := by
  rw [← check_eq_ok_iff, accept]
  cases check (ctx := ctx) node with
  | ok d => exact ⟨fun h => congrArg _ (Except.ok.inj h), fun h => congrArg _ (Except.ok.inj h)⟩
  | error r => exact ⟨nofun, nofun⟩

/-! ## A list of trees at one position -/

/-- Every node of a list as a child of the position: all of them, or nothing. -/
def checkAll? : List RawNode → Option (List (Child ctx))
  | [] => some []
  | node :: rest =>
    match check? node with
    | none => none
    | some c => (checkAll? rest).map (c :: ·)

/-- The children that `checkAll?` answers hold the nodes given, in order. So an element built
from them holds those nodes as its children: `Element.ofChildren cs attrs h` has the children
`cs.map Child.raw`. -/
theorem checkAll?_eq_some_iff : ∀ {nodes : List RawNode} {cs : List (Child ctx)},
    checkAll? nodes = some cs ↔ cs.map Child.raw = nodes
  | [], cs => by
    rw [checkAll?]
    constructor
    · intro h
      cases Option.some.inj h
      rfl
    · intro h
      cases cs with
      | nil => rfl
      | cons c rest => exact nomatch h
  | node :: rest, cs => by
    rw [checkAll?]
    cases hc : check? (ctx := ctx) node with
    | none =>
      refine ⟨nofun, fun h => ?_⟩
      cases cs with
      | nil => exact nomatch h
      | cons c others =>
        rw [check?_eq_some_iff.mpr (List.cons.inj h).1] at hc
        exact nomatch hc
    | some c =>
      have hraw : c.raw = node := check?_eq_some_iff.mp hc
      constructor
      · intro h
        cases hrest : checkAll? (ctx := ctx) rest with
        | none => rw [hrest] at h; exact nomatch h
        | some others =>
          rw [hrest] at h
          cases Option.some.inj h
          rw [List.map_cons, hraw, checkAll?_eq_some_iff.mp hrest]
      · intro h
        cases cs with
        | nil => exact nomatch h
        | cons d others =>
          rw [checkAll?_eq_some_iff.mpr (List.cons.inj h).2,
            ext (hraw.trans (List.cons.inj h).1.symm)]
          rfl

/-- `checkAll?` is `check?` at each node, in order: the list that `mapM` makes. -/
theorem checkAll?_eq_mapM (nodes : List RawNode) :
    checkAll? (ctx := ctx) nodes = nodes.mapM check? := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    rw [checkAll?, List.mapM_cons, ih]
    cases check? (ctx := ctx) node with
    | none => rfl
    | some c => cases List.mapM (check? (ctx := ctx)) rest <;> rfl

/-- A list of children checks back to itself. -/
theorem checkAll?_map_raw (cs : List (Child ctx)) : checkAll? (cs.map Child.raw) = some cs :=
  checkAll?_eq_some_iff.mpr rfl

/-- `checkAll?` answers exactly when the checker accepts every node. -/
theorem isSome_checkAll? (ctx : Ctx) : ∀ nodes : List RawNode,
    (checkAll? (ctx := ctx) nodes).isSome = validAll ctx nodes
  | [] => by rw [checkAll?, Content.validAll_nil]; rfl
  | node :: rest => by
    have hcons : validAll ctx (node :: rest) = (validIn ctx node && validAll ctx rest) :=
      Content.validAllAt_cons _ node rest
    rw [checkAll?, hcons, ← isSome_check? ctx node, ← isSome_checkAll? ctx rest]
    cases check? (ctx := ctx) node with
    | none => rfl
    | some c => cases checkAll? (ctx := ctx) rest <;> rfl

/-- `checkAll`, with the place in the whole list of the first node of this one. -/
def checkAllFrom (start : Nat) : List RawNode → Except ListRefusal (List (Child ctx))
  | [] => .ok []
  | node :: rest =>
    match check node with
    | .error refusal => .error ⟨start, refusal⟩
    | .ok c =>
      match checkAllFrom (start + 1) rest with
      | .error e => .error e
      | .ok cs => .ok (c :: cs)

/-- Every node of a list as a child of the position, or the refusal of the first node that
the checker refuses, with its place in the list. -/
def checkAll (nodes : List RawNode) : Except ListRefusal (List (Child ctx)) := checkAllFrom 0 nodes

theorem toOption_checkAllFrom (ctx : Ctx) : ∀ (nodes : List RawNode) (start : Nat),
    (checkAllFrom (ctx := ctx) start nodes).toOption = checkAll? nodes
  | [], _ => rfl
  | node :: rest, start => by
    rw [checkAllFrom, checkAll?, ← toOption_check ctx node, ← toOption_checkAllFrom ctx rest (start + 1)]
    cases check (ctx := ctx) node with
    | error r => rfl
    | ok c => cases checkAllFrom (ctx := ctx) (start + 1) rest <;> rfl

/-- `checkAll` succeeds exactly when `checkAll?` does, and with the same children. -/
theorem toOption_checkAll (ctx : Ctx) (nodes : List RawNode) :
    (checkAll (ctx := ctx) nodes).toOption = checkAll? nodes :=
  toOption_checkAllFrom ctx nodes 0

/-- The children that `checkAll` answers hold the nodes given, in order. -/
theorem checkAll_eq_ok_iff {nodes : List RawNode} {cs : List (Child ctx)} :
    checkAll nodes = .ok cs ↔ cs.map Child.raw = nodes := by
  rw [← checkAll?_eq_some_iff, ← toOption_checkAll]
  cases checkAll (ctx := ctx) nodes with
  | ok ds => exact ⟨fun h => congrArg _ (Except.ok.inj h), fun h => congrArg _ (Option.some.inj h)⟩
  | error e => exact ⟨nofun, nofun⟩

theorem checkAllFrom_eq_error_iff : ∀ (nodes : List RawNode) (start : Nat) (e : ListRefusal),
    checkAllFrom (ctx := ctx) start nodes = .error e ↔
      ∃ (offset : Nat) (node : RawNode), e.index = start + offset ∧
        validAll ctx (nodes.take offset) = true ∧ nodes[offset]? = some node ∧
        explain ctx node = some e.refusal
  | [], start, e => by
    rw [checkAllFrom]
    refine ⟨nofun, fun ⟨offset, _, _, _, h, _⟩ => ?_⟩
    rw [List.getElem?_nil] at h
    exact nomatch h
  | node :: rest, start, e => by
    rw [checkAllFrom]
    cases hc : check (ctx := ctx) node with
    | error refusal =>
      have hexplain := check_eq_error_iff.mp hc
      constructor
      · intro h
        cases Except.error.inj h
        exact ⟨0, node, rfl, Content.validAll_nil ctx, rfl, hexplain⟩
      · intro ⟨offset, found, hindex, hbefore, hfound, hwhy⟩
        cases offset with
        | zero =>
          cases Option.some.inj hfound
          rw [hexplain] at hwhy
          cases e
          cases Option.some.inj hwhy
          cases hindex
          rfl
        | succ offset =>
          have hvalid := ((Content.validAll_cons_iff ctx node _).mp hbefore).1
          rw [(Content.explain_none_iff ctx node).mpr hvalid] at hexplain
          exact nomatch hexplain
    | ok c =>
      have hraw : c.raw = node := check_eq_ok_iff.mp hc
      have hvalid : validIn ctx node = true := hraw ▸ c.valid
      have ih := checkAllFrom_eq_error_iff rest (start + 1) e
      cases hrest : checkAllFrom (ctx := ctx) (start + 1) rest with
      | ok cs =>
        rw [hrest] at ih
        refine ⟨nofun, fun ⟨offset, found, hindex, hbefore, hfound, hwhy⟩ => ?_⟩
        cases offset with
        | zero =>
          cases Option.some.inj hfound
          rw [(Content.explain_none_iff ctx node).mpr hvalid] at hwhy
          exact nomatch hwhy
        | succ offset =>
          exact nomatch ih.mpr ⟨offset, found, by rw [hindex]; omega,
            ((Content.validAll_cons_iff ctx node _).mp hbefore).2, hfound, hwhy⟩
      | error first =>
        rw [hrest] at ih
        constructor
        · intro h
          cases Except.error.inj h
          obtain ⟨offset, found, hindex, hbefore, hfound, hwhy⟩ := ih.mp rfl
          exact ⟨offset + 1, found, by rw [hindex]; omega,
            Content.validAll_cons ctx node _ hvalid hbefore, hfound, hwhy⟩
        · intro ⟨offset, found, hindex, hbefore, hfound, hwhy⟩
          cases offset with
          | zero =>
            cases Option.some.inj hfound
            rw [(Content.explain_none_iff ctx node).mpr hvalid] at hwhy
            exact nomatch hwhy
          | succ offset =>
            exact ih.mpr ⟨offset, found, by rw [hindex]; omega,
              ((Content.validAll_cons_iff ctx node _).mp hbefore).2, hfound, hwhy⟩

/-- The error of `checkAll` is the first refusal of the list: every node before its place is
one the checker accepts, and its refusal is `Content.explain`'s of the node at its place. -/
theorem checkAll_eq_error_iff {nodes : List RawNode} {e : ListRefusal} :
    checkAll (ctx := ctx) nodes = .error e ↔
      validAll ctx (nodes.take e.index) = true ∧
        ∃ node, nodes[e.index]? = some node ∧ explain ctx node = some e.refusal := by
  rw [checkAll, checkAllFrom_eq_error_iff]
  constructor
  · intro ⟨offset, node, hindex, hbefore, hnode, hwhy⟩
    rw [Nat.zero_add] at hindex
    subst hindex
    exact ⟨hbefore, node, hnode, hwhy⟩
  · intro ⟨hbefore, node, hnode, hwhy⟩
    exact ⟨e.index, node, (Nat.zero_add _).symm, hbefore, hnode, hwhy⟩

/-- Every node of a list as a child of the position, or the first refusal in words: the names
from the refused tree of the list down to the refused node, and the reason. -/
def acceptAll (nodes : List RawNode) : Except String (List (Child ctx)) :=
  match checkAll nodes with
  | .ok cs => .ok cs
  | .error e => .error (e.describeIn ctx nodes)

/-- `acceptAll` succeeds exactly when `checkAll` does, and with the same children. -/
theorem acceptAll_eq_ok_iff {nodes : List RawNode} {cs : List (Child ctx)} :
    acceptAll nodes = .ok cs ↔ cs.map Child.raw = nodes := by
  rw [← checkAll_eq_ok_iff, acceptAll]
  cases checkAll (ctx := ctx) nodes with
  | ok ds => exact ⟨fun h => congrArg _ (Except.ok.inj h), fun h => congrArg _ (Except.ok.inj h)⟩
  | error e => exact ⟨nofun, nofun⟩

end Child

/-- An element built from checked children holds the nodes that were checked: the lemma that
joins a list of data to the combinators. -/
theorem Element.children_ofChildren {t : Tag} {ctx : Ctx} (cs : List (Child (ctx.child t)))
    (attrs : List AttrVal)
    (ho : Content.elementOk ctx t (rawAttrs attrs) (cs.map Child.raw) = true)
    (ht : t.markupName.isSome = true) :
    (Element.ofChildren cs attrs ho ht).children = cs.map Child.raw := rfl

/-- An element whose tag has no ordered model owes only its attributes, whatever its children
are: so a list of children that is data goes into such an element with no proof about the
list. The combinators discharge this themselves; it is stated for `Element.ofChildren`. -/
theorem Content.elementOk_of_seq_none {t : Tag} (h : t.seq? = none) (c : Ctx)
    {attrs : List (String × String)} (ha : Content.attrsOk t attrs = true)
    (children : List RawNode) : Content.elementOk c t attrs children = true := by
  rw [Content.elementOk, ha, Content.seqOk_of_none _ t h]
  rfl

end Whatwg.Html
