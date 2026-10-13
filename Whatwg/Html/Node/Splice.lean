import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Splice

Owner: the parts of a typed tree that are data where the tree is written (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`, its second round; entries W8, W9 and W12 of
`docs/research/2026-10-12-whatwg-requests.md`). A page's frame is written once, and some of
it is known only when a program runs: the value of an attribute, whether an attribute is
there, the attributes of an element that a function returns, a list of children, a child that
may be absent. The tactic of the combinators (`Whatwg/Html/Node/Admit.lean`) and the markup
term (`Whatwg/Html/Syntax/Elaborator.lean`) close an obligation about such a tree by
evaluation, and an evaluation stops at a variable. This module holds what lets it pass: for
each kind of unknown part, a test that does not read the part, and the law that the test
answers for every value of it.

- **A value that is data.** `Content.attrFree t name` is the checker's test of an attribute
  with the test of its value left out. `attrOk_of_attrFree` says that an attribute which passes
  is admitted with every value. So `A.a_href (f k)` is a good attribute of `a`, and
  `A.a_scope_str x` is not shown to be one: `scope` takes keywords.
- **Attributes that are not written out.** `Content.unconditional t` says that no category of
  the element reads its attributes, and `Ctx.admitsWith_unread` that such an element is
  admitted with any attributes where its tag is. So `E.el e` stands for a variable `e`, such
  as a `head` that a function returns.
- **An attribute that may be absent.** `A.opt make o` is the attribute at `some`, and no
  attribute at `none`: `A.a_href href :: A.opt (A.aria_ "current") current`.
- **Children that are a list.** `Content.validAll_append` joins two valid lists, which is what
  a splice of a list among written children needs.

What this module does not claim: that a value which is data is a good value where the checker
reads values. There the value must be a literal, or the obligation is proved by cases.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

/-! ## An attribute whose value is not read

The checker's test of an attribute reads the value only where the attribute index gives the
attribute a kind with a rule: a boolean attribute, a closed list of keywords, an integer.
`attrFree` is the rest of that test, which reads no value, so one evaluation of it answers for
every value. -/

namespace Content

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

/-! ## An element whose attributes are not read -/

/-- No category of the element depends on its attributes: its row states no condition on
interactive, flow or phrasing content. -/
def unconditional (t : Tag) : Bool :=
  t.interactiveIf.isNone && t.flowIf.isNone && t.phrasingIf.isNone

/-- Where no category reads the attributes, the admission with attributes is the admission of
the tag. -/
theorem Ctx.admitsWith_eq_admits {t : Tag} (h : unconditional t = true) (c : Ctx)
    (attrs : List (String × String)) : c.admitsWith t attrs = c.admits t := by
  simp only [unconditional, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hinteractive, hflow⟩, hphrasing⟩ := h
  have hbase : Ctx.baseContainsWith c.base t attrs = c.base.contains t := by
    unfold Ctx.baseContainsWith
    rw [hflow, hphrasing]
    cases c.base <;> exact Bool.and_true _
  have hwith : Ctx.interactiveWith t attrs = Cats.interactive t := by
    unfold Ctx.interactiveWith
    rw [hinteractive]
  rw [Ctx.admitsWith, Ctx.admits, hbase, Ctx.excludedWith, Ctx.excluded, hwith]

/-- An element whose categories read no attribute is admitted with any attributes where its tag
is admitted. The two premises are closed tests: the attributes are not among them, so they may
be those of a variable. -/
theorem Ctx.admitsWith_unread (c : Ctx) (t : Tag) (attrs : List (String × String))
    (hu : unconditional t = true) (ha : c.admits t = true) : c.admitsWith t attrs = true :=
  (Ctx.admitsWith_eq_admits hu c attrs).trans ha

/-! ## A list among written children -/

/-- Two lists that are valid at a position are valid there as one. -/
theorem validAll_append (ctx : Ctx) : ∀ (nodes others : List RawNode),
    validAll ctx nodes = true → validAll ctx others = true →
    validAll ctx (nodes ++ others) = true
  | [], _, _, hothers => hothers
  | node :: rest, others, hnodes, hothers =>
    validAll_cons ctx node (rest ++ others) ((validAll_cons_iff ctx node rest).mp hnodes).1
      (validAll_append ctx rest others ((validAll_cons_iff ctx node rest).mp hnodes).2 hothers)

end Content

/-! ## An attribute that may be absent -/

namespace A

/-- An attribute that may be absent: `make value` at `some value`, and no attribute at `none`.
`A.a_href href :: A.opt (A.aria_ "current") current` is a link that says so when it is the
current one. The obligation of the element is proved for either case. -/
def opt {α : Type} (make : α → AttrVal) : Option α → List AttrVal
  | some value => [make value]
  | none => []

theorem opt_none {α : Type} (make : α → AttrVal) : opt make none = [] := rfl

theorem opt_some {α : Type} (make : α → AttrVal) (value : α) : opt make (some value) = [make value] :=
  rfl

end A

end Whatwg.Html
