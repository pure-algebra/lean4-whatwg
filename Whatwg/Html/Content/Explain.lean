import Whatwg.Html.Content.Valid

/-!
# Whatwg.Html.Content.Explain

Owner: the located refusal (slice S3c of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-16; rule M2 of
its section 3.1). `explain ctx n` answers why the checker refuses a tree and where: a path of
child indices from the root, and a reason. It is the second algebra of the walk
(`Whatwg.Html.Node.Walk`), over the same position as the checker's.

The refusal is complete against the checker: `explain_none_iff` says that it is absent exactly
when `validIn` is true (node C3 of the plan's section 6). The proof is the walk's fusion law at
`Option.isNone`, and it does no induction of its own. It needs one fact per kind of node: a
node's reason is absent exactly when its Boolean test holds (`Pos.isNone_refuse?`).

A reason is first-order data. A node's reason is a cascade of guards in the order of the
conjunction that the checker tests, so `Option.isNone` sends the cascade to that conjunction
(`isNone_orElse`, `isNone_guardReason`). `explainAt_path` says that the path names a node of
the tree (node C4), by the walk's induction law.

`Reason.describe` writes a reason for a message. No judgment reads it. The fault of an
attribute (`AttrFault`) is a description too: the checker's test decides, and the fault says
which part of the test failed.

What this module does not claim: that the first refusal is the only one. `explain` answers the
first in document order, and a tree may hold more.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode Walk)

/-! ## Reasons -/

/-- What is wrong with one attribute. A description for a message: no law reads it. -/
inductive AttrFault where
  /-- No attribute of the element's schema has this name. -/
  | unknown
  /-- The schema has the attribute, and this element does not take it. -/
  | notTaken
  /-- The element takes the attribute, and the value is not of its kind. -/
  | value
  /-- The value is not of its grammar, and no reading of the grammar continues at this offset
  of the value (`Whatwg/Svg/Value/Refusal.lean`). The offset is the count of characters before
  it, and the value's length when the value ends too soon. -/
  | valueAt (offset : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Why a node may not stand where it stands. -/
inductive Reason where
  /-- The name is no element of the position's namespace. -/
  | unknownElement
  /-- The name is a foreign element whose vocabulary is not modelled: `math`. -/
  | notModelled
  /-- The position does not admit the element. -/
  | notAdmitted
  /-- An attribute is not admitted on the element. -/
  | attribute (name : String) (fault : AttrFault)
  /-- An attribute name repeats. -/
  | repeatedAttribute
  /-- The children do not follow the element's ordered model. -/
  | order
  /-- The children do not hold a count of the element's model. -/
  | count
  /-- Character data stands where none may. -/
  | text
  /-- A comment stands where none may. -/
  | comment
  deriving DecidableEq, Repr, Inhabited

/-- A refusal: the path of child indices from the root to the refused node, and the reason. -/
structure Refusal where
  path : List Nat
  reason : Reason
  deriving DecidableEq, Repr, Inhabited

/-! ## Guards compose as a conjunction -/

/-- The reason, unless the test holds. -/
def guardReason (ok : Bool) (reason : Reason) : Option Reason := if ok then none else some reason

theorem isNone_guardReason (ok : Bool) (reason : Reason) :
    (guardReason ok reason).isNone = ok := by
  cases ok <;> rfl

/-- `Option.isNone` sends the first of two reasons to the conjunction of their absences. -/
theorem isNone_orElse {α : Type} (a : Option α) (b : Unit → Option α) :
    (a.orElse b).isNone = (a.isNone && (b ()).isNone) := by
  cases a <;> rfl

/-! ## Attributes -/

/-- The first attribute that fails a test, with the fault a classifier gives it. -/
def firstFault (ok : String → String → Bool) (fault : String → String → AttrFault) :
    List (String × String) → Option Reason
  | [] => none
  | attr :: rest =>
    if ok attr.1 attr.2 then firstFault ok fault rest
    else some (.attribute attr.1 (fault attr.1 attr.2))

theorem isNone_firstFault (ok : String → String → Bool) (fault : String → String → AttrFault) :
    ∀ attrs : List (String × String),
      (firstFault ok fault attrs).isNone = attrs.all fun attr => ok attr.1 attr.2
  | [] => rfl
  | attr :: rest => by
    simp only [firstFault, List.all_cons]
    cases ok attr.1 attr.2
    · rfl
    · simp only [↓reduceIte, Bool.true_and, isNone_firstFault ok fault rest]

/-- Which part of `attrOk` an HTML attribute fails. -/
def attrFault (t : Tag) (name _value : String) : AttrFault :=
  match Attr.ofName? name with
  | none => .unknown
  | some a =>
    match t.attribs? with
    | some set => if set.contains a then .value else .notTaken
    | none => .notTaken

/-- Which part of the SVG test an attribute fails. No value is judged here: the values of an
SVG subtree are the judgment of `Whatwg/Html/Content/Values.lean` (ruling SV-30). -/
def svgAttrFault (name _value : String) : AttrFault :=
  match Whatwg.Svg.Schema.Attr.ofChars? name.toList with
  | none => .unknown
  | some _ => .notTaken

/-- Why an attribute list fails `attrsOk`: the first attribute that is not admitted, or a
repeated name. -/
def attrsReason? (t : Tag) (attrs : List (String × String)) : Option Reason :=
  (firstFault (attrOk t) (attrFault t) attrs).orElse fun _ =>
    guardReason ((attrs.map (·.1)).eraseDups.length == attrs.length) .repeatedAttribute

theorem isNone_attrsReason? (t : Tag) (attrs : List (String × String)) :
    (attrsReason? t attrs).isNone = attrsOk t attrs := by
  simp only [attrsReason?, attrsOk, isNone_orElse, isNone_firstFault, isNone_guardReason]

/-- Why an attribute list fails `svgAttrsOk`. -/
def svgAttrsReason? (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String)) :
    Option Reason :=
  (firstFault (fun name value =>
      Whatwg.Svg.Content.attrOk t name.toList || namespaceAttrOk name value) svgAttrFault
    attrs).orElse fun _ =>
    guardReason ((attrs.map (·.1)).eraseDups.length == attrs.length) .repeatedAttribute

theorem isNone_svgAttrsReason? (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String)) :
    (svgAttrsReason? t attrs).isNone = svgAttrsOk t attrs := by
  simp only [svgAttrsReason?, svgAttrsOk, isNone_orElse, isNone_firstFault, isNone_guardReason]

/-- Why an SVG element fails `svgElementOk`: its attributes, then its counts. -/
def svgElementReason? (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String))
    (children : List RawNode) : Option Reason :=
  (svgAttrsReason? t attrs).orElse fun _ =>
    guardReason (Whatwg.Svg.Content.boundsOk t (svgChildTags children)) .count

theorem isNone_svgElementReason? (t : Whatwg.Svg.Schema.Tag) (attrs : List (String × String))
    (children : List RawNode) :
    (svgElementReason? t attrs children).isNone = svgElementOk t attrs children := by
  simp only [svgElementReason?, svgElementOk, isNone_orElse, isNone_svgAttrsReason?,
    isNone_guardReason]

/-! ## One node -/

/-- Why a name that is neither an HTML element nor `svg` is refused: a foreign element of a
vocabulary that is not modelled, or no element at all. -/
def foreignReason (name : String) : Reason :=
  if (Tag.ofForeignName? name).isSome then .notModelled else .unknownElement

namespace Pos

/-- Why the position refuses an element, in the order of the checker's test; `none` when the
test holds. -/
def refuse? : Pos → String → List (String × String) → List RawNode → Option Reason
  | .html c, name, attrs, children =>
    match Tag.ofName? name with
    | some t =>
      (guardReason (c.admitsWith t attrs) .notAdmitted).orElse fun _ =>
        (attrsReason? t attrs).orElse fun _ =>
          guardReason (seqOk (c.child t) t children) .order
    | none =>
      match Tag.ofForeignName? name with
      | some .svg =>
        (guardReason (c.admitsWith .svg attrs) .notAdmitted).orElse fun _ =>
          svgElementReason? .svg attrs children
      | _ => some (foreignReason name)
  | .svg c _, name, attrs, children =>
    match Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t =>
      (guardReason (c.admits t) .notAdmitted).orElse fun _ => svgElementReason? t attrs children
    | none => some .unknownElement

/-- A node's reason is absent exactly when its Boolean test holds. -/
theorem isNone_refuse? (p : Pos) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    (p.refuse? name attrs children).isNone = p.elementOk name attrs children := by
  cases p with
  | html c =>
    cases ht : Tag.ofName? name with
    | some t =>
      simp only [refuse?, elementOk, ht, isNone_orElse, isNone_guardReason, isNone_attrsReason?,
        Bool.and_assoc]
    | none =>
      cases hd : decide (Tag.ofForeignName? name = some .svg) with
      | true =>
        have hf := of_decide_eq_true hd
        simp only [refuse?, elementOk, ht, hf, isNone_orElse, isNone_guardReason,
          isNone_svgElementReason?]
      | false =>
        have hf := of_decide_eq_false hd
        simp only [refuse?, elementOk, ht, Option.isNone_some]
  | svg c x =>
    cases ht : Whatwg.Svg.Schema.Tag.ofChars? name.toList with
    | some t =>
      simp only [refuse?, elementOk, ht, isNone_orElse, isNone_guardReason,
        isNone_svgElementReason?]
    | none => simp only [refuse?, elementOk, ht, Option.isNone_some]

/-- Why the position refuses character data. -/
def textReason? (p : Pos) : Option Reason := guardReason p.textOk .text

/-- Why the position refuses a comment. -/
def commentReason? (p : Pos) : Option Reason := guardReason p.commentOk .comment

end Pos

/-! ## The refusal algebra -/

/-- The first refusal among the children's results, with the child's index put before its
path. `index` is the index of the list's first result. -/
def firstRefusal : Nat → List (Option Refusal) → Option Refusal
  | _, [] => none
  | index, some refusal :: _ => some ⟨index :: refusal.path, refusal.reason⟩
  | index, none :: rest => firstRefusal (index + 1) rest

theorem isNone_firstRefusal : ∀ (index : Nat) (results : List (Option Refusal)),
    (firstRefusal index results).isNone = (results.map Option.isNone).all id
  | _, [] => rfl
  | _, some _ :: _ => rfl
  | index, none :: rest => by
    simp only [firstRefusal, List.map_cons, List.all_cons, Option.isNone_none, id, Bool.true_and,
      isNone_firstRefusal (index + 1) rest]

/-- A reason at the node itself: the empty path. -/
def here (reason : Option Reason) : Option Refusal := reason.map fun r => ⟨[], r⟩

theorem isNone_here (reason : Option Reason) : (here reason).isNone = reason.isNone := by
  cases reason <;> rfl

/-- The located refusal as an algebra of the walk: a node's own reason, or the first of its
children's refusals. -/
def explainWalk : Walk Pos (Option Refusal) where
  step := Pos.child
  element := fun p name attrs children results =>
    (here (p.refuse? name attrs children)).orElse fun _ => firstRefusal 0 results
  text := fun p _ => here p.textReason?
  entity := fun p _ => here p.textReason?
  comment := fun p _ => here p.commentReason?

/-- Why the node may not stand at the position, and where; `none` when it may. -/
def explainAt (p : Pos) (n : RawNode) : Option Refusal := explainWalk.run p n

/-- Why the node may not stand at the HTML position, and where; `none` when it may. -/
def explain (ctx : Ctx) (n : RawNode) : Option Refusal := explainAt (.html ctx) n

/-- The refusal is absent exactly when the checker accepts: the walk's fusion law at
`Option.isNone`. -/
theorem isNone_explainAt (p : Pos) (n : RawNode) : (explainAt p n).isNone = validAt p n :=
  Walk.fusion explainWalk check Option.isNone (fun _ _ => rfl)
    (fun p name attrs children results => by
      simp only [explainWalk, check, isNone_orElse, isNone_here, Pos.isNone_refuse?,
        isNone_firstRefusal])
    (fun p _ => by
      simp only [explainWalk, check, isNone_here, Pos.textReason?, isNone_guardReason])
    (fun p _ => by
      simp only [explainWalk, check, isNone_here, Pos.textReason?, isNone_guardReason])
    (fun p _ => by
      simp only [explainWalk, check, isNone_here, Pos.commentReason?, isNone_guardReason])
    p n

/-- Node C3: the located refusal is complete against the checker. -/
theorem explain_none_iff (ctx : Ctx) (n : RawNode) : explain ctx n = none ↔ validIn ctx n = true := by
  rw [← Option.isNone_iff_eq_none, explain, isNone_explainAt]
  exact Iff.rfl

/-! ## The path names a node -/

end Whatwg.Html.Content

namespace Whatwg.Html

/-- The node at a path of child indices; `none` when the path leaves the tree. -/
def RawNode.at? : RawNode → List Nat → Option RawNode
  | node, [] => some node
  | .element _ _ children, index :: rest =>
    match children[index]? with
    | some child => child.at? rest
    | none => none
  | .text _, _ :: _ => none
  | .entity _, _ :: _ => none
  | .comment _, _ :: _ => none

end Whatwg.Html

namespace Whatwg.Html.Content

open Whatwg.Html (RawNode Walk)

/-- The first refusal among related children names a child and a path inside it. -/
theorem firstRefusal_path {children : List RawNode} {results : List (Option Refusal)}
    (h : Walk.Related (fun (n : RawNode) (o : Option Refusal) =>
      ∀ r, o = some r → (n.at? r.path).isSome = true) children results) :
    ∀ (index : Nat) (r : Refusal), firstRefusal index results = some r →
      ∃ (offset : Nat) (rest : List Nat) (child : RawNode), r.path = (index + offset) :: rest ∧
        children[offset]? = some child ∧ (child.at? rest).isSome = true := by
  induction h with
  | nil => intro index r hr; exact nomatch hr
  | @cons node result nodes results hnode _ ih =>
    intro index r hr
    cases result with
    | some refusal =>
      simp only [firstRefusal, Option.some.injEq] at hr
      refine ⟨0, refusal.path, node, ?_, rfl, hnode refusal rfl⟩
      rw [← hr]
      rfl
    | none =>
      simp only [firstRefusal] at hr
      obtain ⟨offset, rest, child, hpath, hchild, hat⟩ := ih (index + 1) r hr
      refine ⟨offset + 1, rest, child, ?_, hchild, hat⟩
      rw [hpath, Nat.add_assoc, Nat.add_comm 1 offset]

/-- Node C4: a refusal's path names a node of the tree. -/
theorem explainAt_path (p : Pos) (n : RawNode) {r : Refusal} (h : explainAt p n = some r) :
    (n.at? r.path).isSome = true := by
  refine Walk.relate explainWalk
    (fun (n : RawNode) (o : Option Refusal) => ∀ r, o = some r → (n.at? r.path).isSome = true)
    ?_ ?_ ?_ ?_ p n r h
  · intro s name attrs children results hrel r hr
    simp only [explainWalk] at hr
    cases hown : s.refuse? name attrs children with
    | some reason =>
      simp only [hown, here, Option.map_some, Option.orElse_some, Option.some.injEq] at hr
      rw [← hr]
      rfl
    | none =>
      simp only [hown, here, Option.map_none, Option.orElse_none] at hr
      obtain ⟨offset, rest, child, hpath, hchild, hat⟩ := firstRefusal_path hrel 0 r hr
      rw [hpath, Nat.zero_add, RawNode.at?, hchild]
      exact hat
  · intro s content r hr
    cases hown : s.textReason? with
    | some reason =>
      simp only [explainWalk, hown, here, Option.map_some, Option.some.injEq] at hr
      rw [← hr]
      rfl
    | none => simp only [explainWalk, hown, here, Option.map_none] at hr; exact nomatch hr
  · intro s name r hr
    cases hown : s.textReason? with
    | some reason =>
      simp only [explainWalk, hown, here, Option.map_some, Option.some.injEq] at hr
      rw [← hr]
      rfl
    | none => simp only [explainWalk, hown, here, Option.map_none] at hr; exact nomatch hr
  · intro s content r hr
    cases hown : s.commentReason? with
    | some reason =>
      simp only [explainWalk, hown, here, Option.map_some, Option.some.injEq] at hr
      rw [← hr]
      rfl
    | none => simp only [explainWalk, hown, here, Option.map_none] at hr; exact nomatch hr

/-! ## Messages -/

/-- A reason in words, for a message. No judgment reads this text. -/
def Reason.describe : Reason → String
  | .unknownElement => "the name is no element of this namespace"
  | .notModelled => "the element is a foreign element whose vocabulary is not modelled"
  | .notAdmitted => "the position does not admit the element"
  | .attribute name .unknown => "the attribute `" ++ name ++ "` is no attribute of the schema"
  | .attribute name .notTaken => "the element does not take the attribute `" ++ name ++ "`"
  | .attribute name .value => "the value of the attribute `" ++ name ++ "` is not of its kind"
  | .attribute name (.valueAt offset) =>
    "the value of the attribute `" ++ name ++ "` is not of its kind: no reading continues after " ++
      toString offset ++ (if offset == 1 then " character" else " characters")
  | .repeatedAttribute => "an attribute name repeats"
  | .order => "the children do not follow the element's content model"
  | .count => "the children do not hold a count of the element's content model"
  | .text => "character data may not stand here"
  | .comment => "a comment may not stand here"

end Whatwg.Html.Content
