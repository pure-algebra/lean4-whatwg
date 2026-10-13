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

`Refusal.describe` writes a whole refusal for a message, with the names of the elements along
its path, and `Refusal.describeIn` with the words of the position of the refused node (slice
S17; entry W7 of `docs/research/2026-10-12-whatwg-requests.md`). `explainAt_own` says that the
reason of a refusal is the own reason of the node at its path (node C5).

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

/-! ## A refusal in words, with the names along its path

A refusal holds a path of child indices. A reader of a message wants names: `Refusal.describe`
writes the path as the elements passed from the root, then the reason. A step is an element's
name, with its `id` where it has one (`section#intro`), else with its place among the elements
of its name beside it where there are several (`p[2]`, counted from one). A leaf is `text`,
`entity` or `comment`.

`Refusal.describeIn` says more where the position knows more. The checker judged the refused
node at a position, `Pos.at?` of the path, and that position has words: the context that
refuses an element or a text, the keywords an attribute takes, the model the children break.
These are the words the term `html!` and the tactic of the combinators report when the same
tree is written in a source file (`Ctx.describe`, `attrProblem?`, `seqProblem?`), so a tree
refused when a program runs reads as one refused when it is compiled.

`explainAt_own` is the law under those words (node C5): the reason of a refusal is the own
reason of the node at its path, at the position the transition reaches there. No judgment
reads the text itself. -/

namespace Whatwg.Html

/-- A node as one step of a path in words. An element is its name: with `#` and its `id` when
it has one that is not empty, else with its place among the elements of its name in
`siblings`, counted from one, when there are several. A leaf is its kind. `index` is the
node's place in `siblings`. -/
def RawNode.stepWords (siblings : List RawNode) (index : Nat) : RawNode → String
  | .element name attrs _ =>
    let same : RawNode → Bool := fun sibling => sibling.tagName? == some name
    let placed :=
      if (siblings.filter same).length ≤ 1 then name
      else name ++ "[" ++ toString (((siblings.take index).filter same).length + 1) ++ "]"
    match attrs.lookup "id" with
    | some id => if id.isEmpty then placed else name ++ "#" ++ id
    | none => placed
  | .text _ => "text"
  | .entity _ => "entity"
  | .comment _ => "comment"

/-- The steps of a path that starts in a list of trees: the first index names a tree of the
list, and each later index a child of the node before it. The steps end where the path leaves
the trees. -/
def RawNode.wordsAlong : List RawNode → List Nat → List String
  | _, [] => []
  | siblings, index :: rest =>
    match siblings[index]? with
    | some node => node.stepWords siblings index :: wordsAlong node.childNodes rest
    | none => []

/-- A path that names a node has a word for each of its steps. -/
theorem RawNode.length_wordsAlong : ∀ (path : List Nat) (siblings : List RawNode) (index : Nat)
    (node : RawNode), siblings[index]? = some node → (node.at? path).isSome = true →
    (RawNode.wordsAlong siblings (index :: path)).length = path.length + 1
  | [], siblings, index, node, hnode, _ => by
    rw [RawNode.wordsAlong, hnode]
    rfl
  | next :: rest, siblings, index, node, hnode, hpath => by
    rw [RawNode.wordsAlong, hnode]
    cases node with
    | element name attrs children =>
      rw [RawNode.at?] at hpath
      cases hchild : children[next]? with
      | none => rw [hchild] at hpath; exact nomatch hpath
      | some child =>
        rw [hchild] at hpath
        show (RawNode.wordsAlong children (next :: rest)).length + 1 = (next :: rest).length + 1
        rw [RawNode.length_wordsAlong rest children next child hchild hpath]
        rfl
    | text content => exact nomatch hpath
    | entity name => exact nomatch hpath
    | comment content => exact nomatch hpath

end Whatwg.Html

namespace Whatwg.Html.Content

open Whatwg.Html.Schema
open Whatwg.Html (RawNode Walk)

namespace Pos

/-- The position and the node at a path of child indices: the checker's transition at each
element passed. `none` when the path leaves the tree. -/
def at? : Pos → RawNode → List Nat → Option (Pos × RawNode)
  | p, node, [] => some (p, node)
  | p, .element name _ children, index :: rest =>
    match children[index]? with
    | some child => at? (p.child name) child rest
    | none => none
  | _, .text _, _ :: _ => none
  | _, .entity _, _ :: _ => none
  | _, .comment _, _ :: _ => none

/-- The node that `Pos.at?` answers is the node at the path. -/
theorem at?_node : ∀ (path : List Nat) (p : Pos) (node : RawNode),
    (p.at? node path).map Prod.snd = node.at? path
  | [], p, node => by rw [at?, RawNode.at?]; rfl
  | index :: rest, p, .element name attrs children => by
    rw [at?, RawNode.at?]
    cases children[index]? with
    | none => rfl
    | some child => exact at?_node rest (p.child name) child
  | _ :: _, _, .text _ => rfl
  | _ :: _, _, .entity _ => rfl
  | _ :: _, _, .comment _ => rfl

/-- Why the position refuses the node itself, whatever stands below it: the reason of the
node's own test. -/
def own? (p : Pos) : RawNode → Option Reason
  | .element name attrs children => p.refuse? name attrs children
  | .text _ => p.textReason?
  | .entity _ => p.textReason?
  | .comment _ => p.commentReason?

/-- A reason in the words of the position that gave it. At an HTML position: the context that
refuses an element or a text, the problem of an attribute as the attribute index states
it, and the model that the children break. In both namespaces: the element that is not
admitted, and the namespace that has no element of a name. For every other reason,
`Reason.describe`. -/
def reasonWords : Pos → RawNode → Reason → String
  | .html c, .element name _ _, .notAdmitted =>
    "<" ++ name ++ "> is not admitted here: the context is " ++ c.describe
  | .svg _ _, .element name _ _, .notAdmitted =>
    "<" ++ name ++ "> is not admitted here, in the content of an SVG element"
  | .html _, .element name _ _, .unknownElement => "<" ++ name ++ "> is no element of HTML"
  | .svg _ _, .element name _ _, .unknownElement => "<" ++ name ++ "> is no element of SVG"
  | .html _, .element name attrs _, .attribute attr fault =>
    match Tag.ofName? name, attrs.lookup attr with
    | some t, some value =>
      (attrProblem? t attr value).getD (Reason.describe (.attribute attr fault))
    | _, _ => Reason.describe (.attribute attr fault)
  | .html c, .element name _ children, .order =>
    match Tag.ofName? name with
    | some t => (seqProblem? (c.child t) t children).getD (Reason.describe .order)
    | none => Reason.describe .order
  | .html c, _, .text => "text is not admitted here: the context is " ++ c.describe
  | _, _, reason => reason.describe

end Pos

/-! ### The reason at the path is the node's own -/

theorem explainAt_element (p : Pos) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    explainAt p (.element name attrs children) =
      (here (p.refuse? name attrs children)).orElse fun _ =>
        firstRefusal 0 (explainWalk.runAll (p.child name) children) := by
  rw [explainAt, Walk.run_element]
  rfl

/-- A reason at the node itself has the empty path, and is the reason given. -/
theorem here_eq_some {reason : Option Reason} {r : Refusal} (h : here reason = some r) :
    r.path = [] ∧ reason = some r.reason := by
  cases reason with
  | none => exact nomatch h
  | some own =>
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩

mutual

/-- Node C5: the reason of a refusal is the own reason of the node at its path, at the
position that the checker's transition reaches there. So the words of that position are words
about the test that failed. -/
theorem explainAt_own : ∀ (p : Pos) (n : RawNode) (r : Refusal), explainAt p n = some r →
    ∃ q node, p.at? n r.path = some (q, node) ∧ q.own? node = some r.reason
  | p, .element name attrs children, r, h => by
    rw [explainAt_element] at h
    cases hown : p.refuse? name attrs children with
    | some reason =>
      rw [hown] at h
      obtain ⟨hpath, hreason⟩ := here_eq_some (reason := some reason) h
      refine ⟨p, .element name attrs children, ?_, ?_⟩
      · rw [hpath, Pos.at?]
      · rw [Pos.own?, hown, hreason]
    | none =>
      rw [hown] at h
      obtain ⟨offset, rest, child, hpath, hchild, q, node, hat, hq⟩ :=
        firstRefusal_own (p.child name) children 0 r h
      refine ⟨q, node, ?_, hq⟩
      rw [hpath, Nat.zero_add, Pos.at?, hchild]
      exact hat
  | p, .text content, r, h => by
    obtain ⟨hpath, hreason⟩ := here_eq_some (reason := p.textReason?) h
    exact ⟨p, .text content, by rw [hpath, Pos.at?], hreason⟩
  | p, .entity name, r, h => by
    obtain ⟨hpath, hreason⟩ := here_eq_some (reason := p.textReason?) h
    exact ⟨p, .entity name, by rw [hpath, Pos.at?], hreason⟩
  | p, .comment content, r, h => by
    obtain ⟨hpath, hreason⟩ := here_eq_some (reason := p.commentReason?) h
    exact ⟨p, .comment content, by rw [hpath, Pos.at?], hreason⟩

/-- The same for the first refusal among the children of an element. -/
theorem firstRefusal_own : ∀ (p : Pos) (children : List RawNode) (index : Nat) (r : Refusal),
    firstRefusal index (explainWalk.runAll p children) = some r →
    ∃ (offset : Nat) (rest : List Nat) (child : RawNode), r.path = (index + offset) :: rest ∧
      children[offset]? = some child ∧
      ∃ q node, p.at? child rest = some (q, node) ∧ q.own? node = some r.reason
  | p, [], index, r, h => by
    rw [Walk.runAll_nil] at h
    exact nomatch h
  | p, child :: more, index, r, h => by
    rw [Walk.runAll_cons] at h
    cases hchild : explainWalk.run p child with
    | some refusal =>
      rw [hchild] at h
      obtain ⟨q, node, hat, hq⟩ := explainAt_own p child refusal hchild
      cases Option.some.inj h
      exact ⟨0, refusal.path, child, rfl, rfl, q, node, hat, hq⟩
    | none =>
      rw [hchild] at h
      obtain ⟨offset, rest, found, hpath, hfound, hrest⟩ :=
        firstRefusal_own p more (index + 1) r h
      exact ⟨offset + 1, rest, found, by rw [hpath, Nat.add_assoc, Nat.add_comm 1 offset],
        hfound, hrest⟩

end

namespace Refusal

/-- Where a refusal is, in a list of trees: the names from the tree at `index` down to the
refused node, as `/main/section#intro/p[2]/div`. -/
def placeAmong (r : Refusal) (nodes : List RawNode) (index : Nat) : String :=
  "/" ++ "/".intercalate (RawNode.wordsAlong nodes (index :: r.path))

/-- Why, in the words of the position of the refused node, where `p` is the position of the
list's trees. -/
def wordsAmong (r : Refusal) (p : Pos) (nodes : List RawNode) (index : Nat) : String :=
  match nodes[index]? with
  | some node =>
    match p.at? node r.path with
    | some (q, refused) => q.reasonWords refused r.reason
    | none => r.reason.describe
  | none => r.reason.describe

/-- Where a refusal is in its tree: the names along its path, from the root. -/
def place (r : Refusal) (tree : RawNode) : String := r.placeAmong [tree] 0

/-- A refusal in words: the names along its path, then its reason. It reads the tree and no
position, so it serves a refusal of any judgment of the walk, a refused value included. -/
def describe (r : Refusal) (tree : RawNode) : String := r.place tree ++ ": " ++ r.reason.describe

/-- A refusal of `explainAt p tree` in words: the names along its path, then its reason in
the words of the position of the refused node. -/
def describeAt (r : Refusal) (p : Pos) (tree : RawNode) : String :=
  r.place tree ++ ": " ++ r.wordsAmong p [tree] 0

/-- A refusal of `explain ctx tree` in words: the names along its path, then its reason in
the words of the position of the refused node. -/
def describeIn (r : Refusal) (ctx : Ctx) (tree : RawNode) : String := r.describeAt (.html ctx) tree

end Refusal

/-- A refusal in a list of trees that stand at one position, such as the children of an
element: the place of the refused tree in the list, and that tree's refusal. -/
structure ListRefusal where
  index : Nat
  refusal : Refusal
  deriving DecidableEq, Repr, Inhabited

namespace ListRefusal

/-- A refusal in a list of trees in words: the names from the refused tree of the list down to
the refused node, then the reason. -/
def describe (e : ListRefusal) (nodes : List RawNode) : String :=
  e.refusal.placeAmong nodes e.index ++ ": " ++ e.refusal.reason.describe

/-- The same, with the reason in the words of the position of the refused node, where the
trees of the list stand at `ctx`. -/
def describeIn (e : ListRefusal) (ctx : Ctx) (nodes : List RawNode) : String :=
  e.refusal.placeAmong nodes e.index ++ ": " ++ e.refusal.wordsAmong (.html ctx) nodes e.index

end ListRefusal

/-- The tree's refusal at an HTML position in words; `none` when the checker accepts it. -/
def explainWords (ctx : Ctx) (tree : RawNode) : Option String :=
  (explain ctx tree).map fun refusal => refusal.describeIn ctx tree

/-- The words are absent exactly when the checker accepts. -/
theorem explainWords_none_iff (ctx : Ctx) (tree : RawNode) :
    explainWords ctx tree = none ↔ validIn ctx tree = true := by
  rw [explainWords, Option.map_eq_none_iff, explain_none_iff]

/-- A refusal of the checker has a word for each step of its path, and one for the root. -/
theorem length_wordsAlong_of_explainAt (p : Pos) (tree : RawNode) {r : Refusal}
    (h : explainAt p tree = some r) :
    (RawNode.wordsAlong [tree] (0 :: r.path)).length = r.path.length + 1 :=
  RawNode.length_wordsAlong r.path [tree] 0 tree rfl (explainAt_path p tree h)

end Whatwg.Html.Content
