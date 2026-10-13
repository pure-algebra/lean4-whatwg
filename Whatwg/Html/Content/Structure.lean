import Whatwg.Html.Content.Document

/-!
# Whatwg.Html.Content.Structure

Owner: the structure of a tree as facts that can be named (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; the HTML half of entry W14 of
`docs/research/2026-10-12-whatwg-requests.md`). A stylesheet draws structure: the boundary of
a part, the head of a table, a block of code, a region that scrolls. Entry W14 asks that every
rule of a sheet name the fact it draws, as a value and not as a comment. This module is what
the HTML side owes to that: what a structural fact is, and the test that a tree has it.

What it gives:

- `Spot`, one element as a fact reads it: its name, its attributes, and how many elements
  stand before and after it among the children of its parent.
- `Test`, a test of one spot (a name, a token of `class`, an attribute, a value, the first
  child, the n-th from the last, and their Boolean combinations), and `Where`, a place in a
  tree: an element that passes a test, standing as a child of a place, or anywhere inside one.
  `Where.holds` reads a place against a chain of spots: the element, then the elements above
  it, the nearest first.
- `places w tree`, the paths of the elements of a tree where `w` holds, in tree order, in one
  pass; `placesAll` for a list of trees in a row; `occurs`, whether there is any.
- `Vocabulary`, the class of types of facts: a fact names its place. `Fact` is the package's
  own vocabulary, the facts that its builders make and that the HTML Standard names. A
  consumer's facts (the status of a claim, the key of a part) are a type of the consumer's
  with an instance, and the sum of two vocabularies is one. `unused facts trees` is the facts
  that no tree shows: a rule that draws nothing.

What the laws give. `mem_places_iff`: a path is among the places exactly when the fact holds
of the chain that `chainAt?` reads at that path. So `places` is that reading at every element,
and the pass is no second definition. `Test.holds` is a homomorphism to `Bool` by definition
(`holds_not`, `holds_and`, `holds_or`), so the places of a conjunction are those of both
(`mem_places_and`). `mem_placesAmong_iff` is the law of a list: a place in a list of trees is
a place in one of them, read with the elements before and after it in the whole list.

The selector of a place is `Whatwg/Html/Content/Structure/Selector.lean`, and the sheet whose
every rule holds a fact is `Whatwg/Html/Content/Structure/Sheet.lean`. The theorem that a
selector selects the elements of a place is not here: Selectors is not sealed in this
repository, and a `Where` is this module's own term, not a selector. The constructors were chosen so that each
has one obvious selector (from memory of Selectors Level 4, not checked): a type selector, a
class selector, the two attribute selectors, `:first-child`, `:nth-last-child(n)`, `:not()`,
a compound, `:is()`, the child combinator and the descendant combinator.

What this module does not claim:

- Anything of a state that a tree does not hold: a pointer over an element, the focus, the
  target of the address. Those are no facts of a tree.
- That a name is compared as a browser compares it. Names and values are compared exactly, as
  `Condition.lookup` does: every producer of this library writes them in lower case.
- A namespace. `named "a"` holds of an HTML `a` and of an SVG `a`.
- That the places of a list of trees are those of each tree alone: `first` and `nthLast` read
  the elements beside a tree, so the law of a list carries their counts.
- The basis of `Fact.region`, `Fact.current` and `Fact.currentPage`: WAI-ARIA is not sealed
  here (debt D138). The three are conventions, as in `Whatwg/Html/Node/Region.lean`.
-/

namespace Whatwg.Html.Content.Structure

open Whatwg.Html (RawNode)
open Whatwg.Html.Schema (Condition)

/-! ## One element -/

/-- One element as a structural fact reads it: its name, its attributes, and the number of
elements before it and after it among the children of its parent. Text and comments are not
counted. -/
structure Spot where
  name : String
  attrs : List (String × String)
  before : Nat
  after : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The tokens of the element's `class`: a set of space-separated tokens (HTML Standard,
section "Global attributes"). -/
def Spot.classes (s : Spot) : List String :=
  ((Condition.lookup s.attrs "class").map Document.tokens).getD []

/-- A test of one element. -/
inductive Test where
  /-- Every element. -/
  | any
  /-- The element's name. -/
  | named (name : String)
  /-- A token of its `class`. -/
  | classed (token : String)
  /-- It has the attribute. -/
  | has (attr : String)
  /-- It has the attribute with this value, exactly. -/
  | valued (attr value : String)
  /-- No element stands before it among its parent's children. -/
  | first
  /-- It is the n-th element from the last among its parent's children: `nthLast 1` is the
  last. -/
  | nthLast (n : Nat)
  | not (t : Test)
  | and (a b : Test)
  | or (a b : Test)
  deriving DecidableEq, Repr, Inhabited

/-- The element passes the test. -/
def Test.holds : Test → Spot → Bool
  | .any, _ => true
  | .named name, s => s.name == name
  | .classed token, s => s.classes.contains token
  | .has attr, s => (Condition.lookup s.attrs attr).isSome
  | .valued attr value, s => Condition.lookup s.attrs attr == some value
  | .first, s => s.before == 0
  | .nthLast n, s => s.after + 1 == n
  | .not t, s => !t.holds s
  | .and a b, s => a.holds s && b.holds s
  | .or a b, s => a.holds s || b.holds s

/-- One of several names. -/
def Test.oneOf : List String → Test
  | [] => .not .any
  | [name] => .named name
  | name :: rest => .or (.named name) (Test.oneOf rest)

theorem Test.holds_not (t : Test) (s : Spot) : (Test.not t).holds s = !t.holds s := rfl

theorem Test.holds_and (a b : Test) (s : Spot) : (Test.and a b).holds s = (a.holds s && b.holds s) :=
  rfl

theorem Test.holds_or (a b : Test) (s : Spot) : (Test.or a b).holds s = (a.holds s || b.holds s) :=
  rfl

/-! ## A place -/

/-- A place in a tree. -/
inductive Where where
  /-- An element that passes the test, wherever it stands. -/
  | here (t : Test)
  /-- An element that passes the test and is a child of a place. -/
  | under (parent : Where) (t : Test)
  /-- An element that passes the test and stands anywhere inside a place. -/
  | inside (above : Where) (t : Test)
  deriving DecidableEq, Repr, Inhabited

/-- A chain and each of its tails that is not empty: an element with those above it, then its
parent with those above it, and so on. -/
def suffixes {α : Type} : List α → List (List α)
  | [] => []
  | first :: rest => (first :: rest) :: suffixes rest

/-- The place holds of a chain of spots: the element, then the elements above it, the nearest
first. -/
def Where.holds : Where → List Spot → Bool
  | .here t, chain =>
    match chain with
    | spot :: _ => t.holds spot
    | [] => false
  | .under parent t, chain =>
    match chain with
    | spot :: above => t.holds spot && parent.holds above
    | [] => false
  | .inside ancestor t, chain =>
    match chain with
    | spot :: above => t.holds spot && (suffixes above).any fun higher => ancestor.holds higher
    | [] => false

/-- The test of the element that a place ends in. -/
def Where.test : Where → Test
  | .here t => t
  | .under _ t => t
  | .inside _ t => t

/-- A place holds only of a chain whose element passes its last test. -/
theorem Where.test_of_holds {w : Where} {spot : Spot} {above : List Spot}
    (h : w.holds (spot :: above) = true) : w.test.holds spot = true := by
  cases w with
  | here t => exact h
  | under parent t =>
    have hboth : (t.holds spot && parent.holds above) = true := h
    exact (Bool.and_eq_true _ _ ▸ hboth).1
  | inside ancestor t =>
    have hboth : (t.holds spot && (suffixes above).any fun higher => ancestor.holds higher) = true := h
    exact (Bool.and_eq_true _ _ ▸ hboth).1

/-! ## The places of a tree -/

/-- One for an element, and none for a text, an entity or a comment. -/
def unit : RawNode → Nat
  | .element _ _ _ => 1
  | .text _ => 0
  | .entity _ => 0
  | .comment _ => 0

/-- The number of elements among some nodes. -/
def elementCount : List RawNode → Nat
  | [] => 0
  | node :: rest => unit node + elementCount rest

mutual

/-- The paths below a node where the place holds, the node's own first. `above` is the chain
above the node, and `before` and `after` the elements beside it. -/
def placesOf (w : Where) (above : List Spot) (before after : Nat) : RawNode → List (List Nat)
  | .element name attrs children =>
    (if w.holds (⟨name, attrs, before, after⟩ :: above) then [[]] else []) ++
      placesAmong w (⟨name, attrs, before, after⟩ :: above) 0 0 children
  | .text _ => []
  | .entity _ => []
  | .comment _ => []

/-- The same over the children of one parent, whose chain is `chain`. `index` is the index of
the first node and `before` the elements before it. -/
def placesAmong (w : Where) (chain : List Spot) (index before : Nat) : List RawNode → List (List Nat)
  | [] => []
  | node :: rest =>
    (placesOf w chain before (elementCount rest) node).map (fun path => index :: path) ++
      placesAmong w chain (index + 1) (before + unit node) rest

end

/-- **The places of a fact in a tree**: the paths of the elements where it holds, in tree
order. A path is child indices from the root, as in `Content.Refusal`. -/
def places (w : Where) (tree : RawNode) : List (List Nat) := placesOf w [] 0 0 tree

/-- The places of a fact in a list of trees that stand in a row with nothing above them: each
path begins with the index of its tree. -/
def placesAll (w : Where) (trees : List RawNode) : List (List Nat) := placesAmong w [] 0 0 trees

/-- The tree shows the fact somewhere. -/
def occurs (w : Where) (tree : RawNode) : Bool := !(places w tree).isEmpty

/-! ## What a place is: the chain at a path -/

/-- The chain of the element at a path below a node: its spot, then those of the elements
above it. None when the path leaves the tree or ends at no element. -/
def chainAt? (above : List Spot) (before after : Nat) : RawNode → List Nat → Option (List Spot)
  | .element name attrs _, [] => some (⟨name, attrs, before, after⟩ :: above)
  | .element name attrs children, index :: rest =>
    match children[index]? with
    | some child =>
      chainAt? (⟨name, attrs, before, after⟩ :: above) (elementCount (children.take index))
        (elementCount (children.drop (index + 1))) child rest
    | none => none
  | .text _, _ => none
  | .entity _, _ => none
  | .comment _, _ => none

/-- The law of a list: a place among nodes in a row is a place below one of them, read with
the elements before it and after it in the whole list. -/
theorem mem_placesAmong_iff (w : Where) (chain : List Spot) (path : List Nat) :
    ∀ (nodes : List RawNode) (index before : Nat),
      path ∈ placesAmong w chain index before nodes ↔
        ∃ (offset : Nat) (rest : List Nat) (child : RawNode),
          path = (index + offset) :: rest ∧ nodes[offset]? = some child ∧
            rest ∈ placesOf w chain (before + elementCount (nodes.take offset))
              (elementCount (nodes.drop (offset + 1))) child
  | [], index, before => by
    rw [placesAmong]
    refine ⟨fun h => (nomatch h), fun ⟨offset, _, _, _, h, _⟩ => ?_⟩
    rw [List.getElem?_nil] at h
    exact nomatch h
  | node :: others, index, before => by
    rw [placesAmong, List.mem_append, List.mem_map, mem_placesAmong_iff w chain path others]
    constructor
    · rintro (⟨rest, hrest, rfl⟩ | ⟨offset, rest, child, rfl, hchild, hrest⟩)
      · exact ⟨0, rest, node, rfl, rfl, hrest⟩
      · refine ⟨offset + 1, rest, child, by rw [Nat.add_assoc, Nat.add_comm 1 offset], hchild, ?_⟩
        rw [List.take_succ_cons, List.drop_succ_cons, elementCount, ← Nat.add_assoc]
        exact hrest
    · rintro ⟨offset, rest, child, rfl, hchild, hrest⟩
      cases offset with
      | zero =>
        cases Option.some.inj hchild
        exact Or.inl ⟨rest, hrest, rfl⟩
      | succ offset =>
        refine Or.inr ⟨offset, rest, child, by rw [Nat.add_assoc, Nat.add_comm 1 offset], hchild, ?_⟩
        rw [List.take_succ_cons, List.drop_succ_cons, elementCount, ← Nat.add_assoc] at hrest
        exact hrest

mutual

/-- A path is a place below a node exactly when the place holds of the chain at that path. -/
theorem mem_placesOf_iff (w : Where) :
    ∀ (node : RawNode) (above : List Spot) (before after : Nat) (path : List Nat),
      path ∈ placesOf w above before after node ↔
        ∃ chain, chainAt? above before after node path = some chain ∧ w.holds chain = true
  | .element name attrs children, above, before, after, [] => by
    rw [placesOf, List.mem_append, chainAt?]
    constructor
    · rintro (hhere | hbelow)
      · cases hholds : w.holds (⟨name, attrs, before, after⟩ :: above) with
        | true => exact ⟨_, rfl, hholds⟩
        | false =>
          rw [hholds] at hhere
          exact nomatch hhere
      · obtain ⟨_, _, _, hpath, _⟩ := (mem_placesAmong_iff w _ [] children 0 0).mp hbelow
        exact nomatch hpath
    · rintro ⟨chain, hchain, hholds⟩
      cases Option.some.inj hchain
      rw [hholds]
      exact Or.inl (List.mem_singleton.mpr rfl)
  | .element name attrs children, above, before, after, index :: rest => by
    rw [placesOf, List.mem_append, chainAt?]
    constructor
    · rintro (hhere | hbelow)
      · cases hholds : w.holds (⟨name, attrs, before, after⟩ :: above) with
        | true =>
          rw [hholds] at hhere
          exact nomatch (List.mem_singleton.mp hhere)
        | false =>
          rw [hholds] at hhere
          exact nomatch hhere
      · obtain ⟨offset, tail, child, hpath, hchild, htail⟩ :=
          (mem_placesAmong_iff w _ (index :: rest) children 0 0).mp hbelow
        rw [Nat.zero_add] at hpath htail
        obtain ⟨rfl, rfl⟩ := List.cons.inj hpath
        rw [hchild]
        exact (mem_placesAll_iff w children index child hchild _ _ _ rest).mp htail
    · rintro ⟨chain, hchain, hholds⟩
      cases hchild : children[index]? with
      | none =>
        rw [hchild] at hchain
        exact nomatch hchain
      | some child =>
        rw [hchild] at hchain
        refine Or.inr ((mem_placesAmong_iff w _ (index :: rest) children 0 0).mpr
          ⟨index, rest, child, by rw [Nat.zero_add], hchild, ?_⟩)
        rw [Nat.zero_add]
        exact (mem_placesAll_iff w children index child hchild _ _ _ rest).mpr ⟨chain, hchain, hholds⟩
  | .text _, _, _, _, _ => by
    rw [placesOf, chainAt?]
    exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | .entity _, _, _, _, _ => by
    rw [placesOf, chainAt?]
    exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | .comment _, _, _, _, _ => by
    rw [placesOf, chainAt?]
    exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩

/-- The same at each node of a list. -/
theorem mem_placesAll_iff (w : Where) :
    ∀ (nodes : List RawNode) (index : Nat) (child : RawNode), nodes[index]? = some child →
      ∀ (above : List Spot) (before after : Nat) (path : List Nat),
        path ∈ placesOf w above before after child ↔
          ∃ chain, chainAt? above before after child path = some chain ∧ w.holds chain = true
  | [], _, _, h => by
    rw [List.getElem?_nil] at h
    exact nomatch h
  | node :: _, 0, child, h => by
    cases Option.some.inj h
    exact mem_placesOf_iff w node
  | _ :: rest, index + 1, child, h => mem_placesAll_iff w rest index child h

end

/-- **A path is a place of a fact exactly when the fact holds of the chain at that path.** The
one pass of `places` is the reading of `chainAt?` at every element. -/
theorem mem_places_iff (w : Where) (tree : RawNode) (path : List Nat) :
    path ∈ places w tree ↔ ∃ chain, chainAt? [] 0 0 tree path = some chain ∧ w.holds chain = true :=
  mem_placesOf_iff w tree [] 0 0 path

/-- The places of a conjunction of two tests are the places of both. -/
theorem mem_places_and (a b : Test) (tree : RawNode) (path : List Nat) :
    path ∈ places (.here (.and a b)) tree ↔
      path ∈ places (.here a) tree ∧ path ∈ places (.here b) tree := by
  rw [mem_places_iff, mem_places_iff, mem_places_iff]
  constructor
  · rintro ⟨chain, hchain, hholds⟩
    cases chain with
    | nil => exact nomatch hholds
    | cons spot above =>
      have hboth : (a.holds spot && b.holds spot) = true := hholds
      rw [Bool.and_eq_true] at hboth
      exact ⟨⟨_, hchain, hboth.1⟩, ⟨_, hchain, hboth.2⟩⟩
  · rintro ⟨⟨chain, hchain, ha⟩, ⟨other, hother, hb⟩⟩
    cases Option.some.inj (hchain.symm.trans hother)
    cases chain with
    | nil => exact nomatch ha
    | cons spot above =>
      refine ⟨_, hchain, ?_⟩
      have hleft : a.holds spot = true := ha
      have hright : b.holds spot = true := hb
      show (a.holds spot && b.holds spot) = true
      rw [hleft, hright]
      rfl

/-- The tree shows the fact exactly when the fact holds of the chain at some path. -/
theorem occurs_iff (w : Where) (tree : RawNode) :
    occurs w tree = true ↔
      ∃ path chain, chainAt? [] 0 0 tree path = some chain ∧ w.holds chain = true := by
  unfold occurs
  constructor
  · intro h
    cases hplaces : places w tree with
    | nil =>
      rw [hplaces] at h
      exact nomatch h
    | cons path rest =>
      have hmem : path ∈ places w tree := by
        rw [hplaces]
        exact List.mem_cons_self
      exact ⟨path, (mem_places_iff w tree path).mp hmem⟩
  · rintro ⟨path, hchain⟩
    have hmem := (mem_places_iff w tree path).mpr hchain
    cases hplaces : places w tree with
    | nil =>
      rw [hplaces] at hmem
      exact nomatch hmem
    | cons first rest => rfl

/-! ## Vocabularies -/

/-- A type of structural facts: each fact names the place where it holds. A stylesheet whose
rules each hold a fact of such a type draws only what the type can name. -/
class Vocabulary (φ : Type) where
  /-- Where in a tree the fact holds. -/
  place : φ → Where

/-- Two vocabularies are one: a fact of either. So a sheet draws the package's facts and the
consumer's with one type. -/
instance {φ ψ : Type} [Vocabulary φ] [Vocabulary ψ] : Vocabulary (φ ⊕ ψ) where
  place
    | .inl fact => Vocabulary.place fact
    | .inr fact => Vocabulary.place fact

/-- The places of a fact of a vocabulary in a tree. -/
def placesOfFact {φ : Type} [Vocabulary φ] (fact : φ) (tree : RawNode) : List (List Nat) :=
  places (Vocabulary.place fact) tree

/-- The facts that none of the trees shows: for a sheet, the rules that draw nothing. -/
def unused {φ : Type} [Vocabulary φ] (facts : List φ) (trees : List RawNode) : List φ :=
  facts.filter fun fact => trees.all fun tree => !occurs (Vocabulary.place fact) tree

/-- A fact of `unused` is shown by no tree of the list. -/
theorem occurs_of_mem_unused {φ : Type} [Vocabulary φ] {facts : List φ} {trees : List RawNode}
    {fact : φ} (h : fact ∈ unused facts trees) {tree : RawNode} (htree : tree ∈ trees) :
    occurs (Vocabulary.place fact) tree = false := by
  have hall := (List.mem_filter.mp h).2
  have hone := List.all_eq_true.mp hall tree htree
  cases hoccurs : occurs (Vocabulary.place fact) tree with
  | false => rfl
  | true =>
    rw [hoccurs] at hone
    exact nomatch hone

/-- The headings, `h1` to `h6`. -/
def heading : Test := Test.oneOf ["h1", "h2", "h3", "h4", "h5", "h6"]

/-- The package's own vocabulary: structure that its builders make, or that the HTML Standard
names. -/
inductive Fact where
  /-- The heading that opens a part: a heading that is a child of a `section` or an `article`.
  The boundary of the part is drawn at it. -/
  | partHeading
  /-- A header cell of a table: `th`. -/
  | tableHead
  /-- A cell of the body of a table: a `td` inside a `tbody`. -/
  | bodyCell
  /-- The first cell of a row. -/
  | rowHead
  /-- A block of preformatted text: `pre`. -/
  | block
  /-- Code that is a block: a `code` that is a child of a `pre`, the standard's way to mark a
  block of code. -/
  | codeBlock
  /-- Code in a line: a `code` that is no child of a `pre`. -/
  | codeSpan
  /-- A region that scrolls: the element that `region` of `Whatwg/Html/Node/Region.lean`
  builds, with `role="region"` and `tabindex`. -/
  | region
  /-- The caption of a figure. -/
  | caption
  /-- The summary of a `details`: what stays when it is folded. -/
  | summary
  /-- The item of a navigation that is the current one, by `aria-current` with any value. -/
  | current
  /-- The item that is the current page: `aria-current="page"`. -/
  | currentPage
  /-- The main content, the page's header and its footer: the children of `body` of those
  names. -/
  | main
  | pageHeader
  | pageFooter
  deriving DecidableEq, Repr, Inhabited

/-- Where each fact of the package holds. -/
def Fact.place : Fact → Where
  | .partHeading => .under (.here (.or (.named "section") (.named "article"))) heading
  | .tableHead => .here (.named "th")
  | .bodyCell => .inside (.here (.named "tbody")) (.named "td")
  | .rowHead => .under (.here (.named "tr")) (.and (.or (.named "td") (.named "th")) .first)
  | .block => .here (.named "pre")
  | .codeBlock => .under (.here (.named "pre")) (.named "code")
  | .codeSpan => .under (.here (.not (.named "pre"))) (.named "code")
  | .region => .here (.and (.valued "role" "region") (.has "tabindex"))
  | .caption => .under (.here (.named "figure")) (.named "figcaption")
  | .summary => .under (.here (.named "details")) (.named "summary")
  | .current => .here (.has "aria-current")
  | .currentPage => .here (.valued "aria-current" "page")
  | .main => .under (.here (.named "body")) (.named "main")
  | .pageHeader => .under (.here (.named "body")) (.named "header")
  | .pageFooter => .under (.here (.named "body")) (.named "footer")

instance : Vocabulary Fact := ⟨Fact.place⟩

/-- Every fact of the package, for a census. -/
def Fact.all : List Fact :=
  [.partHeading, .tableHead, .bodyCell, .rowHead, .block, .codeBlock, .codeSpan, .region,
    .caption, .summary, .current, .currentPage, .main, .pageHeader, .pageFooter]

theorem Fact.mem_all (fact : Fact) : fact ∈ Fact.all := by cases fact <;> decide

end Whatwg.Html.Content.Structure
