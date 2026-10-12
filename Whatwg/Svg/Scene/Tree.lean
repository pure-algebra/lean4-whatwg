/-!
# Whatwg.Svg.Scene.Tree

Owner: a tree, and where each of its nodes stands (slice S13 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-70).

A program is a tree, and the first picture of a program is its tree. The rule of placement here
is the plainest one that is true to the tree. The leaves stand in a row in their order, one
column each. A node stands over its leaves: its *span* is the first and the last leaf under it,
and its depth is its row. Twice the middle of a span is a whole number, so the layer needs no
fraction and stays under the strict ceiling.

- `Tree α`: a value and its children, in order.
- `Tree.leaves`: how many leaves a tree has. A node with no child is one leaf.
- `Tree.spans depth start t`: every node of `t` with its span, the root first and each child
  after its parent, with the first leaf of `t` in the column `start`.
- `Tree.links`: every child with its parent, for the edges of a picture.

What the laws say of a picture drawn from the spans, top down:

- `spans_within`: a node's span lies inside its tree's columns, and no node is above the root.
  So a subtree is drawn inside the columns of its root.
- `spansAll_apart`: the columns of a subtree end before the columns of every later sibling
  begin. Two subtrees of one node do not interleave, so an edge of one does not cross an edge
  of the other.
- `spans_shift`: the spans of a tree placed `k` columns on are its spans, moved `k` columns. A
  subtree is drawn the same wherever it stands, so two equal subtrees look the same.
- `spans_values`: the nodes of the picture are the nodes of the tree, each once, in order.

What this module does not claim: a narrower placement, where a small subtree slides under a
neighbour's overhang (Reingold and Tilford); a placement of a graph that is no tree.
-/

namespace Whatwg.Svg.Scene

/-- A tree: a value and its children, in order. -/
inductive Tree (α : Type) where
  | node (value : α) (children : List (Tree α))

/-- Where a node stands among the leaves of its tree: the column of the first leaf under it, the
column of the last, and its depth. -/
structure Span where
  first : Nat
  last : Nat
  depth : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Span

/-- Twice the column of the middle of a span: a whole number. -/
def middle2 (s : Span) : Nat := s.first + s.last

/-- How many columns a span covers. -/
def width (s : Span) : Nat := s.last + 1 - s.first

/-- The span `k` columns on. -/
def shift (k : Nat) (s : Span) : Span := ⟨s.first + k, s.last + k, s.depth⟩

end Span

namespace Tree

variable {α : Type}

/-- The value at the root. -/
def value : Tree α → α
  | .node v _ => v

mutual

/-- The number of leaves of a tree. A node with no child is one leaf. -/
def leaves : Tree α → Nat
  | .node _ cs => max 1 (leavesAll cs)

/-- The number of leaves of a list of trees. -/
def leavesAll : List (Tree α) → Nat
  | [] => 0
  | t :: ts => leaves t + leavesAll ts

end

mutual

/-- The values of a tree, the root first and each child after its parent. -/
def values : Tree α → List α
  | .node v cs => v :: valuesAll cs

/-- The values of a list of trees, tree after tree. -/
def valuesAll : List (Tree α) → List α
  | [] => []
  | t :: ts => values t ++ valuesAll ts

end

mutual

/-- **Every node of a tree with its span**, the root first and each child after its parent. The
root is at `depth` and the first leaf of the tree in the column `start`. -/
def spans (depth start : Nat) : Tree α → List (α × Span)
  | .node v cs =>
    (v, ⟨start, start + max 1 (leavesAll cs) - 1, depth⟩) :: spansAll (depth + 1) start cs

/-- The nodes of a list of trees with their spans: each tree starts in the column after the
last leaf of the tree before it. -/
def spansAll (depth start : Nat) : List (Tree α) → List (α × Span)
  | [] => []
  | t :: ts => spans depth start t ++ spansAll depth (start + leaves t) ts

end

mutual

/-- Every child of a tree with its parent: the parent's value, then the child's. -/
def links : Tree α → List (α × α)
  | .node v cs => linksAll v cs

/-- The links of a list of trees under one parent: each root with the parent, and the links
inside each tree. -/
def linksAll (parent : α) : List (Tree α) → List (α × α)
  | [] => []
  | t :: ts => (parent, value t) :: (links t ++ linksAll parent ts)

end

/-- A tree has a leaf. -/
theorem leaves_pos : ∀ t : Tree α, 0 < leaves t
  | .node _ cs => by
    rw [leaves]
    exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left 1 _)

/-- The root's span: from the first column of the tree to its last, at the tree's depth. -/
theorem spans_head (depth start : Nat) : ∀ t : Tree α,
    (spans depth start t).head? = some (value t, ⟨start, start + leaves t - 1, depth⟩)
  | .node v cs => by
    rw [spans, leaves]
    rfl

mutual

/-- **The nodes of the picture are the nodes of the tree**, each once, in order. -/
theorem spans_values (depth start : Nat) : ∀ t : Tree α,
    (spans depth start t).map (fun p => p.1) = values t
  | .node v cs => by
    rw [spans, values, List.map_cons, spansAll_values (depth + 1) start cs]

/-- The same for a list of trees. -/
theorem spansAll_values (depth start : Nat) : ∀ ts : List (Tree α),
    (spansAll depth start ts).map (fun p => p.1) = valuesAll ts
  | [] => by rw [spansAll, valuesAll, List.map_nil]
  | t :: ts => by
    rw [spansAll, valuesAll, List.map_append, spans_values depth start t,
      spansAll_values depth (start + leaves t) ts]

end

mutual

/-- **A node's span lies inside its tree's columns, and no node is above the root.** -/
theorem spans_within (depth start : Nat) : ∀ (t : Tree α) (p : α × Span), p ∈ spans depth start t →
    start ≤ p.2.first ∧ p.2.first ≤ p.2.last ∧ p.2.last < start + leaves t ∧ depth ≤ p.2.depth
  | .node v cs, p, h => by
    rw [spans] at h
    rw [leaves]
    have h1 : 1 ≤ max 1 (leavesAll cs) := Nat.le_max_left 1 _
    have h2 : leavesAll cs ≤ max 1 (leavesAll cs) := Nat.le_max_right 1 _
    generalize max 1 (leavesAll cs) = m at h h1 h2 ⊢
    cases h with
    | head =>
      refine ⟨Nat.le_refl _, ?_, ?_, Nat.le_refl _⟩
      · show start ≤ start + m - 1
        omega
      · show start + m - 1 < start + m
        omega
    | tail _ hq =>
      obtain ⟨a, b, c, e⟩ := spansAll_within (depth + 1) start cs p hq
      refine ⟨a, b, ?_, ?_⟩
      · omega
      · omega

/-- The same for a list of trees, inside the columns of the whole list. -/
theorem spansAll_within (depth start : Nat) : ∀ (ts : List (Tree α)) (p : α × Span),
    p ∈ spansAll depth start ts →
    start ≤ p.2.first ∧ p.2.first ≤ p.2.last ∧ p.2.last < start + leavesAll ts ∧
      depth ≤ p.2.depth
  | [], p, h => by
    rw [spansAll] at h
    cases h
  | t :: ts, p, h => by
    rw [spansAll] at h
    rw [leavesAll]
    cases List.mem_append.mp h with
    | inl h1 =>
      obtain ⟨a, b, c, e⟩ := spans_within depth start t p h1
      refine ⟨a, b, ?_, e⟩
      omega
    | inr h2 =>
      obtain ⟨a, b, c, e⟩ := spansAll_within depth (start + leaves t) ts p h2
      refine ⟨?_, b, ?_, e⟩
      · omega
      · omega

end

/-- **Two subtrees of one node do not interleave**: the columns of a tree end before the
columns of every later sibling begin. -/
theorem spansAll_apart (depth start : Nat) (t : Tree α) (ts : List (Tree α)) (p q : α × Span)
    (hp : p ∈ spans depth start t) (hq : q ∈ spansAll depth (start + leaves t) ts) :
    p.2.last < q.2.first := by
  have a := (spans_within depth start t p hp).2.2.1
  have b := (spansAll_within depth (start + leaves t) ts q hq).1
  omega

mutual

/-- **A subtree is drawn the same wherever it stands**: the spans of a tree placed `k` columns
on are its spans, moved `k` columns. -/
theorem spans_shift (depth start k : Nat) : ∀ t : Tree α,
    spans depth (start + k) t = (spans depth start t).map fun p => (p.1, p.2.shift k)
  | .node v cs => by
    rw [spans, spans, List.map_cons, spansAll_shift (depth + 1) start k cs]
    have h1 : 1 ≤ max 1 (leavesAll cs) := Nat.le_max_left 1 _
    generalize max 1 (leavesAll cs) = m at h1 ⊢
    have e : start + k + m - 1 = start + m - 1 + k := by omega
    rw [e]
    rfl

/-- The same for a list of trees. -/
theorem spansAll_shift (depth start k : Nat) : ∀ ts : List (Tree α),
    spansAll depth (start + k) ts = (spansAll depth start ts).map fun p => (p.1, p.2.shift k)
  | [] => by rw [spansAll, spansAll, List.map_nil]
  | t :: ts => by
    rw [spansAll, spansAll, List.map_append, spans_shift depth start k t]
    have e : start + k + leaves t = start + leaves t + k := by omega
    rw [e, spansAll_shift depth (start + leaves t) k ts]

end

end Tree

end Whatwg.Svg.Scene
