import Whatwg.Svg.Scene.Tree
import Whatwg.Svg.Scene.Extent

/-!
# Whatwg.Svg.Scene.Tree.Room

Owner: the room of a node of a tree (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Tree.lean` says where a node stands with a `Span`: the first and the last
column of the leaves under it, and its depth. `Whatwg/Svg/Scene/Extent.lean` came later and has
one notion of where a thing is, the box `IBox`, with what it is inside and what it does not
touch. This module reads a span as a box, so the laws of the tree are laws of rooms, and a
tree's nodes can be asked what any other thing of a picture is asked.

- `Span.box`: **the room of a span**, in cells: from its first column to its last, one row
  high at its depth.
- A span moves by whole columns (`Moves Nat Span`, which is `Span.shift`).

What the laws say:

- `Span.box_shift`: the room of a span moved by columns is its room, moved across. This is the
  law that `Boxed` asks of a type, for the moves that a span has. A span is not an instance of
  `Boxed`: it counts its columns in numbers that are not negative, and a `Boxed` thing moves by
  any whole step.
- `Span.box_solid`: the room of a span whose first column is not after its last has a point.
- `Tree.spans_clear`: **no two nodes of a tree share room.** A parent is a row above its
  children, and two subtrees of one node have their columns apart. So the list of a tree's
  rooms is clear as `Layout.Clear` reads it, and a pointer finds one node at a point
  (`Boxed.pick_iff` of `Whatwg/Svg/Scene/Pick.lean`).
- `Tree.spans_band`: the room of each node is inside the columns of its tree, at the tree's
  depth or below.

What this module does not claim: a room in other units than cells, which is a scale of each
side and is not here; the height of a tree, so no box that holds a whole tree.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- A span moves by whole columns. -/
instance : Moves Nat Span where
  move k s := s.shift k
  move_zero s := by
    cases s
    rfl
  move_move d e s := by
    cases s with
    | mk first last depth =>
      show Span.mk (first + d + e) (last + d + e) depth =
        Span.mk (first + (d + e)) (last + (d + e)) depth
      rw [Nat.add_assoc, Nat.add_assoc]

namespace Span

/-- **The room of a span**, in cells: from its first column to its last, one row high at its
depth. -/
def box (s : Span) : IBox := ⟨s.first, s.depth, s.last + 1, s.depth + 1⟩

/-- **The room of a span moved by columns is its room, moved across.** -/
theorem box_shift (k : Nat) (s : Span) : (s.shift k).box = Moves.move (⟨k, 0⟩ : IVec) s.box := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · show ((s.first + k : Nat) : Int) = (s.first : Int) + (k : Int)
    omega
  · show (s.depth : Int) = (s.depth : Int) + 0
    omega
  · show ((s.last + k : Nat) : Int) + 1 = (s.last : Int) + 1 + (k : Int)
    omega
  · show (s.depth : Int) + 1 = (s.depth : Int) + 1 + 0
    omega

/-- The room of a span whose first column is not after its last has a point. -/
theorem box_solid {s : Span} (h : s.first ≤ s.last) : s.box.Solid := by
  constructor
  · show (s.first : Int) < (s.last : Int) + 1
    omega
  · show (s.depth : Int) < (s.depth : Int) + 1
    omega

end Span

namespace Tree

variable {α : Type}

mutual

/-- **No two nodes of a tree share room.** -/
theorem spans_clear (depth start : Nat) : ∀ t : Tree α,
    (spans depth start t).Pairwise fun p q => p.2.box.Disjoint q.2.box
  | .node v cs => by
    rw [spans]
    refine List.Pairwise.cons (fun q hq => ?_) (spansAll_clear (depth + 1) start cs)
    have h := (spansAll_within (depth + 1) start cs q hq).2.2.2
    refine Or.inr (Or.inr (Or.inl ?_))
    show (depth : Int) + 1 ≤ (q.2.depth : Int)
    omega

/-- The same for a list of trees. -/
theorem spansAll_clear (depth start : Nat) : ∀ ts : List (Tree α),
    (spansAll depth start ts).Pairwise fun p q => p.2.box.Disjoint q.2.box
  | [] => by
    rw [spansAll]
    exact List.Pairwise.nil
  | t :: ts => by
    rw [spansAll]
    refine List.pairwise_append.mpr ⟨spans_clear depth start t,
      spansAll_clear depth (start + leaves t) ts, fun p hp q hq => ?_⟩
    have h := spansAll_apart depth start t ts p q hp hq
    refine Or.inl ?_
    show (p.2.last : Int) + 1 ≤ (q.2.first : Int)
    omega

end

/-- **The room of each node is inside the columns of its tree**, at the tree's depth or
below. -/
theorem spans_band (depth start : Nat) (t : Tree α) (p : α × Span) (h : p ∈ spans depth start t) :
    (start : Int) ≤ p.2.box.x0 ∧ p.2.box.x1 ≤ ((start + leaves t : Nat) : Int) ∧
      (depth : Int) ≤ p.2.box.y0 := by
  obtain ⟨a, _, c, e⟩ := spans_within depth start t p h
  refine ⟨?_, ?_, ?_⟩
  · show (start : Int) ≤ (p.2.first : Int)
    omega
  · show (p.2.last : Int) + 1 ≤ ((start + leaves t : Nat) : Int)
    omega
  · show (depth : Int) ≤ (p.2.depth : Int)
    omega

end Tree

/-! ## A reader and a control -/

-- A reader of `Tree.spans_clear`: a root over two leaves has three rooms, the root's a row
-- above and two columns wide.
#guard (Tree.spans 0 0 (.node "r" [.node "a" [], .node "b" []])).map (fun p => (p.1, p.2.box)) ==
  [("r", ⟨0, 0, 2, 1⟩), ("a", ⟨0, 1, 1, 2⟩), ("b", ⟨1, 1, 2, 2⟩)]

-- A control: two rooms of one tree placed at one start do share room, so the law is of one
-- tree and not of two pictures.
#guard !decide ((Span.box ⟨0, 1, 0⟩).Disjoint (Span.box ⟨1, 1, 0⟩))

end Whatwg.Svg.Scene
