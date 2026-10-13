import Whatwg.Svg.Scene.Join.Whole

/-!
# WhatwgTest.Svg.UseJoin

The join as a whole (`Whatwg/Svg/Scene/Join/Whole.lean`, slice S22), read at lean4-effect4's
lines and beside d3's own join. The consumer is read at its checkout `6ad8f7b8d`, and d3 at
d3-selection `d8ea8005f87c`. This module imports nothing of either: it restates what it reads.

- **Where `join` and d3 part.** `bindKey` below is d3's `bindKey`
  (`d3-selection/src/selection/data.js`, lines 31 to 73), on lists: its three passes, with a list
  for its map. On pictures with distinct keys it gives the three selections that `join` gives:
  a finite evaluation here, at three pictures, and no theorem. With a key twice the two part,
  and the two controls say how. d3 lets a key name one node and one datum: a second old node
  with a key exits, and a second new datum with a key enters. `join` lets every new thing with a
  key update from the first old thing with it, and exits no old thing whose key a new thing
  has. The coordinator has ruled that `join` stays as it is; its laws ask for distinct keys
  where the difference would show.
- **The consumer's lines that leave** (`sampleLines` of `tools/Tools/View/Motion.lean`, lines 106
  to 108) are the old lines that no new line has the key of, each with its row. `leaving_lines`
  says that they are the exit of the join, by `join_map_key`: the rows go through the join.
- **A panel that moves as one** (the group of `tools/Tools/View/Retained.lean`, lines 117 to
  121): the join of two moved pictures is the join, moved, by `join_move`.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseJoin

open Whatwg.Svg.Scene

/-! ## d3's join by key -/

/-- **d3's `bindKey`, on lists.** `nodes` are the old things and `data` the new ones.

- First pass: the node of each key is the first one with it, and a later node with a key that
  an earlier one has exits.
- Second pass, datum by datum: where the map has a node for the datum's key, the pair updates
  and the key leaves the map; where it has none, the datum enters.
- Third pass: a node that is still in the map exits.

Each selection is in the order d3 has it: by the place of the datum, and for `exit` by the
place of the node. -/
def bindKey {α κ : Type} [BEq κ] (key : α → κ) (nodes data : List α) : Join α :=
  let ns := nodes.zipIdx
  let byKey : List (α × Nat) :=
    ns.foldl (fun m n => if m.any (fun x => key x.1 == key n.1) then m else m ++ [n]) []
  let bound := data.foldl
    (fun (acc : List α × List (α × α) × List (α × Nat)) d =>
      match acc.2.2.find? (fun x => key x.1 == key d) with
      | some n => (acc.1, acc.2.1 ++ [(n.1, d)], acc.2.2.filter fun x => !(key x.1 == key d))
      | none => (acc.1 ++ [d], acc.2.1, acc.2.2))
    ([], [], byKey)
  { enter := bound.1
    update := bound.2.1
    exit := (ns.filter fun n =>
      !(byKey.any fun x => x.2 == n.2) || bound.2.2.any fun x => x.2 == n.2).map (·.1) }

/-- Whether two joins have the same three selections. -/
def same {α : Type} [DecidableEq α] (a b : Join α) : Bool :=
  a.enter == b.enter && a.update == b.update && a.exit == b.exit

-- Distinct keys in both pictures: the two joins agree. A finite evaluation, at a picture with
-- a thing that stays, one that changes, one that leaves and one that is new, at a picture from
-- nothing, and at a picture to nothing.
#guard same (bindKey Prod.fst [(1, "a"), (2, "b"), (3, "c")] [(2, "B"), (4, "d"), (1, "a")])
  (join Prod.fst [(1, "a"), (2, "b"), (3, "c")] [(2, "B"), (4, "d"), (1, "a")])
#guard same (bindKey Prod.fst [] [(1, "a"), (2, "b")]) (join Prod.fst [] [(1, "a"), (2, "b")])
#guard same (bindKey Prod.fst [(1, "a"), (2, "b")] []) (join Prod.fst [(1, "a"), (2, "b")] [])

-- Control: a key twice in the old picture. d3 exits the second old node. `join` exits neither,
-- since a new thing has their key. Both update the new thing from the first old one.
#guard (bindKey Prod.fst [(1, "a"), (1, "b")] [(1, "c")]).exit == [(1, "b")]
#guard (join Prod.fst [(1, "a"), (1, "b")] [(1, "c")]).exit == []
#guard (bindKey Prod.fst [(1, "a"), (1, "b")] [(1, "c")]).update == [((1, "a"), (1, "c"))] &&
  (join Prod.fst [(1, "a"), (1, "b")] [(1, "c")]).update == [((1, "a"), (1, "c"))]

-- Control: a key twice in the new picture. d3 updates the first new datum and enters the
-- second. `join` updates both from the one old thing, and enters neither.
#guard (bindKey Prod.fst [(1, "a")] [(1, "c"), (1, "d")]).update == [((1, "a"), (1, "c"))] &&
  (bindKey Prod.fst [(1, "a")] [(1, "c"), (1, "d")]).enter == [(1, "d")]
#guard (join Prod.fst [(1, "a")] [(1, "c"), (1, "d")]).update ==
    [((1, "a"), (1, "c")), ((1, "a"), (1, "d"))] &&
  (join Prod.fst [(1, "a")] [(1, "c"), (1, "d")]).enter == []

-- Control of `update_self`'s premise. A list with a key twice, joined to itself, updates its
-- second thing from its first: the pairs are not each thing with itself.
#guard (join Prod.fst [(1, "a"), (1, "b")] [(1, "a"), (1, "b")]).update ==
  [((1, "a"), (1, "a")), ((1, "a"), (1, "b"))]

/-! ## The consumer's lines that leave -/

/-- A line of the page, as far as a join reads it: the consumer's `Line`, its key and its
text. -/
structure Line where
  key : String
  text : String
  deriving DecidableEq, Repr

/-- The old lines that no new line has the key of, each with its row: the consumer's `leaving`
of `sampleLines`, before each is drawn. -/
def leaving (old new : List Line) : List (Line × Nat) :=
  old.zipIdx.filter fun p => !(new.any fun n => n.key == p.1.key)

/-- A list with its places, less the places, is the list. -/
theorem map_fst_zipIdx {α : Type} : ∀ (l : List α) (k : Nat), (l.zipIdx k).map Prod.fst = l
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, map_fst_zipIdx l (k + 1)]

/-- **The lines that leave are the exit of the join, each with its row.** The join of the lines
with their rows, by the key of the line, is the join of the lines: taking the row off keeps
every key, so it goes through the join (`join_map_key`). -/
theorem leaving_lines (old new : List Line) :
    (leaving old new).map Prod.fst = (join Line.key old new).exit := by
  have h := join_map_key (fun p : Line × Nat => p.1.key) Line.key Prod.fst (fun _ => rfl)
    old.zipIdx new.zipIdx
  rw [map_fst_zipIdx, map_fst_zipIdx] at h
  rw [h]
  show (old.zipIdx.filter fun p => !(new.any fun n => n.key == p.1.key)).map Prod.fst =
    (old.zipIdx.filter fun p => !(new.zipIdx.any fun n => n.1.key == p.1.key)).map Prod.fst
  have e : ∀ k : String, (new.zipIdx.any fun n => n.1.key == k) = new.any fun n => n.key == k := by
    intro k
    have h2 : ((new.zipIdx.map Prod.fst).any fun n => n.key == k) =
        new.zipIdx.any fun n => n.1.key == k := List.any_map
    rw [map_fst_zipIdx] at h2
    exact h2.symm
  have e2 : (fun p : Line × Nat => !(new.zipIdx.any fun n => n.1.key == p.1.key)) =
      fun p => !(new.any fun n => n.key == p.1.key) := funext fun p => congrArg not (e p.1.key)
  rw [e2]

-- The page before has the lines `a`, `b`, `c`, and the page after `a`, `c`, `d`: the line `b`
-- leaves, from the row `1`.
#guard leaving [⟨"a", "one"⟩, ⟨"b", "two"⟩, ⟨"c", "three"⟩] [⟨"a", "one"⟩, ⟨"c", "3"⟩, ⟨"d", "four"⟩] ==
  [(⟨"b", "two"⟩, 1)]

/-! ## A panel that moves as one -/

/-- A placed item of the graph: the consumer's `Placed`, as far as a join reads it. -/
structure Placed where
  key : String
  x : Int
  y : Int
  w : Int
  deriving DecidableEq, Repr

/-- An item moves by whole pixels. -/
instance : Moves IVec Placed where
  move d p := { p with x := p.x + d.x, y := p.y + d.y }
  move_zero p := by
    cases p
    simp only [IVec.zero_x, IVec.zero_y, Int.add_zero]
  move_move d e p := by
    cases p
    simp only [IVec.add_x, IVec.add_y, Int.add_assoc]

/-- **The join of a panel that moved is the join, moved.** A move keeps the key of an item, so
the three selections of two frames of a panel are the same wherever the panel stands on the
page: `join_move`, read at the consumer's items. -/
example (d : IVec) (old new : List Placed) :
    join Placed.key (Moves.move d old) (Moves.move d new) =
      (join Placed.key old new).map (Moves.move d) :=
  join_move Placed.key (fun _ _ => rfl) d old new

/-- **A frame joined to itself is still**: no item enters or exits, and each updates to itself,
where its keys are distinct. `join_self`, read at the consumer's items. -/
example (frame : List Placed) (h : Distinct Placed.key frame) :
    join Placed.key frame frame = ⟨[], frame.map fun p => (p, p), []⟩ :=
  join_self Placed.key h

end WhatwgTest.Svg.UseJoin
