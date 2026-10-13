import Whatwg.Svg.Scene.Strip
import Whatwg.Svg.Scene.Extent

/-!
# Whatwg.Svg.Scene.Strip.Room

Owner: the room of a box of a lane (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Strip.lean` writes a box of a lane as a state, a left edge and a width, and
says in its header that it has no `IBox` because the layer had none then.
`Whatwg/Svg/Scene/Extent.lean` has it now. This module reads a box of a lane as an `IBox`, given
the ordinate of the lane and its height, which `Strip` leaves to its caller. So the laws of a
lane are laws of rooms.

- `Strip.box y h b`: **the room of a box of a lane** that stands at `y` and is `h` high.

What the laws say:

- `box_shift`: the room of a box moved right is its room, moved across. This is the law that
  `Boxed` asks of a type, for the move that a box of a lane has (`Strip.shift`). The box of a
  lane is a triple and not a type of its own, so it is no instance of `Boxed`; its room is an
  `IBox`, which is.
- `boxes_clear`, `lane_clear`: **no two boxes of a lane share room**, with columns that are not
  negative.
- `boxes_inside`: each box is inside the room of its lane, from `0` to the column times the
  count of the steps.
- `lanes_clear`: a box of one lane and a box of a lane that begins where the first ends, or
  below, share no room.

What this module does not claim: the ordinate or the height of a lane; a room for a point of a
small line.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Strip

variable {σ : Type}

/-- **The room of a box of a lane** that stands at `y` and is `h` high. -/
def box (y h : Int) (b : σ × Int × Int) : IBox := ⟨b.2.1, y, b.2.1 + b.2.2, y + h⟩

/-- **The room of a box moved right is its room, moved across.** -/
theorem box_shift (y h d : Int) (b : σ × Int × Int) :
    box y h (shift d b) = Moves.move (⟨d, 0⟩ : IVec) (box y h b) := by
  refine IBox.ext ?_ ?_ ?_ ?_
  · rfl
  · show y = y + 0
    omega
  · show b.2.1 + d + b.2.2 = b.2.1 + b.2.2 + d
    omega
  · show y + h = y + h + 0
    omega

/-- Boxes that end where a later one begins, or before, share no room. -/
private theorem clear_of_ordered (y h : Int) {bs : List (σ × Int × Int)}
    (ho : bs.Pairwise fun a b => a.2.1 + a.2.2 ≤ b.2.1) :
    bs.Pairwise fun a b => (box y h a).Disjoint (box y h b) :=
  ho.imp fun hab => Or.inl hab

/-- **No two boxes of a lane share room**, with columns that are not negative. -/
theorem boxes_clear [BEq σ] (column : Int) (hc : 0 ≤ column) (y h : Int) (l : List σ) :
    (boxes column l).Pairwise fun a b => (box y h a).Disjoint (box y h b) :=
  clear_of_ordered y h (boxes_ordered column hc l)

/-- The boxes with a state keep the order of the boxes. -/
private theorem present_ordered : ∀ {bs : List (Option σ × Int × Int)},
    bs.Pairwise (fun a b => a.2.1 + a.2.2 ≤ b.2.1) →
    (present bs).Pairwise fun a b => a.2.1 + a.2.2 ≤ b.2.1
  | [], _ => List.Pairwise.nil
  | (none, _) :: rest, h => present_ordered (bs := rest) (List.pairwise_cons.mp h).2
  | (some s, p) :: rest, h => by
    have h' := List.pairwise_cons.mp h
    show ((s, p) :: present rest).Pairwise fun a b => a.2.1 + a.2.2 ≤ b.2.1
    exact List.Pairwise.cons
      (fun b hb => h'.1 (some b.1, b.2) ((mem_present b.1 b.2 rest).mp hb))
      (present_ordered h'.2)

/-- **No two boxes of a lane with absences share room**, with columns that are not negative. -/
theorem lane_clear [BEq σ] (column : Int) (hc : 0 ≤ column) (y h : Int)
    (states : List (Option σ)) :
    (lane column states).Pairwise fun a b => (box y h a).Disjoint (box y h b) :=
  clear_of_ordered y h (present_ordered (boxes_ordered column hc states))

/-- **Each box is inside the room of its lane**: from `0` to the column times the count of the
steps, with columns that are not negative. -/
theorem boxes_inside [BEq σ] (column : Int) (hc : 0 ≤ column) (y h : Int) (l : List σ)
    (b : σ × Int × Int) (hb : b ∈ boxes column l) :
    (box y h b).Inside ⟨0, y, column * (l.length : Int), y + h⟩ := by
  obtain ⟨h1, _, h3⟩ := boxes_within column hc l b hb
  exact ⟨h1, h3, Int.le_refl y, Int.le_refl (y + h)⟩

/-- **Boxes of two lanes share no room**, where the second lane begins where the first ends, or
below. -/
theorem lanes_clear {τ : Type} (y h y' h' : Int) (hy : y + h ≤ y') (a : σ × Int × Int)
    (b : τ × Int × Int) : (box y h a).Disjoint (box y' h' b) :=
  Or.inr (Or.inr (Or.inl hy))

end Strip

/-! ## A reader -/

-- A lane of two runs, a column eight wide, at the ordinate 30 and 12 high: the rooms of its
-- two boxes meet at 16 and share no point.
#guard (Strip.boxes 8 ["a", "a", "b"]).map (Strip.box 30 12) == [⟨0, 30, 16, 42⟩, ⟨16, 30, 24, 42⟩]

end Whatwg.Svg.Scene
