import Whatwg.Svg.Scene.Between

/-!
# Whatwg.Svg.Scene.Cross

Owner: where two lines of a picture cross, in whole numbers (slice S15 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-83).

Two lines that cross have nothing to do with each other at that place, and two lines that join
have. A picture must say which is which, and at a crossing it must say which line passes over.
A crossing costs a reader most, so the count of crossings is a fact that two layouts are
compared by. With points of whole units the test has no tolerance and no doubt: it reads the
signs of four whole numbers. So this layer needs no fraction and stays under the strict ceiling.

- `IVec.turn a b c`: twice the signed area of the triangle `a b c`. Its sign says on which side
  of the way from `a` to `b` the point `c` is.
- `crosses a b c d`: the segments `a b` and `c d` cross at one point that is inside both.
- `Crossing κ`, `crossings above lines`: the crossings of the lines of a picture, each line a
  key and a row of points. `above` says which of two lines is drawn over the other.
- `Cross.pieces`, `Cross.moveLines`: the pieces of a row, and lines moved by one step.
- `Cross.links`, `Cross.inversions`: straight links between two ranks, and how many pairs of
  them stand in opposite orders at the two ranks.

What the laws say of a picture:

- `IVec.turn_move`, `crosses_move`, `crossings_move`: a move changes no turn and no crossing.
  The crossings of a picture are stored with it, and a picture that moves as a whole computes
  them once. `Cross.pieces_commutes` is `Commutes` of `Whatwg/Svg/Scene/Moves.lean`.
- `IVec.turn_swap`, `IVec.turn_swap_first`, `IVec.turn_swap_outer`, `IVec.turn_cycle`: a turn
  changes its sign when two of its points are exchanged, and it is the same from each of its
  points in turn. So `crosses_symm`, `crosses_flip_first`, `crosses_flip_second`: two segments
  cross in either order and in either direction of each.
- `crosses_touch`, `crosses_shared`, `crosses_self`: the test is strict. Segments that share an
  end, a segment that ends on another and segments on one line do not cross. So three edges
  that leave one port have no crossing there, and no gap is cut where lines join.
- `crosses_layered`: two straight links between two ranks cross exactly when their ends stand
  in opposite orders at the two ranks.
- `crosses_same_order`, `crosses_on_way`: where a step keeps the strict order of the upper ends
  of two links and the strict order of their lower ends, the links cross at every moment of the
  step exactly when they cross before it, and after it. No crossing appears on the way and none
  is lost. The ends travel straight at one eased progress in range, with the rounding of `mix`.
- `mem_crossings`, `crossings_sound`, `crossings_complete`, `crossings_complete_either`: the
  crossings found are the pairs of pieces of two lines that cross, each of them and no other.
- `crossings_above`, `Crossing.above_of`, `Crossing.of_comm`: which line is over follows
  `above`, and does not depend on which of the two lines is listed first.
- `crossings_links_length`: the crossings of a layered picture are the inversions of its order.
  A law about the order of a rank is then a law about the picture.

What a caller must supply: its routes as rows of whole points, after it has flattened them, and
a function `above` from its own order, such as depth. The laws of `above` ask that it puts one
of each two lines over the other.

What this module does not claim: that `crosses` is true exactly where a point is on both
segments at parameters strictly between `0` and `1`, which is a law of exact numbers and not of
this layer; a law for links that are curves, such as `bumpY`; the crossings of a line with
itself; the pairs of marks that are too near, which need a box of whole units that this layer
does not have; a count that is the least over all orders of a rank. `crossings` tests each
piece of a line with each piece of every later line. The controls at the end are two steps
that keep no crossing-free order: a swap of two neighbours, and an easing that passes its end.
-/

namespace Whatwg.Svg.Scene

/-! ## The turn of three points -/

/-- Twice the signed area of the triangle `a b c`: more than zero where `c` is to one side of
the way from `a` to `b`, less where it is to the other, zero where the three are on one line. -/
def IVec.turn (a b c : IVec) : Int := (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

namespace IVec

/-- **A turn does not see a move**: three points moved by one step make the same turn. -/
theorem turn_move (a b c v : IVec) : turn (a + v) (b + v) (c + v) = turn a b c := by
  show (b.x + v.x - (a.x + v.x)) * (c.y + v.y - (a.y + v.y)) -
      (b.y + v.y - (a.y + v.y)) * (c.x + v.x - (a.x + v.x)) =
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
  rw [Int.add_sub_add_right, Int.add_sub_add_right, Int.add_sub_add_right, Int.add_sub_add_right]

/-- With its last two points exchanged, a turn is the opposite: the third point is on the other
side. -/
theorem turn_swap (a b c : IVec) : turn a c b = -turn a b c := by
  show (c.x - a.x) * (b.y - a.y) - (c.y - a.y) * (b.x - a.x) =
    -((b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x))
  rw [Int.mul_comm (c.x - a.x) (b.y - a.y), Int.mul_comm (c.y - a.y) (b.x - a.x)]
  omega

/-- A turn is the same from each of its three points in turn. -/
theorem turn_cycle (a b c : IVec) : turn b c a = turn a b c := by
  show (c.x - b.x) * (a.y - b.y) - (c.y - b.y) * (a.x - b.x) =
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
  simp only [Int.sub_mul, Int.mul_sub]
  have h1 := Int.mul_comm c.x a.y
  have h2 := Int.mul_comm c.x b.y
  have h3 := Int.mul_comm b.x b.y
  have h4 := Int.mul_comm c.y a.x
  have h5 := Int.mul_comm c.y b.x
  have h6 := Int.mul_comm a.x a.y
  omega

/-- With its first two points exchanged, a turn is the opposite: a way walked back has its
sides exchanged. -/
theorem turn_swap_first (a b c : IVec) : turn b a c = -turn a b c := by
  rw [turn_cycle c b a, turn_cycle a c b, turn_swap]

/-- With its first and its last point exchanged, a turn is the opposite. -/
theorem turn_swap_outer (a b c : IVec) : turn c b a = -turn a b c := by
  rw [turn_cycle a c b, turn_swap]

/-- A way of no length makes no turn. -/
theorem turn_start (a c : IVec) : turn a a c = 0 := by
  show (a.x - a.x) * (c.y - a.y) - (a.y - a.y) * (c.x - a.x) = 0
  simp only [Int.sub_self, Int.zero_mul]

/-- The start of a way is on the way. -/
theorem turn_at_start (a b : IVec) : turn a b a = 0 := by
  show (b.x - a.x) * (a.y - a.y) - (b.y - a.y) * (a.x - a.x) = 0
  simp only [Int.sub_self, Int.mul_zero]

/-- The end of a way is on the way. -/
theorem turn_at_end (a b : IVec) : turn a b b = 0 := by
  show (b.x - a.x) * (b.y - a.y) - (b.y - a.y) * (b.x - a.x) = 0
  rw [Int.mul_comm (b.x - a.x) (b.y - a.y), Int.sub_self]

end IVec

/-! ## Two segments that cross -/

namespace Cross

/-- Two numbers on the two sides of zero, neither of them zero. -/
def Opposite (s t : Int) : Prop := (0 < s ∧ t < 0) ∨ (s < 0 ∧ 0 < t)

/-- Whether two numbers are on the two sides of zero can be computed. -/
instance (s t : Int) : Decidable (Opposite s t) := inferInstanceAs (Decidable (_ ∨ _))

/-- Two numbers on the two sides of zero are so in either order. -/
theorem opposite_comm (s t : Int) : Opposite s t ↔ Opposite t s :=
  ⟨fun h => h.elim (fun a => Or.inr ⟨a.2, a.1⟩) (fun a => Or.inl ⟨a.2, a.1⟩),
    fun h => h.elim (fun a => Or.inr ⟨a.2, a.1⟩) (fun a => Or.inl ⟨a.2, a.1⟩)⟩

/-- The opposites of two numbers on the two sides of zero are on the two sides of zero. -/
theorem opposite_neg (s t : Int) : Opposite (-s) (-t) ↔ Opposite s t := by
  unfold Opposite
  rw [Int.neg_pos, Int.neg_neg_iff_pos, Int.neg_neg_iff_pos, Int.neg_pos]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

/-- Zero is on neither side of zero. -/
theorem not_opposite_zero_left (t : Int) : ¬ Opposite 0 t := fun h =>
  h.elim (fun a => Int.lt_irrefl 0 a.1) (fun a => Int.lt_irrefl 0 a.1)

/-- Zero is on neither side of zero. -/
theorem not_opposite_zero_right (s : Int) : ¬ Opposite s 0 := fun h =>
  h.elim (fun a => Int.lt_irrefl 0 a.2) (fun a => Int.lt_irrefl 0 a.2)

/-- A positive number times `k` is positive where `k` is, and only there. -/
theorem pos_mul_pos_iff {h k : Int} (hh : 0 < h) : 0 < h * k ↔ 0 < k := by
  cases Int.lt_trichotomy k 0 with
  | inl hk =>
    have hp := Int.mul_neg_of_pos_of_neg hh hk
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · omega
    · omega
  | inr hk =>
    cases hk with
    | inl hk => rw [hk, Int.mul_zero]
    | inr hk => exact ⟨fun _ => hk, fun _ => Int.mul_pos hh hk⟩

/-- A positive number times `k` is negative where `k` is, and only there. -/
theorem pos_mul_neg_iff {h k : Int} (hh : 0 < h) : h * k < 0 ↔ k < 0 := by
  cases Int.lt_trichotomy k 0 with
  | inl hk => exact ⟨fun _ => hk, fun _ => Int.mul_neg_of_pos_of_neg hh hk⟩
  | inr hk =>
    cases hk with
    | inl hk => rw [hk, Int.mul_zero]
    | inr hk =>
      have hp := Int.mul_pos hh hk
      refine ⟨fun h1 => ?_, fun h1 => ?_⟩
      · omega
      · omega

/-- Two numbers, each times one positive number, are on the two sides of zero where the two
are. -/
theorem opposite_mul {h : Int} (s t : Int) (hh : 0 < h) :
    Opposite (h * s) (h * t) ↔ Opposite s t := by
  unfold Opposite
  rw [pos_mul_pos_iff hh, pos_mul_neg_iff hh, pos_mul_neg_iff hh, pos_mul_pos_iff hh]

/-- Two differences are on the two sides of zero where their terms stand in opposite orders. -/
theorem opposite_sub (a b c d : Int) :
    Opposite (a - b) (c - d) ↔ (b < a ∧ c < d) ∨ (a < b ∧ d < c) := by
  unfold Opposite
  constructor
  · intro h
    cases h with
    | inl h =>
      obtain ⟨h1, h2⟩ := h
      refine Or.inl ⟨?_, ?_⟩
      · omega
      · omega
    | inr h =>
      obtain ⟨h1, h2⟩ := h
      refine Or.inr ⟨?_, ?_⟩
      · omega
      · omega
  · intro h
    cases h with
    | inl h =>
      obtain ⟨h1, h2⟩ := h
      refine Or.inl ⟨?_, ?_⟩
      · omega
      · omega
    | inr h =>
      obtain ⟨h1, h2⟩ := h
      refine Or.inr ⟨?_, ?_⟩
      · omega
      · omega

end Cross

open Cross in
/-- **The two straight segments `a b` and `c d` cross at one point that is inside both.** The
ends `c` and `d` are on the two sides of the way from `a` to `b`, neither of them on it, and
the ends `a` and `b` are on the two sides of the way from `c` to `d`. Segments that touch, that
share an end or that run along one line do not cross. -/
def crosses (a b c d : IVec) : Bool :=
  decide (Opposite (IVec.turn a b c) (IVec.turn a b d) ∧
    Opposite (IVec.turn c d a) (IVec.turn c d b))

namespace Cross

/-- Two segments cross where each has the ends of the other on its two sides. -/
theorem crosses_iff (a b c d : IVec) : crosses a b c d = true ↔
    Opposite (IVec.turn a b c) (IVec.turn a b d) ∧
      Opposite (IVec.turn c d a) (IVec.turn c d b) :=
  decide_eq_true_iff

end Cross

open Cross

/-- **A crossing does not see a move**: two segments moved by one step cross where they
crossed. -/
theorem crosses_move (a b c d v : IVec) :
    crosses (a + v) (b + v) (c + v) (d + v) = crosses a b c d := by
  unfold crosses
  rw [IVec.turn_move, IVec.turn_move, IVec.turn_move, IVec.turn_move]

/-- **Two segments cross in either order.** -/
theorem crosses_symm (a b c d : IVec) : crosses c d a b = crosses a b c d :=
  decide_eq_decide.mpr And.comm

/-- A segment crosses another in either of its two directions. -/
theorem crosses_flip_first (a b c d : IVec) : crosses b a c d = crosses a b c d := by
  unfold crosses
  refine decide_eq_decide.mpr ?_
  rw [IVec.turn_swap_first a b c, IVec.turn_swap_first a b d, opposite_neg,
    opposite_comm (IVec.turn c d b) (IVec.turn c d a)]

/-- A segment is crossed by another in either of the other's two directions. -/
theorem crosses_flip_second (a b c d : IVec) : crosses a b d c = crosses a b c d := by
  rw [← crosses_symm a b d c, crosses_flip_first, crosses_symm]

/-- **A touch is no crossing.** Where an end of one segment is on the line of the other, the
two do not cross: a line that ends on another joins it, and two segments on one line run
along each other. -/
theorem crosses_touch (a b c d : IVec)
    (h : IVec.turn a b c = 0 ∨ IVec.turn a b d = 0 ∨ IVec.turn c d a = 0 ∨
      IVec.turn c d b = 0) : crosses a b c d = false := by
  refine decide_eq_false fun hc => ?_
  cases h with
  | inl h =>
    rw [h] at hc
    exact not_opposite_zero_left _ hc.1
  | inr h =>
    cases h with
    | inl h =>
      rw [h] at hc
      exact not_opposite_zero_right _ hc.1
    | inr h =>
      cases h with
      | inl h =>
        rw [h] at hc
        exact not_opposite_zero_left _ hc.2
      | inr h =>
        rw [h] at hc
        exact not_opposite_zero_right _ hc.2

/-- **Segments that share an end do not cross.** So three edges that leave one port have no
crossing there. -/
theorem crosses_shared (a b c d : IVec) (h : c = a ∨ c = b ∨ d = a ∨ d = b) :
    crosses a b c d = false := by
  refine crosses_touch a b c d ?_
  cases h with
  | inl h =>
    rw [h]
    exact Or.inl (IVec.turn_at_start a b)
  | inr h =>
    cases h with
    | inl h =>
      rw [h]
      exact Or.inl (IVec.turn_at_end a b)
    | inr h =>
      cases h with
      | inl h =>
        rw [h]
        exact Or.inr (Or.inl (IVec.turn_at_start a b))
      | inr h =>
        rw [h]
        exact Or.inr (Or.inl (IVec.turn_at_end a b))

/-- A segment does not cross itself. -/
theorem crosses_self (a b : IVec) : crosses a b a b = false :=
  crosses_shared a b a b (Or.inl rfl)

/-! ## Links between two ranks -/

namespace Cross

/-- The turn of a link from the rank at `y` to the rank at `y'` with a point of its own upper
rank: the height between the ranks times how far the point is to the left. -/
theorem turn_upper (x₁ x₂ x₃ y y' : Int) :
    IVec.turn ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ = (y' - y) * (x₁ - x₃) := by
  show (x₂ - x₁) * (y - y) - (y' - y) * (x₃ - x₁) = (y' - y) * (x₁ - x₃)
  rw [Int.sub_self, Int.mul_zero]
  simp only [Int.mul_sub]
  omega

/-- The turn of a link from the rank at `y` to the rank at `y'` with a point of its lower rank:
the height between the ranks times how far the point is to the left of the link's end. -/
theorem turn_lower (x₁ x₂ x₄ y y' : Int) :
    IVec.turn ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₄, y'⟩ = (y' - y) * (x₂ - x₄) := by
  show (x₂ - x₁) * (y' - y) - (y' - y) * (x₄ - x₁) = (y' - y) * (x₂ - x₄)
  rw [Int.mul_comm (x₂ - x₁) (y' - y)]
  simp only [Int.mul_sub]
  omega

end Cross

/-- **Two straight links between two ranks cross exactly when their ends stand in opposite
orders.** The links go from `x₁` to `x₂` and from `x₃` to `x₄`, from the rank at `y` to the
rank at `y'` below it. -/
theorem crosses_layered (x₁ x₂ x₃ x₄ y y' : Int) (h : y < y') :
    crosses ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ ⟨x₄, y'⟩ = true ↔
      (x₁ < x₃ ∧ x₄ < x₂) ∨ (x₃ < x₁ ∧ x₂ < x₄) := by
  have hh : 0 < y' - y := Int.sub_pos.mpr h
  rw [crosses_iff, turn_upper, turn_lower, turn_upper, turn_lower, opposite_mul _ _ hh,
    opposite_mul _ _ hh, opposite_sub, opposite_sub]
  exact ⟨fun a => a.2, fun a => ⟨a.symm, a⟩⟩

/-- Two links between two ranks whose ends stand in one order at both ranks do not cross. -/
theorem crosses_layered_apart (x₁ x₂ x₃ x₄ y y' : Int) (h : y < y')
    (hs : (x₁ < x₃ ∧ x₂ < x₄) ∨ (x₃ < x₁ ∧ x₄ < x₂)) :
    crosses ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ ⟨x₄, y'⟩ = false := by
  refine Bool.eq_false_iff.mpr fun hc => ?_
  cases (crosses_layered x₁ x₂ x₃ x₄ y y' h).mp hc with
  | inl a =>
    cases hs with
    | inl b => exact Int.lt_irrefl _ (Int.lt_trans a.2 b.2)
    | inr b => exact Int.lt_irrefl _ (Int.lt_trans a.1 b.1)
  | inr a =>
    cases hs with
    | inl b => exact Int.lt_irrefl _ (Int.lt_trans a.1 b.1)
    | inr b => exact Int.lt_irrefl _ (Int.lt_trans a.2 b.2)

/-- **Two layered pictures with the same orders have the same crossing.** Where the upper ends
of two links stand in one strict order in both pictures, and the lower ends too, the links
cross in the second picture exactly when they cross in the first. The ranks may stand at other
heights in the second picture. -/
theorem crosses_same_order (x₁ x₂ x₃ x₄ y y' u₁ u₂ u₃ u₄ v v' : Int) (hy : y < y')
    (hv : v < v') (hupper : (x₁ < x₃ ∧ u₁ < u₃) ∨ (x₃ < x₁ ∧ u₃ < u₁))
    (hlower : (x₂ < x₄ ∧ u₂ < u₄) ∨ (x₄ < x₂ ∧ u₄ < u₂)) :
    crosses ⟨u₁, v⟩ ⟨u₂, v'⟩ ⟨u₃, v⟩ ⟨u₄, v'⟩ = crosses ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ ⟨x₄, y'⟩ := by
  cases hupper with
  | inl a =>
    cases hlower with
    | inl b =>
      rw [crosses_layered_apart u₁ u₂ u₃ u₄ v v' hv (Or.inl ⟨a.2, b.2⟩),
        crosses_layered_apart x₁ x₂ x₃ x₄ y y' hy (Or.inl ⟨a.1, b.1⟩)]
    | inr b =>
      rw [(crosses_layered u₁ u₂ u₃ u₄ v v' hv).mpr (Or.inl ⟨a.2, b.2⟩),
        (crosses_layered x₁ x₂ x₃ x₄ y y' hy).mpr (Or.inl ⟨a.1, b.1⟩)]
  | inr a =>
    cases hlower with
    | inl b =>
      rw [(crosses_layered u₁ u₂ u₃ u₄ v v' hv).mpr (Or.inr ⟨a.2, b.2⟩),
        (crosses_layered x₁ x₂ x₃ x₄ y y' hy).mpr (Or.inr ⟨a.1, b.1⟩)]
    | inr b =>
      rw [crosses_layered_apart u₁ u₂ u₃ u₄ v v' hv (Or.inr ⟨a.2, b.2⟩),
        crosses_layered_apart x₁ x₂ x₃ x₄ y y' hy (Or.inr ⟨a.1, b.1⟩)]

/-- **No crossing appears on the way, and none is lost.** Take two links between two ranks in
two pictures, every end moved the straight way at one eased progress `e` in range. Where the
upper ends stand in one strict order in both pictures, and the lower ends too, the links cross
at that moment exactly when they cross in the first picture. By `crosses_same_order` that is
when they cross in the second. So a step that keeps the order of each rank makes no crossing
and undoes none at any moment, with the rounding of `mix`. -/
theorem crosses_on_way (x₁ x₂ x₃ x₄ y y' u₁ u₂ u₃ u₄ v v' e : Int) (h0 : 0 ≤ e)
    (h1 : e ≤ 1000) (hy : y < y') (hv : v < v')
    (hupper : (x₁ < x₃ ∧ u₁ < u₃) ∨ (x₃ < x₁ ∧ u₃ < u₁))
    (hlower : (x₂ < x₄ ∧ u₂ < u₄) ∨ (x₄ < x₂ ∧ u₄ < u₂)) :
    crosses ⟨mix x₁ u₁ e, mix y v e⟩ ⟨mix x₂ u₂ e, mix y' v' e⟩ ⟨mix x₃ u₃ e, mix y v e⟩
        ⟨mix x₄ u₄ e, mix y' v' e⟩ =
      crosses ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ ⟨x₄, y'⟩ := by
  have hm : mix y v e < mix y' v' e := mix_gap y v y' v' 1 e h0 h1 hy hv
  refine crosses_same_order x₁ x₂ x₃ x₄ y y' _ _ _ _ _ _ hy hm ?_ ?_
  · cases hupper with
    | inl a => exact Or.inl ⟨a.1, mix_gap x₁ u₁ x₃ u₃ 1 e h0 h1 a.1 a.2⟩
    | inr a => exact Or.inr ⟨a.1, mix_gap x₃ u₃ x₁ u₁ 1 e h0 h1 a.1 a.2⟩
  · cases hlower with
    | inl a => exact Or.inl ⟨a.1, mix_gap x₂ u₂ x₄ u₄ 1 e h0 h1 a.1 a.2⟩
    | inr a => exact Or.inr ⟨a.1, mix_gap x₄ u₄ x₂ u₂ 1 e h0 h1 a.1 a.2⟩

/-! ## The crossings of the lines of a picture -/

/-- A crossing of two lines: their keys, and which piece of each. The piece `n` of a line goes
from its point `n` to its point `n + 1`. -/
structure Crossing (κ : Type) where
  /-- the line that is drawn over the other -/
  over : κ
  /-- the line that passes under -/
  under : κ
  /-- the piece of the line that is drawn over -/
  overAt : Nat
  /-- the piece of the line that passes under -/
  underAt : Nat
  deriving DecidableEq, Repr

variable {κ : Type}

/-- The crossing of the piece `p` of a line `k` and the piece `q` of a line `k'`: the line that
`above` puts over the other is `over`. -/
def Crossing.of (above : κ → κ → Bool) (k k' : κ) (p q : Nat) : Crossing κ :=
  bif above k k' then ⟨k, k', p, q⟩ else ⟨k', k, q, p⟩

/-- **Which line is over follows `above`.** Where `above` puts one of two lines over the
other, whichever is asked first, it puts the `over` of their crossing over its `under`. -/
theorem Crossing.above_of (above : κ → κ → Bool) (k k' : κ) (p q : Nat)
    (h : above k k' = false → above k' k = true) :
    above (Crossing.of above k k' p q).over (Crossing.of above k k' p q).under = true := by
  unfold Crossing.of
  cases hk : above k k' with
  | false => exact h hk
  | true => exact hk

/-- **A crossing does not depend on which of its two lines is listed first**, where `above`
puts exactly one of the two over the other. -/
theorem Crossing.of_comm (above : κ → κ → Bool) (k k' : κ) (p q : Nat)
    (h : above k' k = !above k k') : Crossing.of above k' k q p = Crossing.of above k k' p q := by
  unfold Crossing.of
  rw [h]
  cases above k k' <;> rfl

namespace Cross

/-- The pieces of a row of points: each point with the next. -/
def pieces : List IVec → List (IVec × IVec)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: pieces (b :: rest)

/-- The crossings of one piece `s`, the piece `p` of a line `k`, with the pieces `ts` of a line
`k'`, the first of them the piece `q`. -/
def pieceCrossings (above : κ → κ → Bool) (k k' : κ) (p : Nat) (s : IVec × IVec) :
    Nat → List (IVec × IVec) → List (Crossing κ)
  | _, [] => []
  | q, t :: ts =>
    (bif crosses s.1 s.2 t.1 t.2 then [Crossing.of above k k' p q] else []) ++
      pieceCrossings above k k' p s (q + 1) ts

/-- The crossings of the pieces `ss` of a line `k`, the first of them the piece `p`, with all
the pieces `ts` of a line `k'`. -/
def lineCrossings (above : κ → κ → Bool) (k k' : κ) (ts : List (IVec × IVec)) :
    Nat → List (IVec × IVec) → List (Crossing κ)
  | _, [] => []
  | p, s :: ss => pieceCrossings above k k' p s 0 ts ++ lineCrossings above k k' ts (p + 1) ss

/-- The crossings of a line `k` of pieces `ss` with each of the lines listed after it. -/
def withLater (above : κ → κ → Bool) (k : κ) (ss : List (IVec × IVec)) :
    List (κ × List IVec) → List (Crossing κ)
  | [] => []
  | l :: rest => lineCrossings above k l.1 (pieces l.2) 0 ss ++ withLater above k ss rest

/-- The lines, each moved by one step. A key does not move. -/
def moveLines (v : IVec) (lines : List (κ × List IVec)) : List (κ × List IVec) :=
  lines.map fun l => (l.1, Moves.move v l.2)

end Cross

/-- **The crossings of the lines, each a row of points.** `above` says which of two lines is
drawn over the other. Each pair of pieces of two lines that cross is one crossing; a line's
crossings with itself are not listed. -/
def crossings (above : κ → κ → Bool) : List (κ × List IVec) → List (Crossing κ)
  | [] => []
  | l :: rest => withLater above l.1 (pieces l.2) rest ++ crossings above rest

namespace Cross

/-- **The piece `p` of a row goes from its point `p` to its point `p + 1`.** -/
theorem pieces_getElem? : ∀ (ps : List IVec) (p : Nat) (a b : IVec),
    (pieces ps)[p]? = some (a, b) ↔ ps[p]? = some a ∧ ps[p + 1]? = some b
  | [], p, a, b => by
    show ([] : List (IVec × IVec))[p]? = some (a, b) ↔
      ([] : List IVec)[p]? = some a ∧ ([] : List IVec)[p + 1]? = some b
    rw [List.getElem?_nil, List.getElem?_nil]
    exact ⟨fun h => (nomatch h), fun h => nomatch h.1⟩
  | [x], p, a, b => by
    show ([] : List (IVec × IVec))[p]? = some (a, b) ↔
      [x][p]? = some a ∧ [x][p + 1]? = some b
    rw [List.getElem?_nil, List.getElem?_cons_succ, List.getElem?_nil]
    exact ⟨fun h => (nomatch h), fun h => nomatch h.2⟩
  | x :: y :: rest, 0, a, b => by
    show ((x, y) :: pieces (y :: rest))[0]? = some (a, b) ↔
      (x :: y :: rest)[0]? = some a ∧ (x :: y :: rest)[0 + 1]? = some b
    rw [List.getElem?_cons_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_cons_zero]
    exact ⟨fun h => by
      cases h
      exact ⟨rfl, rfl⟩, fun h => by
      cases h.1
      cases h.2
      rfl⟩
  | x :: y :: rest, p + 1, a, b => by
    show ((x, y) :: pieces (y :: rest))[p + 1]? = some (a, b) ↔
      (x :: y :: rest)[p + 1]? = some a ∧ (x :: y :: rest)[p + 1 + 1]? = some b
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact pieces_getElem? (y :: rest) p a b

/-- **The pieces of a moved row are its pieces, moved.** -/
theorem pieces_commutes : Commutes pieces := fun v ps => by
  show pieces (Moves.move v ps) = Moves.move v (pieces ps)
  induction ps with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      show (a + v, b + v) :: pieces (Moves.move v (b :: rest')) =
        (a + v, b + v) :: Moves.move v (pieces (b :: rest'))
      rw [ih]

/-- The crossings of a piece with the pieces of another line: each is a piece that it crosses,
and each piece that it crosses is one. -/
theorem mem_pieceCrossings (above : κ → κ → Bool) (k k' : κ) (p : Nat) (s : IVec × IVec) :
    ∀ (ts : List (IVec × IVec)) (q0 : Nat) (x : Crossing κ),
    x ∈ pieceCrossings above k k' p s q0 ts ↔
      ∃ q t, ts[q]? = some t ∧ crosses s.1 s.2 t.1 t.2 = true ∧
        x = Crossing.of above k k' p (q0 + q)
  | [], _, _ => ⟨fun h => (nomatch h), fun ⟨_, _, h, _⟩ => by
      rw [List.getElem?_nil] at h
      nomatch h⟩
  | t :: ts, q0, x => by
    show x ∈ (bif crosses s.1 s.2 t.1 t.2 then [Crossing.of above k k' p q0] else []) ++
      pieceCrossings above k k' p s (q0 + 1) ts ↔ _
    rw [List.mem_append, mem_pieceCrossings above k k' p s ts (q0 + 1) x]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        cases hc : crosses s.1 s.2 t.1 t.2 with
        | false =>
          rw [hc] at h1
          nomatch h1
        | true =>
          rw [hc] at h1
          exact ⟨0, t, List.getElem?_cons_zero, hc, List.mem_singleton.mp h1⟩
      | inr h2 =>
        obtain ⟨q, t', hq, hc, e⟩ := h2
        refine ⟨q + 1, t', ?_, hc, ?_⟩
        · rw [List.getElem?_cons_succ]
          exact hq
        · rw [e, Nat.add_assoc, Nat.add_comm 1 q]
    · intro ⟨q, t', hq, hc, e⟩
      cases q with
      | zero =>
        rw [List.getElem?_cons_zero] at hq
        cases hq
        refine Or.inl ?_
        rw [hc]
        exact List.mem_singleton.mpr e
      | succ q' =>
        rw [List.getElem?_cons_succ] at hq
        refine Or.inr ⟨q', t', hq, hc, ?_⟩
        rw [e, Nat.add_assoc, Nat.add_comm 1 q']

/-- The crossings of two lines: each is a piece of one and a piece of the other that cross, and
each such pair is one. -/
theorem mem_lineCrossings (above : κ → κ → Bool) (k k' : κ) (ts : List (IVec × IVec)) :
    ∀ (ss : List (IVec × IVec)) (p0 : Nat) (x : Crossing κ),
    x ∈ lineCrossings above k k' ts p0 ss ↔
      ∃ p s q t, ss[p]? = some s ∧ ts[q]? = some t ∧ crosses s.1 s.2 t.1 t.2 = true ∧
        x = Crossing.of above k k' (p0 + p) q
  | [], _, _ => ⟨fun h => (nomatch h), fun ⟨_, _, _, _, h, _⟩ => by
      rw [List.getElem?_nil] at h
      nomatch h⟩
  | s :: ss, p0, x => by
    show x ∈ pieceCrossings above k k' p0 s 0 ts ++ lineCrossings above k k' ts (p0 + 1) ss ↔ _
    rw [List.mem_append, mem_pieceCrossings, mem_lineCrossings above k k' ts ss (p0 + 1) x]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        obtain ⟨q, t, hq, hc, e⟩ := h1
        refine ⟨0, s, q, t, List.getElem?_cons_zero, hq, hc, ?_⟩
        rw [e, Nat.zero_add]
        rfl
      | inr h2 =>
        obtain ⟨p, s', q, t, hp, hq, hc, e⟩ := h2
        refine ⟨p + 1, s', q, t, ?_, hq, hc, ?_⟩
        · rw [List.getElem?_cons_succ]
          exact hp
        · rw [e, Nat.add_assoc, Nat.add_comm 1 p]
    · intro ⟨p, s', q, t, hp, hq, hc, e⟩
      cases p with
      | zero =>
        rw [List.getElem?_cons_zero] at hp
        cases hp
        refine Or.inl ⟨q, t, hq, hc, ?_⟩
        rw [e, Nat.zero_add]
        rfl
      | succ p' =>
        rw [List.getElem?_cons_succ] at hp
        refine Or.inr ⟨p', s', q, t, hp, hq, hc, ?_⟩
        rw [e, Nat.add_assoc, Nat.add_comm 1 p']

/-- The crossings of a line with the lines listed after it: each is a piece of the line and a
piece of a later line that cross, and each such pair is one. -/
theorem mem_withLater (above : κ → κ → Bool) (k : κ) (ss : List (IVec × IVec)) :
    ∀ (rest : List (κ × List IVec)) (x : Crossing κ),
    x ∈ withLater above k ss rest ↔
      ∃ (j : Nat) (l : κ × List IVec) (p : Nat) (s : IVec × IVec) (q : Nat) (t : IVec × IVec),
        rest[j]? = some l ∧ ss[p]? = some s ∧ (pieces l.2)[q]? = some t ∧
        crosses s.1 s.2 t.1 t.2 = true ∧ x = Crossing.of above k l.1 p q
  | [], _ => ⟨fun h => (nomatch h), fun ⟨_, _, _, _, _, _, h, _⟩ => by
      rw [List.getElem?_nil] at h
      nomatch h⟩
  | l :: rest, x => by
    show x ∈ lineCrossings above k l.1 (pieces l.2) 0 ss ++ withLater above k ss rest ↔ _
    rw [List.mem_append, mem_lineCrossings, mem_withLater above k ss rest x]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        obtain ⟨p, s, q, t, hp, hq, hc, e⟩ := h1
        refine ⟨0, l, p, s, q, t, List.getElem?_cons_zero, hp, hq, hc, ?_⟩
        rw [e, Nat.zero_add]
      | inr h2 =>
        obtain ⟨j, l', p, s, q, t, hj, hp, hq, hc, e⟩ := h2
        refine ⟨j + 1, l', p, s, q, t, ?_, hp, hq, hc, e⟩
        rw [List.getElem?_cons_succ]
        exact hj
    · intro ⟨j, l', p, s, q, t, hj, hp, hq, hc, e⟩
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at hj
        cases hj
        refine Or.inl ⟨p, s, q, t, hp, hq, hc, ?_⟩
        rw [e, Nat.zero_add]
      | succ j' =>
        rw [List.getElem?_cons_succ] at hj
        exact Or.inr ⟨j', l', p, s, q, t, hj, hp, hq, hc, e⟩

end Cross

/-- **The crossings found are the pairs of pieces of two lines that cross, each of them and no
other.** A crossing is listed exactly when it is the crossing of the piece `p` of one line and
the piece `q` of a line listed after it, and the two pieces cross. -/
theorem mem_crossings (above : κ → κ → Bool) : ∀ (lines : List (κ × List IVec))
    (x : Crossing κ), x ∈ crossings above lines ↔
      ∃ (i j : Nat) (l l' : κ × List IVec) (p : Nat) (s : IVec × IVec) (q : Nat)
        (t : IVec × IVec), i < j ∧ lines[i]? = some l ∧ lines[j]? = some l' ∧
        (pieces l.2)[p]? = some s ∧ (pieces l'.2)[q]? = some t ∧
        crosses s.1 s.2 t.1 t.2 = true ∧ x = Crossing.of above l.1 l'.1 p q
  | [], _ => ⟨fun h => (nomatch h), fun ⟨_, _, _, _, _, _, _, _, _, h, _⟩ => by
      rw [List.getElem?_nil] at h
      nomatch h⟩
  | l0 :: rest, x => by
    show x ∈ withLater above l0.1 (pieces l0.2) rest ++ crossings above rest ↔ _
    rw [List.mem_append, mem_withLater, mem_crossings above rest x]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        obtain ⟨j, l', p, s, q, t, hj, hp, hq, hc, e⟩ := h1
        refine ⟨0, j + 1, l0, l', p, s, q, t, Nat.succ_pos j, List.getElem?_cons_zero, ?_, hp,
          hq, hc, e⟩
        rw [List.getElem?_cons_succ]
        exact hj
      | inr h2 =>
        obtain ⟨i, j, l, l', p, s, q, t, hij, hi, hj, hp, hq, hc, e⟩ := h2
        refine ⟨i + 1, j + 1, l, l', p, s, q, t, Nat.succ_lt_succ hij, ?_, ?_, hp, hq, hc, e⟩
        · rw [List.getElem?_cons_succ]
          exact hi
        · rw [List.getElem?_cons_succ]
          exact hj
    · intro ⟨i, j, l, l', p, s, q, t, hij, hi, hj, hp, hq, hc, e⟩
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero i)
      | succ j' =>
        rw [List.getElem?_cons_succ] at hj
        cases i with
        | zero =>
          rw [List.getElem?_cons_zero] at hi
          cases hi
          exact Or.inl ⟨j', l', p, s, q, t, hj, hp, hq, hc, e⟩
        | succ i' =>
          rw [List.getElem?_cons_succ] at hi
          exact Or.inr ⟨i', j', l, l', p, s, q, t, Nat.lt_of_succ_lt_succ hij, hi, hj, hp, hq,
            hc, e⟩

/-- **Each crossing found is a crossing**: a piece of one line, from its point `p` to the next,
and a piece of a line listed after it, from its point `q` to the next, that cross. -/
theorem crossings_sound (above : κ → κ → Bool) (lines : List (κ × List IVec)) (x : Crossing κ)
    (h : x ∈ crossings above lines) :
    ∃ (i j : Nat) (k k' : κ) (ps qs : List IVec) (p q : Nat) (a b c d : IVec), i < j ∧
      lines[i]? = some (k, ps) ∧ lines[j]? = some (k', qs) ∧ ps[p]? = some a ∧
      ps[p + 1]? = some b ∧ qs[q]? = some c ∧ qs[q + 1]? = some d ∧
      crosses a b c d = true ∧ x = Crossing.of above k k' p q := by
  obtain ⟨i, j, l, l', p, s, q, t, hij, hi, hj, hp, hq, hc, e⟩ := (mem_crossings above lines x).mp h
  have hp' := (pieces_getElem? l.2 p s.1 s.2).mp hp
  have hq' := (pieces_getElem? l'.2 q t.1 t.2).mp hq
  exact ⟨i, j, l.1, l'.1, l.2, l'.2, p, q, s.1, s.2, t.1, t.2, hij, hi, hj, hp'.1, hp'.2,
    hq'.1, hq'.2, hc, e⟩

/-- **Every crossing of two lines is found**: where the piece from the point `p` of one line
and the piece from the point `q` of a line listed after it cross, their crossing is listed. -/
theorem crossings_complete (above : κ → κ → Bool) (lines : List (κ × List IVec)) (i j : Nat)
    (k k' : κ) (ps qs : List IVec) (p q : Nat) (a b c d : IVec) (hij : i < j)
    (hi : lines[i]? = some (k, ps)) (hj : lines[j]? = some (k', qs)) (hpa : ps[p]? = some a)
    (hpb : ps[p + 1]? = some b) (hqc : qs[q]? = some c) (hqd : qs[q + 1]? = some d)
    (hc : crosses a b c d = true) : Crossing.of above k k' p q ∈ crossings above lines :=
  (mem_crossings above lines _).mpr ⟨i, j, (k, ps), (k', qs), p, (a, b), q, (c, d), hij, hi, hj,
    (pieces_getElem? ps p a b).mpr ⟨hpa, hpb⟩, (pieces_getElem? qs q c d).mpr ⟨hqc, hqd⟩, hc,
    rfl⟩

/-- **Every crossing of two lines is found, whichever of the two is listed first.** The
crossing is listed as the line listed first makes it. Where `above` puts exactly one of the two
lines over the other, the two are one crossing (`Crossing.of_comm`). -/
theorem crossings_complete_either (above : κ → κ → Bool) (lines : List (κ × List IVec))
    (i j : Nat) (k k' : κ) (ps qs : List IVec) (p q : Nat) (a b c d : IVec) (hij : i ≠ j)
    (hi : lines[i]? = some (k, ps)) (hj : lines[j]? = some (k', qs)) (hpa : ps[p]? = some a)
    (hpb : ps[p + 1]? = some b) (hqc : qs[q]? = some c) (hqd : qs[q + 1]? = some d)
    (hc : crosses a b c d = true) :
    Crossing.of above k k' p q ∈ crossings above lines ∨
      Crossing.of above k' k q p ∈ crossings above lines := by
  cases Nat.lt_or_ge i j with
  | inl lt =>
    exact Or.inl (crossings_complete above lines i j k k' ps qs p q a b c d lt hi hj hpa hpb
      hqc hqd hc)
  | inr ge =>
    refine Or.inr (crossings_complete above lines j i k' k qs ps q p c d a b
      (Nat.lt_of_le_of_ne ge fun e => hij e.symm) hj hi hqc hqd hpa hpb ?_)
    rw [crosses_symm]
    exact hc

/-- **Which line is over follows `above`**, at every crossing found, where `above` puts one of
each two lines over the other, whichever is asked first. -/
theorem crossings_above (above : κ → κ → Bool) (lines : List (κ × List IVec))
    (htotal : ∀ k k', above k k' = false → above k' k = true) (x : Crossing κ)
    (h : x ∈ crossings above lines) : above x.over x.under = true := by
  obtain ⟨_, _, l, l', p, _, q, _, _, _, _, _, _, _, e⟩ := (mem_crossings above lines x).mp h
  rw [e]
  exact Crossing.above_of above l.1 l'.1 p q (htotal l.1 l'.1)

namespace Cross

/-- The crossings of a moved piece with moved pieces are its crossings. -/
theorem pieceCrossings_move (above : κ → κ → Bool) (k k' : κ) (p : Nat) (v : IVec)
    (s : IVec × IVec) : ∀ (ts : List (IVec × IVec)) (q : Nat),
    pieceCrossings above k k' p (Moves.move v s) q (Moves.move v ts) =
      pieceCrossings above k k' p s q ts
  | [], _ => rfl
  | t :: ts, q => by
    show (bif crosses (s.1 + v) (s.2 + v) (t.1 + v) (t.2 + v) then [Crossing.of above k k' p q]
        else []) ++ pieceCrossings above k k' p (Moves.move v s) (q + 1) (Moves.move v ts) =
      (bif crosses s.1 s.2 t.1 t.2 then [Crossing.of above k k' p q] else []) ++
        pieceCrossings above k k' p s (q + 1) ts
    rw [crosses_move, pieceCrossings_move above k k' p v s ts (q + 1)]

/-- The crossings of two moved lines are their crossings. -/
theorem lineCrossings_move (above : κ → κ → Bool) (k k' : κ) (v : IVec)
    (ts : List (IVec × IVec)) : ∀ (ss : List (IVec × IVec)) (p : Nat),
    lineCrossings above k k' (Moves.move v ts) p (Moves.move v ss) =
      lineCrossings above k k' ts p ss
  | [], _ => rfl
  | s :: ss, p => by
    show pieceCrossings above k k' p (Moves.move v s) 0 (Moves.move v ts) ++
        lineCrossings above k k' (Moves.move v ts) (p + 1) (Moves.move v ss) =
      pieceCrossings above k k' p s 0 ts ++ lineCrossings above k k' ts (p + 1) ss
    rw [pieceCrossings_move, lineCrossings_move above k k' v ts ss (p + 1)]

/-- The crossings of a moved line with moved later lines are its crossings. -/
theorem withLater_move (above : κ → κ → Bool) (k : κ) (v : IVec) (ss : List (IVec × IVec)) :
    ∀ rest : List (κ × List IVec),
    withLater above k (Moves.move v ss) (moveLines v rest) = withLater above k ss rest
  | [] => rfl
  | l :: rest => by
    show lineCrossings above k l.1 (pieces (Moves.move v l.2)) 0 (Moves.move v ss) ++
        withLater above k (Moves.move v ss) (moveLines v rest) =
      lineCrossings above k l.1 (pieces l.2) 0 ss ++ withLater above k ss rest
    rw [pieces_commutes v l.2, lineCrossings_move, withLater_move above k v ss rest]

end Cross

/-- **The crossings of moved lines are the crossings.** So they are stored with a retained
picture, and a picture that moves as a whole computes them once. -/
theorem crossings_move (above : κ → κ → Bool) (v : IVec) : ∀ lines : List (κ × List IVec),
    crossings above (moveLines v lines) = crossings above lines
  | [] => rfl
  | l :: rest => by
    show withLater above l.1 (pieces (Moves.move v l.2)) (moveLines v rest) ++
        crossings above (moveLines v rest) =
      withLater above l.1 (pieces l.2) rest ++ crossings above rest
    rw [pieces_commutes v l.2, withLater_move, crossings_move above v rest]

/-! ## The crossings of a layered picture are the inversions of its order -/

namespace Cross

/-- Two links between two ranks, each the abscissa of its upper end and of its lower, stand in
opposite orders at the two ranks. -/
def inverted (s t : Int × Int) : Bool :=
  decide ((s.1 < t.1 ∧ t.2 < s.2) ∨ (t.1 < s.1 ∧ s.2 < t.2))

/-- How many of the links `ts` stand in the opposite order to the link `s`. -/
def inversionsWith (s : Int × Int) : List (Int × Int) → Nat
  | [] => 0
  | t :: ts => (bif inverted s t then 1 else 0) + inversionsWith s ts

/-- **The inversions of the links between two ranks**: how many pairs of them stand in opposite
orders at the two ranks. -/
def inversions : List (Int × Int) → Nat
  | [] => 0
  | s :: ss => inversionsWith s ss + inversions ss

/-- Straight links between the rank at `y` and the rank at `y'` as lines: for each its key, the
abscissa of its upper end and the abscissa of its lower end. -/
def links (y y' : Int) (ends : List (κ × Int × Int)) : List (κ × List IVec) :=
  ends.map fun l => (l.1, [⟨l.2.1, y⟩, ⟨l.2.2, y'⟩])

/-- Two links between two ranks cross where they are inverted. -/
theorem crosses_inverted (x₁ x₂ x₃ x₄ y y' : Int) (h : y < y') :
    crosses ⟨x₁, y⟩ ⟨x₂, y'⟩ ⟨x₃, y⟩ ⟨x₄, y'⟩ = inverted (x₁, x₂) (x₃, x₄) := by
  rw [Bool.eq_iff_iff, crosses_layered x₁ x₂ x₃ x₄ y y' h]
  exact decide_eq_true_iff.symm

/-- Two lines of one piece each have one crossing where the pieces cross, and none
elsewhere. -/
theorem lineCrossings_one_length (above : κ → κ → Bool) (k k' : κ) (a b c d : IVec) :
    (lineCrossings above k k' [(c, d)] 0 [(a, b)]).length = bif crosses a b c d then 1 else 0 := by
  show (((bif crosses a b c d then [Crossing.of above k k' 0 0] else []) ++ []) ++ []).length =
    bif crosses a b c d then 1 else 0
  cases crosses a b c d <;> rfl

/-- A link has as many crossings with the links listed after it as stand in the opposite order
to it. -/
theorem withLater_links_length (above : κ → κ → Bool) (k : κ) (x x' y y' : Int) (h : y < y') :
    ∀ rest : List (κ × Int × Int),
    (withLater above k [(⟨x, y⟩, ⟨x', y'⟩)] (links y y' rest)).length =
      inversionsWith (x, x') (rest.map fun l => l.2)
  | [] => rfl
  | l :: rest => by
    show (lineCrossings above k l.1 [(⟨l.2.1, y⟩, ⟨l.2.2, y'⟩)] 0 [(⟨x, y⟩, ⟨x', y'⟩)] ++
        withLater above k [(⟨x, y⟩, ⟨x', y'⟩)] (links y y' rest)).length =
      (bif inverted (x, x') (l.2.1, l.2.2) then 1 else 0) +
        inversionsWith (x, x') (rest.map fun l => l.2)
    rw [List.length_append, withLater_links_length above k x x' y y' h rest,
      lineCrossings_one_length, crosses_inverted x x' l.2.1 l.2.2 y y' h]

end Cross

/-- **The crossings of a layered picture are the inversions of its order.** Straight links
between two ranks have as many crossings as pairs of them stand in opposite orders at the two
ranks, whatever `above` is. So a law about the order of a rank is a law about the picture. -/
theorem crossings_links_length (above : κ → κ → Bool) (y y' : Int) (h : y < y') :
    ∀ ends : List (κ × Int × Int),
    (crossings above (links y y' ends)).length = inversions (ends.map fun l => l.2)
  | [] => rfl
  | l :: rest => by
    show (withLater above l.1 [(⟨l.2.1, y⟩, ⟨l.2.2, y'⟩)] (links y y' rest) ++
        crossings above (links y y' rest)).length =
      inversionsWith (l.2.1, l.2.2) (rest.map fun l => l.2) +
        inversions (rest.map fun l => l.2)
    rw [List.length_append, crossings_links_length above y y' h rest,
      withLater_links_length above l.1 l.2.1 l.2.2 y y' h rest]

/-! ## Finite evaluations -/

-- The two diagonals of a square cross.
#guard crosses ⟨0, 0⟩ ⟨10, 10⟩ ⟨0, 10⟩ ⟨10, 0⟩

-- A touch is no crossing: two edges that leave one point, and an edge that ends on another.
#guard !crosses ⟨0, 0⟩ ⟨10, 10⟩ ⟨0, 0⟩ ⟨10, 0⟩
#guard !crosses ⟨0, 0⟩ ⟨10, 0⟩ ⟨5, 0⟩ ⟨5, 10⟩

-- Two segments that run along one line and overlap do not cross. This is intended: they share
-- a stretch, and no one point is where one passes over the other.
#guard !crosses ⟨0, 0⟩ ⟨10, 0⟩ ⟨5, 0⟩ ⟨15, 0⟩

-- The layered law on a rank of three links, from the abscissae 0, 10 and 20 to 20, 0 and 10:
-- the first link is inverted with each of the others, and the other two are not inverted.
#guard crossings (fun k k' : Nat => k < k')
    (Cross.links 0 10 [(1, 0, 20), (2, 10, 0), (3, 20, 10)]) = [⟨1, 2, 0, 0⟩, ⟨1, 3, 0, 0⟩]
#guard Cross.inversions [(0, 20), (10, 0), (20, 10)] = 2

-- A line of two pieces over a straight line: each piece crosses it once. With `above` the
-- other way, the same two crossings have their two lines exchanged.
#guard crossings (fun k k' : Nat => k < k')
    [(1, [⟨0, 0⟩, ⟨10, 10⟩, ⟨20, 0⟩]), (2, [⟨0, 5⟩, ⟨20, 5⟩])] = [⟨1, 2, 0, 0⟩, ⟨1, 2, 1, 0⟩]
#guard crossings (fun k k' : Nat => k' < k)
    [(1, [⟨0, 0⟩, ⟨10, 10⟩, ⟨20, 0⟩]), (2, [⟨0, 5⟩, ⟨20, 5⟩])] = [⟨2, 1, 0, 0⟩, ⟨2, 1, 0, 1⟩]

-- A control for the orders of `crosses_on_way`: a swap of two neighbours. Neither picture has
-- a crossing. Both orders are opposite in the two pictures, and the lower ends pass each other
-- before the upper ends do. At the eased progress 400 the links cross.
#guard !crosses ⟨0, 0⟩ ⟨0, 10⟩ ⟨10, 0⟩ ⟨4, 10⟩
#guard !crosses ⟨10, 0⟩ ⟨10, 10⟩ ⟨0, 0⟩ ⟨0, 10⟩
#guard crosses ⟨mix 0 10 400, 0⟩ ⟨mix 0 10 400, 10⟩ ⟨mix 10 0 400, 0⟩ ⟨mix 4 0 400, 10⟩

-- A control for the range of `crosses_on_way`: both pictures have the two orders, and none has
-- a crossing. At the eased progress 1200, past the end, the upper ends have passed each other.
#guard !crosses ⟨0, 0⟩ ⟨0, 10⟩ ⟨10, 0⟩ ⟨10, 10⟩
#guard !crosses ⟨100, 0⟩ ⟨0, 10⟩ ⟨101, 0⟩ ⟨10, 10⟩
#guard crosses ⟨mix 0 100 1200, 0⟩ ⟨mix 0 0 1200, 10⟩ ⟨mix 10 101 1200, 0⟩ ⟨mix 10 10 1200, 10⟩

end Whatwg.Svg.Scene
