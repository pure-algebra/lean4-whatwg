import Whatwg.Svg.Scene.Motion
import Whatwg.Svg.Geometry.Cubic.Laws
import Whatwg.Svg.Geometry.Box
import Whatwg.Svg.Geometry.Rational.Laws

/-!
# Whatwg.Svg.Geometry.Grid

Owner: the seam between whole units and exact numbers (slice S12 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-63).

A program that draws counts in whole units: whole pixels, or whole thousandths of one. The
geometry of this package computes in `Rat`. This module is where one becomes the other, and it
says what crosses unchanged.

- `Vec.ofGrid s p` reads a point of whole counts of `1 / s` as an exact point. It is one to one,
  and it takes a sum to the sum.
- `Vec.toGrid s v` rounds an exact point down to such counts, and `Vec.nearGrid s v` to the
  nearest. A point of the grid comes back as itself (`toGrid_ofGrid`).
- **Rounding commutes with a move by a whole count** (`toGrid_add_ofGrid`,
  `nearGrid_add_ofGrid`). So a law that says "the figure of a moved input is the figure, moved"
  holds after the rounding too, for every move by whole units. `Commutes.grid` states that for
  any computation on segments: it is `Commutes.transport` of
  `Whatwg/Svg/Scene/Moves.lean` at this seam.
- `Vec.snap s v` is the rounded point as an exact point again: the end of a stage of a
  computation. A stage that ends so keeps its numbers short, and is within one unit of the grid
  of the exact stage (`snap_le`, `lt_snap_add`).
- `mix_eq_floor`: the whole-number `mix` of `Whatwg/Svg/Scene/Motion.lean` is the exact step
  between two values, rounded down.

The exact types are instances of `Moves`: a point, a segment and a box move by a `Vec`.

What this module does not claim: that two stages that each round are the rounding of the two
exact stages. They are not, and a program that rounds at every division differs from one that
rounds once by up to a unit at each.
-/

namespace Whatwg.Svg.Value

open Whatwg.Svg.Scene (IVec ICubic Moves Commutes)

/-! ## The exact types move -/

/-- No step: the origin. -/
instance : Zero Vec := ⟨Vec.zero⟩

/-- A point moves by a step: the sum. -/
instance : Moves Vec Vec where
  move d p := p + d
  move_zero := Vec.add_zero
  move_move d e p := Vec.add_assoc p d e

/-- A segment moves with its four points. -/
instance : Moves Vec Cubic where
  move d c := c.move d
  move_zero := Cubic.move_zero
  move_move := Cubic.move_move

namespace Box

/-- A box moved by nothing is the box. -/
theorem move_zero (b : Box) : b.move Vec.zero = b := by
  simp only [move, Vec.zero]
  cases b
  simp only [Box.mk.injEq]
  grind

/-- A box moved twice is the box moved by the sum. -/
theorem move_move (d e : Vec) (b : Box) : (b.move d).move e = b.move (d + e) := by
  simp only [move, Vec.add_def, Box.mk.injEq]
  grind

end Box

/-- A box moves with its corners. -/
instance : Moves Vec Box where
  move d b := b.move d
  move_zero := Box.move_zero
  move_move := Box.move_move

/-- A move of a segment, as the class has it, is `Cubic.move`. -/
theorem Cubic.moves_eq (d : Vec) (c : Cubic) : Moves.move d c = c.move d := rfl

/-- A move of a list of segments, as the class has it, is the map of `Cubic.move`. -/
theorem Cubic.moves_list (d : Vec) (cs : List Cubic) : Moves.move d cs = cs.map (Cubic.move d) :=
  rfl

/-! ## Whole counts as exact points -/

/-- A whole number as a natural number of parts is more than zero where the count is. -/
theorem rat_natCast_pos {s : Nat} (hs : 0 < s) : (0 : Rat) < (s : Rat) := Rat.natCast_pos.mpr hs

/-- A quotient by a number that is not zero, times that number, is the dividend. -/
theorem rat_div_mul_cancel {a s : Rat} (h : s ≠ 0) : a / s * s = a := by grind

namespace Vec

/-- The point of whole counts of `1 / s`: `ofGrid 1000 ⟨1500, 250⟩` is `(3/2, 1/4)`. -/
def ofGrid (s : Nat) (p : IVec) : Vec := ⟨(p.x : Rat) / (s : Rat), (p.y : Rat) / (s : Rat)⟩

/-- The point rounded down to whole counts of `1 / s`, along each axis. -/
def toGrid (s : Nat) (v : Vec) : IVec := ⟨(v.x * (s : Rat)).floor, (v.y * (s : Rat)).floor⟩

/-- The point rounded to the nearest whole counts of `1 / s`, a half going up. -/
def nearGrid (s : Nat) (v : Vec) : IVec :=
  ⟨(v.x * (s : Rat) + 1 / 2).floor, (v.y * (s : Rat) + 1 / 2).floor⟩

/-- The point rounded down to the grid of `1 / s`, as an exact point: the end of a stage. -/
def snap (s : Nat) (v : Vec) : Vec := ofGrid s (toGrid s v)

/-- The point rounded to the nearest point of the grid of `1 / s`, as an exact point. -/
def snapNear (s : Nat) (v : Vec) : Vec := ofGrid s (nearGrid s v)

/-- No count is the origin. -/
theorem ofGrid_zero (s : Nat) : ofGrid s 0 = Vec.zero := by
  apply Vec.ext <;> simp only [ofGrid, IVec.zero_x, IVec.zero_y, Vec.zero] <;> grind

/-- The point of a sum of counts is the sum of the points. -/
theorem ofGrid_add (s : Nat) (p q : IVec) : ofGrid s (p + q) = ofGrid s p + ofGrid s q := by
  apply Vec.ext <;>
    simp only [ofGrid, IVec.add_x, IVec.add_y, Vec.add_def, Rat.intCast_add, Rat.div_def,
      Rat.add_mul]

/-- The coordinates of a point of the grid, in counts. -/
theorem ofGrid_mul {s : Nat} (hs : 0 < s) (p : IVec) :
    (ofGrid s p).x * (s : Rat) = (p.x : Rat) ∧ (ofGrid s p).y * (s : Rat) = (p.y : Rat) :=
  ⟨rat_div_mul_cancel (Rat.ne_of_gt (rat_natCast_pos hs)),
    rat_div_mul_cancel (Rat.ne_of_gt (rat_natCast_pos hs))⟩

/-- **A point of the grid comes back as itself.** -/
theorem toGrid_ofGrid {s : Nat} (hs : 0 < s) (p : IVec) : toGrid s (ofGrid s p) = p := by
  apply IVec.ext
  · show ((ofGrid s p).x * (s : Rat)).floor = p.x
    rw [(ofGrid_mul hs p).1, Rat.floor_intCast]
  · show ((ofGrid s p).y * (s : Rat)).floor = p.y
    rw [(ofGrid_mul hs p).2, Rat.floor_intCast]

/-- Two counts with one point are one count: the reading is one to one. -/
theorem ofGrid_injective {s : Nat} (hs : 0 < s) {p q : IVec} (h : ofGrid s p = ofGrid s q) :
    p = q := by
  rw [← toGrid_ofGrid hs p, ← toGrid_ofGrid hs q, h]

/-- **Rounding down commutes with a move by a whole count.** -/
theorem toGrid_add_ofGrid {s : Nat} (hs : 0 < s) (v : Vec) (k : IVec) :
    toGrid s (v + ofGrid s k) = toGrid s v + k := by
  apply IVec.ext
  · show ((v + ofGrid s k).x * (s : Rat)).floor = (v.x * (s : Rat)).floor + k.x
    rw [← Rat.floor_add_intCast, ← (ofGrid_mul hs k).1, ← Rat.add_mul]
    rfl
  · show ((v + ofGrid s k).y * (s : Rat)).floor = (v.y * (s : Rat)).floor + k.y
    rw [← Rat.floor_add_intCast, ← (ofGrid_mul hs k).2, ← Rat.add_mul]
    rfl

/-- **Rounding to the nearest commutes with a move by a whole count.** -/
theorem nearGrid_add_ofGrid {s : Nat} (hs : 0 < s) (v : Vec) (k : IVec) :
    nearGrid s (v + ofGrid s k) = nearGrid s v + k := by
  have hx := (ofGrid_mul hs k).1
  have hy := (ofGrid_mul hs k).2
  apply IVec.ext
  · show ((v + ofGrid s k).x * (s : Rat) + 1 / 2).floor = (v.x * (s : Rat) + 1 / 2).floor + k.x
    rw [← Rat.floor_add_intCast, ← hx]
    congr 1
    simp only [Vec.add_def]
    grind
  · show ((v + ofGrid s k).y * (s : Rat) + 1 / 2).floor = (v.y * (s : Rat) + 1 / 2).floor + k.y
    rw [← Rat.floor_add_intCast, ← hy]
    congr 1
    simp only [Vec.add_def]
    grind

/-- A point of the grid is its own nearest. -/
theorem nearGrid_ofGrid {s : Nat} (hs : 0 < s) (p : IVec) : nearGrid s (ofGrid s p) = p := by
  have h := nearGrid_add_ofGrid hs Vec.zero p
  rw [Vec.zero_add] at h
  rw [h]
  apply IVec.ext
  · show ((0 : Rat) * (s : Rat) + 1 / 2).floor + p.x = p.x
    have e : ((0 : Rat) * (s : Rat) + 1 / 2).floor = 0 :=
      Decimal.rat_floor_eq (by grind) (by grind)
    rw [e, Int.zero_add]
  · show ((0 : Rat) * (s : Rat) + 1 / 2).floor + p.y = p.y
    have e : ((0 : Rat) * (s : Rat) + 1 / 2).floor = 0 :=
      Decimal.rat_floor_eq (by grind) (by grind)
    rw [e, Int.zero_add]

/-- **The end of a stage commutes with a move by a whole count.** -/
theorem snap_add_ofGrid {s : Nat} (hs : 0 < s) (v : Vec) (k : IVec) :
    snap s (v + ofGrid s k) = snap s v + ofGrid s k := by
  rw [snap, toGrid_add_ofGrid hs, ofGrid_add]
  rfl

/-- The nearest point of the grid commutes with a move by a whole count. -/
theorem snapNear_add_ofGrid {s : Nat} (hs : 0 < s) (v : Vec) (k : IVec) :
    snapNear s (v + ofGrid s k) = snapNear s v + ofGrid s k := by
  rw [snapNear, nearGrid_add_ofGrid hs, ofGrid_add]
  rfl

/-- A point of the grid is its own stage end. -/
theorem snap_ofGrid {s : Nat} (hs : 0 < s) (p : IVec) : snap s (ofGrid s p) = ofGrid s p := by
  rw [snap, toGrid_ofGrid hs]

/-- Ending a stage twice is ending it once. -/
theorem snap_snap {s : Nat} (hs : 0 < s) (v : Vec) : snap s (snap s v) = snap s v :=
  snap_ofGrid hs _

/-- The end of a stage is at or below the exact point, along each axis. -/
theorem snap_le {s : Nat} (hs : 0 < s) (v : Vec) : (snap s v).x ≤ v.x ∧ (snap s v).y ≤ v.y := by
  have h := rat_natCast_pos hs
  have hx := Rat.floor_le (v.x * (s : Rat))
  have hy := Rat.floor_le (v.y * (s : Rat))
  constructor
  · show ((v.x * (s : Rat)).floor : Rat) / (s : Rat) ≤ v.x
    have e : v.x = v.x * (s : Rat) / (s : Rat) := by grind
    rw [e]
    exact Decimal.rat_div_le_div h (by rw [← e]; exact hx)
  · show ((v.y * (s : Rat)).floor : Rat) / (s : Rat) ≤ v.y
    have e : v.y = v.y * (s : Rat) / (s : Rat) := by grind
    rw [e]
    exact Decimal.rat_div_le_div h (by rw [← e]; exact hy)

/-- The exact point is less than one unit of the grid above the end of its stage, along each
axis. -/
theorem lt_snap_add {s : Nat} (hs : 0 < s) (v : Vec) :
    v.x < (snap s v).x + 1 / (s : Rat) ∧ v.y < (snap s v).y + 1 / (s : Rat) := by
  have h := rat_natCast_pos hs
  have hx := Rat.lt_floor_add_one (v.x * (s : Rat))
  have hy := Rat.lt_floor_add_one (v.y * (s : Rat))
  rw [Rat.intCast_add] at hx hy
  constructor
  · show v.x < ((v.x * (s : Rat)).floor : Rat) / (s : Rat) + 1 / (s : Rat)
    have e : ((v.x * (s : Rat)).floor : Rat) / (s : Rat) + 1 / (s : Rat) =
        (((v.x * (s : Rat)).floor : Rat) + ((1 : Int) : Rat)) / (s : Rat) := by grind
    have e' : v.x = v.x * (s : Rat) / (s : Rat) := by grind
    rw [e, e']
    exact Decimal.rat_div_lt_div h (by rw [← e']; exact hx)
  · show v.y < ((v.y * (s : Rat)).floor : Rat) / (s : Rat) + 1 / (s : Rat)
    have e : ((v.y * (s : Rat)).floor : Rat) / (s : Rat) + 1 / (s : Rat) =
        (((v.y * (s : Rat)).floor : Rat) + ((1 : Int) : Rat)) / (s : Rat) := by grind
    have e' : v.y = v.y * (s : Rat) / (s : Rat) := by grind
    rw [e, e']
    exact Decimal.rat_div_lt_div h (by rw [← e']; exact hy)

end Vec

/-! ## Segments -/

namespace Cubic

/-- The segment of four points of whole counts of `1 / s`. -/
def ofGrid (s : Nat) (c : ICubic) : Cubic :=
  ⟨Vec.ofGrid s c.p0, Vec.ofGrid s c.p1, Vec.ofGrid s c.p2, Vec.ofGrid s c.p3⟩

/-- The segment with its four points rounded down to whole counts of `1 / s`. -/
def toGrid (s : Nat) (c : Cubic) : ICubic :=
  ⟨Vec.toGrid s c.p0, Vec.toGrid s c.p1, Vec.toGrid s c.p2, Vec.toGrid s c.p3⟩

/-- The segment with its four points rounded to the nearest whole counts of `1 / s`. -/
def nearGrid (s : Nat) (c : Cubic) : ICubic :=
  ⟨Vec.nearGrid s c.p0, Vec.nearGrid s c.p1, Vec.nearGrid s c.p2, Vec.nearGrid s c.p3⟩

/-- A segment of the grid comes back as itself. -/
theorem toGrid_ofGrid {s : Nat} (hs : 0 < s) (c : ICubic) : toGrid s (ofGrid s c) = c := by
  cases c
  simp only [ofGrid, toGrid, Vec.toGrid_ofGrid hs]

/-- A moved segment of whole counts reads as the segment, moved by the reading of the move. -/
theorem ofGrid_move (s : Nat) (k : IVec) (c : ICubic) :
    ofGrid s (Moves.move k c) = (ofGrid s c).move (Vec.ofGrid s k) := by
  cases c
  simp only [ofGrid, Moves.move, Vec.ofGrid_add, Cubic.move, Cubic.map]

/-- A segment moved by a whole count rounds down to the rounded segment, moved. -/
theorem toGrid_move {s : Nat} (hs : 0 < s) (k : IVec) (c : Cubic) :
    toGrid s (c.move (Vec.ofGrid s k)) = Moves.move k (toGrid s c) := by
  simp only [toGrid, Cubic.move, Cubic.map, Vec.toGrid_add_ofGrid hs, Moves.move]

/-- A segment moved by a whole count rounds to the nearest as the rounded segment, moved. -/
theorem nearGrid_move {s : Nat} (hs : 0 < s) (k : IVec) (c : Cubic) :
    nearGrid s (c.move (Vec.ofGrid s k)) = Moves.move k (nearGrid s c) := by
  simp only [nearGrid, Cubic.move, Cubic.map, Vec.nearGrid_add_ofGrid hs, Moves.move]

end Cubic

/-- **A law of the exact geometry is a law on the grid.** A computation `f` on lists of
segments that commutes with moves, read from whole counts and rounded down to them again,
commutes with moves by whole counts. A program that keeps whole pixels calls `f` so, and its own
move law follows with no proof about rounding. -/
theorem _root_.Whatwg.Svg.Scene.Commutes.grid {s : Nat} (hs : 0 < s) {f : List Cubic → List Cubic}
    (hf : Commutes f) :
    Commutes (fun cs : List ICubic => ((f (cs.map (Cubic.ofGrid s))).map (Cubic.toGrid s))) :=
  Commutes.transport (Vec.ofGrid s) (up := fun cs : List ICubic => cs.map (Cubic.ofGrid s))
    (down := fun cs : List Cubic => cs.map (Cubic.toGrid s))
    (fun k cs => by
      show (cs.map (Moves.move k)).map (Cubic.ofGrid s) =
        (cs.map (Cubic.ofGrid s)).map (Cubic.move (Vec.ofGrid s k))
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => Cubic.ofGrid_move s k c)
    hf
    (fun k cs => by
      show (cs.map (Cubic.move (Vec.ofGrid s k))).map (Cubic.toGrid s) =
        (cs.map (Cubic.toGrid s)).map (Moves.move k)
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => Cubic.toGrid_move hs k c)

/-- **A change of shape between two lists of exact segments**, each rounded to the nearest
whole counts of `1 / s`: the change of an edge whose two ends move differently, or of an
outline that is drawn again. Two lists of one length go into each other segment by segment. -/
def _root_.Whatwg.Svg.Scene.Change.morphOf (s : Nat) (old new : List Cubic) :
    Whatwg.Svg.Scene.Change :=
  .morph (old.map (Cubic.nearGrid s)) (new.map (Cubic.nearGrid s))
/-! ## The whole-number step is the exact step, rounded down -/

/-- The quotient of whole numbers that rounds down is the floor of the exact quotient, for a
divisor of a thousand. -/
theorem rat_floor_div_thousand (n : Int) : ((n : Rat) / 1000).floor = n / 1000 := by
  have h1 := Rat.intCast_le_intCast.mpr (Int.ediv_mul_le n (b := 1000) (by decide))
  have h2 := Rat.intCast_lt_intCast.mpr (Int.lt_ediv_add_one_mul_self n (b := 1000) (by decide))
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat] at h1 h2
  apply Decimal.rat_floor_eq
  · generalize ((n / 1000 : Int) : Rat) = k at h1 h2 ⊢
    grind
  · generalize ((n / 1000 : Int) : Rat) = k at h1 h2 ⊢
    grind

/-- **The whole-number `mix` is the exact step, rounded down**: `mix u v e` is the floor of the
value `e` per mille of the way from `u` to `v`. -/
theorem mix_eq_floor (u v e : Int) :
    Whatwg.Svg.Scene.mix u v e =
      ((v : Rat) + ((u : Rat) - (v : Rat)) * (1000 - (e : Rat)) / 1000).floor := by
  have hx : (((u - v) * (1000 - e) : Int) : Rat) = ((u : Rat) - (v : Rat)) * (1000 - (e : Rat)) := by
    simp only [Rat.intCast_mul, Rat.intCast_sub, Rat.intCast_ofNat]
  have e1 : (v : Rat) + ((u : Rat) - (v : Rat)) * (1000 - (e : Rat)) / 1000 =
      (((u - v) * (1000 - e) : Int) : Rat) / 1000 + ((v : Int) : Rat) := by
    rw [hx]
    grind
  rw [e1, Rat.floor_add_intCast, rat_floor_div_thousand]
  show v + (u - v) * (1000 - e) / 1000 = (u - v) * (1000 - e) / 1000 + v
  exact Int.add_comm _ _

end Whatwg.Svg.Value
