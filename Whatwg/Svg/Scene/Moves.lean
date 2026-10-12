/-!
# Whatwg.Svg.Scene.Moves

Owner: things that move, with no rational number in them (slice S12 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-60).

The geometry of `Whatwg/Svg/Geometry/` computes in `Rat`. In Lean's core library the
definition `Rat.add` reaches `Classical.choice`, so a program that keeps its proofs to `propext`
and `Quot.sound` can neither call that geometry nor cite a law of it. Much of what such a
program proves about a picture needs no number at all: a moved list is the list of the moved
things, and a result that was stored is the result. This layer, `Whatwg/Svg/Scene/`, holds those
laws. It is under the strict ceiling, and it imports nothing of the geometry.

A consumer converts no data to use it. It gives an instance of `Moves` for a type of its own,
and the laws here are then laws of that type.

- `IVec`: a step of whole units along each axis, such as whole pixels. `ICubic`: a cubic segment
  of four such points.
- `Moves δ α`: a thing of `α` moves by an amount of `δ`; moving by nothing changes nothing, and
  two moves are the move by their sum. A list, an optional value and a pair move with their
  parts.
- `Commutes f`: `f` of a moved thing is `f` of the thing, moved. The identity, a composition and
  the map over a list commute.
- `Commutes.stored`: a stored result stands for the computation at a moved input.
  `Commutes.from_origin`: a computation may be done at any place and its result moved back.
  `Commutes.transport`: a law of moves crosses a seam between two kinds of amount.

The geometry is one more instance of this layer (`Whatwg/Svg/Geometry/Grid.lean`).
-/

namespace Whatwg.Svg.Scene

/-- A step of whole units along each axis, or a point of whole units. -/
structure IVec where
  x : Int
  y : Int
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace IVec

/-- No step. -/
instance : Zero IVec := ⟨⟨0, 0⟩⟩

/-- The sum, coordinate by coordinate. -/
instance : Add IVec := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩

/-- The difference, coordinate by coordinate. -/
instance : Sub IVec := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩

/-- The opposite. -/
instance : Neg IVec := ⟨fun p => ⟨-p.x, -p.y⟩⟩

/-- The step with each coordinate multiplied by `k`. -/
def scale (k : Int) (p : IVec) : IVec := ⟨k * p.x, k * p.y⟩

theorem ext {p q : IVec} (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  cases p
  cases q
  cases hx
  cases hy
  rfl

theorem zero_x : (0 : IVec).x = 0 := rfl

theorem zero_y : (0 : IVec).y = 0 := rfl

theorem add_x (p q : IVec) : (p + q).x = p.x + q.x := rfl

theorem add_y (p q : IVec) : (p + q).y = p.y + q.y := rfl

theorem sub_x (p q : IVec) : (p - q).x = p.x - q.x := rfl

theorem sub_y (p q : IVec) : (p - q).y = p.y - q.y := rfl

theorem neg_x (p : IVec) : (-p).x = -p.x := rfl

theorem neg_y (p : IVec) : (-p).y = -p.y := rfl

theorem add_assoc (p q r : IVec) : p + q + r = p + (q + r) :=
  ext (Int.add_assoc p.x q.x r.x) (Int.add_assoc p.y q.y r.y)

theorem add_comm (p q : IVec) : p + q = q + p := ext (Int.add_comm p.x q.x) (Int.add_comm p.y q.y)

theorem add_zero (p : IVec) : p + 0 = p := ext (Int.add_zero p.x) (Int.add_zero p.y)

theorem zero_add (p : IVec) : 0 + p = p := ext (Int.zero_add p.x) (Int.zero_add p.y)

/-- A step and its opposite make no step. -/
theorem neg_add_cancel (p : IVec) : -p + p = 0 :=
  ext (Int.add_left_neg p.x) (Int.add_left_neg p.y)

/-- The step from `q` to `p`, taken from `q`, ends at `p`. -/
theorem sub_add_cancel (p q : IVec) : p - q + q = p :=
  ext (Int.sub_add_cancel p.x q.x) (Int.sub_add_cancel p.y q.y)

theorem sub_self (p : IVec) : p - p = 0 := ext (Int.sub_self p.x) (Int.sub_self p.y)

/-- A multiple of a sum is the sum of the multiples. -/
theorem scale_add (k : Int) (p q : IVec) : scale k (p + q) = scale k p + scale k q :=
  ext (Int.mul_add k p.x q.x) (Int.mul_add k p.y q.y)

end IVec

/-- A thing of `α` that moves by an amount of `δ`. Moving by nothing changes nothing, and two
moves are the move by their sum. A thing moves by amounts of one type, so the type of the amount
is read from the thing. -/
class Moves (δ : outParam Type) (α : Type) [Add δ] [Zero δ] where
  /-- The thing, moved by an amount. -/
  move : δ → α → α
  /-- Moving by nothing changes nothing. -/
  move_zero : ∀ a, move 0 a = a
  /-- Two moves are the move by their sum. -/
  move_move : ∀ d e a, move e (move d a) = move (d + e) a

/-- A step moves by a step: the sum. -/
instance : Moves IVec IVec where
  move d p := p + d
  move_zero := IVec.add_zero
  move_move d e p := IVec.add_assoc p d e

/-- A cubic Bézier segment of whole units: its start, its two controls and its end. A program
that counts in whole pixels, or in whole thousandths of one, keeps its curves so. -/
structure ICubic where
  p0 : IVec
  p1 : IVec
  p2 : IVec
  p3 : IVec
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A segment of whole units moves with its four points. -/
instance : Moves IVec ICubic where
  move d c := ⟨c.p0 + d, c.p1 + d, c.p2 + d, c.p3 + d⟩
  move_zero c := by
    cases c
    simp only [IVec.add_zero]
  move_move d e c := by
    cases c
    simp only [IVec.add_assoc]

section

variable {δ α β γ : Type} [Add δ] [Zero δ]

/-- A list moves with its members. -/
instance [Moves δ α] : Moves δ (List α) where
  move d l := l.map (Moves.move d)
  move_zero l := by
    have h : (Moves.move (0 : δ) : α → α) = id := funext Moves.move_zero
    rw [h, List.map_id]
  move_move d e l := by
    rw [List.map_map]
    exact List.map_congr_left fun a _ => Moves.move_move d e a

/-- An optional value moves where there is one. -/
instance [Moves δ α] : Moves δ (Option α) where
  move d o := o.map (Moves.move d)
  move_zero o := by
    cases o with
    | none => rfl
    | some a => exact congrArg some (Moves.move_zero a)
  move_move d e o := by
    cases o with
    | none => rfl
    | some a => exact congrArg some (Moves.move_move d e a)

/-- A pair moves with its two parts. -/
instance [Moves δ α] [Moves δ β] : Moves δ (α × β) where
  move d p := (Moves.move d p.1, Moves.move d p.2)
  move_zero p := by
    cases p with
    | mk a b => exact congr (congrArg Prod.mk (Moves.move_zero a)) (Moves.move_zero b)
  move_move d e p := by
    cases p with
    | mk a b => exact congr (congrArg Prod.mk (Moves.move_move d e a)) (Moves.move_move d e b)

namespace Moves

/-- A moved list is the list of the moved members. -/
theorem move_list [Moves δ α] (d : δ) (l : List α) : move d l = l.map (move d) := rfl

theorem move_nil [Moves δ α] (d : δ) : move d ([] : List α) = [] := rfl

theorem move_cons [Moves δ α] (d : δ) (a : α) (l : List α) :
    move d (a :: l) = move d a :: move d l := rfl

/-- Two lists in a row, moved, are the two moved lists in a row. -/
theorem move_append [Moves δ α] (d : δ) (l m : List α) :
    move d (l ++ m) = move d l ++ move d m := List.map_append

/-- A moved list has as many members. -/
theorem length_move [Moves δ α] (d : δ) (l : List α) : (move d l).length = l.length :=
  List.length_map _

/-- A moved list, turned, is the turned list, moved. -/
theorem move_reverse [Moves δ α] (d : δ) (l : List α) :
    move d l.reverse = (move d l).reverse := List.map_reverse

theorem move_some [Moves δ α] (d : δ) (a : α) : move d (some a) = some (move d a) := rfl

theorem move_pair [Moves δ α] [Moves δ β] (d : δ) (a : α) (b : β) :
    move d (a, b) = (move d a, move d b) := rfl

end Moves

/-- `f` of a moved thing is `f` of the thing, moved. -/
def Commutes [Moves δ α] [Moves δ β] (f : α → β) : Prop :=
  ∀ (d : δ) (a : α), f (Moves.move d a) = Moves.move d (f a)

namespace Commutes

/-- Doing nothing commutes with a move. -/
theorem id [Moves δ α] : Commutes (fun a : α => a) := fun _ _ => rfl

/-- One function after another commutes with a move, where each does. -/
theorem comp [Moves δ α] [Moves δ β] [Moves δ γ] {g : β → γ} {f : α → β} (hg : Commutes g)
    (hf : Commutes f) : Commutes (fun a => g (f a)) := fun d a => by
  show g (f (Moves.move d a)) = Moves.move d (g (f a))
  rw [hf d a, hg d (f a)]

/-- A function over each member of a list commutes with a move, where the function does. -/
theorem map [Moves δ α] [Moves δ β] {f : α → β} (hf : Commutes f) :
    Commutes (fun l : List α => l.map f) := fun d l => by
  show (l.map (Moves.move d)).map f = (l.map f).map (Moves.move d)
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun a _ => hf d a

/-- A function over each member of a list, its results in a row, commutes with a move. -/
theorem flatMap [Moves δ α] [Moves δ β] {f : α → List β} (hf : Commutes f) :
    Commutes (fun l : List α => l.flatMap f) := fun d l => by
  show (l.map (Moves.move d)).flatMap f = (l.flatMap f).map (Moves.move d)
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append, ih, hf d a]
    rfl

/-- **A stored result stands for the computation at a moved input.** Where `stored` is `f a`,
moving it gives `f` of the moved `a`: the computation is done once. -/
theorem stored [Moves δ α] [Moves δ β] {f : α → β} (hf : Commutes f) {kept : β} {a : α}
    (h : kept = f a) (d : δ) : Moves.move d kept = f (Moves.move d a) := by
  rw [h, hf d a]

/-- **A computation may be done at any place.** With `e` and `d` two moves that make none,
`f a` is `f` of `a` moved by `e`, moved back by `d`. A program computes a figure at an origin
and moves the result to where it stands. -/
theorem from_origin [Moves δ α] [Moves δ β] {f : α → β} (hf : Commutes f) {d e : δ}
    (h : e + d = 0) (a : α) : f a = Moves.move d (f (Moves.move e a)) := by
  rw [← hf d (Moves.move e a), Moves.move_move, h, Moves.move_zero]

/-- **A law of moves crosses a seam.** Let `up` take a thing that moves by amounts of `δ'` to
one that moves by amounts of `δ`, a move by `k` becoming the move by `φ k`; let `f` commute with
moves there; and let `down` take the result back, the move by `φ k` becoming the move by `k`.
Then `down` after `f` after `up` commutes with moves by `δ'`. With `up` the reading of whole
pixels as exact numbers and `down` a rounding, a law of the exact geometry is a law of the
program that counts in whole pixels (`Whatwg/Svg/Geometry/Grid.lean`). -/
theorem transport {δ' ε : Type} [Add δ'] [Zero δ'] [Moves δ' α] [Moves δ β] [Moves δ γ]
    [Moves δ' ε] (φ : δ' → δ) {up : α → β} {f : β → γ} {down : γ → ε}
    (hup : ∀ (k : δ') (a : α), up (Moves.move k a) = Moves.move (φ k) (up a)) (hf : Commutes f)
    (hdown : ∀ (k : δ') (c : γ), down (Moves.move (φ k) c) = Moves.move k (down c)) :
    Commutes (fun a : α => down (f (up a))) := fun k a => by
  show down (f (up (Moves.move k a))) = Moves.move k (down (f (up a)))
  rw [hup k a, hf (φ k) (up a), hdown k (f (up a))]

end Commutes

end

end Whatwg.Svg.Scene
