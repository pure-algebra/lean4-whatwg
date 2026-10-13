import Whatwg.Svg.Scene.Pick
import Whatwg.Svg.Scene.Row.Spread

/-!
# WhatwgTest.Svg.UsePlaces

The pointer of lean4-effect4's view and the last pass of its places across, on
`Whatwg/Svg/Scene/Pick.lean` and `Whatwg/Svg/Scene/Row/Spread.lean` (slice S22). The consumer is
read at its checkout `6ad8f7b8d`. This module imports nothing of that package: it restates the
consumer's types under the consumer's names, with the fields that the two functions read.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `Rect.holds`, `keyAt`, `pick` (`tools/Tools/View/Picture.lean`, lines 206 to 216) | `pick`, on `Boxed.pick` over the pointer boxes of the calls; `pick0` is the consumer's own text, kept to evaluate the two against each other |
| `pick_append` (lines 231 to 234) | `pick_append`, from `Boxed.pick_append` |
| `sep`, `spread`, `Apart` (`tools/Tools/View/Place.lean`, lines 62 to 64 and 108 to 121) | the same three, as the consumer writes them, and `spread_eq`, `apart_iff`: they are `Row.spread` and `Row.Apart` at the consumer's distance |
| `spread_apart` (lines 123 to 130) | `spread_apart`, from `Row.spread_apart` |

**What the consumer gains.**

- `pick_exact`: where no two pointer boxes share a pixel, the pointer answers a key exactly
  when the pixel is in a box of that key. The consumer has the order of two lists and no law
  of what answers.
- `pick_move`: the pointer over a moved picture answers what it answered.
- `spread_all`: every two items of a rank are apart by their half widths and a gap. The
  consumer's `spread_apart` says it of an item and the one before it, and its docstring
  concludes that two items of one rank never share a cell. This is the law that says so.
- `spread_leftmost`: no row that is apart and gives each item its place or more stands left of
  the one that `spread` gives, at any item.

The guards: one evaluation of `pick` against the consumer's own text at every pixel of a small
picture, which no theorem here covers; and controls for the premises of `pick_exact` and
`spread_all`.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UsePlaces

open Whatwg.Svg.Scene

/-! ## The pointer -/

/-- One call that reaches the target, as far as the pointer reads it: a pointer box, or any
other call. The consumer's `Dev`. -/
inductive Dev where
  | hit (r : IBox)
  | other

/-- A call with the key of what it draws: the consumer's `Keyed`. -/
structure Keyed (α : Type) where
  key : String
  call : α

/-- A pointer box with its key. It takes room and moves, so it is a thing of the kit. -/
structure Hit where
  key : String
  box : IBox
  deriving DecidableEq, Repr

instance : Moves IVec Hit where
  move d h := ⟨h.key, Moves.move d h.box⟩
  move_zero h := congrArg (Hit.mk h.key) (Moves.move_zero h.box)
  move_move d e h := congrArg (Hit.mk h.key) (Moves.move_move d e h.box)

instance : Boxed Hit where
  box h := h.box
  box_move _ _ := rfl

/-- The pointer boxes of some calls, in their order. -/
def hits (ds : List (Keyed Dev)) : List Hit :=
  ds.filterMap fun d =>
    match d.call with
    | .hit r => some ⟨d.key, r⟩
    | .other => none

/-- **The key under a pixel**: the last pointer box that holds it answers. The consumer's
`pick`, on the kit. -/
def pick (ds : List (Keyed Dev)) (x y : Int) : Option String :=
  (Boxed.pick (hits ds) ⟨x, y⟩).map (·.key)

/-- A box holds a pixel: the consumer's `Rect.holds`, as it writes it. -/
def holds (r : IBox) (x y : Int) : Bool :=
  decide (r.x0 ≤ x) && decide (x < r.x1) && decide (r.y0 ≤ y) && decide (y < r.y1)

/-- The key that one call answers at a pixel: the consumer's `keyAt`, as it writes it. -/
def keyAt (x y : Int) (d : Keyed Dev) : Option String :=
  match d.call with
  | .hit r => if holds r x y then some d.key else none
  | _ => none

/-- The consumer's `pick`, as it writes it. No law here reads it: a guard below evaluates the
port against it. -/
def pick0 (ds : List (Keyed Dev)) (x y : Int) : Option String :=
  ds.reverse.findSome? (keyAt x y)

theorem hits_append (a b : List (Keyed Dev)) : hits (a ++ b) = hits a ++ hits b :=
  List.filterMap_append

/-- **A later call answers the pointer before an earlier one**: the consumer's `pick_append`. -/
theorem pick_append (a b : List (Keyed Dev)) (x y : Int) :
    pick (a ++ b) x y = (pick b x y).or (pick a x y) := by
  rw [pick, hits_append, Boxed.pick_append]
  show Option.map (fun h : Hit => h.key)
      ((Boxed.pick (hits b) ⟨x, y⟩).or (Boxed.pick (hits a) ⟨x, y⟩)) =
    (Option.map (fun h : Hit => h.key) (Boxed.pick (hits b) ⟨x, y⟩)).or
      (Option.map (fun h : Hit => h.key) (Boxed.pick (hits a) ⟨x, y⟩))
  cases Boxed.pick (hits b) ⟨x, y⟩ <;> rfl

/-- **Where no two pointer boxes share a pixel, the pointer answers a key exactly when the
pixel is in a box of that key.** -/
theorem pick_exact {ds : List (Keyed Dev)}
    (hc : (hits ds).Pairwise fun a b => a.box.Disjoint b.box) (x y : Int) (k : String) :
    pick ds x y = some k ↔ ∃ h ∈ hits ds, h.key = k ∧ h.box.Holds ⟨x, y⟩ := by
  constructor
  · intro hp
    cases hf : Boxed.pick (hits ds) ⟨x, y⟩ with
    | none =>
      rw [pick, hf] at hp
      exact nomatch hp
    | some h =>
      rw [pick, hf] at hp
      exact ⟨h, (Boxed.pick_some hf).1, Option.some.inj hp, (Boxed.pick_some hf).2⟩
  · intro ⟨h, hm, hk, hh⟩
    rw [pick, (Boxed.pick_iff hc).mpr ⟨hm, hh⟩]
    exact congrArg some hk

/-- The pointer boxes of calls moved by whole pixels. The consumer's `Call.move`, at a pointer
box. -/
def moveAll (d : IVec) (ds : List (Keyed Dev)) : List (Keyed Dev) :=
  ds.map fun c =>
    match c.call with
    | .hit r => ⟨c.key, .hit (Moves.move d r)⟩
    | .other => c

theorem hits_moveAll (d : IVec) : ∀ ds : List (Keyed Dev),
    hits (moveAll d ds) = Moves.move d (hits ds)
  | [] => rfl
  | ⟨k, .hit r⟩ :: ds => congrArg ((⟨k, Moves.move d r⟩ : Hit) :: ·) (hits_moveAll d ds)
  | ⟨_, .other⟩ :: ds => hits_moveAll d ds

/-- **The pointer over a moved picture answers what it answered.** -/
theorem pick_move (d : IVec) (ds : List (Keyed Dev)) (x y : Int) :
    pick (moveAll d ds) (x + d.x) (y + d.y) = pick ds x y := by
  rw [pick, hits_moveAll]
  have e := Boxed.pick_move d (hits ds) ⟨x, y⟩
  have e' : Boxed.pick (Moves.move d (hits ds)) ⟨x + d.x, y + d.y⟩ =
      Moves.move d (Boxed.pick (hits ds) ⟨x, y⟩) := e
  rw [e', pick]
  cases Boxed.pick (hits ds) ⟨x, y⟩ <;> rfl

/-- Two pointer boxes, the second over a corner of the first, and a call that is no box. -/
def twoBoxes : List (Keyed Dev) :=
  [⟨"under", .hit ⟨0, 0, 6, 6⟩⟩, ⟨"paint", .other⟩, ⟨"over", .hit ⟨4, 4, 9, 9⟩⟩]

-- The port answers as the consumer's own text does, at each of the 144 pixels from -1 to 10
-- each way. No theorem here says that the two are one function.
#guard (List.range 12).all fun i => (List.range 12).all fun j =>
  pick twoBoxes ((i : Int) - 1) ((j : Int) - 1) == pick0 twoBoxes ((i : Int) - 1) ((j : Int) - 1)

-- Where the two boxes share a pixel the later one answers, and the first box holds the pixel
-- without answering. `pick_exact` asks that no two boxes share a pixel, and this is why.
#guard pick twoBoxes 5 5 == some "over"
#guard decide ((⟨0, 0, 6, 6⟩ : IBox).Holds ⟨5, 5⟩)
#guard pick twoBoxes 1 1 == some "under"
#guard pick twoBoxes 20 20 == none

/-! ## Places apart -/

/-- A key of an item, and the gap between two items in cells: the consumer's `Key` and `GAP`. -/
abbrev Key := String

def GAP : Nat := 2

/-- The distance between the centres of two neighbours in half cells: the consumer's `sep`. -/
def sep (width : Key → Nat) (u v : Key) : Int := width u + width v + 2 * GAP

/-- **Separation**: each centre at least `sep` right of the one before it. The consumer's
`spread`, as it writes it. -/
def spread (width : Key → Nat) : Option (Key × Int) → List (Key × Int) → List (Key × Int)
  | _, [] => []
  | none, (k, x) :: rest => (k, x) :: spread width (some (k, x)) rest
  | some (u, xu), (k, x) :: rest =>
    let x' := max x (xu + sep width u k)
    (k, x') :: spread width (some (k, x')) rest

/-- Each centre of a list stands at least `sep` right of the one before it: the consumer's
`Apart`, as it writes it. -/
def Apart (width : Key → Nat) : Option (Key × Int) → List (Key × Int) → Prop
  | _, [] => True
  | none, (k, x) :: rest => Apart width (some (k, x)) rest
  | some (u, xu), (k, x) :: rest => xu + sep width u k ≤ x ∧ Apart width (some (k, x)) rest

/-- The consumer's `spread` after an item is the kit's. -/
theorem spread_after (width : Key → Nat) : ∀ (u : Key) (xu : Int) (xs : List (Key × Int)),
    spread width (some (u, xu)) xs = Row.spreadAfter (sep width) u xu xs
  | _, _, [] => rfl
  | u, xu, (k, x) :: rest =>
    congrArg ((k, max x (xu + sep width u k)) :: ·) (spread_after width k _ rest)

/-- **The consumer's `spread` is `Row.spread`** at the consumer's distance. -/
theorem spread_eq (width : Key → Nat) : ∀ xs : List (Key × Int),
    spread width none xs = Row.spread (sep width) xs
  | [] => rfl
  | (k, x) :: rest => congrArg ((k, x) :: ·) (spread_after width k x rest)

/-- The consumer's `Apart` after an item is the kit's, of the item and the list. -/
theorem apart_after (width : Key → Nat) : ∀ (u : Key) (xu : Int) (xs : List (Key × Int)),
    Apart width (some (u, xu)) xs ↔ Row.Apart (sep width) ((u, xu) :: xs)
  | _, _, [] => Iff.rfl
  | _, _, (k, x) :: rest => and_congr Iff.rfl (apart_after width k x rest)

/-- **The consumer's `Apart` is `Row.Apart`.** -/
theorem apart_iff (width : Key → Nat) : ∀ xs : List (Key × Int),
    Apart width none xs ↔ Row.Apart (sep width) xs
  | [] => Iff.rfl
  | (k, x) :: rest => apart_after width k x rest

/-- **The law of separation**: the consumer's `spread_apart`, for a rank from its first item. -/
theorem spread_apart (width : Key → Nat) (xs : List (Key × Int)) :
    Apart width none (spread width none xs) := by
  rw [spread_eq, apart_iff]
  exact Row.spread_apart (sep width) xs

/-- The consumer's distance does not shorten a way: the half width of the item between and the
gap are not negative. -/
theorem sep_way (width : Key → Nat) (a b c : Key) :
    sep width a c ≤ sep width a b + sep width b c := by
  show (width a : Int) + width c + 2 * GAP ≤
    (width a : Int) + width b + 2 * GAP + ((width b : Int) + width c + 2 * GAP)
  omega

/-- **Every two items of a rank are apart** by their half widths and a gap, so no two share a
cell. -/
theorem spread_all (width : Key → Nat) (xs : List (Key × Int)) :
    (spread width none xs).Pairwise fun p q => p.2 + sep width p.1 q.1 ≤ q.2 := by
  rw [spread_eq]
  exact Row.spread_pairwise (sep_way width) xs

/-- **No row that is apart and gives each item its place or more stands left of this one.** -/
theorem spread_leftmost (width : Key → Nat) {xs zs : List (Key × Int)} (hn : Row.NoLess xs zs)
    (ha : Apart width none zs) : Row.NoLess (spread width none xs) zs := by
  rw [spread_eq]
  exact Row.spread_least (sep width) hn ((apart_iff width zs).mp ha)

/-- Every item four half cells wide. -/
def four : Key → Nat := fun _ => 4

-- By hand: the distance between two centres is 4 + 4 + 2 * 2 = 12. The second item asks for 5
-- and is put at 0 + 12; the third asks for 40 and keeps it; the fourth asks for 41 and is put
-- at 40 + 12.
#guard spread four none [("a", 0), ("b", 5), ("c", 40), ("d", 41)] ==
  [("a", 0), ("b", 12), ("c", 40), ("d", 52)]

/-- A distance that is long between `a` and `c` alone: it shortens the way through `b`. -/
def odd : Key → Key → Int := fun u v => if u == "a" && v == "c" then 100 else 1

-- A control for `sep_way`, the premise of `Row.spread_pairwise`. Under `odd` a row is apart at
-- each neighbour, and `a` and `c` are not apart.
#guard decide (Row.Apart odd [("a", 0), ("b", 1), ("c", 2)])
#guard !decide ([(("a" : Key), (0 : Int)), ("b", 1), ("c", 2)].Pairwise
  fun p q => p.2 + odd p.1 q.1 ≤ q.2)

end WhatwgTest.Svg.UsePlaces
