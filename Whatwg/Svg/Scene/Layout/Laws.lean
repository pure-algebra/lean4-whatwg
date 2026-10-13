import Whatwg.Svg.Scene.Layout
import Whatwg.Svg.Scene.Row.Laws

/-!
# Whatwg.Svg.Scene.Layout.Laws

Owner: where the parts of a layout stand (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Layout.lean` puts parts together and says of the result that it fits and is
clear. It does not say where a part went. A caller that draws a link from one part to another,
or asks whether one part is above another, needs that. This module says it, and it says it with
the edges of `Row.spans` of `Whatwg/Svg/Scene/Row.lean`: a column is its parts, each moved down
to an edge of the row of their heights. So the layout and the row that moves hold one idea of
"one after another" between them. This module is beside `Layout.lean` and not in it because
`Row` imports the modules of motion, and a program that only lays out should not.

- `Stands l d a`: **the part `a` stands in `l` at the step `d`.** Each thing of `a`, moved by
  `d`, is a thing of `l`.
- `rowParts gap ls`, `columnParts gap ls`: the parts of a row or a column, each with the step to
  where it stands.

What the laws say:

- **A part of a part is a part** (`Stands.refl`, `Stands.trans`): a layout stands in itself at
  no step, and the steps of a part in a part in a layout add. Each operation of `Layout.lean`
  says where its parts stand (`stands_beside_left`, `stands_beside_right`, and so for `above`,
  `over`, `inset` and `centred`), and a part stands in a placed layout at its step and the
  layout's origin (`Stands.place`).
- **A column is its parts at the edges of a row** (`column_items`, and `row_items` for a row):
  the things of `column gap ls` are the things of each part, moved to that part's step. So each
  part stands at its step (`stands_column`, `stands_row`). The parts are listed once in their
  order (`columnParts_parts`), so each part has a step (`columnParts_mem`, `columnParts_at`),
  and a step of a column goes straight down and not up (`columnParts_step`).
- **An earlier part ends the gap before a later one** (`columnParts_below`,
  `rowParts_beside`), of each two parts and not of neighbours only. Where the parts fit, a thing
  of the earlier part ends the gap before a thing of the later (`column_below`, `row_beside`,
  through `Fits.apart_down` and `Fits.apart_across`).
- **No thing is lost and none is made** (`row_items_map`, `column_items_map`): a reading that
  does not see a move, such as the key of a thing, reads a row or a column as its parts one
  after another. So the keys of a composite are distinct exactly when the keys of its parts
  are.
- A row is as high as each of its parts, and a column as wide (`row_h_le`, `column_w_le`).

`Whatwg/Svg/Scene/Layered.lean` is the first reader: a graph in layers is a column of rows, and
that a link goes down is `columnParts_below` at the rows of its two ends.

What this module does not claim: where a thing of a part stands inside the part; that a part
stands at one step only, since a layout may hold a thing twice; anything of `stack`, whose
parts are centred first (it is a `column` of them, so the laws of a column hold of the centred
parts).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Layout

variable {α : Type}

/-- **The parts of a row, each with the step to where it stands**: across to an edge of the row
of the parts' widths, each with the gap (`Row.spans`). -/
def rowParts (gap : Nat) (ls : List (Layout α)) : List (Layout α × IVec) :=
  (ls.zip (Row.spans 0 (ls.map fun l => ((l.w + gap : Nat) : Int)))).map fun p => (p.1, ⟨p.2.1, 0⟩)

/-- **The parts of a column, each with the step to where it stands**: down to an edge of the
row of the parts' heights, each with the gap (`Row.spans`). -/
def columnParts (gap : Nat) (ls : List (Layout α)) : List (Layout α × IVec) :=
  (ls.zip (Row.spans 0 (ls.map fun l => ((l.h + gap : Nat) : Int)))).map fun p => (p.1, ⟨0, p.2.1⟩)

/-! ## Parts at the edges of a row of lengths, along either axis -/

/-- Parts at the edges of the row of their sizes from `s`, each with the step that `f` makes of
its edge. A row and a column are this, with two functions `f`. -/
private def partsFrom (f : Int → IVec) (size : Layout α → Nat) (gap : Nat) (s : Int)
    (ls : List (Layout α)) : List (Layout α × IVec) :=
  (ls.zip (Row.spans s (ls.map fun l => ((size l + gap : Nat) : Int)))).map fun p => (p.1, f p.2.1)

private theorem partsFrom_cons (f : Int → IVec) (size : Layout α → Nat) (gap : Nat) (s : Int)
    (l : Layout α) (ls : List (Layout α)) : partsFrom f size gap s (l :: ls) =
      (l, f s) :: partsFrom f size gap (s + ((size l + gap : Nat) : Int)) ls := rfl

/-- The parts are listed once, in their order. -/
private theorem partsFrom_parts (f : Int → IVec) (size : Layout α → Nat) (gap : Nat) :
    ∀ (s : Int) (ls : List (Layout α)), (partsFrom f size gap s ls).map (fun p => p.1) = ls
  | _, [] => rfl
  | s, l :: ls => by
    rw [partsFrom_cons, List.map_cons, partsFrom_parts f size gap _ ls]

/-- No part stands before the start. -/
private theorem partsFrom_from {f : Int → IVec} {c : IVec → Int} (hc : ∀ n, c (f n) = n)
    (size : Layout α → Nat) (gap : Nat) : ∀ (s : Int) (ls : List (Layout α))
    (P : Layout α × IVec), P ∈ partsFrom f size gap s ls → s ≤ c P.2
  | _, [], _, h => nomatch h
  | s, l :: ls, P, h => by
    rw [partsFrom_cons] at h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      show s ≤ c (f s)
      rw [hc]
      exact Int.le_refl s
    | inr hp =>
      have h1 := partsFrom_from hc size gap _ ls P hp
      omega

/-- Each part ends the gap before every later part begins. -/
private theorem partsFrom_apart {f : Int → IVec} {c : IVec → Int} (hc : ∀ n, c (f n) = n)
    (size : Layout α → Nat) (gap : Nat) : ∀ (s : Int) (ls : List (Layout α)),
    (partsFrom f size gap s ls).Pairwise fun P Q => c P.2 + size P.1 + gap ≤ c Q.2
  | _, [] => List.Pairwise.nil
  | s, l :: ls => by
    rw [partsFrom_cons]
    refine List.Pairwise.cons (fun Q hQ => ?_) (partsFrom_apart hc size gap _ ls)
    have h1 := partsFrom_from hc size gap _ ls Q hQ
    show c (f s) + (size l : Int) + (gap : Int) ≤ c Q.2
    rw [hc]
    omega

/-- The step across by a whole number of units. -/
private def stepX (n : Int) : IVec := ⟨n, 0⟩

/-- The step down by a whole number of units. -/
private def stepY (n : Int) : IVec := ⟨0, n⟩

private theorem stepX_add (a b : Int) : stepX (a + b) = stepX a + stepX b :=
  IVec.ext rfl (Int.add_zero 0).symm

private theorem stepY_add (a b : Int) : stepY (a + b) = stepY a + stepY b :=
  IVec.ext (Int.add_zero 0).symm rfl

/-- Parts from a start `d` further on are the parts, each with its step `f d` further on. -/
private theorem partsFrom_shift {f : Int → IVec} (hf : ∀ a b, f (a + b) = f a + f b)
    (size : Layout α → Nat) (gap : Nat) (d : Int) : ∀ (s : Int) (ls : List (Layout α)),
    partsFrom f size gap (s + d) ls = (partsFrom f size gap s ls).map fun P => (P.1, P.2 + f d)
  | _, [] => rfl
  | s, l :: ls => by
    show (l, f (s + d)) :: partsFrom f size gap (s + d + ((size l + gap : Nat) : Int)) ls =
      (l, f s + f d) :: (partsFrom f size gap (s + ((size l + gap : Nat) : Int)) ls).map
        fun P => (P.1, P.2 + f d)
    rw [Int.add_right_comm s d, partsFrom_shift hf size gap d _ ls, hf]

/-- Each part and the next: the next begins where the part ends, and the gap. -/
private theorem partsFrom_next {f : Int → IVec} {c : IVec → Int} (hc : ∀ n, c (f n) = n)
    (size : Layout α → Nat) (gap : Nat) : ∀ (s : Int) (ls : List (Layout α)) (i : Nat)
    (P Q : Layout α × IVec), (partsFrom f size gap s ls)[i]? = some P →
    (partsFrom f size gap s ls)[i + 1]? = some Q → c P.2 + size P.1 + gap = c Q.2
  | _, [], _, _, _, hP, _ => by
    rw [show partsFrom f size gap _ ([] : List (Layout α)) = [] from rfl, List.getElem?_nil] at hP
    exact nomatch hP
  | s, l :: ls, 0, P, Q, hP, hQ => by
    rw [partsFrom_cons, List.getElem?_cons_zero] at hP
    rw [partsFrom_cons, List.getElem?_cons_succ] at hQ
    cases ls with
    | nil =>
      rw [show partsFrom f size gap _ ([] : List (Layout α)) = [] from rfl, List.getElem?_nil] at hQ
      exact nomatch hQ
    | cons m ms =>
      rw [partsFrom_cons, List.getElem?_cons_zero] at hQ
      rw [← Option.some.inj hP, ← Option.some.inj hQ]
      show c (f s) + (size l : Int) + (gap : Int) = c (f (s + ((size l + gap : Nat) : Int)))
      rw [hc, hc]
      omega
  | s, l :: ls, i + 1, P, Q, hP, hQ => by
    rw [partsFrom_cons, List.getElem?_cons_succ] at hP hQ
    exact partsFrom_next hc size gap _ ls i P Q hP hQ

/-- The part at a place of a list of parts is the part at that place among the parts with their
steps. -/
private theorem part_at {ps : List (Layout α × IVec)} {ls : List (Layout α)}
    (h : ps.map (fun p => p.1) = ls) {i : Nat} {a : Layout α} (hi : ls[i]? = some a) :
    ∃ d : IVec, ps[i]? = some (a, d) := by
  rw [← h, List.getElem?_map] at hi
  cases hp : ps[i]? with
  | none =>
    rw [hp] at hi
    exact nomatch hi
  | some P =>
    rw [hp] at hi
    have e : P.1 = a := Option.some.inj hi
    exact ⟨P.2, by rw [← e]⟩

/-- Each part of a list of parts is among the parts with their steps. -/
private theorem part_mem {ps : List (Layout α × IVec)} {ls : List (Layout α)}
    (h : ps.map (fun p => p.1) = ls) {a : Layout α} (ha : a ∈ ls) : ∃ d : IVec, (a, d) ∈ ps := by
  rw [← h] at ha
  obtain ⟨P, hP, e⟩ := List.mem_map.mp ha
  exact ⟨P.2, by rw [← e]; exact hP⟩

theorem rowParts_nil (gap : Nat) : rowParts gap ([] : List (Layout α)) = [] := rfl

theorem columnParts_nil (gap : Nat) : columnParts gap ([] : List (Layout α)) = [] := rfl

/-- **The parts of a row, part by part**: the first stands at no step, and each later part
stands where it stands in the row of the rest, and the width of the first and the gap further
on. -/
theorem rowParts_cons (gap : Nat) (a : Layout α) (ls : List (Layout α)) :
    rowParts gap (a :: ls) =
      (a, 0) :: (rowParts gap ls).map fun P => (P.1, P.2 + across (a.w + gap)) := by
  show (a, stepX 0) :: partsFrom stepX (fun l => l.w) gap (0 + ((a.w + gap : Nat) : Int)) ls = _
  rw [partsFrom_shift stepX_add]
  rfl

/-- **The parts of a column, part by part**: the first stands at no step, and each later part
stands where it stands in the column of the rest, and the height of the first and the gap
further down. -/
theorem columnParts_cons (gap : Nat) (a : Layout α) (ls : List (Layout α)) :
    columnParts gap (a :: ls) =
      (a, 0) :: (columnParts gap ls).map fun P => (P.1, P.2 + down (a.h + gap)) := by
  show (a, stepY 0) :: partsFrom stepY (fun l => l.h) gap (0 + ((a.h + gap : Nat) : Int)) ls = _
  rw [partsFrom_shift stepY_add]
  rfl

/-- **Each part of a row and the next**: the next begins where the part ends, and the gap. -/
theorem rowParts_next (gap : Nat) (ls : List (Layout α)) {i : Nat} {P Q : Layout α × IVec}
    (hP : (rowParts gap ls)[i]? = some P) (hQ : (rowParts gap ls)[i + 1]? = some Q) :
    P.2.x + (P.1.w : Int) + (gap : Int) = Q.2.x :=
  partsFrom_next (f := stepX) (c := fun v => v.x) (fun _ => rfl) (fun l => l.w) gap 0 ls i P Q hP hQ

/-- **Each part of a column and the next**: the next begins where the part ends, and the
gap. -/
theorem columnParts_next (gap : Nat) (ls : List (Layout α)) {i : Nat} {P Q : Layout α × IVec}
    (hP : (columnParts gap ls)[i]? = some P) (hQ : (columnParts gap ls)[i + 1]? = some Q) :
    P.2.y + (P.1.h : Int) + (gap : Int) = Q.2.y :=
  partsFrom_next (f := stepY) (c := fun v => v.y) (fun _ => rfl) (fun l => l.h) gap 0 ls i P Q hP hQ

/-- **The parts of a row are listed once, in their order.** -/
theorem rowParts_parts (gap : Nat) (ls : List (Layout α)) :
    (rowParts gap ls).map (fun p => p.1) = ls :=
  partsFrom_parts stepX (fun l => l.w) gap 0 ls

/-- **The parts of a column are listed once, in their order.** -/
theorem columnParts_parts (gap : Nat) (ls : List (Layout α)) :
    (columnParts gap ls).map (fun p => p.1) = ls :=
  partsFrom_parts stepY (fun l => l.h) gap 0 ls

/-- Each part of a row has a step. -/
theorem rowParts_mem (gap : Nat) {ls : List (Layout α)} {a : Layout α} (ha : a ∈ ls) :
    ∃ d : IVec, (a, d) ∈ rowParts gap ls := part_mem (rowParts_parts gap ls) ha

/-- Each part of a column has a step. -/
theorem columnParts_mem (gap : Nat) {ls : List (Layout α)} {a : Layout α} (ha : a ∈ ls) :
    ∃ d : IVec, (a, d) ∈ columnParts gap ls := part_mem (columnParts_parts gap ls) ha

/-- The part at a place of a row has its step at that place. -/
theorem rowParts_at (gap : Nat) {ls : List (Layout α)} {i : Nat} {a : Layout α}
    (hi : ls[i]? = some a) : ∃ d : IVec, (rowParts gap ls)[i]? = some (a, d) :=
  part_at (rowParts_parts gap ls) hi

/-- The part at a place of a column has its step at that place. -/
theorem columnParts_at (gap : Nat) {ls : List (Layout α)} {i : Nat} {a : Layout α}
    (hi : ls[i]? = some a) : ∃ d : IVec, (columnParts gap ls)[i]? = some (a, d) :=
  part_at (columnParts_parts gap ls) hi

/-- A step of a row goes straight across, and not back. -/
theorem rowParts_step (gap : Nat) (ls : List (Layout α)) (P : Layout α × IVec)
    (h : P ∈ rowParts gap ls) : 0 ≤ P.2.x ∧ P.2.y = 0 := by
  refine ⟨partsFrom_from (f := stepX) (c := fun v => v.x) (fun _ => rfl) (fun l => l.w) gap 0 ls
    P h, ?_⟩
  obtain ⟨p, _, e⟩ := List.mem_map.mp h
  rw [← e]

/-- A step of a column goes straight down, and not up. -/
theorem columnParts_step (gap : Nat) (ls : List (Layout α)) (P : Layout α × IVec)
    (h : P ∈ columnParts gap ls) : P.2.x = 0 ∧ 0 ≤ P.2.y := by
  refine ⟨?_,
    partsFrom_from (f := stepY) (c := fun v => v.y) (fun _ => rfl) (fun l => l.h) gap 0 ls P h⟩
  obtain ⟨p, _, e⟩ := List.mem_map.mp h
  rw [← e]

/-- **A part of a row ends the gap before every later part begins**: its step, its width and
the gap are no more than the later part's step. -/
theorem rowParts_beside (gap : Nat) (ls : List (Layout α)) :
    (rowParts gap ls).Pairwise fun P Q => P.2.x + (P.1.w : Int) + (gap : Int) ≤ Q.2.x :=
  partsFrom_apart (f := stepX) (c := fun v => v.x) (fun _ => rfl) (fun l => l.w) gap 0 ls

/-- **A part of a column ends the gap above every later part**: its step, its height and the
gap are no more than the later part's step. -/
theorem columnParts_below (gap : Nat) (ls : List (Layout α)) :
    (columnParts gap ls).Pairwise fun P Q => P.2.y + (P.1.h : Int) + (gap : Int) ≤ Q.2.y :=
  partsFrom_apart (f := stepY) (c := fun v => v.y) (fun _ => rfl) (fun l => l.h) gap 0 ls

/-- A row is as high as each of its parts, at least. -/
theorem row_h_le [Moves IVec α] (gap : Nat) : ∀ (ls : List (Layout α)) (a : Layout α), a ∈ ls →
    a.h ≤ (row gap ls).h
  | [], _, h => nomatch h
  | [b], a, h => by
    rw [List.mem_singleton.mp h]
    exact Nat.le_refl _
  | b :: c :: rest, a, h => by
    show a.h ≤ max b.h (row gap (c :: rest)).h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_max_left _ _
    | inr h' => exact Nat.le_trans (row_h_le gap (c :: rest) a h') (Nat.le_max_right _ _)

/-- A column is as wide as each of its parts, at least. -/
theorem column_w_le [Moves IVec α] (gap : Nat) : ∀ (ls : List (Layout α)) (a : Layout α),
    a ∈ ls → a.w ≤ (column gap ls).w
  | [], _, h => nomatch h
  | [b], a, h => by
    rw [List.mem_singleton.mp h]
    exact Nat.le_refl _
  | b :: c :: rest, a, h => by
    show a.w ≤ max b.w (column gap (c :: rest)).w
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_max_left _ _
    | inr h' => exact Nat.le_trans (column_w_le gap (c :: rest) a h') (Nat.le_max_right _ _)

section

variable [Moves IVec α]

/-! ## Where a part stands -/

/-- **The part `a` stands in `l` at the step `d`**: each thing of `a`, moved by `d`, is a thing
of `l`. -/
def Stands (l : Layout α) (d : IVec) (a : Layout α) : Prop :=
  ∀ x ∈ a.items, Moves.move d x ∈ l.items

/-- A layout stands in itself, at no step. -/
theorem Stands.refl (l : Layout α) : l.Stands 0 l := fun x hx => by
  rw [Moves.move_zero]
  exact hx

/-- **A part of a part is a part**, and the two steps add. -/
theorem Stands.trans {a b c : Layout α} {d e : IVec} (h : b.Stands d a) (k : c.Stands e b) :
    c.Stands (d + e) a := fun x hx => by
  rw [← Moves.move_move]
  exact k _ (h x hx)

/-- A part stands in a placed layout at its step and the layout's origin. -/
theorem Stands.place {l a : Layout α} {d : IVec} (h : l.Stands d a) (origin : IVec) :
    ∀ x ∈ a.items, Moves.move (d + origin) x ∈ place origin l := fun x hx => by
  rw [← Moves.move_move]
  exact List.mem_map_of_mem (h x hx)

theorem stands_beside_left (gap : Nat) (a b : Layout α) : (beside gap a b).Stands 0 a :=
  fun x hx => by
    rw [Moves.move_zero]
    exact List.mem_append_left _ hx

theorem stands_beside_right (gap : Nat) (a b : Layout α) :
    (beside gap a b).Stands (across (a.w + gap)) b :=
  fun _ hx => List.mem_append_right _ (List.mem_map_of_mem hx)

theorem stands_above_left (gap : Nat) (a b : Layout α) : (above gap a b).Stands 0 a :=
  fun x hx => by
    rw [Moves.move_zero]
    exact List.mem_append_left _ hx

theorem stands_above_right (gap : Nat) (a b : Layout α) :
    (above gap a b).Stands (down (a.h + gap)) b :=
  fun _ hx => List.mem_append_right _ (List.mem_map_of_mem hx)

theorem stands_over_left (a b : Layout α) : (over a b).Stands 0 a := fun x hx => by
  rw [Moves.move_zero]
  exact List.mem_append_left _ hx

theorem stands_over_right (a b : Layout α) : (over a b).Stands 0 b := fun x hx => by
  rw [Moves.move_zero]
  exact List.mem_append_right _ hx

theorem stands_inset (left top right bottom : Nat) (a : Layout α) :
    (inset left top right bottom a).Stands (across left + down top) a :=
  fun _ hx => List.mem_map_of_mem hx

theorem stands_centred (width : Nat) (a : Layout α) :
    (centred width a).Stands (across ((width - a.w) / 2)) a :=
  fun _ hx => List.mem_map_of_mem hx

/-! ## A row and a column are their parts at the edges -/

/-- Parts from a start `d` further on are the parts, each thing moved by the step of `d`. -/
private theorem things_shift {f : Int → IVec} (hf : ∀ a b, f (a + b) = f a + f b)
    (size : Layout α → Nat) (gap : Nat) (d : Int) : ∀ (s : Int) (ls : List (Layout α)),
    (partsFrom f size gap (s + d) ls).flatMap (fun p => Moves.move p.2 p.1.items) =
      Moves.move (f d) ((partsFrom f size gap s ls).flatMap fun p => Moves.move p.2 p.1.items)
  | _, [] => rfl
  | s, l :: ls => by
    show Moves.move (f (s + d)) l.items ++
        (partsFrom f size gap (s + d + ((size l + gap : Nat) : Int)) ls).flatMap
          (fun p => Moves.move p.2 p.1.items) =
      Moves.move (f d) (Moves.move (f s) l.items ++
        (partsFrom f size gap (s + ((size l + gap : Nat) : Int)) ls).flatMap
          fun p => Moves.move p.2 p.1.items)
    rw [Moves.move_append, Moves.move_move, ← hf, Int.add_right_comm s d,
      things_shift hf size gap d (s + ((size l + gap : Nat) : Int)) ls]

/-- **A row is its parts at the edges of the row of their widths**: the things of each part,
moved across to the part's step, part after part. -/
theorem row_items (gap : Nat) : ∀ ls : List (Layout α),
    (row gap ls).items = (rowParts gap ls).flatMap fun p => Moves.move p.2 p.1.items
  | [] => rfl
  | [a] => by
    show a.items = Moves.move (0 : IVec) a.items ++ []
    rw [List.append_nil, Moves.move_zero]
  | a :: b :: rest => by
    show a.items ++ Moves.move (stepX ((a.w + gap : Nat) : Int)) (row gap (b :: rest)).items =
      Moves.move (0 : IVec) a.items ++
        (partsFrom stepX (fun l => l.w) gap (0 + ((a.w + gap : Nat) : Int)) (b :: rest)).flatMap
          fun p => Moves.move p.2 p.1.items
    rw [things_shift stepX_add, Moves.move_zero, row_items gap (b :: rest)]
    rfl

/-- **A column is its parts at the edges of the row of their heights**: the things of each
part, moved down to the part's step, part after part. -/
theorem column_items (gap : Nat) : ∀ ls : List (Layout α),
    (column gap ls).items = (columnParts gap ls).flatMap fun p => Moves.move p.2 p.1.items
  | [] => rfl
  | [a] => by
    show a.items = Moves.move (0 : IVec) a.items ++ []
    rw [List.append_nil, Moves.move_zero]
  | a :: b :: rest => by
    show a.items ++ Moves.move (stepY ((a.h + gap : Nat) : Int)) (column gap (b :: rest)).items =
      Moves.move (0 : IVec) a.items ++
        (partsFrom stepY (fun l => l.h) gap (0 + ((a.h + gap : Nat) : Int)) (b :: rest)).flatMap
          fun p => Moves.move p.2 p.1.items
    rw [things_shift stepY_add, Moves.move_zero, column_items gap (b :: rest)]
    rfl

/-- **Each part of a row stands in the row at its step.** -/
theorem stands_row {gap : Nat} {ls : List (Layout α)} {P : Layout α × IVec}
    (h : P ∈ rowParts gap ls) : (row gap ls).Stands P.2 P.1 := fun x hx => by
  rw [row_items]
  exact List.mem_flatMap.mpr ⟨P, h, List.mem_map_of_mem hx⟩

/-- **Each part of a column stands in the column at its step.** -/
theorem stands_column {gap : Nat} {ls : List (Layout α)} {P : Layout α × IVec}
    (h : P ∈ columnParts gap ls) : (column gap ls).Stands P.2 P.1 := fun x hx => by
  rw [column_items]
  exact List.mem_flatMap.mpr ⟨P, h, List.mem_map_of_mem hx⟩

/-! ## What a reading that does not see a move reads -/

/-- A reading that does not see a move reads a moved list as the list. -/
private theorem map_move {β : Type} {f : α → β}
    (hf : ∀ (d : IVec) (a : α), f (Moves.move d a) = f a) (d : IVec) (l : List α) :
    (Moves.move d l).map f = l.map f := by
  show (l.map (Moves.move d)).map f = l.map f
  rw [List.map_map]
  exact List.map_congr_left fun a _ => hf d a

/-- **A reading that does not see a move reads a row as its parts in a row.** With `f` the key
of a thing, the keys of a row are the keys of its parts, part after part: no thing is lost and
none is made. -/
theorem row_items_map {β : Type} {f : α → β} (hf : ∀ (d : IVec) (a : α), f (Moves.move d a) = f a)
    (gap : Nat) : ∀ ls : List (Layout α),
    (row gap ls).items.map f = (ls.flatMap fun l => l.items).map f
  | [] => rfl
  | [a] => by
    show a.items.map f = (a.items ++ []).map f
    rw [List.append_nil]
  | a :: b :: rest => by
    show (a.items ++ Moves.move (across (a.w + gap)) (row gap (b :: rest)).items).map f =
      (a.items ++ (b :: rest).flatMap fun l => l.items).map f
    rw [List.map_append, List.map_append, map_move hf, row_items_map hf gap (b :: rest)]

/-- **A reading that does not see a move reads a column as its parts in a row.** -/
theorem column_items_map {β : Type} {f : α → β}
    (hf : ∀ (d : IVec) (a : α), f (Moves.move d a) = f a) (gap : Nat) : ∀ ls : List (Layout α),
    (column gap ls).items.map f = (ls.flatMap fun l => l.items).map f
  | [] => rfl
  | [a] => by
    show a.items.map f = (a.items ++ []).map f
    rw [List.append_nil]
  | a :: b :: rest => by
    show (a.items ++ Moves.move (down (a.h + gap)) (column gap (b :: rest)).items).map f =
      (a.items ++ (b :: rest).flatMap fun l => l.items).map f
    rw [List.map_append, List.map_append, map_move hf, column_items_map hf gap (b :: rest)]

end

/-! ## Things of two parts that are apart -/

section

variable [Moves IVec α] [Boxed α]

/-- **Things of parts whose rooms are apart, down, are apart.** Where two parts fit, and the
room of the first at its step ends a gap above the step of the second, each thing of the first
ends the gap above each thing of the second. -/
theorem Fits.apart_down {a b : Layout α} (fa : a.Fits) (fb : b.Fits) {d e : IVec} {gap : Int}
    (h : d.y + a.h + gap ≤ e.y) {x y : α} (hx : x ∈ a.items) (hy : y ∈ b.items) :
    (Boxed.box (Moves.move d x)).y1 + gap ≤ (Boxed.box (Moves.move e y)).y0 := by
  have h1 : (Boxed.box x).y1 ≤ (a.h : Int) := (fa x hx).2.2.2
  have h2 : (0 : Int) ≤ (Boxed.box y).y0 := (fb y hy).2.2.1
  rw [Boxed.box_move, Boxed.box_move, IBox.move_y1, IBox.move_y0]
  omega

/-- **Things of parts whose rooms are apart, across, are apart.** -/
theorem Fits.apart_across {a b : Layout α} (fa : a.Fits) (fb : b.Fits) {d e : IVec} {gap : Int}
    (h : d.x + a.w + gap ≤ e.x) {x y : α} (hx : x ∈ a.items) (hy : y ∈ b.items) :
    (Boxed.box (Moves.move d x)).x1 + gap ≤ (Boxed.box (Moves.move e y)).x0 := by
  have h1 : (Boxed.box x).x1 ≤ (a.w : Int) := (fa x hx).2.1
  have h2 : (0 : Int) ≤ (Boxed.box y).x0 := (fb y hy).1
  rw [Boxed.box_move, Boxed.box_move, IBox.move_x1, IBox.move_x0]
  omega

/-- A part that stands in a layout that fits has its things inside the layout's room. -/
theorem Stands.inside {l a : Layout α} {d : IVec} (h : l.Stands d a) (fl : l.Fits) :
    ∀ x ∈ a.items, (Boxed.box (Moves.move d x)).Inside l.room := fun x hx => fl _ (h x hx)

/-- **A thing of an earlier part of a row ends the gap before a thing of a later part**, where
the parts fit. -/
theorem row_beside {gap : Nat} {ls : List (Layout α)} (hf : ∀ l ∈ ls, l.Fits) :
    (rowParts gap ls).Pairwise fun P Q => ∀ x ∈ P.1.items, ∀ y ∈ Q.1.items,
      (Boxed.box (Moves.move P.2 x)).x1 + gap ≤ (Boxed.box (Moves.move Q.2 y)).x0 := by
  have hm : ∀ P ∈ rowParts gap ls, P.1 ∈ ls := fun P hP => by
    have h := List.mem_map_of_mem (f := fun p : Layout α × IVec => p.1) hP
    rw [rowParts_parts] at h
    exact h
  exact (rowParts_beside gap ls).imp_of_mem fun hP hQ h x hx y hy =>
    (hf _ (hm _ hP)).apart_across (hf _ (hm _ hQ)) h hx hy

/-- **A thing of an earlier part of a column ends the gap above a thing of a later part**,
where the parts fit. -/
theorem column_below {gap : Nat} {ls : List (Layout α)} (hf : ∀ l ∈ ls, l.Fits) :
    (columnParts gap ls).Pairwise fun P Q => ∀ x ∈ P.1.items, ∀ y ∈ Q.1.items,
      (Boxed.box (Moves.move P.2 x)).y1 + gap ≤ (Boxed.box (Moves.move Q.2 y)).y0 := by
  have hm : ∀ P ∈ columnParts gap ls, P.1 ∈ ls := fun P hP => by
    have h := List.mem_map_of_mem (f := fun p : Layout α × IVec => p.1) hP
    rw [columnParts_parts] at h
    exact h
  exact (columnParts_below gap ls).imp_of_mem fun hP hQ h x hx y hy =>
    (hf _ (hm _ hP)).apart_down (hf _ (hm _ hQ)) h hx hy

end

end Layout

end Whatwg.Svg.Scene
