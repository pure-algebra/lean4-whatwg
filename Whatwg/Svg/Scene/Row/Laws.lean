import Whatwg.Svg.Scene.Row

/-!
# Whatwg.Svg.Scene.Row.Laws

Owner: where each span of a row stands (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Row.spans start ws` of `Whatwg/Svg/Scene/Row.lean` is the row of the lengths `ws` from `start`.
That module says of it that it tiles, and no more: its laws are about the row between two rows.
A layout reads the row itself. A part of a column stands at an edge of the row of the parts'
heights, and it asks where that edge is, and that the edges come in order.

What the laws say of `Row.spans start ws`:

- `spans_length`, `spans_lengths`: a span for each length, with that length.
- `spans_getElem?`: **the span `i` begins at the start and the lengths before it.**
- `spans_shift`: the row from a start `d` further on is the row, each span `d` further on.
- `spans_append`: two rows in a row; the second begins where the first ends.
- `spans_from`, `spans_until`, `spans_ordered`: with lengths that are not negative, no span
  begins before the start or ends after the start and the sum of the lengths, and **each span
  ends where a later one begins, or before it.**
- `pairwise_at`: a relation that holds of each thing of a list and each later thing holds of the
  things at two places in order. It is of lists, and it is here because the layer has no module
  of lists.

What this module does not claim: anything of lengths that are negative, where a later span may
begin before an earlier one.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **A relation of each thing and each later thing holds at two places in order.** -/
theorem pairwise_at {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {i j : Nat} {a b : α}, i < j → l[i]? = some a → l[j]? = some b → R a b
  | [], _, _, _, _, _, _, hi, _ => nomatch hi
  | x :: xs, h, i, j, a, b, hij, hi, hj => by
    cases j with
    | zero => exact absurd hij (Nat.not_lt_zero i)
    | succ j =>
      rw [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at hi
        rw [← Option.some.inj hi]
        exact (List.pairwise_cons.mp h).1 b (List.mem_of_getElem? hj)
      | succ i =>
        rw [List.getElem?_cons_succ] at hi
        exact pairwise_at (List.pairwise_cons.mp h).2 (Nat.lt_of_succ_lt_succ hij) hi hj

namespace Row

theorem spans_nil (s : Int) : spans s [] = [] := rfl

theorem spans_cons (s w : Int) (ws : List Int) : spans s (w :: ws) = (s, w) :: spans (s + w) ws :=
  rfl

/-- A row has a span for each length. -/
theorem spans_length : ∀ (s : Int) (ws : List Int), (spans s ws).length = ws.length
  | _, [] => rfl
  | s, w :: ws => congrArg (· + 1) (spans_length (s + w) ws)

/-- The spans have the lengths given, in order. -/
theorem spans_lengths : ∀ (s : Int) (ws : List Int), (spans s ws).map (fun p => p.2) = ws
  | _, [] => rfl
  | s, w :: ws => congrArg (w :: ·) (spans_lengths (s + w) ws)

/-- **A row from a start further on is the row, each span as much further on.** -/
theorem spans_shift (d : Int) : ∀ (s : Int) (ws : List Int),
    spans (s + d) ws = (spans s ws).map fun p => (p.1 + d, p.2)
  | _, [] => rfl
  | s, w :: ws => by
    rw [spans_cons, spans_cons, List.map_cons, Int.add_right_comm s d w, spans_shift d (s + w) ws]

/-- **Two rows in a row**: the second begins where the first ends. -/
theorem spans_append : ∀ (s : Int) (a b : List Int),
    spans s (a ++ b) = spans s a ++ spans (s + a.sum) b
  | s, [], b => by
    rw [List.nil_append, spans_nil, List.nil_append, List.sum_nil, Int.add_zero]
  | s, w :: a, b => by
    rw [List.cons_append, spans_cons, spans_cons, spans_append (s + w) a b, List.sum_cons,
      Int.add_assoc, List.cons_append]

/-- **Where the span `i` stands**: it begins at the start and the lengths before it, and it has
the length `i`. -/
theorem spans_getElem? : ∀ (s : Int) (ws : List Int) (i : Nat),
    (spans s ws)[i]? = ws[i]?.map fun w => (s + (ws.take i).sum, w)
  | _, [], _ => rfl
  | s, w :: ws, 0 => by
    rw [spans_cons, List.getElem?_cons_zero, List.getElem?_cons_zero, List.take_zero,
      List.sum_nil, Int.add_zero]
    rfl
  | s, w :: ws, i + 1 => by
    rw [spans_cons, List.getElem?_cons_succ, List.getElem?_cons_succ, spans_getElem? (s + w) ws i,
      List.take_succ_cons, List.sum_cons, Int.add_assoc]

/-- With lengths that are not negative, no span begins before the start. -/
theorem spans_from : ∀ {ws : List Int}, (∀ w ∈ ws, 0 ≤ w) → ∀ (s : Int) (p : Int × Int),
    p ∈ spans s ws → s ≤ p.1
  | [], _, _, _, h => nomatch h
  | w :: ws, hw, s, p, h => by
    rw [spans_cons] at h
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Int.le_refl s
    | inr hp =>
      have h1 := spans_from (fun v hv => hw v (List.mem_cons_of_mem w hv)) (s + w) p hp
      have h2 := hw w List.mem_cons_self
      omega

/-- A sum of lengths that are not negative is not negative. -/
theorem sum_nonneg : ∀ {ws : List Int}, (∀ w ∈ ws, 0 ≤ w) → 0 ≤ ws.sum
  | [], _ => Int.le_refl 0
  | w :: ws, hw => by
    rw [List.sum_cons]
    have h1 := hw w List.mem_cons_self
    have h2 := sum_nonneg (ws := ws) fun v hv => hw v (List.mem_cons_of_mem w hv)
    omega

/-- With lengths that are not negative, no span ends after the start and the sum of the
lengths. -/
theorem spans_until : ∀ {ws : List Int}, (∀ w ∈ ws, 0 ≤ w) → ∀ (s : Int) (p : Int × Int),
    p ∈ spans s ws → p.1 + p.2 ≤ s + ws.sum
  | [], _, _, _, h => nomatch h
  | w :: ws, hw, s, p, h => by
    have hrest : ∀ v ∈ ws, 0 ≤ v := fun v hv => hw v (List.mem_cons_of_mem w hv)
    rw [spans_cons] at h
    rw [List.sum_cons]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      have h0 : 0 ≤ ws.sum := sum_nonneg hrest
      show s + w ≤ s + (w + ws.sum)
      omega
    | inr hp =>
      have h1 := spans_until hrest (s + w) p hp
      omega

/-- **With lengths that are not negative, each span ends where a later one begins, or before
it.** -/
theorem spans_ordered : ∀ {ws : List Int}, (∀ w ∈ ws, 0 ≤ w) → ∀ s : Int,
    (spans s ws).Pairwise fun p q => p.1 + p.2 ≤ q.1
  | [], _, _ => List.Pairwise.nil
  | w :: ws, hw, s => by
    have hrest : ∀ v ∈ ws, 0 ≤ v := fun v hv => hw v (List.mem_cons_of_mem w hv)
    rw [spans_cons]
    exact List.Pairwise.cons (fun q hq => spans_from hrest (s + w) q hq)
      (spans_ordered hrest (s + w))

end Row

/-! ## Controls and readers -/

-- A reader of `spans_getElem?`: the third span of a row from 24 begins at 24 + 120 + 16.
#guard (Row.spans 24 [120, 16, 160])[2]? == some (160, 160)

-- A control for the premise of `spans_ordered`: with a negative length the first span ends at
-- 10, and the third begins at 3.
#guard Row.spans 0 [10, -7, 5] == [(0, 10), (10, -7), (3, 5)]

end Whatwg.Svg.Scene
