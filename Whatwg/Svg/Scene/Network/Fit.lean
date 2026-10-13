import Whatwg.Svg.Scene.Network.Laws

/-!
# Whatwg.Svg.Scene.Network.Fit

Owner: the scale that fits a flow network into a room (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; ask W18 of `docs/research/2026-10-12-whatwg-requests.md`).

A picture has a room, and a network must stand inside it. d3-sankey finds the scale from the
room: of each column it asks how much length the room has after the gaps between the column's
nodes, shares that length among the values of those nodes, and takes the least share over the
columns (`ky` of `initializeNodeBreadths`, `src/sankey.js` at `bb7233ea0004`). `Network.fit` of
`Whatwg/Svg/Scene/Network.lean` is that scale as a ratio of whole numbers, and these are its
laws.

- **Every column is inside the room** (`fit_fits`): with the scale `ratio` of `fit` and the
  gap that `fit` was given, each node ends at the room's height or before, wherever a column's
  gaps alone are no higher than the room. With `layout_fits` and `layout_clear` of
  `Whatwg/Svg/Scene/Network/Laws.lean`, the nodes are inside the caller's room and apart.
- **The scale is no more than the share of any column** (`fit_le`), and it is the share of one
  column or the whole room for one unit: its quantity is not nothing (`fit_pos`), so the scale
  divides by no zero.
- `sum_ratio_le`: lengths rounded down one by one are together no more than the length of the
  sum. This is why a column fits with the rounding.

What a caller must supply for `fit_fits`: that the gaps of each column alone fit the room.
d3 makes it so by lowering the gap (`py` of `computeNodeBreadths`); this module leaves the gap
to the caller.

What this module does not claim: that `fit` is the greatest scale that fits, which holds of
the exact ratio and which no law here states; that a column fills the room, since each length
is rounded down (the port `WhatwgTest/Svg/UseNetwork.lean` evaluates the loss at d3's example:
less than one unit for each node of the column).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Network

variable {ε ν : Type}

/-! ## Ratios of whole numbers -/

/-- The order of ratios goes through a ratio between: `a / b ≤ c / d` and `c / d ≤ e / f` give
`a / b ≤ e / f`, each written with no division. -/
theorem ratio_trans {a b c d e f : Nat} (hd : 0 < d) (h1 : a * d ≤ c * b) (h2 : c * f ≤ e * d) :
    a * f ≤ e * b := by
  have s1 : a * f * d ≤ c * b * f := by
    rw [Nat.mul_right_comm a f d]
    exact Nat.mul_le_mul_right f h1
  have s2 : c * b * f ≤ e * b * d := by
    rw [Nat.mul_right_comm c b f, Nat.mul_right_comm e b d]
    exact Nat.mul_le_mul_right b h2
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans s1 s2) hd

/-- Two quotients are together no more than the quotient of the sum. -/
theorem div_add_div_le (a b d : Nat) : a / d + b / d ≤ (a + b) / d := by
  by_cases hd : d = 0
  · rw [hd, Nat.div_zero, Nat.div_zero, Nat.div_zero]
    exact Nat.le_refl _
  · refine (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd)).mpr ?_
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self b d)

/-- **Lengths rounded down one by one are together no more than the length of the sum.** -/
theorem sum_ratio_le (num den : Nat) : ∀ xs : List Nat,
    (xs.map (ratio num den)).sum ≤ ratio num den xs.sum
  | [] => Nat.zero_le _
  | x :: xs => by
    have ih : (xs.map (ratio num den)).sum ≤ xs.sum * num / den := sum_ratio_le num den xs
    have h := div_add_div_le (x * num) (xs.sum * num) den
    show x * num / den + (xs.map (ratio num den)).sum ≤ (x :: xs).sum * num / den
    rw [List.sum_cons, Nat.add_mul]
    exact Nat.le_trans (Nat.add_le_add_left ih _) h

theorem lesser_pos {s best : Nat × Nat} (h : 0 < best.2) : 0 < (lesser s best).2 := by
  unfold lesser
  by_cases h0 : s.2 = 0
  · rw [if_pos h0]
    exact h
  · rw [if_neg h0]
    by_cases hlt : s.1 * best.2 < best.1 * s.2
    · rw [if_pos hlt]
      omega
    · rw [if_neg hlt]
      exact h

/-- The lesser of two ratios is no more than the second. -/
theorem lesser_le_right (s best : Nat × Nat) :
    (lesser s best).1 * best.2 ≤ best.1 * (lesser s best).2 := by
  unfold lesser
  by_cases h0 : s.2 = 0
  · rw [if_pos h0]
    exact Nat.le_refl _
  · rw [if_neg h0]
    by_cases hlt : s.1 * best.2 < best.1 * s.2
    · rw [if_pos hlt]
      exact Nat.le_of_lt hlt
    · rw [if_neg hlt]
      exact Nat.le_refl _

/-- The lesser of two ratios is no more than the first, where the first is of some
quantity. -/
theorem lesser_le_left {s best : Nat × Nat} (hs : 0 < s.2) :
    (lesser s best).1 * s.2 ≤ s.1 * (lesser s best).2 := by
  unfold lesser
  rw [if_neg (by omega)]
  by_cases hlt : s.1 * best.2 < best.1 * s.2
  · rw [if_pos hlt]
    exact Nat.le_refl _
  · rw [if_neg hlt]
    omega

/-! ## Sums down a column -/

/-- Some lengths with a gap after each are the lengths and as many gaps. -/
theorem sum_map_add (f : ν → Nat) (g : Nat) : ∀ l : List ν,
    (l.map fun u => f u + g).sum = (l.map f).sum + l.length * g
  | [] => by
    show 0 = 0 + 0 * g
    rw [Nat.zero_mul]
  | x :: l => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, sum_map_add f g l,
      List.length_cons, Nat.succ_mul]
    omega

section

variable [DecidableEq ν]

/-- A node, its length and a gap are within the lengths and gaps of the nodes of its column. -/
theorem topIn_le_column (len : ν → Nat) (gap : Nat) (col : ν → Nat) : ∀ (l : List ν) (v : ν),
    v ∈ l → topIn len gap col l v + len v + gap ≤
      ((l.filter fun u => decide (col u = col v)).map fun u => len u + gap).sum
  | [], _, h => nomatch h
  | x :: xs, v, h => by
    by_cases hx : x = v
    · subst hx
      rw [topIn_cons_self,
        List.filter_cons_of_pos (p := fun u => decide (col u = col x)) (decide_eq_true rfl),
        List.map_cons, List.sum_cons]
      omega
    · have hv : v ∈ xs := by
        cases List.mem_cons.mp h with
        | inl e => exact absurd e.symm hx
        | inr h' => exact h'
      have ih := topIn_le_column len gap col xs v hv
      rw [topIn_cons_ne len gap col hx]
      by_cases hc : col x = col v
      · rw [if_pos hc,
          List.filter_cons_of_pos (p := fun u => decide (col u = col v)) (decide_eq_true hc),
          List.map_cons, List.sum_cons]
        omega
      · rw [if_neg hc,
          List.filter_cons_of_neg (p := fun u => decide (col u = col v))
            (fun hh => hc (of_decide_eq_true hh))]
        omega

/-! ## The scale that fits -/

/-- **The ratio of `fit` is of a quantity that is not nothing**, so the scale `ratio` of it
divides by no zero. -/
theorem fit_pos (n : Network ε ν) (col : ν → Nat) (gap room : Nat) :
    0 < (n.fit col gap room).2 := by
  have key : ∀ l : List Nat,
      0 < (l.foldr (fun c best => lesser (n.share col gap room c) best) (room, 1)).2 := by
    intro l
    induction l with
    | nil => exact Nat.one_pos
    | cons c l ih => exact lesser_pos ih
  exact key _

/-- **The scale that fits is no more than the share of any column** whose nodes have a
value. -/
theorem fit_le (n : Network ε ν) (col : ν → Nat) (gap room : Nat) {v : ν} (hv : v ∈ n.nodes)
    (hs : 0 < (n.share col gap room (col v)).2) :
    (n.fit col gap room).1 * (n.share col gap room (col v)).2 ≤
      (n.share col gap room (col v)).1 * (n.fit col gap room).2 := by
  have pos : ∀ l : List Nat,
      0 < (l.foldr (fun c best => lesser (n.share col gap room c) best) (room, 1)).2 := by
    intro l
    induction l with
    | nil => exact Nat.one_pos
    | cons c l ih => exact lesser_pos ih
  have key : ∀ l : List Nat, col v ∈ l →
      (l.foldr (fun c best => lesser (n.share col gap room c) best) (room, 1)).1 *
          (n.share col gap room (col v)).2 ≤
        (n.share col gap room (col v)).1 *
          (l.foldr (fun c best => lesser (n.share col gap room c) best) (room, 1)).2 := by
    intro l
    induction l with
    | nil => exact fun h => nomatch h
    | cons x l ih =>
      intro h
      rw [List.foldr_cons]
      cases List.mem_cons.mp h with
      | inl e =>
        rw [← e]
        exact lesser_le_left hs
      | inr h' => exact ratio_trans (pos l) (lesser_le_right _ _) (ih h')
  exact key _ (List.mem_map_of_mem hv)

/-- **Every column is inside the room that the scale was fitted to.** With the scale `ratio`
of `fit` and the gap that `fit` was given, each node ends at the room's height or before,
where the gaps of each column alone are no higher than the room. -/
theorem fit_fits (n : Network ε ν) {m : Measure} (col : ν → Nat) {room : Nat}
    (hm : m.scale = ratio (n.fit col m.gap room).1 (n.fit col m.gap room).2)
    (hgap : ∀ v ∈ n.nodes,
      ((n.nodes.filter fun u => decide (col u = col v)).length - 1) * m.gap ≤ room)
    {v : ν} (hv : v ∈ n.nodes) : n.top m col v + n.length m v ≤ room := by
  have h1 : n.top m col v + n.length m v + m.gap ≤
      ((n.nodes.filter fun u => decide (col u = col v)).map fun u => n.length m u + m.gap).sum :=
    topIn_le_column (n.length m) m.gap col n.nodes v hv
  rw [sum_map_add] at h1
  have hmem : v ∈ n.nodes.filter fun u => decide (col u = col v) :=
    List.mem_filter.mpr ⟨hv, decide_eq_true rfl⟩
  have hlen : 0 < (n.nodes.filter fun u => decide (col u = col v)).length :=
    List.length_pos_of_mem hmem
  have hsplit : (n.nodes.filter fun u => decide (col u = col v)).length * m.gap =
      ((n.nodes.filter fun u => decide (col u = col v)).length - 1) * m.gap + m.gap := by
    have e := Nat.succ_mul ((n.nodes.filter fun u => decide (col u = col v)).length - 1) m.gap
    rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hlen] at e
    exact e
  have hg := hgap v hv
  have h2 : ((n.nodes.filter fun u => decide (col u = col v)).map (n.length m)).sum ≤
      (n.share col m.gap room (col v)).1 := by
    have e : (n.nodes.filter fun u => decide (col u = col v)).map (n.length m) =
        ((n.nodes.filter fun u => decide (col u = col v)).map n.value).map
          (ratio (n.fit col m.gap room).1 (n.fit col m.gap room).2) := by
      rw [List.map_map, ← hm]
      rfl
    rw [e]
    refine Nat.le_trans (sum_ratio_le _ _ _) ?_
    show (n.share col m.gap room (col v)).2 * (n.fit col m.gap room).1 /
      (n.fit col m.gap room).2 ≤ (n.share col m.gap room (col v)).1
    by_cases h0 : (n.share col m.gap room (col v)).2 = 0
    · rw [h0, Nat.zero_mul, Nat.zero_div]
      exact Nat.zero_le _
    · have hle := fit_le n col m.gap room hv (Nat.pos_of_ne_zero h0)
      refine Nat.div_le_of_le_mul ?_
      rw [Nat.mul_comm (n.share col m.gap room (col v)).2, Nat.mul_comm (n.fit col m.gap room).2]
      exact hle
  have h3 : (n.share col m.gap room (col v)).1 =
      room - ((n.nodes.filter fun u => decide (col u = col v)).length - 1) * m.gap := rfl
  omega

end

end Network

end Whatwg.Svg.Scene
