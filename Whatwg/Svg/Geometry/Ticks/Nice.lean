import Whatwg.Svg.Geometry.Ticks.Laws

/-!
# Whatwg.Svg.Geometry.Ticks.Nice

Owner: the laws of a range moved out to round numbers (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

d3 tests `nice` on fourteen ranges, and tests on seventeen more that the ticks of a nice range
begin and end at its ends (`d3-array`, `test/nice-test.js`; `d3-scale`, `test/linear-test.js`,
"linear.ticks(X) spans linear.nice(X).domain()"). Here both hold of every range.

- **A nice range holds the range** (`nice_contains`): its low end is no more and its high end no
  less, whatever the count and the rounds.
- **A nice range is the range as it was, or is settled** (`nice_settled`): `nice` never answers
  a range that is half moved.
- **The ends of a settled range are its first and its last tick** (`settled_ends`). So the
  axis of a nice range has a tick at each end.

What this module does not claim: that `nice` settles. With the count `1` and zero inside the
range it need not (the header of `Ticks.lean` has the case). Nor that a nice range is the
least settled range that holds the range.
-/

namespace Whatwg.Svg.Value

namespace Ticks

/-! ## A range moved out to the multiples of a step -/

/-- **A range moved out to the multiples of a step holds the range.** -/
theorem widen_contains (start stop : Rat) {s : Decimal} (hs : 0 < s.toRat) :
    (widen start stop s).1 ≤ start ∧ stop ≤ (widen start stop s).2 :=
  ⟨(le_high_iff hs (high start s)).mp (Int.le_refl _),
    (low_le_iff hs (low stop s)).mp (Int.le_refl _)⟩

theorem floor_mul_div {s : Rat} (hs : 0 < s) (i : Int) : (((i : Rat) * s) / s).floor = i := by
  rw [Rat.mul_div_cancel (Rat.ne_of_gt hs), Rat.floor_intCast]

theorem ceil_mul_div {s : Rat} (hs : 0 < s) (i : Int) : (((i : Rat) * s) / s).ceil = i := by
  rw [Rat.mul_div_cancel (Rat.ne_of_gt hs), Rat.ceil_intCast]

/-- A range whose ends are multiples of a step is not moved by the step. -/
theorem widen_of_multiples {s : Decimal} (hs : 0 < s.toRat) (i j : Int) :
    widen ((i : Rat) * s.toRat) ((j : Rat) * s.toRat) s =
      ((i : Rat) * s.toRat, (j : Rat) * s.toRat) := by
  unfold widen
  rw [floor_mul_div hs, ceil_mul_div hs]

/-! ## Rounds -/

theorem settle_succ (count rounds : Nat) (before : Decimal) (start stop : Rat) :
    settle count (rounds + 1) before start stop =
      if step start stop count = before then some (start, stop)
      else
        settle count rounds (step start stop count) (widen start stop (step start stop count)).1
          (widen start stop (step start stop count)).2 := rfl

/-- What the rounds answer holds the range that they began with. -/
theorem settle_contains (count : Nat) : ∀ (rounds : Nat) (before : Decimal) (start stop : Rat)
    (r : Rat × Rat), settle count rounds before start stop = some r → r.1 ≤ start ∧ stop ≤ r.2
  | 0, _, _, _, _, h => nomatch h
  | rounds + 1, before, start, stop, r, h => by
    rw [settle_succ] at h
    by_cases hs : step start stop count = before
    · rw [if_pos hs] at h
      cases h
      exact ⟨Rat.le_refl, Rat.le_refl⟩
    · rw [if_neg hs] at h
      have ih := settle_contains count rounds _ _ _ r h
      have w := widen_contains start stop (step_pos start stop count)
      exact ⟨Rat.le_trans ih.1 w.1, Rat.le_trans w.2 ih.2⟩

/-- What the rounds answer is settled, where they began with multiples of the step before. -/
theorem settle_settled (count : Nat) : ∀ (rounds : Nat) (before : Decimal) (i j : Int)
    (r : Rat × Rat), 0 < before.toRat →
      settle count rounds before ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) = some r →
      Settled r.1 r.2 count
  | 0, _, _, _, _, _, h => nomatch h
  | rounds + 1, before, i, j, r, hb, h => by
    rw [settle_succ] at h
    by_cases hs : step ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) count = before
    · rw [if_pos hs] at h
      cases h
      show widen ((i : Rat) * before.toRat) ((j : Rat) * before.toRat)
          (step ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) count) =
        ((i : Rat) * before.toRat, (j : Rat) * before.toRat)
      rw [hs]
      exact widen_of_multiples hb i j
    · rw [if_neg hs] at h
      exact settle_settled count rounds
        (step ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) count)
        (high ((i : Rat) * before.toRat)
          (step ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) count))
        (low ((j : Rat) * before.toRat)
          (step ((i : Rat) * before.toRat) ((j : Rat) * before.toRat) count))
        r (step_pos _ _ count) h

/-! ## A nice range -/

/-- **A nice range holds the range.** -/
theorem nice_contains {start stop : Rat} (h : start < stop) (count rounds : Nat) :
    (nice start stop count rounds).1 ≤ start ∧ stop ≤ (nice start stop count rounds).2 := by
  unfold nice
  by_cases hn : count = 0 ∨ start = stop
  · rw [if_pos hn]
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  · rw [if_neg hn, if_pos h]
    cases hr : settle count rounds (step start stop count)
        (widen start stop (step start stop count)).1
        (widen start stop (step start stop count)).2 with
    | none => exact ⟨Rat.le_refl, Rat.le_refl⟩
    | some r =>
      have c := settle_contains count rounds _ _ _ r hr
      have w := widen_contains start stop (step_pos start stop count)
      exact ⟨Rat.le_trans c.1 w.1, Rat.le_trans w.2 c.2⟩

/-- **A nice range is the range as it was, or is settled.** -/
theorem nice_settled {start stop : Rat} (h : start < stop) (count rounds : Nat) :
    nice start stop count rounds = (start, stop) ∨
      Settled (nice start stop count rounds).1 (nice start stop count rounds).2 count := by
  unfold nice
  by_cases hn : count = 0 ∨ start = stop
  · rw [if_pos hn]
    exact Or.inl rfl
  · rw [if_neg hn, if_pos h]
    cases hr : settle count rounds (step start stop count)
        (widen start stop (step start stop count)).1
        (widen start stop (step start stop count)).2 with
    | none => exact Or.inl rfl
    | some r =>
      exact Or.inr (settle_settled count rounds (step start stop count)
        (high start (step start stop count)) (low stop (step start stop count)) r
        (step_pos start stop count) hr)

/-! ## The ticks of a settled range -/

/-- The multiples of a step between two of its multiples begin at the first and end at the
second. -/
theorem between_ends {s : Decimal} (hs : 0 < s.toRat) {i j : Int} (hij : i ≤ j) :
    ((between ((i : Rat) * s.toRat) ((j : Rat) * s.toRat) s).map Decimal.toRat).head? =
        some ((i : Rat) * s.toRat) ∧
      ((between ((i : Rat) * s.toRat) ((j : Rat) * s.toRat) s).map Decimal.toRat).getLast? =
        some ((j : Rat) * s.toRat) := by
  have el : low ((i : Rat) * s.toRat) s = i := ceil_mul_div hs i
  have eh : high ((j : Rat) * s.toRat) s = j := floor_mul_div hs j
  have hn : (j - i + 1).toNat ≠ 0 := by omega
  have e0 : i + ((0 : Nat) : Int) = i := by omega
  have e1 : i + (((j - i + 1).toNat - 1 : Nat) : Int) = j := by omega
  unfold between
  rw [el, eh, List.map_map]
  constructor
  · rw [List.head?_map, List.head?_range, if_neg hn]
    show some ((times s (i + ((0 : Nat) : Int))).toRat) = some ((i : Rat) * s.toRat)
    rw [e0, toRat_times]
  · rw [List.getLast?_map, List.getLast?_range, if_neg hn]
    show some ((times s (i + (((j - i + 1).toNat - 1 : Nat) : Int))).toRat) =
      some ((j : Rat) * s.toRat)
    rw [e1, toRat_times]

/-- **The ends of a settled range are its first and its last tick.** With `nice_settled`: the
ticks of a nice range span it, where `nice` settled. -/
theorem settled_ends {start stop : Rat} (h : start < stop) {count : Nat} (hc : count ≠ 0)
    (hs : Settled start stop count) :
    (values start stop count).head? = some start ∧
      (values start stop count).getLast? = some stop := by
  have hS := step_pos start stop count
  have e1 : ((high start (step start stop count) : Int) : Rat) * (step start stop count).toRat =
      start := congrArg Prod.fst hs
  have e2 : ((low stop (step start stop count) : Int) : Rat) * (step start stop count).toRat =
      stop := congrArg Prod.snd hs
  have hij : high start (step start stop count) ≤ low stop (step start stop count) := by
    have hlt : ((high start (step start stop count) : Int) : Rat) * (step start stop count).toRat <
        ((low stop (step start stop count) : Int) : Rat) * (step start stop count).toRat := by
      rw [e1, e2]
      exact h
    exact Int.le_of_lt (Rat.intCast_lt_intCast.mp ((Rat.mul_lt_mul_right hS).mp hlt))
  have key := between_ends hS hij
  rw [e1, e2] at key
  unfold values ticks
  rw [if_neg fun hn => hn.elim hc (Rat.ne_of_lt h), if_pos h]
  exact key

end Ticks

end Whatwg.Svg.Value
