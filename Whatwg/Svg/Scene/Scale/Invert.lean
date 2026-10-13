import Whatwg.Svg.Scene.Scale

/-!
# Whatwg.Svg.Scene.Scale.Invert

Owner: the value under a mark (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Scale.at` goes from a quantity to a length. A program that answers a pointer, cuts a picture
at an edge or labels a place goes the other way: which quantity is drawn here? A scale in whole
numbers rounds, and draws some values alike, so there is no inverse in the plain sense. There is
the next best thing, and it is exact: the value whose mark is the nearest mark at or before the
place asked for.

- `Scale.domain s`: the range of the data, the least and the greatest value that the scale
  can tell from its neighbours.
- `Scale.invert s y`: the value of the domain under the mark `y`. On a scale that rises it is
  the greatest value whose mark is no more than `y`. On a scale that falls it is the least
  such value. It is found by halving the domain, so it is defined for every kind of scale, and
  costs as many readings of `Scale.at` as the domain has binary digits.
- `Scale.search`: the halving, for any map of whole numbers.

What the laws say:

- **The law of a rising scale** (`at_invert_le`, `lt_at_invert_succ`): for a mark `y` from the
  first mark to before the last, `at (invert y) ≤ y < at (invert y + 1)`. The cell of a value
  runs from its mark to the mark of the next value, and `invert` names the cell that `y` is in.
- **The law of a falling scale** (`at_invert_le_of_falling`, `lt_at_invert_pred`):
  `at (invert y) ≤ y < at (invert y - 1)`. The cell of a value runs from its mark to the mark
  of the value before it.
- **One law for both** (`invert_nearest`): the mark of `invert y` is no more than `y`, and no
  value of the domain has a mark that is nearer `y` from below.
- **An adjoint** (`invert_galois`, `invert_galois_of_falling`): on a rising scale
  `at v ≤ y ↔ v ≤ invert y` for a value of the domain, and on a falling one
  `at v ≤ y ↔ invert y ≤ v`. Every other law here follows from these two and from
  `Scale.at_mono` and `Scale.at_anti`, and a caller that chains scales chains these.
- **From a value and back** (`le_invert_at`, `at_invert_at`, `invert_at_of_lt`): on a rising
  scale `invert (at v)` is no less than `v` and is drawn as `v` is, so it is the last value
  that the scale draws like `v`. Where the next value is drawn longer, it is `v` itself. So a
  `linear` scale with a unit of length or more for each unit of the quantity gives back every
  value of its domain (`invert_at_linear`). On a falling scale `invert (at v)` is the first
  value drawn like `v` (`invert_at_le`, `at_invert_at_of_falling`).
- **From a mark and back** (`at_invert_at`, `at_invert_linear`): `at (invert y)` is `y` where
  `y` is the mark of some value of the domain, and otherwise the nearest mark before `y`. A
  `linear` scale with a unit of the quantity or more for each unit of length has a value at
  every length of its range, so it gives back every mark.
- `invert_mem`: the answer is always a value of the domain. `invert_of_lt`, `invert_of_le`: a
  place before the first mark of a rising scale answers the low end of the domain, and a place
  at the last mark or past it the high end, as `Scale.at` draws a value outside its range at
  the nearer end.

For a straight line, `Whatwg/Svg/Scene/Scale/Linear.lean` says how far the answer is from the
value or the mark asked for, where the scale rounds.

A scale with ties. Where two values are drawn alike, no function gives both back. On a rising
scale `invert` gives the greater of them, and on a falling one the lesser: `(v, invert (at v))`
is then a pair of `Scale.ties`, by `Scale.mem_ties` and `at_invert_at`.

How this differs from d3 (`d3-scale` at `d6904a4bde09`, `src/continuous.js`), which inverts in
floating point by the same straight line read backwards. d3 answers a fraction, and this
module a whole value of the domain. d3 without `clamp` goes on past the ends of the range, and
`Scale.at` holds a value at the nearer end, so this module answers as d3 with `clamp(true)`
does. For a range of one length d3 answers the middle of the domain, and this module the last
value of a rising scale: every value is then drawn alike, and the adjoint picks one end.

What this module does not claim: a closed form of the answer for a `linear` scale, which is a
straight line rounded once and which no law here states; that a `steps` scale draws every
value outside its `domain` as the nearer end, which holds and is not proved; an inverse of a
scale that neither rises nor falls.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Scale

/-! ## The greatest place that a map has not passed -/

/-- The greatest `v` from `a` to `a + n` with `f v ≤ y`, by halving, where `f` never falls there
and `f a ≤ y`. The first number bounds the count of halvings: `n` is always enough. -/
def search (f : Int → Int) (y : Int) : Nat → Int → Nat → Int
  | 0, a, _ => a
  | fuel + 1, a, n =>
    if n = 0 then a
    else if f (a + ((n + 1) / 2 : Nat)) ≤ y then
      search f y fuel (a + ((n + 1) / 2 : Nat)) (n - (n + 1) / 2)
    else search f y fuel a ((n + 1) / 2 - 1)

theorem search_zero (f : Int → Int) (y a : Int) (n : Nat) : search f y 0 a n = a := rfl

theorem search_succ (f : Int → Int) (y : Int) (fuel : Nat) (a : Int) (n : Nat) :
    search f y (fuel + 1) a n =
      if n = 0 then a
      else if f (a + ((n + 1) / 2 : Nat)) ≤ y then
        search f y fuel (a + ((n + 1) / 2 : Nat)) (n - (n + 1) / 2)
      else search f y fuel a ((n + 1) / 2 - 1) := rfl

/-- What a search finds is among the places searched, whatever the map. -/
theorem search_mem (f : Int → Int) (y : Int) : ∀ (fuel : Nat) (a : Int) (n : Nat),
    a ≤ search f y fuel a n ∧ search f y fuel a n ≤ a + n
  | 0, a, n => by
    rw [search_zero]
    exact ⟨Int.le_refl a, by omega⟩
  | fuel + 1, a, n => by
    rw [search_succ]
    rcases Decidable.em (n = 0) with h0 | h0
    · rw [if_pos h0]
      exact ⟨Int.le_refl a, by omega⟩
    · rw [if_neg h0]
      rcases Decidable.em (f (a + ((n + 1) / 2 : Nat)) ≤ y) with hf | hf
      · rw [if_pos hf]
        have ih := search_mem f y fuel (a + ((n + 1) / 2 : Nat)) (n - (n + 1) / 2)
        have h1 := ih.1
        have h2 := ih.2
        exact ⟨by omega, by omega⟩
      · rw [if_neg hf]
        have ih := search_mem f y fuel a ((n + 1) / 2 - 1)
        have h2 := ih.2
        exact ⟨ih.1, by omega⟩

/-- **What a search finds**: a place `r` from `a` to `a + n` that the map has not passed, which
is the last place or is followed by a place that the map has passed. -/
structure Found (f : Int → Int) (y a : Int) (n : Nat) (r : Int) : Prop where
  /-- It is no less than the first place. -/
  lo : a ≤ r
  /-- It is no more than the last place. -/
  hi : r ≤ a + n
  /-- The map has not passed `y` there. -/
  le : f r ≤ y
  /-- It is the last place, or the map has passed `y` at the next. -/
  last : r = a + n ∨ y < f (r + 1)

/-- A search with halvings enough, from a place that the map has not passed, finds such a
place. No premise says that the map never falls: that premise is what makes the place the only
one (`Found.galois`). -/
theorem search_found (f : Int → Int) (y : Int) : ∀ (fuel : Nat) (a : Int) (n : Nat), n ≤ fuel →
    f a ≤ y → Found f y a n (search f y fuel a n)
  | 0, a, n, hn, ha => by
    rw [search_zero]
    exact ⟨Int.le_refl a, by omega, ha, Or.inl (by omega)⟩
  | fuel + 1, a, n, hn, ha => by
    rw [search_succ]
    rcases Decidable.em (n = 0) with h0 | h0
    · rw [if_pos h0]
      exact ⟨Int.le_refl a, by omega, ha, Or.inl (by omega)⟩
    · rw [if_neg h0]
      rcases Decidable.em (f (a + ((n + 1) / 2 : Nat)) ≤ y) with hf | hf
      · rw [if_pos hf]
        have ih := search_found f y fuel (a + ((n + 1) / 2 : Nat)) (n - (n + 1) / 2) (by omega) hf
        have h1 := ih.lo
        have h2 := ih.hi
        refine ⟨by omega, by omega, ih.le, ?_⟩
        rcases ih.last with e | e
        · exact Or.inl (by omega)
        · exact Or.inr e
      · rw [if_neg hf]
        have ih := search_found f y fuel a ((n + 1) / 2 - 1) (by omega) ha
        have h2 := ih.hi
        refine ⟨ih.lo, by omega, ih.le, ?_⟩
        rcases ih.last with e | e
        · have e' : search f y fuel a ((n + 1) / 2 - 1) + 1 = a + ((n + 1) / 2 : Nat) := by omega
          rw [e']
          exact Or.inr (Int.not_le.mp hf)
        · exact Or.inr e

/-- **A place found is the adjoint.** Where the map never falls from `a` to `a + n`, the map has
not passed `y` at a place exactly when the place is no later than the one found. So the place
found is the only one that `Found` holds of. -/
theorem Found.galois {f : Int → Int} {y a : Int} {n : Nat} {r : Int} (h : Found f y a n r)
    (hm : ∀ u w : Int, a ≤ u → u ≤ w → w ≤ a + n → f u ≤ f w) {v : Int} (h1 : a ≤ v)
    (h2 : v ≤ a + n) : f v ≤ y ↔ v ≤ r := by
  constructor
  · intro hv
    rcases h.last with e | e
    · omega
    · refine Int.not_lt.mp fun hlt => ?_
      have h0 := h.lo
      have h3 := hm (r + 1) v (by omega) (by omega) h2
      omega
  · intro hv
    exact Int.le_trans (hm v r h1 hv h.hi) h.le

/-- A search over places that the map has all passed, but perhaps the first, answers the
first. -/
theorem search_of_lt (f : Int → Int) (y : Int) : ∀ (fuel : Nat) (a : Int) (n : Nat),
    (∀ v : Int, a < v → v ≤ a + n → y < f v) → search f y fuel a n = a
  | 0, a, n, _ => search_zero f y a n
  | fuel + 1, a, n, h => by
    rw [search_succ]
    rcases Decidable.em (n = 0) with h0 | h0
    · rw [if_pos h0]
    · rw [if_neg h0, if_neg (Int.not_le.mpr (h _ (by omega) (by omega)))]
      exact search_of_lt f y fuel a _ fun v h1 h2 => h v h1 (by omega)

/-! ## The range of the data -/

/-- The least threshold less one, and the greatest threshold: a value below the first is drawn
at the base level, and a value past the second at the last level. -/
def stepsDomain : List (Int × Int) → Int × Int
  | [] => (0, 0)
  | (t, _) :: rest =>
    (rest.foldl (fun m p => min m p.1) t - 1, rest.foldl (fun m p => max m p.1) t)

/-- **The range of the data**: the least and the greatest value that the scale can tell from
its neighbours. A value outside it is drawn as the nearer end is. -/
def domain : Scale → Int × Int
  | .linear dataLo dataHi _ _ => (dataLo, dataHi)
  | .root _ dataLo dataHi _ _ => (dataLo, dataHi)
  | .log2 dataLo dataHi _ _ => ((dataLo : Int), (dataHi : Int))
  | .steps _ levels => stepsDomain levels

/-- **The value under a mark.** On a scale that rises, the greatest value of the domain whose
mark is no more than `y`. On a scale that falls and does not rise, the least such value. A mark
before all the marks of the scale answers the end of the domain that is drawn there. -/
def invert (s : Scale) (y : Int) : Int :=
  if s.Rising then
    search s.at y (s.domain.2 - s.domain.1).toNat s.domain.1 (s.domain.2 - s.domain.1).toNat
  else
    s.domain.2 -
      search (fun k => s.at (s.domain.2 - k)) y (s.domain.2 - s.domain.1).toNat 0
        (s.domain.2 - s.domain.1).toNat

/-- **The value under a mark is a value of the domain**, on every scale and for every mark. -/
theorem invert_mem (s : Scale) (hd : s.domain.1 ≤ s.domain.2) (y : Int) :
    s.domain.1 ≤ s.invert y ∧ s.invert y ≤ s.domain.2 := by
  unfold invert
  rcases Decidable.em s.Rising with hr | hr
  · rw [if_pos hr]
    have h := search_mem s.at y (s.domain.2 - s.domain.1).toNat s.domain.1
      (s.domain.2 - s.domain.1).toNat
    have h1 := h.1
    have h2 := h.2
    exact ⟨h1, by omega⟩
  · rw [if_neg hr]
    have h := search_mem (fun k => s.at (s.domain.2 - k)) y (s.domain.2 - s.domain.1).toNat 0
      (s.domain.2 - s.domain.1).toNat
    have h1 := h.1
    have h2 := h.2
    exact ⟨by omega, by omega⟩

/-! ## A scale that rises -/

/-- What `invert` finds on a scale that rises. -/
theorem found_of_rising (s : Scale) (hr : s.Rising) {y : Int} (hy : s.at s.domain.1 ≤ y) :
    Found s.at y s.domain.1 (s.domain.2 - s.domain.1).toNat (s.invert y) := by
  unfold invert
  rw [if_pos hr]
  exact search_found s.at y _ _ _ (Nat.le_refl _) hy

/-- **The mark of the value under a mark is no later than the mark**, on a scale that rises and
for a mark no earlier than its first. -/
theorem at_invert_le (s : Scale) (hr : s.Rising) {y : Int} (hy : s.at s.domain.1 ≤ y) :
    s.at (s.invert y) ≤ y :=
  (found_of_rising s hr hy).le

/-- **The adjoint of a rising scale.** A value of the domain is drawn at `y` or before it
exactly when it is no more than the value under `y`. -/
theorem invert_galois (s : Scale) (hr : s.Rising) {y : Int} (hy : s.at s.domain.1 ≤ y) {v : Int}
    (h1 : s.domain.1 ≤ v) (h2 : v ≤ s.domain.2) : s.at v ≤ y ↔ v ≤ s.invert y :=
  (found_of_rising s hr hy).galois (fun _ _ _ huw _ => at_mono s hr huw) h1 (by omega)

/-- **The next value is drawn past the mark.** With `at_invert_le`, this is the law of a rising
scale: `at (invert y) ≤ y < at (invert y + 1)`, for a mark from the first to before the last. -/
theorem lt_at_invert_succ (s : Scale) (hr : s.Rising) (hd : s.domain.1 ≤ s.domain.2) {y : Int}
    (hy : s.at s.domain.1 ≤ y) (hlt : y < s.at s.domain.2) : y < s.at (s.invert y + 1) := by
  have h := found_of_rising s hr hy
  rcases h.last with e | e
  · have e' : s.invert y = s.domain.2 := by omega
    have hle := h.le
    rw [e'] at hle
    exact absurd hlt (Int.not_lt.mpr hle)
  · exact e

/-- A value of the domain is no more than the value under its own mark. -/
theorem le_invert_at (s : Scale) (hr : s.Rising) {v : Int} (h1 : s.domain.1 ≤ v)
    (h2 : v ≤ s.domain.2) : v ≤ s.invert (s.at v) :=
  (invert_galois s hr (at_mono s hr h1) h1 h2).mp (Int.le_refl _)

/-- **From a value to its mark and back gives a value that is drawn alike.** On a rising scale
it is the last value of the domain that the scale draws as it draws `v`. Read from the other
side: a mark of the scale is given back exactly. -/
theorem at_invert_at (s : Scale) (hr : s.Rising) {v : Int} (h1 : s.domain.1 ≤ v)
    (h2 : v ≤ s.domain.2) : s.at (s.invert (s.at v)) = s.at v :=
  Int.le_antisymm (at_invert_le s hr (at_mono s hr h1)) (at_mono s hr (le_invert_at s hr h1 h2))

/-- **Where the next value is drawn longer, a value is given back.** -/
theorem invert_at_of_lt (s : Scale) (hr : s.Rising) {v : Int} (h1 : s.domain.1 ≤ v)
    (h2 : v < s.domain.2) (hlt : s.at v < s.at (v + 1)) : s.invert (s.at v) = v := by
  have hle := le_invert_at s hr h1 (Int.le_of_lt h2)
  have hn : ¬ v + 1 ≤ s.invert (s.at v) := fun h =>
    absurd ((invert_galois s hr (at_mono s hr h1) (by omega) (by omega)).mpr h) (Int.not_le.mpr hlt)
  omega

/-- The last value of the domain is given back. -/
theorem invert_at_last (s : Scale) (hr : s.Rising) (hd : s.domain.1 ≤ s.domain.2) :
    s.invert (s.at s.domain.2) = s.domain.2 :=
  Int.le_antisymm (invert_mem s hd _).2 (le_invert_at s hr hd (Int.le_refl _))

/-- **A place at the last mark or past it answers the high end of the domain**, on a scale that
rises. -/
theorem invert_of_le (s : Scale) (hr : s.Rising) (hd : s.domain.1 ≤ s.domain.2) {y : Int}
    (hy : s.at s.domain.2 ≤ y) : s.invert y = s.domain.2 :=
  Int.le_antisymm (invert_mem s hd y).2
    ((invert_galois s hr (Int.le_trans (at_mono s hr hd) hy) hd (Int.le_refl _)).mp hy)

/-- **A place before the first mark answers the low end of the domain**, on a scale that
rises. -/
theorem invert_of_lt (s : Scale) (hr : s.Rising) {y : Int} (hy : y < s.at s.domain.1) :
    s.invert y = s.domain.1 := by
  unfold invert
  rw [if_pos hr]
  exact search_of_lt s.at y _ _ _ fun v h1 _ =>
    Int.lt_of_lt_of_le hy (at_mono s hr (Int.le_of_lt h1))

/-! ## A scale that falls -/

/-- What `invert` finds on a scale that falls and does not rise, counted back from the high end
of the domain. -/
theorem found_of_falling (s : Scale) (hn : ¬ s.Rising) {y : Int} (hy : s.at s.domain.2 ≤ y) :
    Found (fun k => s.at (s.domain.2 - k)) y 0 (s.domain.2 - s.domain.1).toNat
      (s.domain.2 - s.invert y) := by
  have e : ∀ r : Int, s.domain.2 - (s.domain.2 - r) = r := fun r => by omega
  unfold invert
  rw [if_neg hn, e]
  refine search_found _ y _ 0 _ (Nat.le_refl _) ?_
  show s.at (s.domain.2 - 0) ≤ y
  rw [Int.sub_zero]
  exact hy

/-- **The mark of the value under a mark is no later than the mark**, on a scale that falls and
for a mark no earlier than its least. -/
theorem at_invert_le_of_falling (s : Scale) (hn : ¬ s.Rising) {y : Int}
    (hy : s.at s.domain.2 ≤ y) : s.at (s.invert y) ≤ y := by
  have h : s.at (s.domain.2 - (s.domain.2 - s.invert y)) ≤ y := (found_of_falling s hn hy).le
  have e : s.domain.2 - (s.domain.2 - s.invert y) = s.invert y := by omega
  rw [e] at h
  exact h

/-- **The adjoint of a falling scale.** A value of the domain is drawn at `y` or before it
exactly when it is no less than the value under `y`. -/
theorem invert_galois_of_falling (s : Scale) (hf : s.Falling) (hn : ¬ s.Rising) {y : Int}
    (hy : s.at s.domain.2 ≤ y) {v : Int} (h1 : s.domain.1 ≤ v) (h2 : v ≤ s.domain.2) :
    s.at v ≤ y ↔ s.invert y ≤ v := by
  have g : s.at (s.domain.2 - (s.domain.2 - v)) ≤ y ↔ s.domain.2 - v ≤ s.domain.2 - s.invert y :=
    (found_of_falling s hn hy).galois
      (fun u w _ huw _ => at_anti s hf (by omega : s.domain.2 - w ≤ s.domain.2 - u))
      (v := s.domain.2 - v) (by omega) (by omega)
  have e : s.domain.2 - (s.domain.2 - v) = v := by omega
  rw [e] at g
  constructor
  · intro hv
    have h := g.mp hv
    omega
  · intro hv
    exact g.mpr (by omega)

/-- **The value before is drawn past the mark.** With `at_invert_le_of_falling`, this is the law
of a falling scale: `at (invert y) ≤ y < at (invert y - 1)`, for a mark from the least to
before the greatest. -/
theorem lt_at_invert_pred (s : Scale) (hn : ¬ s.Rising) (hd : s.domain.1 ≤ s.domain.2) {y : Int}
    (hy : s.at s.domain.2 ≤ y) (hlt : y < s.at s.domain.1) : y < s.at (s.invert y - 1) := by
  have h := found_of_falling s hn hy
  rcases h.last with e | e
  · have e' : s.invert y = s.domain.1 := by omega
    have hle := at_invert_le_of_falling s hn hy
    rw [e'] at hle
    exact absurd hlt (Int.not_lt.mpr hle)
  · have e' : s.domain.2 - (s.domain.2 - s.invert y + 1) = s.invert y - 1 := by omega
    have e2 : y < s.at (s.domain.2 - (s.domain.2 - s.invert y + 1)) := e
    rw [e'] at e2
    exact e2

/-- The value under the mark of a value of the domain is no more than the value. -/
theorem invert_at_le (s : Scale) (hf : s.Falling) (hn : ¬ s.Rising) {v : Int}
    (h1 : s.domain.1 ≤ v) (h2 : v ≤ s.domain.2) : s.invert (s.at v) ≤ v :=
  (invert_galois_of_falling s hf hn (at_anti s hf h2) h1 h2).mp (Int.le_refl _)

/-- **From a value to its mark and back gives a value that is drawn alike**: on a falling scale,
the first value of the domain that the scale draws as it draws `v`. -/
theorem at_invert_at_of_falling (s : Scale) (hf : s.Falling) (hn : ¬ s.Rising) {v : Int}
    (h1 : s.domain.1 ≤ v) (h2 : v ≤ s.domain.2) :
    s.at (s.invert (s.at v)) = s.at v :=
  Int.le_antisymm (at_invert_le_of_falling s hn (at_anti s hf h2))
    (at_anti s hf (invert_at_le s hf hn h1 h2))

/-! ## One law for both -/

/-- **The value under a mark has the nearest mark at or before it.** Let a scale rise, or fall
and not rise, and let `y` be no earlier than the least of its marks. Then the mark of `invert y`
is no later than `y`, and no value of the domain has a mark between the two. -/
theorem invert_nearest (s : Scale) (h : s.Rising ∨ (s.Falling ∧ ¬ s.Rising)) {y : Int}
    (hy : (s.Rising → s.at s.domain.1 ≤ y) ∧ (¬ s.Rising → s.at s.domain.2 ≤ y)) :
    s.at (s.invert y) ≤ y ∧
      ∀ w : Int, s.domain.1 ≤ w → w ≤ s.domain.2 → s.at w ≤ y → s.at w ≤ s.at (s.invert y) := by
  rcases h with hr | ⟨hf, hn⟩
  · exact ⟨at_invert_le s hr (hy.1 hr), fun w h1 h2 hw =>
      at_mono s hr ((invert_galois s hr (hy.1 hr) h1 h2).mp hw)⟩
  · exact ⟨at_invert_le_of_falling s hn (hy.2 hn), fun w h1 h2 hw =>
      at_anti s hf ((invert_galois_of_falling s hf hn (hy.2 hn) h1 h2).mp hw)⟩

/-! ## A straight line -/

/-- **A scale that is long enough gives back every value.** A `linear` scale with one unit of
length or more for each unit of the quantity draws no two values of its range alike
(`Scale.linear_strict`), so the value under the mark of a value is that value. -/
theorem invert_at_linear (dataLo dataHi lo hi : Int) (hu : dataHi - dataLo ≤ hi - lo) {v : Int}
    (h1 : dataLo ≤ v) (h2 : v ≤ dataHi) :
    (Scale.linear dataLo dataHi lo hi).invert ((Scale.linear dataLo dataHi lo hi).at v) = v := by
  have hr : (Scale.linear dataLo dataHi lo hi).Rising := by
    show lo ≤ hi
    omega
  rcases Int.lt_or_eq_of_le h2 with hlt | heq
  · exact invert_at_of_lt _ hr h1 hlt
      (linear_strict dataLo dataHi lo hi hu h1 (by omega) (by omega))
  · subst heq
    exact invert_at_last _ hr (Int.le_trans h1 h2)

/-- On a line with a unit of the quantity or more for each unit of length, the next value is
drawn one unit further at most: no length between two marks is passed over. -/
theorem lineAt_succ_le (dataLo dataHi lo hi : Int) (hr : lo ≤ hi)
    (hu : hi - lo ≤ dataHi - dataLo) {v : Int} (h1 : dataLo ≤ v) (h2 : v < dataHi) :
    lineAt dataLo dataHi lo hi (v + 1) ≤ lineAt dataLo dataHi lo hi v + 1 := by
  have hd : 0 < dataHi - dataLo := by omega
  have e : (hi - lo) * (v + 1 - dataLo) = (hi - lo) * (v - dataLo) + (hi - lo) := by
    have e' : v + 1 - dataLo = v - dataLo + 1 := by omega
    rw [e', Int.mul_add, Int.mul_one]
  have h3 : ((hi - lo) * (v - dataLo) + (hi - lo)) / (dataHi - dataLo) ≤
      ((hi - lo) * (v - dataLo) + 1 * (dataHi - dataLo)) / (dataHi - dataLo) :=
    Int.ediv_le_ediv hd (by omega)
  rw [Int.add_mul_ediv_right _ _ (Int.ne_of_gt hd)] at h3
  unfold lineAt
  rw [clamp_of_mem (v := v + 1) (by omega) (by omega), clamp_of_mem h1 (by omega), e]
  omega

/-- **A scale that is short enough gives back every mark.** A `linear` scale that rises, with
one unit of the quantity or more for each unit of length, draws some value at every length of
its range. So the mark of the value under a mark is that mark. With `invert_at_linear`: a
scale with exactly one unit of length for each unit of the quantity gives back every value and
every mark. -/
theorem at_invert_linear (dataLo dataHi lo hi : Int) (hd : dataLo < dataHi) (hr : lo ≤ hi)
    (hu : hi - lo ≤ dataHi - dataLo) {y : Int} (h1 : lo ≤ y) (h2 : y ≤ hi) :
    (Scale.linear dataLo dataHi lo hi).at ((Scale.linear dataLo dataHi lo hi).invert y) = y := by
  have hR : (Scale.linear dataLo dataHi lo hi).Rising := hr
  have hdm : (Scale.linear dataLo dataHi lo hi).domain.1 ≤
      (Scale.linear dataLo dataHi lo hi).domain.2 := Int.le_of_lt hd
  have e1 : (Scale.linear dataLo dataHi lo hi).at dataLo = lo :=
    linear_lo dataLo dataHi lo hi (Int.le_of_lt hd)
  have e2 : (Scale.linear dataLo dataHi lo hi).at dataHi = hi := linear_hi dataLo dataHi lo hi hd
  have hy : (Scale.linear dataLo dataHi lo hi).at
      (Scale.linear dataLo dataHi lo hi).domain.1 ≤ y := by
    show (Scale.linear dataLo dataHi lo hi).at dataLo ≤ y
    rw [e1]
    exact h1
  have hle := at_invert_le _ hR hy
  have hm := invert_mem (Scale.linear dataLo dataHi lo hi) hdm y
  have hm2 : (Scale.linear dataLo dataHi lo hi).invert y ≤ dataHi := hm.2
  rcases Int.lt_or_eq_of_le h2 with hlt | heq
  · have hlt' : y < (Scale.linear dataLo dataHi lo hi).at
        (Scale.linear dataLo dataHi lo hi).domain.2 := by
      show y < (Scale.linear dataLo dataHi lo hi).at dataHi
      rw [e2]
      exact hlt
    have hs : y < lineAt dataLo dataHi lo hi ((Scale.linear dataLo dataHi lo hi).invert y + 1) :=
      lt_at_invert_succ _ hR hdm hy hlt'
    have hne : (Scale.linear dataLo dataHi lo hi).invert y < dataHi := by
      rcases Int.lt_or_eq_of_le hm2 with hl | he
      · exact hl
      · rw [he, e2] at hle
        exact absurd hlt (Int.not_lt.mpr hle)
    have hstep := lineAt_succ_le dataLo dataHi lo hi hr hu hm.1 hne
    have hle' : lineAt dataLo dataHi lo hi ((Scale.linear dataLo dataHi lo hi).invert y) ≤ y := hle
    show lineAt dataLo dataHi lo hi ((Scale.linear dataLo dataHi lo hi).invert y) = y
    omega
  · have hg := (invert_galois _ hR hy (v := dataHi) (Int.le_of_lt hd) (Int.le_refl _)).mp (by
      rw [e2]
      exact Int.le_of_eq heq.symm)
    rw [Int.le_antisymm hm2 hg, e2]
    exact heq.symm

end Scale

/-! ## Finite evaluations

The values of d3's own tests of `invert` (`d3-scale` at `d6904a4bde09`,
`test/linear-test.js`), in whole numbers. d3's domains and ranges there are fractions between
`0` and `2`, so each is written here in thousandths, and each comparison is exact. -/

-- "linear.invert(y) maps a range value y to a domain value x": the range `[1, 2]` and the
-- domain `[0, 1]`, and `invert(1.5)` is `0.5`.
#guard (Scale.linear 0 1000 1000 2000).invert 1500 == 500

-- "linear(x) can map a bilinear domain": the domain `[1, 2]` on the range `[0, 1]`. The three
-- marks inside the range answer as d3 does.
#guard [0, 500, 1000].map (Scale.linear 1000 2000 0 1000).invert == [1000, 1500, 2000]

-- "linear.clamp(true) restricts input values to the domain": the range `[10, 20]`, and a place
-- on either side of it. Without `clamp` d3 answers `2` and `-1` here: it goes on past the ends,
-- and a scale of this package does not.
#guard [30000, 0].map (Scale.linear 0 1000 10000 20000).invert == [1000, 0]

-- "linear.invert(y) maps an empty range to the middle of the domain": d3 answers `1.5`. Every
-- value is drawn alike, and the adjoint answers the last of them.
#guard (Scale.linear 1000 2000 0 0).invert 0 == 2000

-- The edge of the consumer's scale of `Whatwg/Svg/Scene/Scale.lean`: a share in millionths on a
-- trunk from `1` to `8`. Seven widths have seven first shares, an eighth of the range apart.
#guard (List.range 8).map (fun y => (Scale.linear 125000 1000000 1 8).invert (y + 1 : Nat)) ==
  [249999, 374999, 499999, 624999, 749999, 874999, 999999, 1000000]
#guard (Scale.linear 125000 1000000 1 8).at 249999 == 1 &&
  (Scale.linear 125000 1000000 1 8).at 250000 == 2

-- A scale that falls, as on a screen whose ordinates grow downward: the small line of
-- `Whatwg/Svg/Scene/Strip.lean`, values `0` to `9` on ordinates `12` to `0`. Each ordinate
-- answers the least value drawn at it or above it on the screen.
#guard (List.range 13).map (fun y => (Scale.linear 0 9 12 0).invert (y : Nat)) ==
  [9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0]
#guard (List.range 10).map (fun v => (Scale.linear 0 9 12 0).at (v : Nat)) ==
  [12, 10, 9, 8, 6, 5, 4, 2, 1, 0]

-- A scale with ties. Ten values on five units of length are drawn two by two, and the value
-- under the mark of a value is the greater of its pair: a control of `invert_at_linear`, which
-- asks for a unit of length for each unit of the quantity.
#guard (List.range 11).map (fun v => (Scale.linear 0 10 0 5).invert ((Scale.linear 0 10 0 5).at
  (v : Nat))) == [1, 1, 3, 3, 5, 5, 7, 7, 9, 9, 10]

-- A root, a logarithm and levels are inverted by the same halving. The root of `Scale.lean`:
-- a quarter of the quantity is half the length. A doubling is a tenth of the length. On three
-- levels of weight by depth, the third level is the depth `3` and every depth past it.
#guard (Scale.root 2 0 100 0 10).invert 5 == 35 && (Scale.root 2 0 100 0 10).at 35 == 5 &&
  (Scale.root 2 0 100 0 10).at 36 == 6
#guard (Scale.log2 1 1024 0 100).invert 50 == 63 && (Scale.log2 1 1024 0 100).at 64 == 60
#guard [1, 2, 3].map (Scale.steps 1 [(2, 2), (3, 3)]).invert == [1, 2, 3]

-- A control of the law of a rising scale, which asks for a mark no earlier than the first. A
-- place before the first mark answers the low end, whose mark is past the place.
#guard (Scale.linear 0 10 100 200).invert 50 == 0 && (Scale.linear 0 10 100 200).at 0 == 100

end Whatwg.Svg.Scene
