import Whatwg.Svg.Scene.Motion.Laws
import Whatwg.Svg.Scene.Between

/-!
# Whatwg.Svg.Scene.Ease

Owner: the family of an easing (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

An easing is written once, as the way a thing leaves its start. Two more come from it with no
new formula: the same way of arriving at the end, and the two in a row. lean4-effect4's look has
`in_`, `out` and `inOut` as three formulas (`tools/Tools/View/Look.lean`), and d3-ease has three
functions for each of its nine families (`src/cubic.js`, `src/back.js`, `src/poly.js`). d3's
tests say what the three have in common: `test/generic.js` defines `out(easeIn)` as
`t => 1 - easeIn(1 - t)` and `inOut(easeIn)` as
`t => (t < 0.5 ? easeIn(t * 2) : (2 - easeIn((1 - t) * 2))) / 2`, and each test file compares
the written functions with those two (d3-ease at commit `4099c6d715f5`; BSD 3-Clause licence,
Copyright 2010-2021 Mike Bostock, 2001 Robert Penner). Here the two are the definitions, on the
data of an easing, and the three of a family are one value and two calls.

- `Easing.out e`: `e` turned about the middle of its square. What `e` does as it leaves `0`,
  `e.out` does as it arrives at `1000`. For a cubic it exchanges the two heights and takes each
  from a thousand. For stops it takes each value from a thousand and reverses their order.
- `Easing.values e pieces`: the values of an easing at evenly spaced stops. Stops have their
  own. A cubic is read at `pieces + 1` moments, as `Easing.sampled` reads it.
- `Easing.inOut e pieces`: `e` at twice the speed and half the height, and then the same
  turned. It is stops, since two cubics in a row are no one cubic, and CSS writes it `linear()`.
- `Easing.Rises e`: a test on the data. The values of the stops never fall, or the two heights
  of the cubic are from `0` to `1000`. `Whatwg/Svg/Geometry/Ease.lean` proves what the test is
  for: such an easing reads no less at a later moment, so a thing that takes it never goes back
  (`mix_mono` and `mix_anti` here are the last step of that).
- `Easing.backIn`, `Easing.cubicInOut`: the two members of the kit's families that were not
  named.

What the laws say:

- `out_out`: turning twice gives the easing back. So `in` and `out` are one relation, and a law
  of one is a law of the other.
- `cubicIn_out`, `backOut_out`, `linear_out`: the named easings of
  `Whatwg/Svg/Scene/Motion.lean` are each other's turns, as values.
- `proper_out`, `bounded_out`, `rises_out`: a turned easing starts at `0` and ends at `1000`
  where the easing does, stays in range where it does, and rises where it does.
- `inOut_out`: an easing in and out is its own turn. Its second half is its first, turned.
- `proper_inOut`, `bounded_inOut`, `rises_inOut`: the same three properties of the two in a row.
- `inOut_at_half`: the two in a row read `500` at the middle of the progress.

What this module does not claim. The laws here are of the data. That a turned cubic reads
`1 - e (1 - s)` at every exact progress is `Easing.exact_out_cubic` of
`Whatwg/Svg/Geometry/Ease.lean`; for stops it is the definition at each stop, and between two
stops it is not proved. In whole numbers the two sides differ by the rounding, one per mille at
most, since one rounds down what the other rounds up. `inOut` halves each value with a
division that rounds down, so a value of the first half is at most half a per mille under the
exact half, and a value of the second half as much over it: the choice makes the easing its own
turn. `Rises` is a test that suffices: a cubic with a height out of range may still rise. An
easing after an easing (a composition) is not here.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Easing

/-! ## The turn -/

/-- The values of a list, each taken from a thousand, in the opposite order. -/
def turned (values : List Int) : List Int := (values.map fun v => 1000 - v).reverse

/-- **The easing turned about the middle**: at the progress `s` it reads what is left of the
whole after the easing at `1 - s`. An easing that is slow at first becomes one that is slow at
last, with the same curve. d3 writes it `t => 1 - easeIn(1 - t)`. -/
def out : Easing → Easing
  | .stops values => .stops (turned values)
  | .cubic y1 y2 => .cubic (1000 - y2) (1000 - y1)

/-- **The values of an easing at evenly spaced stops.** Stops have their own, and `pieces` is
not read. A cubic is read at `pieces + 1` moments from `0` to `1000`. -/
def values (e : Easing) (pieces : Nat := 20) : List Int :=
  match e with
  | .stops vs => vs
  | .cubic y1 y2 => (List.range (pieces + 1)).map fun i => cubicAt y1 y2 (i * 1000 / pieces)

/-- **The easing in and out**: the easing at twice the speed and half the height, and then the
same turned, so that it arrives as it left. The result is stops with twice the pieces of
`e.values pieces`. d3 writes it
`t => (t < 0.5 ? easeIn(t * 2) : (2 - easeIn((1 - t) * 2))) / 2`. -/
def inOut (e : Easing) (pieces : Nat := 10) : Easing :=
  let half := (e.values pieces).map fun v => v / 2
  .stops (half ++ (turned half).drop 1)

/-- The usual `back` easing at its start: it goes a tenth below `0` before it leaves. It is
`backOut`, turned. -/
def backIn : Easing := backOut.out

/-- Slow at first and at last: the cube of the progress, in and out, at twenty-one stops. -/
def cubicInOut : Easing := cubicIn.inOut

/-- **The easing never falls**: a test on its data. No value of the stops is below the one
before it, or the two heights of the cubic are from `0` to `1000`. For a cubic it is the test
`Easing.bounded`: a cubic that stays in range never goes back. -/
def Rises : Easing → Prop
  | .stops values => values.Pairwise fun a b => a ≤ b
  | .cubic y1 y2 => 0 ≤ y1 ∧ y1 ≤ 1000 ∧ 0 ≤ y2 ∧ y2 ≤ 1000

instance (e : Easing) : Decidable e.Rises := by
  cases e <;> unfold Rises <;> exact inferInstance

/-! ## Lists that are turned -/

/-- Two lists in a row, turned, are the second turned and then the first turned. -/
theorem turned_append (a b : List Int) : turned (a ++ b) = turned b ++ turned a := by
  unfold turned
  rw [List.map_append, List.reverse_append]

/-- A list turned twice is the list. -/
theorem turned_turned (a : List Int) : turned (turned a) = a := by
  have h : ((fun v : Int => 1000 - v) ∘ fun v : Int => 1000 - v) = id := funext fun v => by
    show 1000 - (1000 - v) = v
    omega
  unfold turned
  rw [List.map_reverse, List.reverse_reverse, List.map_map, h, List.map_id]

/-- A turned list has as many values. -/
theorem length_turned (a : List Int) : (turned a).length = a.length := by
  unfold turned
  rw [List.length_reverse, List.length_map]

/-- A turned list starts with what is left of a thousand after the last value. -/
theorem head?_turned (a : List Int) : (turned a).head? = a.getLast?.map fun v => 1000 - v := by
  unfold turned
  rw [List.head?_reverse, List.getLast?_map]

/-- A turned list ends with what is left of a thousand after the first value. -/
theorem getLast?_turned (a : List Int) : (turned a).getLast? = a.head?.map fun v => 1000 - v := by
  unfold turned
  rw [List.getLast?_reverse, List.head?_map]

/-- A value of a turned list is what is left of a thousand after a value of the list. -/
theorem mem_turned {a : List Int} {x : Int} (h : x ∈ turned a) : ∃ v ∈ a, 1000 - v = x := by
  unfold turned at h
  exact List.mem_map.mp (List.mem_reverse.mp h)

/-- A list with a value has a front and a last value. -/
theorem front_last : ∀ l : List Int, l ≠ [] → ∃ f m, l = f ++ [m]
  | [], h => absurd rfl h
  | [m], _ => ⟨[], m, rfl⟩
  | a :: b :: rest, _ =>
    have ⟨f, m, e⟩ := front_last (b :: rest) (List.cons_ne_nil b rest)
    ⟨a :: f, m, congrArg (List.cons a) e⟩

/-- A list with one more value at its end ends with that value. -/
theorem getLast?_front : ∀ (f : List Int) (m : Int), (f ++ [m]).getLast? = some m
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: rest, m => (List.getLast?_cons_cons).trans (getLast?_front (b :: rest) m)

/-- A list with a last value, turned and less its first value, is its front turned. -/
theorem drop_turned_front (f : List Int) (m : Int) : (turned (f ++ [m])).drop 1 = turned f := by
  rw [turned_append]
  rfl

/-! ## The turn of an easing -/

/-- **An easing turned twice is the easing.** -/
theorem out_out (e : Easing) : e.out.out = e := by
  cases e with
  | stops values => exact congrArg Easing.stops (turned_turned values)
  | cubic y1 y2 =>
    have h1 : 1000 - (1000 - y1) = y1 := by omega
    have h2 : 1000 - (1000 - y2) = y2 := by omega
    show Easing.cubic (1000 - (1000 - y1)) (1000 - (1000 - y2)) = Easing.cubic y1 y2
    rw [h1, h2]

/-- Two easings with one turn are one easing. -/
theorem out_inj {e f : Easing} (h : e.out = f.out) : e = f := by
  rw [← out_out e, ← out_out f, h]

/-- The easing that is slow at first, turned, is the one that is slow at last. -/
theorem cubicIn_out : cubicIn.out = cubicOut := rfl

/-- The easing that is slow at last, turned, is the one that is slow at first. -/
theorem cubicOut_out : cubicOut.out = cubicIn := rfl

/-- The progress itself is its own turn. -/
theorem linear_out : linear.out = linear := rfl

/-- The `back` easing at its start, turned, is the `back` easing at its end. -/
theorem backIn_out : backIn.out = backOut := out_out backOut

/-- Proper stops begin with `0`. -/
theorem head_of_proper {values : List Int} (h : (stops values).Proper) :
    values.head? = some 0 := by
  cases values with
  | nil => exact absurd h.2 (by decide)
  | cons v rest => exact congrArg some ((stopsAt_zero v rest).symm.trans h.1)

/-- Proper stops end with `1000`. -/
theorem last_of_proper {values : List Int} (h : (stops values).Proper) :
    values.getLast? = some 1000 := by
  have e : values.getLast?.getD 0 = 1000 := (stopsAt_end values).symm.trans h.2
  cases hl : values.getLast? with
  | none =>
    rw [hl] at e
    exact absurd e (by decide)
  | some v =>
    rw [hl] at e
    exact congrArg some e

/-- **A proper easing, turned, is proper**: it starts at `0` and ends at `1000`. -/
theorem proper_out {e : Easing} (h : e.Proper) : e.out.Proper := by
  cases e with
  | cubic y1 y2 => exact proper_cubic _ _
  | stops values =>
    refine proper_stops (turned values) ?_ ?_
    · rw [head?_turned, last_of_proper h]
      rfl
    · rw [getLast?_turned, head_of_proper h]
      rfl

/-- **An easing that stays in range, turned, stays in range.** -/
theorem bounded_out {e : Easing} (h : e.bounded = true) : e.out.bounded = true := by
  cases e with
  | stops values =>
    refine List.all_eq_true.mpr fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := mem_turned hx
    have hb := List.all_eq_true.mp h v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    obtain ⟨h0, h1⟩ := hb
    exact ⟨by omega, by omega⟩
  | cubic y1 y2 =>
    simp only [bounded, out, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

/-- **An easing that never falls, turned, never falls.** -/
theorem rises_out {e : Easing} (h : e.Rises) : e.out.Rises := by
  cases e with
  | stops values =>
    show (turned values).Pairwise fun a b => a ≤ b
    unfold turned
    rw [List.pairwise_reverse, List.pairwise_map]
    refine List.Pairwise.imp ?_ h
    intro a b hab
    show 1000 - b ≤ 1000 - a
    omega
  | cubic y1 y2 =>
    obtain ⟨a, b, c, d⟩ := h
    exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## The values of an easing -/

/-- The values of stops are the stops. -/
theorem values_stops (vs : List Int) (pieces : Nat) : (stops vs).values pieces = vs := rfl

/-- The values of a cubic are the stops of the cubic sampled. -/
theorem sampled_cubic (y1 y2 : Int) (pieces : Nat) :
    sampled (cubic y1 y2).at pieces = stops ((cubic y1 y2).values pieces) := rfl

/-- **The values of a proper easing begin with `0`**, at one piece or more. -/
theorem values_head {e : Easing} (h : e.Proper) (pieces : Nat) :
    (e.values pieces).head? = some 0 := by
  cases e with
  | stops vs => exact head_of_proper h
  | cubic y1 y2 =>
    show ((List.range (pieces + 1)).map fun i => cubicAt y1 y2 (i * 1000 / pieces)).head? = some 0
    rw [List.range_succ_eq_map, List.map_cons, List.head?_cons, Nat.zero_mul, Nat.zero_div,
      cubicAt_zero]

/-- **The values of a proper easing end with `1000`**, at one piece or more. -/
theorem values_last {e : Easing} (h : e.Proper) {pieces : Nat} (hp : 0 < pieces) :
    (e.values pieces).getLast? = some 1000 := by
  cases e with
  | stops vs => exact last_of_proper h
  | cubic y1 y2 =>
    show ((List.range (pieces + 1)).map fun i => cubicAt y1 y2 (i * 1000 / pieces)).getLast? =
      some 1000
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, getLast?_front,
      Nat.mul_div_cancel_left 1000 hp, cubicAt_end]

/-- The values of an easing that stays in range are from `0` to `1000`. -/
theorem values_bounded {e : Easing} (h : e.bounded = true) (pieces : Nat) :
    ∀ v ∈ e.values pieces, 0 ≤ v ∧ v ≤ 1000 := by
  cases e with
  | stops vs =>
    intro v hv
    have hb := List.all_eq_true.mp h v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact hb
  | cubic y1 y2 =>
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    have hlt : i < pieces + 1 := List.mem_range.mp hi
    have hle : i * 1000 / pieces ≤ 1000 :=
      Nat.div_le_of_le_mul (by
        rw [Nat.mul_comm pieces 1000, Nat.mul_comm i 1000]
        exact Nat.mul_le_mul_left 1000 (Nat.le_of_lt_succ hlt))
    exact bounded_at (cubic y1 y2) _ h hle

/-! ## In and out -/

/-- A list that ends with `500`, then itself turned less the first value, is its own turn. -/
theorem turned_inOut (half : List Int) (h : half.getLast? = some 500) :
    turned (half ++ (turned half).drop 1) = half ++ (turned half).drop 1 := by
  have hne : half ≠ [] := fun e => by
    rw [e] at h
    cases h
  obtain ⟨f, m, rfl⟩ := front_last half hne
  rw [getLast?_front] at h
  cases h
  rw [drop_turned_front, turned_append, turned_turned, turned_append, List.append_assoc]
  rfl

/-- The halves of values that end with `1000` end with `500`. -/
theorem half_last {vs : List Int} (h : vs.getLast? = some 1000) :
    (vs.map fun v => v / 2).getLast? = some 500 := by
  rw [List.getLast?_map, h]
  rfl

/-- **An easing in and out is its own turn**: it arrives as it left. It asks that the values of
the easing end with `1000`, which the values of a proper easing do (`values_last`). -/
theorem inOut_out (e : Easing) (pieces : Nat) (h : (e.values pieces).getLast? = some 1000) :
    (e.inOut pieces).out = e.inOut pieces :=
  congrArg Easing.stops (turned_inOut _ (half_last h))

/-- **A proper easing in and out is proper.** It asks for the two ends of the values, which a
proper easing has at one piece or more (`values_head`, `values_last`). -/
theorem proper_inOut_of (e : Easing) (pieces : Nat) (h0 : (e.values pieces).head? = some 0)
    (h1 : (e.values pieces).getLast? = some 1000) : (e.inOut pieces).Proper := by
  have hh : ((e.values pieces).map fun v => v / 2).head? = some 0 := by
    rw [List.head?_map, h0]
    rfl
  have hl := half_last h1
  show (stops (((e.values pieces).map fun v => v / 2) ++
    (turned ((e.values pieces).map fun v => v / 2)).drop 1)).Proper
  generalize (e.values pieces).map (fun v => v / 2) = half at hh hl
  have hne : half ≠ [] := fun e => by
    rw [e] at hl
    cases hl
  obtain ⟨f, m, rfl⟩ := front_last half hne
  rw [drop_turned_front]
  cases f with
  | nil =>
    rw [getLast?_front] at hl
    cases hl
    cases hh
  | cons a f' =>
    cases hh
    refine proper_stops _ rfl ?_
    have e1 : turned ((0 : Int) :: f') = turned f' ++ [1000] := turned_append [0] f'
    rw [e1, ← List.append_assoc, getLast?_front]

/-- **A proper easing in and out is proper**, at one piece or more. -/
theorem proper_inOut {e : Easing} (h : e.Proper) {pieces : Nat} (hp : 0 < pieces) :
    (e.inOut pieces).Proper :=
  proper_inOut_of e pieces (values_head h pieces) (values_last h hp)

/-- **An easing that stays in range, in and out, stays in range.** -/
theorem bounded_inOut {e : Easing} (h : e.bounded = true) (pieces : Nat) :
    (e.inOut pieces).bounded = true := by
  have hv := values_bounded h pieces
  refine List.all_eq_true.mpr fun x hx => ?_
  have hhalf : ∀ y ∈ (e.values pieces).map (fun v => v / 2), 0 ≤ y ∧ y ≤ 500 := fun y hy => by
    obtain ⟨v, hm, rfl⟩ := List.mem_map.mp hy
    obtain ⟨h0, h1⟩ := hv v hm
    exact ⟨by omega, by omega⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases List.mem_append.mp hx with hl | hr
  · obtain ⟨h0, h1⟩ := hhalf x hl
    exact ⟨h0, by omega⟩
  · obtain ⟨y, hy, rfl⟩ := mem_turned (List.mem_of_mem_drop hr)
    obtain ⟨h0, h1⟩ := hhalf y hy
    exact ⟨by omega, by omega⟩

/-- **Values that never fall and are at most `1000` give an easing in and out that never
falls.** The values of stops that rise are such, where the stops are in range. -/
theorem rises_inOut_of (e : Easing) (pieces : Nat)
    (hr : (e.values pieces).Pairwise fun a b => a ≤ b)
    (hb : ∀ v ∈ e.values pieces, 0 ≤ v ∧ v ≤ 1000) : (e.inOut pieces).Rises := by
  have hhalf : ((e.values pieces).map fun v => v / 2).Pairwise fun a b => a ≤ b := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ hr
    intro a b hab
    show a / 2 ≤ b / 2
    omega
  have hm : ∀ y ∈ (e.values pieces).map (fun v => v / 2), 0 ≤ y ∧ y ≤ 500 := fun y hy => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    obtain ⟨h0, h1⟩ := hb v hv
    exact ⟨by omega, by omega⟩
  show (((e.values pieces).map fun v => v / 2) ++
    (turned ((e.values pieces).map fun v => v / 2)).drop 1).Pairwise fun a b => a ≤ b
  generalize (e.values pieces).map (fun v => v / 2) = half at hhalf hm
  have ht : (turned half).Pairwise fun a b => a ≤ b := by
    unfold turned
    rw [List.pairwise_reverse, List.pairwise_map]
    refine List.Pairwise.imp ?_ hhalf
    intro a b hab
    show 1000 - b ≤ 1000 - a
    omega
  refine List.pairwise_append.mpr ⟨hhalf, ht.sublist (List.drop_sublist 1 _), fun a ha b hb' => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_turned (List.mem_of_mem_drop hb')
  obtain ⟨_, a1⟩ := hm a ha
  obtain ⟨_, y1⟩ := hm y hy
  omega

/-- **Stops in range that never fall, in and out, never fall.** -/
theorem rises_inOut_stops {vs : List Int} (hr : (stops vs).Rises) (hb : (stops vs).bounded = true)
    (pieces : Nat) : ((stops vs).inOut pieces).Rises :=
  rises_inOut_of (stops vs) pieces hr (values_bounded hb pieces)

/-- **An easing in and out reads `500` at the middle of the progress**, where its values end
with `1000`. -/
theorem inOut_at_half (e : Easing) (pieces : Nat) (h : (e.values pieces).getLast? = some 1000) :
    (e.inOut pieces).at 500 = 500 := by
  have hl := half_last h
  show stopsAt (((e.values pieces).map fun v => v / 2) ++
    (turned ((e.values pieces).map fun v => v / 2)).drop 1) 500 = 500
  generalize (e.values pieces).map (fun v => v / 2) = half at hl
  have hne : half ≠ [] := fun e => by
    rw [e] at hl
    cases hl
  obtain ⟨f, m, rfl⟩ := front_last half hne
  rw [getLast?_front] at hl
  cases hl
  rw [drop_turned_front]
  have hlen : (f ++ [(500 : Int)] ++ turned f).length - 1 = 2 * f.length := by
    rw [List.length_append, List.length_append, length_turned, List.length_singleton]
    omega
  have hi : f.length < (f ++ [(500 : Int)] ++ turned f).length := by
    rw [List.length_append, List.length_append, length_turned, List.length_singleton]
    omega
  rw [stopsAt_stop _ f.length 500 hi (by rw [hlen]; omega), List.append_assoc]
  show ((f ++ ([(500 : Int)] ++ turned f))[f.length]?).getD 0 = 500
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

end Easing

/-! ## What a rising progress is for -/

/-- **On the way up, more progress is no lower.** A value that goes from `u` up to `v` is no
less at a greater eased progress. With an easing that never falls it never goes back. -/
theorem mix_mono {u v : Int} (h : u ≤ v) {e e' : Int} (he : e ≤ e') : mix u v e ≤ mix u v e' := by
  have p : (u - v) * (1000 - e) ≤ (u - v) * (1000 - e') :=
    Int.mul_le_mul_of_nonpos_left (show u - v ≤ 0 by omega) (show 1000 - e' ≤ 1000 - e by omega)
  exact Int.add_le_add_left (Int.ediv_le_ediv (by decide) p) v

/-- **On the way down, more progress is no higher.** -/
theorem mix_anti {u v : Int} (h : v ≤ u) {e e' : Int} (he : e ≤ e') : mix u v e' ≤ mix u v e := by
  have p : (u - v) * (1000 - e') ≤ (u - v) * (1000 - e) :=
    Int.mul_le_mul_of_nonneg_left (show 1000 - e' ≤ 1000 - e by omega) (show 0 ≤ u - v by omega)
  exact Int.add_le_add_left (Int.ediv_le_ediv (by decide) p) v

end Whatwg.Svg.Scene
