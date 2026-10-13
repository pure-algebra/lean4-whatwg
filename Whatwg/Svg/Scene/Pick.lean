import Whatwg.Svg.Scene.Extent

/-!
# Whatwg.Svg.Scene.Pick

Owner: the thing under a point (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A pointer is at a point, and a picture answers which of its things is there. Where two things
hold the point, the one drawn later is over the other, so it answers. lean4-effect4 has this as
`pick` of its `tools/Tools/View/Picture.lean`: the last pointer box of a list that holds a
pixel answers its key. Here it is two lines on `IBox.Holds` of `Whatwg/Svg/Scene/Extent.lean`,
for a list of things of any type that takes room (`Boxed`).

- `Boxed.pick l p`: **the thing under the point `p`**: the last thing of `l` whose box holds
  it, and none where no box does.

What the laws say:

- `pick_append`: **a later thing answers before an earlier one.** The thing under a point of
  two lists in a row is the thing of the second, or else of the first.
- `pick_some`, `pick_eq_none`: what answers is a thing of the list whose box holds the point,
  and nothing answers exactly where no box holds it.
- `pick_iff`: **among things that share no room, a thing answers exactly where the point is in
  its box.** So in a layout that is clear (`Layout.Clear`), the order of drawing does not
  matter to the pointer.
- `pick_move`: **the thing under a moved point of a moved picture is the thing, moved.** A
  picture that moves as a whole needs no second search.

What this module does not claim: a search that is faster than reading the list; a thing whose
drawn shape is less than its box, which answers at every point of its box; a point on the last
edge of a box, which the box does not hold.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Boxed

variable {α : Type} [Moves IVec α] [Boxed α]

/-- **The thing under a point**: the last thing of a list whose box holds the point. The last
is the one drawn over the others. -/
def pick (l : List α) (p : IVec) : Option α :=
  l.reverse.find? fun a => decide ((Boxed.box a).Holds p)

theorem pick_nil (p : IVec) : pick ([] : List α) p = none := rfl

/-- **A later thing answers before an earlier one.** -/
theorem pick_append (a b : List α) (p : IVec) : pick (a ++ b) p = (pick b p).or (pick a p) := by
  rw [pick, List.reverse_append, List.find?_append]
  rfl

/-- **What answers is a thing of the list whose box holds the point.** -/
theorem pick_some {l : List α} {p : IVec} {a : α} (h : pick l p = some a) :
    a ∈ l ∧ (Boxed.box a).Holds p :=
  ⟨List.mem_reverse.mp (List.mem_of_find?_eq_some h),
    of_decide_eq_true (List.find?_some (p := fun a => decide ((Boxed.box a).Holds p)) h)⟩

/-- **Nothing answers exactly where no box holds the point.** -/
theorem pick_eq_none {l : List α} {p : IVec} :
    pick l p = none ↔ ∀ a ∈ l, ¬(Boxed.box a).Holds p := by
  rw [pick, List.find?_eq_none]
  constructor
  · intro h a ha hp
    exact h a (List.mem_reverse.mpr ha) (decide_eq_true hp)
  · intro h a ha hp
    exact h a (List.mem_reverse.mp ha) (of_decide_eq_true hp)

omit [Moves IVec α] [Boxed α] in
/-- Two things of a list that are related, each to each later one, are one thing or related one
way or the other. -/
private theorem pairwise_two {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {a b : α}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => nomatch ha
  | x :: xs, h, a, b, ha, hb => by
    have h' := List.pairwise_cons.mp h
    cases List.mem_cons.mp ha with
    | inl ea =>
      cases List.mem_cons.mp hb with
      | inl eb => exact Or.inl (ea.trans eb.symm)
      | inr hb' => exact Or.inr (Or.inl (ea ▸ h'.1 b hb'))
    | inr ha' =>
      cases List.mem_cons.mp hb with
      | inl eb => exact Or.inr (Or.inr (eb ▸ h'.1 a ha'))
      | inr hb' => exact pairwise_two h'.2 ha' hb'

/-- **Among things that share no room, a thing answers exactly where the point is in its
box.** -/
theorem pick_iff {l : List α} (hc : l.Pairwise fun x y => (Boxed.box x).Disjoint (Boxed.box y))
    {p : IVec} {a : α} : pick l p = some a ↔ a ∈ l ∧ (Boxed.box a).Holds p := by
  constructor
  · exact pick_some
  · intro ⟨ha, hp⟩
    cases hf : pick l p with
    | none => exact absurd hp (pick_eq_none.mp hf a ha)
    | some b =>
      obtain ⟨hb, hq⟩ := pick_some hf
      cases pairwise_two hc ha hb with
      | inl e => rw [e]
      | inr d =>
        cases d with
        | inl d => exact absurd hq (d.not_holds hp)
        | inr d => exact absurd hp (d.not_holds hq)

/-- The first thing of a moved list whose box holds a moved point is the first thing of the
list whose box holds the point, moved. -/
private theorem find_move (d p : IVec) : ∀ l : List α,
    (Moves.move d l).find? (fun a => decide ((Boxed.box a).Holds (p + d))) =
      Moves.move d (l.find? fun a => decide ((Boxed.box a).Holds p))
  | [] => rfl
  | a :: l => by
    have e : decide ((Boxed.box (Moves.move d a)).Holds (p + d)) =
        decide ((Boxed.box a).Holds p) := by
      rw [Boxed.box_move]
      exact decide_eq_decide.mpr (IBox.holds_move d)
    rw [Moves.move_cons]
    cases hb : decide ((Boxed.box a).Holds p) with
    | true =>
      rw [List.find?_cons_of_pos (p := fun a => decide ((Boxed.box a).Holds (p + d))) (e.trans hb),
        List.find?_cons_of_pos (p := fun a => decide ((Boxed.box a).Holds p)) hb]
      rfl
    | false =>
      have n1 : ¬decide ((Boxed.box (Moves.move d a)).Holds (p + d)) = true := fun h =>
        Bool.false_ne_true ((e.trans hb).symm.trans h)
      have n2 : ¬decide ((Boxed.box a).Holds p) = true := fun h =>
        Bool.false_ne_true (hb.symm.trans h)
      rw [List.find?_cons_of_neg (p := fun a => decide ((Boxed.box a).Holds (p + d))) n1,
        List.find?_cons_of_neg (p := fun a => decide ((Boxed.box a).Holds p)) n2]
      exact find_move d p l

/-- **The thing under a moved point of a moved picture is the thing, moved.** -/
theorem pick_move (d : IVec) (l : List α) (p : IVec) :
    pick (Moves.move d l) (p + d) = Moves.move d (pick l p) := by
  rw [pick, pick, ← Moves.move_reverse]
  exact find_move d p l.reverse

end Boxed

end Whatwg.Svg.Scene
