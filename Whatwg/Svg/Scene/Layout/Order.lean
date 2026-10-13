import Whatwg.Svg.Scene.Join.Laws
import Whatwg.Svg.Scene.Order
import Whatwg.Svg.Scene.Layout.Laws

/-!
# Whatwg.Svg.Scene.Layout.Order

Owner: a layout that keeps an order (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A picture of a program that reads from the top says one thing with its heights: what comes
first stands above. `Whatwg/Svg/Scene/Order.lean` has the order as an algebra of four
operations, and `Whatwg/Svg/Scene/Layout.lean` has the picture as operations on parts. This
module says that the second realizes the first, operation by operation: `above` is `connect`,
and `beside` and `over` are `overlay`. So a program that folds its structure into an order and
into a layout by the same cases has, by one line for each case, that its picture keeps its
order. lean4-effect4 proves this of its flows over four hundred lines
(`lay_realizes`, `place_keeps_order` of its `tools/Tools/View/FlowOrder.lean`), by following
the list arithmetic of its own layout.

- `Realizes key gap g l`: **the layout `l` realizes the order `g`**, read by the key of a
  thing. Each thing of the order is the key of a thing of the layout (`shows`), and where the
  order puts `u` before `v`, a thing with the key `u` ends the gap above a thing with the key
  `v` (`keeps`).

What the laws say:

- `Realizes.congr`: the relation reads what an order says, and not how it is written. So each
  law of the algebra is a law here: a layout that realizes a series grouped one way realizes it
  grouped the other way (`AGraph.connect_assoc`), and an order with no thing may be left out
  (`AGraph.connect_none_left`).
- `realizes_empty`, `realizes_leaf`: every layout realizes the empty order, and one thing in a
  room realizes the order of its key.
- **`above` is `connect`** (`Realizes.above`): two parts that fit, one above the other with the
  gap, realize the series of their orders. The step between the parts is `Layout.above_gap`.
- **`beside` and `over` are `overlay`** (`Realizes.beside`, `Realizes.over`), and one layout
  that realizes two orders realizes them side by side (`Realizes.overlay`).
- `Realizes.stands`: **a part that realizes an order still does where it stands** in a greater
  layout. So `inset`, `centred`, a frame and a move to an origin keep it (`Realizes.place`).
- `Realizes.column`, `Realizes.stack`, `Realizes.row`: a column or a stack of parts realizes
  the series of their orders, and a row their orders side by side. These are the folds.
- `Realizes.mono`: a layout that keeps an order at a gap keeps it at a lesser one.
- `Realizes.no_vertex`: a layout with no thing realizes only orders with no thing.
- `Realizes.all`: **with distinct keys, every thing with the key `u` ends the gap above every
  thing with the key `v`**, and not one of each only.

What a caller must supply: the key of a thing, with the law that a move does not change it.

What this module does not claim: the converse, that a thing above another comes before it,
which is false of branches side by side; that things with no order between them stand side by
side, or at one height; anything of the order across; a law for an order realized by the
layers of `Layers.heights` and not by `above` (the links of an order as a list, and that the
things of an order in the order written serve them, are not here).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Layout

open AGraph (denote)

variable {α κ : Type}

section

variable [Moves IVec α] [Boxed α]

/-- **The layout realizes the order**, read by the key of a thing. -/
structure Realizes (key : α → κ) (gap : Nat) (g : AGraph κ) (l : Layout α) : Prop where
  /-- Each thing of the order is the key of a thing of the layout. -/
  shows : ∀ k, (denote g).has k → ∃ a ∈ l.items, key a = k
  /-- Where the order puts `u` before `v`, a thing with the key `u` ends the gap above a thing
  with the key `v`. -/
  keeps : ∀ u v, (denote g).edge u v → ∃ a ∈ l.items, ∃ b ∈ l.items, key a = u ∧ key b = v ∧
    (Boxed.box a).y1 + gap ≤ (Boxed.box b).y0

variable {key : α → κ} {gap : Nat} {g h : AGraph κ}

/-- **The relation reads what an order says, and not how it is written.** -/
theorem Realizes.congr {g' : AGraph κ} {l : Layout α} (e : denote g = denote g')
    (r : Realizes key gap g l) : Realizes key gap g' l :=
  ⟨fun k hk => r.shows k (by rw [e]; exact hk), fun u v he => r.keeps u v (by rw [e]; exact he)⟩

/-- A layout that keeps an order at a gap keeps it at a lesser gap. -/
theorem Realizes.mono {gap' : Nat} {l : Layout α} (hg : gap' ≤ gap) (r : Realizes key gap g l) :
    Realizes key gap' g l :=
  ⟨r.shows, fun u v he => by
    obtain ⟨a, ha, b, hb, ea, eb, hy⟩ := r.keeps u v he
    exact ⟨a, ha, b, hb, ea, eb, by omega⟩⟩

/-- An order with no thing is realized by every layout. -/
theorem realizes_none (key : α → κ) (gap : Nat) (l : Layout α) {g : AGraph κ}
    (hn : ∀ k, ¬(denote g).has k) : Realizes key gap g l :=
  ⟨fun k hk => absurd hk (hn k), fun u _ he => absurd (AGraph.edge_has g he).1 (hn u)⟩

/-- The empty order is realized by every layout. -/
theorem realizes_empty (key : α → κ) (gap : Nat) (l : Layout α) : Realizes key gap .empty l :=
  realizes_none key gap l fun _ hk => hk

/-- **One thing in a room realizes the order of its key.** -/
theorem realizes_leaf (key : α → κ) (gap : Nat) (w h : Nat) (a : α) :
    Realizes key gap (.vertex (key a)) (leaf w h a) :=
  ⟨fun _ hk => ⟨a, List.mem_cons_self, hk.symm⟩, fun _ _ he => he.elim⟩

/-- A layout with no thing realizes only orders with no thing. -/
theorem Realizes.no_vertex {l : Layout α} (r : Realizes key gap g l) (hl : l.items = []) :
    ∀ k, ¬(denote g).has k := fun k hk => by
  obtain ⟨a, ha, _⟩ := r.shows k hk
  rw [hl] at ha
  exact nomatch ha

/-- **A part that realizes an order still does where it stands** in a greater layout, where a
move does not change a key. -/
theorem Realizes.stands (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a)
    {l l' : Layout α} {d : IVec} (r : Realizes key gap g l) (hs : l'.Stands d l) :
    Realizes key gap g l' :=
  ⟨fun k hkk => by
      obtain ⟨a, ha, e⟩ := r.shows k hkk
      exact ⟨Moves.move d a, hs a ha, (hk d a).trans e⟩,
    fun u v he => by
      obtain ⟨a, ha, b, hb, ea, eb, hy⟩ := r.keeps u v he
      refine ⟨Moves.move d a, hs a ha, Moves.move d b, hs b hb, (hk d a).trans ea,
        (hk d b).trans eb, ?_⟩
      rw [Boxed.box_move, Boxed.box_move, IBox.move_y1, IBox.move_y0]
      omega⟩

/-- **One layout that realizes two orders realizes them side by side.** -/
theorem Realizes.overlay {l : Layout α} (rg : Realizes key gap g l) (rh : Realizes key gap h l) :
    Realizes key gap (.overlay g h) l :=
  ⟨fun k hk => hk.elim (rg.shows k) (rh.shows k),
    fun u v he => he.elim (rg.keeps u v) (rh.keeps u v)⟩

/-- **`beside` is `overlay`**: two parts side by side realize their two orders with no order
between them. -/
theorem Realizes.beside (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a)
    {a b : Layout α} (ra : Realizes key gap g a) (rb : Realizes key gap h b) (across : Nat) :
    Realizes key gap (.overlay g h) (Layout.beside across a b) :=
  (ra.stands hk (stands_beside_left across a b)).overlay
    (rb.stands hk (stands_beside_right across a b))

/-- **`over` is `overlay`**: two parts in one room realize their two orders with no order
between them. -/
theorem Realizes.over (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a)
    {a b : Layout α} (ra : Realizes key gap g a) (rb : Realizes key gap h b) :
    Realizes key gap (.overlay g h) (Layout.over a b) :=
  (ra.stands hk (stands_over_left a b)).overlay (rb.stands hk (stands_over_right a b))

/-- **`above` is `connect`**: two parts that fit, the first above the second with a gap that is
the gap of the order at least, realize the series of their orders. -/
theorem Realizes.above_of_le (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a)
    {a b : Layout α} (ra : Realizes key gap g a) (rb : Realizes key gap h b) (fa : a.Fits)
    (fb : b.Fits) {down : Nat} (hg : gap ≤ down) :
    Realizes key gap (.connect g h) (Layout.above down a b) := by
  have ra' := ra.stands hk (stands_above_left down a b)
  have rb' := rb.stands hk (stands_above_right down a b)
  refine ⟨fun k hkk => hkk.elim (ra'.shows k) (rb'.shows k), fun u v he => ?_⟩
  rcases he with he | he | ⟨hu, hv⟩
  · exact ra'.keeps u v he
  · exact rb'.keeps u v he
  · obtain ⟨x, hx, ex⟩ := ra.shows u hu
    obtain ⟨y, hy, ey⟩ := rb.shows v hv
    have hgap := above_gap (gap := down) fa fb hx hy
    exact ⟨x, List.mem_append_left _ hx, Moves.move (Layout.down (a.h + down)) y,
      List.mem_append_right _ (List.mem_map_of_mem hy), ex, (hk _ y).trans ey, by omega⟩

/-- **`above` is `connect`**, at the gap of the order. -/
theorem Realizes.above (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a)
    {a b : Layout α} (ra : Realizes key gap g a) (rb : Realizes key gap h b) (fa : a.Fits)
    (fb : b.Fits) : Realizes key gap (.connect g h) (Layout.above gap a b) :=
  ra.above_of_le hk rb fa fb (Nat.le_refl gap)

/-- **A row of parts realizes their orders side by side.** The parts and their orders are
given by one list of indices, as a fold has them. -/
theorem Realizes.row (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a) {ι : Type}
    (g : ι → AGraph κ) (l : ι → Layout α) (across : Nat) : ∀ xs : List ι,
    (∀ x ∈ xs, Realizes key gap (g x) (l x)) →
    Realizes key gap (AGraph.overlays (xs.map g)) (Layout.row across (xs.map l))
  | [], _ => realizes_empty key gap _
  | [x], r => (r x List.mem_cons_self).overlay (realizes_empty key gap _)
  | x :: y :: rest, r =>
    Realizes.beside hk (r x List.mem_cons_self)
      (Realizes.row hk g l across (y :: rest) fun z hz => r z (List.mem_cons_of_mem x hz)) across

/-- **A column of parts that fit realizes the series of their orders.** -/
theorem Realizes.column (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a) {ι : Type}
    (g : ι → AGraph κ) (l : ι → Layout α) : ∀ xs : List ι,
    (∀ x ∈ xs, Realizes key gap (g x) (l x)) → (∀ x ∈ xs, (l x).Fits) →
    Realizes key gap (AGraph.connects (xs.map g)) (Layout.column gap (xs.map l))
  | [], _, _ => realizes_empty key gap _
  | [x], r, _ => (r x List.mem_cons_self).congr (AGraph.connect_empty (g x)).symm
  | x :: y :: rest, r, f =>
    Realizes.above hk (r x List.mem_cons_self)
      (Realizes.column hk g l (y :: rest) (fun z hz => r z (List.mem_cons_of_mem x hz))
        fun z hz => f z (List.mem_cons_of_mem x hz))
      (f x List.mem_cons_self)
      (Fits.column gap ((y :: rest).map l) fun m hm => by
        obtain ⟨z, hz, e⟩ := List.mem_map.mp hm
        rw [← e]
        exact f z (List.mem_cons_of_mem x hz))

/-- **A stack of parts that fit realizes the series of their orders**: centring moves a part
across, and not down. -/
theorem Realizes.stack (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a) {ι : Type}
    (g : ι → AGraph κ) (l : ι → Layout α) (xs : List ι)
    (r : ∀ x ∈ xs, Realizes key gap (g x) (l x)) (f : ∀ x ∈ xs, (l x).Fits) :
    Realizes key gap (AGraph.connects (xs.map g)) (Layout.stack gap (xs.map l)) := by
  have e : Layout.stack gap (xs.map l) =
      Layout.column gap (xs.map fun x => centred (widest (xs.map l)) (l x)) := by
    show Layout.column gap ((xs.map l).map (centred (widest (xs.map l)))) = _
    rw [List.map_map]
    rfl
  rw [e]
  exact Realizes.column hk g (fun x => centred (widest (xs.map l)) (l x)) xs
    (fun x hx => (r x hx).stands hk (stands_centred _ _)) fun x hx => (f x hx).centred

/-- **A placed layout keeps the order**: moved to an origin, a thing with the key `u` still
ends the gap above a thing with the key `v`. -/
theorem Realizes.place (hk : ∀ (d : IVec) (a : α), key (Moves.move d a) = key a) {l : Layout α}
    (r : Realizes key gap g l) (origin : IVec) {u v : κ} (he : (denote g).edge u v) :
    ∃ a ∈ Layout.place origin l, ∃ b ∈ Layout.place origin l, key a = u ∧ key b = v ∧
      (Boxed.box a).y1 + gap ≤ (Boxed.box b).y0 :=
  (r.stands hk (l' := ⟨l.w, l.h, Layout.place origin l⟩) (d := origin)
    fun _ hx => List.mem_map_of_mem hx).keeps u v he

/-- **With distinct keys, every thing with the key `u` ends the gap above every thing with the
key `v`.** -/
theorem Realizes.all {l : Layout α} (r : Realizes key gap g l) (hd : Distinct key l.items)
    {u v : κ} (he : (denote g).edge u v) : ∀ a ∈ l.items, ∀ b ∈ l.items, key a = u → key b = v →
    (Boxed.box a).y1 + gap ≤ (Boxed.box b).y0 := fun a ha b hb ea eb => by
  obtain ⟨a', ha', b', hb', ea', eb', hy⟩ := r.keeps u v he
  rw [eq_of_distinct key l.items hd a a' ha ha' (ea.trans ea'.symm),
    eq_of_distinct key l.items hd b b' hb hb' (eb.trans eb'.symm)]
  exact hy

end

end Layout

end Whatwg.Svg.Scene
