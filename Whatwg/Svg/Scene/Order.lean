
/-!
# Whatwg.Svg.Scene.Order

Owner: an order of things as an algebra (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A program says what comes before what by how it is put together. Its parts in a series come
one before the next, its branches side by side have no order between them, and a part inside a
region keeps the order that it has. So an order is built with four operations, and it need not
be written as a list of pairs: the empty order, one thing, two orders with nothing between them
(`overlay`), and two orders with each thing of the first before each thing of the second
(`connect`). This is the algebra of graphs of A. Mokhov, "Algebraic graphs with class", Haskell
Symposium 2017, as lean4-effect4's `tools/Tools/View/AlgGraph.lean` cites it; the reference is
taken from that file and was not read here. No expression of it names a pair whose ends are not
things of it.

lean4-effect4 has this algebra, with the same four constructors and the laws below under the
same names, and folds its flows into it (`Flow.order` of its `tools/Tools/View/FlowOrder.lean`).
It is here so that the layout of `Whatwg/Svg/Scene/Layout.lean` can be said to keep an order:
`Whatwg/Svg/Scene/Layout/Order.lean` is that law.

- `AGraph α`: an order of things of `α`, as an expression.
- `AGraph.Rel α`: what an order says. `has a`: the thing is in it. `edge a b`: it puts `a`
  before `b`.
- `AGraph.denote`: what an expression says. Two expressions are one order when they say the
  same.
- `AGraph.connects`, `AGraph.overlays`: a series of orders, and orders side by side.
- Whether a thing is in an order, and whether an order puts one thing before another, are
  decided for things with an equality test, so a program can test its orders.

What the laws say, each as an equation of what two expressions say:

- **The eight laws of the algebra**: `overlay_comm`, `overlay_assoc`; `connect_assoc`,
  `empty_connect`, `connect_empty`; `connect_overlay`, `overlay_connect`; and `decompose`, a
  series of three is its three pairs. With them `overlay_idem` and `absorb`.
- `edge_has`: the two ends of a pair are things of the order.
- `connect_congr`, `overlay_congr`: an expression may be replaced inside another by one that
  says the same. `denote_of_none`: an order with no thing says what the empty order says.
- `has_connects`, `has_overlays`, `edge_overlays`: a thing of a series, or of orders side by
  side, is a thing of one of them, and orders side by side put a thing before another only
  where one of them does. `connects_append`, `overlays_append`: a series of two lists is the
  two series in a series, and so for side by side.
- `connects_filter`: an order with no thing may be left out of a series.

What this module does not claim: that an order has no cycle (`connect` of a thing with itself
puts it before itself); that `edge` is transitive, which it is not for `overlay` of two series
that share a thing; a normal form of expressions, or a test of whether two say the same.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **An order of things, as an expression**: the empty order, one thing, two orders with
nothing between them, and two orders with each thing of the first before each thing of the
second. -/
inductive AGraph (α : Type) where
  /-- No thing. -/
  | empty
  /-- One thing. -/
  | vertex (a : α)
  /-- Two orders, and no order between them. -/
  | overlay (x y : AGraph α)
  /-- Two orders, and each thing of the first before each thing of the second. -/
  | connect (x y : AGraph α)

namespace AGraph

variable {α : Type}

/-- **What an order says**: which things are in it, and which it puts before which. -/
structure Rel (α : Type) where
  /-- The thing is in the order. -/
  has : α → Prop
  /-- The order puts the first thing before the second. -/
  edge : α → α → Prop

/-- **What an expression says.** -/
def denote : AGraph α → Rel α
  | .empty => ⟨fun _ => False, fun _ _ => False⟩
  | .vertex a => ⟨fun b => b = a, fun _ _ => False⟩
  | .overlay x y => ⟨fun b => (denote x).has b ∨ (denote y).has b,
      fun a b => (denote x).edge a b ∨ (denote y).edge a b⟩
  | .connect x y => ⟨fun b => (denote x).has b ∨ (denote y).has b,
      fun a b => (denote x).edge a b ∨ (denote y).edge a b ∨ ((denote x).has a ∧ (denote y).has b)⟩

/-- A series of orders: each before all that follow. -/
def connects : List (AGraph α) → AGraph α
  | [] => .empty
  | x :: xs => .connect x (connects xs)

/-- Orders side by side: no order between any two. -/
def overlays : List (AGraph α) → AGraph α
  | [] => .empty
  | x :: xs => .overlay x (overlays xs)

/-- Two orders say the same when they have the same things and the same pairs. -/
theorem Rel.ext' {r s : Rel α} (h1 : ∀ a, r.has a ↔ s.has a)
    (h2 : ∀ a b, r.edge a b ↔ s.edge a b) : r = s := by
  cases r
  cases s
  congr
  · funext a
    exact propext (h1 a)
  · funext a b
    exact propext (h2 a b)

/-- **The two ends of a pair are things of the order.** -/
theorem edge_has : ∀ (x : AGraph α) {a b : α}, (denote x).edge a b →
    (denote x).has a ∧ (denote x).has b
  | .empty, _, _, h => h.elim
  | .vertex _, _, _, h => h.elim
  | .overlay x y, _, _, h => by
    rcases h with h | h
    · exact ⟨.inl (edge_has x h).1, .inl (edge_has x h).2⟩
    · exact ⟨.inr (edge_has y h).1, .inr (edge_has y h).2⟩
  | .connect x y, _, _, h => by
    rcases h with h | h | ⟨ha, hb⟩
    · exact ⟨.inl (edge_has x h).1, .inl (edge_has x h).2⟩
    · exact ⟨.inr (edge_has y h).1, .inr (edge_has y h).2⟩
    · exact ⟨.inl ha, .inr hb⟩

/-- Whether a thing is in an order, decided by the expression. -/
def decHas [DecidableEq α] : ∀ (x : AGraph α) (a : α), Decidable ((denote x).has a)
  | .empty, _ => isFalse fun h => h
  | .vertex b, a => inferInstanceAs (Decidable (a = b))
  | .overlay x y, a => @instDecidableOr _ _ (decHas x a) (decHas y a)
  | .connect x y, a => @instDecidableOr _ _ (decHas x a) (decHas y a)

/-- Whether a thing is in an order is decided, so a program can test its orders. -/
instance [DecidableEq α] (x : AGraph α) (a : α) : Decidable ((denote x).has a) := decHas x a

/-- Whether an order puts a thing before another, decided by the expression. -/
def decEdge [DecidableEq α] : ∀ (x : AGraph α) (a b : α), Decidable ((denote x).edge a b)
  | .empty, _, _ => isFalse fun h => h
  | .vertex _, _, _ => isFalse fun h => h
  | .overlay x y, a, b => @instDecidableOr _ _ (decEdge x a b) (decEdge y a b)
  | .connect x y, a, b =>
    @instDecidableOr _ _ (decEdge x a b)
      (@instDecidableOr _ _ (decEdge y a b) (@instDecidableAnd _ _ (decHas x a) (decHas y b)))

/-- Whether an order puts a thing before another is decided. -/
instance [DecidableEq α] (x : AGraph α) (a b : α) : Decidable ((denote x).edge a b) :=
  decEdge x a b

/-! ## The eight laws -/

theorem overlay_comm (x y : AGraph α) : denote (overlay x y) = denote (overlay y x) :=
  Rel.ext' (fun _ => Or.comm) (fun _ _ => Or.comm)

theorem overlay_assoc (x y z : AGraph α) :
    denote (overlay x (overlay y z)) = denote (overlay (overlay x y) z) :=
  Rel.ext' (fun _ => or_assoc.symm) (fun _ _ => or_assoc.symm)

theorem empty_connect (x : AGraph α) : denote (connect empty x) = denote x := by
  refine Rel.ext' (fun _ => ⟨fun h => h.elim False.elim id, .inr⟩)
    (fun _ _ => ⟨fun h => ?_, fun h => .inr (.inl h)⟩)
  rcases h with h | h | ⟨h, _⟩
  · exact h.elim
  · exact h
  · exact h.elim

theorem connect_empty (x : AGraph α) : denote (connect x empty) = denote x := by
  refine Rel.ext' (fun _ => ⟨fun h => h.elim id False.elim, .inl⟩)
    (fun _ _ => ⟨fun h => ?_, fun h => .inl h⟩)
  rcases h with h | h | ⟨_, h⟩
  · exact h
  · exact h.elim
  · exact h.elim

theorem connect_assoc (x y z : AGraph α) :
    denote (connect x (connect y z)) = denote (connect (connect x y) z) := by
  refine Rel.ext' (fun _ => or_assoc.symm) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with h | (h | h | ⟨ha, hb⟩) | ⟨ha, hb | hb⟩
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr ⟨.inl ha, hb⟩)
  · rcases h with (h | h | ⟨ha, hb⟩) | h | ⟨ha | ha, hb⟩
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr ⟨ha, .inl hb⟩)
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inr (.inr ⟨ha, .inr hb⟩)
    · exact .inr (.inl (.inr (.inr ⟨ha, hb⟩)))

theorem connect_overlay (x y z : AGraph α) :
    denote (connect x (overlay y z)) = denote (overlay (connect x y) (connect x z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with h | h | h
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr (.inr h)
  · rcases h with (h | h) | (h | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · rcases h with h | (h | h) | ⟨ha, hb | hb⟩
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with (h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr ⟨ha, .inl hb⟩)
    · exact .inl h
    · exact .inr (.inl (.inr h))
    · exact .inr (.inr ⟨ha, .inr hb⟩)

theorem overlay_connect (x y z : AGraph α) :
    denote (connect (overlay x y) z) = denote (overlay (connect x z) (connect y z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr h)
  · rcases h with (h | h) | (h | h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)
    · exact .inr h
  · rcases h with (h | h) | h | ⟨ha | ha, hb⟩
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with (h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inl ha, hb⟩)
    · exact .inl (.inr h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)

/-- **A series of three is its three pairs.** -/
theorem decompose (x y z : AGraph α) :
    denote (connect (connect x y) z) =
      denote (overlay (overlay (connect x y) (connect x z)) (connect y z)) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inr (.inr h)
  · rcases h with ((h | h) | (h | h)) | (h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)
    · exact .inr h
  · rcases h with (h | h | ⟨ha, hb⟩) | h | ⟨ha | ha, hb⟩
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr (.inl h)))
    · exact .inl (.inl (.inr (.inr ⟨ha, hb⟩)))
    · exact .inr (.inr (.inl h))
    · exact .inl (.inr (.inr (.inr ⟨ha, hb⟩)))
    · exact .inr (.inr (.inr ⟨ha, hb⟩))
  · rcases h with ((h | h | ⟨ha, hb⟩) | (h | h | ⟨ha, hb⟩)) | (h | h | ⟨ha, hb⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr (.inl h))
    · exact .inl (.inr (.inr ⟨ha, hb⟩))
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inl ha, hb⟩)
    · exact .inl (.inr (.inl h))
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨.inr ha, hb⟩)

/-! ## Two consequences -/

theorem overlay_idem (x : AGraph α) : denote (overlay x x) = denote x :=
  Rel.ext' (fun _ => or_self_iff) (fun _ _ => or_self_iff)

theorem absorb (x y : AGraph α) :
    denote (overlay (overlay (connect x y) x) y) = denote (connect x y) := by
  refine Rel.ext' (fun a => ⟨fun h => ?_, fun h => ?_⟩) (fun a b => ⟨fun h => ?_, fun h => ?_⟩)
  · rcases h with (h | h) | h
    · exact h
    · exact .inl h
    · exact .inr h
  · exact .inl (.inl h)
  · rcases h with (h | h) | h
    · exact h
    · exact .inl h
    · exact .inr (.inl h)
  · exact .inl (.inl h)

/-! ## One expression inside another -/

/-- **A series respects what its two parts say.** -/
theorem connect_congr {x x' y y' : AGraph α} (hx : denote x = denote x')
    (hy : denote y = denote y') : denote (connect x y) = denote (connect x' y') := by
  show Rel.mk _ _ = Rel.mk _ _
  rw [hx, hy]

/-- **Side by side respects what its two parts say.** -/
theorem overlay_congr {x x' y y' : AGraph α} (hx : denote x = denote x')
    (hy : denote y = denote y') : denote (overlay x y) = denote (overlay x' y') := by
  show Rel.mk _ _ = Rel.mk _ _
  rw [hx, hy]

/-- **An order with no thing says what the empty order says.** -/
theorem denote_of_none {x : AGraph α} (h : ∀ a, ¬(denote x).has a) : denote x = denote empty :=
  Rel.ext' (fun a => ⟨fun ha => h a ha, False.elim⟩)
    (fun a _ => ⟨fun he => h a (edge_has x he).1, False.elim⟩)

/-- A series after an order with no thing is the rest of the series. -/
theorem connect_none_left {x y : AGraph α} (h : ∀ a, ¬(denote x).has a) :
    denote (connect x y) = denote y :=
  (connect_congr (denote_of_none h) rfl).trans (empty_connect y)

/-! ## Series and side by side, of many -/

/-- A thing of a series is a thing of one of its orders. -/
theorem has_connects : ∀ (xs : List (AGraph α)) (a : α),
    (denote (connects xs)).has a ↔ ∃ x ∈ xs, (denote x).has a
  | [], _ => ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩
  | x :: xs, a => by
    show (denote x).has a ∨ (denote (connects xs)).has a ↔ _
    rw [has_connects xs a]
    constructor
    · intro h
      rcases h with h | ⟨y, hy, h⟩
      · exact ⟨x, List.mem_cons_self, h⟩
      · exact ⟨y, List.mem_cons_of_mem x hy, h⟩
    · intro ⟨y, hy, h⟩
      rcases List.mem_cons.mp hy with e | hy'
      · exact .inl (e ▸ h)
      · exact .inr ⟨y, hy', h⟩

/-- A thing of orders side by side is a thing of one of them. -/
theorem has_overlays : ∀ (xs : List (AGraph α)) (a : α),
    (denote (overlays xs)).has a ↔ ∃ x ∈ xs, (denote x).has a
  | [], _ => ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩
  | x :: xs, a => by
    show (denote x).has a ∨ (denote (overlays xs)).has a ↔ _
    rw [has_overlays xs a]
    constructor
    · intro h
      rcases h with h | ⟨y, hy, h⟩
      · exact ⟨x, List.mem_cons_self, h⟩
      · exact ⟨y, List.mem_cons_of_mem x hy, h⟩
    · intro ⟨y, hy, h⟩
      rcases List.mem_cons.mp hy with e | hy'
      · exact .inl (e ▸ h)
      · exact .inr ⟨y, hy', h⟩

/-- **Orders side by side put a thing before another only where one of them does.** -/
theorem edge_overlays : ∀ (xs : List (AGraph α)) (a b : α),
    (denote (overlays xs)).edge a b ↔ ∃ x ∈ xs, (denote x).edge a b
  | [], _, _ => ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩
  | x :: xs, a, b => by
    show (denote x).edge a b ∨ (denote (overlays xs)).edge a b ↔ _
    rw [edge_overlays xs a b]
    constructor
    · intro h
      rcases h with h | ⟨y, hy, h⟩
      · exact ⟨x, List.mem_cons_self, h⟩
      · exact ⟨y, List.mem_cons_of_mem x hy, h⟩
    · intro ⟨y, hy, h⟩
      rcases List.mem_cons.mp hy with e | hy'
      · exact .inl (e ▸ h)
      · exact .inr ⟨y, hy', h⟩

/-- **A series of two lists is the two series in a series.** -/
theorem connects_append : ∀ xs ys : List (AGraph α),
    denote (connects (xs ++ ys)) = denote (connect (connects xs) (connects ys))
  | [], ys => (empty_connect (connects ys)).symm
  | x :: xs, ys =>
    (connect_congr rfl (connects_append xs ys)).trans (connect_assoc x (connects xs) (connects ys))

/-- **Two lists side by side are their orders side by side.** -/
theorem overlays_append : ∀ xs ys : List (AGraph α),
    denote (overlays (xs ++ ys)) = denote (overlay (overlays xs) (overlays ys))
  | [], _ => Rel.ext' (fun _ => ⟨.inr, fun h => h.elim False.elim id⟩)
      (fun _ _ => ⟨.inr, fun h => h.elim False.elim id⟩)
  | x :: xs, ys =>
    (overlay_congr rfl (overlays_append xs ys)).trans (overlay_assoc x (overlays xs) (overlays ys))

/-- **An order with no thing may be left out of a series.** Where each index that a test
refuses gives an order with no thing, the series of the indices that pass says what the series
of all says. -/
theorem connects_filter {ι : Type} (g : ι → AGraph α) (p : ι → Bool) : ∀ xs : List ι,
    (∀ x ∈ xs, p x = false → ∀ a, ¬(denote (g x)).has a) →
    denote (connects ((xs.filter p).map g)) = denote (connects (xs.map g))
  | [], _ => rfl
  | x :: xs, h => by
    have ih := connects_filter g p xs fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hp : p x with
    | true =>
      rw [List.filter_cons_of_pos hp]
      exact connect_congr rfl ih
    | false =>
      rw [List.filter_cons_of_neg (fun e => Bool.false_ne_true (hp.symm.trans e))]
      exact ih.trans (connect_none_left (h x List.mem_cons_self hp)).symm

end AGraph

end Whatwg.Svg.Scene
