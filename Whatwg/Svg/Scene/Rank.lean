import Whatwg.Svg.Scene.Cross

/-!
# Whatwg.Svg.Scene.Rank

Owner: the order of the things of one rank (slice S22 of `docs/SVG-PACKAGE-PLAN.md`). A first
step, and not the whole of it.

A graph drawn in layers has its things in rows (`Layers.rows` of
`Whatwg/Svg/Scene/Layered.lean`), and the laws of that picture hold whatever the order of a row
(`Layers.Down.members`). The order matters to a reader all the same: two links that cross cost
most, and the order of a row decides which cross. `Whatwg/Svg/Scene/Cross.lean` counts the
crossings of an order (`Cross.inversions`) and has no operation that lowers the count.
lean4-effect4 orders each rank by the mean place of each thing's neighbours in the rank beside
it (`Graph.reorder` of its `tools/Tools/View/Graph.lean`), which that file calls the order by
barycentres. This module has that operation, and the first law that it needs to be used at
all: it loses no thing and makes none.

- `Rank.sortBy le l`: **a row in order**, by a test of "not after". Things that the test does
  not tell apart keep the order they had.
- `Rank.place order k`: the place of a thing in a rank.
- `Rank.mean order beside nbrs k`: the mean place of a thing's neighbours in the rank beside,
  as a fraction of two whole numbers. A thing with no neighbour there keeps its own place.
- `Rank.reorder order beside nbrs`: **the rank in the order of those means.**
- `Rank.ends upper lower links`: the links between two ranks as pairs of places, which
  `Cross.inversions` counts.

What the laws say:

- `mem_sortBy`, `length_sortBy`, `sortBy_nodup`: the row has the things given, as many, and
  each once where they were given once. `mem_reorder`, `reorder_nodup` say it of `reorder`. So
  rows that go down the links of a graph still do when each is reordered, and the laws of the
  layered picture hold of the reordered rows.
- `sortBy_of_sorted`: a row that is in order is left as it is.
- `sortBy_sorted`: the row is in order, where the test puts one of each two things not after
  the other and is transitive.

What this module does not claim: **that `reorder` lowers the count of crossings.** It is a
method that often does, and a guard below shows one case; no law here says when. The law that
is wanted first is that a rank whose things have one neighbour each has no crossing after it.
Nor does it claim the sweeps down and up over all the ranks, or places across.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Rank

variable {κ : Type}

/-- A thing put into a row, before the first thing that it is not after. -/
def put (le : κ → κ → Bool) (a : κ) : List κ → List κ
  | [] => [a]
  | b :: rest => if le a b then a :: b :: rest else b :: put le a rest

/-- **A row in order**, by a test of "not after". Things that the test does not tell apart keep
the order they had. -/
def sortBy (le : κ → κ → Bool) : List κ → List κ
  | [] => []
  | a :: rest => put le a (sortBy le rest)

theorem mem_put (le : κ → κ → Bool) (a x : κ) : ∀ l : List κ, x ∈ put le a l ↔ x = a ∨ x ∈ l
  | [] => List.mem_singleton.trans ⟨Or.inl, fun h => h.elim id fun h' => nomatch h'⟩
  | b :: rest => by
    cases h : le a b with
    | true =>
      rw [put, if_pos h]
      exact List.mem_cons
    | false =>
      rw [put, if_neg (fun e => Bool.false_ne_true (h.symm.trans e)), List.mem_cons,
        mem_put le a x rest, List.mem_cons]
      exact ⟨fun h1 => h1.elim (fun e => Or.inr (Or.inl e))
          fun h2 => h2.elim Or.inl fun m => Or.inr (Or.inr m),
        fun h1 => h1.elim (fun e => Or.inr (Or.inl e))
          fun h2 => h2.elim Or.inl fun m => Or.inr (Or.inr m)⟩

/-- **The row has the things given.** -/
theorem mem_sortBy (le : κ → κ → Bool) (x : κ) : ∀ l : List κ, x ∈ sortBy le l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: rest => by
    rw [sortBy, mem_put, mem_sortBy le x rest, List.mem_cons]

theorem length_put (le : κ → κ → Bool) (a : κ) : ∀ l : List κ, (put le a l).length = l.length + 1
  | [] => rfl
  | b :: rest => by
    cases h : le a b with
    | true => rw [put, if_pos h, List.length_cons]
    | false =>
      rw [put, if_neg (fun e => Bool.false_ne_true (h.symm.trans e)), List.length_cons,
        length_put le a rest, List.length_cons]

/-- The row has as many things as were given. -/
theorem length_sortBy (le : κ → κ → Bool) : ∀ l : List κ, (sortBy le l).length = l.length
  | [] => rfl
  | a :: rest => by
    rw [sortBy, length_put, length_sortBy le rest, List.length_cons]

theorem put_nodup (le : κ → κ → Bool) (a : κ) : ∀ l : List κ, a ∉ l → l.Nodup →
    (put le a l).Nodup
  | [], _, _ => List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩
  | b :: rest, ha, hn => by
    cases h : le a b with
    | true =>
      rw [put, if_pos h]
      exact List.nodup_cons.mpr ⟨ha, hn⟩
    | false =>
      have nd := List.nodup_cons.mp hn
      rw [put, if_neg (fun e => Bool.false_ne_true (h.symm.trans e))]
      refine List.nodup_cons.mpr ⟨fun hb => ?_,
        put_nodup le a rest (fun m => ha (List.mem_cons_of_mem b m)) nd.2⟩
      cases (mem_put le a b rest).mp hb with
      | inl e => exact ha (e ▸ List.mem_cons_self)
      | inr m => exact nd.1 m

/-- **The row has each thing once**, where the things were given once. -/
theorem sortBy_nodup (le : κ → κ → Bool) : ∀ l : List κ, l.Nodup → (sortBy le l).Nodup
  | [], _ => List.nodup_nil
  | a :: rest, hn => by
    have nd := List.nodup_cons.mp hn
    rw [sortBy]
    exact put_nodup le a _ (fun m => nd.1 ((mem_sortBy le a rest).mp m))
      (sortBy_nodup le rest nd.2)

/-- **A row that is in order is left as it is.** -/
theorem sortBy_of_sorted (le : κ → κ → Bool) : ∀ {l : List κ},
    l.Pairwise (fun a b => le a b = true) → sortBy le l = l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    have h' := List.pairwise_cons.mp h
    rw [sortBy, sortBy_of_sorted le h'.2, put, if_pos (h'.1 b List.mem_cons_self)]

/-- A thing put into a row that is in order leaves it in order. -/
theorem put_sorted {le : κ → κ → Bool} (total : ∀ a b, le a b = true ∨ le b a = true)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) (a : κ) : ∀ l : List κ,
    l.Pairwise (fun x y => le x y = true) → (put le a l).Pairwise fun x y => le x y = true
  | [], _ => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | b :: rest, h => by
    have h' := List.pairwise_cons.mp h
    cases hab : le a b with
    | true =>
      rw [put, if_pos hab]
      refine List.Pairwise.cons (fun y hy => ?_) h
      cases List.mem_cons.mp hy with
      | inl e =>
        rw [e]
        exact hab
      | inr m => exact trans a b y hab (h'.1 y m)
    | false =>
      have hba : le b a = true :=
        (total a b).resolve_left fun e => Bool.false_ne_true (hab.symm.trans e)
      rw [put, if_neg (fun e => Bool.false_ne_true (hab.symm.trans e))]
      refine List.Pairwise.cons (fun y hy => ?_) (put_sorted total trans a rest h'.2)
      cases (mem_put le a y rest).mp hy with
      | inl e =>
        rw [e]
        exact hba
      | inr m => exact h'.1 y m

/-- **The row is in order**, where the test puts one of each two things not after the other and
is transitive. -/
theorem sortBy_sorted {le : κ → κ → Bool} (total : ∀ a b, le a b = true ∨ le b a = true)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) : ∀ l : List κ,
    (sortBy le l).Pairwise fun x y => le x y = true
  | [] => List.Pairwise.nil
  | a :: rest => put_sorted total trans a _ (sortBy_sorted total trans rest)

section

variable [DecidableEq κ]

/-- The place of a thing in a rank: how many things stand before the first of it. A thing that
is not in the rank has the count of the rank. -/
def place (order : List κ) (k : κ) : Nat := order.findIdx fun x => decide (x = k)

/-- **The mean place of a thing's neighbours in the rank beside**, as a fraction: twice the sum
of their places over twice their count. A thing with no neighbour there keeps its own place. -/
def mean (order beside : List κ) (nbrs : κ → List κ) (k : κ) : Nat × Nat :=
  if ((nbrs k).filter fun n => decide (n ∈ beside)).isEmpty then (2 * place order k, 2)
  else (((nbrs k).filter fun n => decide (n ∈ beside)).foldl (fun s n => s + 2 * place beside n) 0,
    2 * ((nbrs k).filter fun n => decide (n ∈ beside)).length)

/-- **The rank in the order of the mean places of its things' neighbours** in the rank beside.
Two fractions are compared by their cross products. -/
def reorder (order beside : List κ) (nbrs : κ → List κ) : List κ :=
  sortBy (fun a b => decide ((mean order beside nbrs a).1 * (mean order beside nbrs b).2 ≤
    (mean order beside nbrs b).1 * (mean order beside nbrs a).2)) order

/-- **A reordered rank has the things of the rank.** -/
theorem mem_reorder (order beside : List κ) (nbrs : κ → List κ) (x : κ) :
    x ∈ reorder order beside nbrs ↔ x ∈ order := mem_sortBy _ x order

/-- **A reordered rank has each thing once**, where the rank has. -/
theorem reorder_nodup (order beside : List κ) (nbrs : κ → List κ) (h : order.Nodup) :
    (reorder order beside nbrs).Nodup := sortBy_nodup _ order h

/-- The links between two ranks as pairs of places: for each link, the place of its upper end
and the place of its lower end. `Cross.inversions` of them is the count of crossings. -/
def ends (upper lower : List κ) (links : List (κ × κ)) : List (Int × Int) :=
  links.map fun l => ((place upper l.1 : Nat), (place lower l.2 : Nat))

end

end Rank

/-! ## One case, and a control -/

-- Two links that cross: from `a` to `d` and from `b` to `c`, with the lower rank in the order
-- `c`, `d`. The mean place of the neighbours of `c` is 1 and of `d` is 0, so the lower rank
-- reordered is `d`, `c`, and the links no longer cross. This is one case, and no law.
#guard Cross.inversions (Rank.ends ["a", "b"] ["c", "d"] [("a", "d"), ("b", "c")]) == 1
#guard Rank.reorder ["c", "d"] ["a", "b"]
  (fun k => if k == "c" then ["b"] else if k == "d" then ["a"] else []) == ["d", "c"]
#guard Cross.inversions (Rank.ends ["a", "b"] ["d", "c"] [("a", "d"), ("b", "c")]) == 0

-- A control: things whose neighbours have one mean keep the order they were given, whatever
-- crosses. Each of `x` and `y` has both upper things as its neighbours, and the rank stays as
-- it is.
#guard Rank.reorder ["x", "y"] ["a", "b"] (fun _ => ["a", "b"]) == ["x", "y"]

-- A stable sort keeps the order of things that the test does not tell apart.
#guard Rank.sortBy (fun (a b : Nat × String) => decide (a.1 ≤ b.1))
  [(2, "p"), (1, "q"), (2, "r"), (1, "s")] == [(1, "q"), (1, "s"), (2, "p"), (2, "r")]

end Whatwg.Svg.Scene
