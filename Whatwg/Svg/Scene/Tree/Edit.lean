import Whatwg.Svg.Scene.Tree
import Whatwg.Svg.Scene.Between

/-!
# Whatwg.Svg.Scene.Tree.Edit

Owner: what an edit of a tree does to the placement of its nodes (slice S16 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-88).

A live view answers one edit at a time. An edit replaces the subtree at one address, and
nothing else. The picture of the tree before and the picture after are joined by key, and the
step between them is drawn. This module says what the edit does to the nodes it did not touch,
so that the step needs no search. The placement is that of `Whatwg/Svg/Scene/Tree.lean`: the
leaves in a row, and a node over its leaves. Every law here is exact, in whole numbers.

- `Tree.replace new a t`: the tree with the subtree at the address `a` replaced by `new`. An
  address is the child to take at each level, from the root. `Tree.subtree? a t` is the subtree
  there, if the address leads to one, and `Tree.column start a t` is the column where it starts.
- The address after the edit. The subtree there is the new one (`subtree?_replace`). An address
  that leads nowhere changes nothing (`replace_none`), and neither does a subtree replaced by
  itself (`replace_self`). The second of two edits at one address is the one that stays
  (`replace_replace`).
- The leaves. `leaves_replace`: the edited tree and the old subtree have together as many
  leaves as the tree and the new subtree. Whole numbers have no difference, so a change of a
  count is said with two sums. With `gain` the leaves of the new subtree and `loss` the leaves
  of the old one, a count `n` becomes the `n'` with `n' + loss = n + gain`.
- Where the subtrees stand. The subtree at an address stands inside the columns of the tree
  (`column_within`), and it is drawn at its column and at the depth of its address
  (`spans_subtree`). The new subtree starts where the old one started (`column_replace`), and
  it is drawn there (`spans_replace_new`).
- **The law of the module** is `spans_replace`. Every node of the edited picture is a node of
  the new subtree, or it is a node of the old picture with the same value whose span is
  `Span.Edited`. `spans_replace_old` is the same law from the old picture: no kept node is
  lost. `Span.Edited` has three groups, and the old span tells which
  (`Edited.eq_of_before`, `Edited.stretched_of_over`, `Edited.shifted_of_after`).
  - A node that ends before the edit keeps its span.
  - A node over the edit, on the way to the address, keeps its first column and its depth. Its
    last column moves by the change of the count (`Span.Stretched`).
  - A node that starts after the edit moves by the change of the count, with its width and its
    depth as they were (`Span.Shifted`).

  `spans_replace_before`, `spans_replace_over` and `spans_replace_after` are the law for one
  node of the old picture in each group. The old span and the edit give the new span
  (`Edited.unique`). An edit read backward is an edit (`Edited.symm`), and no kept node changes
  its row (`Edited.depth`). Each of the three relations is read from numbers, so a program may
  check a step.
- A group that shifts is rigid. `Span.place` is where a node is drawn. Two nodes after the edit
  keep the step between them (`Shifted.rigid`, `Shifted.place_step`), and they keep it at every
  eased progress when both go the straight way with one timing (`Shifted.moment`). The nodes
  before the edit do not move. So the edges inside each of the two groups need no change of
  shape. The nodes on the way are the third group: an edge from one of them to a node after the
  edit changes its shape.
- No interleaving on the way. `spansAll_apart_between`: the columns of a subtree stay before
  the columns of its later siblings at every eased progress in range, between any two
  pictures.

What this module does not claim. The two pictures are joined by the value of a node, which is
its key. Where two nodes of one picture have one value, `spans_replace` gives a node of the old
picture with that value and does not say which. No law here counts the nodes: that each picture
has each of its nodes once is `spans_values` of `Tree.lean`. An edit that moves a subtree to
another address is two edits, and no law here joins the two. The laws are of the placement of
`Tree.lean`. A narrower placement, where a small subtree slides under a neighbour, is another
placement, and nothing here speaks of it.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Tree

variable {α : Type}

/-! ## An edit at an address -/

mutual

/-- The tree with the subtree at an address replaced. An address is the child to take at each
level, from the root. An address that leads nowhere leaves the tree as it is. -/
def replace (new : Tree α) : List Nat → Tree α → Tree α
  | [], _ => new
  | i :: rest, .node v cs => .node v (replaceAt new i rest cs)

/-- The list of trees with the subtree at an address replaced: the address is the place `i` in
the list, and then `rest` from that tree. -/
def replaceAt (new : Tree α) : Nat → List Nat → List (Tree α) → List (Tree α)
  | _, _, [] => []
  | 0, rest, t :: ts => replace new rest t :: ts
  | i + 1, rest, t :: ts => t :: replaceAt new i rest ts

end

mutual

/-- The subtree at an address, if the address leads to one. -/
def subtree? : List Nat → Tree α → Option (Tree α)
  | [], t => some t
  | i :: rest, .node _ cs => subtreeAt? i rest cs

/-- The subtree at an address in a list of trees, if the address leads to one. -/
def subtreeAt? : Nat → List Nat → List (Tree α) → Option (Tree α)
  | _, _, [] => none
  | 0, rest, t :: _ => subtree? rest t
  | i + 1, rest, _ :: ts => subtreeAt? i rest ts

end

mutual

/-- The column where the subtree at an address starts, in a tree whose first leaf is in the
column `start`. An address that leads nowhere gives a column of the tree, and no law reads
it. -/
def column (start : Nat) : List Nat → Tree α → Nat
  | [], _ => start
  | i :: rest, .node _ cs => columnAt start i rest cs

/-- The column where the subtree at an address starts, in a list of trees whose first leaf is in
the column `start`. -/
def columnAt (start : Nat) : Nat → List Nat → List (Tree α) → Nat
  | _, _, [] => start
  | 0, rest, t :: _ => column start rest t
  | i + 1, rest, t :: ts => columnAt (start + leaves t) i rest ts

end

/-! ## What the address leads to, after the edit -/

mutual

/-- **The subtree at the address after the edit is the new one.** -/
theorem subtree?_replace (new old : Tree α) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some old → subtree? a (replace new a t) = some new
  | [], _, _ => by rw [replace, subtree?]
  | i :: rest, .node _ cs, h => by
    rw [subtree?] at h
    rw [replace, subtree?]
    exact subtreeAt?_replaceAt new old i rest cs h

/-- The same for a list of trees. -/
theorem subtreeAt?_replaceAt (new old : Tree α) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), subtreeAt? i rest cs = some old →
    subtreeAt? i rest (replaceAt new i rest cs) = some new
  | _, _, [], h => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: _, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, subtreeAt?]
    exact subtree?_replace new old rest t h
  | i + 1, rest, _ :: ts, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, subtreeAt?]
    exact subtreeAt?_replaceAt new old i rest ts h

end

mutual

/-- **An address that leads nowhere changes nothing.** -/
theorem replace_none (new : Tree α) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = none → replace new a t = t
  | [], _, h => by
    rw [subtree?] at h
    cases h
  | i :: rest, .node _ cs, h => by
    rw [subtree?] at h
    rw [replace, replaceAt_none new i rest cs h]

/-- The same for a list of trees. -/
theorem replaceAt_none (new : Tree α) : ∀ (i : Nat) (rest : List Nat) (cs : List (Tree α)),
    subtreeAt? i rest cs = none → replaceAt new i rest cs = cs
  | _, _, [], _ => by rw [replaceAt]
  | 0, rest, t :: _, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, replace_none new rest t h]
  | i + 1, rest, _ :: ts, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, replaceAt_none new i rest ts h]

end

mutual

/-- **A subtree replaced by itself is the tree.** -/
theorem replace_self (old : Tree α) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some old → replace old a t = t
  | [], _, h => by
    rw [subtree?] at h
    cases h
    rw [replace]
  | i :: rest, .node _ cs, h => by
    rw [subtree?] at h
    rw [replace, replaceAt_self old i rest cs h]

/-- The same for a list of trees. -/
theorem replaceAt_self (old : Tree α) : ∀ (i : Nat) (rest : List Nat) (cs : List (Tree α)),
    subtreeAt? i rest cs = some old → replaceAt old i rest cs = cs
  | _, _, [], _ => by rw [replaceAt]
  | 0, rest, t :: _, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, replace_self old rest t h]
  | i + 1, rest, _ :: ts, h => by
    rw [subtreeAt?] at h
    rw [replaceAt, replaceAt_self old i rest ts h]

end

mutual

/-- **The second of two edits at one address is the one that stays.** -/
theorem replace_replace (new next : Tree α) : ∀ (a : List Nat) (t : Tree α),
    replace next a (replace new a t) = replace next a t
  | [], _ => by rw [replace, replace]
  | i :: rest, .node _ cs => by
    rw [replace, replace, replace, replaceAt_replaceAt new next i rest cs]

/-- The same for a list of trees. -/
theorem replaceAt_replaceAt (new next : Tree α) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), replaceAt next i rest (replaceAt new i rest cs) = replaceAt next i rest cs
  | _, _, [] => by rw [replaceAt]
  | 0, rest, t :: _ => by
    rw [replaceAt, replaceAt, replaceAt, replace_replace new next rest t]
  | i + 1, rest, _ :: ts => by
    rw [replaceAt, replaceAt, replaceAt, replaceAt_replaceAt new next i rest ts]

end

/-! ## The leaves -/

/-- A list of trees with a tree in it has a leaf. -/
theorem leavesAll_pos (t : Tree α) (ts : List (Tree α)) : 0 < leavesAll (t :: ts) := by
  rw [leavesAll]
  exact Nat.lt_of_lt_of_le (leaves_pos t) (Nat.le_add_right _ _)

/-- The children that an address goes into have a leaf, before the edit and after it. -/
private theorem leavesAll_pos_of_some (new : Tree α) {old : Tree α} : ∀ (i : Nat)
    (rest : List Nat) (cs : List (Tree α)), subtreeAt? i rest cs = some old →
    0 < leavesAll cs ∧ 0 < leavesAll (replaceAt new i rest cs)
  | _, _, [], h => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: ts, _ => by
    rw [replaceAt]
    exact ⟨leavesAll_pos t ts, leavesAll_pos (replace new rest t) ts⟩
  | i + 1, rest, t :: ts, _ => by
    rw [replaceAt]
    exact ⟨leavesAll_pos t ts, leavesAll_pos t (replaceAt new i rest ts)⟩

mutual

/-- **An edit changes the leaves of the tree by what it changes at the address.** With `old` the
subtree that the edit takes away, the edited tree and `old` have together as many leaves as the
tree and `new`. So every node on the way to the address gains or loses exactly what the edit
gains or loses. -/
theorem leaves_replace (new old : Tree α) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some old → leaves (replace new a t) + leaves old = leaves t + leaves new
  | [], _, h => by
    rw [subtree?] at h
    cases h
    rw [replace]
    exact Nat.add_comm _ _
  | i :: rest, .node _ cs, h => by
    rw [subtree?] at h
    have ih := leavesAll_replaceAt new old i rest cs h
    obtain ⟨p, p'⟩ := leavesAll_pos_of_some new i rest cs h
    rw [replace, leaves, leaves, Nat.max_eq_right p', Nat.max_eq_right p]
    exact ih

/-- The same for a list of trees. -/
theorem leavesAll_replaceAt (new old : Tree α) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), subtreeAt? i rest cs = some old →
    leavesAll (replaceAt new i rest cs) + leaves old = leavesAll cs + leaves new
  | _, _, [], h => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: ts, h => by
    rw [subtreeAt?] at h
    have ih := leaves_replace new old rest t h
    rw [replaceAt, leavesAll, leavesAll]
    omega
  | i + 1, rest, t :: ts, h => by
    rw [subtreeAt?] at h
    have ih := leavesAll_replaceAt new old i rest ts h
    rw [replaceAt, leavesAll, leavesAll]
    omega

end

/-! ## The column of the edit -/

mutual

/-- **The subtree at an address stands inside the columns of the tree**: it starts no earlier
than the tree, and it ends no later. -/
theorem column_within (sub : Tree α) (start : Nat) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some sub →
    start ≤ column start a t ∧ column start a t + leaves sub ≤ start + leaves t
  | [], _, h => by
    rw [subtree?] at h
    cases h
    rw [column]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | i :: rest, .node _ cs, h => by
    rw [subtree?] at h
    obtain ⟨a, b⟩ := columnAt_within sub start i rest cs h
    have m : leavesAll cs ≤ max 1 (leavesAll cs) := Nat.le_max_right 1 _
    rw [column, leaves]
    refine ⟨a, ?_⟩
    omega

/-- The same for a list of trees. -/
theorem columnAt_within (sub : Tree α) (start : Nat) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), subtreeAt? i rest cs = some sub →
    start ≤ columnAt start i rest cs ∧ columnAt start i rest cs + leaves sub ≤ start + leavesAll cs
  | _, _, [], h => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: ts, h => by
    rw [subtreeAt?] at h
    obtain ⟨a, b⟩ := column_within sub start rest t h
    rw [columnAt, leavesAll]
    refine ⟨a, ?_⟩
    omega
  | i + 1, rest, t :: ts, h => by
    rw [subtreeAt?] at h
    obtain ⟨a, b⟩ := columnAt_within sub (start + leaves t) i rest ts h
    rw [columnAt, leavesAll]
    refine ⟨?_, ?_⟩
    · omega
    · omega

end

mutual

/-- **The new subtree starts in the column where the old one started.** -/
theorem column_replace (new : Tree α) (start : Nat) : ∀ (a : List Nat) (t : Tree α),
    column start a (replace new a t) = column start a t
  | [], _ => by rw [column, column]
  | i :: rest, .node _ cs => by
    rw [replace, column, column, columnAt_replaceAt new start i rest cs]

/-- The same for a list of trees. -/
theorem columnAt_replaceAt (new : Tree α) (start : Nat) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), columnAt start i rest (replaceAt new i rest cs) = columnAt start i rest cs
  | _, _, [] => by rw [replaceAt]
  | 0, rest, t :: _ => by
    rw [replaceAt, columnAt, columnAt, column_replace new start rest t]
  | i + 1, rest, t :: ts => by
    rw [replaceAt, columnAt, columnAt, columnAt_replaceAt new (start + leaves t) i rest ts]

end

/-- The depth of the child that an address takes, and then the rest of the address. -/
private theorem depth_cons (depth i : Nat) (rest : List Nat) :
    depth + (i :: rest).length = depth + 1 + rest.length := by
  rw [List.length_cons]
  omega

mutual

/-- **The subtree at an address is drawn at its column and at the depth of its address.** Its
nodes are nodes of the picture of the tree, with the spans they have as a tree of their own
placed there. -/
theorem spans_subtree (sub : Tree α) (depth start : Nat) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some sub →
    ∀ p ∈ spans (depth + a.length) (column start a t) sub, p ∈ spans depth start t
  | [], _, h, _, hp => by
    rw [subtree?] at h
    cases h
    rw [column] at hp
    exact hp
  | i :: rest, .node _ cs, h, p, hp => by
    rw [subtree?] at h
    rw [column, depth_cons] at hp
    rw [spans]
    exact List.Mem.tail _ (spansAll_subtreeAt sub (depth + 1) start i rest cs h p hp)

/-- The same for a list of trees. -/
theorem spansAll_subtreeAt (sub : Tree α) (depth start : Nat) : ∀ (i : Nat) (rest : List Nat)
    (cs : List (Tree α)), subtreeAt? i rest cs = some sub →
    ∀ p ∈ spans (depth + rest.length) (columnAt start i rest cs) sub, p ∈ spansAll depth start cs
  | _, _, [], h, _, _ => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: _, h, p, hp => by
    rw [subtreeAt?] at h
    rw [columnAt] at hp
    rw [spansAll]
    exact List.mem_append.mpr (Or.inl (spans_subtree sub depth start rest t h p hp))
  | i + 1, rest, t :: ts, h, p, hp => by
    rw [subtreeAt?] at h
    rw [columnAt] at hp
    rw [spansAll]
    exact List.mem_append.mpr
      (Or.inr (spansAll_subtreeAt sub depth (start + leaves t) i rest ts h p hp))

end

/-- **The new subtree is drawn where the old one stood**: at its column and at the depth of
the address. Its nodes are nodes of the picture of the edited tree. -/
theorem spans_replace_new (new old : Tree α) (depth start : Nat) (a : List Nat) (t : Tree α)
    (h : subtree? a t = some old) :
    ∀ p ∈ spans (depth + a.length) (column start a t) new,
      p ∈ spans depth start (replace new a t) := by
  intro p hp
  rw [← column_replace new start a t] at hp
  exact spans_subtree new depth start a (replace new a t) (subtree?_replace new old a t h) p hp

end Tree

/-! ## How a span changes -/

namespace Span

/-- **The span of a node on the way to the edit**, before and after an edit that puts `gain`
leaves where `loss` were. Its first column and its depth are as before. Its last column moves
by the change of the count: with whole numbers, the new one and `loss` are the old one and
`gain`. -/
structure Stretched (gain loss : Nat) (s s' : Span) : Prop where
  /-- The first column is as before. -/
  first : s'.first = s.first
  /-- The last column moves by the change of the count. -/
  last : s'.last + loss = s.last + gain
  /-- The depth is as before. -/
  depth : s'.depth = s.depth

/-- **The span of a node after the edit**, before and after an edit that puts `gain` leaves
where `loss` were. Its first and its last column both move by the change of the count, and its
depth is as before: the node moves, and its width stays. -/
structure Shifted (gain loss : Nat) (s s' : Span) : Prop where
  /-- The first column moves by the change of the count. -/
  first : s'.first + loss = s.first + gain
  /-- The last column moves by the change of the count. -/
  last : s'.last + loss = s.last + gain
  /-- The depth is as before. -/
  depth : s'.depth = s.depth

/-- **What an edit does to the span of a node that it keeps.** The edit puts `gain` leaves
where `loss` were, from the column `col`. The node is in one of three groups, and its span in
the old picture says which.

- `same`: it ends before the edit, and its span is its span.
- `stretch`: it is over the edit, on the way to the address. Its first column stays, and its
  last column moves by the change of the count.
- `shift`: it starts after the edit. It moves by the change of the count, as it is. -/
inductive Edited (col gain loss : Nat) (s s' : Span) : Prop where
  | same (before : s.last < col) (eq : s' = s)
  | stretch (left : s.first ≤ col) (right : col + loss ≤ s.last + 1)
      (moved : Stretched gain loss s s')
  | shift (after : col + loss ≤ s.first) (moved : Shifted gain loss s s')

/-- Whether a span is stretched so is read from its numbers. -/
instance (gain loss : Nat) (s s' : Span) : Decidable (Stretched gain loss s s') :=
  decidable_of_iff (s'.first = s.first ∧ s'.last + loss = s.last + gain ∧ s'.depth = s.depth)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.first, h.last, h.depth⟩⟩

/-- Whether a span is shifted so is read from its numbers. -/
instance (gain loss : Nat) (s s' : Span) : Decidable (Shifted gain loss s s') :=
  decidable_of_iff
    (s'.first + loss = s.first + gain ∧ s'.last + loss = s.last + gain ∧ s'.depth = s.depth)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.first, h.last, h.depth⟩⟩

/-- Whether a span is edited so is read from its numbers. -/
instance (col gain loss : Nat) (s s' : Span) : Decidable (Edited col gain loss s s') :=
  decidable_of_iff
    ((s.last < col ∧ s' = s) ∨
      (s.first ≤ col ∧ col + loss ≤ s.last + 1 ∧ Stretched gain loss s s') ∨
        (col + loss ≤ s.first ∧ Shifted gain loss s s'))
    ⟨fun h => h.elim (fun a => .same a.1 a.2) fun h =>
        h.elim (fun b => .stretch b.1 b.2.1 b.2.2) fun c => .shift c.1 c.2,
      fun h => by
        cases h with
        | same a b => exact Or.inl ⟨a, b⟩
        | stretch a b c => exact Or.inr (Or.inl ⟨a, b, c⟩)
        | shift a b => exact Or.inr (Or.inr ⟨a, b⟩)⟩

/-- A span is its three numbers. -/
private theorem eq_of_numbers {s t : Span} (h1 : s.first = t.first) (h2 : s.last = t.last)
    (h3 : s.depth = t.depth) : s = t := by
  cases s
  cases t
  cases h1
  cases h2
  cases h3
  rfl

/-- A span that does not change is shifted by nothing. -/
theorem Shifted.refl (g : Nat) (s : Span) : Shifted g g s s := ⟨rfl, rfl, rfl⟩

/-- An edit read backward shifts a span back. -/
theorem Shifted.symm {gain loss : Nat} {s s' : Span} (h : Shifted gain loss s s') :
    Shifted loss gain s' s := ⟨h.first.symm, h.last.symm, h.depth.symm⟩

/-- An edit read backward stretches a span back. -/
theorem Stretched.symm {gain loss : Nat} {s s' : Span} (h : Stretched gain loss s s') :
    Stretched loss gain s' s := ⟨h.first.symm, h.last.symm, h.depth.symm⟩

/-- **No kept node changes its row.** -/
theorem Edited.depth {col gain loss : Nat} {s s' : Span} (h : Edited col gain loss s s') :
    s'.depth = s.depth := by
  cases h with
  | same _ eq => rw [eq]
  | stretch _ _ moved => exact moved.depth
  | shift _ moved => exact moved.depth

/-- **An edit read backward is an edit**: the edit that puts the old subtree back, with the
`loss` leaves where the `gain` are. Each group is the same group read backward. -/
theorem Edited.symm {col gain loss : Nat} {s s' : Span} (h : Edited col gain loss s s') :
    Edited col loss gain s' s := by
  cases h with
  | same before eq =>
    refine Edited.same ?_ eq.symm
    rw [eq]
    exact before
  | stretch left right moved =>
    have a := moved.first
    have b := moved.last
    refine Edited.stretch ?_ ?_ moved.symm
    · omega
    · omega
  | shift after moved =>
    have a := moved.first
    refine Edited.shift ?_ moved.symm
    omega

/-- **A node that ends before the edit keeps its span.** The old span tells the group: here it
ends before the column of the edit. -/
theorem Edited.eq_of_before {col gain loss : Nat} {s s' : Span} (h : Edited col gain loss s s')
    (hl : 0 < loss) (hs : s.first ≤ s.last) (hb : s.last < col) : s' = s := by
  cases h with
  | same _ eq => exact eq
  | stretch _ right _ =>
    exfalso
    omega
  | shift after _ =>
    exfalso
    omega

/-- **A node that is over the edit is stretched.** The old span tells the group: here it starts
no later than the edit and ends no earlier. -/
theorem Edited.stretched_of_over {col gain loss : Nat} {s s' : Span}
    (h : Edited col gain loss s s') (hl : 0 < loss) (h1 : s.first ≤ col)
    (h2 : col + loss ≤ s.last + 1) : Stretched gain loss s s' := by
  cases h with
  | same before _ =>
    exfalso
    omega
  | stretch _ _ moved => exact moved
  | shift after _ =>
    exfalso
    omega

/-- **A node that starts after the edit is shifted.** The old span tells the group: here it
starts after the last column of the old subtree. -/
theorem Edited.shifted_of_after {col gain loss : Nat} {s s' : Span}
    (h : Edited col gain loss s s') (hl : 0 < loss) (hs : s.first ≤ s.last)
    (ha : col + loss ≤ s.first) : Shifted gain loss s s' := by
  cases h with
  | same before _ =>
    exfalso
    omega
  | stretch left _ _ =>
    exfalso
    omega
  | shift _ moved => exact moved

/-- **The old span and the edit give the new span.** A span of a tree is edited to one span and
no other, so the new picture of the kept nodes is read from the old one with no search. The
old subtree has a leaf, and a span of a tree starts no later than it ends. -/
theorem Edited.unique {col gain loss : Nat} {s s₁ s₂ : Span} (h₁ : Edited col gain loss s s₁)
    (h₂ : Edited col gain loss s s₂) (hl : 0 < loss) (hs : s.first ≤ s.last) : s₁ = s₂ := by
  cases h₁ with
  | same before eq => rw [eq, h₂.eq_of_before hl hs before]
  | stretch left right moved =>
    have m := h₂.stretched_of_over hl left right
    have a := moved.first
    have b := moved.last
    have c := moved.depth
    have a' := m.first
    have b' := m.last
    have c' := m.depth
    exact eq_of_numbers (by omega) (by omega) (by omega)
  | shift after moved =>
    have m := h₂.shifted_of_after hl hs after
    have a := moved.first
    have b := moved.last
    have c := moved.depth
    have a' := m.first
    have b' := m.last
    have c' := m.depth
    exact eq_of_numbers (by omega) (by omega) (by omega)

end Span

namespace Tree

variable {α : Type}

/-! ## The three groups -/

/-- A list of trees placed from another column has its spans moved: where the new start and
`loss` are the old start and `gain`, each node is shifted so. -/
theorem spansAll_moved (depth x x' gain loss : Nat) (h : x' + loss = x + gain)
    (ts : List (Tree α)) (p' : α × Span) (hp' : p' ∈ spansAll depth x' ts) :
    ∃ s, (p'.1, s) ∈ spansAll depth x ts ∧ Span.Shifted gain loss s p'.2 := by
  have e1 := spansAll_shift depth x' loss ts
  have e2 := spansAll_shift depth x gain ts
  rw [h, e2] at e1
  have m : (p'.1, p'.2.shift loss) ∈ (spansAll depth x' ts).map fun p => (p.1, p.2.shift loss) :=
    List.mem_map.mpr ⟨p', hp', rfl⟩
  rw [← e1] at m
  obtain ⟨q, hq, e⟩ := List.mem_map.mp m
  have ev0 := congrArg Prod.fst e
  have es0 := congrArg Prod.snd e
  have ev : q.1 = p'.1 := ev0
  have es : q.2.shift gain = p'.2.shift loss := es0
  refine ⟨q.2, ?_, ⟨(congrArg Span.first es).symm, (congrArg Span.last es).symm,
    (congrArg Span.depth es).symm⟩⟩
  rw [← ev]
  exact hq

mutual

/-- **The law of the module: what an edit does to the nodes it does not touch.** The edit
replaces the subtree `old` at the address `a` by `new`. Every node of the picture of the edited
tree is a node of `new`, drawn where `old` stood, or it is a node of the old picture with the
same value whose span is `Span.Edited`: the same before the edit, stretched on the way to it,
and shifted after it. The change of the count is the leaves of `new` against the leaves of
`old`. So a step from the old picture to the new one needs no search. -/
theorem spans_replace (new old : Tree α) (depth start : Nat) : ∀ (a : List Nat) (t : Tree α),
    subtree? a t = some old → ∀ p' ∈ spans depth start (replace new a t),
      p' ∈ spans (depth + a.length) (column start a t) new ∨
        ∃ s, (p'.1, s) ∈ spans depth start t ∧
          Span.Edited (column start a t) (leaves new) (leaves old) s p'.2
  | [], _, _, _, hp' => by
    rw [replace] at hp'
    rw [column]
    exact Or.inl hp'
  | i :: rest, .node v cs, h, p', hp' => by
    rw [subtree?] at h
    obtain ⟨c0, c1⟩ := columnAt_within old start i rest cs h
    obtain ⟨q, q'⟩ := leavesAll_pos_of_some new i rest cs h
    have e := leavesAll_replaceAt new old i rest cs h
    rw [replace, spans, Nat.max_eq_right q'] at hp'
    rw [column]
    cases hp' with
    | head =>
      refine Or.inr ⟨⟨start, start + leavesAll cs - 1, depth⟩, ?_, ?_⟩
      · rw [spans, Nat.max_eq_right q]
        exact List.Mem.head _
      · refine Span.Edited.stretch c0 ?_ ⟨rfl, ?_, rfl⟩
        · show columnAt start i rest cs + leaves old ≤ start + leavesAll cs - 1 + 1
          omega
        · show start + leavesAll (replaceAt new i rest cs) - 1 + leaves old =
            start + leavesAll cs - 1 + leaves new
          omega
    | tail _ hq =>
      rcases spansAll_replaceAt new old (depth + 1) start i rest cs h p' hq with
        hn | ⟨s, hs, hE⟩
      · rw [depth_cons]
        exact Or.inl hn
      · refine Or.inr ⟨s, ?_, hE⟩
        rw [spans]
        exact List.Mem.tail _ hs

/-- The same for a list of trees. -/
theorem spansAll_replaceAt (new old : Tree α) (depth start : Nat) : ∀ (i : Nat)
    (rest : List Nat) (cs : List (Tree α)), subtreeAt? i rest cs = some old →
    ∀ p' ∈ spansAll depth start (replaceAt new i rest cs),
      p' ∈ spans (depth + rest.length) (columnAt start i rest cs) new ∨
        ∃ s, (p'.1, s) ∈ spansAll depth start cs ∧
          Span.Edited (columnAt start i rest cs) (leaves new) (leaves old) s p'.2
  | _, _, [], h, _, _ => by
    rw [subtreeAt?] at h
    cases h
  | 0, rest, t :: ts, h, p', hp' => by
    rw [subtreeAt?] at h
    rw [replaceAt, spansAll] at hp'
    rw [columnAt]
    cases List.mem_append.mp hp' with
    | inl h1 =>
      rcases spans_replace new old depth start rest t h p' h1 with hn | ⟨s, hs, hE⟩
      · exact Or.inl hn
      · refine Or.inr ⟨s, ?_, hE⟩
        rw [spansAll]
        exact List.mem_append.mpr (Or.inl hs)
    | inr h2 =>
      have e := leaves_replace new old rest t h
      obtain ⟨_, c1⟩ := column_within old start rest t h
      obtain ⟨s, hs, hS⟩ := spansAll_moved depth (start + leaves t)
        (start + leaves (replace new rest t)) (leaves new) (leaves old) (by omega) ts p' h2
      have w : start + leaves t ≤ s.first := (spansAll_within depth (start + leaves t) ts _ hs).1
      refine Or.inr ⟨s, ?_, Span.Edited.shift ?_ hS⟩
      · rw [spansAll]
        exact List.mem_append.mpr (Or.inr hs)
      · omega
  | i + 1, rest, t :: ts, h, p', hp' => by
    rw [subtreeAt?] at h
    rw [replaceAt, spansAll] at hp'
    rw [columnAt]
    cases List.mem_append.mp hp' with
    | inl h1 =>
      obtain ⟨c0, _⟩ := columnAt_within old (start + leaves t) i rest ts h
      have w : p'.2.last < start + leaves t := (spans_within depth start t p' h1).2.2.1
      refine Or.inr ⟨p'.2, ?_, Span.Edited.same ?_ rfl⟩
      · rw [spansAll]
        exact List.mem_append.mpr (Or.inl h1)
      · omega
    | inr h2 =>
      rcases spansAll_replaceAt new old depth (start + leaves t) i rest ts h p' h2 with
        hn | ⟨s, hs, hE⟩
      · exact Or.inl hn
      · refine Or.inr ⟨s, ?_, hE⟩
        rw [spansAll]
        exact List.mem_append.mpr (Or.inr hs)

end

/-- **The same law from the old picture.** Every node of the picture of the tree is a node of
`old`, which the edit takes away, or it is a node of the new picture with the same value whose
span is `Span.Edited`. So no kept node is lost, and each one has its group. -/
theorem spans_replace_old (new old : Tree α) (depth start : Nat) (a : List Nat) (t : Tree α)
    (h : subtree? a t = some old) : ∀ p ∈ spans depth start t,
      p ∈ spans (depth + a.length) (column start a t) old ∨
        ∃ s', (p.1, s') ∈ spans depth start (replace new a t) ∧
          Span.Edited (column start a t) (leaves new) (leaves old) p.2 s' := by
  intro p hp
  have back : replace old a (replace new a t) = t := by
    rw [replace_replace, replace_self old a t h]
  rw [← back] at hp
  rcases spans_replace old new depth start a (replace new a t) (subtree?_replace new old a t h)
    p hp with ho | ⟨s, hs, hE⟩
  · rw [column_replace] at ho
    exact Or.inl ho
  · rw [column_replace] at hE
    exact Or.inr ⟨s, hs, hE.symm⟩

/-- **A node that ends before the edit is in the new picture as it is**: the same value with
the same span. The group is read from the old picture: the node ends before the column of the
edit. -/
theorem spans_replace_before (new old : Tree α) (depth start : Nat) (a : List Nat) (t : Tree α)
    (h : subtree? a t = some old) (p : α × Span) (hp : p ∈ spans depth start t)
    (hb : p.2.last < column start a t) : p ∈ spans depth start (replace new a t) := by
  obtain ⟨_, w2, _, _⟩ := spans_within depth start t p hp
  rcases spans_replace_old new old depth start a t h p hp with ho | ⟨s', hs', hE⟩
  · obtain ⟨v1, v2, _, _⟩ := spans_within (depth + a.length) (column start a t) old p ho
    exfalso
    omega
  · rw [hE.eq_of_before (leaves_pos old) w2 hb] at hs'
    exact hs'

/-- **A node on the way to the edit is in the new picture, stretched**: its first column and
its depth are as before, and its last column moves by the change of the count. The group is
read from the old picture: the node is over the columns of the old subtree, and it is above
the depth of the address. -/
theorem spans_replace_over (new old : Tree α) (depth start : Nat) (a : List Nat) (t : Tree α)
    (h : subtree? a t = some old) (p : α × Span) (hp : p ∈ spans depth start t)
    (h1 : p.2.first ≤ column start a t) (h2 : column start a t + leaves old ≤ p.2.last + 1)
    (hd : p.2.depth < depth + a.length) :
    ∃ s', (p.1, s') ∈ spans depth start (replace new a t) ∧
      Span.Stretched (leaves new) (leaves old) p.2 s' := by
  rcases spans_replace_old new old depth start a t h p hp with ho | ⟨s', hs', hE⟩
  · obtain ⟨_, _, _, v4⟩ := spans_within (depth + a.length) (column start a t) old p ho
    exfalso
    omega
  · exact ⟨s', hs', hE.stretched_of_over (leaves_pos old) h1 h2⟩

/-- **A node that starts after the edit is in the new picture, shifted**: it moves by the
change of the count, as it is. The group is read from the old picture: the node starts after
the last column of the old subtree. -/
theorem spans_replace_after (new old : Tree α) (depth start : Nat) (a : List Nat) (t : Tree α)
    (h : subtree? a t = some old) (p : α × Span) (hp : p ∈ spans depth start t)
    (ha : column start a t + leaves old ≤ p.2.first) :
    ∃ s', (p.1, s') ∈ spans depth start (replace new a t) ∧
      Span.Shifted (leaves new) (leaves old) p.2 s' := by
  obtain ⟨_, w2, _, _⟩ := spans_within depth start t p hp
  rcases spans_replace_old new old depth start a t h p hp with ho | ⟨s', hs', hE⟩
  · obtain ⟨_, v2, v3, _⟩ := spans_within (depth + a.length) (column start a t) old p ho
    exfalso
    omega
  · exact ⟨s', hs', hE.shifted_of_after (leaves_pos old) w2 ha⟩

end Tree

/-! ## A group that shifts is rigid -/

namespace Span

/-- Where a node is drawn, in half columns and in rows: twice the middle of its span, and its
depth. -/
def place (s : Span) : IVec := ⟨(s.middle2 : Int), (s.depth : Int)⟩

/-- A node that shifts keeps its width. -/
theorem Shifted.width {gain loss : Nat} {s s' : Span} (h : Shifted gain loss s s') :
    s'.width = s.width := by
  have a := h.first
  have b := h.last
  show s'.last + 1 - s'.first = s.last + 1 - s.first
  omega

/-- **Two nodes that shift keep the step between them.** Whole numbers have no difference, so
the law is a sum: the new column of the second and the old column of the first are the old
column of the second and the new column of the first. It holds of the first columns, of the
last columns and of the depths. -/
theorem Shifted.rigid {gain loss : Nat} {s₁ s₁' s₂ s₂' : Span} (h₁ : Shifted gain loss s₁ s₁')
    (h₂ : Shifted gain loss s₂ s₂') :
    s₂'.first + s₁.first = s₂.first + s₁'.first ∧ s₂'.last + s₁.last = s₂.last + s₁'.last ∧
      s₂'.depth + s₁.depth = s₂.depth + s₁'.depth := by
  have a := h₁.first
  have b := h₂.first
  have c := h₁.last
  have d := h₂.last
  have f := h₁.depth
  have g := h₂.depth
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- **Two nodes that shift stand the same step apart in both pictures**, as places of whole
units. So an edge between them has one shape in both. -/
theorem Shifted.place_step {gain loss : Nat} {s₁ s₁' s₂ s₂' : Span}
    (h₁ : Shifted gain loss s₁ s₁') (h₂ : Shifted gain loss s₂ s₂') :
    s₂'.place = s₁'.place + (s₂.place - s₁.place) := by
  have a := h₁.first
  have b := h₂.first
  have c := h₁.last
  have d := h₂.last
  have f := h₁.depth
  have g := h₂.depth
  refine IVec.ext ?_ ?_
  · show ((s₂'.first + s₂'.last : Nat) : Int) =
      ((s₁'.first + s₁'.last : Nat) : Int) +
        (((s₂.first + s₂.last : Nat) : Int) - ((s₁.first + s₁.last : Nat) : Int))
    omega
  · show (s₂'.depth : Int) = (s₁'.depth : Int) + ((s₂.depth : Int) - (s₁.depth : Int))
    omega

/-- **Two nodes that shift keep their step at every moment of a step.** Each goes the straight
way from its old place to its new one, and both take one eased progress `e`. Then the second
stands the step of the old picture from the first, at every `e`, in range or not. It is
`Kept.step` of `Whatwg/Svg/Scene/Between.lean` for the two places. So the edges among the nodes
after the edit need no change of shape, and neither do the edges among the nodes before it,
which do not move (`Shifted.refl`). -/
theorem Shifted.moment {gain loss : Nat} {s₁ s₁' s₂ s₂' : Span} (h₁ : Shifted gain loss s₁ s₁')
    (h₂ : Shifted gain loss s₂ s₂') (e : Int) :
    (⟨mix s₂.place.x s₂'.place.x e, mix s₂.place.y s₂'.place.y e⟩ : IVec) =
      ⟨mix s₁.place.x s₁'.place.x e, mix s₁.place.y s₁'.place.y e⟩ + (s₂.place - s₁.place) := by
  have k := Shifted.place_step h₁ h₂
  have k0 : s₂.place = s₁.place + (s₂.place - s₁.place) :=
    ((IVec.add_comm _ _).trans (IVec.sub_add_cancel s₂.place s₁.place)).symm
  generalize s₂.place - s₁.place = d at k k0 ⊢
  rw [k, k0]
  exact IVec.ext (mix_add_right _ _ _ e) (mix_add_right _ _ _ e)

end Span

namespace Tree

variable {α : Type}

/-! ## No interleaving on the way -/

/-- **Two subtrees of one node do not interleave on the way.** In each of two pictures a tree
stands before its later siblings: `p` is a node of the tree and `q` a node of a later sibling in
the first picture, and `p'` and `q'` are such nodes in the second. Each column goes the straight
way. Then the last column of the first node is before the first column of the second at every
eased progress in range. The two pictures may be any two: an edit inside the tree, inside a
later sibling, or elsewhere. So no edge of one subtree crosses an edge of the other during the
step. -/
theorem spansAll_apart_between (depth start depth' start' : Nat) (t t' : Tree α)
    (ts ts' : List (Tree α)) (p q p' q' : α × Span) (hp : p ∈ spans depth start t)
    (hq : q ∈ spansAll depth (start + leaves t) ts) (hp' : p' ∈ spans depth' start' t')
    (hq' : q' ∈ spansAll depth' (start' + leaves t') ts') (e : Int) (h0 : 0 ≤ e)
    (h1 : e ≤ 1000) :
    mix (p.2.last : Int) (p'.2.last : Int) e + 1 ≤ mix (q.2.first : Int) (q'.2.first : Int) e := by
  have a := spansAll_apart depth start t ts p q hp hq
  have a' := spansAll_apart depth' start' t' ts' p' q' hp' hq'
  exact mix_gap _ _ _ _ 1 e h0 h1 (by omega) (by omega)

end Tree

/-! ## Controls and finite evaluations

The tree is a root `0` with three children: a leaf `1`, a node `2` with the two leaves `3` and
`4`, and a leaf `5`. Its picture is six nodes over four columns. Each span is the first column,
the last column and the depth. -/

#guard (Tree.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []]).spans 0 0 =
  [(0, ⟨0, 3, 0⟩), (1, ⟨0, 0, 1⟩), (2, ⟨1, 2, 1⟩), (3, ⟨1, 1, 2⟩), (4, ⟨2, 2, 2⟩), (5, ⟨3, 3, 1⟩)]

-- The middle child is at the address `[1]`. It starts in the column `1` and has two leaves.
#guard Tree.column 0 [1] (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []]) = 1

-- The middle child replaced by a leaf: one leaf where two were. The leaf `1` is before the edit
-- and keeps its span. The root is on the way: its last column goes from `3` to `2`. The leaf
-- `5` is after the edit: it goes from the column `3` to the column `2`.
#guard (Tree.replace (.node 9 []) [1]
    (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).spans 0 0 =
  [(0, ⟨0, 2, 0⟩), (1, ⟨0, 0, 1⟩), (9, ⟨1, 1, 1⟩), (5, ⟨2, 2, 1⟩)]
#guard Span.Edited 1 1 2 ⟨0, 0, 1⟩ ⟨0, 0, 1⟩
#guard Span.Edited 1 1 2 ⟨0, 3, 0⟩ ⟨0, 2, 0⟩ ∧ Span.Stretched 1 2 ⟨0, 3, 0⟩ ⟨0, 2, 0⟩
#guard Span.Edited 1 1 2 ⟨3, 3, 1⟩ ⟨2, 2, 1⟩ ∧ Span.Shifted 1 2 ⟨3, 3, 1⟩ ⟨2, 2, 1⟩

-- The middle child replaced by a node with four leaves: four leaves where two were. The new
-- subtree is drawn from the column `1` at the depth `1`. The root's last column goes from `3`
-- to `5`, and the leaf `5` goes from the column `3` to the column `5`.
#guard (Tree.replace (.node 9 [.node 10 [], .node 11 [], .node 12 [], .node 13 []]) [1]
    (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).spans 0 0 =
  [(0, ⟨0, 5, 0⟩), (1, ⟨0, 0, 1⟩), (9, ⟨1, 4, 1⟩), (10, ⟨1, 1, 2⟩), (11, ⟨2, 2, 2⟩),
    (12, ⟨3, 3, 2⟩), (13, ⟨4, 4, 2⟩), (5, ⟨5, 5, 1⟩)]
#guard (Tree.node 9 [.node 10 [], .node 11 [], .node 12 [], .node 13 []]).spans 1 1 =
  [(9, ⟨1, 4, 1⟩), (10, ⟨1, 1, 2⟩), (11, ⟨2, 2, 2⟩), (12, ⟨3, 3, 2⟩), (13, ⟨4, 4, 2⟩)]
#guard Span.Edited 1 4 2 ⟨0, 3, 0⟩ ⟨0, 5, 0⟩ ∧ Span.Stretched 4 2 ⟨0, 3, 0⟩ ⟨0, 5, 0⟩
#guard Span.Edited 1 4 2 ⟨3, 3, 1⟩ ⟨5, 5, 1⟩ ∧ Span.Shifted 4 2 ⟨3, 3, 1⟩ ⟨5, 5, 1⟩

-- The middle child replaced by itself: the picture is the picture.
#guard (Tree.replace (.node 2 [.node 3 [], .node 4 []]) [1]
    (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).spans 0 0 =
  [(0, ⟨0, 3, 0⟩), (1, ⟨0, 0, 1⟩), (2, ⟨1, 2, 1⟩), (3, ⟨1, 1, 2⟩), (4, ⟨2, 2, 2⟩), (5, ⟨3, 3, 1⟩)]

-- An edit one level down, at the address `[1, 0]`: the leaf `3` replaced by a node with three
-- leaves. Two nodes are on the way, the root and the node `2`, and both are stretched. Two
-- nodes are after the edit, the leaves `4` and `5`, and both are shifted by two columns.
#guard Tree.column 0 [1, 0]
  (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []]) = 1
#guard (Tree.replace (.node 9 [.node 10 [], .node 11 [], .node 12 []]) [1, 0]
    (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).spans 0 0 =
  [(0, ⟨0, 5, 0⟩), (1, ⟨0, 0, 1⟩), (2, ⟨1, 4, 1⟩), (9, ⟨1, 3, 2⟩), (10, ⟨1, 1, 3⟩),
    (11, ⟨2, 2, 3⟩), (12, ⟨3, 3, 3⟩), (4, ⟨4, 4, 2⟩), (5, ⟨5, 5, 1⟩)]
#guard Span.Stretched 3 1 ⟨0, 3, 0⟩ ⟨0, 5, 0⟩ ∧ Span.Stretched 3 1 ⟨1, 2, 1⟩ ⟨1, 4, 1⟩
#guard Span.Shifted 3 1 ⟨2, 2, 2⟩ ⟨4, 4, 2⟩ ∧ Span.Shifted 3 1 ⟨3, 3, 1⟩ ⟨5, 5, 1⟩

-- The two nodes after that edit are one rigid body: the step from the leaf `4` to the leaf `5`
-- is the same in both pictures. A node on the way is not part of it: the step from the root to
-- the leaf `5` changes, so the edge between them changes its shape.
#guard (Span.place ⟨3, 3, 1⟩ - Span.place ⟨2, 2, 2⟩ : IVec) =
  Span.place ⟨5, 5, 1⟩ - Span.place ⟨4, 4, 2⟩
#guard (Span.place ⟨3, 3, 1⟩ - Span.place ⟨0, 3, 0⟩ : IVec) ≠
  Span.place ⟨5, 5, 1⟩ - Span.place ⟨0, 5, 0⟩

-- An address that leads nowhere: the root has no child `7`, and the leaf `1` has no child.
-- The edit changes nothing.
#guard (Tree.subtree? [7]
  (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).isNone
#guard (Tree.subtree? [0, 0]
  (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).isNone
#guard (Tree.replace (.node 9 []) [7]
    (.node 0 [.node 1 [], .node 2 [.node 3 [], .node 4 []], .node 5 []])).spans 0 0 =
  [(0, ⟨0, 3, 0⟩), (1, ⟨0, 0, 1⟩), (2, ⟨1, 2, 1⟩), (3, ⟨1, 1, 2⟩), (4, ⟨2, 2, 2⟩), (5, ⟨3, 3, 1⟩)]

end Whatwg.Svg.Scene
