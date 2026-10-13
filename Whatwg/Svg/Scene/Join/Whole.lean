import Whatwg.Svg.Scene.Join.Laws
import Whatwg.Svg.Scene.Moves

/-!
# Whatwg.Svg.Scene.Join.Whole

Owner: the join by key as a whole (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Join/Laws.lean` says where each thing of a join goes. This module says what a
whole join is in the two cases where a caller knows it without computing it: a picture joined to
itself, and a picture joined after a change that keeps every key.

- `Join.map f j`: the same join of other things. It keeps the order of each selection
  (`Join.map_id`, `Join.map_map`).
- **A picture joined to itself** (`join_self`): with distinct keys, no thing enters, no thing
  exits, and each thing updates to itself, in the order of the picture (`update_self`). So a
  step from a picture to itself is the still picture, and a caller may skip it.
- **A change that keeps keys goes through the join** (`join_map`): where `f` gives two things
  one key exactly when they had one, the join of the changed pictures is the join, changed. The
  keys may be of another type after the change. `join_map_key` is the case where the key of
  `f a` is the key of `a`. So a caller may join first and restyle, scale or relabel afterwards,
  or the other way round, and has one join.
- **A picture moved as one** (`join_move`): where a move keeps the key of a thing, the join of
  two moved pictures is the join, moved.

What this module does not claim. `join_map` asks nothing of the keys of the two lists: it holds
with repeated keys too. `update_self` needs distinct keys, and the control in
`WhatwgTest/Svg/UseJoin.lean` shows a list with a repeated key whose join to itself is not the
list paired with itself.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

variable {α β γ κ κ' : Type}

/-- **The same join of other things**: `f` of each thing that enters, of both things of each
pair, and of each thing that exits, in the same order. -/
def Join.map (f : α → β) (j : Join α) : Join β where
  enter := j.enter.map f
  update := j.update.map fun p => (f p.1, f p.2)
  exit := j.exit.map f

/-- A join is its three selections. -/
theorem Join.ext' {j k : Join α} (h1 : j.enter = k.enter) (h2 : j.update = k.update)
    (h3 : j.exit = k.exit) : j = k := by
  cases j
  cases k
  cases h1
  cases h2
  cases h3
  rfl

theorem Join.map_id (j : Join α) : j.map (fun a => a) = j :=
  Join.ext' (List.map_id' j.enter) (List.map_id' j.update) (List.map_id' j.exit)

theorem Join.map_map (g : β → γ) (f : α → β) (j : Join α) :
    (j.map f).map g = j.map fun a => g (f a) :=
  Join.ext' (List.map_map.trans rfl) (List.map_map.trans rfl) (List.map_map.trans rfl)

/-! ## A picture joined to itself -/

/-- A `filterMap` that answers each member with one value is the map of those values. -/
theorem filterMap_eq_map_of (f : α → Option β) (g : α → β) : ∀ l : List α,
    (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons_some (h a List.mem_cons_self), List.map_cons,
      filterMap_eq_map_of f g l fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- **A list with distinct keys joined to itself updates each thing to itself**, in the order of
the list. -/
theorem update_self [BEq κ] [LawfulBEq κ] (key : α → κ) {l : List α} (hd : Distinct key l) :
    (join key l l).update = l.map fun a => (a, a) :=
  filterMap_eq_map_of _ _ l fun a ha =>
    congrArg (Option.map (·, a)) (find_of_distinct key hd ha rfl)

/-- **A picture joined to itself is the still picture**: with distinct keys, no thing enters,
each thing updates to itself, and no thing exits. -/
theorem join_self [BEq κ] [LawfulBEq κ] (key : α → κ) {l : List α} (hd : Distinct key l) :
    join key l l = ⟨[], l.map fun a => (a, a), []⟩ :=
  Join.ext' (enter_self key l) (update_self key hd) (exit_self key l)

/-! ## A change that keeps keys -/

/-- A filter of a changed list, where the test of `f a` is another test of `a`, is the filter
of the list by that test, changed. -/
theorem filter_map_of (f : α → β) (p : β → Bool) (q : α → Bool) (h : ∀ a, p (f a) = q a) :
    ∀ l : List α, (l.map f).filter p = (l.filter q).map f
  | [] => rfl
  | a :: l => by
    cases hq : q a with
    | true =>
      rw [List.map_cons, List.filter_cons_of_pos ((h a).trans hq), List.filter_cons_of_pos hq,
        List.map_cons, filter_map_of f p q h l]
    | false =>
      have h1 : ¬q a = true := fun e => Bool.false_ne_true (hq.symm.trans e)
      have h2 : ¬p (f a) = true := fun e => h1 ((h a).symm.trans e)
      rw [List.map_cons, List.filter_cons_of_neg h2, List.filter_cons_of_neg h1,
        filter_map_of f p q h l]

/-- A `filterMap` of a changed list, where the answer at `f a` is another answer at `a`,
changed, is the `filterMap` of the list by that answer, changed. -/
theorem filterMap_map_of {γ' : Type} (f : α → β) (g : γ → γ') (p : β → Option γ')
    (q : α → Option γ) (h : ∀ a, p (f a) = (q a).map g) :
    ∀ l : List α, (l.map f).filterMap p = (l.filterMap q).map g
  | [] => rfl
  | a :: l => by
    cases hq : q a with
    | none =>
      have h2 : p (f a) = none := (h a).trans (congrArg (Option.map g) hq)
      rw [List.map_cons, List.filterMap_cons_none h2, List.filterMap_cons_none hq,
        filterMap_map_of f g p q h l]
    | some c =>
      have h2 : p (f a) = some (g c) := (h a).trans (congrArg (Option.map g) hq)
      rw [List.map_cons, List.filterMap_cons_some h2, List.filterMap_cons_some hq, List.map_cons,
        filterMap_map_of f g p q h l]

section

variable [BEq κ] [BEq κ'] (key : α → κ) (key' : β → κ') (f : α → β)
  (hk : ∀ a b, (key' (f a) == key' (f b)) = (key a == key b))

include hk

/-- Whether a changed list has a thing with the key of `f n` is whether the list has one with
the key of `n`. -/
private theorem any_map_of (n : α) : ∀ l : List α,
    ((l.map f).any fun o => key' o == key' (f n)) = l.any fun o => key o == key n
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.any_cons, List.any_cons, hk a n, any_map_of n l]

/-- The search of a changed list for the key of `f n` finds `f` of what the search of the list
for the key of `n` finds. -/
private theorem find_map_of (n : α) : ∀ l : List α,
    (l.map f).find? (fun o => key' o == key' (f n)) = (l.find? fun o => key o == key n).map f
  | [] => rfl
  | a :: l => by
    cases h : key a == key n with
    | true =>
      rw [List.map_cons, List.find?_cons_of_pos (p := fun o => key' o == key' (f n))
        ((hk a n).trans h), List.find?_cons_of_pos (p := fun o => key o == key n) h]
      rfl
    | false =>
      have h1 : ¬(key a == key n) = true := fun e => Bool.false_ne_true (h.symm.trans e)
      have h2 : ¬(key' (f a) == key' (f n)) = true := fun e => h1 ((hk a n).symm.trans e)
      rw [List.map_cons, List.find?_cons_of_neg (p := fun o => key' o == key' (f n)) h2,
        List.find?_cons_of_neg (p := fun o => key o == key n) h1, find_map_of n l]

/-- **A change that keeps keys goes through the join.** Where `f` gives two things one key
exactly when they had one, the join of the two changed lists is the join of the lists, changed:
`f` of each thing that enters, of both things of each pair, and of each thing that exits. -/
theorem join_map (old new : List α) :
    join key' (old.map f) (new.map f) = (join key old new).map f := by
  refine Join.ext' ?_ ?_ ?_
  · exact filter_map_of f (fun n => !((old.map f).any fun o => key' o == key' n))
      (fun n => !(old.any fun o => key o == key n))
      (fun n => congrArg not (any_map_of key key' f hk n old)) new
  · refine filterMap_map_of f (fun p : α × α => (f p.1, f p.2))
      (fun n => ((old.map f).find? fun o => key' o == key' n).map (·, n))
      (fun n => (old.find? fun o => key o == key n).map (·, n)) (fun n => ?_) new
    show ((old.map f).find? fun o => key' o == key' (f n)).map (·, f n) =
      ((old.find? fun o => key o == key n).map (·, n)).map fun p : α × α => (f p.1, f p.2)
    rw [find_map_of key key' f hk n old]
    cases old.find? (fun o => key o == key n) with
    | none => rfl
    | some o => rfl
  · exact filter_map_of f (fun o => !((new.map f).any fun n => key' n == key' o))
      (fun o => !(new.any fun n => key n == key o))
      (fun o => congrArg not (any_map_of key key' f hk o new)) old
end

/-- **A change that leaves each key as it is goes through the join**: the case of `join_map`
where the key of `f a` is the key of `a`. A restyle, a relabel and a scale are such changes. -/
theorem join_map_key [BEq κ] (key : α → κ) (key' : β → κ) (f : α → β)
    (hk : ∀ a, key' (f a) = key a) (old new : List α) :
    join key' (old.map f) (new.map f) = (join key old new).map f :=
  join_map key key' f (fun a b => by rw [hk a, hk b]) old new

/-- **A picture moved as one**: where a move keeps the key of a thing, the join of two moved
pictures is the join, moved. -/
theorem join_move {δ : Type} [Add δ] [Zero δ] [Moves δ α] [BEq κ] (key : α → κ)
    (hk : ∀ (d : δ) (a : α), key (Moves.move d a) = key a) (d : δ) (old new : List α) :
    join key (Moves.move d old) (Moves.move d new) = (join key old new).map (Moves.move d) :=
  join_map_key key key (Moves.move d) (hk d) old new

end Whatwg.Svg.Scene
