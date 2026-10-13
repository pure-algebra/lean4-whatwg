import Whatwg.Svg.Scene.Patch.Laws

/-!
# Whatwg.Svg.Scene.Patch.Order

Owner: the new order of a kept picture, written short (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

A patch of `Whatwg/Svg/Scene/Patch.lean` carries the new order of the keys whole. Between two
frames of a picture most keys stay, and they stay in their order: a few leave and a few are
new. Then the new order is said with the new keys alone, each with the key before it.
lean4-effect4 writes its patches so (`insertsFrom`, `insertAfter` and `inserts_rebuild` of
`tools/Tools/View/Retained.lean`), and a store that keeps its order as a linked list applies
such a row with no search of the rest. Here that coding is written once, for any key.

- `Reorder κ`: `inserts`, the new keys each with the key before it, where the kept keys kept
  their order; or `whole`, the new order, where they did not.
- `Reorder.of old new`: the coding of a new order against an old one. `Reorder.ofBy inOld inNew
  old new` is the same with the two tests given: whether a key was there before, and whether
  it is there now. A program with a table asks its table, as lean4-effect4 does.
- `r.apply stays old`: the order after. `stays` says which keys of the old order are kept: a
  reader of a patch knows them from the drops it has done.
- `Patch.dropped p`: the keys that a patch drops.

What the laws say:

- **The coding gives the new order back** (`Reorder.apply_ofBy`, `Reorder.apply_of`): where the
  new order has no repeat, and `stays` answers the old keys as the test `inNew` does. Nothing
  is asked of the two tests: they choose the form, and both forms give the order back.
- **An order that did not change is coded with nothing** (`Reorder.of_self`).
- **A patch says which keys stay** (`Patch.reorder_coded`): the keys that the patch from one
  kept picture to another does not drop are the old keys with a new thing, so the order coded
  with the new table as its test, applied with them, is the new order. The new order has no
  repeat, and the old table has a thing at each key of the old order.
- The steps: a key put after the last key of a part with no repeat stands right after it
  (`Reorder.insertAfter_mid`), and the new keys of an order, put in turn into the kept keys,
  give the order (`Reorder.rebuild_insertsOf`).

What this module does not claim: that the coding is the shortest; anything of two codings in a
row, which are not one coding by joining their lists, since a key may be new in the first and
gone in the second. `Patch.order` stays the whole order, and `++` of patches is stated of it.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-- **The new order of the keys, coded against the old one.** -/
inductive Reorder (κ : Type) where
  /-- The kept keys kept their order: the new keys, each with the key before it in the new
  order, and none for a key that is first. -/
  | inserts (new : List (κ × Option κ))
  /-- The kept keys changed their order: the new order, whole. -/
  | whole (order : List κ)
  deriving DecidableEq, Repr

namespace Reorder

variable {κ : Type}

/-- The new keys of an order, each with the key before it: `kept` says which keys are not new,
and `prev` is the key before the first of the list. -/
def insertsOf (kept : κ → Bool) : Option κ → List κ → List (κ × Option κ)
  | _, [] => []
  | prev, k :: rest =>
    if kept k = true then insertsOf kept (some k) rest
    else (k, prev) :: insertsOf kept (some k) rest

/-- Two filters that agree at each member agree. -/
theorem filter_congr_mem {p q : κ → Bool} : ∀ {l : List κ},
    (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
    have ih : xs.filter p = xs.filter q :=
      filter_congr_mem fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hq : q x with
    | true =>
      rw [List.filter_cons_of_pos ((h x List.mem_cons_self).trans hq), List.filter_cons_of_pos hq,
        ih]
    | false =>
      have hq' : ¬q x = true := fun e => Bool.false_ne_true (hq.symm.trans e)
      have hp' : ¬p x = true := fun e => hq' ((h x List.mem_cons_self).symm.trans e)
      rw [List.filter_cons_of_neg hp', List.filter_cons_of_neg hq', ih]

/-- A list with no repeat does not have a member twice: the part before a member lacks it. -/
theorem not_mem_of_nodup_append {a : κ} : ∀ {pre rest : List κ},
    (pre ++ a :: rest).Nodup → a ∉ pre
  | [], _, _ => fun h => nomatch h
  | x :: pre, rest, hnd => by
    have h' : x ∉ pre ++ a :: rest ∧ (pre ++ a :: rest).Nodup := List.nodup_cons.mp hnd
    intro hm
    rcases List.mem_cons.mp hm with e | hm'
    · exact h'.1 (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl e.symm))))
    · exact not_mem_of_nodup_append h'.2 hm'

/-- Where every key is kept, no key is new. -/
theorem insertsOf_of_all (kept : κ → Bool) : ∀ (l : List κ) (prev : Option κ),
    (∀ k ∈ l, kept k = true) → insertsOf kept prev l = []
  | [], _, _ => rfl
  | k :: rest, prev, h => by
    have e : insertsOf kept prev (k :: rest) = insertsOf kept (some k) rest :=
      if_pos (h k List.mem_cons_self)
    rw [e]
    exact insertsOf_of_all kept rest (some k) fun j hj => h j (List.mem_cons_of_mem k hj)

variable [DecidableEq κ]

/-- An order with `k` put after the first `prev`. Where the order has no `prev`, `k` is put
last. -/
def putAfter (k prev : κ) : List κ → List κ
  | [] => [k]
  | x :: xs => if x = prev then x :: k :: xs else x :: putAfter k prev xs

/-- An order with `k` put after the first `prev`, or first where there is no `prev`. -/
def insertAfter (k : κ) : Option κ → List κ → List κ
  | none, order => k :: order
  | some prev, order => putAfter k prev order

/-- An order with each new key put at its place, in turn. -/
def rebuild (ins : List (κ × Option κ)) (base : List κ) : List κ :=
  ins.foldl (fun o x => insertAfter x.1 x.2 o) base

/-- **The coding of a new order against an old one, with the two tests given.** `inOld` says
whether a key was there before, and `inNew` whether it is there now. Where the keys of both are
in one order in both, the new keys with their places. Otherwise the new order, whole. -/
def ofBy (inOld inNew : κ → Bool) (old new : List κ) : Reorder κ :=
  if new.filter inOld = old.filter inNew then .inserts (insertsOf inOld none new)
  else .whole new

/-- **The coding of a new order against an old one**, the two tests read from the two lists. -/
def of (old new : List κ) : Reorder κ :=
  ofBy (fun k => decide (k ∈ old)) (fun k => decide (k ∈ new)) old new

/-- **The order after.** `stays` says which keys of the old order are kept. -/
def apply : Reorder κ → (κ → Bool) → List κ → List κ
  | .inserts ins, stays, old => rebuild ins (old.filter stays)
  | .whole order, _, _ => order

/-- **A key put after the last key of a part with no repeat stands right after it.** -/
theorem insertAfter_mid (k last : κ) (rest : List κ) : ∀ pre : List κ, last ∉ pre →
    insertAfter k (some last) (pre ++ last :: rest) = pre ++ last :: k :: rest
  | [], _ => by
    show (if last = last then last :: k :: rest else last :: putAfter k last rest) =
      last :: k :: rest
    exact if_pos rfl
  | x :: xs, h => by
    have hx : ¬x = last := fun e => h (List.mem_cons.mpr (Or.inl e.symm))
    have ih : putAfter k last (xs ++ last :: rest) = xs ++ last :: k :: rest :=
      insertAfter_mid k last rest xs fun hm => h (List.mem_cons_of_mem x hm)
    show (if x = last then x :: k :: (xs ++ last :: rest)
      else x :: putAfter k last (xs ++ last :: rest)) = x :: (xs ++ last :: k :: rest)
    rw [if_neg hx, ih]

/-- **The new keys of an order, put in turn into its kept keys, give the order**, after a part
that ends at `last`. -/
theorem rebuild_insertsOf (kept : κ → Bool) : ∀ (rest pre : List κ) (last : κ),
    (pre ++ last :: rest).Nodup →
    rebuild (insertsOf kept (some last) rest) (pre ++ last :: rest.filter kept) =
      pre ++ last :: rest
  | [], _, _, _ => rfl
  | x :: rest, pre, last, hnd => by
    have hlast : last ∉ pre := not_mem_of_nodup_append hnd
    have hnd' : ((pre ++ [last]) ++ x :: rest).Nodup := by
      rw [List.append_assoc]
      exact hnd
    have ih := rebuild_insertsOf kept rest (pre ++ [last]) x hnd'
    rw [List.append_assoc, List.append_assoc] at ih
    cases hk : kept x with
    | true =>
      have e1 : insertsOf kept (some last) (x :: rest) = insertsOf kept (some x) rest := if_pos hk
      rw [e1, List.filter_cons_of_pos hk]
      exact ih
    | false =>
      have hk' : ¬kept x = true := fun e => Bool.false_ne_true (hk.symm.trans e)
      have e1 : insertsOf kept (some last) (x :: rest) =
          (x, some last) :: insertsOf kept (some x) rest := if_neg hk'
      rw [e1, List.filter_cons_of_neg hk']
      show rebuild (insertsOf kept (some x) rest)
        (insertAfter x (some last) (pre ++ last :: rest.filter kept)) = pre ++ last :: x :: rest
      rw [insertAfter_mid x last (rest.filter kept) pre hlast]
      exact ih

/-- The same from the first key of an order with no repeat. -/
theorem rebuild_insertsOf_none (kept : κ → Bool) : ∀ new : List κ, new.Nodup →
    rebuild (insertsOf kept none new) (new.filter kept) = new
  | [], _ => rfl
  | x :: rest, hnd => by
    have ih : rebuild (insertsOf kept (some x) rest) (x :: rest.filter kept) = x :: rest :=
      rebuild_insertsOf kept rest [] x hnd
    cases hk : kept x with
    | true =>
      have e1 : insertsOf kept none (x :: rest) = insertsOf kept (some x) rest := if_pos hk
      rw [e1, List.filter_cons_of_pos hk]
      exact ih
    | false =>
      have hk' : ¬kept x = true := fun e => Bool.false_ne_true (hk.symm.trans e)
      have e1 : insertsOf kept none (x :: rest) = (x, none) :: insertsOf kept (some x) rest :=
        if_neg hk'
      rw [e1, List.filter_cons_of_neg hk']
      show rebuild (insertsOf kept (some x) rest) (insertAfter x none (rest.filter kept)) =
        x :: rest
      exact ih

/-- **The coding gives the new order back**, whatever the two tests are. The new order has no
repeat, and `stays` answers each key of the old order as `inNew` does. The tests choose
between the two forms, and each form gives the order back. -/
theorem apply_ofBy {old new : List κ} (inOld : κ → Bool) {inNew stays : κ → Bool}
    (hn : new.Nodup) (hs : ∀ k ∈ old, stays k = inNew k) :
    (ofBy inOld inNew old new).apply stays old = new := by
  unfold ofBy
  by_cases h : new.filter inOld = old.filter inNew
  · rw [if_pos h]
    show rebuild (insertsOf inOld none new) (old.filter stays) = new
    rw [filter_congr_mem hs, ← h]
    exact rebuild_insertsOf_none inOld new hn
  · rw [if_neg h]
    rfl

/-- **The coding gives the new order back.** The new order has no repeat, and `stays` is true
of exactly the keys of the old order that the new order has. -/
theorem apply_of {old new : List κ} (hn : new.Nodup) {stays : κ → Bool}
    (hs : ∀ k ∈ old, stays k = decide (k ∈ new)) : (of old new).apply stays old = new :=
  apply_ofBy _ hn hs

/-- **An order that did not change is coded with nothing.** -/
theorem of_self (l : List κ) : of l l = .inserts [] := by
  unfold of ofBy
  rw [if_pos rfl, insertsOf_of_all _ l none fun k hk => decide_eq_true hk]

end Reorder

namespace Patch

variable {σ τ κ α δ : Type}

/-- The key that an operation drops, where it is a drop. -/
def Op.dropped? : Op κ α δ → Option κ
  | .drop k => some k
  | .put _ _ => none
  | .move _ _ => none

/-- **The keys that a patch drops**, in the order of its operations. -/
def dropped (p : Patch κ α δ) : List κ := p.ops.filterMap Op.dropped?

/-- A patch drops a key exactly when it has a `drop` of it. -/
theorem mem_dropped {p : Patch κ α δ} {k : κ} : k ∈ p.dropped ↔ Op.drop k ∈ p.ops := by
  constructor
  · intro h
    obtain ⟨op, hop, e⟩ := List.mem_filterMap.mp h
    cases op with
    | drop j =>
      have hj : j = k := Option.some.inj e
      rw [← hj]
      exact hop
    | put j a => exact nomatch e
    | move j d => exact nomatch e
  · intro h
    exact List.mem_filterMap.mpr ⟨.drop k, h, rfl⟩

section

variable [DecidableEq κ] [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α] [DecidableEq α]
  [Store σ κ α] [Store τ κ α]

/-- **The patch from one kept picture to another drops a key** exactly when the old order names
it, the old table has a thing at it and the new table has none. -/
theorem drop_mem_of (old : σ) (oldOrder : List κ) (new : τ) (newOrder : List κ) (k : κ) :
    Op.drop k ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops ↔
      k ∈ oldOrder ∧ (∃ b, Store.get? old k = some b) ∧ Store.get? new k = none := by
  rw [of_ops]
  constructor
  · intro h
    rcases List.mem_append.mp h with h1 | h1
    · obtain ⟨j, _, e⟩ := List.mem_filterMap.mp h1
      exact absurd e (Op.change_ne_drop j k _ _)
    · obtain ⟨j, hj, e⟩ := List.mem_filterMap.mp h1
      obtain ⟨e1, e2, e3⟩ := Op.leave_some e
      have hjk : k = j := Op.drop.inj e1
      rw [hjk]
      exact ⟨hj, e2, e3⟩
  · intro ⟨hk, ⟨b, hb⟩, hn⟩
    refine List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr ⟨k, hk, ?_⟩))
    rw [hb, hn]
    rfl

/-- **A patch says which keys stay.** The keys of the old order that the patch from one kept
picture to another does not drop are the keys with a new thing. So the new order, coded with
the new table as the test of what is there now, and applied with the keys that the patch does
not drop, is the new order: a reader of a patch needs the new keys with their places, and no
more. `inOld` may be any test. The new order has no repeat, and the old table has a thing at
each key of the old order. -/
theorem reorder_coded (old : σ) {oldOrder : List κ} (new : τ) {newOrder : List κ}
    (inOld : κ → Bool) (hn : newOrder.Nodup)
    (hold : ∀ k ∈ oldOrder, ∃ b, Store.get? old k = some b) :
    (Reorder.ofBy inOld (fun k => (Store.get? new k).isSome) oldOrder newOrder).apply
        (fun k => !decide (k ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).dropped))
        oldOrder = newOrder :=
  Reorder.apply_ofBy inOld hn fun k hk => by
    obtain ⟨b, hb⟩ := hold k hk
    show (!decide (k ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).dropped)) =
      (Store.get? new k).isSome
    cases ha : Store.get? new k with
    | some a =>
      have hnd : k ∉ (Patch.of old oldOrder new newOrder : Patch κ α δ).dropped := fun hd => by
        have h3 := ((drop_mem_of old oldOrder new newOrder k).mp (mem_dropped.mp hd)).2.2
        rw [ha] at h3
        exact nomatch h3
      exact congrArg not (decide_eq_false hnd)
    | none =>
      have hd : k ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).dropped :=
        mem_dropped.mpr ((drop_mem_of old oldOrder new newOrder k).mpr ⟨hk, ⟨b, hb⟩, ha⟩)
      exact congrArg not (decide_eq_true hd)
end

end Patch

end Whatwg.Svg.Scene
