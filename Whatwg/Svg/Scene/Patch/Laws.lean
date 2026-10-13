import Whatwg.Svg.Scene.Patch
import Whatwg.Svg.Scene.Join.Laws

/-!
# Whatwg.Svg.Scene.Patch.Laws

Owner: the laws of a patch (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A patch of `Whatwg/Svg/Scene/Patch.lean` is a list of things to do to a kept picture. These
laws say that doing them gives the next picture, that nothing is done where nothing changed,
and that two patches in a row are one.

- **Every table does what the plain one does** (`Patch.get?_applyTo`): a lookup after the
  operations on a table is the operations on its lookup. So each law below is proved of
  lookups, and holds of every table. Two tables that answer alike answer alike after a patch
  (`Patch.applyTo_congr`).
- **The patch gives the next picture.** After the patch from one kept picture to another, the
  table answers at every key as the new one does (`Patch.get?_applyTo_of`), where the new order
  has no repeat and each table has a thing only at keys of its order. A key of the new order
  with a new thing needs the first premise only (`Patch.get?_applyTo_of_mem`). The order after
  the patch is the new order (`Patch.reorder_of`), and the things drawn are the new things
  (`Patch.things_of`).
- **Nothing is done where nothing changed.** A key that both tables answer alike is in no
  operation (`Patch.of_kept`). The patch from a kept picture to itself is the empty patch, with
  no premise (`Patch.of_self`).
- **A thing that moved is moved.** Where the new thing at a key is the old one moved, and is
  not the old one, the patch has a `move` of that key that gives the new thing
  (`Patch.of_moved`) and no `put` of it (`Patch.of_moved_no_put`).
- **Two patches in a row are one.** `++` is associative with `Patch.empty` on both sides
  (`Patch.append_assoc`, `Patch.empty_append`, `Patch.append_empty`), and it is doing the first
  and then the second (`Patch.applyTo_append`, `Patch.reorder_append`).
- **Pictures that are lists.** With distinct keys in the new picture, the patch applied to the
  old picture is the new picture (`apply_diff`), and two patches in a row take the first
  picture to the third (`apply_append_diff`). The patch of a picture to itself is empty
  (`diff_self`). In the words of the join: a key is dropped exactly when a thing with it exits
  (`drop_mem_diff`), and a thing that enters is put (`put_mem_diff`).

What this module does not claim. No law bounds the size of a patch beyond the two above: a
thing that changed is put whole. `Patch.get?_applyTo_of` is of lookups, so two tables with the
same answers are not said to be one table. Nothing here is about a table whose new order
repeats a key: the control in `WhatwgTest/Svg/UsePatch.lean` shows a `move` done twice.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## Tables -/

namespace Store

variable {σ τ κ α : Type} [DecidableEq κ] [Store σ κ α] [Store τ κ α]

/-- A lookup at the inserted key answers the inserted thing. -/
theorem get?_insert_self (s : σ) (k : κ) (v : α) : get? (insert s k v) k = some v :=
  (get?_insert s k k v).trans (if_pos rfl)

/-- A lookup at another key answers as before the insert. -/
theorem get?_insert_of_ne (s : σ) {k j : κ} (h : k ≠ j) (v : α) :
    get? (insert s k v) j = get? s j :=
  (get?_insert s k j v).trans (if_neg h)

/-- A lookup at the erased key answers nothing. -/
theorem get?_erase_self (s : σ) (k : κ) : get? (erase s k) k = none :=
  (get?_erase s k k).trans (if_pos rfl)

/-- A lookup at another key answers as before the erase. -/
theorem get?_erase_of_ne (s : σ) {k j : κ} (h : k ≠ j) : get? (erase s k) j = get? s j :=
  (get?_erase s k j).trans (if_neg h)

/-- **Two tables that answer alike at each key of an order have the same things in it.** The
tables may be of two kinds. -/
theorem things_congr {s : σ} {t : τ} : ∀ {order : List κ},
    (∀ k ∈ order, get? s k = get? t k) → things s order = things t order
  | [], _ => rfl
  | k :: rest, h => by
    have ih : rest.filterMap (get? s) = rest.filterMap (get? t) :=
      things_congr fun j hj => h j (List.mem_cons_of_mem k hj)
    show (k :: rest).filterMap (get? s) = (k :: rest).filterMap (get? t)
    rw [List.filterMap_cons, List.filterMap_cons, h k List.mem_cons_self, ih]

end Store

namespace Patch

/-! ## Two patches in a row are one -/

section

variable {κ α δ : Type}

/-- A patch is its operations and its order. -/
theorem ext' {p q : Patch κ α δ} (h1 : p.ops = q.ops) (h2 : p.order = q.order) : p = q := by
  cases p
  cases q
  cases h1
  cases h2
  rfl

theorem append_ops (p q : Patch κ α δ) : (p ++ q).ops = p.ops ++ q.ops := rfl

theorem append_order (p q : Patch κ α δ) : (p ++ q).order = q.order.or p.order := rfl

/-- **The order after two patches in a row** is the order after the second, of the order after
the first. -/
theorem reorder_append (p q : Patch κ α δ) (order : List κ) :
    (p ++ q).reorder order = q.reorder (p.reorder order) := by
  show (q.order.or p.order).getD order = q.order.getD (p.order.getD order)
  cases q.order with
  | none => rfl
  | some o => rfl

theorem reorder_empty (order : List κ) : (Patch.empty : Patch κ α δ).reorder order = order := rfl

/-- The empty patch first changes nothing. -/
theorem empty_append (p : Patch κ α δ) : Patch.empty ++ p = p := by
  refine ext' rfl ?_
  show p.order.or none = p.order
  cases p.order with
  | none => rfl
  | some o => rfl

/-- The empty patch afterwards changes nothing. -/
theorem append_empty (p : Patch κ α δ) : p ++ Patch.empty = p :=
  ext' (List.append_nil p.ops) rfl

/-- **Patches in a row may be grouped in either way.** -/
theorem append_assoc (p q r : Patch κ α δ) : p ++ q ++ r = p ++ (q ++ r) := by
  refine ext' (List.append_assoc p.ops q.ops r.ops) ?_
  show r.order.or (q.order.or p.order) = (r.order.or q.order).or p.order
  cases r.order with
  | none => rfl
  | some o => rfl

/-- A thing that leaves is dropped: the key had a thing, and has none now. -/
theorem Op.leave_some {k : κ} {o n : Option α} {op : Op κ α δ} (h : Op.leave k o n = some op) :
    op = .drop k ∧ (∃ b, o = some b) ∧ n = none := by
  cases o with
  | none => exact nomatch h
  | some b =>
    cases n with
    | none => exact ⟨(Option.some.inj h).symm, ⟨b, rfl⟩, rfl⟩
    | some a => exact nomatch h

end

/-! ## What a key needs -/

section

variable {κ α δ : Type} [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α]

/-- The operation from an old thing to a new one is about its key. -/
theorem Op.step_key (k : κ) (b a : α) : (Op.step k b a : Op κ α δ).key = k := by
  unfold Op.step
  cases MovedBy.amount b a with
  | none => rfl
  | some d => rfl

/-- **The operation from an old thing to a new one gives the new one.** -/
theorem Op.step_at (k : κ) (b a : α) : (Op.step k b a : Op κ α δ).at (some b) = some a := by
  unfold Op.step
  cases h : MovedBy.amount b a with
  | none => rfl
  | some d => exact congrArg some (MovedBy.amount_sound h)

/-- The operation from an old thing to a new one is never a drop. -/
theorem Op.step_ne_drop (k j : κ) (b a : α) : (Op.step k b a : Op κ α δ) ≠ .drop j := by
  unfold Op.step
  cases MovedBy.amount b a with
  | none => exact fun h => nomatch h
  | some d => exact fun h => nomatch h

variable [DecidableEq α]

/-- What a key needs is about that key. -/
theorem Op.change_key {k : κ} {o n : Option α} {op : Op κ α δ} (h : Op.change k o n = some op) :
    op.key = k := by
  cases n with
  | none =>
    cases o with
    | none => exact nomatch h
    | some b => exact nomatch h
  | some a =>
    cases o with
    | none =>
      have e : Op.put k a = op := Option.some.inj h
      rw [← e]
      rfl
    | some b =>
      have h' : (if a = b then none else some (Op.step k b a)) = some op := h
      by_cases e : a = b
      · rw [if_pos e] at h'
        exact nomatch h'
      · rw [if_neg e] at h'
        rw [← Option.some.inj h']
        exact Op.step_key k b a

/-- What a key needs is never a drop. -/
theorem Op.change_ne_drop (k j : κ) (o n : Option α) :
    (Op.change k o n : Option (Op κ α δ)) ≠ some (.drop j) := by
  intro h
  cases n with
  | none =>
    cases o with
    | none => exact nomatch h
    | some b => exact nomatch h
  | some a =>
    cases o with
    | none =>
      have e : (Op.put k a : Op κ α δ) = .drop j := Option.some.inj h
      exact nomatch e
    | some b =>
      have h' : (if a = b then none else some (Op.step k b a)) = some (Op.drop j) := h
      by_cases e : a = b
      · rw [if_pos e] at h'
        exact nomatch h'
      · rw [if_neg e] at h'
        exact Op.step_ne_drop k j b a (Option.some.inj h')

/-- A key with no new thing needs nothing here: its drop is `Op.leave`. -/
theorem Op.change_none (k : κ) (o : Option α) : (Op.change k o none : Option (Op κ α δ)) = none := by
  cases o with
  | none => rfl
  | some b => rfl

/-- A key whose thing is the same needs nothing. -/
theorem Op.change_same (k : κ) (o : Option α) : (Op.change k o o : Option (Op κ α δ)) = none := by
  cases o with
  | none => rfl
  | some a =>
    show (if a = a then none else some (Op.step k a a)) = none
    exact if_pos rfl

/-- **What a key needs gives its new thing**: done to the old thing, or with nothing done where
nothing is needed, the key has the new thing. -/
theorem Op.change_at (k : κ) (o : Option α) (a : α) :
    (((Op.change k o (some a) : Option (Op κ α δ))).map fun op => op.at o).getD o = some a := by
  cases o with
  | none => rfl
  | some b =>
    show (((if a = b then none else some (Op.step k b a) : Option (Op κ α δ))).map
      fun op => op.at (some b)).getD (some b) = some a
    by_cases e : a = b
    · rw [if_pos e]
      exact congrArg some e.symm
    · rw [if_neg e]
      exact Op.step_at k b a

end

section

variable {σ τ κ α δ : Type} [DecidableEq κ] [Add δ] [Zero δ] [Moves δ α] [Store σ κ α]
  [Store τ κ α]

/-! ## Every table does what the plain one does -/

/-- A lookup after one operation on a table is the operation on the lookup. -/
theorem Op.get?_apply (s : σ) (op : Op κ α δ) :
    Store.get? (op.apply s) = op.apply (Store.get? s) := by
  funext j
  cases op with
  | put k a => exact Store.get?_insert s k j a
  | move k d =>
    show Store.get? ((Store.get? s k).elim s fun a => Store.insert s k (Moves.move d a)) j =
      ((Store.get? s k).elim (Store.get? s) fun a =>
        Store.insert (Store.get? s) k (Moves.move d a)) j
    cases Store.get? s k with
    | none => rfl
    | some a => exact Store.get?_insert s k j (Moves.move d a)
  | drop k => exact Store.get?_erase s k j

/-- A lookup after a list of operations on a table is the operations on the lookup. -/
theorem Op.get?_foldl : ∀ (ops : List (Op κ α δ)) (s : σ),
    Store.get? (ops.foldl Op.apply s) = ops.foldl Op.apply (Store.get? s)
  | [], _ => rfl
  | op :: ops, s => by
    rw [List.foldl_cons, List.foldl_cons, Op.get?_foldl ops (op.apply s), Op.get?_apply]

/-- **A lookup after a patch on a table is the patch on its lookup.** A table of any kind does
what the plain table does, so a law of patches is proved once, of lookups. -/
theorem get?_applyTo (p : Patch κ α δ) (s : σ) :
    Store.get? (p.applyTo s) = p.applyTo (Store.get? s) :=
  Op.get?_foldl p.ops s

/-- **Two tables that answer alike answer alike after a patch.** The tables may be of two
kinds: a patch made for one store is good for every store with the same answers. -/
theorem applyTo_congr (p : Patch κ α δ) {s : σ} {t : τ} (h : Store.get? s = Store.get? t) :
    Store.get? (p.applyTo s) = Store.get? (p.applyTo t) := by
  rw [get?_applyTo, get?_applyTo, h]

/-! ## One operation on a lookup -/

/-- At its key an operation makes what `Op.at` says. -/
theorem Op.apply_self (f : κ → Option α) (op : Op κ α δ) :
    op.apply f op.key = op.at (f op.key) := by
  cases op with
  | put k a =>
    show (if k = k then some a else f k) = some a
    exact if_pos rfl
  | move k d =>
    show ((f k).elim f fun a => Store.insert f k (Moves.move d a)) k = (f k).map (Moves.move d)
    cases h : f k with
    | none => exact h
    | some a =>
      show (if k = k then some (Moves.move d a) else f k) = some (Moves.move d a)
      exact if_pos rfl
  | drop k =>
    show (if k = k then none else f k) = none
    exact if_pos rfl

/-- At every other key an operation changes nothing. -/
theorem Op.apply_of_ne (f : κ → Option α) (op : Op κ α δ) {j : κ} (h : op.key ≠ j) :
    op.apply f j = f j := by
  cases op with
  | put k a =>
    show (if k = j then some a else f j) = f j
    exact if_neg h
  | move k d =>
    show ((f k).elim f fun a => Store.insert f k (Moves.move d a)) j = f j
    cases f k with
    | none => rfl
    | some a =>
      show (if k = j then some (Moves.move d a) else f j) = f j
      exact if_neg h
  | drop k =>
    show (if k = j then none else f j) = f j
    exact if_neg h

/-- Operations on other keys leave the thing at a key. -/
theorem Op.foldl_of_ne (j : κ) : ∀ (ops : List (Op κ α δ)) (f : κ → Option α),
    (∀ op ∈ ops, op.key ≠ j) → ops.foldl Op.apply f j = f j
  | [], _, _ => rfl
  | op :: ops, f, h => by
    rw [List.foldl_cons,
      Op.foldl_of_ne j ops (op.apply f) fun o ho => h o (List.mem_cons_of_mem op ho)]
    exact Op.apply_of_ne f op (h op List.mem_cons_self)

/-- Where every operation on a key is a drop, a key with nothing keeps nothing. -/
theorem Op.foldl_none (k : κ) : ∀ (ops : List (Op κ α δ)) (f : κ → Option α),
    (∀ op ∈ ops, op.key = k → op = .drop k) → f k = none → ops.foldl Op.apply f k = none
  | [], _, _, h => h
  | op :: ops, f, hd, h => by
    rw [List.foldl_cons]
    refine Op.foldl_none k ops (op.apply f) (fun o ho => hd o (List.mem_cons_of_mem op ho)) ?_
    by_cases e : op.key = k
    · rw [hd op List.mem_cons_self e]
      show (if k = k then none else f k) = none
      exact if_pos rfl
    · rw [Op.apply_of_ne f op e]
      exact h

/-- Where every operation on a key is a drop and there is one, the key ends with nothing. -/
theorem Op.foldl_dropped (k : κ) : ∀ (ops : List (Op κ α δ)) (f : κ → Option α),
    (∀ op ∈ ops, op.key = k → op = .drop k) → (∃ op ∈ ops, op.key = k) →
    ops.foldl Op.apply f k = none
  | [], _, _, ⟨_, h, _⟩ => nomatch h
  | op :: ops, f, hd, hex => by
    rw [List.foldl_cons]
    by_cases e : op.key = k
    · refine Op.foldl_none k ops _ (fun o ho => hd o (List.mem_cons_of_mem op ho)) ?_
      rw [hd op List.mem_cons_self e]
      show (if k = k then none else f k) = none
      exact if_pos rfl
    · obtain ⟨o, ho, hk⟩ := hex
      have ho' : o ∈ ops := (List.mem_cons.mp ho).resolve_left fun eo => e (eo ▸ hk)
      exact Op.foldl_dropped k ops _ (fun o ho => hd o (List.mem_cons_of_mem op ho))
        ⟨o, ho', hk⟩

section

variable (g : κ → Option (Op κ α δ)) (hg : ∀ j op, g j = some op → op.key = j)

include hg

/-- One operation for each key of a list: a key outside the list is left as it is. -/
theorem Op.foldl_filterMap_of_not_mem {k : κ} (l : List κ) (f : κ → Option α) (hk : k ∉ l) :
    (l.filterMap g).foldl Op.apply f k = f k :=
  Op.foldl_of_ne k _ f fun op hop he => by
    obtain ⟨j, hj, e⟩ := List.mem_filterMap.mp hop
    have hjk : j = k := (hg j op e).symm.trans he
    exact hk (hjk ▸ hj)

/-- **One operation for each key of a list with no repeat acts alone at its key.** The thing at
a key of the list is what that key's operation makes of the thing before, or the thing before
where the key has no operation. -/
theorem Op.foldl_filterMap_of_mem {k : κ} : ∀ (l : List κ) (f : κ → Option α), l.Nodup → k ∈ l →
    (l.filterMap g).foldl Op.apply f k = ((g k).map fun op => op.at (f k)).getD (f k)
  | [], _, _, h => nomatch h
  | x :: xs, f, hn, h => by
    have hn' : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hn
    by_cases hx : x = k
    · subst hx
      cases hgx : g x with
      | none =>
        have e := Op.foldl_filterMap_of_not_mem g hg xs f hn'.1
        rw [List.filterMap_cons_none hgx]
        exact e
      | some op =>
        have e := Op.apply_self f op
        rw [hg x op hgx] at e
        rw [List.filterMap_cons_some hgx, List.foldl_cons,
          Op.foldl_filterMap_of_not_mem g hg xs _ hn'.1]
        exact e
    · have hk : k ∈ xs := (List.mem_cons.mp h).resolve_left fun e => hx e.symm
      cases hgx : g x with
      | none =>
        rw [List.filterMap_cons_none hgx]
        exact Op.foldl_filterMap_of_mem xs f hn'.2 hk
      | some op =>
        have hne : op.key ≠ k := fun e => hx ((hg x op hgx).symm.trans e)
        have e := Op.foldl_filterMap_of_mem xs (op.apply f) hn'.2 hk
        rw [Op.apply_of_ne f op hne] at e
        rw [List.filterMap_cons_some hgx, List.foldl_cons]
        exact e

end

/-! ## The patch gives the next picture -/

section

variable [MovedBy δ α] [DecidableEq α]

/-- The operations of the patch from one kept picture to another. -/
theorem of_ops (old : σ) (oldOrder : List κ) (new : τ) (newOrder : List κ) :
    (Patch.of old oldOrder new newOrder : Patch κ α δ).ops =
      newOrder.filterMap (fun k => Op.change k (Store.get? old k) (Store.get? new k)) ++
        oldOrder.filterMap fun k => Op.leave k (Store.get? old k) (Store.get? new k) := rfl

/-- An operation of the patch on a key is what that key needs, or its drop. -/
theorem of_mem {old : σ} {oldOrder : List κ} {new : τ} {newOrder : List κ} {op : Op κ α δ}
    (h : op ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops) :
    Op.change op.key (Store.get? old op.key) (Store.get? new op.key) = some op ∨
      Op.leave op.key (Store.get? old op.key) (Store.get? new op.key) = some op := by
  rw [of_ops] at h
  rcases List.mem_append.mp h with h1 | h1
  · obtain ⟨j, _, e⟩ := List.mem_filterMap.mp h1
    have hj : op.key = j := Op.change_key e
    rw [hj]
    exact Or.inl e
  · obtain ⟨j, _, e⟩ := List.mem_filterMap.mp h1
    have hj : op.key = j := by
      rw [(Op.leave_some e).1]
      rfl
    rw [hj]
    exact Or.inr e

/-- **A key of the new order with a new thing has it after the patch.** The new order has no
repeat. Nothing is asked of the old picture. -/
theorem get?_applyTo_of_mem (old : σ) (oldOrder : List κ) (new : τ) {newOrder : List κ}
    (hn : newOrder.Nodup) {k : κ} (hk : k ∈ newOrder) {a : α} (ha : Store.get? new k = some a) :
    Store.get? ((Patch.of old oldOrder new newOrder : Patch κ α δ).applyTo old) k = some a := by
  have hdrops : ∀ op ∈ oldOrder.filterMap (fun j =>
      (Op.leave j (Store.get? old j) (Store.get? new j) : Option (Op κ α δ))), op.key ≠ k := by
    intro op hop he
    obtain ⟨j, _, e⟩ := List.mem_filterMap.mp hop
    obtain ⟨e1, _, e3⟩ := Op.leave_some e
    rw [e1] at he
    have hj : j = k := he
    rw [hj, ha] at e3
    exact nomatch e3
  have hchange := Op.foldl_filterMap_of_mem (δ := δ)
    (fun j => Op.change j (Store.get? old j) (Store.get? new j)) (fun _ _ e => Op.change_key e)
    newOrder (Store.get? old) hn hk
  have hat := Op.change_at (δ := δ) k (Store.get? old k) a
  rw [← ha] at hat
  rw [get?_applyTo]
  show ((newOrder.filterMap fun j => Op.change j (Store.get? old j) (Store.get? new j)) ++
    oldOrder.filterMap fun j => Op.leave j (Store.get? old j) (Store.get? new j)).foldl
      Op.apply (Store.get? old) k = some a
  rw [List.foldl_append, Op.foldl_of_ne k _ _ hdrops, hchange]
  exact hat.trans ha

/-- **A key with no new thing has nothing after the patch**, where the old order names it or
the old table has nothing at it. -/
theorem get?_applyTo_of_none (old : σ) {oldOrder : List κ} (new : τ) (newOrder : List κ) {k : κ}
    (hk : Store.get? new k = none) (ho : k ∈ oldOrder ∨ Store.get? old k = none) :
    Store.get? ((Patch.of old oldOrder new newOrder : Patch κ α δ).applyTo old) k = none := by
  have hdrop : ∀ op ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops, op.key = k →
      op = .drop k := by
    intro op hop he
    rcases of_mem hop with h1 | h1
    · rw [he, hk, Op.change_none] at h1
      exact nomatch h1
    · rw [he] at h1
      exact (Op.leave_some h1).1
  rw [get?_applyTo]
  cases hb : Store.get? old k with
  | none =>
    refine (Op.foldl_of_ne k _ _ fun op hop he => ?_).trans hb
    have e := hdrop op hop he
    rcases of_mem hop with h1 | h1
    · rw [e] at h1
      exact Op.change_ne_drop k k _ _ h1
    · rw [he, hb] at h1
      exact nomatch h1
  | some b =>
    have hmem : k ∈ oldOrder := ho.resolve_right fun e => nomatch hb.symm.trans e
    refine Op.foldl_dropped k _ _ hdrop ⟨.drop k, ?_, rfl⟩
    rw [of_ops]
    refine List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr ⟨k, hmem, ?_⟩))
    rw [hb, hk]
    rfl

/-- **The patch gives the next picture**: after it the table answers at every key as the new
one does. The new order has no repeat, and each table has a thing only at keys of its order. -/
theorem get?_applyTo_of (old : σ) {oldOrder : List κ} (new : τ) {newOrder : List κ}
    (hn : newOrder.Nodup) (hold : ∀ k b, Store.get? old k = some b → k ∈ oldOrder)
    (hnew : ∀ k a, Store.get? new k = some a → k ∈ newOrder) (k : κ) :
    Store.get? ((Patch.of old oldOrder new newOrder : Patch κ α δ).applyTo old) k =
      Store.get? new k := by
  cases ha : Store.get? new k with
  | some a => exact get?_applyTo_of_mem old oldOrder new hn (hnew k a ha) ha
  | none =>
    refine get?_applyTo_of_none old new newOrder ha ?_
    cases hb : Store.get? old k with
    | none => exact Or.inr rfl
    | some b => exact Or.inl (hold k b hb)

/-- **The order after the patch is the new order.** -/
theorem reorder_of (old : σ) (oldOrder : List κ) (new : τ) (newOrder : List κ) :
    (Patch.of old oldOrder new newOrder : Patch κ α δ).reorder oldOrder = newOrder := by
  show (if newOrder = oldOrder then none else some newOrder).getD oldOrder = newOrder
  by_cases e : newOrder = oldOrder
  · rw [if_pos e]
    exact e.symm
  · rw [if_neg e]
    rfl

/-- **The things drawn after the patch are the new things.** The new order has no repeat, and
each of its keys has a thing. Nothing is asked of the old picture. -/
theorem things_of (old : σ) (oldOrder : List κ) (new : τ) {newOrder : List κ}
    (hn : newOrder.Nodup) (hall : ∀ k ∈ newOrder, ∃ a, Store.get? new k = some a) :
    Store.things ((Patch.of old oldOrder new newOrder : Patch κ α δ).applyTo old)
        ((Patch.of old oldOrder new newOrder : Patch κ α δ).reorder oldOrder) =
      Store.things new newOrder := by
  rw [reorder_of]
  refine Store.things_congr fun k hk => ?_
  obtain ⟨a, ha⟩ := hall k hk
  rw [ha]
  exact get?_applyTo_of_mem old oldOrder new hn hk ha

/-! ## Nothing is done where nothing changed -/

/-- **A key that both tables answer alike is in no operation.** -/
theorem of_kept {old : σ} {oldOrder : List κ} {new : τ} {newOrder : List κ} {k : κ}
    (h : Store.get? old k = Store.get? new k) :
    ∀ op ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops, op.key ≠ k := by
  intro op hop he
  rcases of_mem hop with h1 | h1
  · rw [he, h, Op.change_same] at h1
    exact nomatch h1
  · rw [he, h] at h1
    obtain ⟨_, ⟨b, e2⟩, e3⟩ := Op.leave_some h1
    exact nomatch e2.symm.trans e3

/-- **The patch from a kept picture to itself is the empty patch.** -/
theorem of_self (s : σ) (order : List κ) :
    (Patch.of s order s order : Patch κ α δ) = Patch.empty := by
  refine ext' (eq_nil_of_no_mem fun op hop => ?_) (if_pos rfl)
  exact of_kept (δ := δ) (k := op.key) rfl op hop rfl

/-! ## A thing that moved is moved -/

/-- **A thing that moved is moved.** Where a key of the new order has the old thing moved, and
that is not the old thing, the patch has a `move` of the key that gives the new thing. -/
theorem of_moved (old : σ) (oldOrder : List κ) (new : τ) {newOrder : List κ} {k : κ}
    (hk : k ∈ newOrder) {b : α} {d : δ} (ho : Store.get? old k = some b)
    (hnw : Store.get? new k = some (Moves.move d b)) (hne : Moves.move d b ≠ b) :
    ∃ e : δ, Op.move k e ∈ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops ∧
      Moves.move e b = Moves.move d b := by
  cases h : MovedBy.amount b (Moves.move d b) with
  | none =>
    have c := MovedBy.amount_complete d b
    rw [h] at c
    exact nomatch c
  | some e =>
    refine ⟨e, ?_, MovedBy.amount_sound h⟩
    rw [of_ops]
    refine List.mem_append.mpr (Or.inl (List.mem_filterMap.mpr ⟨k, hk, ?_⟩))
    rw [ho, hnw]
    show (if Moves.move d b = b then none else some (Op.step k b (Moves.move d b))) =
      some (Op.move k e)
    rw [if_neg hne]
    unfold Op.step
    rw [h]

/-- **A thing that moved is not put again**: the patch has no `put` of its key. -/
theorem of_moved_no_put (old : σ) (oldOrder : List κ) (new : τ) (newOrder : List κ) {k : κ}
    {b : α} {d : δ} (ho : Store.get? old k = some b)
    (hnw : Store.get? new k = some (Moves.move d b)) (c : α) :
    Op.put k c ∉ (Patch.of old oldOrder new newOrder : Patch κ α δ).ops := by
  intro hop
  rcases of_mem hop with h1 | h1
  · have h2 : Op.change k (Store.get? old k) (Store.get? new k) = some (Op.put k c) := h1
    rw [ho, hnw] at h2
    have h3 : (if Moves.move d b = b then none else some (Op.step k b (Moves.move d b))) =
        some (Op.put k c) := h2
    by_cases e : Moves.move d b = b
    · rw [if_pos e] at h3
      exact nomatch h3
    · rw [if_neg e] at h3
      have h4 : Op.step k b (Moves.move d b) = Op.put k c := Option.some.inj h3
      unfold Op.step at h4
      cases h : MovedBy.amount b (Moves.move d b) with
      | none =>
        have c' := MovedBy.amount_complete d b
        rw [h] at c'
        exact nomatch c'
      | some e' =>
        rw [h] at h4
        exact nomatch h4
  · exact nomatch (Op.leave_some h1).1

end

/-! ## Two patches in a row, on a table -/

/-- **Two patches in a row, on a table, are the first and then the second.** -/
theorem applyTo_append (p q : Patch κ α δ) (s : σ) :
    (p ++ q).applyTo s = q.applyTo (p.applyTo s) :=
  List.foldl_append

theorem applyTo_empty (s : σ) : (Patch.empty : Patch κ α δ).applyTo s = s := rfl

end

end Patch

/-! ## Pictures that are lists -/

/-- A list read back through answers that give each thing at its key is the list. -/
private theorem filterMap_keys {κ α : Type} (key : α → κ) (f : κ → Option α) : ∀ m : List α,
    (∀ a ∈ m, f (key a) = some a) → (m.map key).filterMap f = m
  | [], _ => rfl
  | a :: m, h => by
    rw [List.map_cons, List.filterMap_cons_some (h a List.mem_cons_self),
      filterMap_keys key f m fun b hb => h b (List.mem_cons_of_mem a hb)]

section

variable {κ α δ : Type} [DecidableEq κ]

/-- What the lookup of a list answers is a thing of the list with the key. -/
theorem byKey_some {key : α → κ} {l : List α} {k : κ} {a : α} (h : byKey key l k = some a) :
    a ∈ l ∧ key a = k :=
  ⟨List.mem_of_find?_eq_some h, beq_iff_eq.mp (List.find?_some (p := fun a => key a == k) h)⟩

/-- Where the lookup of a list answers nothing, no thing of the list has the key. -/
theorem byKey_none {key : α → κ} {l : List α} {k : κ} (h : byKey key l k = none) :
    ∀ a ∈ l, key a ≠ k :=
  fun a ha e => List.find?_eq_none.mp h a ha (beq_iff_eq.mpr e)

/-- With distinct keys, the lookup of a list answers each thing at its key. -/
theorem byKey_of_mem {key : α → κ} {l : List α} (hd : Distinct key l) {a : α} (ha : a ∈ l) :
    byKey key l (key a) = some a :=
  find_of_distinct key hd ha rfl

/-- The lookup of a list answers at each key of the list. -/
theorem byKey_of_key {key : α → κ} {l : List α} {k : κ} (hk : k ∈ l.map key) :
    ∃ a, byKey key l k = some a := by
  obtain ⟨b, hb, e⟩ := List.mem_map.mp hk
  cases h : byKey key l k with
  | some a => exact ⟨a, rfl⟩
  | none => exact absurd e (byKey_none h b hb)

/-- **A list with distinct keys is the things of its lookup, in the order of its keys.** -/
theorem things_byKey {key : α → κ} {l : List α} (hd : Distinct key l) :
    Store.things (byKey key l) (l.map key) = l :=
  filterMap_keys key (byKey key l) l fun _ ha => byKey_of_mem hd ha

variable [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α] [DecidableEq α]

/-- **The patch applied to the old picture is the new picture**, where the keys of the new
picture are distinct. Nothing is asked of the old picture. -/
theorem apply_diff (key : α → κ) (old : List α) {new : List α} (hd : Distinct key new) :
    (diff key old new : Patch κ α δ).apply key old = new :=
  (Patch.things_of (byKey key old) (old.map key) (byKey key new) hd fun _ hk =>
    byKey_of_key hk).trans (things_byKey hd)

/-- **After the patch the lookup of the old picture is the lookup of the new one**, at every
key, where the keys of the new picture are distinct. -/
theorem applyTo_diff (key : α → κ) (old : List α) {new : List α} (hd : Distinct key new) :
    (diff key old new : Patch κ α δ).applyTo (byKey key old) = byKey key new :=
  funext fun k =>
    Patch.get?_applyTo_of (byKey key old) (byKey key new) hd
      (fun _ b h => List.mem_map.mpr ⟨b, (byKey_some h).1, (byKey_some h).2⟩)
      (fun _ a h => List.mem_map.mpr ⟨a, (byKey_some h).1, (byKey_some h).2⟩) k

/-- **The patch of a picture to itself is the empty patch.** -/
theorem diff_self (key : α → κ) (l : List α) : (diff key l l : Patch κ α δ) = Patch.empty :=
  Patch.of_self (byKey key l) (l.map key)

/-- **A thing that is in both pictures is in no operation**, where the keys of each picture are
distinct. -/
theorem diff_kept (key : α → κ) {old new : List α} (ho : Distinct key old)
    (hn : Distinct key new) {a : α} (h1 : a ∈ old) (h2 : a ∈ new) :
    ∀ op ∈ (diff key old new : Patch κ α δ).ops, op.key ≠ key a :=
  Patch.of_kept (σ := κ → Option α) (τ := κ → Option α)
    ((byKey_of_mem ho h1).trans (byKey_of_mem hn h2).symm)

/-- **A thing that moved is moved, and not put again.** The old picture has `b`, the new one
has `b` moved, under the same key, and that is not `b`. Then the patch has a `move` of the key
that gives the new thing, and no `put` of the key. -/
theorem diff_moved (key : α → κ) {old new : List α} (ho : Distinct key old)
    (hn : Distinct key new) {b : α} {d : δ} (h1 : b ∈ old) (h2 : Moves.move d b ∈ new)
    (hk : key (Moves.move d b) = key b) (hne : Moves.move d b ≠ b) :
    (∃ e : δ, Patch.Op.move (key b) e ∈ (diff key old new : Patch κ α δ).ops ∧
        Moves.move e b = Moves.move d b) ∧
      ∀ c, Patch.Op.put (key b) c ∉ (diff key old new : Patch κ α δ).ops := by
  have e1 : byKey key old (key b) = some b := byKey_of_mem ho h1
  have e2 : byKey key new (key b) = some (Moves.move d b) := by
    rw [← hk]
    exact byKey_of_mem hn h2
  have hm : key b ∈ new.map key := List.mem_map.mpr ⟨Moves.move d b, h2, hk⟩
  exact ⟨Patch.of_moved (byKey key old) (old.map key) (byKey key new) hm e1 e2 hne,
    Patch.of_moved_no_put (byKey key old) (old.map key) (byKey key new) (new.map key) e1 e2⟩

/-- **Two patches in a row take the first picture to the third**, where the keys of the second
and of the third are distinct. -/
theorem apply_append_diff (key : α → κ) (a : List α) {b c : List α} (hb : Distinct key b)
    (hc : Distinct key c) :
    (diff key a b ++ diff key b c : Patch κ α δ).apply key a = c := by
  show Store.things ((diff key a b ++ diff key b c : Patch κ α δ).applyTo (byKey key a))
    ((diff key a b ++ diff key b c : Patch κ α δ).reorder (a.map key)) = c
  rw [Patch.applyTo_append, Patch.reorder_append, applyTo_diff key a hb]
  have e : (diff key a b : Patch κ α δ).reorder (a.map key) = b.map key :=
    Patch.reorder_of (byKey key a) (a.map key) (byKey key b) (b.map key)
  rw [e]
  exact apply_diff key b hc

/-! ## In the words of the join -/

/-- **A key is dropped exactly when a thing with it exits.** -/
theorem drop_mem_diff (key : α → κ) (old new : List α) (k : κ) :
    Patch.Op.drop k ∈ (diff key old new : Patch κ α δ).ops ↔
      ∃ o ∈ (join key old new).exit, key o = k := by
  constructor
  · intro h
    rcases Patch.of_mem h with h1 | h1
    · exact absurd h1 (Patch.Op.change_ne_drop k k _ _)
    · obtain ⟨_, ⟨b, e2⟩, e3⟩ := Patch.Op.leave_some h1
      have hb : byKey key old k = some b := e2
      have hn : byKey key new k = none := e3
      obtain ⟨m, hkb⟩ := byKey_some hb
      refine ⟨b, (mem_exit key old new).mpr ⟨m, fun n hnm e => ?_⟩, hkb⟩
      exact byKey_none hn n hnm (e.trans hkb)
  · intro ⟨o, ho, hk⟩
    obtain ⟨m, hne⟩ := (mem_exit key old new).mp ho
    have hkm : k ∈ old.map key := List.mem_map.mpr ⟨o, m, hk⟩
    obtain ⟨b, hb⟩ := byKey_of_key hkm
    have hn : byKey key new k = none :=
      List.find?_eq_none.mpr fun n hnm e => hne n hnm ((beq_iff_eq.mp e).trans hk.symm)
    rw [show (diff key old new : Patch κ α δ).ops = _ from
      Patch.of_ops (byKey key old) (old.map key) (byKey key new) (new.map key)]
    refine List.mem_append.mpr (Or.inr (List.mem_filterMap.mpr ⟨k, hkm, ?_⟩))
    show Patch.Op.leave k (byKey key old k) (byKey key new k) = some (Patch.Op.drop k)
    rw [hb, hn]
    rfl

/-- **A thing that enters is put**, where the keys of the new picture are distinct. -/
theorem put_mem_diff (key : α → κ) (old : List α) {new : List α} (hd : Distinct key new) {n : α}
    (h : n ∈ (join key old new).enter) :
    Patch.Op.put (key n) n ∈ (diff key old new : Patch κ α δ).ops := by
  obtain ⟨m, hne⟩ := (mem_enter key old new).mp h
  have ho : byKey key old (key n) = none :=
    List.find?_eq_none.mpr fun o hom e => hne o hom (beq_iff_eq.mp e)
  have hn : byKey key new (key n) = some n := byKey_of_mem hd m
  rw [show (diff key old new : Patch κ α δ).ops = _ from
    Patch.of_ops (byKey key old) (old.map key) (byKey key new) (new.map key)]
  refine List.mem_append.mpr (Or.inl (List.mem_filterMap.mpr ⟨key n, List.mem_map_of_mem m, ?_⟩))
  show Patch.Op.change (key n) (byKey key old (key n)) (byKey key new (key n)) =
    some (Patch.Op.put (key n) n)
  rw [ho, hn]
  rfl

end

end Whatwg.Svg.Scene
