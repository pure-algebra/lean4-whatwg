import Whatwg.Svg.Scene.Join
import Whatwg.Svg.Scene.Moves

/-!
# Whatwg.Svg.Scene.Patch

Owner: the change from one picture to the next, as a value that is applied (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

The join of `Whatwg/Svg/Scene/Join.lean` says what happens to each thing between two pictures. A
program that keeps a picture, in a table by key, wants the same fact as a list of things to do:
put this thing at this key, move the thing at that key, drop the thing at a third, and paint in
this order. That list is a patch. lean4-effect4 has it for its retained scene
(`tools/Tools/View/Retained.lean`: `Op`, `Patch`, `diff`, `Scene.apply`), written for its own
table and its own objects. Here it is written once, for any table and any thing that moves.

- `Store σ κ α`: **a table by key.** A lookup, an insert and an erase, with the two laws that a
  lookup after each reads. A program gives an instance for its own table and converts nothing.
  A lookup itself, a function from keys to things, is a table: it is the plain one, and the
  laws are proved of it.
- `MovedBy δ α`: a thing of `α` that moves, where it can be told whether one thing is another,
  moved, and by what amount. A point is one.
- `Patch.Op κ α δ`: `put k a`, `move k d`, `drop k`. `Patch κ α δ`: operations, and the new
  order of the keys, or none where the order stays.
- `Patch.of old oldOrder new newOrder`: **the patch from one kept picture to another.** A key
  whose thing is the same in both has no operation. A key whose new thing is the old one moved
  has a `move`. A key with another new thing, or with none before, has a `put`. A key of the old
  order with no new thing has a `drop`.
- `p.applyTo s`: the operations of the patch on a table, in turn. `p.reorder order`: the order
  after the patch. `Store.things s order`: the things of a table, in an order.
- `p ++ q`: the patch `p` and then the patch `q`, as one patch. `Patch.empty` changes nothing.
- For a picture that is a list with a key: `byKey key l` is its lookup, `diff key old new` its
  patch and `p.apply key l` the picture after the patch.

The laws are in `Whatwg/Svg/Scene/Patch/Laws.lean`.

One decision, and its reason. The store is a class, and the specification is one of its
instances. The other choice was a specification on lists that each store refines: then a
program proves the refinement for its own store, and has to read its store as a list to state
it. With the class the refinement is proved here, once, for every instance
(`Patch.get?_applyTo`: a lookup after the operations on a table is the operations on the
lookup), and a program's table is an instance by the two laws it already has.

What this module does not claim. A patch is not the least one: a thing that changed and did not
move is put whole, and a thing that moved and changed is put whole. The order is carried whole
where it changed; lean4-effect4's shorter form, the new keys each after the key before it, is
`Whatwg/Svg/Scene/Patch/Order.lean`. A table may hold a thing at a key that its order does not
name, and the laws say what they need of the two.

This layer is under the strict ceiling and has no number in it.
-/

namespace Whatwg.Svg.Scene

/-- **A table by key.** A lookup after an insert answers the inserted thing at that key and the
old answer at every other key, and a lookup after an erase answers nothing at that key and the
old answer at every other key. -/
class Store (σ : Type) (κ α : outParam Type) [DecidableEq κ] where
  /-- The thing at a key. -/
  get? : σ → κ → Option α
  /-- The table with a thing at a key. -/
  insert : σ → κ → α → σ
  /-- The table with nothing at a key. -/
  erase : σ → κ → σ
  /-- A lookup after an insert. -/
  get?_insert : ∀ (s : σ) (k j : κ) (v : α),
    get? (insert s k v) j = if k = j then some v else get? s j
  /-- A lookup after an erase. -/
  get?_erase : ∀ (s : σ) (k j : κ), get? (erase s k) j = if k = j then none else get? s j

/-- **A lookup is a table**: the plain one. An insert and an erase change the answer at one
key. -/
instance {κ α : Type} [DecidableEq κ] : Store (κ → Option α) κ α where
  get? s := s
  insert s k v := fun j => if k = j then some v else s j
  erase s k := fun j => if k = j then none else s j
  get?_insert _ _ _ _ := rfl
  get?_erase _ _ _ := rfl

/-- **A thing that moves, where the move between two things can be told.** `amount a b` is an
amount that takes `a` to `b`, where there is one. -/
class MovedBy (δ : outParam Type) (α : Type) [Add δ] [Zero δ] [Moves δ α] where
  /-- An amount that takes the first thing to the second, where there is one. -/
  amount : α → α → Option δ
  /-- The amount takes the first thing to the second. -/
  amount_sound : ∀ {a b : α} {d : δ}, amount a b = some d → Moves.move d a = b
  /-- A thing and the thing moved have an amount between them. -/
  amount_complete : ∀ (d : δ) (a : α), (amount a (Moves.move d a)).isSome = true

/-- From a point to a point there is one step. -/
instance : MovedBy IVec IVec where
  amount p q := some (q - p)
  amount_sound h := by
    cases h
    exact (IVec.add_comm _ _).trans (IVec.sub_add_cancel _ _)
  amount_complete _ _ := rfl

/-- **One operation of a patch**: a thing put at a key, the thing at a key moved, or the thing
at a key dropped. -/
inductive Patch.Op (κ α δ : Type) where
  | put (k : κ) (a : α)
  | move (k : κ) (d : δ)
  | drop (k : κ)
  deriving DecidableEq, Repr

/-- **A patch**: operations on the things of a table, and the new order of its keys. With no
order the keys stay in the order they have. -/
structure Patch (κ α δ : Type) where
  /-- The operations, in the order in which they are done. -/
  ops : List (Patch.Op κ α δ) := []
  /-- The order of the keys after the patch, where it is not the order before. -/
  order : Option (List κ) := none
  deriving DecidableEq, Repr

namespace Patch

variable {σ τ κ α δ : Type}

/-- The key that an operation is about. -/
def Op.key : Op κ α δ → κ
  | .put k _ => k
  | .move k _ => k
  | .drop k => k

section

variable [Add δ] [Zero δ] [Moves δ α]

/-- What an operation makes of the thing at its key. A move of nothing is nothing. -/
def Op.at : Op κ α δ → Option α → Option α
  | .put _ a, _ => some a
  | .move _ d, o => o.map (Moves.move d)
  | .drop _, _ => none

variable [DecidableEq κ] [Store σ κ α]

/-- **One operation on a table.** A move of a key with no thing changes nothing. -/
def Op.apply (s : σ) : Op κ α δ → σ
  | .put k a => Store.insert s k a
  | .move k d => (Store.get? s k).elim s fun a => Store.insert s k (Moves.move d a)
  | .drop k => Store.erase s k

/-- **The operations of a patch on a table**, in turn. -/
def applyTo (p : Patch κ α δ) (s : σ) : σ := p.ops.foldl Op.apply s

end

/-- **The order of the keys after a patch.** -/
def reorder (p : Patch κ α δ) (order : List κ) : List κ := p.order.getD order

/-- **The patch that changes nothing.** -/
def empty : Patch κ α δ := {}

/-- **One patch and then another, as one patch**: the operations of the first and then those of
the second, and the order of the second, or of the first where the second keeps the order. -/
def append (p q : Patch κ α δ) : Patch κ α δ where
  ops := p.ops ++ q.ops
  order := q.order.or p.order

/-- `p ++ q` is the patch `p` and then the patch `q`. -/
instance : Append (Patch κ α δ) := ⟨append⟩

section

variable [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α] [DecidableEq α]

/-- The operation that takes the old thing `b` at a key to the new thing `a`: a `move` where
`a` is `b` moved, and a `put` otherwise. -/
def Op.step (k : κ) (b a : α) : Op κ α δ :=
  match MovedBy.amount b a with
  | some d => .move k d
  | none => .put k a

/-- What a key needs for its new thing, from its old thing and its new one. Nothing where there
is no new thing, or where the new thing is the old one. A `put` where there was none. Otherwise
the `move` or the `put` of `Op.step`. -/
def Op.change (k : κ) : Option α → Option α → Option (Op κ α δ)
  | none, none => none
  | some _, none => none
  | none, some a => some (.put k a)
  | some b, some a => if a = b then none else some (Op.step k b a)

end

/-- What a key needs where its thing leaves: a `drop` where there was a thing and there is none
now, and nothing otherwise. -/
def Op.leave (k : κ) : Option α → Option α → Option (Op κ α δ)
  | some _, none => some (.drop k)
  | some _, some _ => none
  | none, _ => none

section

variable [Add δ] [Zero δ] [Moves δ α] [MovedBy δ α] [DecidableEq α] [DecidableEq κ]
  [Store σ κ α] [Store τ κ α]

/-- **The patch from one kept picture to another.** Each is a table and the order of its keys,
and the two tables may be of two kinds. First what each key of the new order needs
(`Op.change`), in the new order, and then a `drop` for each key of the old order that has no new
thing. The order is carried where it changed. -/
def of (old : σ) (oldOrder : List κ) (new : τ) (newOrder : List κ) : Patch κ α δ where
  ops := newOrder.filterMap (fun k => Op.change k (Store.get? old k) (Store.get? new k)) ++
    oldOrder.filterMap fun k => Op.leave k (Store.get? old k) (Store.get? new k)
  order := if newOrder = oldOrder then none else some newOrder

end

end Patch

/-- **The things of a table, in an order**: what is drawn. A key with no thing gives none. -/
def Store.things {σ κ α : Type} [DecidableEq κ] [Store σ κ α] (s : σ) (order : List κ) : List α :=
  order.filterMap (Store.get? s)

/-! ## A picture that is a list with a key -/

section

variable {κ α δ : Type} [DecidableEq κ]

/-- **The lookup of a list by key**: the first thing of the list with the key. -/
def byKey (key : α → κ) (l : List α) : κ → Option α := fun k => l.find? fun a => key a == k

variable [Add δ] [Zero δ] [Moves δ α]

/-- **The picture after a patch**: the things of its lookup after the operations, in the order
after the patch. -/
def Patch.apply (key : α → κ) (p : Patch κ α δ) (l : List α) : List α :=
  Store.things (p.applyTo (byKey key l)) (p.reorder (l.map key))

variable [MovedBy δ α] [DecidableEq α]

/-- **The patch from one picture to the next**, each a list with a key. -/
def diff (key : α → κ) (old new : List α) : Patch κ α δ :=
  Patch.of (byKey key old) (old.map key) (byKey key new) (new.map key)

end

end Whatwg.Svg.Scene
