import Whatwg.Svg.Scene.Patch.Order
import Whatwg.Svg.Scene.Step.Patch

/-!
# WhatwgTest.Svg.UsePatch

lean4-effect4's retained picture, on `Whatwg/Svg/Scene/Patch.lean` (slice S22). The consumer is
read at its checkout `6ad8f7b8d`: `tools/Tools/View/Retained.lean` (921 lines), with
`KeyMap.lean`, `Live.lean` and `LiveChecks.lean` beside it. This module imports nothing of that
package: it restates the consumer's types under the consumer's names.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `KeyMap`, `get?_empty`, `get?_insert`, `get?_erase` (`KeyMap.lean`, lines 85 to 183) | the same names and the same three statements, over one bucket; `Store (KeyMap κ α) κ α` is the two laws, word for word |
| `ObjId`, `Obj`, `Obj.calls` (`Retained.lean`, lines 43 to 73) | the same, the anchor an `IVec`; `Obj` is an instance of `Moves` and of `MovedBy` |
| `Scene`, `Scene.callsOf`, `Scene.flatten` (lines 125 to 166) | the same |
| `Op.put`, `Op.move`, `Op.drop` (lines 171 to 174) | `Patch.Op ObjId Obj IVec` |
| `Op.shift` of a group (line 175) | `Patch.Op.move` on the table of origins: a second patch, `Patch String IVec IVec` |
| `Patch` (lines 180 to 183) | `ScenePatch`: the patch of the origins and the patch of the objects |
| `shiftOf`, `change`, `dropOf`, `diff` (lines 186 to 220) | `Patch.of`, twice |
| `applyOp`, `Scene.apply` (lines 223 to 260) | `Patch.applyTo` and `Patch.reorder`, twice |
| `Scene.WF` (lines 412 to 414) | the same four clauses, and a fifth: a group with an origin is listed |
| `Op.target`, `Op.group`, `fold_objs_other`, `fold_origins_other`, `opAt`, `applyOp_target`, `shiftAt`, `applyOp_group`, `fold_filterMap_at`, `fold_shifts_at`, `split_nodup`, `change_target`, `dropOf_target`, `shiftOf_group`, `change_gives`, `shiftOf_gives` (lines 416 to 616, 795 to 801) | nothing: they are `Patch.get?_applyTo_of` of the package |
| `apply_diff` (lines 808 to 868) | `apply_diff`, twelve lines |
| `Patch.size` (lines 264 to 283) | `size`, a fold of the operations |
| `Patch.inserts`, `insertsFrom`, `insertAfter`, and the test of `diff` that the old objects kept their order (lines 180 to 183, 207 to 243, 218) | `Reorder ObjId`, `Reorder.ofBy` with the two tables as its tests, `Reorder.apply` |
| `Op.dropped?`, `Patch.dropped`, `contains_ids`, `filterMap_nothing`, `filterMap_twice`, `diff_dropped`, `filter_all`, `filter_congr_mem`, `insertAfter_go`, `inserts_rebuild`, `dropped_contains`, `apply_diff_order` (lines 245 to 251, 618 to 791) | `order_coded`, three lines, by `Patch.reorder_coded` of the package |
| `patchRows` (`Live.lean`, lines 150 to 162) | `patchRows`, a put without its device rows |
| the two guards of `apply_diff` and the control of a group listed twice (`LiveChecks.lean`, lines 212 to 231) | the guards at the end |

**What does not fit, and what would make it fit.**

- *Reading a flat picture as objects* (`runs`, `rank`, `entries`, `Scene.ofGroups`, `of_flatten`,
  `ofGroups_wf`, lines 81 to 157 and 288 to 406, 871 to 919). This is how the consumer makes
  keys distinct: a key and the rank of its run. Nothing of it is a patch. `ofList` below builds a
  scene from keyed objects for the guards.
- *The groups* fit as a second table, and the anchors as `Moves`, as the table above says. Two
  things change for the consumer. Its `Scene.apply` leaves `groups` as it was, and here the
  patch of the origins carries the new list. Its origin of a group reads `(0, 0)` where the
  table has none, so its `shiftOf` moves from there. Here a group with no origin before gets a
  `put`, and an origin of a group that the old scene does not list is never dropped: the fifth
  clause of `WF` says there is none, and the last control shows one.
- *The order* is whole in the patch of the objects (`Patch.order`), which is what two patches in
  a row need. `orderOf` is the consumer's shorter writing of it, beside the patch.

The last section reads the patch of a step (`Whatwg/Svg/Scene/Step/Patch.lean`) at the consumer's
items.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UsePatch

open Whatwg.Svg.Scene

/-! ## The consumer's table by key -/

/-- A table by key: the consumer's `KeyMap`, over one bucket. The consumer's has 4096 buckets
on a sparse index, and the same five operations and three laws. -/
structure KeyMap (κ α : Type) where
  entries : List (κ × α) := []

namespace KeyMap

/-- A list's first entry that passes a test, past a filter that keeps every entry that passes
it. The consumer's `find?_filter_keep`. -/
theorem find?_filter_keep {β : Type} (p q : β → Bool) (keep : ∀ e, p e = true → q e = true) :
    ∀ l : List β, (l.filter q).find? p = l.find? p
  | [] => rfl
  | e :: l => by
    cases hp : p e with
    | true =>
      rw [List.filter_cons_of_pos (keep e hp), List.find?_cons_of_pos hp,
        List.find?_cons_of_pos hp]
    | false =>
      have hp' : ¬p e = true := fun h => Bool.false_ne_true (hp.symm.trans h)
      cases hq : q e with
      | true =>
        rw [List.filter_cons_of_pos hq, List.find?_cons_of_neg hp', List.find?_cons_of_neg hp',
          find?_filter_keep p q keep l]
      | false =>
        have hq' : ¬q e = true := fun h => Bool.false_ne_true (hq.symm.trans h)
        rw [List.filter_cons_of_neg hq', List.find?_cons_of_neg hp', find?_filter_keep p q keep l]

variable {κ α : Type} [DecidableEq κ]

/-- The value at a key. -/
def get? (m : KeyMap κ α) (k : κ) : Option α :=
  (m.entries.find? fun e => decide (e.1 = k)).map (·.2)

/-- The value at a key, or `d`. -/
def getD (m : KeyMap κ α) (k : κ) (d : α) : α := (m.get? k).getD d

/-- The table with `v` at `k`. -/
def insert (m : KeyMap κ α) (k : κ) (v : α) : KeyMap κ α :=
  ⟨(k, v) :: m.entries.filter fun e => !decide (e.1 = k)⟩

/-- The table with nothing at `k`. -/
def erase (m : KeyMap κ α) (k : κ) : KeyMap κ α :=
  ⟨m.entries.filter fun e => !decide (e.1 = k)⟩

/-- An entry at the key `j` passes the filter that drops the key `k`, where the two differ. -/
private theorem keep_other {k j : κ} (hkj : ¬k = j) (e : κ × α)
    (he : decide (e.1 = j) = true) : (!decide (e.1 = k)) = true := by
  have h1 : e.1 = j := of_decide_eq_true he
  have h2 : decide (e.1 = k) = false := decide_eq_false fun h => hkj (h.symm.trans h1)
  rw [h2]
  rfl

/-- **The empty table answers nothing.** -/
theorem get?_empty (k : κ) : ({} : KeyMap κ α).get? k = none := rfl

/-- **A lookup after an insert** answers the value at the inserted key, and the old answer at
every other key. The consumer's statement. -/
theorem get?_insert (m : KeyMap κ α) (k j : κ) (v : α) :
    (m.insert k v).get? j = if k = j then some v else m.get? j := by
  show (((k, v) :: m.entries.filter fun e => !decide (e.1 = k)).find?
    fun e => decide (e.1 = j)).map (·.2) = _
  by_cases hkj : k = j
  · rw [if_pos hkj,
      List.find?_cons_of_pos (p := fun e : κ × α => decide (e.1 = j)) (decide_eq_true hkj)]
    rfl
  · rw [if_neg hkj, List.find?_cons_of_neg (p := fun e : κ × α => decide (e.1 = j))
        (fun e => hkj (of_decide_eq_true e)),
      find?_filter_keep (fun e : κ × α => decide (e.1 = j)) (fun e => !decide (e.1 = k))
        (keep_other hkj) m.entries]
    rfl

/-- **A lookup after an erase** answers nothing at the erased key, and the old answer at every
other key. The consumer's statement. -/
theorem get?_erase (m : KeyMap κ α) (k j : κ) :
    (m.erase k).get? j = if k = j then none else m.get? j := by
  show ((m.entries.filter fun e => !decide (e.1 = k)).find? fun e => decide (e.1 = j)).map (·.2) = _
  by_cases hkj : k = j
  · have hnone : (m.entries.filter fun e => !decide (e.1 = k)).find?
        (fun e => decide (e.1 = j)) = none :=
      List.find?_eq_none.mpr fun e he hd => by
        have h2 : (!decide (e.1 = k)) = true := (List.mem_filter.mp he).2
        have h3 : decide (e.1 = k) = true := decide_eq_true ((of_decide_eq_true hd).trans hkj.symm)
        rw [h3] at h2
        exact Bool.false_ne_true h2
    rw [if_pos hkj, hnone]
    rfl
  · rw [if_neg hkj,
      find?_filter_keep (fun e : κ × α => decide (e.1 = j)) (fun e => !decide (e.1 = k))
        (keep_other hkj) m.entries]
    rfl

end KeyMap

/-- **The consumer's table is a table of the package**, by the two laws it has. -/
instance {κ α : Type} [DecidableEq κ] : Store (KeyMap κ α) κ α where
  get? := KeyMap.get?
  insert := KeyMap.insert
  erase := KeyMap.erase
  get?_insert := KeyMap.get?_insert
  get?_erase := KeyMap.get?_erase

/-! ## Objects -/

/-- An object's identity: its group, its key, and the rank of its run. The consumer's `ObjId`. -/
structure ObjId where
  group : String
  key : String
  nth : Nat
  deriving DecidableEq, Repr

/-- A call of a picture, as far as a patch reads it: what it draws, and where. The consumer's
`Call` has nine shapes, each with a place that `Call.move` moves. -/
structure Call where
  what : String
  place : IVec
  deriving DecidableEq, Repr

/-- A call moved by whole pixels: the consumer's `Call.move`. -/
def Call.move (d : IVec) (c : Call) : Call := { c with place := c.place + d }

/-- An object: its anchor in its group, and its calls relative to the anchor. The consumer's
`Obj`. -/
structure Obj where
  anchor : IVec
  rel : List Call
  deriving DecidableEq, Repr

theorem Obj.ext' {a b : Obj} (h1 : a.anchor = b.anchor) (h2 : a.rel = b.rel) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  rfl

/-- An object's calls, at its anchor: the consumer's `Obj.calls`. -/
def Obj.calls (o : Obj) : List Call := o.rel.map (Call.move o.anchor)

/-- **An object moves by its anchor.** The consumer's `Op.move` adds to the anchor
(`applyOp`, line 228). -/
instance : Moves IVec Obj where
  move d o := { o with anchor := o.anchor + d }
  move_zero o := Obj.ext' (IVec.add_zero o.anchor) rfl
  move_move d e o := Obj.ext' (IVec.add_assoc o.anchor d e) rfl

/-- **One object is another, moved, where the two have the same calls**: the test of the
consumer's `change` (lines 196 to 198), with its two laws. -/
instance : MovedBy IVec Obj where
  amount p o := if o.rel = p.rel then some (o.anchor - p.anchor) else none
  amount_sound {a b d} h := by
    have h' : (if b.rel = a.rel then some (b.anchor - a.anchor) else none) = some d := h
    by_cases e : b.rel = a.rel
    · rw [if_pos e] at h'
      have hd : b.anchor - a.anchor = d := Option.some.inj h'
      rw [← hd]
      exact Obj.ext' ((IVec.add_comm _ _).trans (IVec.sub_add_cancel _ _)) e.symm
    · rw [if_neg e] at h'
      exact nomatch h'
  amount_complete d a := by
    show (if a.rel = a.rel then some (a.anchor + d - a.anchor) else none).isSome = true
    rw [if_pos rfl]
    rfl

/-! ## Scenes -/

/-- A retained picture: its groups, the origin of each, its objects by identity, and their
order of painting. The consumer's `Scene`. -/
structure Scene where
  groups : List String := []
  origins : KeyMap String IVec := {}
  objs : KeyMap ObjId Obj := {}
  order : List ObjId := []

/-- The calls of one object of a scene, each moved to its group's origin and keyed. The
consumer's `Scene.callsOf`. -/
def Scene.callsOf (s : Scene) (id : ObjId) : List (String × Call) :=
  ((s.objs.get? id).map fun ob =>
    ob.calls.map fun c => (id.key, c.move (s.origins.getD id.group 0))).getD []

/-- **The picture of a retained scene**: the consumer's `Scene.flatten`. -/
def Scene.flatten (s : Scene) : List (String × Call) := s.order.flatMap s.callsOf

/-- A scene from groups with their origins and objects with their identities, in order. -/
def Scene.ofList (groups : List (String × IVec)) (objs : List (ObjId × Obj)) : Scene where
  groups := groups.map (·.1)
  origins := groups.foldr (fun g m => m.insert g.1 g.2) {}
  objs := objs.foldr (fun e m => m.insert e.1 e.2) {}
  order := objs.map (·.1)

/-! ## The patch -/

/-- **The patch of a scene**: the patch of its origins by group, and the patch of its objects
by identity. A `move` of the first is the consumer's `Op.shift`. -/
structure ScenePatch where
  shifts : Patch String IVec IVec := {}
  objs : Patch ObjId Obj IVec := {}

/-- **The patch from one scene to the next**: the consumer's `diff`. -/
def diff (old new : Scene) : ScenePatch where
  shifts := Patch.of old.origins old.groups new.origins new.groups
  objs := Patch.of old.objs old.order new.objs new.order

/-- **A patch applied** to a retained scene: the consumer's `Scene.apply`. -/
def Scene.apply (s : Scene) (p : ScenePatch) : Scene where
  groups := p.shifts.reorder s.groups
  origins := p.shifts.applyTo s.origins
  objs := p.objs.applyTo s.objs
  order := p.objs.reorder s.order

/-- Two patches of a scene in a row, as one. The consumer has no such operation. -/
def ScenePatch.append (p q : ScenePatch) : ScenePatch := ⟨p.shifts ++ q.shifts, p.objs ++ q.objs⟩

/-- **A well-formed scene**: the consumer's four clauses, and a fifth, that a group with an
origin is listed. -/
def Scene.WF (s : Scene) : Prop :=
  s.order.Nodup ∧ s.groups.Nodup ∧ (∀ id, (s.objs.get? id).isSome = true ↔ id ∈ s.order) ∧
    (∀ id ∈ s.order, id.group ∈ s.groups) ∧
      ∀ g, (s.origins.get? g).isSome = true → g ∈ s.groups

/-- **A scene patched by the diff to another flattens to the other.** The consumer's
`apply_diff`, by the law of the package at each of the two tables. -/
theorem apply_diff {s t : Scene} (hs : s.WF) (ht : t.WF) :
    (s.apply (diff s t)).flatten = t.flatten := by
  obtain ⟨_, _, hsobj, _, hsorig⟩ := hs
  obtain ⟨htnd, htg, htobj, _, htorig⟩ := ht
  have hobjs : ∀ id, ((diff s t).objs.applyTo s.objs).get? id = t.objs.get? id :=
    Patch.get?_applyTo_of s.objs t.objs htnd
      (fun k _ h => (hsobj k).mp (congrArg Option.isSome h))
      (fun k _ h => (htobj k).mp (congrArg Option.isSome h))
  have horig : ∀ g, ((diff s t).shifts.applyTo s.origins).get? g = t.origins.get? g :=
    Patch.get?_applyTo_of s.origins t.origins htg
      (fun g _ h => hsorig g (congrArg Option.isSome h))
      (fun g _ h => htorig g (congrArg Option.isSome h))
  have horder : (diff s t).objs.reorder s.order = t.order :=
    Patch.reorder_of s.objs s.order t.objs t.order
  have hcalls : (s.apply (diff s t)).callsOf = t.callsOf := funext fun id => by
    show (((diff s t).objs.applyTo s.objs).get? id |>.map fun ob => ob.calls.map fun c =>
        (id.key, c.move ((((diff s t).shifts.applyTo s.origins).get? id.group).getD 0))).getD [] =
      ((t.objs.get? id).map fun ob => ob.calls.map fun c =>
        (id.key, c.move ((t.origins.get? id.group).getD 0))).getD []
    rw [hobjs id, horig id.group]
  show ((diff s t).objs.reorder s.order).flatMap (s.apply (diff s t)).callsOf =
    t.order.flatMap t.callsOf
  rw [horder, hcalls]

/-! ## What reads a patch -/

/-- The size of a patch: the consumer's `Size`. -/
structure Size where
  shifts : Nat := 0
  moves : Nat := 0
  putsNew : Nat := 0
  putsChanged : Nat := 0
  drops : Nat := 0
  calls : Nat := 0
  reordered : Nat := 0
  deriving DecidableEq, Repr

/-- A patch's size, from the scene it applies to: the consumer's `Patch.size`. -/
def size (old : Scene) (p : ScenePatch) : Size :=
  p.objs.ops.foldl (fun (z : Size) op =>
    match op with
    | .move .. => { z with moves := z.moves + 1 }
    | .put id o =>
      if (old.objs.get? id).isSome then
        { z with putsChanged := z.putsChanged + 1, calls := z.calls + o.rel.length }
      else { z with putsNew := z.putsNew + 1, calls := z.calls + o.rel.length }
    | .drop .. => { z with drops := z.drops + 1 })
    { shifts := p.shifts.ops.length, reordered := if p.objs.order.isSome then 1 else 0 }

/-- An object's id as a row field: the consumer's `idText`. -/
def idText (id : ObjId) : String := id.group ++ "/" ++ id.key ++ "#" ++ toString id.nth

/-- **The order of a patch, as the consumer writes it**: the new objects each with the object
before it, where the old objects kept their order, and else the whole order. The consumer's
`inserts` and `order` of a `Patch`. -/
def orderOf (old new : Scene) : Reorder ObjId :=
  Reorder.ofBy (fun id => (old.objs.get? id).isSome) (fun id => (new.objs.get? id).isSome)
    old.order new.order

/-- **The order that a coded patch leaves is the new order**: the consumer's
`apply_diff_order`. A store drops what the patch drops, and puts each new object after the
object named. -/
theorem order_coded {s t : Scene} (hs : s.WF) (ht : t.WF) :
    (orderOf s t).apply (fun id => !decide (id ∈ (diff s t).objs.dropped)) s.order = t.order :=
  Patch.reorder_coded s.objs t.objs (fun id => (s.objs.get? id).isSome) ht.1
    fun k hk => Option.isSome_iff_exists.mp ((hs.2.2.1 k).mpr hk)

/-- **A patch as rows**: the consumer's `patchRows`, a put without its device rows. -/
def patchRows (frame : Nat) (p : ScenePatch) (order : Reorder ObjId) : List String :=
  p.shifts.ops.filterMap (fun
    | .move g d => some s!"G\t{g}\t{d.x}\t{d.y}"
    | .put g o => some s!"G=\t{g}\t{o.x}\t{o.y}"
    | .drop _ => none) ++
  p.objs.ops.map (fun
    | .put id o => s!"O\t{idText id}\t{o.anchor.x}\t{o.anchor.y}"
    | .move id d => s!"M\t{idText id}\t{d.x}\t{d.y}"
    | .drop id => s!"X\t{idText id}") ++
  (match order with
    | .inserts ins => ins.map fun x => s!"I\t{idText x.1}\t{(x.2.map idText).getD ""}"
    | .whole ids => ["Q\t" ++ "\t".intercalate (ids.map idText)]) ++
  [s!"E\t{frame}"]

/-! ## Finite evaluations

Two frames of a page. The graph's panel stands at `(16, 200)` and then at `(16, 248)`: a line
was added above it. In the panel the box `a` stays, the box `b` moves `40` to the right, the box
`c` gets another label, the box `d` leaves and the box `e` is new. -/

/-- A box of the graph: one frame and one text, relative to its anchor. -/
def box (label : String) : List Call := [⟨"frame", ⟨0, 0⟩⟩, ⟨"text " ++ label, ⟨8, 16⟩⟩]

def frame1 : Scene :=
  Scene.ofList [("lines", ⟨0, 0⟩), ("graph", ⟨16, 200⟩)]
    [(⟨"graph", "a", 0⟩, ⟨⟨0, 0⟩, box "a"⟩), (⟨"graph", "b", 0⟩, ⟨⟨0, 72⟩, box "b"⟩),
      (⟨"graph", "c", 0⟩, ⟨⟨0, 144⟩, box "c"⟩), (⟨"graph", "d", 0⟩, ⟨⟨0, 216⟩, box "d"⟩)]

def frame2 : Scene :=
  Scene.ofList [("lines", ⟨0, 0⟩), ("graph", ⟨16, 248⟩)]
    [(⟨"graph", "a", 0⟩, ⟨⟨0, 0⟩, box "a"⟩), (⟨"graph", "e", 0⟩, ⟨⟨120, 72⟩, box "e"⟩),
      (⟨"graph", "b", 0⟩, ⟨⟨40, 72⟩, box "b"⟩), (⟨"graph", "c", 0⟩, ⟨⟨0, 144⟩, box "see"⟩)]

-- The patch, as the rows the consumer writes: the panel is shifted, and that one row moves
-- every box of it; `e` and the changed `c` are put, `b` is moved, `d` is dropped, and the new
-- box `e` has its place after `a`, since the kept boxes kept their order. `a` is in no row.
#guard patchRows 2 (diff frame1 frame2) (orderOf frame1 frame2) ==
  ["G\tgraph\t0\t48", "O\tgraph/e#0\t120\t72", "M\tgraph/b#0\t40\t0", "O\tgraph/c#0\t0\t144",
    "X\tgraph/d#0", "I\tgraph/e#0\tgraph/a#0", "E\t2"]

-- A store that reads those rows has the new order: it drops `d`, and puts `e` after `a`.
#guard (orderOf frame1 frame2).apply (fun id => !decide (id ∈ (diff frame1 frame2).objs.dropped))
    frame1.order == frame2.order

-- Back from the second frame to the first, `d` is new and last, after `c`. Where two kept
-- boxes change places the order is written whole.
#guard orderOf frame2 frame1 == .inserts [(⟨"graph", "d", 0⟩, some ⟨"graph", "c", 0⟩)]
#guard orderOf frame1 { frame1 with order := frame1.order.reverse } ==
  .whole frame1.order.reverse

-- Its size, as the consumer counts it: one shift, one move, one new object and one changed
-- one of two calls each, one drop, and the order.
#guard size frame1 (diff frame1 frame2) ==
  { shifts := 1, moves := 1, putsNew := 1, putsChanged := 1, drops := 1, calls := 4,
    reordered := 1 }

-- The consumer's guard of `apply_diff` (`LiveChecks.lean`, lines 212 to 216), at these frames
-- and back.
#guard (frame1.apply (diff frame1 frame2)).flatten == frame2.flatten
#guard (frame2.apply (diff frame2 frame1)).flatten == frame1.flatten

-- A frame to itself: no row but the end, and no order.
#guard patchRows 3 (diff frame2 frame2) (orderOf frame2 frame2) == ["E\t3"]

-- The first frame of a session, from the empty scene: every group's origin and every object is
-- put, and the scene after is the frame.
#guard size {} (diff {} frame1) ==
  { shifts := 2, moves := 0, putsNew := 4, putsChanged := 0, drops := 0, calls := 8,
    reordered := 1 }
#guard (({} : Scene).apply (diff {} frame1)).flatten == frame1.flatten

-- Two patches in a row, as one: from the empty scene to the second frame through the first.
#guard (({} : Scene).apply ((diff {} frame1).append (diff frame1 frame2))).flatten ==
  frame2.flatten

/-! ## Controls -/

/-- A scene of one object in the group `g` at the origin `o`, its group listed `n` times. The
consumer's `oneObject`. -/
def oneObject (o : IVec) (n : Nat) : Scene :=
  { Scene.ofList [("g", o)] [(⟨"g", "k", 0⟩, ⟨⟨0, 0⟩, [⟨"hit", ⟨0, 0⟩⟩]⟩)] with
    groups := List.replicate n "g" }

-- The control of the premise that the new order has no repeat (`Patch.get?_applyTo_of_mem`),
-- which is the consumer's control of a group listed twice (`LiveChecks.lean`, lines 226 to
-- 231): the group's move is written twice and done twice, and the patched scene stands twice
-- as far off.
#guard ((oneObject ⟨0, 0⟩ 1).apply (diff (oneObject ⟨0, 0⟩ 1) (oneObject ⟨5, 0⟩ 1))).flatten ==
  (oneObject ⟨5, 0⟩ 1).flatten
#guard ((oneObject ⟨0, 0⟩ 1).apply (diff (oneObject ⟨0, 0⟩ 1) (oneObject ⟨5, 0⟩ 2))).flatten !=
  (oneObject ⟨5, 0⟩ 2).flatten
#guard (diff (oneObject ⟨0, 0⟩ 1) (oneObject ⟨5, 0⟩ 2)).shifts.ops ==
  [.move "g" ⟨5, 0⟩, .move "g" ⟨5, 0⟩]

-- The control of the fifth clause of `WF`. The old scene has an origin for a group that it
-- does not list, and the new scene has that group in its list with no origin, which reads as
-- the origin `0`. No `drop` is written for a key outside the old order, so the old origin
-- stays, and the object stands off. The consumer's `shiftOf` reads both origins with a default
-- and has no such case.
#guard
  let old : Scene := { oneObject ⟨5, 0⟩ 0 with order := [] }
  let new : Scene := { oneObject ⟨0, 0⟩ 1 with origins := {} }
  (diff old new).shifts.ops == [] && (old.apply (diff old new)).flatten != new.flatten

/-! ## A picture that is a list -/

/-- A placed item of the graph: the consumer's `Placed` (`tools/Tools/View/Graph.lean`, line
150), as far as a patch reads it. -/
structure Placed where
  key : String
  x : Int
  y : Int
  w : Int
  deriving DecidableEq, Repr

theorem Placed.ext' {a b : Placed} (h1 : a.key = b.key) (h2 : a.x = b.x) (h3 : a.y = b.y)
    (h4 : a.w = b.w) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  cases h4
  rfl

/-- An item moves by whole pixels. -/
instance : Moves IVec Placed where
  move d p := { p with x := p.x + d.x, y := p.y + d.y }
  move_zero p := by
    cases p
    simp only [IVec.zero_x, IVec.zero_y, Int.add_zero]
  move_move d e p := by
    cases p
    simp only [IVec.add_x, IVec.add_y, Int.add_assoc]

/-- One item is another, moved, where the two have one key and one width. -/
instance : MovedBy IVec Placed where
  amount p q := if q.key = p.key ∧ q.w = p.w then some ⟨q.x - p.x, q.y - p.y⟩ else none
  amount_sound {a b d} h := by
    have h' : (if b.key = a.key ∧ b.w = a.w then some (⟨b.x - a.x, b.y - a.y⟩ : IVec) else none) =
        some d := h
    by_cases e : b.key = a.key ∧ b.w = a.w
    · rw [if_pos e] at h'
      have hd : (⟨b.x - a.x, b.y - a.y⟩ : IVec) = d := Option.some.inj h'
      rw [← hd]
      exact Placed.ext' e.1.symm (by show a.x + (b.x - a.x) = b.x; omega)
        (by show a.y + (b.y - a.y) = b.y; omega) e.2.symm
    · rw [if_neg e] at h'
      exact nomatch h'
  amount_complete d a := by
    show (if a.key = a.key ∧ a.w = a.w then
      some (⟨a.x + d.x - a.x, a.y + d.y - a.y⟩ : IVec) else none).isSome = true
    rw [if_pos ⟨rfl, rfl⟩]
    rfl

/-- **The patch of two laid graphs, applied to the first, is the second**, where the keys of
the second are distinct: `apply_diff` of the package, read at the consumer's items. -/
example (old new : List Placed) (h : Distinct Placed.key new) :
    (Whatwg.Svg.Scene.diff Placed.key old new).apply Placed.key old = new :=
  Whatwg.Svg.Scene.apply_diff Placed.key old h

/-- **Three laid graphs in a row**: the two patches as one take the first to the third. -/
example (a b c : List Placed) (hb : Distinct Placed.key b) (hc : Distinct Placed.key c) :
    (Whatwg.Svg.Scene.diff Placed.key a b ++ Whatwg.Svg.Scene.diff Placed.key b c).apply
      Placed.key a = c :=
  apply_append_diff Placed.key a hb hc

-- A graph before and after a node was added above: the kept boxes move down as they are, the
-- new one is put, and nothing is said of the box that stayed.
#guard (Whatwg.Svg.Scene.diff Placed.key
    [⟨"root", 40, 0, 64⟩, ⟨"left", 0, 72, 64⟩, ⟨"right", 80, 72, 64⟩]
    [⟨"root", 40, 0, 64⟩, ⟨"mid", 40, 72, 64⟩, ⟨"left", 0, 144, 64⟩, ⟨"right", 80, 144, 72⟩]).ops ==
  [.put "mid" ⟨"mid", 40, 72, 64⟩, .move "left" ⟨0, 72⟩, .put "right" ⟨"right", 80, 144, 72⟩]

-- The control of `apply_diff`'s premise. The new picture has two things with one key: the
-- lookup answers the first for both, and the picture after the patch has the first one twice.
#guard (Whatwg.Svg.Scene.diff Placed.key [] [⟨"k", 0, 0, 8⟩, ⟨"k", 9, 9, 8⟩]).apply Placed.key
    ([] : List Placed) ==
  [⟨"k", 0, 0, 8⟩, ⟨"k", 0, 0, 8⟩]

/-! ## The patch of a step -/

/-- **The patch of a step of the graph, applied to the graph before, is the graph after**:
`Step.apply_patch`, read at the consumer's items. -/
example (s : Step Placed String) (h : Distinct s.key s.new) :
    s.patch.apply s.key s.old = s.new :=
  s.apply_patch h

-- A step in which `a` stays, `b` leaves and `c` is new: the patch puts `c` and drops `b`. The
-- step is interrupted half way by a picture with `a` alone, five to the right. The things
-- drawn then are `b`, which was leaving, and `a` and `c`, so the patch of the step that
-- interrupts moves `a` and drops both others.
#guard
  let still : Plan Placed := ⟨fun _ _ => [], fun _ => [], fun _ => []⟩
  let s : Step Placed String :=
    { key := Placed.key, old := [⟨"a", 0, 0, 8⟩, ⟨"b", 10, 0, 8⟩],
      new := [⟨"a", 0, 0, 8⟩, ⟨"c", 20, 0, 8⟩], plan := still }
  s.patch.ops == [.put "c" ⟨"c", 20, 0, 8⟩, .drop "b"] &&
    s.drawn 500 == [⟨"b", 10, 0, 8⟩, ⟨"a", 0, 0, 8⟩, ⟨"c", 20, 0, 8⟩] &&
    (s.interrupt 500 [⟨"a", 5, 0, 8⟩] fun _ => {}).patch.ops ==
      [.move "a" ⟨5, 0⟩, .drop "b", .drop "c"]

end WhatwgTest.Svg.UsePatch
