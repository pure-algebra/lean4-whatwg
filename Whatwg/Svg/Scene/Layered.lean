import Whatwg.Svg.Scene.Layers
import Whatwg.Svg.Scene.Join.Laws
import Whatwg.Svg.Scene.Layout.Laws

/-!
# Whatwg.Svg.Scene.Layered

Owner: a graph drawn in layers (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Layers.lean` gives each thing of a graph its layer, as a number.
`Whatwg/Svg/Scene/Layout.lean` puts parts side by side and one above the other. A picture of a
graph in layers is the two together: the things of one layer in a row, and the rows in a
column. lean4-effect4 builds it so (`Graph.layout` of its `tools/Tools/View/Graph.lean`) and
then tests each picture it has drawn with two finite checks: no two boxes share a pixel
(`boxesApart`), and each link drawn down ends below where it starts (`edgesDescend`). Here the
two are laws of the picture, for every graph.

- `Layers.rows h order`: **the things of each layer**, layer by layer from `0`. The row `i` has
  the things of `order` that stand at `i` under `h`, in their order. `h` is any function to
  whole numbers: the layers of `Layers.heights`, or a rank that a program keeps in its own data.
- `Layers.Down r links rows`: **the rows go down the links**. The source of each link is in a
  row before the row of its target.
- `Layout.layered across down rows`: rows of parts, one row above the next. In each row the
  parts stand side by side.

What the laws say:

- `Layers.mem_rows`, `Layers.rows_has`: a thing is in the row of its number and in no other,
  and each thing of the order that stands at `0` or later is in a row.
- `Layers.rows_distinct`: where the keys of the order are distinct, the keys of the rows are:
  no thing is in two rows, and none is twice in a row. `Layout.layered_items_map`: the keys of
  the picture are the keys of its parts, row after row. So a thing of the picture is found by
  its key.
- `Layers.rows_lt`: a thing that stands before another is in an earlier row.
- `Layers.rows_down`: **the rows of the layers go down the links**, along an order that serves
  them, where each link asks for a step of one at least.
- `Layers.Down.members`, `Layers.Down.mono`: rows that go down the links still do when each row
  is put in another order or has more things, and for fewer links. So a caller may order each
  row as it likes, to cross fewer links, and loses nothing here.
- `Layout.Fits.layered`, `Layout.Clear.layered`: the picture fits, and no two of its things
  share room, where each part fits and is clear. This is `boxesApart`.
- `Layout.layered_stands`: each part stands in the picture.
- `Layout.layered_below`: a part of an earlier row ends the gap above every part of a later
  row.
- `Layout.layered_link`: **every link goes down.** Over rows that go down the links, the part
  of the source of each link stands in the picture, the part of its target stands in it, and
  the first ends the gap between rows above the second. This is `edgesDescend`.

What a caller must supply: the part of each thing, as a layout of its own; and for `rows_down`
an order that serves the links (`Layers.sorted` of `Whatwg/Svg/Scene/Layers/Sorted.lean` makes
one).

What this module does not claim: an order of the things of a row that crosses few links, or
places across that put a thing near its neighbours (a row is its parts from the left, a gap
apart); a place for a link that passes several rows; that no row is empty, which is so for
layers in steps of one and not for any `h`; that `rows` is fast, since it reads the order once
for each row.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Layers

variable {ε ν : Type}

/-- The number of the last layer that holds a thing of the order. -/
def last (h : ν → Int) (order : List ν) : Nat := order.foldl (fun m v => max m (h v).toNat) 0

/-- **The things of each layer**, layer by layer from `0`: the row `i` has the things of
`order` that stand at `i`, in their order. -/
def rows (h : ν → Int) (order : List ν) : List (List ν) :=
  (List.range (last h order + 1)).map fun (i : Nat) =>
    order.filter fun v => decide (h v = (i : Int))

/-- **The rows go down the links**: the source of each link is in a row before the row of its
target. -/
def Down (r : Reading ε ν) (links : List ε) (rows : List (List ν)) : Prop :=
  ∀ e ∈ links, ∃ (i j : Nat) (ri rj : List ν), i < j ∧ rows[i]? = some ri ∧ rows[j]? = some rj ∧
    r.src e ∈ ri ∧ r.dst e ∈ rj

/-- The fold of `last` never goes below where it began. -/
private theorem le_foldl_last (h : ν → Int) : ∀ (l : List ν) (m : Nat),
    m ≤ l.foldl (fun m v => max m (h v).toNat) m
  | [], _ => Nat.le_refl _
  | _ :: l, m => Nat.le_trans (Nat.le_max_left m _) (le_foldl_last h l _)

/-- The fold of `last` is at least the number of each thing. -/
private theorem toNat_le_foldl (h : ν → Int) : ∀ (l : List ν) (m : Nat) (v : ν), v ∈ l →
    (h v).toNat ≤ l.foldl (fun m v => max m (h v).toNat) m
  | [], _, _, hv => nomatch hv
  | w :: l, m, v, hv => by
    rw [List.foldl_cons]
    cases List.mem_cons.mp hv with
    | inl e =>
      rw [e]
      exact Nat.le_trans (Nat.le_max_right m _) (le_foldl_last h l _)
    | inr hl => exact toNat_le_foldl h l _ v hl

/-- No thing of the order stands after the last layer. -/
theorem toNat_le_last (h : ν → Int) {order : List ν} {v : ν} (hv : v ∈ order) :
    (h v).toNat ≤ last h order := toNat_le_foldl h order 0 v hv

/-- There is a row for each number up to the last, and none after. -/
theorem rows_length (h : ν → Int) (order : List ν) : (rows h order).length = last h order + 1 := by
  rw [rows, List.length_map, List.length_range]

/-- **The row `i` is the things of the order that stand at `i`**, in their order. -/
theorem rows_at {h : ν → Int} {order : List ν} {i : Nat} {row : List ν}
    (hi : (rows h order)[i]? = some row) :
    row = order.filter fun v => decide (h v = (i : Int)) := by
  rw [rows, List.getElem?_map] at hi
  cases Nat.lt_or_ge i (last h order + 1) with
  | inl lt =>
    rw [List.getElem?_range lt] at hi
    exact (Option.some.inj hi).symm
  | inr ge =>
    rw [List.getElem?_eq_none (by rw [List.length_range]; exact ge)] at hi
    exact nomatch hi

/-- **A thing is in the row of its number, and in no other.** -/
theorem mem_rows {h : ν → Int} {order : List ν} {i : Nat} {row : List ν}
    (hi : (rows h order)[i]? = some row) {v : ν} : v ∈ row ↔ v ∈ order ∧ h v = (i : Int) := by
  rw [rows_at hi, List.mem_filter, decide_eq_true_iff]

/-- **Each thing of the order that stands at `0` or later is in a row**: the row of its
number. -/
theorem rows_has {h : ν → Int} {order : List ν} {v : ν} (hv : v ∈ order) (h0 : 0 ≤ h v) :
    ∃ row, (rows h order)[(h v).toNat]? = some row ∧ v ∈ row := by
  have hl := toNat_le_last h hv
  refine ⟨order.filter fun w => decide (h w = (((h v).toNat : Nat) : Int)), ?_, ?_⟩
  · rw [rows, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hl)]
    rfl
  · rw [List.mem_filter, decide_eq_true_iff]
    exact ⟨hv, (Int.toNat_of_nonneg h0).symm⟩

/-- **A thing that stands before another is in an earlier row.** -/
theorem rows_lt {h : ν → Int} {order : List ν} {u v : ν} (hu : u ∈ order) (hv : v ∈ order)
    (h0 : 0 ≤ h u) (hlt : h u < h v) :
    ∃ (i j : Nat) (ri rj : List ν), i < j ∧ (rows h order)[i]? = some ri ∧
      (rows h order)[j]? = some rj ∧ u ∈ ri ∧ v ∈ rj := by
  obtain ⟨ri, hi, hui⟩ := rows_has hu h0
  obtain ⟨rj, hj, hvj⟩ := rows_has hv (Int.le_trans h0 (Int.le_of_lt hlt))
  refine ⟨_, _, ri, rj, ?_, hi, hj, hui, hvj⟩
  omega

/-- The numbers below `n` in their order have no number twice. -/
private theorem range_nodup : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨range_nodup n, List.pairwise_singleton _ _, fun a ha b hb e => ?_⟩
    have h1 : a < n := List.mem_range.mp ha
    have h2 : b = n := List.mem_singleton.mp hb
    omega

/-- The keys of the rows of some numbers, each number once, are distinct. -/
private theorem distinct_from {κ : Type} {key : ν → κ} {h : ν → Int} {order : List ν}
    (hd : (order.map key).Nodup) : ∀ ns : List Nat, ns.Nodup →
    ((ns.map fun (i : Nat) => order.filter fun v => decide (h v = (i : Int))).flatMap
      fun row => row.map key).Nodup
  | [], _ => List.nodup_nil
  | i :: ns, hn => by
    have nd := List.nodup_cons.mp hn
    rw [List.map_cons, List.flatMap_cons]
    refine List.nodup_append.mpr ⟨?_, distinct_from hd ns nd.2, fun a ha b hb e => ?_⟩
    · exact List.pairwise_map.mpr ((List.pairwise_map.mp hd).filter _)
    · obtain ⟨u, hu, eu⟩ := List.mem_map.mp ha
      obtain ⟨row, hrow, hb'⟩ := List.mem_flatMap.mp hb
      obtain ⟨j, hj, erow⟩ := List.mem_map.mp hrow
      rw [← erow] at hb'
      obtain ⟨v, hv, ev⟩ := List.mem_map.mp hb'
      have hu' := List.mem_filter.mp hu
      have hv' := List.mem_filter.mp hv
      have e1 : h u = (i : Int) := of_decide_eq_true hu'.2
      have e2 : h v = (j : Int) := of_decide_eq_true hv'.2
      have e3 : h u = h v :=
        congrArg h (eq_of_distinct key order hd u v hu'.1 hv'.1 (by rw [eu, ev]; exact e))
      have e4 : i = j := by omega
      exact nd.1 (e4 ▸ hj)

/-- **No thing is in two rows, and none is twice in a row**: where the keys of the order are
distinct, the keys of the rows, row after row, are distinct. -/
theorem rows_distinct {κ : Type} {key : ν → κ} (h : ν → Int) {order : List ν}
    (hd : (order.map key).Nodup) : ((rows h order).flatMap fun row => row.map key).Nodup :=
  distinct_from hd _ (range_nodup _)

/-- Rows that go down some links go down fewer. -/
theorem Down.mono {r : Reading ε ν} {links fewer : List ε} {rows : List (List ν)}
    (h : Down r links rows) (hs : ∀ e ∈ fewer, e ∈ links) : Down r fewer rows :=
  fun e he => h e (hs e he)

/-- **Rows may be put in another order.** Where each row of `rows` has its things in the row of
`rows'` at its place, and `rows` go down the links, `rows'` go down them. -/
theorem Down.members {r : Reading ε ν} {links : List ε} {rows rows' : List (List ν)}
    (h : Down r links rows)
    (hm : ∀ (i : Nat) (ri : List ν), rows[i]? = some ri →
      ∃ ri', rows'[i]? = some ri' ∧ ∀ v ∈ ri, v ∈ ri') : Down r links rows' := fun e he => by
  obtain ⟨i, j, ri, rj, hij, hi, hj, hs, hd⟩ := h e he
  obtain ⟨ri', hi', mi⟩ := hm i ri hi
  obtain ⟨rj', hj', mj⟩ := hm j rj hj
  exact ⟨i, j, ri', rj', hij, hi', hj', mi _ hs, mj _ hd⟩

/-- **The rows of the layers go down the links**, along an order that serves them, where each
link asks for a step of one at least. -/
theorem rows_down [DecidableEq ν] {r : Reading ε ν} {links : List ε} {order : List ν}
    (h : Serves r links order) (hs : ∀ e ∈ links, 1 ≤ r.sep e) :
    Down r links (rows (heights r links 0 order) order) := fun e he => by
  obtain ⟨i, j, _, hi, hj⟩ := h.2 e he
  have h1 := heights_meets h 0 he
  have h2 := hs e he
  exact rows_lt (List.mem_of_getElem? hi) (List.mem_of_getElem? hj)
    (heights_start r links 0 order (r.src e)) (by omega)

end Layers

namespace Layout

variable {α ε ν : Type}

section

variable [Moves IVec α]

/-- **Rows of parts, one row above the next.** In each row the parts stand side by side,
`across` apart, and the rows are `down` apart. -/
def layered (across down : Nat) (rows : List (List (Layout α))) : Layout α :=
  column down (rows.map (row across))

/-- **Each part of a layered picture stands in it**, at a step that is not negative. -/
theorem layered_stands {across down : Nat} {rows : List (List (Layout α))} {r : List (Layout α)}
    {a : Layout α} (hr : r ∈ rows) (ha : a ∈ r) :
    ∃ d : IVec, (layered across down rows).Stands d a ∧ 0 ≤ d.x ∧ 0 ≤ d.y := by
  obtain ⟨da, hda⟩ := rowParts_mem across ha
  obtain ⟨dr, hdr⟩ := columnParts_mem down (List.mem_map_of_mem (f := row across) hr)
  have h1 : 0 ≤ da.x ∧ da.y = 0 := rowParts_step across r _ hda
  have h2 : dr.x = 0 ∧ 0 ≤ dr.y := columnParts_step down _ _ hdr
  refine ⟨da + dr, (stands_row hda).trans (stands_column hdr), ?_, ?_⟩
  · show 0 ≤ da.x + dr.x
    have e1 := h1.1
    have e2 := h2.1
    omega
  · show 0 ≤ da.y + dr.y
    have e1 := h1.2
    have e2 := h2.2
    omega

/-- **A part of an earlier row ends the gap above every part of a later row.** Each of the two
stands in the picture, and the room of the first at its step ends `down` above the step of the
second. -/
theorem layered_below {across down : Nat} {rows : List (List (Layout α))} {i j : Nat}
    (hij : i < j) {ri rj : List (Layout α)} (hi : rows[i]? = some ri) (hj : rows[j]? = some rj)
    {a b : Layout α} (ha : a ∈ ri) (hb : b ∈ rj) :
    ∃ d e : IVec, (layered across down rows).Stands d a ∧ (layered across down rows).Stands e b ∧
      d.y + a.h + down ≤ e.y := by
  have hi' : (rows.map (row across))[i]? = some (row across ri) := by
    rw [List.getElem?_map, hi]
    rfl
  have hj' : (rows.map (row across))[j]? = some (row across rj) := by
    rw [List.getElem?_map, hj]
    rfl
  obtain ⟨di, hdi⟩ := columnParts_at down hi'
  obtain ⟨dj, hdj⟩ := columnParts_at down hj'
  obtain ⟨da, hda⟩ := rowParts_mem across ha
  obtain ⟨db, hdb⟩ := rowParts_mem across hb
  have hrows : di.y + ((row across ri).h : Int) + (down : Int) ≤ dj.y :=
    pairwise_at (columnParts_below down (rows.map (row across))) hij hdi hdj
  have hah : a.h ≤ (row across ri).h := row_h_le across ri a ha
  have ya : da.y = 0 := (rowParts_step across ri _ hda).2
  have yb : db.y = 0 := (rowParts_step across rj _ hdb).2
  refine ⟨da + di, db + dj,
    (stands_row hda).trans (stands_column (List.mem_of_getElem? hdi)),
    (stands_row hdb).trans (stands_column (List.mem_of_getElem? hdj)), ?_⟩
  show da.y + di.y + (a.h : Int) + (down : Int) ≤ db.y + dj.y
  omega

/-- **No thing is lost and none is made**: a reading that does not see a move, such as the key
of a thing, reads a layered picture as its parts one after another, row after row. -/
theorem layered_items_map {β : Type} {f : α → β}
    (hf : ∀ (d : IVec) (a : α), f (Moves.move d a) = f a) (across down : Nat)
    (rows : List (List (Layout α))) :
    (layered across down rows).items.map f =
      (rows.flatMap fun r => r.flatMap fun l => l.items).map f := by
  rw [layered, column_items_map hf]
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    show ((row across r).items ++ (rows.map (row across)).flatMap fun l => l.items).map f =
      ((r.flatMap fun l => l.items) ++ rows.flatMap fun r => r.flatMap fun l => l.items).map f
    rw [List.map_append, List.map_append, ih, row_items_map hf]

/-- **Every link goes down.** Over rows that go down the links, the part of the source of each
link and the part of its target stand in the picture, and the room of the first ends the gap
between rows above the second. -/
theorem layered_link {r : Layers.Reading ε ν} {links : List ε} {rows : List (List ν)}
    (hd : Layers.Down r links rows) (part : ν → Layout α) (across down : Nat) {e : ε}
    (he : e ∈ links) :
    ∃ d d' : IVec,
      (layered across down (rows.map fun row => row.map part)).Stands d (part (r.src e)) ∧
      (layered across down (rows.map fun row => row.map part)).Stands d' (part (r.dst e)) ∧
      d.y + (part (r.src e)).h + down ≤ d'.y := by
  obtain ⟨i, j, ri, rj, hij, hi, hj, hs, ht⟩ := hd e he
  have hi' : (rows.map fun row => row.map part)[i]? = some (ri.map part) := by
    rw [List.getElem?_map, hi]
    rfl
  have hj' : (rows.map fun row => row.map part)[j]? = some (rj.map part) := by
    rw [List.getElem?_map, hj]
    rfl
  exact layered_below hij hi' hj' (List.mem_map_of_mem hs) (List.mem_map_of_mem ht)

end

section

variable [Moves IVec α] [Boxed α]

/-- A layered picture fits where each of its parts fits. -/
theorem Fits.layered {across down : Nat} {rows : List (List (Layout α))}
    (h : ∀ r ∈ rows, ∀ l ∈ r, l.Fits) : (layered across down rows).Fits :=
  Fits.column down _ fun l hl => by
    obtain ⟨r, hr, e⟩ := List.mem_map.mp hl
    rw [← e]
    exact Fits.row across r (h r hr)

/-- **A layered picture is clear** where each of its parts fits and is clear: no two of its
things share room. -/
theorem Clear.layered {across down : Nat} {rows : List (List (Layout α))}
    (f : ∀ r ∈ rows, ∀ l ∈ r, l.Fits) (c : ∀ r ∈ rows, ∀ l ∈ r, l.Clear) :
    (layered across down rows).Clear :=
  Clear.column down _
    (fun l hl => by
      obtain ⟨r, hr, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact Fits.row across r (f r hr))
    fun l hl => by
      obtain ⟨r, hr, e⟩ := List.mem_map.mp hl
      rw [← e]
      exact Clear.row across r (f r hr) (c r hr)

end

end Layout

end Whatwg.Svg.Scene
