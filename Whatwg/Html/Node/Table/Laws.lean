import Whatwg.Html.Node.Table
import Whatwg.Html.Content.Structure

/-!
# Whatwg.Html.Node.Table.Laws

Owner: where the head of a table of `Whatwg/Html/Node/Table.lean` stands, as a fact of
`Whatwg/Html/Content/Structure.lean` (the HTML half of entry W14 of
`docs/research/2026-10-12-whatwg-requests.md`).

- `placesOf_headRaw`: the fact `Structure.Fact.tableHead` holds in the head at each header
  cell and nowhere else: the k-th header cell is at the path `[0, k]` of the head, its row and
  the cell.
- `head_mem_places`: so in the table each header cell is a place of the fact, at
  `[0, 0, k]`, and `head_mem_places_scrolling`: in the table's region, at `[0, 0, 0, k]`. A
  sheet's rule for a table's head draws those cells.

What the laws do not say: that the fact holds nowhere else in the table. A cell of the body
holds what the caller puts in it, and a table inside a cell has header cells of its own.
-/

namespace Whatwg.Html.Table

open Whatwg.Html.Content
open Whatwg.Html.Content.Structure (Spot Where places placesOf placesAmong)

/-- The place of a header cell: the fact `Structure.Fact.tableHead`, a `th`. -/
def headMark : Where := Structure.Fact.tableHead.place

/-- The places of the fact among header cells in a row: each cell, at its index. -/
theorem placesAmong_headCells (chain : List Spot) : ∀ (headers : List String) (index before : Nat),
    placesAmong headMark chain index before (headers.map headCellRaw) =
      (List.range' index headers.length).map fun k => [k]
  | [], _, _ => by
    rw [List.map_nil, placesAmong]
    rfl
  | words :: rest, index, before => by
    have hcell : placesOf headMark chain before (Structure.elementCount (rest.map headCellRaw))
        (headCellRaw words) = [[]] := by
      rw [headCellRaw, placesOf, placesAmong, placesOf, placesAmong]
      rfl
    rw [List.map_cons, placesAmong, hcell, placesAmong_headCells chain rest, List.length_cons,
      List.range'_succ]
    rfl

/-- **Where the head of a table is**: the fact `tableHead` holds in the head at each header
cell, the k-th at the path `[0, k]`, and nowhere else. -/
theorem placesOf_headRaw (headers : List String) (above : List Spot) (before after : Nat) :
    placesOf headMark above before after (headRaw headers) =
      (List.range headers.length).map fun k => [0, k] := by
  have hhead : headMark.holds (⟨"thead", [], before, after⟩ :: above) = false := rfl
  have hrow : ∀ chain, headMark.holds (⟨"tr", [], 0, Structure.elementCount []⟩ :: chain) = false :=
    fun _ => rfl
  rw [headRaw, placesOf, hhead, placesAmong, placesOf, hrow, placesAmong_headCells, placesAmong,
    List.range_eq_range']
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, List.map_map]
  rfl

/-- Each header cell is a place of the fact below the table, wherever the table stands. -/
theorem head_mem_placesOf (headers : List String) (rows : List (List (List RawNode)))
    (above : List Spot) (before after : Nat) {k : Nat} (hk : k < headers.length) :
    [0, 0, k] ∈ placesOf headMark above before after (tableRaw headers rows) := by
  have htable : headMark.holds (⟨"table", [], before, after⟩ :: above) = false := rfl
  rw [tableRaw, placesOf, htable, placesAmong, placesOf_headRaw]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [List.map_map]
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

/-- **`Structure.places` finds the head of a table**: each header cell is a place of the fact
`tableHead`, the k-th at the path `[0, 0, k]`: the head, its row, the cell. -/
theorem head_mem_places (headers : List String) (rows : List (List (List RawNode))) {k : Nat}
    (hk : k < headers.length) : [0, 0, k] ∈ places headMark (tableRaw headers rows) :=
  head_mem_placesOf headers rows [] 0 0 hk

/-- The same for a table in its region: the k-th header cell is at `[0, 0, 0, k]`. -/
theorem head_mem_places_scrolling (name : Region.Name) (headers : List String)
    (rows : List (List (List RawNode))) (className : Option String) {k : Nat}
    (hk : k < headers.length) :
    [0, 0, 0, k] ∈ places headMark (regionRaw name [tableRaw headers rows] className) := by
  rw [places, regionRaw, placesOf, placesAmong]
  exact List.mem_append_right _ (List.mem_append_left _
    (List.mem_map.mpr ⟨[0, 0, k], head_mem_placesOf headers rows _ _ _ hk, rfl⟩))

end Whatwg.Html.Table
