import Whatwg.Html.Print.Render
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Check
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Node.Table.Laws

/-!
# WhatwgTest.Html.Tables

The table of lean4-effect4's documents, on `Whatwg/Html/Node/Table.lean` (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entries W9, W13 and W14 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at `6ad8f7b8d`:

| The consumer's code | Here |
| --- | --- |
| `algebra.table`, `tools/Tools/Document/Html.lean`, lines 92 to 98: a table in its region, from headers and rows that are data | `Theirs.table`, with each cell's line already folded to nodes |
| the width check of `censusAlgebra`, `tools/Tools/Document.lean`, lines 149 to 151: "a row's width differs from its header" | `Theirs.widthProblem`; here the width is the type's |
| `page.css`, lines 121 to 133: the rules of a table, each with the fact it draws in a comment | `Table.headMark`, the fact of the head |

`table_raw` says that the typed table in its region erases to the consumer's node, for every
table with a row. The consumer checks that node when its program runs, and checks the widths
of the rows in a pass of its own; the typed table is checked when this module is compiled, and
a row of another width is no value of its type.

What this battery does not claim: that this is the consumer's file. Its fold of a line into
nodes is not restated: a cell here is any typed children.
-/

namespace WhatwgTest.Html.Tables

open Whatwg.Html
open Whatwg.Html.Content (Ctx)
open Whatwg.Html.Content.Structure (places placesOfFact Fact)

def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- Where a block of a page stands, and where a table stands in its region. -/
abbrev InMain : Ctx := Ctx.document.below [.html, .body, .main]
abbrev InScroll : Ctx := InMain.child .div

/-- A cell of a table of a page's block. -/
abbrev Cell : Type := List (Child (Table.cellCtx InScroll))

/-! ## The consumer's code -/

namespace Theirs

/-- `algebra.table`: nothing for a table with no row; else the table in a region that scrolls,
labelled by its columns. -/
def table (hs : List String) (rs : List (List (List RawNode))) : List RawNode :=
  if rs.isEmpty then [] else
    let head := el "thead" [el "tr" (hs.map fun h => el "th" [.text h] [("scope", "col")])]
    let body := el "tbody" (rs.map fun r => el "tr" (r.map fun c => el "td" c))
    [el "div" [el "table" [head, body]]
      [("class", "scroll"), ("role", "region"), ("tabindex", "0"),
       ("aria-label", "Table: " ++ ", ".intercalate hs)]]

/-- The width check of the consumer's census. -/
def widthProblem (hs : List String) (rs : List (List (List RawNode))) : Option String :=
  if rs.all (·.length == hs.length) then none
  else some s!"table [{", ".intercalate hs}]: a row's width differs from its header"

end Theirs

/-! ## The same on the package's table -/

/-- A table of a page's block: in its region, labelled by its columns. -/
def table {width : Nat} (t : Table InScroll width) : Child InMain :=
  E.el (Table.scrolling (t.name "Table: ") t (some "scroll"))

/-- **The typed table erases to the consumer's node**, for every table with a row, of every
width. -/
theorem table_raw {width : Nat} (t : Table InScroll width) (h : t.rows ≠ []) :
    [(table t).raw] = Theirs.table t.headers.toList t.rawRows := by
  have hmine : (table t).raw =
      regionRaw (t.name "Table: ") [tableRaw t.headers.toList t.rawRows] (some "scroll") :=
    Table.scrolling_toRaw _ _ _ _
  have hrows : t.rawRows.isEmpty = false := by
    unfold Table.rawRows
    cases hr : t.rows with
    | nil => exact absurd hr h
    | cons row rest => rfl
  rw [hmine, Theirs.table, hrows]
  rfl

/-- The claims of a page: two columns. -/
def claims : Table InScroll 2 :=
  ⟨#v["Claim", "Status"],
    [#v[[html! <code>"keys-once"</code>], [E.txt "proved"]], #v[[html! <code>"descent"</code>], [E.txt "open"]]]⟩

-- The consumer's text.
#guard Print.render (table claims).raw ==
  "<div class=\"scroll\" role=\"region\" tabindex=\"0\" aria-label=\"Table: Claim, Status\"><table>" ++
    "<thead><tr><th scope=\"col\">Claim</th><th scope=\"col\">Status</th></tr></thead><tbody>" ++
    "<tr><td><code>keys-once</code></td><td>proved</td></tr>" ++
    "<tr><td><code>descent</code></td><td>open</td></tr></tbody></table></div>"

-- The facts of a table that the consumer's sheet draws, on the typed table: the two header
-- cells, the four cells of the body, and the first cell of each row, the head's too.
#guard placesOfFact Fact.tableHead (table claims).raw == [[0, 0, 0, 0], [0, 0, 0, 1]]
#guard (placesOfFact Fact.bodyCell (table claims).raw).length == 4
#guard placesOfFact Fact.rowHead (table claims).raw == [[0, 0, 0, 0], [0, 1, 0, 0], [0, 1, 1, 0]]
#guard placesOfFact Fact.region (table claims).raw == [[]]

/-! ## The width of a row -/

/-- Reader of `isSome_ofLists?`: the package's table from lists is there exactly where the
consumer's check of the widths finds no problem. -/
theorem ofLists?_iff_theirs (hs : List String) (rs : List (List Cell)) :
    (Table.ofLists? (ctx := InScroll) hs rs).isSome =
      (Theirs.widthProblem hs (rs.map fun r => r.map fun c => c.map Child.raw)).isNone := by
  have htheirs : (Theirs.widthProblem hs (rs.map fun r => r.map fun c => c.map Child.raw)).isNone =
      rs.all fun r => r.length == hs.length := by
    unfold Theirs.widthProblem
    rw [List.all_map]
    have hsame : ((fun x : List (List RawNode) => x.length == hs.length) ∘
        fun r : List Cell => r.map fun c => c.map Child.raw) = fun r => r.length == hs.length :=
      funext fun r => by rw [Function.comp_apply, List.length_map]
    rw [hsame]
    cases rs.all fun r => r.length == hs.length <;> rfl
  rw [htheirs, Bool.eq_iff_iff, Table.isSome_ofLists?, List.all_eq_true]
  exact forall_congr' fun r => forall_congr' fun _ => beq_iff_eq.symm

-- Rows that are lists enter once: a table of the width of the headers, or nothing.
#guard ((Table.ofLists? (ctx := InScroll) ["Claim", "Status"] [[[E.txt "keys-once"], [E.txt "proved"]]]).map
    fun t => Print.render (table t).raw).isSome
#guard (Table.ofLists? (ctx := InScroll) ["Claim", "Status"] [[[E.txt "keys-once"]]]).isNone

-- Control: a row of one cell is no row of a table of two columns. The consumer finds this
-- when its program runs (`widthProblem`); here the definition is not accepted.
/--
error: Application type mismatch: The argument
  #v[cell]
has type
  Vector Cell 1
but is expected to have type
  Vector (List (Child (Table.cellCtx InScroll))) 2
in the application
  List.cons #v[cell]
-/
#guard_msgs in
example (cell : Cell) : Table InScroll 2 := ⟨#v["Claim", "Status"], [#v[cell]]⟩

#guard (Theirs.widthProblem ["Claim", "Status"] [[[.text "keys-once"]]]).isSome

/-! ## Readers of the laws -/

/-- Reader of `head_mem_places_scrolling`: **`Structure.places` finds the head of every table
of a page**: each column's header cell is a place of the fact `tableHead`, for every table and
every column. -/
theorem head_found {width : Nat} (t : Table InScroll width) {k : Nat} (hk : k < width) :
    [0, 0, 0, k] ∈ places Table.headMark (table t).raw := by
  have hraw : (table t).raw =
      regionRaw (t.name "Table: ") [tableRaw t.headers.toList t.rawRows] (some "scroll") :=
    Table.scrolling_toRaw _ _ _ _
  rw [hraw]
  exact Table.head_mem_places_scrolling _ _ _ _ (by rw [Vector.length_toList]; exact hk)

-- Reader of `ofLists?_eq_some`: the table that enters holds the headers and the rows given.
example (hs : List String) (rs : List (List Cell)) (t : Table InScroll hs.length)
    (h : Table.ofLists? hs rs = some t) : t.headers.toList = hs :=
  (Table.ofLists?_eq_some h).1

/-! ## Controls -/

-- Control: a table may not stand below a `caption`: the test of the position is false there.
#guard !((Ctx.flow.child .table).child .caption |>.child .div).admits .table

-- Control: a cell takes flow content, and a table's row takes nothing but cells: a paragraph
-- is no child of a row.
#guard (Child.check? (ctx := ((InScroll.child .table).child .tbody).child .tr) (el "p" [.text "x"])).isNone
#guard (Child.check? (ctx := Table.cellCtx InScroll) (el "p" [.text "x"])).isSome

end WhatwgTest.Html.Tables
