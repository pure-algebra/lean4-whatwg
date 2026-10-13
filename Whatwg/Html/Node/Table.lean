import Whatwg.Html.Node.Region
import Whatwg.Html.Node.Run
import Whatwg.Html.Node.Check

/-!
# Whatwg.Html.Node.Table

Owner: a table with its head, typed (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; entries W9 and
W13 of `docs/research/2026-10-12-whatwg-requests.md`). A table of a document is data: the
words of its columns and its rows. A writer of pages makes of it a `table` with a `thead` whose
cells say that they head a column, a `tbody` of rows, and around it a region that scrolls where
the table is wider than its page.

```
def claims : Table (InMain.child .div) 2 :=
  ⟨#v["Claim", "Status"], [#v[[E.txt "keys-once"], [E.txt "proved"]], #v[[E.txt "descent"], [E.txt "open"]]]⟩

Table.scrolling (claims.name "Table: ") claims (some "scroll")
-- <div class="scroll" role="region" tabindex="0" aria-label="Table: Claim, Status">
--   <table><thead><tr><th scope="col">Claim</th><th scope="col">Status</th></tr></thead>
--     <tbody><tr><td>keys-once</td><td>proved</td></tr>…</tbody></table></div>
```

- `Table ctx width` is a table of `width` columns that stands at `ctx`: the words of its header
  cells, and its rows. A row is a `Vector` of `width` cells, so a row of another width is no
  row of the table: the check "a row's width differs from its header" is the type's.
  `Table.ofLists?` makes that check once for rows that are lists, where data enters.
- `Table.element` is the `table`. Its content model is ordered (a head, then bodies), so its
  children are a run (`Whatwg/Html/Node/Run.lean`). `Table.scrolling name t` is the table in a
  region (`Whatwg/Html/Node/Region.lean`), and `Table.name` a name for it from its columns.
- `tableRaw` is the same tree as a raw node, for a fold of data, and `element_toRaw`,
  `scrolling_toRaw` say that the typed forms write it.

What is proved once. A `table` takes a `thead` and a `tbody`, each takes rows, and a row takes
its cells, wherever the table stands; `th` takes `scope="col"`. What is left is the content of
a cell, typed at the position of a cell (`Table.cellCtx`), and one closed test where the table
is placed: that the position takes a `table`.

`Whatwg/Html/Node/Table/Laws.lean` says where the fact `Structure.Fact.tableHead` holds: at
each header cell.

The basis: the content models of `table`, `thead`, `tbody` and `tr`, and `scope` of `th` with
its keyword `col`, are the HTML Standard's (sections "The table element" to "The th element",
`vendor/whatwg-html-746f2ede/source`). That a wide table stands in a region that takes the
keyboard is the convention of `Region.lean`.

What this module does not claim:

- A caption, column groups, a foot, row headers, or cells that span. A table here is a head of
  one row and one body.
- That a table has a row. A table with no row is a head and an empty body.
- The table model's own rules (that no two cells overlap): with no cell that spans, a row of
  `width` cells under `width` header cells has none to break.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema
open Whatwg.Html.Content (Ctx validIn validAll)

/-- The position of the content of a body cell of a table that stands at `ctx`. -/
abbrev Table.cellCtx (ctx : Ctx) : Ctx := (((ctx.child .table).child .tbody).child .tr).child .td

/-- **A table of `width` columns** that stands at `ctx`: the words of its header cells, and its
rows, each `width` cells. A cell is typed children of the position of a cell. -/
structure Table (ctx : Ctx) (width : Nat) where
  headers : Vector String width
  rows : List (Vector (List (Child (Table.cellCtx ctx))) width)

namespace Table

variable {ctx : Ctx} {width : Nat}

/-! ## The raw tree -/

/-- A header cell as a raw node: a `th` that heads its column. -/
def headCellRaw (words : String) : RawNode := .element "th" [("scope", "col")] [.text words]

/-- The head as a raw node: one row of header cells. -/
def headRaw (headers : List String) : RawNode :=
  .element "thead" [] [.element "tr" [] (headers.map headCellRaw)]

/-- A row of the body as a raw node. -/
def rowRaw (row : List (List RawNode)) : RawNode :=
  .element "tr" [] (row.map fun cell => .element "td" [] cell)

/-- The body as a raw node. -/
def bodyRaw (rows : List (List (List RawNode))) : RawNode := .element "tbody" [] (rows.map rowRaw)

/-- The table as a raw node, for a fold of data: the head, then the body. -/
def _root_.Whatwg.Html.tableRaw (headers : List String) (rows : List (List (List RawNode))) : RawNode :=
  .element "table" [] [headRaw headers, bodyRaw rows]

/-! ## The typed tree -/

/-- A header cell, among the cells of the head's row. -/
def headCell (words : String) : Child (((ctx.child .table).child .thead).child .tr) :=
  Child.of
    (Element.ofChildren (t := .th)
      [Child.text words (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide))]
      [⟨.scope, "scope", "col"⟩] (Content.elementOk_of_seq_none rfl _ (by decide +kernel) _))
    (Content.Ctx.admitsWith_unread _ .th _ (by decide)
      (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide)))

/-- A cell of the body, among the cells of its row. -/
def bodyCell (content : List (Child (cellCtx ctx))) :
    Child (((ctx.child .table).child .tbody).child .tr) :=
  Child.of (Element.ofChildren (t := .td) content [] (Content.elementOk_of_seq_none rfl _ rfl _))
    (Content.Ctx.admitsWith_unread _ .td _ (by decide)
      (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide)))

/-- A row of the body, among the rows of the body. -/
def bodyRow (row : Vector (List (Child (cellCtx ctx))) width) : Child ((ctx.child .table).child .tbody) :=
  Child.of
    (Element.ofChildren (t := .tr) (row.toList.map bodyCell) []
      (Content.elementOk_of_seq_none rfl _ rfl _))
    (Content.Ctx.admitsWith_unread _ .tr _ (by decide)
      (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide)))

/-- The head: one row of header cells. -/
def head (t : Table ctx width) : Element .thead (ctx.child .table) :=
  Element.ofChildren
    [Child.of
      (Element.ofChildren (t := .tr) (t.headers.toList.map headCell) []
        (Content.elementOk_of_seq_none rfl _ rfl _))
      (Content.Ctx.admitsWith_unread _ .tr _ (by decide)
        (Content.Ctx.admits_child_of_noHits _ (by decide) (by decide) (by decide)))]
    [] (Content.elementOk_of_seq_none rfl _ rfl _)

/-- The body: the rows. -/
def body (t : Table ctx width) : Element .tbody (ctx.child .table) :=
  Element.ofChildren (t.rows.map bodyRow) [] (Content.elementOk_of_seq_none rfl _ rfl _)

/-- **The table**: its head, then its body. The ordered model of `table` is followed by a run
of the two, for every position. -/
def element (t : Table ctx width) : Element .table ctx :=
  Element.ofRun
    ((Run.el t.head
        (Content.Ctx.admitsWith_unread _ .thead _ (by decide)
          (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))).append
      (Run.el t.body
        (Content.Ctx.admitsWith_unread _ .tbody _ (by decide)
          (Content.Ctx.admits_child_of_noHits ctx (by decide) (by decide) (by decide)))))
    [] rfl

/-- The rows of a table as raw nodes: each cell's nodes. -/
def rawRows (t : Table ctx width) : List (List (List RawNode)) :=
  t.rows.map fun row => row.toList.map fun cell => cell.map Child.raw

/-- The typed table writes the raw one. -/
theorem element_toRaw (t : Table ctx width) : t.element.toRaw = tableRaw t.headers.toList t.rawRows := by
  have hnodes : t.element.toRaw =
      .element "table" []
        [.element "thead" [] [.element "tr" [] ((t.headers.toList.map (headCell (ctx := ctx))).map Child.raw)],
          .element "tbody" [] ((t.rows.map bodyRow).map Child.raw)] := rfl
  have hrow : ∀ row : Vector (List (Child (cellCtx ctx))) width,
      (bodyRow row).raw = rowRaw (row.toList.map fun cell => cell.map Child.raw) := fun row => by
    show RawNode.element "tr" [] ((row.toList.map bodyCell).map Child.raw) = _
    rw [List.map_map, rowRaw, List.map_map]
    rfl
  rw [hnodes, List.map_map, List.map_map, tableRaw, headRaw, bodyRaw, rawRows, List.map_map]
  congr 3
  exact congrArg (RawNode.element "tbody" []) (List.map_congr_left fun row _ => hrow row)

/-! ## In a region that scrolls -/

/-- A name for the region of a table, from the words of its columns after a lead:
`t.name "Table: "` is `aria-label="Table: Claim, Status"`. -/
def name (t : Table ctx width) (lead : String := "") : Region.Name :=
  .label (lead ++ ", ".intercalate t.headers.toList)

/-- **The table in a region that scrolls**: a `div` that takes the keyboard and has a name,
around the table. Owed: one closed test, that the region takes a `table`. -/
def scrolling (name : Region.Name) (t : Table (ctx.child .div) width)
    (className : Option String := none)
    (htable : (ctx.child .div).admits .table = true := by decide) : Element .div ctx :=
  region name [Child.of t.element (Content.Ctx.admitsWith_unread _ .table _ (by decide) htable)]
    className

/-- The typed region writes the raw one, around the raw table. -/
theorem scrolling_toRaw (name : Region.Name) (t : Table (ctx.child .div) width)
    (className : Option String) (htable : (ctx.child .div).admits .table = true) :
    (scrolling name t className htable).toRaw =
      regionRaw name [tableRaw t.headers.toList t.rawRows] className := by
  rw [← element_toRaw]
  rfl

/-! ## Rows that are lists -/

/-- **A table from lists**, when each row has as many cells as there are headers; none
otherwise. The check of a row's width, made once, where the data enters. -/
def ofLists? (headers : List String) (rows : List (List (List (Child (cellCtx ctx))))) :
    Option (Table ctx headers.length) :=
  if h : ∀ row ∈ rows, row.length = headers.length then
    some ⟨⟨headers.toArray, List.size_toArray⟩,
      rows.attach.map fun row => ⟨row.1.toArray, List.size_toArray.trans (h row.1 row.2)⟩⟩
  else none

/-- `ofLists?` answers exactly when every row has the width of the headers. -/
theorem isSome_ofLists? (headers : List String)
    (rows : List (List (List (Child (cellCtx ctx))))) :
    (ofLists? headers rows).isSome = true ↔ ∀ row ∈ rows, row.length = headers.length := by
  unfold ofLists?
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun hsome => Bool.noConfusion hsome, fun hall => absurd hall h⟩

/-- The table that `ofLists?` answers holds the headers and the rows given. -/
theorem ofLists?_eq_some {headers : List String}
    {rows : List (List (List (Child (cellCtx ctx))))} {t : Table ctx headers.length}
    (h : ofLists? headers rows = some t) :
    t.headers.toList = headers ∧ t.rows.map Vector.toList = rows := by
  unfold ofLists? at h
  split at h
  · cases Option.some.inj h
    refine ⟨rfl, ?_⟩
    rw [List.map_map]
    exact List.attach_map_subtype_val rows
  · exact nomatch h

end Table

end Whatwg.Html
