import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Scene.Label

/-! A probe of labels fitted to rooms (`Whatwg/Svg/Scene/Metrics.lean` and `Label.lean`). Run it
from the repository root after `lake build`:

    lake env lean workshop/LabelProbe.lean

It writes `docs/research/2026-10-12-motion-probe/label.html`. No module imports this file, and no
gate reads its output.

The data is eight qualified names such as a picture of a program holds, in lean4-effect4's grid
of cells eight pixels wide. A name is cut at its dots into pieces, and a later piece matters
more: the last names the thing. The page shows every name in rooms of six widths, one table for
each of two ways:

1. each label fitted by itself (`Label.fit`);
2. the labels of the picture fitted together (`Label.fitAll`).

Under each table it prints, for each room, how many pairs of different names are shown as one
text. `Label.fitAll_distinct` says that the second way has none. -/

open Whatwg.Html
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- The cell of the grid, in thousandths of a pixel. -/
def cell : Nat := 8000

/-- The face of the grid: every character one cell wide. It needs no host. -/
def grid : Metrics := Metrics.mono cell 12000 4000

def names : List String :=
  ["Effect.forkDaemon", "Effect.fork", "Stream.mapEffect", "Sink.mapEffect",
    "Schedule.exponential", "Effect4.Program.NativeEff.bind", "Fiber.interruptFrom", "Fiber.await"]

/-- A qualified name as pieces: it is cut after each dot, a line may end there, and a later
piece matters more. -/
def pieces (name : String) : List (Piece String) :=
  let parts := name.splitOn "."
  let n := parts.length
  Label.ofTexts grid (parts.zipIdx.map fun (p, i) =>
    if i + 1 < n then (p ++ ".", i + 1, true) else (p, n + 1, false))

/-- The rooms, in cells. -/
def rooms : List Nat := [5, 9, 12, 16, 22, 30]

/-- The lines of a form as texts: a mark is written `…`, a sign `·`. -/
def lines : Shown String → List String
  | .whole ls => ls.map String.join
  | .cut ls => ls.map fun l => String.join (l.map fun
      | some s => s
      | none => "…")
  | .sign => ["·"]
  | .none => [""]

/-- The labels in a room of `cells` cells and one line: each by itself, or together. -/
def fitted (together : Bool) (cells : Nat) : List (Shown String) :=
  let labels := names.map pieces
  if together then Label.fitAll (cells * cell) 1 cell labels
  else labels.map (Label.fit (cells * cell) 1 cell)

/-- How many pairs of different names have one text. -/
def collisions (shown : List (Shown String)) : Nat :=
  let texts := shown.map Shown.text
  ((List.range texts.length).map fun i =>
    ((List.range i).filter fun j =>
      (texts.getD i none).isSome && texts.getD i none == texts.getD j none).length).sum

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d
def dim : Rgb := .ofNat 0x8a8176
def warn : Rgb := .ofNat 0xe0a458
def boxInk : Rgb := .ofNat 0x2a2520

def face (colour : Rgb) : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb colour), .xmlSpacePreserve]

/-- The left edge of each room's column. -/
def columns : List (Nat × Int) :=
  (rooms.foldl (fun (acc : List (Nat × Int) × Int) (r : Nat) =>
      (acc.1 ++ [(r, acc.2)], acc.2 + (r : Int) * 8 + 28))
    ([], 16)).1

/-- One table: a column for each room, a row for each name. A whole label is drawn in the ink,
a cut one in amber, a sign dim. -/
def table (together : Bool) : SvgNode :=
  let width : Nat := 16 + (rooms.map fun r => r * 8 + 28).sum
  let height : Nat := 28 + names.length * 30
  Svg.svg
    [.attr .width (.user (.ofNat width)), .attr .height (.user (.ofNat height)),
      .attr .viewBox (ViewBox.ofSize width height)]
    (Svg.box (.ofSize ⟨0, 0⟩ width height) [.fill (.rgb ground)] ::
      columns.flatMap fun (r, x) =>
        Svg.label ⟨(x : Rat), 16⟩ (toString r ++ " cells") (face dim) ::
          (fitted together r).zipIdx.flatMap fun (s, row) =>
            let y : Int := 26 + row * 30
            let colour := match s with
              | .whole _ => ink
              | .cut _ => warn
              | _ => dim
            [Svg.loops [Cubic.roundRect (.ofSize ⟨x, y⟩ (r * 8 + 12) 24) 4] [.fill (.rgb boxInk)],
              Svg.label ⟨(x : Rat) + 6, (y : Rat) + 17⟩ ((lines s).headD "") (face colour)])

def verdict (together : Bool) : String :=
  "<p>Pairs of different names shown as one text, room by room: <b>" ++
    ", ".intercalate (rooms.map fun r => toString (collisions (fitted together r))) ++ "</b>.</p>\n"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>Labels in rooms</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">Labels in rooms</h1>\n" ++
    "<p>Eight names, each in rooms of six widths. A whole label is white, a cut one amber, " ++
    "and a dot says that the thing is there and its name is not shown.</p>\n" ++
    "<h2 style=\"font-weight:400\">1. Each label fitted by itself</h2>\n" ++
    (table false).render ++ "\n" ++ verdict false ++
    "<h2 style=\"font-weight:400\">2. The labels of the picture fitted together</h2>\n" ++
    (table true).render ++ "\n" ++ verdict true ++ "</body>\n"

#eval rooms.map fun r => (r, collisions (fitted false r), collisions (fitted true r),
  (fitted true r).map fun s => (lines s).headD "")
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/label.html" page
