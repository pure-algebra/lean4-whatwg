import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Stroke
import Whatwg.Svg.Geometry.Stack
import Whatwg.Svg.Scene.Branch

/-! A probe of widths that conserve (module M4 of
`docs/research/2026-10-12-pictures-craft-modules.md`). Run it from the repository root after
`lake build`:

    lake env lean workshop/BranchProbe.lean

It writes `docs/research/2026-10-12-motion-probe/branch.html`. No module imports this file, and
no gate reads its output.

A trunk forks in two. Each branch carries half of what the trunk carries. The page draws the
fork four times as small panels: the exponent of the widths at 1 (widths add, as in a flow
diagram) and at 2 (Leonardo's rule: the squares of the widths add), and the wobble of the
organic stroke at 350 per mille, which is lean4-effect4's default look, and at 150.

A width means a share of the work, so a branch must not look as wide as its trunk. Under each
panel the page prints the narrowest place of the trunk and the widest place of a branch, by
the kit's own half-width (`Stroke.organic`) at every pixel along the lines, and the room that
`Branch.wobbleRoom` gives the two widths. Where the wobble is within the room the branch is
narrower than the trunk at every point (`Branch.wobbleRoom_apart`). Where it is not, the page
shows the places. -/

open Whatwg.Html
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- The width of the trunk, in thousandths of a pixel. -/
def trunk : Nat := 9000

/-- The width of a line with a share, in pixels. -/
def widthOf (k : Nat) (s : Share) : Rat := (Share.width k trunk s : Rat) / 1000

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d
def warn : Rgb := .ofNat 0xe0a458

/-- The trunk and its two branches, as centre lines. The branches leave the fork at the ports
of a row of their widths. -/
def lines (k : Nat) : List (String × Share × List Cubic) :=
  let half := (Share.whole.split [1, 1])
  let ws := half.map (widthOf k)
  let ps := ports 170 ws
  let ends : List Vec := [⟨70, 250⟩, ⟨270, 250⟩]
  ("trunk", Share.whole, [Cubic.line ⟨170, 20⟩ ⟨170, 120⟩]) ::
    (half.zip (ps.zip ends)).zipIdx.map fun ((s, port, b), i) =>
      ("branch " ++ toString i, s, (Curve.bumpY (1 / 2)).cubics [⟨port, 120⟩, b])

/-- The two half-widths of a line, as functions of the length run. -/
def sides (key : String) (w amp : Rat) : (Rat → Rat → Rat) × (Rat → Rat → Rat) :=
  let seed := Noise.seedOf key
  (Stroke.organic seed (w / 2) amp 40, Stroke.organic (seed + 7) (w / 2) amp 40)

/-- The least and the greatest width of a line over every pixel of its length. -/
def widthRange (key : String) (w amp : Rat) (line : List Cubic) : Rat × Rat :=
  let whole := Stroke.total (Stroke.samples line)
  let (r, l) := sides key w amp
  ((List.range (whole.floor.toNat + 1)).map fun (i : Nat) => r i whole + l i whole).foldl
    (fun acc x => (min acc.1 x, max acc.2 x)) (w * 10, 0)

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat 12),
    .fill (.rgb ink), .xmlSpacePreserve]

/-- A number of pixels at two places. -/
def px (q : Rat) : String := toString (Decimal.ofRat q 2).trim

/-- One panel and what it measures. -/
def panel (k : Nat) (amp : Nat) : String :=
  let a : Rat := (amp : Rat) / 1000
  let ls := lines k
  let ranges := ls.map fun (key, s, line) => (key, widthRange key (widthOf k s) a line)
  let trunkLeast := (ranges.head?.map fun x => x.2.1).getD 0
  let branchMost := (ranges.drop 1).foldl (fun m x => max m x.2.2) 0
  let n := Share.width k trunk ⟨1, 2⟩
  let room := Branch.wobbleRoom n (Share.width k trunk Share.whole)
  let bad := trunkLeast ≤ branchMost
  let svg :=
    Svg.svg
      [.attr .width (.user (.ofNat 340)), .attr .height (.user (.ofNat 270)),
        .attr .viewBox (ViewBox.ofSize 340 270)]
      (Svg.box (.ofSize ⟨0, 0⟩ 340 270) [.fill (.rgb ground)] ::
        ls.map fun (key, s, line) =>
          let (r, l) := sides key (widthOf k s) a
          Svg.loops [Stroke.stroke line r l] [.fill (.rgb (if bad then warn else ink))])
  "<figure style=\"display:inline-block;margin:0 16px 24px 0;vertical-align:top\">" ++ svg.render ++
    "<figcaption style=\"font:13px Georgia,serif;max-width:340px\">exponent " ++ toString k ++
    ", wobble " ++ toString amp ++ " per mille. Widths " ++
    px (widthOf k Share.whole) ++ " and " ++ px (widthOf k ⟨1, 2⟩) ++ " pixels; the room is " ++
    toString room ++ " per mille. Narrowest trunk " ++ px trunkLeast ++ ", widest branch " ++
    px branchMost ++ (if bad then ": <b>a branch is in places as wide as the trunk</b>."
      else ": the trunk is the wider at every point.") ++ "</figcaption></figure>"

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>Widths that conserve</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">Widths that conserve</h1>\n" ++
    "<p>A trunk forks in two, and each branch carries half. Four panels at one scale: the " ++
    "exponent of the widths across, the wobble of the stroke down.</p>\n" ++
    "<div>" ++ panel 1 350 ++ panel 2 350 ++ "</div>\n<div>" ++ panel 1 150 ++ panel 2 150 ++
    "</div>\n</body>\n"

#eval [1, 2].map fun k => (k, Share.width k trunk Share.whole, Share.width k trunk ⟨1, 2⟩,
  Branch.wobbleRoom (Share.width k trunk ⟨1, 2⟩) (Share.width k trunk Share.whole))
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/branch.html" page
