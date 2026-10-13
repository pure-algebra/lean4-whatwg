import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline
import Whatwg.Svg.Geometry.Stroke.Laws
import Whatwg.Svg.Geometry.Stack
import Whatwg.Svg.Scene.Tree.Edit
import Whatwg.Svg.Scene.Stage

/-! A probe of a tree that grows (slice S13 of `docs/SVG-PACKAGE-PLAN.md`), with data like
lean4-effect4's. Run it from the repository root after `lake build`:

    lake env lean workshop/TreeProbe.lean

It writes `docs/research/2026-10-12-motion-probe/tree.html`. No module imports this file, and
no gate reads its output.

The data is the tree of the program `pFork` of lean4-effect4, with its keys and its nodes: the
tree before the body of the fork is written, and the tree after. Each node stands over the
middle of its leaves, by the kit's `Tree.spans`. A node keeps its key from one
tree to the next. In the step between them a kept node moves to its new place, a kept edge
changes its shape so that it stays joined to both its nodes while they move, a new edge draws
itself from its parent, and then the new node at its end grows. New things enter level by
level.

An edge is an organic stroke. Its width says how much of the tree hangs below it, by
Leonardo's rule: the widths of the branches at a fork, squared, sum to the width of the trunk,
squared. So a width is the root of a share of the leaves. -/

open Whatwg.Html
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene
open Whatwg.Svg.Value

/-- A node of a program: its key and its label. -/
abbrev Node : Type := String × String

/-- A node with its place: its span among the leaves, by the kit's `Tree.spans`. A leaf takes
one column, and a node stands over the middle of its leaves. -/
structure Placed where
  key : String
  label : String
  span : Span

def placedOf (t : Tree Node) : List Placed := (t.spans 0 0).map fun (v, s) => ⟨v.1, v.2, s⟩

def treeBefore : Tree Node :=
  .node ("[]", "bind") [
    .node ("[0]", "withFiber") [.node ("[0 0]", "fork") []],
    .node ("[1]", "awaitFiber") []]

/-- The address of the fork: the first child of the first child of the root. -/
def forkAt : List Nat := [0, 0]

/-- The fork with its body written. -/
def forkWritten : Tree Node :=
  .node ("[0 0]", "fork") [
    .node ("[0 0 0]", "bind") [
      .node ("[0 0 0 0]", "yieldNow 0") [],
      .node ("[0 0 0 1]", "succeed (lit 7)") []]]

/-- The tree after the edit: the subtree at the fork is replaced, and nothing else
(`Tree.replace` of `Whatwg/Svg/Scene/Tree/Edit.lean`). -/
def treeAfter : Tree Node := Tree.replace forkWritten forkAt treeBefore

/-- **What the edit does to a node of the new picture**, read from the two spans by the
relations of `Tree.spans_replace`: a node of the new subtree; a node before the edit, as it
was; a node on the way to the address, stretched; a node after the edit, shifted. -/
def groupOf (p : Placed) : String :=
  let col := Tree.column 0 forkAt treeBefore
  let gain := forkWritten.leaves
  let loss := ((Tree.subtree? forkAt treeBefore).map Tree.leaves).getD 0
  match (placedOf treeBefore).find? fun o => o.key == p.key with
  | none => "of the new subtree"
  | some o =>
    if forkAt.length ≤ o.span.depth ∧ col ≤ o.span.first ∧ o.span.last < col + loss then
      "of the new subtree"
    else if o.span.last < col then "as it was"
    else if decide (Span.Stretched gain loss o.span p.span) then "stretched"
    else if decide (Span.Shifted gain loss o.span p.span) then "shifted"
    else "in no group"

/-- The nodes of the new picture, group by group. -/
def groups : List (String × List String) :=
  ["as it was", "stretched", "shifted", "of the new subtree", "in no group"].filterMap fun g =>
    match ((placedOf treeAfter).filter fun p => groupOf p == g).map fun p => p.label with
    | [] => none
    | labels => some (g, labels)
/-! ## A tree as marks -/

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d

/-- The middle of a node. -/
def centre (p : Placed) : Vec :=
  ⟨140 + 85 * (p.span.middle2 : Rat), 50 + 84 * (p.span.depth : Rat)⟩

/-- The box of a node: as wide as its label asks. -/
def nodeBox (p : Placed) : Box :=
  let w : Rat := 8 * (p.label.length : Rat) + 20
  .ofSize ⟨(centre p).x - w / 2, (centre p).y - 13⟩ w 26

/-- The width of the edge to a node: the trunk's width times the root of the node's share of
the leaves, and the finest width at least. -/
def edgeWidth (leaves total : Nat) : Rat :=
  max (6 / 5) (5 * sqrtDown ((leaves : Rat) / (total : Rat)) 3)

/-- What a new mark does as it enters. -/
inductive Kind where
  | box | edge

/-- A mark: a key, a place, its depth, its shape if it is an edge, and its element under
attributes of motion. `fresh` is the element of a mark that enters. -/
structure Mark where
  key : String
  place : Vec
  depth : Nat
  kind : Kind
  shape : List Cubic
  node : ({t : Tag} → List (SvgAttr t)) → SvgNode
  fresh : ({t : Tag} → List (SvgAttr t)) → SvgNode

def face : List (SvgAttr .text) :=
  [.fontFamily "Menlo, 'DejaVu Sans Mono', monospace", .fontSize (Decimal.ofRat (1661 / 125)),
    .fill (.rgb ink), .textAnchor .middle, .xmlSpacePreserve]

def nodeMark (p : Placed) : Mark :=
  let b := nodeBox p
  let el : ({t : Tag} → List (SvgAttr t)) → SvgNode := fun more =>
    Svg.g more
      [Svg.loops [Cubic.roundRect b 5] [.fill (.rgb ground)],
        Svg.loops (Cubic.ring b 5 1) [.fill (.rgb ink), .fillRule .evenodd],
        Svg.label ⟨(centre p).x, (centre p).y + 5⟩ p.label face]
  { key := p.key, place := centre p, depth := p.span.depth, kind := .box, shape := [], node := el,
    fresh := el }

def edgeMark (total : Nat) (parent child : Placed) (port : Rat) : Mark :=
  let a : Vec := ⟨port, (centre parent).y + 13⟩
  let b : Vec := ⟨(centre child).x, (centre child).y - 13⟩
  let line := (Curve.bumpY (1 / 2)).cubics [a, b]
  let w := edgeWidth child.span.width total
  let seed := Noise.seedOf child.key
  let outline :=
    Stroke.stroke line (Stroke.organic seed (w / 2) (7 / 20) 40)
      (Stroke.organic (seed + 7) (w / 2) (7 / 20) 40) 8 (Vec.snapNear 1000)
  let key := "edge " ++ child.key
  let maskId := "mask-" ++ (((key.replace " " "-").replace "[" "").replace "]" "")
  { key := key, place := a, depth := child.span.depth, kind := .edge, shape := outline
    node := fun more => Svg.loops [outline] ([.fill (.rgb ink)] ++ more)
    fresh := fun more =>
      Svg.g []
        (Svg.revealed maskId
          (Svg.revealLine line (w * (27 / 20) + 1) more)
          [Svg.loops [outline] [.fill (.rgb ink)]]) }

/-- The marks of a tree: its edges, then its nodes over them. The edges to the children of a
node leave it side by side, at the ports of a row of their widths about its middle
(`ports`), so two branches of one node do not lie over each other. -/
def marksOf (t : Tree Node) : List Mark :=
  let ps := placedOf t
  let total := t.leaves
  let edges := ps.flatMap fun p =>
    let kids := (t.links.filter fun l => l.1.1 == p.key).filterMap fun l =>
      ps.find? fun c => c.key == l.2.1
    let widths := kids.map fun c => edgeWidth c.span.width total
    (kids.zip (ports (centre p).x widths)).map fun (c, port) => edgeMark total p c port
  edges ++ ps.map nodeMark

/-! ## The step as tracks -/

/-- lean4-effect4's critically damped spring, at every twentieth of its progress. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

/-- lean4-effect4's underdamped spring. -/
def spring : Easing :=
  .stops [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026,
    1019, 1012, 1007, 1003, 1000]

/-- The length of a step, in milliseconds. A slow step, so that an eye can follow it. -/
def stepMs : Nat := 1400

/-- A place in whole thousandths of a pixel. -/
def milli (v : Vec) : IVec := Vec.nearGrid 1000 v

/-- The kept things settle together: one transition for the nodes and the edges, so that an
edge stays joined to its nodes at every moment. -/
def move : Transition := .per stepMs { duration := 520, ease := settle }

/-- **The plan of a step.** A kept node moves, and one that does not move has no track. A kept
edge changes its shape by the same transition, so it stays joined to its nodes. A new edge
draws itself in the first 45 per cent of its level's time, and the node at its end grows from
40 per cent of it: lean4-effect4's shares. -/
def plan : Plan Mark where
  kept := fun o n =>
    match n.kind with
    | .box => Plan.moving (fun m => milli m.place) move o n
    | .edge => [(Change.morphOf 1000 o.shape n.shape, move)]
  enter := fun n =>
    match n.kind with
    | .edge => [(.reveal 0 1000, { delay := 0, duration := 450, ease := Easing.cubicOut })]
    | .box => [(.grow 0 1000, { delay := 400, duration := 600, ease := spring })]
  leave := fun _ => []

/-- **The motion of a step, in stages** (`Motion.staged`): the kept things come to rest by the
moment 300, and then the new things enter level by level, each level in a slot of its own. No
new thing appears before the kept things are at rest, and none before the level above it is
done. -/
def motion (old new : List Mark) : Motion String :=
  let j := join Mark.key old new
  let top := (j.enter.map fun n => n.depth).foldl min 1000
  let deepest := (j.enter.map fun n => n.depth).foldl max 0
  Motion.staged Mark.key j plan 300 (deepest + 1 - top) fun n => n.depth - top

/-! ## The page -/

def before : List Mark := marksOf treeBefore

def after : List Mark := marksOf treeAfter

def step : Motion String := motion before after

/-- Whether a mark is new in the step. -/
def isNew (k : Mark) : Bool := !(before.any fun o => o.key == k.key)

def picture (attrs : String → ({t : Tag} → List (SvgAttr t))) (sheet : Option String)
    (width height : Nat) : SvgNode :=
  Svg.svg
    [.attr .width (.user (.ofNat width)), .attr .height (.user (.ofNat height)),
      .attr .viewBox (ViewBox.ofSize 640 420)]
    (sheet.toList.map Svg.styleSheet ++
      [Svg.box (.ofSize ⟨0, 0⟩ 640 420) [.fill (.rgb ground)]] ++
      after.map fun k => if isNew k then k.fresh (attrs k.key) else k.node (attrs k.key))

def animated : SvgNode :=
  picture (fun key => Motion.attrs step key { step := stepMs, grid := 1000 }) (some (Motion.sheet step { step := stepMs, grid := 1000 })) 640 420

def still (t : Nat) : SvgNode := picture (fun key => Motion.attrsAt step key t { grid := 1000 }) none 320 210

/-- The browser's own still picture of the moment `t`: the same tracks, opened at that moment
and paused. No script runs. The rules of the sheet are those of the animated picture. -/
def paused (t : Nat) : SvgNode :=
  picture (fun key => Motion.attrs step key { step := stepMs, grid := 1000, opened := t, paused := true }) none 320 210

def page : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>pFork: a tree that grows</title>\n" ++
    "<body style=\"background:#14110d;color:#f3f4f6;font-family:Georgia,serif\">\n" ++
    "<h1 style=\"font-weight:400\">pFork: a tree that grows</h1>\n" ++
    "<p>One picture and its tracks, animated by the browser from the CSS that the kit wrote. " ++
    "<button onclick=\"const s=document.querySelector('svg');s.replaceWith(s.cloneNode(true))\">" ++
    "play again</button></p>\n" ++
    animated.render ++
    "\n<p>The same step at the moments 0, 250, 500, 750 and 1000, as the kit's own reading " ++
    "computes them, with no animation.</p>\n<div>" ++
    String.join ([0, 250, 500, 750, 1000].map fun t => (still t).render) ++ "</div>\n" ++
    "<p>The same five moments as the browser computes them: the animated picture's own tracks, " ++
    "opened at each moment and paused. The two rows must look the same.</p>\n<div id=\"paused\">" ++
    String.join ([0, 250, 500, 750, 1000].map fun t => (paused t).render) ++ "</div>\n" ++
    "<p>The step is one edit: the subtree at the fork is replaced. What the edit does to each " ++
    "node of the new picture, read from its two spans: " ++
    "; ".intercalate (groups.map fun (g, labels) => "<b>" ++ g ++ "</b>: " ++
      ", ".intercalate labels) ++ ".</p>\n</body>\n"

#eval animated.okIn Whatwg.Html.Content.Ctx.flow
#eval groups
#eval step.map fun tr => (tr.key, tr.timing.delay, tr.timing.duration)
#eval IO.FS.writeFile "docs/research/2026-10-12-motion-probe/tree.html" page
