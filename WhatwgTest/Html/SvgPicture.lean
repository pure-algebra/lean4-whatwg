import Whatwg.Html.Node.SvgValid
import Whatwg.Html.Print.Render

/-!
# WhatwgTest.Html.SvgPicture

A consumer's picture writer on the typed SVG node, whole: from a list of device calls to one
picture, with the proof that every picture is valid (slice S7 of `docs/SVG-PACKAGE-PLAN.md`).
It is a reader of the laws of `Whatwg/Html/Node/SvgValid.lean` at a real carrier, a fold, and
the pattern that lean4-effect4 can copy.

The device calls have the shapes of lean4-effect4's `tools/Tools/View/Output.lean`, read at
`707b9a01`: a filled box, a stroked curve, a text, a cut and its end, a pointer box, and a
filled shape of several closed paths. This module imports nothing of that package. It differs
from its string writer in what a tree forces:

- A cut and its end are two calls in a flat list. In a tree the group holds its children, so
  the fold keeps a stack of open cuts. An end with no open cut is dropped, and a cut with no
  end is closed at the end of the picture. So the tree of every list is balanced.
- A size is the difference of two corners, an integer. A negative size is no value of the
  type (ruling SV-35), and this writer writes it as zero. `AutoExtent.ofInt?` refuses it
  instead.

The theorem is `picture_okIn`: for every look, size, ratio and list of calls, the picture
passes `okIn` at every HTML position that admits `svg`. With the law V8 the checker accepts its
raw tree, and with V7 its values are of their grammars. Nothing is checked when a picture is
built.

How the proof goes. Each leaf is a tree with free values, and one evaluation proves it:
`conv => lhs; whnf`, after a case split on the one value that picks the tree's shape, whether
the key is empty. The fold is an invariant over its state, with `okAllAt_cons`,
`okAllAt_append`, `okAllAt_reverse` and `okAt_inSvg_g`. No step has arithmetic.

What this battery does not claim: that the picture is the one lean4-effect4 draws. No theorem
relates this writer to that package's string writer. The two texts differ in spelling:
`<rect …></rect>` for `<rect …/>`, `M10,20C10,30 30,30 30,40` for `M 10 20 C 10 30, 30 30, 30 40`,
one line for one line a call, and `'` unescaped.
-/

namespace WhatwgTest.Html.SvgPicture

open Whatwg.Html
open Whatwg.Html.Content
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value

/-! ## The device calls -/

/-- What a mark is for. Its colour is the look's. -/
inductive Role where
  | ground | ink | host
  deriving DecidableEq, Repr

/-- The role's name in a class. -/
def Role.name : Role → String
  | .ground => "ground"
  | .ink => "ink"
  | .host => "host"

/-- A box by two corners, in device pixels. -/
structure Box where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving DecidableEq, Repr

/-- A cubic segment by its four points. -/
structure Cubic where
  p0 : Int × Int
  p1 : Int × Int
  p2 : Int × Int
  p3 : Int × Int
  deriving DecidableEq, Repr

/-- One call to the drawing device. A cut opens a clip, and `uncut` closes the innermost one.
The points of a shape are in thousandths of a device pixel, and so is an opacity. -/
inductive Dev where
  | fill (role : Role) (opacity : Nat) (box : Box)
  | curve (role : Role) (segment : Cubic) (weight : Nat)
  | text (x base : Int) (content : String)
  | cut (x y w h : Int)
  | uncut
  | hit (box : Box)
  | shape (role : Role) (opacity : Nat) (paths : List (List Cubic))
  deriving Repr

/-- A call with the key of the object it draws. The empty key is no key. -/
structure Keyed where
  key : String
  call : Dev
  deriving Repr

/-- The look: its name, and the colour of each role as text. -/
structure Look where
  name : String
  ground : String
  ink : String
  host : String

/-- The colour of a role in a look. -/
def Look.color (look : Look) : Role → String
  | .ground => look.ground
  | .ink => look.ink
  | .host => look.host

/-! ## The typed writer -/

/-- An attribute list with the key of the call's object after it, when it has one. -/
def keyed {t : Tag} (key : String) (attrs : List (SvgAttr t)) : List (SvgAttr t) :=
  if key.isEmpty then attrs else attrs ++ [.data "key" key]

/-- A coordinate in user units. -/
def px (v : Int) : Length := .user (.ofInt v)

/-- A size in user units. A negative difference is written as zero. -/
def size (v : Int) : AutoExtent := .user (.ofNat v.toNat)

/-- A point of whole device pixels. -/
def point (p : Int × Int) : Point := ⟨.ofInt p.1, .ofInt p.2⟩

/-- A point in thousandths of a device pixel, with no zero at the end of a fraction. -/
def milli (p : Int × Int) : Point := ⟨(Decimal.ofScaled p.1 3).trim, (Decimal.ofScaled p.2 3).trim⟩

/-- A count of thousandths as the text of a number, for an attribute whose value is text. -/
def thousandths (n : Nat) : String :=
  String.ofList (Decimal.grammar.print (Decimal.ofScaled (Int.ofNat n) 3).trim)

/-- A filled box. -/
def fillNode (look : Look) (role : Role) (opacity : Nat) (b : Box) (key : String) : SvgNode :=
  .element .rect (keyed key
    [.attr .«class» ("e4-fill-" ++ role.name), .attr .x (px b.x0), .attr .y (px b.y0),
      .attr .width (size (b.x1 - b.x0)), .attr .height (size (b.y1 - b.y0)),
      .attr .fill (look.color role), .attr .fill_opacity (thousandths opacity)]) []

/-- A stroked cubic curve. -/
def curveNode (look : Look) (role : Role) (c : Cubic) (weight : Nat) (key : String) : SvgNode :=
  .element .path (keyed key
    [.attr .«class» ("e4-stroke-" ++ role.name),
      .attr .d (.path (.moveto false (point c.p0) []
        [.curveto false (point c.p1, point c.p2, point c.p3) []])),
      .attr .fill "none", .attr .stroke (look.color role),
      .attr .stroke_width (toString weight)]) []

/-- A text at a place, scaled by the ratio. Its `x` and `y` are text (debt D96). -/
def textNode (look : Look) (ratio : Nat) (x base : Int) (content key : String) : SvgNode :=
  .element .text (keyed key
    [.attr .x (toString x), .attr .y (toString base), .attr .«class» "e4-text",
      .attr .fill look.ink, .attr .transform [.scale (.ofInt ratio) none],
      .attr .xml_space "preserve"]) [.text content]

/-- An invisible box that takes the pointer. -/
def hitNode (b : Box) (key : String) : SvgNode :=
  .element .rect (keyed key
    [.attr .x (px b.x0), .attr .y (px b.y0), .attr .width (size (b.x1 - b.x0)),
      .attr .height (size (b.y1 - b.y0)), .attr .fill "none", .attr .pointer_events "all"]) []

/-- One closed path as a subpath: its start, a curve for each segment, and a closepath. A path
with no segment is no subpath. -/
def closedPath : List Cubic → Option (Point × List Command)
  | [] => none
  | c :: rest =>
    some (milli c.p0,
      ((c :: rest).map fun s => Command.curveto false (milli s.p1, milli s.p2, milli s.p3) []) ++
        [.closepath false])

/-- A filled shape of several closed paths in one `d`. -/
def shapeNode (look : Look) (role : Role) (opacity : Nat) (paths : List (List Cubic))
    (key : String) : SvgNode :=
  .element .path (keyed key
    [.attr .«class» ("e4-fill-" ++ role.name),
      .attr .d (.path (.ofSubpaths (paths.filterMap closedPath))),
      .attr .fill_rule "evenodd", .attr .fill (look.color role),
      .attr .fill_opacity (thousandths opacity)]) []

/-- A clip path and the group it clips, in device pixels at the ratio. -/
def clipPair (id ratio : Nat) (x y w h : Int) (children : List SvgNode) : List SvgNode :=
  [.element .clipPath [.attr .id ("c" ++ toString id)]
      [.element .rect [.attr .x (px (ratio * x)), .attr .y (px (ratio * y)),
        .attr .width (size (ratio * w)), .attr .height (size (ratio * h))] []],
    .element .g [.attr .clip_path ("url(#c" ++ toString id ++ ")")] children]

/-! ## The fold -/

/-- A cut that is open: its number, its box, and the marks that stood before it, last first. -/
structure Open where
  id : Nat
  x : Int
  y : Int
  w : Int
  h : Int
  before : List SvgNode

/-- The state of the fold: the marks at the depth of the innermost open cut, last first, and
the open cuts, innermost first. -/
structure State where
  marks : List SvgNode
  cuts : List Open

/-- Close a cut around the marks drawn inside it. The result is last first. -/
def close (ratio : Nat) (o : Open) (inner : List SvgNode) : List SvgNode :=
  (clipPair o.id ratio o.x o.y o.w o.h inner.reverse).reverse ++ o.before

/-- One device call, with its index in the list. A cut opens a group under that index, and its
end closes the innermost one. An end with no open cut is dropped. -/
def step (look : Look) (ratio : Nat) (s : State) (d : Keyed × Nat) : State :=
  match d.1.call with
  | .cut x y w h => ⟨[], ⟨d.2, x, y, w, h, s.marks⟩ :: s.cuts⟩
  | .uncut =>
    match s.cuts with
    | [] => s
    | o :: rest => ⟨close ratio o s.marks, rest⟩
  | .fill role opacity b => ⟨fillNode look role opacity b d.1.key :: s.marks, s.cuts⟩
  | .curve role c weight => ⟨curveNode look role c weight d.1.key :: s.marks, s.cuts⟩
  | .text x base content => ⟨textNode look ratio x base content d.1.key :: s.marks, s.cuts⟩
  | .hit b => ⟨hitNode b d.1.key :: s.marks, s.cuts⟩
  | .shape role opacity paths => ⟨shapeNode look role opacity paths d.1.key :: s.marks, s.cuts⟩

/-- Close every cut that is still open. -/
def finish (ratio : Nat) : List Open → List SvgNode → List SvgNode
  | [], marks => marks
  | o :: rest, marks => finish ratio rest (close ratio o marks)

/-- The state after every call. -/
def run (look : Look) (ratio : Nat) (calls : List Keyed) : State :=
  calls.zipIdx.foldl (step look ratio) ⟨[], []⟩

/-- The marks of a list of device calls, in order. -/
def marksOf (look : Look) (ratio : Nat) (calls : List Keyed) : List SvgNode :=
  (finish ratio (run look ratio calls).cuts (run look ratio calls).marks).reverse

/-- The picture: `W` by `H` logical pixels at a ratio, in a look. -/
def picture (look : Look) (W H ratio : Nat) (calls : List Keyed) : SvgNode :=
  .element .svg
    [.xmlns, .attr .«class» "e4-view", .data "look" look.name,
      .attr .width (.user (.ofNat W)), .attr .height (.user (.ofNat H)),
      .attr .viewBox ⟨0, 0, .ofNat (ratio * W), .ofNat (ratio * H)⟩]
    (marksOf look ratio calls)

/-! ## The structure of every picture

Each statement is at `Pos.inSvg x` for every set `x` of HTML exclusions, so the picture's
theorem holds at every HTML position that admits `svg`, and not in flow content alone. -/

variable (x : Exclusions)

theorem fillNode_ok (look : Look) (role : Role) (opacity : Nat) (b : Box) (key : String) :
    (fillNode look role opacity b key).okAt (Pos.inSvg x) = true := by
  unfold fillNode keyed
  cases key.isEmpty <;> conv => lhs; whnf

theorem curveNode_ok (look : Look) (role : Role) (c : Cubic) (weight : Nat) (key : String) :
    (curveNode look role c weight key).okAt (Pos.inSvg x) = true := by
  unfold curveNode keyed
  cases key.isEmpty <;> conv => lhs; whnf

theorem textNode_ok (look : Look) (ratio : Nat) (cx base : Int) (content key : String) :
    (textNode look ratio cx base content key).okAt (Pos.inSvg x) = true := by
  unfold textNode keyed
  cases key.isEmpty <;> conv => lhs; whnf

theorem hitNode_ok (b : Box) (key : String) : (hitNode b key).okAt (Pos.inSvg x) = true := by
  unfold hitNode keyed
  cases key.isEmpty <;> conv => lhs; whnf

theorem shapeNode_ok (look : Look) (role : Role) (opacity : Nat) (paths : List (List Cubic))
    (key : String) : (shapeNode look role opacity paths key).okAt (Pos.inSvg x) = true := by
  unfold shapeNode keyed
  cases key.isEmpty <;> conv => lhs; whnf

/-- A clip pair passes among the marks when its children do. -/
theorem clipPair_ok (id ratio : Nat) (cx cy w h : Int) (children : List SvgNode)
    (hc : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    SvgNode.okAllAt (Pos.inSvg x) (clipPair id ratio cx cy w h children) = true := by
  rw [clipPair, SvgNode.okAllAt_cons, SvgNode.okAllAt_cons, SvgNode.okAllAt_nil,
    SvgNode.okAt_inSvg_g, hc]
  conv => lhs; whnf

theorem close_ok (ratio : Nat) (o : Open) (inner : List SvgNode)
    (hi : SvgNode.okAllAt (Pos.inSvg x) inner = true)
    (ho : SvgNode.okAllAt (Pos.inSvg x) o.before = true) :
    SvgNode.okAllAt (Pos.inSvg x) (close ratio o inner) = true := by
  rw [close, SvgNode.okAllAt_append, SvgNode.okAllAt_reverse,
    clipPair_ok x _ _ _ _ _ _ _ ((SvgNode.okAllAt_reverse _ inner).trans hi), ho]
  rfl

/-- The invariant of the fold: the marks pass, and so do the marks before each open cut. -/
def State.Ok (s : State) : Prop :=
  SvgNode.okAllAt (Pos.inSvg x) s.marks = true ∧
    ∀ o ∈ s.cuts, SvgNode.okAllAt (Pos.inSvg x) o.before = true

theorem State.Ok.push {x : Exclusions} {s : State} (h : s.Ok x) {node : SvgNode}
    (hn : node.okAt (Pos.inSvg x) = true) : State.Ok x ⟨node :: s.marks, s.cuts⟩ :=
  ⟨by rw [SvgNode.okAllAt_cons, hn, h.1]; rfl, h.2⟩

/-- Each call keeps the invariant. -/
theorem step_ok (look : Look) (ratio : Nat) (s : State) (d : Keyed × Nat) (h : s.Ok x) :
    (step look ratio s d).Ok x := by
  obtain ⟨⟨key, call⟩, i⟩ := d
  cases call with
  | fill role opacity b => exact h.push (fillNode_ok x look role opacity b key)
  | curve role c weight => exact h.push (curveNode_ok x look role c weight key)
  | text cx base content => exact h.push (textNode_ok x look ratio cx base content key)
  | hit b => exact h.push (hitNode_ok x b key)
  | shape role opacity paths => exact h.push (shapeNode_ok x look role opacity paths key)
  | cut cx cy w h' =>
    exact ⟨SvgNode.okAllAt_nil _, fun o ho => by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact h.1
      · exact h.2 o ho⟩
  | uncut =>
    obtain ⟨marks, cuts⟩ := s
    cases cuts with
    | nil => exact h
    | cons o rest =>
      exact ⟨close_ok x ratio o marks h.1 (h.2 o List.mem_cons_self),
        fun o' ho' => h.2 o' (List.mem_cons_of_mem _ ho')⟩

theorem foldl_ok (look : Look) (ratio : Nat) : ∀ (calls : List (Keyed × Nat)) (s : State),
    s.Ok x → (calls.foldl (step look ratio) s).Ok x
  | [], _, h => h
  | d :: rest, s, h => foldl_ok look ratio rest _ (step_ok x look ratio s d h)

theorem finish_ok (ratio : Nat) : ∀ (cuts : List Open) (marks : List SvgNode),
    SvgNode.okAllAt (Pos.inSvg x) marks = true →
    (∀ o ∈ cuts, SvgNode.okAllAt (Pos.inSvg x) o.before = true) →
    SvgNode.okAllAt (Pos.inSvg x) (finish ratio cuts marks) = true
  | [], _, h, _ => h
  | o :: rest, marks, h, hs =>
    finish_ok ratio rest _ (close_ok x ratio o marks h (hs o List.mem_cons_self))
      (fun o' ho' => hs o' (List.mem_cons_of_mem _ ho'))

/-- The marks of every list of device calls pass where the marks of a picture stand. -/
theorem marksOf_ok (look : Look) (ratio : Nat) (calls : List Keyed) :
    SvgNode.okAllAt (Pos.inSvg x) (marksOf look ratio calls) = true := by
  have h := foldl_ok x look ratio calls.zipIdx ⟨[], []⟩
    ⟨SvgNode.okAllAt_nil _, fun _ ho => nomatch ho⟩
  rw [marksOf, SvgNode.okAllAt_reverse]
  exact finish_ok x ratio _ _ h.1 h.2

/-- The structure of every picture, at every HTML position that admits `svg`: for every look,
size, ratio and list of device calls, balanced or not. -/
theorem picture_okIn (ctx : Ctx) (hctx : ctx.admits .svg = true) (look : Look) (W H ratio : Nat)
    (calls : List Keyed) : (picture look W H ratio calls).okIn ctx = true := by
  rw [picture, SvgNode.okIn_svg, hctx, marksOf_ok (ctx.child .svg).excl]
  conv => lhs; whnf

/-- The checker accepts the raw tree of every picture in flow content (law V8). -/
theorem picture_valid (look : Look) (W H ratio : Nat) (calls : List Keyed) :
    validIn Ctx.flow (picture look W H ratio calls).toRaw = true :=
  SvgNode.validIn_of_okIn (picture_okIn Ctx.flow (by decide +kernel) look W H ratio calls)

/-- Every value of every picture is of its grammar (law V7). -/
theorem picture_values (look : Look) (W H ratio : Nat) (calls : List Keyed) :
    valuesOk (picture look W H ratio calls).toRaw = true :=
  SvgNode.valuesOk_toRaw _

/-- A picture as a child of the typed HTML tree, with no check when it is built. -/
def pictureChild (look : Look) (W H ratio : Nat) (calls : List Keyed) : Child Ctx.flow :=
  Child.ofSvg (picture look W H ratio calls)
    (picture_okIn Ctx.flow (by decide +kernel) look W H ratio calls)

/-! ## One picture, printed -/

/-- A look. -/
def plain : Look := ⟨"plain", "#14110d", "#f3f4f6", "#c0851f"⟩

/-- A call of each kind: a cut around a text, a key with characters that the printer escapes,
and a shape of two closed paths. -/
def sample : List Keyed :=
  [⟨"n1", .fill .ground 1000 ⟨0, 0, 40, 20⟩⟩,
   ⟨"", .fill .ink 500 ⟨2, 2, 38, 18⟩⟩,
   ⟨"e<1>", .curve .ink ⟨(10, 20), (10, 30), (30, 30), (30, 40)⟩ 2⟩,
   ⟨"", .cut 0 0 20 10⟩,
   ⟨"n1", .text 4 14 "a<b & c"⟩,
   ⟨"", .uncut⟩,
   ⟨"n1", .hit ⟨0, 0, 40, 20⟩⟩,
   ⟨"s", .shape .host 350
     [[⟨(0, 0), (1000, 0), (2500, 500), (3005, 1000)⟩,
       ⟨(3005, 1000), (2000, 1500), (1000, 2000), (0, 0)⟩],
      [⟨(500, 500), (600, 500), (700, 600), (500, 500)⟩]]⟩]

-- The fold nests the text in its group, and numbers the clip by the index of its cut.
#guard (marksOf plain 2 sample).length == 7

-- The printed picture: each typed value in its grammar's one spelling, a key's `<` and `>`
-- escaped, and the two closed paths of the shape in one `d`.
#guard Print.render (picture plain 40 20 2 sample).toRaw ==
  "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"e4-view\" data-look=\"plain\" " ++
  "width=\"40\" height=\"20\" viewBox=\"0 0 80 40\">" ++
  "<rect class=\"e4-fill-ground\" x=\"0\" y=\"0\" width=\"40\" height=\"20\" " ++
  "fill=\"#14110d\" fill-opacity=\"1\" data-key=\"n1\"></rect>" ++
  "<rect class=\"e4-fill-ink\" x=\"2\" y=\"2\" width=\"36\" height=\"16\" " ++
  "fill=\"#f3f4f6\" fill-opacity=\"0.5\"></rect>" ++
  "<path class=\"e4-stroke-ink\" d=\"M10,20C10,30 30,30 30,40\" fill=\"none\" " ++
  "stroke=\"#f3f4f6\" stroke-width=\"2\" data-key=\"e&lt;1&gt;\"></path>" ++
  "<clipPath id=\"c3\"><rect x=\"0\" y=\"0\" width=\"40\" height=\"20\"></rect></clipPath>" ++
  "<g clip-path=\"url(#c3)\"><text x=\"4\" y=\"14\" class=\"e4-text\" fill=\"#f3f4f6\" " ++
  "transform=\"scale(2)\" xml:space=\"preserve\" data-key=\"n1\">a&lt;b &amp; c</text></g>" ++
  "<rect x=\"0\" y=\"0\" width=\"40\" height=\"20\" fill=\"none\" pointer-events=\"all\" " ++
  "data-key=\"n1\"></rect>" ++
  "<path class=\"e4-fill-host\" d=\"M0,0C1,0 2.5,0.5 3.005,1C2,1.5 1,2 0,0Z" ++
  "M0.5,0.5C0.6,0.5 0.7,0.6 0.5,0.5Z\" fill-rule=\"evenodd\" fill=\"#c0851f\" " ++
  "fill-opacity=\"0.35\" data-key=\"s\"></path></svg>"

-- Control: an end with no open cut is dropped, and a cut with no end is closed at the end.
#guard (picture plain 1 1 1 [⟨"", .uncut⟩, ⟨"a", .hit ⟨0, 0, 1, 1⟩⟩]).toRaw ==
  (picture plain 1 1 1 [⟨"a", .hit ⟨0, 0, 1, 1⟩⟩]).toRaw
#guard (picture plain 1 1 1 [⟨"", .cut 0 0 1 1⟩, ⟨"a", .hit ⟨0, 0, 1, 1⟩⟩]).toRaw ==
  (picture plain 1 1 1 [⟨"", .cut 0 0 1 1⟩, ⟨"a", .hit ⟨0, 0, 1, 1⟩⟩, ⟨"", .uncut⟩]).toRaw

-- Control: corners out of order give a size of zero, by this writer's choice.
#guard Print.render (hitNode ⟨5, 5, 2, 9⟩ "").toRaw ==
  "<rect x=\"5\" y=\"5\" width=\"0\" height=\"4\" fill=\"none\" pointer-events=\"all\"></rect>"

end WhatwgTest.Html.SvgPicture
