import Whatwg.Html.Node.SvgKeyword
import Whatwg.Html.Node.SvgDraw
import Whatwg.Html.Node.SvgNest

/-!
# Whatwg.Html.Node.SvgDefs

Owner: the things of a picture that are defined once and referred to (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`): a gradient, a clip path, a mask, a marker, a filter, a group that
is drawn again. In markup each is an element with an `id`, and a mark refers to it by a text,
`url(#id)`. A program wrote the identifier twice, as a text, and nothing tied the two: a letter
wrong in one of them is a mark with no paint, and two definitions under one identifier are one
definition.

Here a program types no identifier. It makes a definition inside `Svg.Defs`, a program that
counts, and is handed a reference, `Svg.Ref`, which is what the attributes of a mark take:

```
Svg.withDefs "edge" do
  let fade ← Svg.Defs.linearGradient a b [⟨0, ink, some 1⟩, ⟨1, ink, some 0⟩]
  let head ← Svg.Defs.arrowHead 6 8 (.rgb ink)
  let shown ← Svg.Defs.mask [Svg.box region [.fill white]]
  pure [Svg.g [.maskBy shown] [Svg.cubics edge [.fill .none, .stroke fade, .markerEnd head]]]
```

- `Svg.Ref kind` is a reference to a definition of one kind. A gradient's is a paint, so
  `.fill` and `.stroke` take it; `.clipBy`, `.maskBy`, `.filterBy`, `.markerStart`, `.markerMid`
  and `.markerEnd` take the reference of their kind and no other, and `Svg.use` draws a group
  again. A mask where a paint is expected is no term.
- `Svg.Def` is a definition without its identifier: a tag, its attributes and its children.
  `Def.linearGradient`, `radialGradient`, `clip`, `mask`, `marker`, `arrowHead`, `blur`,
  `dropShadow` and `group` are the ones a picture needs first, and `Svg.Stop` is a typed stop of
  a gradient.
- `Svg.Defs α` is a program that makes definitions and gives an `α`. It reads a stem and the
  number of definitions made before it, and hands back the definitions it makes, in order.
  `Defs.add` makes one, and `Defs.each` runs a program for each item of a list. It is a monad,
  so a `do` block writes one. The identifier of the definition at the place `i` is the stem, a
  hyphen and `i` (`Defs.name`), and it is written by the runner, `Defs.named`, never by a
  program: a program holds no identifier to get wrong.
- `Svg.withDefs stem program` is the forest of a picture: one `defs` with every definition
  under its identifier, then the marks that the program gives.
- `Svg.Defs.cuts` is the fold of `Whatwg/Html/Node/SvgNest.lean` as a program: the cuts of a
  flat list of device calls are clip paths among the definitions, under the picture's stem.
- `Svg.link` is an `a` around marks, and `Svg.titled` an `svg` that is one image with a name:
  `role="img"`, a `title` and a `desc` under identifiers made from the stem (`Svg.titleId`,
  `Svg.descId`), and `aria-labelledby` and `aria-describedby` naming them.

The identifiers of a tree, for a tree built in any way, are read by three functions:
`SvgNode.ids`, every `id` it declares; `SvgNode.refs`, every identifier that one of its
attributes refers to, where an `href` to another page refers to none and `href="#x"` to `x`;
and `SvgNode.linked`, the test that no identifier is declared twice and every one referred to
is declared. A check of a whole page reads the first two of each picture. The checker of `Whatwg/Html/Node/SvgValid.lean` judges none
of this: to it an `id` and a `url(#…)` are texts.

The laws are in `Whatwg/Html/Node/SvgDefs/Laws.lean`: the definitions of every program have
distinct identifiers; two runs under two stems share none; a reference written by a helper is
read back by `SvgNode.refs`; and `defs` passes the structure test when its definitions do.

How a definition is written follows a figure of the sealed chapter Document Structure
(`vendor/w3c-svgwg-47e645ef/master/struct.html`, the figure of the `use` element's shadow
tree): a `marker` with `refX`, `refY`, `markerWidth`, `markerHeight` and `orient` around a
`path`, and a `g` under `defs` that a `use` draws by `href`. The attributes of a gradient, a
mask and a filter are written from memory: their chapters are not sealed.

What this module does not claim. That a browser draws a definition as its docstring says: a
text here is written by rule. That a reference names a definition of its own kind in a tree
built by hand: `SvgNode.linked` reads identifiers, and the kind of a reference is in its type
only. That a raw subtree, the HTML below `foreignObject`, declares no identifier: `ids` does not
read one. Nor an identifier for a stem that holds white space or a `)`, which `urlRef` writes
as it is.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value

namespace Svg

/-! ## A reference -/

/-- What a definition is referred to as. -/
inductive RefKind where
  /-- A paint server: a gradient. `fill` and `stroke` refer to it. -/
  | paint
  /-- A clip path. -/
  | clip
  /-- A mask. -/
  | mask
  /-- A marker: an arrow head. -/
  | marker
  /-- A filter. -/
  | filter
  /-- A group that `use` draws again. -/
  | shape
  deriving DecidableEq, Repr, Inhabited

/-- A reference to a definition of one kind, by its identifier. `Defs.add` hands one back; a
program has no need to make one itself. -/
structure Ref (kind : RefKind) where
  /-- The identifier of the definition. -/
  id : String
  deriving DecidableEq, Repr, Inhabited

/-- The reference to a gradient is a paint: `.fill fade`. -/
instance : Coe (Ref .paint) Paint := ⟨fun r => .url r.id⟩

/-- The text of a number that a program computed, at `places` places. -/
def num (q : Rat) (places : Nat := 3) : String := SvgAttr.numberText (.ofRat q places)

/-! ## A definition without its identifier -/

/-- A definition without its identifier: an element that is referred to. The runner writes the
`id`, so `attrs` holds none. -/
structure Def where
  /-- The element. -/
  tag : Tag
  /-- Its attributes, other than `id`. -/
  attrs : List (SvgAttr tag)
  /-- Its children. -/
  children : List SvgNode

/-- The element of a definition under an identifier: `id` first, then its own attributes. -/
def Def.node (d : Def) (id : String) : SvgNode := .element d.tag (.ident id :: d.attrs) d.children

/-- A stop of a gradient: where it stands, from `0` at the start to `1` at the end, its colour,
and its opacity where it is less than one. -/
structure Stop where
  /-- The place of the stop along the gradient, from `0` to `1`. -/
  offset : Decimal
  /-- The colour at the stop. -/
  color : Rgb
  /-- The opacity at the stop. None is an opacity of one. -/
  opacity : Option Decimal := none
  deriving DecidableEq, Repr, Inhabited

/-- `stop`: `offset`, `stop-color`, and `stop-opacity` where the stop has one. -/
def Stop.node (s : Stop) : SvgNode :=
  .element .stop
    ([.attr .offset (SvgAttr.numberText s.offset), .attr .stop_color s.color.hex] ++
      match s.opacity with
      | none => []
      | some o => [.attr .stop_opacity (SvgAttr.numberText o)])
    []

/-- Stops evenly spaced from `0` to `1`, one for each colour, at three places. One colour is one
stop at `0`. -/
def Stop.even (colors : List Rgb) : List Stop :=
  colors.zipIdx.map fun p =>
    ⟨.ofRat ((p.2 : Rat) / ((colors.length - 1 : Nat) : Rat)), p.1, none⟩

namespace Def

/-- A gradient along the line from `a` to `b`. With `userSpaceOnUse` the two points are in the
user space of the mark that is painted; with `objectBoundingBox` they are fractions of its
box. -/
def linearGradient (a b : Vec) (stops : List Stop) (units : Units := .userSpaceOnUse)
    (more : List (SvgAttr .linearGradient) := []) (places : Nat := 3) : Def :=
  ⟨.linearGradient,
    [.attr .x1 (num a.x places), .attr .y1 (num a.y places), .attr .x2 (num b.x places),
      .attr .y2 (num b.y places), .gradientUnits units] ++ more,
    stops.map Stop.node⟩

/-- A gradient from a centre outwards to the radius `r`. -/
def radialGradient (center : Vec) (r : Rat) (stops : List Stop)
    (units : Units := .userSpaceOnUse) (more : List (SvgAttr .radialGradient) := [])
    (places : Nat := 3) : Def :=
  ⟨.radialGradient,
    [.attr .cx (num center.x places), .attr .cy (num center.y places), .attr .r (num r places),
      .gradientUnits units] ++ more,
    stops.map Stop.node⟩

/-- A clip path: what is drawn shows inside the shapes. -/
def clip (shapes : List SvgNode) : Def := ⟨.clipPath, [], shapes⟩

/-- A mask in user space: what is drawn shows where the children are light, and not where they
are dark or where there is none. With a `region` the mask is that box and nothing shows outside
it; with none it is the box that the element's defaults give. -/
def mask (children : List SvgNode) (region : Option Box := none)
    (more : List (SvgAttr .mask) := []) (places : Nat := 3) : Def :=
  ⟨.mask,
    (.maskUnits .userSpaceOnUse ::
      match region with
      | none => []
      | some b =>
        [.attr .x (num b.x0 places), .attr .y (num b.y0 places),
          .attr .width (num b.width places), .attr .height (num b.height places)]) ++ more,
    children⟩

/-- A marker: `children` drawn at a vertex of a path, in a box `size` wide and high whose point
`anchor` stands on the vertex. -/
def marker (size anchor : Vec) (children : List SvgNode) (orient : Orient := .auto)
    (units : MarkerUnits := .strokeWidth) (more : List (SvgAttr .marker) := [])
    (places : Nat := 3) : Def :=
  ⟨.marker,
    [.attr .markerWidth (num size.x places), .attr .markerHeight (num size.y places),
      .attr .refX (num anchor.x places), .attr .refY (num anchor.y places), .orient orient,
      .markerUnits units] ++ more,
    children⟩

/-- An arrow head: a filled triangle `along` long and `across` wide, in user units, whose tip
stands on the vertex and points along the path. At the start of a path it points back. -/
def arrowHead (along across : Rat) (paint : Paint) (places : Nat := 3) : Def :=
  marker ⟨along, across⟩ ⟨along, across / 2⟩
    [Svg.loops
      [[Cubic.line ⟨0, 0⟩ ⟨along, across / 2⟩, Cubic.line ⟨along, across / 2⟩ ⟨0, across⟩,
        Cubic.line ⟨0, across⟩ ⟨0, 0⟩]]
      [.fill paint] places]
    .autoStartReverse .userSpaceOnUse [] places

/-- A filter that blurs by a standard deviation, in user units. -/
def blur (deviation : Rat) (more : List (SvgAttr .filter) := []) (places : Nat := 3) : Def :=
  ⟨.filter, more, [.element .feGaussianBlur [.attr .stdDeviation (num deviation places)] []]⟩

/-- A filter that draws a shadow under what it is put on: moved by `offset`, blurred by
`deviation`, in a colour at an opacity. -/
def dropShadow (offset : Vec) (deviation : Rat) (color : Rgb) (opacity : Decimal := 1)
    (more : List (SvgAttr .filter) := []) (places : Nat := 3) : Def :=
  ⟨.filter, more,
    [.element .feDropShadow
      [.attr .dx (num offset.x places), .attr .dy (num offset.y places),
        .attr .stdDeviation (num deviation places), .attr .flood_color color.hex,
        .attr .flood_opacity (SvgAttr.numberText opacity)] []]⟩

/-- A group that is not drawn where it stands: `Svg.use` draws it, any number of times. -/
def group (children : List SvgNode) (more : List (SvgAttr .g) := []) : Def :=
  ⟨.g, more, children⟩

end Def

/-! ## A program that makes definitions -/

/-- A program that makes definitions and gives an `α`. It reads the stem of the identifiers and
the number of definitions made before it, and hands back what it gives and the definitions it
makes, in order. -/
def Defs (α : Type) : Type := String → Nat → α × List Def

namespace Defs

/-- A program that makes no definition. -/
protected def pure {α : Type} (a : α) : Defs α := fun _ _ => (a, [])

/-- One program and then another: the second counts on from where the first ended. -/
protected def bind {α β : Type} (m : Defs α) (f : α → Defs β) : Defs β := fun stem n =>
  ((f (m stem n).1 stem (n + (m stem n).2.length)).1,
    (m stem n).2 ++ (f (m stem n).1 stem (n + (m stem n).2.length)).2)

instance : Monad Defs where
  pure := Defs.pure
  bind := Defs.bind

/-- The identifier of the definition at the place `i`: the stem, a hyphen, and `i`. -/
def name (stem : String) (i : Nat) : String := stem ++ "-" ++ toString i

/-- **Make a definition.** It takes the next place, and the reference to it is handed back. -/
def add (kind : RefKind) (d : Def) : Defs (Ref kind) := fun stem n => (⟨name stem n⟩, [d])

/-- One program for each item of a list, in order, and what each gives: a mark and its
definitions for each edge of a graph. -/
def each {α β : Type} : List α → (α → Defs β) → Defs (List β)
  | [], _ => pure []
  | a :: rest, f => f a >>= fun b => each rest f >>= fun bs => pure (b :: bs)

/-- The definitions of a list under their identifiers, the first at the place `i`. -/
def namedFrom (stem : String) : Nat → List Def → List SvgNode
  | _, [] => []
  | i, d :: ds => d.node (name stem i) :: namedFrom stem (i + 1) ds

/-- The definitions of a list, each under the identifier of its place. -/
def named (stem : String) (ds : List Def) : List SvgNode := namedFrom stem 0 ds

/-- The `defs` of a list of definitions: one element that holds each under its identifier, and
nothing for no definition. -/
def block (stem : String) : List Def → List SvgNode
  | [] => []
  | d :: ds => [Svg.defs (named stem (d :: ds))]

/-- What a program gives, and its definitions under their identifiers. -/
def run {α : Type} (stem : String) (m : Defs α) : α × List SvgNode :=
  ((m stem 0).1, named stem (m stem 0).2)

/-- A gradient along a line, as a paint. -/
def linearGradient (a b : Vec) (stops : List Stop) (units : Units := .userSpaceOnUse)
    (more : List (SvgAttr .linearGradient) := []) (places : Nat := 3) : Defs (Ref .paint) :=
  add .paint (.linearGradient a b stops units more places)

/-- A gradient from a centre outwards, as a paint. -/
def radialGradient (center : Vec) (r : Rat) (stops : List Stop)
    (units : Units := .userSpaceOnUse) (more : List (SvgAttr .radialGradient) := [])
    (places : Nat := 3) : Defs (Ref .paint) :=
  add .paint (.radialGradient center r stops units more places)

/-- A clip path of shapes. -/
def clip (shapes : List SvgNode) : Defs (Ref .clip) := add .clip (.clip shapes)

/-- A mask in user space. -/
def mask (children : List SvgNode) (region : Option Box := none)
    (more : List (SvgAttr .mask) := []) (places : Nat := 3) : Defs (Ref .mask) :=
  add .mask (.mask children region more places)

/-- A marker of any content. -/
def marker (size anchor : Vec) (children : List SvgNode) (orient : Orient := .auto)
    (units : MarkerUnits := .strokeWidth) (more : List (SvgAttr .marker) := [])
    (places : Nat := 3) : Defs (Ref .marker) :=
  add .marker (.marker size anchor children orient units more places)

/-- An arrow head, in user units. -/
def arrowHead (along across : Rat) (paint : Paint) (places : Nat := 3) : Defs (Ref .marker) :=
  add .marker (.arrowHead along across paint places)

/-- A filter that blurs. -/
def blur (deviation : Rat) (more : List (SvgAttr .filter) := []) (places : Nat := 3) :
    Defs (Ref .filter) :=
  add .filter (.blur deviation more places)

/-- A filter that draws a shadow. -/
def dropShadow (offset : Vec) (deviation : Rat) (color : Rgb) (opacity : Decimal := 1)
    (more : List (SvgAttr .filter) := []) (places : Nat := 3) : Defs (Ref .filter) :=
  add .filter (.dropShadow offset deviation color opacity more places)

/-- A group that `Svg.use` draws. -/
def group (children : List SvgNode) (more : List (SvgAttr .g) := []) : Defs (Ref .shape) :=
  add .shape (.group children more)

end Defs

/-- **The forest of a picture with its definitions**: one `defs` that holds every definition of
the program under its identifier, then the marks that the program gives. A program that makes
no definition writes no `defs`. One stem serves one picture: two pictures of one page take two
stems, and then share no identifier (`Defs.name_injective`). -/
def withDefs (stem : String) (m : Defs (List SvgNode)) : List SvgNode :=
  Defs.block stem (m stem 0).2 ++ (m stem 0).1

/-- `use`: a group of the definitions, drawn with its origin at a place. -/
def use (shape : Ref .shape) (place : Vec := ⟨0, 0⟩) (more : List (SvgAttr .use) := [])
    (places : Nat := 3) : SvgNode :=
  .element .use
    ([.attr .href ("#" ++ shape.id), .attr .x (num place.x places), .attr .y (num place.y places)]
      ++ more)
    []

/-! ## A link, and a picture that is read by name -/

/-- `a`: a link around marks, to a page or to a place in one. A node of a graph that links to
its page is `Svg.link "fiber-0.html" [box, label]`. -/
def link (href : String) (children : List SvgNode) (more : List (SvgAttr .a) := []) : SvgNode :=
  .element .a (.attr .href href :: more) children

/-- The identifier of the title of the picture under a stem. The HTML around a picture names
its title by this. -/
def titleId (stem : String) : String := stem ++ "-title"

/-- The identifier of the description of the picture under a stem. -/
def descId (stem : String) : String := stem ++ "-desc"

/-- `title` of a picture, under the identifier of its stem. -/
def titleNode (stem label : String) : SvgNode :=
  .element .title [.ident (titleId stem)] [.text label]

/-- `desc` of a picture, under the identifier of its stem. -/
def descNode (stem text : String) : SvgNode := .element .desc [.ident (descId stem)] [.text text]

/-- The attributes that make an `svg` one image with a name: `role="img"`, `aria-labelledby`
naming its title, and `aria-describedby` naming its description where it has one. -/
def titledAttrs (stem : String) (described : Bool) : List (SvgAttr .svg) :=
  [.attr .role "img", .attr .aria_labelledby (titleId stem)] ++
    if described then [.attr .aria_describedby (descId stem)] else []

/-- **A picture that is read by name**: an `svg` that is one image, whose first child is its
`title`, then its `desc` where it has one, each under an identifier made from the stem and named
by the `svg`. No identifier is typed. `more` holds the size and the view box. -/
def titled (stem label : String) (more : List (SvgAttr .svg)) (children : List SvgNode)
    (desc : Option String := none) : SvgNode :=
  Svg.svg (titledAttrs stem desc.isSome ++ more)
    (titleNode stem label ::
      ((match desc with
        | none => []
        | some text => [descNode stem text]) ++ children))

/-- A frame's picture that is read by name. -/
def Frame.titled (f : Frame) (stem label : String) (more : List (SvgAttr .svg))
    (children : List SvgNode) (desc : Option String := none) : SvgNode :=
  Svg.titled stem label (more ++ f.attrs) children desc

end Svg

/-! ## Attributes that refer -/

namespace SvgAttr

variable {t : Tag}

/-- `clip-path`, by the reference to a clip path. -/
def clipBy (clip : Svg.Ref .clip) : SvgAttr t := .clipPath clip.id

/-- `mask`, by the reference to a mask. -/
def maskBy (mask : Svg.Ref .mask) : SvgAttr t := .attr .mask (urlRef mask.id)

/-- `filter`, by the reference to a filter. -/
def filterBy (filter : Svg.Ref .filter) : SvgAttr t := .attr .filter (urlRef filter.id)

/-- `marker-start`: a marker at the first vertex of a path. -/
def markerStart (marker : Svg.Ref .marker) : SvgAttr t := .attr .marker_start (urlRef marker.id)

/-- `marker-mid`: a marker at every vertex of a path but the first and the last. -/
def markerMid (marker : Svg.Ref .marker) : SvgAttr t := .attr .marker_mid (urlRef marker.id)

/-- `marker-end`: a marker at the last vertex of a path. -/
def markerEnd (marker : Svg.Ref .marker) : SvgAttr t := .attr .marker_end (urlRef marker.id)

end SvgAttr

/-! ## The identifiers of a tree -/

/-- Read a reference back: the identifier of `url(#id)`, and nothing for any other text. -/
def urlRef? (text : String) : Option String :=
  match text.toList with
  | 'u' :: 'r' :: 'l' :: '(' :: '#' :: rest =>
    if rest.getLast? = some ')' then some (String.ofList rest.dropLast) else none
  | _ => none

/-- The identifier of a fragment `#id`: what `href` of a `use` holds. -/
def fragment? (text : String) : Option String :=
  match text.toList with
  | '#' :: rest => some (String.ofList rest)
  | _ => none

namespace SvgAttr

variable {t : Tag}

/-- The identifier that an attribute declares: the value of `id`. -/
def id? (a : SvgAttr t) : Option String :=
  match a.key with
  | .attr .id => some a.toPair.2
  | _ => none

/-- The identifier that an attribute refers to: that of `url(#id)` in `fill`, `stroke`,
`clip-path`, `mask`, `filter` and the three marker properties, and that of `#id` in `href`. A
paint that is a colour, and an `href` to another document, refer to none. -/
def ref? (a : SvgAttr t) : Option String :=
  match a.key with
  | .attr .fill | .attr .stroke | .attr .clip_path | .attr .mask | .attr .filter
  | .attr .marker_start | .attr .marker_mid | .attr .marker_end => urlRef? a.toPair.2
  | .attr .href => fragment? a.toPair.2
  | _ => none

/-- Every identifier that an attribute refers to: the one of `ref?`, and each word of
`aria-labelledby` and of `aria-describedby`, which name elements by a list of identifiers. -/
def refs (a : SvgAttr t) : List String :=
  match a.key with
  | .attr .aria_labelledby | .attr .aria_describedby =>
    (a.toPair.2.splitOn " ").filter fun word => !word.isEmpty
  | _ => a.ref?.toList

end SvgAttr

namespace SvgNode

/-- The identifier of an element: the value of its first `id`. -/
def id? : SvgNode → Option String
  | .element _ attrs _ => attrs.findSome? SvgAttr.id?
  | _ => none

mutual

/-- Every identifier that a tree declares, in the order of the document. A raw subtree is not
read. -/
def ids : SvgNode → List String
  | .element _ attrs children => attrs.filterMap SvgAttr.id? ++ idsAll children
  | _ => []

/-- Every identifier that a forest declares. -/
def idsAll : List SvgNode → List String
  | [] => []
  | node :: rest => node.ids ++ idsAll rest

end

mutual

/-- Every identifier that an attribute of a tree refers to, in the order of the document. -/
def refs : SvgNode → List String
  | .element _ attrs children => attrs.flatMap SvgAttr.refs ++ refsAll children
  | _ => []

/-- Every identifier that an attribute of a forest refers to. -/
def refsAll : List SvgNode → List String
  | [] => []
  | node :: rest => node.refs ++ refsAll rest

end

/-- No text of the list stands in it twice. -/
def distinct : List String → Bool
  | [] => true
  | s :: rest => !rest.contains s && distinct rest

/-- **The identifiers of a forest are in order**: none is declared twice, and every one that an
attribute refers to is declared. A reference to a definition in another tree of the page is
refused here: test the forest that holds both. -/
def linkedAll (nodes : List SvgNode) : Bool :=
  distinct (idsAll nodes) && (refsAll nodes).all fun r => (idsAll nodes).contains r

/-- The identifiers of a tree are in order. -/
def linked (node : SvgNode) : Bool := linkedAll [node]

/-! ## A flat list of calls whose groups are numbered -/

/-- Number the groups of a flat list of calls: each start takes the next number, from `n`. -/
def Flat.numbered {α : Type} : Nat → List (Flat α) → List (Flat (Nat × α))
  | _, [] => []
  | n, .leaf node :: rest => .leaf node :: Flat.numbered n rest
  | n, .enter label :: rest => .enter (n, label) :: Flat.numbered (n + 1) rest
  | n, .leave :: rest => .leave :: Flat.numbered n rest

/-- The labels of the groups that a flat list of calls starts, in order. -/
def Flat.enters {α : Type} : List (Flat α) → List α
  | [] => []
  | .enter label :: rest => label :: Flat.enters rest
  | .leaf _ :: rest => Flat.enters rest
  | .leave :: rest => Flat.enters rest

end SvgNode

/-- **A flat list of calls with cuts, as a program.** A drawing device is called in order: a
mark, the start of a cut, more marks, the end of the cut (`SvgNode.nest`). Here each cut is a
clip path among the definitions, `clip` of its label, and the group of its marks refers to it:
the `k`-th cut that starts is the `k`-th definition that the program makes, so the runner writes
the identifier that the group names. A writer types no identifier and counts none, and two
pictures of one page under two stems declare no clip path twice. -/
def Svg.Defs.cuts {α : Type} (clip : α → List SvgNode) (calls : List (SvgNode.Flat α)) :
    Svg.Defs (List SvgNode) := fun stem n =>
  (SvgNode.nest
      (fun (k : Nat × α) kids => [Svg.g [.clipBy ⟨Svg.Defs.name stem k.1⟩] kids])
      (SvgNode.Flat.numbered n calls),
    (SvgNode.Flat.enters calls).map fun label => Svg.Def.clip (clip label))

end Whatwg.Html
