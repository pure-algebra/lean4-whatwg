import Whatwg.Svg.Scene.Layout
import Whatwg.Svg.Scene.Layers

/-!
# Whatwg.Svg.Scene.Network

Owner: a flow network laid out (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; ask W18 of
`docs/research/2026-10-12-whatwg-requests.md`).

A run moves units from place to place, and its totals say where the units went: four offered,
three entered at once and one waited. The picture of such totals is a network of nodes and
links in which a width is a quantity. A node is as long as what passes it, a link is a band as
wide as what it carries, and at each side of a node the bands of its links lie one below the
other with no gap and no overlap. So a reader sees a split as a split: the branches are
together as wide as the trunk.

This is the layout of d3-sankey (`src/sankey.js` at `bb7233ea0004`) as far as it is exact. The
columns are the layers of `Whatwg/Svg/Scene/Layers.lean`, which the port
`WhatwgTest/Svg/UseLayers.lean` shows equal to d3's on d3's own example. This module adds what
d3 does next: the value of a node (`computeNodeValues`), its length on a scale and its place
down its column (`initializeNodeBreadths`), and the band of each link at each of its two ends
(`computeLinkBreadths`). A caller gives its own nodes and links and three functions that read a
link, and converts no data.

- `Network ε ν`: the nodes, the links, and how a link is read: its source, its target and how
  much it carries.
- `enters`, `leaves`, `value`, `Conserved`: what the links bring to a node and take from it,
  the greater of the two, and whether the two are one.
- `depth order`, `justify order`: the column of a node, from the layers. `justify` is d3's
  default: a node that nothing leaves stands in the last column.
- `Measure`: the four numbers of a picture: how thick a node is across, how far one column is
  from the next, the gap between two nodes of a column, and the scale, a function from a
  quantity to a length.
- `fit col gap room`: d3's scale, the greatest that puts every column inside a room of a given
  height, as a ratio. `times k` and `ratio num den` are scales.
- `box m col v`, `layout m col`: where a node stands, and all of them as a `Layout`.
- `Channel ε`, `channels m col`: **each link as data for a ribbon**: the band where it leaves
  its source and the band where it enters its target, each a box with no width on the side of
  the node. `outs`, `ins`: the bands at one side of a node, in their order.
- `pile scale p xs`: values piled along a scale. It is the one piece of arithmetic here, and
  every law of a band is a law of it.

The laws are in `Whatwg/Svg/Scene/Network/Laws.lean`, and those of `fit` in
`Whatwg/Svg/Scene/Network/Fit.lean`.

What is taken from d3-sankey, and what is left.

- Taken: the value of a node; the columns; `justify`; the scale `ky`; the order of the links
  at a side (`computeLinkBreadths` reads the order of the lists, and so does `channels`); the
  bands.
- Changed: lengths are whole numbers. The edges of the bands are rounded, and a band is what
  lies between two edges, as in `Whatwg/Svg/Scene/Row.lean`. So the bands tile with the
  rounding, where widths rounded one by one would not.
- Changed: the nodes of a column stand from the top of the room, each a gap below the one
  before it, in the order of the list of nodes. d3 spreads the room that is left between
  them, and then moves them.
- Left: d3's relaxation (`relaxLeftToRight`, `relaxRightToLeft`, `resolveCollisions`), which
  is an iteration in floating point with no fixed point that a law could name; the sorts that
  go with it (`reorderLinks`), since a caller gives the order of its links and of its nodes;
  the alignments `left`, `right` and `center` (`depth` is `left`).

What this module does not claim: a least number of crossings; that a link between columns that
are not neighbours passes no node, which needs a place kept for it in each column between (the
laws say which nodes a link cannot meet); a ribbon, which is a curve of the exact geometry;
that `depth` is fast.

Every definition here reaches Lean alone, and every law depends on `propext` and `Quot.sound`
at most.
-/

namespace Whatwg.Svg.Scene

/-- **A flow network**: the caller's nodes and links, and how a link is read. -/
structure Network (ε ν : Type) where
  /-- The nodes. Those of one column stand down it in this order. -/
  nodes : List ν
  /-- The links. Those at one side of a node stand down it in this order. -/
  links : List ε
  /-- The node that a link leaves. -/
  src : ε → ν
  /-- The node that a link enters. -/
  dst : ε → ν
  /-- How much a link carries. -/
  carry : ε → Nat

namespace Network

variable {ε ν : Type}

/-! ## Values piled along a scale -/

/-- **A scale rises**: more is never drawn as less. -/
def Rising (scale : Nat → Nat) : Prop := ∀ a b : Nat, a ≤ b → scale a ≤ scale b

/-- **Values piled along a scale**, from the sum `p`: each value is the band from the length of
the sum before it to the length of the sum with it. The edges are rounded and not the widths,
so the bands tile whatever the scale. -/
def pile (scale : Nat → Nat) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | p, x :: xs => (scale p, scale (p + x)) :: pile scale (p + x) xs

/-- **The bands tile**: each starts where the one before it ends. -/
def Tiles : List (Nat × Nat) → Prop
  | a :: b :: rest => a.2 = b.1 ∧ Tiles (b :: rest)
  | _ => True

/-- The scale of a whole number of units of length for each unit of quantity. -/
def times (k : Nat) : Nat → Nat := fun v => v * k

/-- The scale of `num` units of length for each `den` units of quantity, rounded down. -/
def ratio (num den : Nat) : Nat → Nat := fun v => v * num / den

theorem length_pile (scale : Nat → Nat) : ∀ (xs : List Nat) (p : Nat),
    (pile scale p xs).length = xs.length
  | [], _ => rfl
  | x :: xs, p => congrArg (· + 1) (length_pile scale xs (p + x))

/-- **Piled values tile**, whatever the scale. -/
theorem pile_tiles (scale : Nat → Nat) : ∀ (xs : List Nat) (p : Nat), Tiles (pile scale p xs)
  | [], _ => True.intro
  | [_], _ => True.intro
  | x :: y :: xs, p => ⟨rfl, pile_tiles scale (y :: xs) (p + x)⟩

/-- **Each band of a pile lies in the pile**: on a scale that rises, it starts at the length
of the first sum or after, ends where it starts or after, and ends at the length of the whole
sum or before. -/
theorem pile_mem {scale : Nat → Nat} (hs : Rising scale) : ∀ (xs : List Nat) (p : Nat),
    ∀ b ∈ pile scale p xs, scale p ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ scale (p + xs.sum)
  | [], _, _, h => nomatch h
  | x :: xs, p, b, h => by
    rw [List.sum_cons, ← Nat.add_assoc]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact ⟨Nat.le_refl _, hs _ _ (Nat.le_add_right p x), hs _ _ (Nat.le_add_right (p + x) _)⟩
    | inr h' =>
      have ih := pile_mem hs xs (p + x) b h'
      exact ⟨Nat.le_trans (hs _ _ (Nat.le_add_right p x)) ih.1, ih.2.1, ih.2.2⟩

/-- **A band is as wide as its value** on a scale of whole units. -/
theorem pile_times (k : Nat) : ∀ (xs : List Nat) (p : Nat),
    (pile (times k) p xs).map (fun b => b.2 - b.1) = xs.map (· * k)
  | [], _ => rfl
  | x :: xs, p => by
    show ((p + x) * k - p * k) :: (pile (times k) (p + x) xs).map (fun b => b.2 - b.1) =
      (x * k) :: xs.map (· * k)
    rw [pile_times k xs (p + x), Nat.add_mul, Nat.add_sub_cancel_left]

theorem rising_times (k : Nat) : Rising (times k) := fun _ _ h => Nat.mul_le_mul_right k h

theorem rising_ratio (num den : Nat) : Rising (ratio num den) := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul_right num h)

/-! ## What enters a node, and what leaves it -/

section

variable [DecidableEq ν]

/-- What the links of a list carry at a node on one side, link by link: `side` is the source
or the target of a link. -/
def valuesAt (carry : ε → Nat) (side : ε → ν) (v : ν) (links : List ε) : List Nat :=
  (links.filter fun e => decide (side e = v)).map carry

/-- **What enters a node**: the sum of what the links into it carry. -/
def enters (n : Network ε ν) (v : ν) : Nat := (valuesAt n.carry n.dst v n.links).sum

/-- **What leaves a node**: the sum of what the links out of it carry. -/
def leaves (n : Network ε ν) (v : ν) : Nat := (valuesAt n.carry n.src v n.links).sum

/-- **The value of a node**: the greater of what enters it and what leaves it. d3-sankey's
`computeNodeValues`. -/
def value (n : Network ε ν) (v : ν) : Nat := max (n.enters v) (n.leaves v)

/-- **A node conserves**: what enters it is what leaves it. -/
def Conserved (n : Network ε ν) (v : ν) : Prop := n.enters v = n.leaves v

instance (n : Network ε ν) (v : ν) : Decidable (n.Conserved v) :=
  inferInstanceAs (Decidable (n.enters v = n.leaves v))

/-! ## The columns -/

/-- The links as `Layers` reads them: the target of a link stands one column after its source,
at least. -/
def steps (n : Network ε ν) : Layers.Reading ε ν := ⟨n.src, n.dst, fun _ => 1⟩

/-- **The column of a node**: the longest way into it, in links. `order` is an order of the
nodes that serves the links (`Layers.serves`). d3-sankey's `computeNodeDepths`. -/
def depth (n : Network ε ν) (order : List ν) : ν → Nat :=
  let table := Layers.table n.steps n.links 0 order
  fun v => (Layers.read 0 table v).toNat

/-- The greatest of some numbers, and `0` of none. -/
def greatest (l : List Nat) : Nat := l.foldr max 0

/-- **The column of a node, with the ends in the last column**: a node that no link leaves
stands in the last column, and every other at its depth. d3-sankey's default, `justify`. -/
def justify (n : Network ε ν) (order : List ν) : ν → Nat :=
  let d := n.depth order
  let last := greatest (n.nodes.map d)
  fun v => if n.links.any (fun e => decide (n.src e = v)) then d v else last

end

/-! ## The measure, and where a node stands -/

/-- **The numbers of a picture of a network.** -/
structure Measure where
  /-- How far a node reaches across. -/
  thick : Nat
  /-- From the left side of one column to the left side of the next. -/
  stride : Nat
  /-- The gap between two nodes of a column. -/
  gap : Nat
  /-- The length of a quantity. -/
  scale : Nat → Nat

/-- A node with its place. -/
structure Node (ν : Type) where
  /-- The caller's node. -/
  node : ν
  /-- Its room. -/
  box : IBox

/-- A placed node moves with its box. -/
instance : Moves IVec (Node ν) where
  move d p := ⟨p.node, Moves.move d p.box⟩
  move_zero p := by
    cases p
    exact congrArg (Node.mk _) (Moves.move_zero _)
  move_move d e p := by
    cases p
    exact congrArg (Node.mk _) (Moves.move_move d e _)

/-- The room of a placed node is its box. -/
instance : Boxed (Node ν) where
  box p := p.box
  box_move _ _ := rfl

/-- **A link, placed**: the band where it leaves its source and the band where it enters its
target. Each band is a box with no width, on the side of the node: from `y0` to `y1` down. A
ribbon is drawn from the one to the other. -/
structure Channel (ε : Type) where
  /-- The caller's link. -/
  link : ε
  /-- The band on the right side of the source. -/
  out : IBox
  /-- The band on the left side of the target. -/
  into : IBox

/-- A placed link moves with its two bands. -/
instance : Moves IVec (Channel ε) where
  move d c := ⟨c.link, Moves.move d c.out, Moves.move d c.into⟩
  move_zero c := by
    cases c with
    | mk l o i =>
      show Channel.mk l (Moves.move 0 o) (Moves.move 0 i) = Channel.mk l o i
      rw [Moves.move_zero, Moves.move_zero]
  move_move d e c := by
    cases c with
    | mk l o i =>
      show Channel.mk l (Moves.move e (Moves.move d o)) (Moves.move e (Moves.move d i)) =
        Channel.mk l (Moves.move (d + e) o) (Moves.move (d + e) i)
      rw [Moves.move_move, Moves.move_move]

/-- The room of a placed link: the least box that holds its two bands. -/
instance : Boxed (Channel ε) where
  box c := IBox.hull c.out c.into
  box_move d c := IBox.hull_move d c.out c.into

namespace Channel

/-- The upper edge of a link: from the top of its band at the source to the top of its band at
the target. -/
def upper (c : Channel ε) : IVec × IVec := (⟨c.out.x0, c.out.y0⟩, ⟨c.into.x0, c.into.y0⟩)

/-- The lower edge of a link. -/
def lower (c : Channel ε) : IVec × IVec := (⟨c.out.x0, c.out.y1⟩, ⟨c.into.x0, c.into.y1⟩)

end Channel

/-- The band from `lo` to `hi` below `top`, on the upright line at `x`: a box with no width. -/
def band (x top lo hi : Nat) : IBox := ⟨x, (top + lo : Nat), x, (top + hi : Nat)⟩

/-- **The bands lie one below the other**: each starts where the one before it ends. -/
def Stacked : List IBox → Prop
  | a :: b :: rest => a.y1 = b.y0 ∧ Stacked (b :: rest)
  | _ => True

section

variable [DecidableEq ν]

/-- How far down its column a node stands: the lengths of the nodes of its column that are
before it in the list, and a gap after each. -/
def topIn (len : ν → Nat) (gap : Nat) (col : ν → Nat) : List ν → ν → Nat
  | [], _ => 0
  | u :: us, v =>
    if u = v then 0 else (if col u = col v then len u + gap else 0) + topIn len gap col us v

/-- **The length of a node**: its value on the scale. -/
def length (n : Network ε ν) (m : Measure) (v : ν) : Nat := m.scale (n.value v)

/-- How far down a node stands. -/
def top (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) : Nat :=
  topIn (n.length m) m.gap col n.nodes v

/-- How far across a node stands: its column. -/
def left (m : Measure) (col : ν → Nat) (v : ν) : Nat := col v * m.stride

/-- **Where a node stands**: across at its column, and down below the nodes of its column that
are before it. -/
def box (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) : IBox :=
  ⟨(left m col v : Nat), (n.top m col v : Nat), (left m col v + m.thick : Nat),
    (n.top m col v + n.length m v : Nat)⟩

/-- **The nodes, placed**, in a room that holds them. -/
def layout (n : Network ε ν) (m : Measure) (col : ν → Nat) : Layout (Node ν) where
  w := greatest (n.nodes.map fun v => left m col v + m.thick)
  h := greatest (n.nodes.map fun v => n.top m col v + n.length m v)
  items := n.nodes.map fun v => ⟨v, n.box m col v⟩

/-- One more quantity at a node. -/
def bump (acc : ν → Nat) (v : ν) (x : Nat) : ν → Nat := fun k => if k = v then acc k + x else acc k

/-- One link, placed, after links that left `out v` and brought `into v` at each node `v`:
its band at each end is from the length of the sum before it to the length of the sum with
it. -/
def channelAt (n : Network ε ν) (m : Measure) (col : ν → Nat) (out into : ν → Nat) (e : ε) :
    Channel ε where
  link := e
  out := band (left m col (n.src e) + m.thick) (n.top m col (n.src e))
    (m.scale (out (n.src e))) (m.scale (out (n.src e) + n.carry e))
  into := band (left m col (n.dst e)) (n.top m col (n.dst e))
    (m.scale (into (n.dst e))) (m.scale (into (n.dst e) + n.carry e))

/-- The links of a list, placed, after links that left `out v` and brought `into v` at each
node `v`. -/
def channelsFrom (n : Network ε ν) (m : Measure) (col : ν → Nat) :
    (ν → Nat) → (ν → Nat) → List ε → List (Channel ε)
  | _, _, [] => []
  | out, into, e :: es =>
    channelAt n m col out into e ::
      channelsFrom n m col (bump out (n.src e) (n.carry e)) (bump into (n.dst e) (n.carry e)) es

/-- **The links, placed**: each with the band where it leaves its source, on the right side of
that node, and the band where it enters its target, on the left side of that one. The bands at
a side lie in the order of the links. This is what a drawing of the links reads. -/
def channels (n : Network ε ν) (m : Measure) (col : ν → Nat) : List (Channel ε) :=
  channelsFrom n m col (fun _ => 0) (fun _ => 0) n.links

/-- **The bands of the links that leave a node**, in their order down its right side. -/
def outs (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) : List IBox :=
  ((n.channels m col).filter fun c => decide (n.src c.link = v)).map (·.out)

/-- **The bands of the links that enter a node**, in their order down its left side. -/
def ins (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) : List IBox :=
  ((n.channels m col).filter fun c => decide (n.dst c.link = v)).map (·.into)

/-! ## A scale that fits a room -/

/-- What one column has in a room `room` high: the length that is left after the gaps between
its nodes, and the sum of the values of its nodes, which share that length. -/
def share (n : Network ε ν) (col : ν → Nat) (gap room c : Nat) : Nat × Nat :=
  (room - ((n.nodes.filter fun u => decide (col u = c)).length - 1) * gap,
    ((n.nodes.filter fun u => decide (col u = c)).map n.value).sum)

/-- The lesser of two ratios, each a length and the quantity that has it. A ratio of no
quantity bounds nothing and is not taken. -/
def lesser (s best : Nat × Nat) : Nat × Nat :=
  if s.2 = 0 then best else if s.1 * best.2 < best.1 * s.2 then s else best

/-- **The scale that fits a room**, as a length and the quantity that has it: the greatest
length for each unit of quantity with which every column, with its gaps, is no higher than
`room`. It is the least ratio among the columns, and no more than the whole room for one unit.
d3-sankey's `ky` of `initializeNodeBreadths`. A measure takes it as `ratio k.1 k.2`. -/
def fit (n : Network ε ν) (col : ν → Nat) (gap room : Nat) : Nat × Nat :=
  (n.nodes.map col).foldr (fun c best => lesser (n.share col gap room c) best) (room, 1)

end

end Network

end Whatwg.Svg.Scene
