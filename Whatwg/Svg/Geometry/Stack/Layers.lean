import Whatwg.Svg.Geometry.Through

/-!
# Whatwg.Svg.Geometry.Stack.Layers

Owner: layers laid one upon another over the beats of a run, and the area of each (ask W19 of
the consumer's list; slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Stack.lean` has intervals in a row, each as long as its weight (`stack`):
that is a stack at one beat. This module has the same over several beats, with the layers as
the things that are named, and the areas between their edges. At each beat a pile of this
module is `stack` of that module (`Stack.column_pile` of the laws), so its laws of one beat are
laws of this one.

A run has several quantities at each of its beats: units held, offers waiting, takers waiting.
Drawn on one axis, each is a layer whose thickness at a beat is its value, and the layers lie
one upon another so that the eye reads each quantity and their sum. lean4-effect4 draws the
three counts of a queue so, by hand (`docs/research/2026-10-13-living-quantities/`): the takers
that wait are a deficit below zero, the units held fill a vessel, and the offers that wait
press above its brim.

The prior art is d3-shape's `stack` (`src/stack.js`, with `src/offset/none.js` and
`src/offset/diverging.js`, commit `a82254af78f0`; ISC licence, Copyright 2010-2022 Mike
Bostock), and its `area` (`src/area.js`) for the region between two lines.

A layer is its values, one for each beat. A stack is, for each layer, its **band**: at each
beat its baseline and its top. The top is the baseline and the value, so the height of a layer
at a beat is its value.

- `Stack.pile floor layers`: each layer upon the one before, the first upon `floor`. It is
  d3's `stackOffsetNone`. `Stack.plain layers` piles them upon zero, which is d3's `stack()`.
- `Stack.diverging layers`: d3's `stackOffsetDiverging`, as d3 has it: a value above zero is
  piled upward from zero, a value below zero downward from zero, and a value of zero stands at
  zero. Each band entry is the lower and the upper edge.
- `Stack.signed layers`: **the stack with a signed baseline.** A value above zero is piled
  upward from zero and a value below zero hangs downward from zero, as in `diverging`. It
  differs in two ways. A band entry is the baseline and the top, so the top of a layer that
  hangs is its lower edge, and the top less the baseline is the value with its sign. And a
  value of zero stands on the edge of its layer's own side (`Stack.hangs`: the lower side for a
  layer that has a value below zero) and not at zero. d3's rule is right for bars. For an area
  it is not: a layer that is nothing at one beat and something at the next would be drawn from
  zero across the layers under it.
- `Stack.bases`, `Stack.tops`, `Stack.heights`: the readings of a band. `Stack.span`: a band
  entry as its lower and its upper edge. `Stack.column bands b` and `Stack.valuesAt layers b`:
  the bands and the values of every layer at one beat. `Stack.layers rows`: the layers of rows
  that have one value for each layer at one beat, as d3's data has them.
- `Stack.edge xs ys`: the points of an edge, at the abscissae of the beats.
- `Curve.Through.between g xs band`: **the area between the two edges of a band**, as one
  outline: along the tops, straight across at the last beat, and back along the baselines. It
  is `Curve.Through.areaCubics` of the two edges, so an area between two monotone curves has no
  code of its own. `Stack.outlines g xs bands` and `Stack.paths` are the outlines and the paths
  of every layer.

The laws are in `Whatwg/Svg/Geometry/Stack/Layers/Laws.lean`. They say what holds at the beats,
which is exact, and what holds between them, which depends on the curve.

What this module does not claim: d3's other offsets (`expand`, `silhouette`, `wiggle`) and its
orders by size, which a caller applies to the list of layers; a value that is no number, which
d3 reads as zero and `Rat` does not have.
-/

namespace Whatwg.Svg.Value

namespace Stack

/-- The floor at zero: a `0` for each beat of the first layer. -/
def ground (layers : List (List Rat)) : List Rat :=
  List.replicate ((layers.head?.map List.length).getD 0) 0

/-- **Each layer upon the one before**, the first upon `floor`: the band of a layer is, at each
beat, the top of the layer before it and that top with the layer's value. d3's
`stackOffsetNone`. -/
def pile (floor : List Rat) : List (List Rat) → List (List (Rat × Rat))
  | [] => []
  | layer :: rest =>
    List.zipWith (fun b v => (b, b + v)) floor layer ::
      pile (List.zipWith (fun b v => b + v) floor layer) rest

/-- **The layers piled upon zero**: d3's `stack()` with its own order and offset. -/
def plain (layers : List (List Rat)) : List (List (Rat × Rat)) := pile (ground layers) layers

/-- The two edges of a stack at a beat after one more value: a value above zero raises the upper
edge, and a value below zero lowers the lower edge. -/
def grow (e : Rat × Rat) (v : Rat) : Rat × Rat :=
  if 0 < v then (e.1 + v, e.2) else if v < 0 then (e.1, e.2 + v) else e

/-- Where d3's diverging offset puts a value at a beat, as its lower and its upper edge: above
the upper edge of the stack, below its lower edge, or at zero for a value of zero. -/
def divergingAt (e : Rat × Rat) (v : Rat) : Rat × Rat :=
  if 0 < v then (e.1, e.1 + v) else if v < 0 then (e.2 + v, e.2) else (0, 0)

/-- d3's diverging offset from the two edges of a stack at each beat. -/
def divergingFrom (edges : List (Rat × Rat)) : List (List Rat) → List (List (Rat × Rat))
  | [] => []
  | layer :: rest =>
    List.zipWith divergingAt edges layer :: divergingFrom (List.zipWith grow edges layer) rest

/-- **d3's `stackOffsetDiverging`**: values above zero piled upward from zero, values below
zero downward from zero, and a value of zero at zero. Each entry is the lower and the upper
edge of the layer at the beat. -/
def diverging (layers : List (List Rat)) : List (List (Rat × Rat)) :=
  divergingFrom ((ground layers).map fun z => (z, z)) layers

/-- **A layer of the lower side**: it has a value below zero. Its values of zero stand on the
lower edge of the stack. -/
def hangs (layer : List Rat) : Bool := layer.any fun v => v < 0

/-- The baseline of a value at a beat: the upper edge of the stack for a value above zero, the
lower edge for a value below zero, and for a value of zero the edge of its layer's side. -/
def baseAt (down : Bool) (e : Rat × Rat) (v : Rat) : Rat :=
  if 0 < v then e.1 else if v < 0 then e.2 else if down then e.2 else e.1

/-- The baseline and the top of a value at a beat. -/
def signedAt (down : Bool) (e : Rat × Rat) (v : Rat) : Rat × Rat :=
  (baseAt down e v, baseAt down e v + v)

/-- The signed stack from the two edges of a stack at each beat. -/
def signedFrom (edges : List (Rat × Rat)) : List (List Rat) → List (List (Rat × Rat))
  | [] => []
  | layer :: rest =>
    List.zipWith (signedAt (hangs layer)) edges layer ::
      signedFrom (List.zipWith grow edges layer) rest

/-- **The stack with a signed baseline**: values above zero are piled upward from zero and
values below zero hang downward from zero, each layer in its order. Each entry is the baseline
and the top of the layer at the beat, and the top less the baseline is the value. A value of
zero stands on the edge of its layer's side. -/
def signed (layers : List (List Rat)) : List (List (Rat × Rat)) :=
  signedFrom ((ground layers).map fun z => (z, z)) layers

/-- The baselines of a band, beat by beat. -/
def bases (band : List (Rat × Rat)) : List Rat := band.map Prod.fst

/-- The tops of a band, beat by beat. -/
def tops (band : List (Rat × Rat)) : List Rat := band.map Prod.snd

/-- The heights of a band, beat by beat: the top less the baseline. -/
def heights (band : List (Rat × Rat)) : List Rat := band.map fun e => e.2 - e.1

/-- A band entry as its lower and its upper edge. -/
def span (e : Rat × Rat) : Rat × Rat := (min e.1 e.2, max e.1 e.2)

/-- The band entries of every layer at the beat `b`, in the order of the layers. -/
def column (bands : List (List (Rat × Rat))) (b : Nat) : List (Rat × Rat) :=
  bands.filterMap fun band => band[b]?

/-- The values of every layer at the beat `b`, in the order of the layers. -/
def valuesAt (layers : List (List Rat)) (b : Nat) : List Rat :=
  layers.filterMap fun layer => layer[b]?

/-- **The layers of rows**: each row has one value for each layer at one beat, as d3's data
has; the layer `i` is the value `i` of every row. A row that is short reads `0`. -/
def layers (rows : List (List Rat)) : List (List Rat) :=
  (List.range ((rows.head?.map List.length).getD 0)).map fun i => rows.map fun row => row.getD i 0

/-- The points of an edge: the abscissa of each beat with the height there. -/
def edge (xs ys : List Rat) : List Vec := List.zipWith Vec.mk xs ys

end Stack

/-- **The area between the two edges of a band**, as one outline: along the tops at the
abscissae `xs`, straight across at the last beat, and back along the baselines. A closepath
joins its end to its start. -/
def Curve.Through.between (g : Curve.Through) (xs : List Rat) (band : List (Rat × Rat))
    (back : Curve.Through := g) : List Cubic :=
  g.areaCubics (Stack.edge xs (Stack.tops band)) (Stack.edge xs (Stack.bases band)) back

namespace Stack

/-- The outline of every layer of a stack, at the abscissae `xs` of the beats. -/
def outlines (g : Curve.Through) (xs : List Rat) (bands : List (List (Rat × Rat))) :
    List (List Cubic) :=
  bands.map fun band => g.between xs band

/-- The closed path of every layer of a stack. -/
def paths (g : Curve.Through) (xs : List Rat) (bands : List (List (Rat × Rat)))
    (places : Nat := 3) : List Path :=
  (outlines g xs bands).map fun cs => Path.ofLoop cs places

end Stack

end Whatwg.Svg.Value
