import Whatwg.Svg.Geometry.Monotone.Laws
import Whatwg.Svg.Geometry.Shape

/-!
# WhatwgTest.Svg.Monotone

The laws of the monotone curve (`Whatwg/Svg/Geometry/Monotone/Laws.lean`) read at a chart, and
the control that shows what they are for. d3's own vectors for the curve are in
`WhatwgTest/Svg/D3Monotone.lean`.

The chart is a count over time: nothing, nothing, ten, ten. No value is negative and none is
more than ten.

- The control: the cardinal spline of the kit through the same points goes below zero before
  the rise and above ten after it. It draws a count that the data never had.
- The laws at this chart: the monotone curve stays from `0` to `10` at every parameter of every
  piece, and it never falls.
-/

namespace WhatwgTest.Svg.Monotone

open Whatwg.Svg.Value

/-- A count over time: nothing, nothing, ten, ten. -/
def counts : List Vec := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 10⟩, ⟨3, 10⟩]

-- A control: the cardinal spline through the counts is below zero at the middle of a piece,
-- and above ten at the middle of another.
#guard (Curve.catmullRom.cubics counts).any fun c => decide ((c.pointAt (1 / 2)).y < 0)
#guard (Curve.catmullRom.cubics counts).any fun c => decide (10 < (c.pointAt (1 / 2)).y)

/-- **The monotone curve through the counts is never negative and never more than ten**, at
every parameter of every piece. The law at this chart. -/
example : ∀ c ∈ Curve.monotoneX counts, ∀ s : Rat, 0 ≤ s → s ≤ 1 →
    0 ≤ (c.pointAt s).y ∧ (c.pointAt s).y ≤ 10 :=
  fun _ hc _ h0 h1 => Curve.monotoneX_range counts (by decide) hc h0 h1

/-- **The monotone curve through the counts never falls**: the counts never fall, so each piece
ends no lower than it starts, and on each piece a later parameter is no lower. The two laws at
this chart. -/
example : ∀ c ∈ Curve.monotoneX counts, ∀ s t : Rat, 0 ≤ s → s ≤ t → t ≤ 1 →
    (c.pointAt s).y ≤ (c.pointAt t).y :=
  fun _ hc _ _ hs hst ht =>
    Curve.monotoneX_rises counts hc
      (Curve.monotoneX_related (fun a b => a.y ≤ b.y) counts (by decide) hc) hs hst ht

-- A finite evaluation that no law states: the curve has one piece between each two points,
-- and the level pieces are level at their middles.
#guard (Curve.monotoneX counts).map (fun c => (c.pointAt (1 / 2)).y) == [0, 5, 10]

end WhatwgTest.Svg.Monotone
