import Whatwg.Svg.Geometry.Shape.Laws

/-!
# Whatwg.Svg.Geometry.Smooth

Owner: how smooth a spline is at its joints (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-64).

`Whatwg/Svg/Geometry/Shape/Laws.lean` proves that a spline is a chain: each segment starts
where the one before it ends. A chain may still have a corner at a joint. This module says that
the splines of the kit have none.

- `Cubic.Smooth`: a list of segments in which each starts where the one before it ends, with
  the velocity that one arrives with. A curve drawn through such a list has one tangent at
  every joint, and a point that travels along it does not change its speed there.
- `Curve.cardinalSegment_smooth`, `Curve.basisSegment_smooth`: a segment of a cardinal spline,
  and one of a basis spline, leaves a joint with the velocity the segment before arrives with.
- `Curve.smooth_windows`, and from it `smooth_cubics_cardinal`, `smooth_cubicsOpen` and
  `smooth_cubicsClosed`: every cardinal spline of `Curve`, and every open or closed basis
  spline, is smooth.
- `Cubic.bend0` and `Cubic.bend1`: the second difference of the control points at each end, a
  sixth of the acceleration there. `Curve.basisSegment_bend`: a basis spline keeps it across a
  joint, so it bends evenly.

What this module does not claim: that `Curve.cubics .basis` is smooth at its two ends, where a
straight segment joins the spline to the first and the last point: the direction is kept there
and the speed is not. That the curve of real parameters is differentiable is a statement about
real numbers: `Cubic.velocity` is the derivative (`analysis/WhatwgAnalysis/Velocity.lean`), and
gluing two such pieces is not stated yet.
-/

namespace Whatwg.Svg.Value

namespace Cubic

/-- A list of segments in which each starts where the one before it ends, with the velocity
that one arrives with. -/
def Smooth : List Cubic → Prop
  | a :: b :: rest => a.p3 = b.p0 ∧ a.velocity 1 = b.velocity 0 ∧ Smooth (b :: rest)
  | _ => True

/-- The second difference of the control points at the start: a sixth of the acceleration
there. -/
def bend0 (c : Cubic) : Vec := c.p0 - Vec.scale 2 c.p1 + c.p2

/-- The second difference of the control points at the end: a sixth of the acceleration
there. -/
def bend1 (c : Cubic) : Vec := c.p1 - Vec.scale 2 c.p2 + c.p3

/-- No segment and one segment have no joint. -/
theorem smooth_nil : Smooth [] := trivial

theorem smooth_singleton (c : Cubic) : Smooth [c] := trivial

/-- A smooth list is a chain. -/
theorem chained_of_smooth : ∀ cs : List Cubic, Smooth cs → Chained cs = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [chained_cons, chained_of_smooth (b :: rest) h.2.2, Bool.and_true]
    exact decide_eq_true h.1

end Cubic

namespace Curve

/-- A segment of a cardinal spline leaves a joint with the velocity the segment before it
arrives with: three times `k` of the chord of the joint's two neighbours. -/
theorem cardinalSegment_smooth (k : Rat) (a b c d e : Vec) :
    (cardinalSegment k a b c d).velocity 1 = (cardinalSegment k b c d e).velocity 0 := by
  rw [Cubic.velocity_one, Cubic.velocity_zero]
  apply Vec.ext <;> simp only [cardinalSegment, Vec.scale, Vec.add_def, Vec.sub_def] <;> grind

/-- A segment of a basis spline leaves a joint with the velocity the segment before it arrives
with: half the chord of the joint's two neighbours. -/
theorem basisSegment_smooth (a b c d e : Vec) :
    (basisSegment a b c d).velocity 1 = (basisSegment b c d e).velocity 0 := by
  rw [Cubic.velocity_one, Cubic.velocity_zero]
  apply Vec.ext <;> simp only [basisSegment, Vec.scale, Vec.add_def, Vec.sub_def] <;> grind

/-- A basis spline keeps its bend across a joint. -/
theorem basisSegment_bend (a b c d e : Vec) :
    (basisSegment a b c d).bend1 = (basisSegment b c d e).bend0 := by
  apply Vec.ext <;>
    simp only [Cubic.bend0, Cubic.bend1, basisSegment, Vec.scale, Vec.add_def, Vec.sub_def] <;>
    grind

/-- **The windows of a rule that joins smoothly are a smooth list.** -/
theorem smooth_windows {segment : Vec → Vec → Vec → Vec → Cubic}
    (join : ∀ a b c d e : Vec, (segment a b c d).p3 = (segment b c d e).p0)
    (smooth : ∀ a b c d e : Vec, (segment a b c d).velocity 1 = (segment b c d e).velocity 0) :
    ∀ points : List Vec, Cubic.Smooth (windows segment points)
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
  | [_, _, _] => trivial
  | [_, _, _, _] => trivial
  | a :: b :: c :: d :: e :: rest => by
    have ih := smooth_windows join smooth (b :: c :: d :: e :: rest)
    show Cubic.Smooth (segment a b c d :: segment b c d e :: windows segment (c :: d :: e :: rest))
    exact ⟨join a b c d e, smooth a b c d e, ih⟩

/-- **A cardinal spline is smooth**, from its first point to its last. -/
theorem smooth_cubics_cardinal (tension : Rat) (points : List Vec) :
    Cubic.Smooth ((Curve.cardinal tension).cubics points) :=
  smooth_windows (cardinalSegment_join _) (cardinalSegment_smooth _) _

/-- **An open spline is smooth**: cardinal or basis. -/
theorem smooth_cubicsOpen_cardinal (tension : Rat) (points : List Vec) :
    Cubic.Smooth ((Curve.cardinal tension).cubicsOpen points) :=
  smooth_windows (cardinalSegment_join _) (cardinalSegment_smooth _) _

theorem smooth_cubicsOpen_basis (points : List Vec) :
    Cubic.Smooth (Curve.basis.cubicsOpen points) :=
  smooth_windows basisSegment_join basisSegment_smooth _

/-- **A closed spline is smooth** at every joint between two of its segments: cardinal or
basis. -/
theorem smooth_cubicsClosed_cardinal (tension : Rat) (points : List Vec) :
    Cubic.Smooth ((Curve.cardinal tension).cubicsClosed points) :=
  smooth_windows (cardinalSegment_join _) (cardinalSegment_smooth _) _

theorem smooth_cubicsClosed_basis (points : List Vec) :
    Cubic.Smooth (Curve.basis.cubicsClosed points) :=
  smooth_windows basisSegment_join basisSegment_smooth _

end Curve

end Whatwg.Svg.Value
