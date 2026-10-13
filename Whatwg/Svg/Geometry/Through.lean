import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Geometry.Monotone.Laws

/-!
# Whatwg.Svg.Geometry.Through

Owner: a way to carry a curve through a list of points, as a value (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Geometry/Shape.lean` has nine forms of curve as one closed type, `Curve`, and its
line, its pen and its area take a `Curve`. A curve whose rule reads all the points at once, as
the monotone curve of `Whatwg/Svg/Geometry/Monotone.lean` does, cannot be a tenth form without
a new case in every law of that type. So it stood beside `Curve`, with no line and no area of
its own, and a caller put its area together by hand.

d3-shape has the same seam, and it is a value there: a curve is an object that a line and an
area are handed (`line().curve(c)`, `area().curve(c)` of `src/line.js` and `src/area.js`,
commit `a82254af78f0`; ISC licence, Copyright 2010-2022 Mike Bostock). Here it is a value with
its laws.

- `Curve.Through`: the function from a list of points to the pieces of the curve, with the four
  laws that every curve of the kit has. The pieces are a chain. The first piece starts at the
  first point, and the last ends at the last. The curve through moved points is the curve,
  moved.
- `Curve.toThrough c`: a form of `Curve` as such a value. `Curve.Through.monotoneX` and
  `Curve.Through.monotoneY`: the monotone curve along each axis.
- `Curve.Through.under g f`: the curve of `g` with the plane exchanged by `f` before and after,
  for an `f` that is its own inverse and takes a sum to the sum. `monotoneY` is `monotoneX`
  under the exchange of the two axes, so every law of a generator is a law of it with no proof
  of its own.
- `Curve.Through.areaCubics g top base`: the outline of the region between two lines, as
  `Curve.areaCubics` has it. `Curve.Through.line`, `link` and `area` are the paths, and
  `Pen.through` draws the curve with a pen. Each is `Shape.line`, `Shape.link`, `Shape.area` and
  `Pen.curve` for a generator, and those four are these at `Curve.toThrough c`
  (`Whatwg/Svg/Geometry/Through/Laws.lean`).

So an area under the monotone curve is `Curve.Through.monotoneX.area top base`, and a curve
that lands later gets a line, a pen and an area by giving its four laws once.

What this module does not claim: an open or a closed generator, as `Curve.cubicsOpen` and
`Curve.cubicsClosed` are, since neither starts at the first point; that a generator passes
through every point, which a basis spline does not; that a generator has a piece for two points
or more, which the monotone curve has not where the two are one point.
-/

namespace Whatwg.Svg.Value

/-! ## Where the monotone curve starts and ends -/

namespace Monotone

/-- The points with no repeat start with the first point. -/
theorem distinct_head? : ∀ l : List Vec, (distinct l).head? = l.head?
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    show (if a = b then distinct (b :: rest) else a :: distinct (b :: rest)).head? = some a
    split
    · next h => exact (distinct_head? (b :: rest)).trans (congrArg some h.symm)
    · rfl

/-- The points with no repeat end with the last point. -/
theorem distinct_getLast? : ∀ l : List Vec, (distinct l).getLast? = l.getLast?
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have ih := distinct_getLast? (b :: rest)
    have hh := distinct_head? (b :: rest)
    show (if a = b then distinct (b :: rest) else a :: distinct (b :: rest)).getLast? =
      (a :: b :: rest).getLast?
    rw [List.getLast?_cons_cons]
    split
    · exact ih
    · generalize distinct (b :: rest) = d at ih hh
      cases d with
      | nil => cases hh
      | cons x xs => exact List.getLast?_cons_cons.trans ih

end Monotone

namespace Curve

open Monotone

/-- A list whose front has a first item starts with that item. -/
theorem head?_of_dropLast {α : Type} : ∀ {l : List α} {x : α},
    l.dropLast.head? = some x → l.head? = some x
  | [], _, h => nomatch h
  | [_], _, h => nomatch h
  | _ :: _ :: _, _, h => h

/-- A list whose tail has a last item ends with that item. -/
theorem getLast?_of_tail {α : Type} : ∀ {l : List α} {x : α},
    l.tail.getLast? = some x → l.getLast? = some x
  | [], _, h => nomatch h
  | [_], _, h => nomatch h
  | _ :: _ :: _, _, h => List.getLast?_cons_cons.trans h

/-- **Pieces that start at every point but the last and end at every point but the first are a
chain.** A curve that passes through its points in order is one. -/
theorem chained_of_passing : ∀ (cs : List Cubic) (l : List Vec),
    cs.map (fun c => c.p0) = l.dropLast → cs.map (fun c => c.p3) = l.tail →
      Cubic.Chained cs = true
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | c :: d :: cs, l, h0, h3 => by
    match l, h0, h3 with
    | [], h0, _ => cases h0
    | [_], h0, _ => cases h0
    | [_, _], h0, _ => cases h0
    | x :: y :: z :: l', h0, h3 =>
      have hd : d.p0 = y := (List.cons.inj (List.cons.inj h0).2).1
      have hc : c.p3 = y := (List.cons.inj h3).1
      rw [Cubic.chained_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hc.trans hd.symm,
        chained_of_passing (d :: cs) (y :: z :: l') (List.cons.inj h0).2 (List.cons.inj h3).2⟩

/-- **The first piece of the monotone curve starts at the first point.** -/
theorem monotoneX_head_of (points : List Vec) (c : Cubic)
    (h : (monotoneX points).head? = some c) : points.head? = some c.p0 := by
  have e := congrArg List.head? (monotoneX_starts points)
  rw [List.head?_map, h] at e
  exact (distinct_head? points).symm.trans (head?_of_dropLast e.symm)

/-- **The last piece of the monotone curve ends at the last point.** -/
theorem monotoneX_getLast (points : List Vec) (c : Cubic)
    (h : (monotoneX points).getLast? = some c) : points.getLast? = some c.p3 := by
  have e := congrArg List.getLast? (monotoneX_ends points)
  rw [List.getLast?_map, h] at e
  exact (distinct_getLast? points).symm.trans (getLast?_of_tail e.symm)

/-! ## A generator -/

/-- **A way to carry a curve through a list of points**: the pieces of the curve, and the four
laws that a line, a pen and an area need of them. -/
structure Through where
  /-- The pieces of the curve through the points, in order. -/
  cubics : List Vec → List Cubic
  /-- The pieces are a chain: each starts where the one before it ends. -/
  chained : ∀ points : List Vec, Cubic.Chained (cubics points) = true
  /-- The first piece starts at the first point. -/
  starts : ∀ (points : List Vec) (c : Cubic),
    (cubics points).head? = some c → points.head? = some c.p0
  /-- The last piece ends at the last point. -/
  ends : ∀ (points : List Vec) (c : Cubic),
    (cubics points).getLast? = some c → points.getLast? = some c.p3
  /-- The curve through moved points is the curve, moved. -/
  moved : ∀ (d : Vec) (points : List Vec),
    cubics (points.map fun p => p + d) = (cubics points).map (Cubic.move d)

/-- **A form of `Curve` as a generator**: its curve from the first point to the last. -/
def toThrough (c : Curve) : Through where
  cubics := c.cubics
  chained := chained_cubics c
  starts := cubics_head_of c
  ends := cubics_getLast c
  moved := cubics_move c

namespace Through

/-- **The monotone curve along `x`** as a generator: d3's `curveMonotoneX`. -/
def monotoneX : Through where
  cubics := Curve.monotoneX
  chained := chained_monotoneX
  starts := monotoneX_head_of
  ends := monotoneX_getLast
  moved := monotoneX_move

/-- **The generator with the plane exchanged before and after**: the points go through `f`, the
curve of `g` is carried through them, and its pieces come back through `f`. It asks that `f` is
its own inverse and takes a sum to the sum, as the exchange of the two axes and a mirror in an
axis do. The four laws of `g` are then laws of the result. -/
def under (g : Through) (f : Vec → Vec) (hff : ∀ p, f (f p) = p)
    (hadd : ∀ p d, f (p + d) = f p + f d) : Through where
  cubics points := (g.cubics (points.map f)).map (Cubic.map f)
  chained points := Cubic.chained_map f _ (g.chained _)
  starts points c h := by
    rw [List.head?_map] at h
    cases hc : (g.cubics (points.map f)).head? with
    | none =>
      rw [hc] at h
      cases h
    | some c0 =>
      rw [hc] at h
      have hc' : c0.map f = c := Option.some.inj h
      subst hc'
      have e := g.starts _ c0 hc
      rw [List.head?_map] at e
      cases hp : points.head? with
      | none =>
        rw [hp] at e
        cases e
      | some p =>
        rw [hp] at e
        have e' : f p = c0.p0 := Option.some.inj e
        show some p = some (f c0.p0)
        rw [← e', hff]
  ends points c h := by
    rw [List.getLast?_map] at h
    cases hc : (g.cubics (points.map f)).getLast? with
    | none =>
      rw [hc] at h
      cases h
    | some c0 =>
      rw [hc] at h
      have hc' : c0.map f = c := Option.some.inj h
      subst hc'
      have e := g.ends _ c0 hc
      rw [List.getLast?_map] at e
      cases hp : points.getLast? with
      | none =>
        rw [hp] at e
        cases e
      | some p =>
        rw [hp] at e
        have e' : f p = c0.p3 := Option.some.inj e
        show some p = some (f c0.p3)
        rw [← e', hff]
  moved d points := by
    have e1 : (points.map fun p => p + d).map f = (points.map f).map fun p => p + f d := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun p _ => hadd p d
    show (g.cubics ((points.map fun p => p + d).map f)).map (Cubic.map f) =
      ((g.cubics (points.map f)).map (Cubic.map f)).map (Cubic.move d)
    rw [e1, g.moved, List.map_map, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    show (c.move (f d)).map f = (c.map f).move d
    apply Cubic.ext <;> show f (_ + f d) = f _ + d <;> rw [hadd, hff]

/-- **The monotone curve along `y`** as a generator: d3's `curveMonotoneY`. It is `monotoneX`
under the exchange of the two axes, and its pieces are `Curve.monotoneY`. -/
def monotoneY : Through := monotoneX.under Monotone.swap (fun _ => rfl) (fun _ _ => rfl)

/-! ## The line, the pen and the area of a generator -/

/-- **The outline of the region between two lines**: along `top`, straight to the last point of
`base`, and back along `base` taken in reverse. A closepath joins its end to its start. The way
back is carried by `back`, which is `g` itself unless another is given: a form whose steps turn
round on the way back names its flipped form there (`Curve.flip`). -/
def areaCubics (g : Through) (top base : List Vec) (back : Through := g) : List Cubic :=
  g.cubics top ++
    (match top.getLast?, base.getLast? with
      | some t, some b => [Cubic.line t b]
      | _, _ => []) ++
    back.cubics base.reverse

/-- The path of the curve through a list of points: the empty path where it has no piece. -/
def line (g : Through) (points : List Vec) (places : Nat := 3) : Path :=
  .ofCubics (g.cubics points) places

/-- The curve from one point to another. -/
def link (g : Through) (a b : Vec) (places : Nat := 3) : Path := g.line [a, b] places

/-- The closed region between two lines: along `top` in order, straight to the last point of
`base`, back along `base`, and closed. -/
def area (g : Through) (top base : List Vec) (places : Nat := 3) (back : Through := g) : Path :=
  .ofLoop (g.areaCubics top base back) places

end Through

end Curve

/-- The curve of a generator through a list of points, drawn by the pen. Its first point starts
a subpath where the pen is not there already. -/
def Pen.through (pen : Pen) (g : Curve.Through) (points : List Vec) (places : Nat := 3) : Pen :=
  pen.cubics (g.cubics points) places

end Whatwg.Svg.Value
