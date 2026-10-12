import Whatwg.Svg.Geometry.Shape
import Whatwg.Svg.Geometry.Pen.Laws

/-!
# Whatwg.Svg.Geometry.Shape.Laws

Owner: the laws of the curves and shapes of `Whatwg/Svg/Geometry/Shape.lean` (slice S10 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-45). Each is stated by the cursor of
`Whatwg/Svg/Geometry/Cursor.lean`, the two points that the path chapter of SVG 2 keeps, and each
holds for every form: the seven exact ones, the cardinal spline and the basis spline.

- `Curve.run_through`: a curve through a list of points ends at the last of them, from
  wherever it starts, and stays in its subpath. For a spline this is exact though its control
  points are rounded, because a point of the data is never rounded.
- `Curve.through_plain`: no form starts a subpath.
- `Shape.cursor_line`: a line starts a subpath at its first point and ends at its last.
- `Shape.cursor_link`: a link from `a` to `b` ends at `b`.
- `Shape.cursor_area`: an area is closed: it ends where it started.
- `Pen.cursor_through`: a pen that draws through a list of points is at the last of them.

The proof of a form is a case split and `rfl`, or one induction on the list for a spline: the
cursor reads where a command ends and no control point, so no arithmetic is evaluated.
-/

namespace Whatwg.Svg.Value

namespace Curve

/-! ## The forms that join two points -/

/-- Every form between two points ends at the second, and keeps the subpath. -/
theorem run_pair (c : Curve) (s : Cursor) (a b : Point) : s.run (c.pair a b) = ⟨b, s.start⟩ := by
  cases c <;> rfl

theorem pair_plain (c : Curve) (a b : Point) : ((c.pair a b).all fun k => !k.isMoveto) = true := by
  cases c <;> rfl

theorem run_pairwise (c : Curve) : ∀ (points : List Point) (a : Point) (s : Cursor),
    s.run (c.pairwise a points) = ⟨last s.current points, s.start⟩
  | [], _, _ => rfl
  | b :: rest, a, s => by
    rw [pairwise, Cursor.run_append, run_pair, run_pairwise c rest b]
    rfl

theorem pairwise_plain (c : Curve) : ∀ (points : List Point) (a : Point),
    ((c.pairwise a points).all fun k => !k.isMoveto) = true
  | [], _ => rfl
  | b :: rest, a => by
    rw [pairwise, List.all_append, pair_plain, pairwise_plain c rest b]
    rfl

/-! ## The cardinal spline -/

/-- A cardinal spline ends at its last point, whatever its tension and its rounding. -/
theorem run_cardinalFrom (along : Point → Point) :
    ∀ (points : List Point) (before : Option Point) (a : Point) (s : Cursor),
      s.run (cardinalFrom along before a points) = ⟨last s.current points, s.start⟩
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | b :: c :: rest, before, a, s => by
    rw [cardinalFrom, Cursor.run_cons]
    show (Cursor.mk b s.start).run (cardinalFrom along (some a) b (c :: rest)) = _
    rw [run_cardinalFrom along (c :: rest) (some a) b]
    rfl

theorem cardinalFrom_plain (along : Point → Point) :
    ∀ (points : List Point) (before : Option Point) (a : Point),
      ((cardinalFrom along before a points).all fun k => !k.isMoveto) = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | b :: c :: rest, before, a => by
    rw [cardinalFrom, List.all_cons, cardinalFrom_plain along (c :: rest) (some a) b]
    rfl

/-! ## The basis spline -/

/-- The segments of a basis spline end at the last point: the straight segment that d3 draws
last reaches it exactly. -/
theorem run_basisFrom (places : Nat) : ∀ (points : List Point) (p q : Point) (s : Cursor),
    s.run (basisFrom places p q points) = ⟨last q points, s.start⟩
  | [], _, _, _ => rfl
  | r :: rest, p, q, s => by
    rw [basisFrom, Cursor.run_cons]
    show (Cursor.mk _ s.start).run (basisFrom places q r rest) = _
    rw [run_basisFrom places rest q r]
    rfl

theorem basisFrom_plain (places : Nat) : ∀ (points : List Point) (p q : Point),
    ((basisFrom places p q points).all fun k => !k.isMoveto) = true
  | [], _, _ => rfl
  | r :: rest, p, q => by
    rw [basisFrom, List.all_cons, basisFrom_plain places rest q r]
    rfl

theorem run_basisThrough (places : Nat) : ∀ (points : List Point) (a : Point) (s : Cursor),
    s.run (basisThrough places a points) = ⟨last s.current points, s.start⟩
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | b :: c :: rest, a, s => by
    rw [basisThrough, Cursor.run_cons]
    show (Cursor.mk _ s.start).run (basisFrom places a b (c :: rest)) = _
    rw [run_basisFrom places (c :: rest) a b]
    rfl

theorem basisThrough_plain (places : Nat) : ∀ (points : List Point) (a : Point),
    ((basisThrough places a points).all fun k => !k.isMoveto) = true
  | [], _ => rfl
  | [_], _ => rfl
  | b :: c :: rest, a => by
    rw [basisThrough, List.all_cons, basisFrom_plain places (c :: rest) a b]
    rfl

/-! ## Every form -/

/-- A curve through a list of points ends at the last of them, and keeps the subpath: for
every form, exactly. -/
theorem run_through (c : Curve) (points : List Point) (a : Point) (s : Cursor) :
    s.run (c.through a points) = ⟨last s.current points, s.start⟩ := by
  cases c with
  | cardinal tension places =>
    match points with
    | [] => rfl
    | [_] => rfl
    | b :: d :: rest => exact run_cardinalFrom _ (b :: d :: rest) none a s
  | basis places => exact run_basisThrough places points a s
  | linear => exact run_pairwise .linear points a s
  | stepX => exact run_pairwise .stepX points a s
  | stepY => exact run_pairwise .stepY points a s
  | stepBefore => exact run_pairwise .stepBefore points a s
  | stepAfter => exact run_pairwise .stepAfter points a s
  | bumpX => exact run_pairwise .bumpX points a s
  | bumpY => exact run_pairwise .bumpY points a s

/-- A curve through a list of points starts no subpath. -/
theorem through_plain (c : Curve) (points : List Point) (a : Point) :
    ((c.through a points).all fun k => !k.isMoveto) = true := by
  cases c with
  | cardinal tension places =>
    match points with
    | [] => rfl
    | [_] => rfl
    | b :: d :: rest => exact cardinalFrom_plain _ (b :: d :: rest) none a
  | basis places => exact basisThrough_plain places points a
  | linear => exact pairwise_plain .linear points a
  | stepX => exact pairwise_plain .stepX points a
  | stepY => exact pairwise_plain .stepY points a
  | stepBefore => exact pairwise_plain .stepBefore points a
  | stepAfter => exact pairwise_plain .stepAfter points a
  | bumpX => exact pairwise_plain .bumpX points a
  | bumpY => exact pairwise_plain .bumpY points a

/-- Every form between two points ends at the second, and keeps the subpath. -/
theorem run_join (c : Curve) (s : Cursor) (a b : Point) : s.run (c.join a b) = ⟨b, s.start⟩ := by
  rw [join, run_through]
  rfl

/-- The way back along a list of points starts no subpath. -/
theorem back_plain (c : Curve) : ∀ points : List Point,
    ((c.back points).all fun k => !k.isMoveto) = true
  | [] => rfl
  | q :: rest => by
    rw [back, List.all_cons, through_plain c rest q]
    rfl

end Curve

/-- A pen that draws through a list of points is at the last of them. -/
theorem Pen.cursor_through (pen : Pen) (c : Curve) (points : List Point) :
    (pen.through c points).cursor = ⟨Curve.last pen.current points, pen.cursor.start⟩ := by
  rw [Pen.through, Pen.cursor_pushAll, Curve.run_through]
  rfl

/-- A pen that draws through a list of points stays plain. -/
theorem Pen.plain_through (pen : Pen) (c : Curve) (points : List Point) (h : pen.Plain = true) :
    (pen.through c points).Plain = true :=
  Pen.plain_pushAll pen _ h (Curve.through_plain c points pen.current)

namespace Shape

/-- The line through no point is the empty path. -/
theorem cursor_line_nil (c : Curve) : (line c []).cursor = none := rfl

/-- A line starts a subpath at its first point and ends at its last. -/
theorem cursor_line (c : Curve) (p : Point) (rest : List Point) :
    (line c (p :: rest)).cursor = some ⟨Curve.last p rest, p⟩ := by
  rw [line, Path.cursor_moveto, Curve.run_through]

/-- A link from one point to another ends at the other. -/
theorem cursor_link (c : Curve) (a b : Point) : (link c a b).cursor = some ⟨b, a⟩ := by
  rw [link, Path.cursor_moveto, Curve.run_join]

/-- A cubic with a reach ends at its second point. -/
theorem cursor_bumpX (reach : Decimal) (a b : Point) : (bumpX reach a b).cursor = some ⟨b, a⟩ :=
  rfl

theorem cursor_bumpY (reach : Decimal) (a b : Point) : (bumpY reach a b).cursor = some ⟨b, a⟩ :=
  rfl

/-- An area is closed: its current point is back at its first point, where its one subpath
started. -/
theorem cursor_area (c : Curve) (p : Point) (rest base : List Point) :
    (area c (p :: rest) base).cursor = some ⟨p, p⟩ := by
  have plain :
      ((c.through p rest ++ c.flip.back base.reverse).all fun k => !k.isMoveto) = true := by
    rw [List.all_append, Curve.through_plain, Curve.back_plain]
    rfl
  rw [area, Path.cursor_moveto, Cursor.run_append, Cursor.run_cons, Cursor.run_nil,
    Command.advance_closepath, Cursor.run_start _ _ plain]

end Shape

end Whatwg.Svg.Value
