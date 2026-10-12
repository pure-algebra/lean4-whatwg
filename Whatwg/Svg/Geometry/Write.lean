import Whatwg.Svg.Geometry.Pen.Laws
import Whatwg.Svg.Geometry.Rational
import Whatwg.Svg.Geometry.Box
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Length
import Whatwg.Svg.Value.Extent

/-!
# Whatwg.Svg.Geometry.Write

Owner: writing exact geometry into the typed values of an attribute (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-53). A program computes its segments and its boxes in
`Rat`, and this module is where they become a `Path` and a `ViewBox`, each coordinate rounded
once to a stated number of places (`Decimal.ofRat`).

**Segments into a path.** `Pen.cubic` writes one segment with the shortest command that draws
it:

- a segment that draws a straight line (`Cubic.isStraight`) is an `H`, a `V` or an `L`;
- any other is a `C`;
- a straight segment that ends where the pen stands, as written, writes nothing;
- a segment that does not start where the pen is, as a number, starts a subpath with a
  moveto.

`Pen.cubics` writes a list, `Path.ofCubics` is the path of a list, and `Path.ofLoops` the path
of several closed outlines, which a fill by the even-odd rule reads as a shape with holes.
An outline should be a chain: a list that is no chain is written as several subpaths, and the
closepath closes the last of them only.

The laws are about the path chapter's own meaning, `Pen.current` of
`Whatwg/Svg/Geometry/Cursor.lean`: after a segment the pen is at the end of the segment as
written (`Pen.current_cubic`); a chain is one subpath (`Pen.done_cubics`); the path of a list
ends at the end of its last segment (`Path.endPoint_ofCubics`).

**A box into a view box.** `Box.viewBox` rounds the least corner down and the far corner up,
so that the view box that is written holds what the box held.

What this module does not claim: that the path drawn is within some distance of the exact
segments, which follows from the half unit of each rounding and is not stated here; a law
that the view box of a box holds the box, which is so on the boxes a review tried; reading a
`Path` back into segments.
-/

namespace Whatwg.Svg.Value

namespace Cubic

/-- The command that draws the segment from the point `current`, with its coordinates at
`places` places: `H`, `V` or `L` for a segment that draws a straight line, and `C` for any
other. An `H` is written only where the end has the `y` of `current` as written, and a `V`
only where it has its `x`. -/
def command (c : Cubic) (places : Nat) (current : Point) : Command :=
  if c.isStraight then
    if (c.p3.round places).y = current.y then .horizontalLineto false (c.p3.round places).x []
    else if (c.p3.round places).x = current.x then .verticalLineto false (c.p3.round places).y []
    else .lineto false (c.p3.round places) []
  else .curveto false (c.p1.round places, c.p2.round places, c.p3.round places) []

theorem command_isMoveto (c : Cubic) (places : Nat) (current : Point) :
    (c.command places current).isMoveto = false := by
  unfold command
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- **The command ends at the end of the segment**, as written, from the point it was made
for. -/
theorem advance_command (c : Cubic) (places : Nat) (s : Cursor) :
    Command.advance s (c.command places s.current) = ⟨c.p3.round places, s.start⟩ := by
  unfold command
  split
  · split
    · next h =>
      show Cursor.mk ⟨(c.p3.round places).x, s.current.y⟩ s.start = _
      rw [← h]
    · split
      · next h =>
        show Cursor.mk ⟨s.current.x, (c.p3.round places).y⟩ s.start = _
        rw [← h]
      · rfl
  · rfl

end Cubic

namespace Pen

/-- The pen where the segment starts: the pen itself when it is at that point already, as a
number, and a new subpath there otherwise. The test reads the numbers and not their spelling,
so a pen that an earlier call left at `1.0` is at `1`. -/
def startAt (pen : Pen) (p : Point) : Pen :=
  if pen.current.toVec = p.toVec then pen else pen.moveTo p

/-- One segment: a moveto where the pen is not at its start, and its command. A segment that
draws a straight line and ends where the pen stands, as written, writes no command. -/
def cubic (pen : Pen) (c : Cubic) (places : Nat := 3) : Pen :=
  if c.isStraight ∧ (pen.startAt (c.p0.round places)).current = c.p3.round places then
    pen.startAt (c.p0.round places)
  else
    (pen.startAt (c.p0.round places)).push
      (c.command places (pen.startAt (c.p0.round places)).current)

/-- The segments of a list, in order. -/
def cubics (pen : Pen) (cs : List Cubic) (places : Nat := 3) : Pen :=
  cs.foldl (fun pen c => pen.cubic c places) pen

/-- The pen that draws a list of segments, and none for no segment. -/
def ofCubics? (cs : List Cubic) (places : Nat := 3) : Option Pen :=
  match cs with
  | [] => none
  | c :: rest => some ((Pen.begin (c.p0.round places)).cubics (c :: rest) places)

/-- The list with no last segment, where the list is a chain and that segment draws a straight
line back to the start of the first: a closepath draws the same line. A list of one segment,
and a list that is no chain, are kept whole. -/
def withoutReturn (cs : List Cubic) : List Cubic :=
  match cs, cs.getLast? with
  | first :: _ :: _, some last =>
    if Cubic.Chained cs ∧ last.isStraight ∧ last.p3 = first.p0 then cs.dropLast else cs
  | _, _ => cs

/-- The pen that draws a closed outline, and none for no segment. In a chain, a straight last
segment back to the start is left to the closepath. A list that is no chain is several
subpaths, and the closepath closes the last of them only. -/
def ofLoop? (cs : List Cubic) (places : Nat := 3) : Option Pen :=
  (ofCubics? (withoutReturn cs) places).map close

/-! ### Where the pen is -/

theorem plain_startAt (pen : Pen) (p : Point) (h : pen.Plain = true) :
    (pen.startAt p).Plain = true := by
  unfold startAt
  split
  · exact h
  · exact plain_moveTo pen p

/-- A pen that is where the segment starts is not moved. -/
theorem startAt_of_current (pen : Pen) (p : Point) (h : pen.current = p) : pen.startAt p = pen := by
  unfold startAt
  rw [if_pos (congrArg Point.toVec h)]

/-- The pen that starts at a point is at that point, as a number. -/
theorem toVec_current_startAt (pen : Pen) (p : Point) :
    (pen.startAt p).current.toVec = p.toVec := by
  unfold startAt
  split
  · next h => exact h
  · rw [current_moveTo]

/-- **After a segment the pen is at the end of the segment**, as written. -/
theorem current_cubic (pen : Pen) (c : Cubic) (places : Nat) :
    (pen.cubic c places).current = c.p3.round places := by
  unfold cubic
  split
  · next h => exact h.2
  · rw [Pen.current, cursor_push, Pen.current, Cubic.advance_command]

theorem plain_cubic (pen : Pen) (c : Cubic) (places : Nat) (h : pen.Plain = true) :
    (pen.cubic c places).Plain = true := by
  unfold cubic
  split
  · exact plain_startAt pen _ h
  · exact plain_push _ _ (plain_startAt pen _ h) (Cubic.command_isMoveto c places _)
theorem cubics_nil (pen : Pen) (places : Nat) : pen.cubics [] places = pen := rfl

theorem cubics_cons (pen : Pen) (c : Cubic) (cs : List Cubic) (places : Nat) :
    pen.cubics (c :: cs) places = (pen.cubic c places).cubics cs places := rfl

theorem cubics_append (pen : Pen) (cs ds : List Cubic) (places : Nat) :
    pen.cubics (cs ++ ds) places = (pen.cubics cs places).cubics ds places :=
  List.foldl_append

theorem plain_cubics : ∀ (cs : List Cubic) (pen : Pen) (places : Nat), pen.Plain = true →
    (pen.cubics cs places).Plain = true
  | [], _, _, h => h
  | c :: cs, pen, places, h => plain_cubics cs (pen.cubic c places) places (plain_cubic pen c places h)

/-- **After a list of segments the pen is at the end of the last one**, as written, and where
it was for no segment. -/
theorem current_cubics : ∀ (cs : List Cubic) (pen : Pen) (places : Nat),
    (pen.cubics cs places).current = ((cs.getLast?.map fun c => c.p3.round places).getD pen.current)
  | [], _, _ => rfl
  | [c], pen, places => current_cubic pen c places
  | c :: d :: cs, pen, places => by
    rw [cubics_cons, current_cubics (d :: cs) (pen.cubic c places) places, List.getLast?_cons_cons]
    rfl

/-- A segment that starts where the pen is adds its command to the subpath, or nothing, and
starts no subpath. -/
theorem cubic_of_current (pen : Pen) (c : Cubic) (places : Nat) (h : pen.current = c.p0.round places) :
    pen.cubic c places =
      if c.isStraight ∧ pen.current = c.p3.round places then pen
      else pen.push (c.command places pen.current) := by
  rw [cubic, startAt_of_current pen _ h]

theorem done_cubic_of_current (pen : Pen) (c : Cubic) (places : Nat)
    (h : pen.current = c.p0.round places) : (pen.cubic c places).done = pen.done ∧
      (pen.cubic c places).start = pen.start := by
  rw [cubic_of_current pen c places h]
  split <;> exact ⟨rfl, rfl⟩

/-- **A chain is one subpath**: from a pen that is at its start, a chain of segments starts no
subpath. -/
theorem done_cubics : ∀ (cs : List Cubic) (pen : Pen) (places : Nat), Cubic.Chained cs = true →
    (∀ c, cs.head? = some c → pen.current = c.p0.round places) →
    (pen.cubics cs places).done = pen.done ∧ (pen.cubics cs places).start = pen.start
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | [c], pen, places, _, h0 => done_cubic_of_current pen c places (h0 c rfl)
  | c :: d :: cs, pen, places, hc, h0 => by
    rw [Cubic.chained_cons, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := done_cubic_of_current pen c places (h0 c rfl)
    have h2 := done_cubics (d :: cs) (pen.cubic c places) places hc.2 (by
      intro e he
      cases he
      rw [current_cubic, hc.1])
    rw [cubics_cons]
    exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

end Pen

namespace Path

/-- The path of a list of segments: the empty path for none. A list that is a chain is one
subpath. -/
def ofCubics (cs : List Cubic) (places : Nat := 3) : Path :=
  match Pen.ofCubics? cs places with
  | none => .empty
  | some pen => pen.path

/-- The path of several closed outlines, each a subpath that ends in a closepath. An outline
of no segment writes nothing. -/
def ofLoops (loops : List (List Cubic)) (places : Nat := 3) : Path :=
  Pen.join (loops.filterMap fun cs => Pen.ofLoop? cs places)

/-- The path of one closed outline. -/
def ofLoop (cs : List Cubic) (places : Nat := 3) : Path := ofLoops [cs] places

/-- **The path of a list of segments ends at the end of the last one**, as written. -/
theorem endPoint_ofCubics (cs : List Cubic) (places : Nat) :
    (ofCubics cs places).endPoint = cs.getLast?.map fun c => c.p3.round places := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    show (((Pen.begin (c.p0.round places)).cubics (c :: rest) places).path).endPoint = _
    rw [Pen.endPoint_path, Pen.current_cubics]
    cases h : (c :: rest).getLast? with
    | none => exact absurd h (by rw [List.getLast?_eq_none_iff]; exact List.cons_ne_nil c rest)
    | some d => rfl

end Path

/-! ## A number into a length and a size -/

/-- The size that a decimal writes: its digits, and `0` for zero and for a negative one. -/
def Magnitude.ofDecimal (d : Decimal) : Magnitude :=
  if 0 < d.mantissa then ⟨d.mantissa.toNat, d.exponent⟩ else ⟨0, 0⟩

/-- A length in user units at `places` places. -/
def Length.ofRat (q : Rat) (places : Nat := 3) : Length := .user (.ofRat q places)

/-- A size in user units at `places` places: a negative one is zero. -/
def Extent.ofRat (q : Rat) (places : Nat := 3) : Extent :=
  .user (Magnitude.ofDecimal (.ofRat q places))

/-- A size in user units at `places` places: a negative one is zero. -/
def AutoExtent.ofRat (q : Rat) (places : Nat := 3) : AutoExtent :=
  .user (Magnitude.ofDecimal (.ofRat q places))

/-! ## A box into a view box -/

namespace Box

/-- The view box that holds the box, with each side rounded outwards at `places` places: the
least corner down, and the width and the height up from there. -/
def viewBox (b : Box) (places : Nat := 3) : ViewBox :=
  let lowX := (b.x0 * (10 : Rat) ^ places).floor
  let lowY := (b.y0 * (10 : Rat) ^ places).floor
  ⟨.fixed places lowX, .fixed places lowY,
    .ofDecimal (.fixed places ((b.x1 * (10 : Rat) ^ places).ceil - lowX)),
    .ofDecimal (.fixed places ((b.y1 * (10 : Rat) ^ places).ceil - lowY))⟩

end Box

end Whatwg.Svg.Value
