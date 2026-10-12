import Whatwg.Svg.Geometry.Pen

/-!
# Whatwg.Svg.Geometry.Pen.Laws

Owner: the laws of the path cursor and of the pen (slice S10 of `docs/SVG-PACKAGE-PLAN.md`;
ruling SV-44). The authority is the chapter Paths of SVG 2, sealed at
`vendor/w3c-svgwg-47e645ef/master/paths.html`: under `PathDataGeneralInformation` a relative
command starts at the current point, under `TermInitialPoint` a moveto sets the initial point
of a subpath, and under `PathDataClosePathCommand` a closepath returns to it.

What is stated:

- what each command does to the two points, as an equation (`Command.advance_…`);
- `Path.cursor_ofSubpaths_append`: the cursor of a path of several subpaths is that of its
  last subpath alone, because a moveto forgets where the path was;
- `Pen.cursor_path`: the cursor that a pen computes is the cursor of the path it builds, so
  `Pen.current` is the chapter's current point of that path and no field of its own;
- where each call of the pen leaves the current point. A closepath returns to the start of
  the pen's subpath for a pen that was built by its own calls (`Pen.Plain`): one that was
  handed a moveto as a command has started a subpath that the pen does not record.
-/

namespace Whatwg.Svg.Value

/-! ## The cursor over a list of commands -/

namespace Cursor

theorem run_nil (s : Cursor) : s.run [] = s := rfl

theorem run_cons (s : Cursor) (c : Command) (cs : List Command) :
    s.run (c :: cs) = (Command.advance s c).run cs := rfl

/-- The cursor after two lists is the cursor after the second, from that after the first. -/
theorem run_append (s : Cursor) (cs ds : List Command) : s.run (cs ++ ds) = (s.run cs).run ds :=
  List.foldl_append

/-- Segments to pairs keep the subpath. -/
theorem foldl_lineTo_start (relative : Bool) : ∀ (ps : List Point) (s : Cursor),
    (ps.foldl (fun c p => c.lineTo relative p) s).start = s.start
  | [], _ => rfl
  | p :: ps, s => foldl_lineTo_start relative ps (s.lineTo relative p)

/-- Horizontal segments keep the subpath. -/
theorem foldl_hTo_start (relative : Bool) : ∀ (xs : List Decimal) (s : Cursor),
    (xs.foldl (fun c x => c.hTo relative x) s).start = s.start
  | [], _ => rfl
  | x :: xs, s => foldl_hTo_start relative xs (s.hTo relative x)

/-- Vertical segments keep the subpath. -/
theorem foldl_vTo_start (relative : Bool) : ∀ (ys : List Decimal) (s : Cursor),
    (ys.foldl (fun c y => c.vTo relative y) s).start = s.start
  | [], _ => rfl
  | y :: ys, s => foldl_vTo_start relative ys (s.vTo relative y)

/-- Segments to the ends of a list of items keep the subpath. -/
theorem foldl_lineTo_map_start {α : Type} (relative : Bool) (f : α → Point) :
    ∀ (items : List α) (s : Cursor),
      (items.foldl (fun c item => c.lineTo relative (f item)) s).start = s.start
  | [], _ => rfl
  | item :: items, s => foldl_lineTo_map_start relative f items (s.lineTo relative (f item))

end Cursor

/-! ## One command -/

namespace Command

/-- A closepath returns to the initial point of the subpath, and the next subpath starts
there. -/
theorem advance_closepath (s : Cursor) (relative : Bool) :
    advance s (.closepath relative) = ⟨s.start, s.start⟩ := rfl

/-- An absolute moveto to one pair starts a subpath at the pair, wherever the path was. -/
theorem advance_moveto (s : Cursor) (p : Point) : advance s (.moveto false p []) = ⟨p, p⟩ := rfl

/-- A relative moveto to one pair starts a subpath at the current point moved by the pair. -/
theorem advance_moveto_relative (s : Cursor) (p : Point) :
    advance s (.moveto true p []) = ⟨s.current + p, s.current + p⟩ := rfl

/-- An absolute lineto ends at its pair. -/
theorem advance_lineto (s : Cursor) (p : Point) :
    advance s (.lineto false p []) = ⟨p, s.start⟩ := rfl

/-- A relative lineto ends at the current point moved by its pair. -/
theorem advance_lineto_relative (s : Cursor) (p : Point) :
    advance s (.lineto true p []) = ⟨s.current + p, s.start⟩ := rfl

/-- An absolute `H` changes the `x` of the current point. -/
theorem advance_horizontalLineto (s : Cursor) (x : Decimal) :
    advance s (.horizontalLineto false x []) = ⟨⟨x, s.current.y⟩, s.start⟩ := rfl

/-- An absolute `V` changes the `y` of the current point. -/
theorem advance_verticalLineto (s : Cursor) (y : Decimal) :
    advance s (.verticalLineto false y []) = ⟨⟨s.current.x, y⟩, s.start⟩ := rfl

/-- An absolute cubic ends at its last pair. -/
theorem advance_curveto (s : Cursor) (c1 c2 p : Point) :
    advance s (.curveto false (c1, c2, p) []) = ⟨p, s.start⟩ := rfl

/-- An absolute smooth cubic ends at its last pair. -/
theorem advance_smoothCurveto (s : Cursor) (c2 p : Point) :
    advance s (.smoothCurveto false (c2, p) []) = ⟨p, s.start⟩ := rfl

/-- An absolute quadratic ends at its last pair. -/
theorem advance_quadraticBezierCurveto (s : Cursor) (c p : Point) :
    advance s (.quadraticBezierCurveto false (c, p) []) = ⟨p, s.start⟩ := rfl

/-- An absolute arc ends at the point it names. -/
theorem advance_ellipticalArc (s : Cursor) (a : Arc) :
    advance s (.ellipticalArc false a []) = ⟨a.to, s.start⟩ := rfl

/-- A command that is no moveto keeps the subpath, or closes it and starts the next at the
same point. -/
theorem advance_start (s : Cursor) (c : Command) (h : c.isMoveto = false) :
    (advance s c).start = s.start := by
  cases c with
  | moveto relative first rest => exact Bool.noConfusion h
  | closepath relative => rfl
  | lineto relative first rest => exact Cursor.foldl_lineTo_start relative (first :: rest) s
  | horizontalLineto relative first rest => exact Cursor.foldl_hTo_start relative (first :: rest) s
  | verticalLineto relative first rest => exact Cursor.foldl_vTo_start relative (first :: rest) s
  | curveto relative first rest =>
    exact Cursor.foldl_lineTo_map_start relative (fun t : Point × Point × Point => t.2.2)
      (first :: rest) s
  | smoothCurveto relative first rest =>
    exact Cursor.foldl_lineTo_map_start relative (fun t : Point × Point => t.2) (first :: rest) s
  | quadraticBezierCurveto relative first rest =>
    exact Cursor.foldl_lineTo_map_start relative (fun t : Point × Point => t.2) (first :: rest) s
  | smoothQuadraticBezierCurveto relative first rest =>
    exact Cursor.foldl_lineTo_start relative (first :: rest) s
  | ellipticalArc relative first rest =>
    exact Cursor.foldl_lineTo_map_start relative (fun a : Arc => a.to) (first :: rest) s

end Command

/-- Commands with no moveto among them keep the initial point of the subpath. -/
theorem Cursor.run_start : ∀ (cs : List Command) (s : Cursor),
    (cs.all fun c => !c.isMoveto) = true → (s.run cs).start = s.start
  | [], _, _ => rfl
  | c :: cs, s, h => by
    rw [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [Cursor.run_cons, Cursor.run_start cs _ h.2, Command.advance_start s c h.1]

/-! ## A path of several subpaths -/

namespace Path

/-- The cursor of a path of one subpath. -/
theorem cursor_moveto (p : Point) (cs : List Command) :
    (Path.moveto false p [] cs).cursor = some ((Cursor.mk p p).run cs) := rfl

/-- The cursor of a path of several subpaths is the cursor of the last one alone: its moveto
forgets where the path was. -/
theorem cursor_ofSubpaths_append (subs : List (Point × List Command)) (p : Point)
    (cs : List Command) :
    (ofSubpaths (subs ++ [(p, cs)])).cursor = some ((Cursor.mk p p).run cs) := by
  cases subs with
  | nil => rw [List.nil_append, ofSubpaths_singleton, cursor_moveto]
  | cons first rest =>
    rw [List.cons_append, ofSubpaths, List.flatMap_append, List.flatMap_singleton, cursor_moveto,
      Cursor.run_append, Cursor.run_append, Cursor.run_cons, Command.advance_moveto]

end Path

/-! ## The pen -/

namespace Pen

/-- The cursor that the pen computes is the cursor of the path it builds: the two points of
the path chapter after the whole path. -/
theorem cursor_path (pen : Pen) : pen.path.cursor = some pen.cursor := by
  rw [Pen.path, Pen.subpaths, Path.cursor_ofSubpaths_append]
  rfl

/-- The current point of the pen is where the path it builds ends. -/
theorem endPoint_path (pen : Pen) : pen.path.endPoint = some pen.current := by
  rw [Path.endPoint, cursor_path]
  rfl

/-- A pen at a point has drawn nothing: both points are that point. -/
theorem cursor_begin (p : Point) : (begin p).cursor = ⟨p, p⟩ := rfl

/-- One more command moves the cursor as the chapter says. -/
theorem cursor_push (pen : Pen) (c : Command) :
    (pen.push c).cursor = Command.advance pen.cursor c := by
  show (Cursor.mk pen.start pen.start).run (pen.commands ++ [c]) = _
  rw [Cursor.run_append]
  rfl

/-- More commands move the cursor through each. -/
theorem cursor_pushAll (pen : Pen) (cs : List Command) :
    (pen.pushAll cs).cursor = pen.cursor.run cs := by
  show (Cursor.mk pen.start pen.start).run (pen.commands ++ cs) = _
  rw [Cursor.run_append]
  rfl

theorem current_begin (p : Point) : (begin p).current = p := rfl

/-- A new subpath starts at its point. -/
theorem cursor_moveTo (pen : Pen) (p : Point) : (pen.moveTo p).cursor = ⟨p, p⟩ := by
  rw [Pen.moveTo]
  cases pen.commands <;> rfl

theorem current_moveTo (pen : Pen) (p : Point) : (pen.moveTo p).current = p := by
  rw [Pen.current, cursor_moveTo]

theorem current_lineTo (pen : Pen) (p : Point) : (pen.lineTo p).current = p := by
  rw [Pen.current, Pen.lineTo, cursor_push]
  rfl

theorem current_hTo (pen : Pen) (x : Decimal) : (pen.hTo x).current = ⟨x, pen.current.y⟩ := by
  rw [Pen.current, Pen.hTo, cursor_push]
  rfl

theorem current_vTo (pen : Pen) (y : Decimal) : (pen.vTo y).current = ⟨pen.current.x, y⟩ := by
  rw [Pen.current, Pen.vTo, cursor_push]
  rfl

theorem current_curveTo (pen : Pen) (c1 c2 p : Point) : (pen.curveTo c1 c2 p).current = p := by
  rw [Pen.current, Pen.curveTo, cursor_push]
  rfl

theorem current_smoothTo (pen : Pen) (c2 p : Point) : (pen.smoothTo c2 p).current = p := by
  rw [Pen.current, Pen.smoothTo, cursor_push]
  rfl

theorem current_quadTo (pen : Pen) (c p : Point) : (pen.quadTo c p).current = p := by
  rw [Pen.current, Pen.quadTo, cursor_push]
  rfl

theorem current_arcTo (pen : Pen) (rx ry : Magnitude) (largeArc sweep : Bool) (p : Point)
    (rotation : Magnitude) : (pen.arcTo rx ry largeArc sweep p rotation).current = p := by
  rw [Pen.current, Pen.arcTo, cursor_push]
  rfl

/-- A closepath returns the pen to the initial point of its subpath, by the chapter's rule. -/
theorem cursor_close (pen : Pen) : pen.close.cursor = ⟨pen.cursor.start, pen.cursor.start⟩ := by
  rw [Pen.close, cursor_push]
  rfl

theorem plain_begin (p : Point) : (begin p).Plain = true := rfl

/-- A new subpath has no command, so the pen is plain. -/
theorem plain_moveTo (pen : Pen) (p : Point) : (pen.moveTo p).Plain = true := by
  rw [Pen.moveTo]
  cases pen.commands <;> rfl

/-- A command that is no moveto keeps the pen plain. -/
theorem plain_push (pen : Pen) (c : Command) (h : pen.Plain = true) (hc : c.isMoveto = false) :
    (pen.push c).Plain = true := by
  show (List.all (pen.commands ++ [c]) fun c => !c.isMoveto) = true
  rw [List.all_append, List.all_cons, List.all_nil, hc]
  exact (Bool.and_eq_true _ _).mpr ⟨h, rfl⟩

theorem plain_lineTo (pen : Pen) (p : Point) (h : pen.Plain = true) : (pen.lineTo p).Plain = true :=
  plain_push pen _ h rfl

theorem plain_hTo (pen : Pen) (x : Decimal) (h : pen.Plain = true) : (pen.hTo x).Plain = true :=
  plain_push pen _ h rfl

theorem plain_vTo (pen : Pen) (y : Decimal) (h : pen.Plain = true) : (pen.vTo y).Plain = true :=
  plain_push pen _ h rfl

theorem plain_curveTo (pen : Pen) (c1 c2 p : Point) (h : pen.Plain = true) :
    (pen.curveTo c1 c2 p).Plain = true :=
  plain_push pen _ h rfl

theorem plain_quadTo (pen : Pen) (c p : Point) (h : pen.Plain = true) :
    (pen.quadTo c p).Plain = true :=
  plain_push pen _ h rfl

theorem plain_close (pen : Pen) (h : pen.Plain = true) : pen.close.Plain = true :=
  plain_push pen _ h rfl

theorem plain_smoothTo (pen : Pen) (c2 p : Point) (h : pen.Plain = true) :
    (pen.smoothTo c2 p).Plain = true :=
  plain_push pen _ h rfl

theorem plain_arcTo (pen : Pen) (rx ry : Magnitude) (largeArc sweep : Bool) (p : Point)
    (rotation : Magnitude) (h : pen.Plain = true) :
    (pen.arcTo rx ry largeArc sweep p rotation).Plain = true :=
  plain_push pen _ h rfl

/-- Commands with no moveto among them keep the pen plain. -/
theorem plain_pushAll (pen : Pen) (cs : List Command) (h : pen.Plain = true)
    (hcs : (cs.all fun c => !c.isMoveto) = true) : (pen.pushAll cs).Plain = true := by
  show (List.all (pen.commands ++ cs) fun c => !c.isMoveto) = true
  rw [List.all_append, hcs]
  exact (Bool.and_eq_true _ _).mpr ⟨h, rfl⟩

theorem plain_linesTo (pen : Pen) (points : List Point) (h : pen.Plain = true) :
    (pen.linesTo points).Plain = true := by
  cases points with
  | nil => exact h
  | cons p rest => exact plain_push pen _ h rfl

theorem plain_curvesTo (pen : Pen) (segments : List (Point × Point × Point))
    (h : pen.Plain = true) : (pen.curvesTo segments).Plain = true := by
  cases segments with
  | nil => exact h
  | cons s rest => exact plain_push pen _ h rfl

/-- A rectangle is a closed subpath of its own: the pen is back at its corner. -/
theorem cursor_rect (pen : Pen) (corner : Point) (width height : Decimal) :
    (pen.rect corner width height).cursor = ⟨corner, corner⟩ := by
  rw [Pen.rect, cursor_pushAll, cursor_moveTo]
  rfl

theorem plain_rect (pen : Pen) (corner : Point) (width height : Decimal) :
    (pen.rect corner width height).Plain = true :=
  plain_pushAll _ _ (plain_moveTo pen corner) rfl

/-- The initial point of a plain pen's subpath is the pen's start. -/
theorem cursor_start_of_plain (pen : Pen) (h : pen.Plain = true) : pen.cursor.start = pen.start :=
  Cursor.run_start pen.commands ⟨pen.start, pen.start⟩ h

/-- A closepath returns a plain pen to the start of its subpath. -/
theorem current_close (pen : Pen) (h : pen.Plain = true) : pen.close.current = pen.start := by
  rw [Pen.current, cursor_close]
  exact cursor_start_of_plain pen h

end Pen

end Whatwg.Svg.Value
