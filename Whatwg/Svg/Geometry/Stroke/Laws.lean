import Whatwg.Svg.Geometry.Stroke
import Whatwg.Svg.Geometry.Shape.Laws
import Whatwg.Svg.Geometry.Root.Laws
import Whatwg.Svg.Geometry.Grid

/-!
# Whatwg.Svg.Geometry.Stroke.Laws

Owner: the laws of the figures of `Whatwg/Svg/Geometry/Stroke.lean`. Each holds for every
centre line, every half-width and every count of steps and of places.

- **A smooth path through points** (`Curve.chained_through`, `Curve.through_starts`,
  `Curve.through_ends`): at every tension it is a chain, it starts a segment at every point
  but the last and ends one at every point but the first. So it passes through every point,
  from the first to the last (`Curve.through_head`, `Curve.through_last`).
- **A stroke is a closed outline** (`Stroke.closed_outline`, `Stroke.closed_stroke`): a chain
  that ends where it starts, for every two sides. `Path.ofLoops` asks for such a list: it
  writes a list that is no chain as several subpaths.
- **The move law** (`Stroke.stroke_move`): the stroke of a moved line is the stroke, moved. A
  stroke reads its line through its samples. A move of the line moves each sample's point and
  keeps its direction and its length (`Stroke.samples_move`), since a distance reads a
  difference of two points. A side adds an offset to each point (`Stroke.side_move`), and an
  outline through moved points is the outline, moved (`Stroke.outline_move`). The law asks of
  `snap` that it follows the move: `snap (v + d) = snap v + d`. The `snap` that does nothing
  follows every move, and one that rounds to a grid follows a move by a step of the grid. So a
  program may keep the stroke of a line at the origin and move it into place.
- **The band of a half-width** (`Stroke.organic_band`): without a tip, `Stroke.organic` stays
  within the share `amp` of `hw`, for every seed, wave, length of the line and place along it.
- **A collar** is closed, and the collar at a moved point is the collar, moved.
- **A reveal and an arrowhead** of a moved line are those of the line, moved.

The lemma under "For the other modules" is about a list of `Whatwg/Svg/Geometry/Shape.lean`
and serves the proofs after it.

What this module does not claim: a band for `Stroke.organic` with a tip; a bound on the
distance of an edge from the centre line; that an outline does not cross itself; a law for a
scaling or a turn of the plane, since a distance and a normal are rounded.
-/

namespace Whatwg.Svg.Value

/-! ## For the other modules -/

/-- The list of two points or more with each end twice. Its place is beside
`Curve.reflected_cons_cons` of `Whatwg/Svg/Geometry/Shape/Laws.lean`. -/
theorem Curve.doubled_cons_cons (a b : Vec) (rest : List Vec) :
    ∃ l, Curve.doubled (a :: b :: rest) = a :: a :: b :: rest ++ [l] :=
  ⟨_, rfl⟩

/-! ## A smooth path through points -/

namespace Curve

/-- A smooth path through points is a chain. -/
theorem chained_through (points : List Vec) (tension : Rat) :
    Cubic.Chained (through points tension) = true :=
  chained_windows _ (cardinalSegment_join _) _

/-- A smooth path through moved points is the path, moved. -/
theorem through_move (d : Vec) (points : List Vec) (tension : Rat) :
    through (points.map fun p => p + d) tension = (through points tension).map (Cubic.move d) := by
  unfold through
  rw [doubled_map]
  exact windows_map _ _ _ (cardinalSegment_move (cardinalScale tension) d) _

/-- A smooth path starts a segment at every point but the last. -/
theorem through_starts (points : List Vec) (tension : Rat) :
    (through points tension).map (fun s => s.p0) = points.dropLast := by
  unfold through
  rw [windows_cardinal_starts]
  match points with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := doubled_cons_cons a b rest
    rw [h]
    show ((a :: b :: rest) ++ [l]).dropLast.dropLast = (a :: b :: rest).dropLast
    rw [List.dropLast_concat]

/-- A smooth path ends a segment at every point but the first. -/
theorem through_ends (points : List Vec) (tension : Rat) :
    (through points tension).map (fun s => s.p3) = points.tail := by
  unfold through
  rw [windows_cardinal_ends]
  match points with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := doubled_cons_cons a b rest
    rw [h]
    show ((b :: rest) ++ [l]).dropLast = b :: rest
    rw [List.dropLast_concat]

/-- The first segment of a smooth path starts at the first point of its list. -/
theorem through_head (tension : Rat) : ∀ (points : List Vec) (y : Cubic),
    (through points tension).head? = some y → points.head? = some y.p0
  | [], _, h => by cases h
  | [_], _, h => by cases h
  | a :: b :: rest, y, h => by
    have e := congrArg List.head? (through_starts (a :: b :: rest) tension)
    rw [List.head?_map, h] at e
    exact e.symm

/-- The last segment of a smooth path ends at the last point of its list. -/
theorem through_last (tension : Rat) : ∀ (points : List Vec) (x : Cubic),
    (through points tension).getLast? = some x → points.getLast? = some x.p3
  | [], _, h => by cases h
  | [_], _, h => by cases h
  | a :: b :: rest, x, h => by
    have e := congrArg List.getLast? (through_ends (a :: b :: rest) tension)
    rw [List.getLast?_map, h] at e
    rw [List.getLast?_cons_cons]
    exact e.symm

/-- A smooth path with no segment is through one point at most: its first is its last. -/
theorem through_eq_nil (tension : Rat) : ∀ (points : List Vec) (a b : Vec),
    through points tension = [] → points.head? = some a → points.getLast? = some b → a = b
  | [], _, _, _, ha, _ => by cases ha
  | [_], _, _, _, ha, hb => by
    cases ha
    cases hb
    rfl
  | a :: b :: rest, _, _, h, _, _ => by
    have e := through_ends (a :: b :: rest) tension
    rw [h] at e
    cases e

end Curve

namespace Stroke

/-! ## The outline of two sides -/

/-- **The outline of two sides is a chain that ends where it starts**, for every two lists of
points and every tension. -/
theorem closed_outline (ahead back : List Vec) (tension : Rat) :
    Cubic.Closed (outline ahead back tension) = true := by
  unfold outline
  cases hae : ahead.getLast? with
  | none => rfl
  | some ae =>
    cases hbs : back.head? with
    | none => rfl
    | some bs =>
      cases hbe : back.getLast? with
      | none => rfl
      | some be =>
        cases has : ahead.head? with
        | none => rfl
        | some a0 =>
          have hmid : Cubic.Chained (Curve.through ahead tension ++ [Cubic.line ae bs] ++
              Curve.through back tension) = true := by
            have h := Curve.chained_bridge (Curve.through ahead tension)
              (Curve.through back tension) ahead.getLast? back.head?
              (Curve.chained_through ahead tension) (Curve.chained_through back tension)
              (Curve.through_last tension ahead) (Curve.through_head tension back)
            rw [hae, hbs] at h
            exact h
          have hall : Cubic.Chained (Curve.through ahead tension ++ [Cubic.line ae bs] ++
              Curve.through back tension ++ [Cubic.line be a0]) = true := by
            refine Cubic.chained_append _ _ hmid rfl ?_
            intro x y hx hy
            cases hy
            cases hr : Curve.through back tension with
            | nil =>
              rw [hr, List.append_nil, List.getLast?_concat] at hx
              cases hx
              exact Curve.through_eq_nil tension back bs be hr hbs hbe
            | cons s ss =>
              rw [hr, Curve.getLast?_append_cons] at hx
              have hx' := Curve.through_last tension back x (by rw [hr]; exact hx)
              rw [hbe] at hx'
              exact (Option.some.inj hx').symm
          refine Curve.closed_of _ hall ?_
          rw [List.getLast?_concat]
          cases hl : Curve.through ahead tension with
          | nil =>
            have e := Curve.through_eq_nil tension ahead a0 ae hl has hae
            rw [e]
            rfl
          | cons s ss =>
            have e := Curve.through_head tension ahead s (by rw [hl]; rfl)
            rw [has] at e
            exact e

/-- An outline of moved sides is the outline, moved. -/
theorem outline_move (d : Vec) (ahead back : List Vec) (tension : Rat) :
    outline (ahead.map fun p => p + d) (back.map fun p => p + d) tension =
      (outline ahead back tension).map (Cubic.move d) := by
  unfold outline
  rw [List.getLast?_map, List.head?_map, List.getLast?_map, List.head?_map]
  cases ahead.getLast? <;> cases back.head? <;> cases back.getLast? <;> cases ahead.head? <;>
    simp only [Option.map_none, Option.map_some, List.map_nil, List.map_append, List.map_cons,
      Curve.through_move, Cubic.move_line]

/-! ## The samples of a moved line -/

/-- The points of a moved segment are the points, moved, with the same directions
(`Cubic.move_pointAt`, `Cubic.move_direction`). -/
theorem stationsOf_move (d : Vec) (c : Cubic) (n : Nat) (first : Bool) :
    stationsOf (c.move d) n first = (stationsOf c n first).map fun x => (x.1 + d, x.2) := by
  simp only [stationsOf, List.map_map, Cubic.move_pointAt, Cubic.move_direction,
    Function.comp_def]

/-- The points of a moved line are the points, moved, with the same directions. -/
theorem stations_move (d : Vec) (cs : List Cubic) (n : Nat) :
    stations (cs.map (Cubic.move d)) n = (stations cs n).map fun x => (x.1 + d, x.2) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    simp only [List.map_cons, stations, stationsOf_move, List.map_append, List.flatMap_map,
      List.map_flatMap]

/-- Moved points are as far on from each other as the points were (`Vec.dist_move`). -/
theorem measured_move (d : Vec) (places : Nat) : ∀ (l : List (Vec × Vec)) (run : Rat) (prev : Vec),
    measured places run (prev + d) (l.map fun x => (x.1 + d, x.2)) =
      (measured places run prev l).map (Sample.move d)
  | [], _, _ => rfl
  | x :: rest, run, prev => by
    simp only [List.map_cons, measured, Vec.dist_move, measured_move d places rest]
    rfl

/-- **The samples of a moved line are the samples, moved**: each point moved, each direction
and each length kept. -/
theorem samples_move (d : Vec) (cs : List Cubic) (n places : Nat) :
    samples (cs.map (Cubic.move d)) n places = (samples cs n places).map (Sample.move d) := by
  unfold samples
  rw [stations_move]
  cases stations cs n with
  | nil => rfl
  | cons x rest =>
    simp only [List.map_cons, measured_move]
    rfl

/-- Moved samples are of a line of the same length. -/
theorem total_move (d : Vec) (ss : List Sample) : total (ss.map (Sample.move d)) = total ss := by
  unfold total
  rw [List.getLast?_map]
  cases ss.getLast? <;> rfl

/-! ## The move law of a stroke -/

/-- **A side of moved samples is the side, moved**, for a `snap` that follows the move. -/
theorem side_move (d : Vec) (snap : Vec → Vec) (h : ∀ v, snap (v + d) = snap v + d)
    (ss : List Sample) (half : Rat → Rat → Rat) (sign : Rat) (places : Nat) :
    side (ss.map (Sample.move d)) half sign snap places =
      (side ss half sign snap places).map fun p => p + d := by
  simp only [side, total_move, List.map_map]
  apply List.map_congr_left
  intro s _
  simp only [Function.comp, Sample.move]
  rw [Vec.add_right_comm, h]

/-- **Every stroke is a chain that ends where it starts**, for every centre line, every two
half-widths, every count of steps and of places and every `snap`. -/
theorem closed_stroke (cs : List Cubic) (right left : Rat → Rat → Rat) (n : Nat)
    (snap : Vec → Vec) (places : Nat) :
    Cubic.Closed (stroke cs right left n snap places) = true :=
  closed_outline _ _ _

/-- **The move law of a stroke.** For a `snap` that follows the move by `d`, the stroke of a
centre line moved by `d` is the stroke, moved by `d`: for every line, every two half-widths
and every count of steps and of places. With no `snap`, which is `id`, this is every move. -/
theorem stroke_move (d : Vec) (snap : Vec → Vec) (h : ∀ v, snap (v + d) = snap v + d)
    (cs : List Cubic) (right left : Rat → Rat → Rat) (n places : Nat) :
    stroke (cs.map (Cubic.move d)) right left n snap places =
      (stroke cs right left n snap places).map (Cubic.move d) := by
  simp only [stroke, samples_move, side_move d snap h]
  rw [← List.map_reverse, outline_move]

/-! ## The band of a half-width -/

/-- **A half-width that wanders stays in its band**: for a half-width and a share that are not
negative, `organic` without a tip differs from `hw` by at most the share `amp` of it, at every
seed, wave, length of the line and place along it. The envelope is in `[0, 1]` and the noise
in `[-1, 1]` (`Noise.envelope_band`, `Noise.two_band`). -/
theorem organic_band (seed : Nat) {hw amp : Rat} (hw0 : 0 ≤ hw) (hamp : 0 ≤ amp)
    (wave s whole : Rat) :
    hw * (1 - amp) ≤ organic seed hw amp wave false s whole ∧
      organic seed hw amp wave false s whole ≤ hw * (1 + amp) := by
  have henv := Noise.envelope_band (wave / 2) whole s
  have hv := Noise.two_band seed wave s
  simp only [organic, Bool.false_eq_true, false_and, if_false]
  -- The envelope and the noise are named before the arithmetic, so that the search does not
  -- unfold the noise down to its hash.
  generalize Noise.envelope (wave / 2) whole s = env at henv ⊢
  generalize Noise.two seed wave s = v at hv ⊢
  have a : 0 ≤ hw * amp := Rat.mul_nonneg hw0 hamp
  have b0 : 0 ≤ hw * amp * env := Rat.mul_nonneg a henv.1
  have b1 : hw * amp * env ≤ hw * amp * 1 := Rat.mul_le_mul_of_nonneg_left henv.2 a
  have c1 : hw * amp * env * v ≤ hw * amp * env * 1 := Rat.mul_le_mul_of_nonneg_left hv.2 b0
  have c0 : hw * amp * env * (-1) ≤ hw * amp * env * v := Rat.mul_le_mul_of_nonneg_left hv.1 b0
  constructor <;> grind

/-! ## A collar -/

/-- A collar is a chain that ends where it starts. -/
theorem closed_collar (p : Vec) (w r : Rat) (down : Bool) (k : Rat) :
    Cubic.Closed (collar p w r down k) = true := by
  simp only [collar, Cubic.Closed, Cubic.chained_cons, Cubic.chained_singleton, Cubic.line,
    Cubic.corner, List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some, decide_true,
    Bool.and_self, beq_self_eq_true]

/-- The collar at a moved point is the collar, moved. -/
theorem collar_move (d p : Vec) (w r : Rat) (down : Bool) (k : Rat) :
    collar (p + d) w r down k = (collar p w r down k).map (Cubic.move d) := by
  simp only [collar, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Cubic.ext <;> apply Vec.ext <;>
    simp only [Cubic.line, Cubic.corner, Cubic.move, Cubic.map, Vec.lerp, Vec.add_def] <;> grind

/-! ## An arrowhead -/

/-- The arrowhead of a moved segment is the arrowhead, moved (`Cubic.move_direction`,
`Cubic.move_line`). -/
theorem arrowhead_move (d : Vec) (c : Cubic) (along across : Rat) :
    arrowhead (c.move d) along across = (arrowhead c along across).map (Cubic.move d) := by
  have e : (c.move d).p3 = c.p3 + d := rfl
  simp only [arrowhead, Cubic.move_direction, e, List.map_cons, List.map_nil, Cubic.move_line,
    Vec.add_right_comm c.p3 d]

end Stroke

/-! ## A reveal -/

/-- **A moved list is revealed as the list, moved**, for every budget: a program may reveal a
line where it was laid out and move the result into place, or move it first. -/
theorem Cubic.revealed_move (d : Vec) : ∀ (cs : List Cubic) (budget : Rat),
    Cubic.revealed (cs.map (Cubic.move d)) budget = (Cubic.revealed cs budget).map (Cubic.move d)
  | [], _ => rfl
  | c :: rest, budget => by
    simp only [List.map_cons, Cubic.revealed, Cubic.move_taxi]
    split
    · rfl
    · split
      · rw [List.map_cons, Cubic.revealed_move d rest]
      · rw [List.map_cons, List.map_nil, Cubic.move_upTo]

/-! ## A stroke across the seam of whole units

`Whatwg/Svg/Geometry/Grid.lean` reads whole counts as exact points and rounds exact points to
whole counts. These three laws put a stroke across that seam. -/

namespace Stroke

open Whatwg.Svg.Scene (IVec ICubic Commutes)

/-- **A stroke commutes with every move**, as `Whatwg/Svg/Scene/Moves.lean` says it: the
stroke of a moved line is the stroke, moved. -/
theorem commutes_stroke (right left : Rat → Rat → Rat) (n places : Nat) :
    Commutes (fun cs : List Cubic => stroke cs right left n id places) :=
  fun d cs => stroke_move d id (fun _ => rfl) cs right left n places

/-- **A stroke whose side points end a stage on a grid moves with its line**, for every move by
a whole count of the grid. The numbers of such a stroke stay short, and its move law is kept. -/
theorem stroke_move_grid {s : Nat} (hs : 0 < s) (k : IVec) (cs : List Cubic)
    (right left : Rat → Rat → Rat) (n places : Nat) :
    stroke (cs.map (Cubic.move (Vec.ofGrid s k))) right left n (Vec.snap s) places =
      (stroke cs right left n (Vec.snap s) places).map (Cubic.move (Vec.ofGrid s k)) :=
  stroke_move (Vec.ofGrid s k) (Vec.snap s) (fun v => Vec.snap_add_ofGrid hs v k) cs right left n
    places

/-- **A stroke computed for a program that keeps whole units commutes with its moves.** The
line is read from whole counts, stroked in exact numbers, and the outline rounded down to whole
counts. A program that stores such an outline and moves it has the outline of the moved line
(`Commutes.stored`), with no proof about rounding of its own. -/
theorem commutes_onGrid {s : Nat} (hs : 0 < s) (right left : Rat → Rat → Rat) (n places : Nat) :
    Commutes (fun cs : List ICubic =>
      (stroke (cs.map (Cubic.ofGrid s)) right left n id places).map (Cubic.toGrid s)) :=
  Commutes.grid hs (commutes_stroke right left n places)

end Stroke
end Whatwg.Svg.Value
