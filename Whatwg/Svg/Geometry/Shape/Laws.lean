import Whatwg.Svg.Geometry.Shape

/-!
# Whatwg.Svg.Geometry.Shape.Laws

Owner: the laws of the curves of `Whatwg/Svg/Geometry/Shape.lean` (slice S11 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-54). Each is about the exact segments in `Rat`, and each
holds for every form.

- **A chain from the first point to the last** (`chained_cubics`, `cubics_head`,
  `cubics_last`): every form through a list of points is a chain, and through two points or
  more it starts at the first and ends at the last. An open form is a chain too
  (`chained_cubicsOpen`).
- **A cardinal spline passes through every point** (`cardinal_starts`, `cardinal_ends`): its
  segments start at the points but the last, and end at the points but the first.
- **A closed form ends where it starts** (`closed_cubicsClosed`).
- **An area is a chain** (`chained_areaCubics`): along the top, straight across, and back along
  the base.
- **A curve through moved or scaled points is the curve, moved or scaled** (`cubics_move`,
  `cubicsOpen_move`, `cubicsClosed_move`, `areaCubics_move`, `cubics_scale`,
  `cubicsClosed_scale`). Both are cases of one law (`cubics_map`) for a map of the plane that
  the rule for two points and the two rules for four points follow.
- **The path as written** (`Pen.done_ofCubics?`, `Shape.endPoint_line`, `Shape.endPoint_link`):
  a chain is written as one subpath, and the path of a line ends at its last point, rounded
  once.

A spline is the windows of a list with points added beyond its ends, so its laws are those of
`windows` (`chained_windows`, `windows_map`) and of the three lists `reflected`, `doubled` and
`wrapped`. The arithmetic is in the laws of one segment, which `grind` proves.

What this module does not claim: that a basis spline passes through its points, which it does
not; a law for a turn of the plane, which the step and bump forms do not follow; a law for the
rounded coordinates of a path other than where it ends.
-/

namespace Whatwg.Svg.Value
namespace Curve

/-! ## Lists -/

/-- The last of a list before a list that is not empty is the last of the second. -/
theorem getLast?_append_cons {α : Type} : ∀ (xs : List α) (y : α) (ys : List α),
    (xs ++ y :: ys).getLast? = (y :: ys).getLast?
  | [], _, _ => rfl
  | [_], _, _ => List.getLast?_cons_cons
  | x :: x' :: xs, y, ys => by
    show (x :: x' :: (xs ++ y :: ys)).getLast? = _
    rw [List.getLast?_cons_cons]
    exact getLast?_append_cons (x' :: xs) y ys

/-- A list that is not empty has a last item. -/
theorem getLast?_cons_some {α : Type} (a : α) (l : List α) :
    ∃ last, (a :: l).getLast? = some last :=
  ⟨_, rfl⟩

/-- Two lists of one segment are equal when the segments are. -/
theorem list_one {a a' : Cubic} (h : a = a') : [a] = [a'] := by
  rw [h]

/-- Two lists of two segments are equal when the segments are. -/
theorem list_two {a b a' b' : Cubic} (ha : a = a') (hb : b = b') : [a, b] = [a', b'] := by
  rw [ha, hb]

/-- Two lists of three segments are equal when the segments are. -/
theorem list_three {a b c a' b' c' : Cubic} (ha : a = a') (hb : b = b') (hc : c = c') :
    [a, b, c] = [a', b', c'] := by
  rw [ha, hb, hc]

/-! ## Windows -/

/-- A list of `n` points has `n - 3` windows of four. -/
theorem length_windows (segment : Vec → Vec → Vec → Vec → Cubic) (points : List Vec) :
    (windows segment points).length = points.length - 3 := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | p0 :: p1 :: p2 :: p3 :: rest =>
    have ih := length_windows segment (p1 :: p2 :: p3 :: rest)
    show (windows segment (p1 :: p2 :: p3 :: rest)).length + 1 = (rest.length + 4) - 3
    rw [ih]
    show (rest.length + 3) - 3 + 1 = (rest.length + 4) - 3
    omega

/-- The windows of a rule whose segments join are a chain. -/
theorem chained_windows (segment : Vec → Vec → Vec → Vec → Cubic)
    (join : ∀ p0 p1 p2 p3 p4 : Vec, (segment p0 p1 p2 p3).p3 = (segment p1 p2 p3 p4).p0)
    (points : List Vec) : Cubic.Chained (windows segment points) = true := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | p0 :: p1 :: p2 :: p3 :: p4 :: rest =>
    show Cubic.Chained (segment p0 p1 p2 p3 :: segment p1 p2 p3 p4 ::
      windows segment (p2 :: p3 :: p4 :: rest)) = true
    rw [Cubic.chained_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨join p0 p1 p2 p3 p4, chained_windows segment join (p1 :: p2 :: p3 :: p4 :: rest)⟩

/-- A segment of a cardinal spline ends where the next one starts. -/
theorem cardinalSegment_join (k : Rat) (p0 p1 p2 p3 p4 : Vec) :
    (cardinalSegment k p0 p1 p2 p3).p3 = (cardinalSegment k p1 p2 p3 p4).p0 := rfl

/-- A segment of a basis spline ends where the next one starts. -/
theorem basisSegment_join (p0 p1 p2 p3 p4 : Vec) :
    (basisSegment p0 p1 p2 p3).p3 = (basisSegment p1 p2 p3 p4).p0 := rfl

/-- The windows of mapped points are the mapped windows, for a rule that follows the map. -/
theorem windows_map (segment : Vec → Vec → Vec → Vec → Cubic) (f : Vec → Vec) (g : Cubic → Cubic)
    (h : ∀ p0 p1 p2 p3 : Vec, segment (f p0) (f p1) (f p2) (f p3) = g (segment p0 p1 p2 p3))
    (points : List Vec) : windows segment (points.map f) = (windows segment points).map g := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | p0 :: p1 :: p2 :: p3 :: rest =>
    show segment (f p0) (f p1) (f p2) (f p3) :: windows segment ((p1 :: p2 :: p3 :: rest).map f) =
      g (segment p0 p1 p2 p3) :: (windows segment (p1 :: p2 :: p3 :: rest)).map g
    rw [h, windows_map segment f g h (p1 :: p2 :: p3 :: rest)]

/-- The first window of a list of four points or more holds its first three points. -/
theorem windows_head (segment : Vec → Vec → Vec → Vec → Cubic) (x y : Vec) (mid : List Vec)
    (u v : Vec) :
    ∃ w, (windows segment (x :: y :: mid ++ [u, v])).head? =
      some (segment x y (mid.head?.getD u) w) := by
  match mid with
  | [] => exact ⟨v, rfl⟩
  | [_] => exact ⟨u, rfl⟩
  | _ :: w :: _ => exact ⟨w, rfl⟩

/-- The last window of a list of four points or more holds its last three points. -/
theorem windows_getLast (segment : Vec → Vec → Vec → Vec → Cubic) (u v : Vec) :
    ∀ (mid : List Vec) (x y last : Vec), (y :: mid).getLast? = some last →
      ∃ w, (windows segment (x :: y :: mid ++ [u, v])).getLast? = some (segment w last u v)
  | [], x, _, _, h => by
    cases h
    exact ⟨x, rfl⟩
  | [_], _, y, _, h => by
    cases h
    exact ⟨y, rfl⟩
  | z :: w :: mid, x, y, last, h => by
    rw [List.getLast?_cons_cons] at h
    obtain ⟨w', hw'⟩ := windows_getLast segment u v (w :: mid) y z last h
    refine ⟨w', ?_⟩
    show (segment x y z w :: windows segment (y :: z :: (w :: mid) ++ [u, v])).getLast? = _
    rw [List.getLast?_cons, hw', Option.getD_some]

/-- Cardinal segments start at the points of a list but its first and its last two. -/
theorem windows_cardinal_starts (k : Rat) (points : List Vec) :
    (windows (cardinalSegment k) points).map (fun s => s.p0) = points.tail.dropLast.dropLast := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: p1 :: p2 :: p3 :: rest =>
    exact congrArg (List.cons p1) (windows_cardinal_starts k (p1 :: p2 :: p3 :: rest))

/-- Cardinal segments end at the points of a list but its first two and its last. -/
theorem windows_cardinal_ends (k : Rat) (points : List Vec) :
    (windows (cardinalSegment k) points).map (fun s => s.p3) = points.tail.tail.dropLast := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: p1 :: p2 :: p3 :: rest =>
    exact congrArg (List.cons p2) (windows_cardinal_ends k (p1 :: p2 :: p3 :: rest))

/-! ## The forms that join two points -/

/-- Two segments, the second starting where the first ends, are a chain. -/
theorem chained_two (a b : Cubic) (h : a.p3 = b.p0) : Cubic.Chained [a, b] = true := by
  rw [Cubic.chained_cons, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h, rfl⟩

/-- Three segments, each starting where the one before ends, are a chain. -/
theorem chained_three (a b c : Cubic) (hab : a.p3 = b.p0) (hbc : b.p3 = c.p0) :
    Cubic.Chained [a, b, c] = true := by
  rw [Cubic.chained_cons, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hab, chained_two b c hbc⟩

/-- The segments that join two points are a chain. -/
theorem chained_pair (c : Curve) (a b : Vec) : Cubic.Chained (c.pair a b) = true := by
  cases c with
  | stepX => exact chained_three _ _ _ rfl rfl
  | stepY => exact chained_three _ _ _ rfl rfl
  | stepBefore => exact chained_two _ _ rfl
  | stepAfter => exact chained_two _ _ rfl
  | _ => rfl

/-- The segments that join two points start at the first. -/
theorem pair_head (c : Curve) (a b : Vec) : (c.pair a b).head?.map (fun s => s.p0) = some a := by
  cases c <;> rfl

/-- The segments that join two points end at the second. -/
theorem pair_last (c : Curve) (a b : Vec) : (c.pair a b).getLast?.map (fun s => s.p3) = some b := by
  cases c <;> rfl

/-- Two points are joined by one segment or more. -/
theorem pair_cons (c : Curve) (a b : Vec) : ∃ s rest, c.pair a b = s :: rest := by
  cases c <;> exact ⟨_, _, rfl⟩

/-- The segments through two points or more start at the first. -/
theorem pairs_head (c : Curve) (a b : Vec) (rest : List Vec) :
    (c.pairs (a :: b :: rest)).head?.map (fun s => s.p0) = some a := by
  cases c <;> rfl

/-- The segments through two points or more end at the last. -/
theorem pairs_last (c : Curve) (a b : Vec) (rest : List Vec) :
    (c.pairs (a :: b :: rest)).getLast?.map (fun s => s.p3) = (a :: b :: rest).getLast? := by
  match rest with
  | [] =>
    show (c.pair a b ++ []).getLast?.map (fun s : Cubic => s.p3) = some b
    rw [List.append_nil]
    exact pair_last c a b
  | d :: rest =>
    obtain ⟨s, tail, hs⟩ := pair_cons c b d
    have ih := pairs_last c b d rest
    show (c.pair a b ++ (c.pair b d ++ c.pairs (d :: rest))).getLast?.map
      (fun s : Cubic => s.p3) = _
    rw [hs, List.cons_append, getLast?_append_cons, List.getLast?_cons_cons, ← ih]
    show _ = (c.pair b d ++ c.pairs (d :: rest)).getLast?.map (fun s : Cubic => s.p3)
    rw [hs, List.cons_append]

/-- The segments through a list of points, every two joined on their own, are a chain. -/
theorem chained_pairs (c : Curve) (points : List Vec) : Cubic.Chained (c.pairs points) = true := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [a, b] =>
    show Cubic.Chained (c.pair a b ++ []) = true
    rw [List.append_nil]
    exact chained_pair c a b
  | a :: b :: d :: rest =>
    show Cubic.Chained (c.pair a b ++ c.pairs (b :: d :: rest)) = true
    refine Cubic.chained_append _ _ (chained_pair c a b) (chained_pairs c (b :: d :: rest)) ?_
    intro x y hx hy
    have h1 := pair_last c a b
    have h2 := pairs_head c b d rest
    rw [hx] at h1
    rw [hy] at h2
    exact (Option.some.inj h1).trans (Option.some.inj h2).symm

/-! ## What stands beyond the ends -/

/-- The reflected list of two points or more: the second point, the list, and one point more. -/
theorem reflected_cons_cons (a b : Vec) (rest : List Vec) :
    ∃ l, reflected (a :: b :: rest) = b :: a :: b :: rest ++ [l] :=
  ⟨_, rfl⟩

/-- The reflected list without its first point and its last two is the list without its last. -/
theorem reflected_starts (points : List Vec) :
    (reflected points).tail.dropLast.dropLast = points.dropLast := by
  match points with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := reflected_cons_cons a b rest
    rw [h]
    show ((a :: b :: rest) ++ [l]).dropLast.dropLast = (a :: b :: rest).dropLast
    rw [List.dropLast_concat]

/-- The reflected list without its first two points and its last is the list without its first. -/
theorem reflected_ends (points : List Vec) :
    (reflected points).tail.tail.dropLast = points.tail := by
  match points with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    obtain ⟨l, h⟩ := reflected_cons_cons a b rest
    rw [h]
    show ((b :: rest) ++ [l]).dropLast = b :: rest
    rw [List.dropLast_concat]

/-- The reflected list of mapped points is the mapped reflected list. -/
theorem reflected_map (f : Vec → Vec) (points : List Vec) :
    reflected (points.map f) = (reflected points).map f := by
  unfold reflected
  rw [← List.map_tail, List.head?_map, ← List.map_dropLast, List.getLast?_map]
  cases points.tail.head? with
  | none => rfl
  | some second =>
    cases points.dropLast.getLast? with
    | none => rfl
    | some lastButOne =>
      show f second :: List.map f points ++ [f lastButOne] =
        List.map f (second :: points ++ [lastButOne])
      simp only [List.map_append, List.map_cons, List.map_nil]

/-- The doubled list of mapped points is the mapped doubled list. -/
theorem doubled_map (f : Vec → Vec) (points : List Vec) :
    doubled (points.map f) = (doubled points).map f := by
  unfold doubled
  rw [List.head?_map, List.getLast?_map]
  cases points.head? with
  | none => rfl
  | some first =>
    cases points.getLast? with
    | none => rfl
    | some last =>
      show f first :: List.map f points ++ [f last] = List.map f (first :: points ++ [last])
      simp only [List.map_append, List.map_cons, List.map_nil]

/-- The ring of a list that is not empty: its last point, the list, and its first two again. -/
theorem wrapped_cons (first : Vec) (rest : List Vec) (last : Vec)
    (h : (first :: rest).getLast? = some last) :
    wrapped (first :: rest) = last :: first :: rest ++ [first, rest.head?.getD first] := by
  simp only [wrapped, h]

/-- The ring of mapped points is the mapped ring. -/
theorem wrapped_map (f : Vec → Vec) (points : List Vec) :
    wrapped (points.map f) = (wrapped points).map f := by
  match points with
  | [] => rfl
  | first :: rest =>
    obtain ⟨last, h⟩ := getLast?_cons_some first rest
    have h' : (f first :: rest.map f).getLast? = some (f last) := by
      show ((first :: rest).map f).getLast? = some (f last)
      rw [List.getLast?_map, h, Option.map_some]
    show wrapped (f first :: rest.map f) = _
    rw [wrapped_cons _ _ _ h', wrapped_cons _ _ _ h, List.head?_map, Option.getD_map]
    simp only [List.map_append, List.map_cons, List.map_nil]

/-! ## A cardinal spline passes through every point -/

/-- A cardinal spline starts a segment at every point but the last. -/
theorem cardinal_starts (tension : Rat) (points : List Vec) :
    ((cardinal tension).cubics points).map (fun s => s.p0) = points.dropLast :=
  (windows_cardinal_starts (cardinalScale tension) (reflected points)).trans
    (reflected_starts points)

/-- A cardinal spline ends a segment at every point but the first. -/
theorem cardinal_ends (tension : Rat) (points : List Vec) :
    ((cardinal tension).cubics points).map (fun s => s.p3) = points.tail :=
  (windows_cardinal_ends (cardinalScale tension) (reflected points)).trans
    (reflected_ends points)

/-! ## The basis spline of three points or more -/

/-- A basis spline of three points or more: a straight start, the windows, and a straight end. -/
theorem cubics_basis_exists (a b d : Vec) (rest : List Vec) :
    ∃ (last : Vec) (wn : Cubic),
      (a :: b :: d :: rest).getLast? = some last ∧
      (windows basisSegment (doubled (a :: b :: d :: rest))).getLast? = some wn ∧
      basis.cubics (a :: b :: d :: rest) =
        Cubic.line a (basisSegment a a b d).p0 ::
          windows basisSegment (doubled (a :: b :: d :: rest)) ++ [Cubic.line wn.p3 last] :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- The same, for a last point and a last window that are given. -/
theorem cubics_basis_of (a b d : Vec) (rest : List Vec) (last : Vec) (wn : Cubic)
    (h1 : (a :: b :: d :: rest).getLast? = some last)
    (h2 : (windows basisSegment (doubled (a :: b :: d :: rest))).getLast? = some wn) :
    basis.cubics (a :: b :: d :: rest) =
      Cubic.line a (basisSegment a a b d).p0 ::
        windows basisSegment (doubled (a :: b :: d :: rest)) ++ [Cubic.line wn.p3 last] := by
  obtain ⟨last', wn', h1', h2', h⟩ := cubics_basis_exists a b d rest
  rw [h1] at h1'
  rw [h2] at h2'
  cases h1'
  cases h2'
  exact h

/-- The first window of the doubled list of three points or more. -/
theorem windows_doubled_head (a b d : Vec) (rest : List Vec) :
    (windows basisSegment (doubled (a :: b :: d :: rest))).head? = some (basisSegment a a b d) :=
  rfl

/-- A basis spline is a chain. -/
theorem chained_cubics_basis (points : List Vec) : Cubic.Chained (basis.cubics points) = true := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: d :: rest =>
    obtain ⟨last, wn, _, h2, h⟩ := cubics_basis_exists a b d rest
    rw [h]
    refine Cubic.chained_append _ _ ?_ rfl ?_
    · show Cubic.Chained ([Cubic.line a (basisSegment a a b d).p0] ++
        windows basisSegment (doubled (a :: b :: d :: rest))) = true
      refine Cubic.chained_append _ _ rfl (chained_windows basisSegment basisSegment_join _) ?_
      intro x y hx hy
      rw [windows_doubled_head] at hy
      cases hx
      cases hy
      rfl
    · intro x y hx hy
      rw [List.getLast?_cons, h2, Option.getD_some] at hx
      cases hx
      cases hy
      rfl

/-! ## Every form: a chain from the first point to the last -/

/-- A curve through no point has no segment. -/
theorem cubics_nil (c : Curve) : c.cubics [] = [] := by
  cases c <;> rfl

/-- A curve through one point has no segment. -/
theorem cubics_singleton (c : Curve) (a : Vec) : c.cubics [a] = [] := by
  cases c <;> rfl

/-- Every form through a list of points is a chain. -/
theorem chained_cubics (c : Curve) (points : List Vec) :
    Cubic.Chained (c.cubics points) = true := by
  cases c with
  | cardinal tension =>
    exact chained_windows (cardinalSegment (cardinalScale tension))
      (cardinalSegment_join (cardinalScale tension)) (reflected points)
  | basis => exact chained_cubics_basis points
  | _ => exact chained_pairs _ points

/-- Every form through two points or more starts at the first. -/
theorem cubics_head (c : Curve) (a b : Vec) (rest : List Vec) :
    (c.cubics (a :: b :: rest)).head?.map (fun s => s.p0) = some a := by
  cases c with
  | cardinal tension =>
    have h := congrArg List.head? (cardinal_starts tension (a :: b :: rest))
    rw [List.head?_map] at h
    exact h
  | basis =>
    cases rest with
    | nil => rfl
    | cons d rest =>
      obtain ⟨last, wn, _, _, h⟩ := cubics_basis_exists a b d rest
      rw [h]
      rfl
  | _ => exact pairs_head _ a b rest

/-- Every form through two points or more ends at the last. -/
theorem cubics_last (c : Curve) (a b : Vec) (rest : List Vec) :
    (c.cubics (a :: b :: rest)).getLast?.map (fun s => s.p3) = (a :: b :: rest).getLast? := by
  cases c with
  | cardinal tension =>
    have h := congrArg List.getLast? (cardinal_ends tension (a :: b :: rest))
    rw [List.getLast?_map] at h
    rw [List.getLast?_cons_cons]
    exact h
  | basis =>
    cases rest with
    | nil => rfl
    | cons d rest =>
      obtain ⟨last, wn, h1, _, h⟩ := cubics_basis_exists a b d rest
      rw [h, List.getLast?_concat, h1, Option.map_some]
      rfl
  | _ => exact pairs_last _ a b rest

/-- The last segment of a curve ends at the last point of its list. -/
theorem cubics_getLast (c : Curve) : ∀ (points : List Vec) (x : Cubic),
    (c.cubics points).getLast? = some x → points.getLast? = some x.p3
  | [], _, h => by
    rw [cubics_nil] at h
    cases h
  | [_], _, h => by
    rw [cubics_singleton] at h
    cases h
  | a :: b :: rest, x, h => by
    have e := cubics_last c a b rest
    rw [h] at e
    exact e.symm

/-- The first segment of a curve starts at the first point of its list. -/
theorem cubics_head_of (c : Curve) : ∀ (points : List Vec) (y : Cubic),
    (c.cubics points).head? = some y → points.head? = some y.p0
  | [], _, h => by
    rw [cubics_nil] at h
    cases h
  | [_], _, h => by
    rw [cubics_singleton] at h
    cases h
  | a :: b :: rest, y, h => by
    have e := cubics_head c a b rest
    rw [h] at e
    exact e.symm

/-- Every open form is a chain. -/
theorem chained_cubicsOpen (c : Curve) (points : List Vec) :
    Cubic.Chained (c.cubicsOpen points) = true := by
  cases c with
  | cardinal tension =>
    exact chained_windows (cardinalSegment (cardinalScale tension))
      (cardinalSegment_join (cardinalScale tension)) points
  | basis => exact chained_windows basisSegment basisSegment_join points
  | _ => exact chained_pairs _ points.tail.dropLast

/-! ## A closed form ends where it starts -/

/-- A chain whose last segment ends where its first starts is closed. -/
theorem closed_of : ∀ (cs : List Cubic), Cubic.Chained cs = true →
    cs.getLast?.map (fun s => s.p3) = cs.head?.map (fun s => s.p0) → Cubic.Closed cs = true
  | [], _, _ => rfl
  | c :: rest, hc, h => by
    have h' : (c :: rest).getLast?.map (fun s => s.p3) = some c.p0 := h
    show (Cubic.Chained (c :: rest) &&
      ((c :: rest).getLast?.map (fun s => s.p3) == some c.p0)) = true
    rw [hc, h', Bool.true_and]
    exact beq_self_eq_true _

/-- The windows of a ring, for a rule whose segments join, are closed. -/
theorem closed_windows_wrapped (segment : Vec → Vec → Vec → Vec → Cubic)
    (join : ∀ p0 p1 p2 p3 p4 : Vec, (segment p0 p1 p2 p3).p3 = (segment p1 p2 p3 p4).p0)
    (points : List Vec) : Cubic.Closed (windows segment (wrapped points)) = true := by
  match points with
  | [] => rfl
  | first :: rest =>
    obtain ⟨last, hl⟩ := getLast?_cons_some first rest
    rw [wrapped_cons first rest last hl]
    obtain ⟨w, hw⟩ := windows_head segment last first rest first (rest.head?.getD first)
    obtain ⟨w', hw'⟩ :=
      windows_getLast segment first (rest.head?.getD first) rest last first last hl
    refine closed_of _ (chained_windows segment join _) ?_
    rw [hw, hw']
    exact congrArg some (join w' last first (rest.head?.getD first) w)

/-- The segments through a list and back to its first point are closed. -/
theorem closed_pairs_ring (c : Curve) (first : Vec) (rest : List Vec) :
    Cubic.Closed (c.pairs (first :: rest ++ [first])) = true := by
  refine closed_of _ (chained_pairs c _) ?_
  match rest with
  | [] => exact (pairs_last c first first []).trans (pairs_head c first first []).symm
  | second :: rest =>
    have h1 := pairs_last c first second (rest ++ [first])
    have h2 := pairs_head c first second (rest ++ [first])
    have h3 : (first :: second :: (rest ++ [first])).getLast? = some first :=
      List.getLast?_concat (l := first :: second :: rest)
    exact (h1.trans h3).trans h2.symm

/-- Every closed form is a chain that ends where it starts. -/
theorem closed_cubicsClosed (c : Curve) (points : List Vec) :
    Cubic.Closed (c.cubicsClosed points) = true := by
  cases c with
  | cardinal tension =>
    exact closed_windows_wrapped (cardinalSegment (cardinalScale tension))
      (cardinalSegment_join (cardinalScale tension)) points
  | basis => exact closed_windows_wrapped basisSegment basisSegment_join points
  | _ =>
    cases points with
    | nil => rfl
    | cons first rest => exact closed_pairs_ring _ first rest

/-! ## An area is a chain -/

/-- A form flipped twice is the form. -/
theorem flip_flip (c : Curve) : c.flip.flip = c := by
  cases c <;> rfl

/-- Two chains with the straight segment from the end of one to the start of the other are one. -/
theorem chained_bridge (front back : List Cubic) (t b : Option Vec)
    (hfront : Cubic.Chained front = true) (hback : Cubic.Chained back = true)
    (ht : ∀ x, front.getLast? = some x → t = some x.p3)
    (hb : ∀ y, back.head? = some y → b = some y.p0) :
    Cubic.Chained (front ++
      (match (generalizing := false) t, b with
        | some t, some b => [Cubic.line t b]
        | _, _ => []) ++ back) = true := by
  cases t with
  | none =>
    have hnil : front = [] := by
      cases hl : front.getLast? with
      | none => exact List.getLast?_eq_none_iff.mp hl
      | some x => cases ht x hl
    subst hnil
    exact hback
  | some tv =>
    cases b with
    | none =>
      have hnil : back = [] := by
        cases hl : back.head? with
        | none => exact List.head?_eq_none_iff.mp hl
        | some y => cases hb y hl
      subst hnil
      show Cubic.Chained (front ++ [] ++ []) = true
      rw [List.append_nil, List.append_nil]
      exact hfront
    | some bv =>
      show Cubic.Chained (front ++ [Cubic.line tv bv] ++ back) = true
      refine Cubic.chained_append _ _ (Cubic.chained_append _ _ hfront rfl ?_) hback ?_
      · intro x y hx hy
        cases hy
        cases ht x hx
        rfl
      · intro x y hx hy
        rw [List.getLast?_concat] at hx
        cases hx
        cases hb y hy
        rfl

/-- The outline of an area is a chain. -/
theorem chained_areaCubics (c : Curve) (top base : List Vec) :
    Cubic.Chained (c.areaCubics top base) = true :=
  chained_bridge (c.cubics top) (c.flip.cubics base.reverse) top.getLast? base.getLast?
    (chained_cubics c top) (chained_cubics c.flip base.reverse)
    (fun x hx => cubics_getLast c top x hx)
    (fun y hy => by
      have h := cubics_head_of c.flip base.reverse y hy
      rw [List.head?_reverse] at h
      exact h)

/-! ## A curve through mapped points is the curve, mapped

One law for a map of the plane that the rule for two points (`pair`) and the two rules for four
points (`cardinalSegment`, `basisSegment`) follow. A move and a scaling are such maps. -/

/-- The segments through mapped points are the mapped segments, for a form that follows the map. -/
theorem pairs_map (f : Vec → Vec) (c : Curve)
    (hpair : ∀ a b : Vec, c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (points : List Vec) : c.pairs (points.map f) = (c.pairs points).map (Cubic.map f) := by
  match points with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    show c.pair (f a) (f b) ++ c.pairs ((b :: rest).map f) =
      (c.pair a b ++ c.pairs (b :: rest)).map (Cubic.map f)
    rw [hpair, pairs_map f c hpair (b :: rest), List.map_append]

/-- A straight segment follows a map that the forms between two points follow. -/
theorem line_map (f : Vec → Vec)
    (hpair : ∀ (c : Curve) (a b : Vec), c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (a b : Vec) : Cubic.line (f a) (f b) = (Cubic.line a b).map f :=
  Option.some.inj (congrArg List.head? (hpair .linear a b))

/-- A basis spline through mapped points is the mapped spline, for a map its rules follow. -/
theorem cubics_basis_map (f : Vec → Vec)
    (hline : ∀ a b : Vec, Cubic.line (f a) (f b) = (Cubic.line a b).map f)
    (hbasis : ∀ p0 p1 p2 p3 : Vec,
      basisSegment (f p0) (f p1) (f p2) (f p3) = (basisSegment p0 p1 p2 p3).map f)
    (points : List Vec) :
    basis.cubics (points.map f) = (basis.cubics points).map (Cubic.map f) := by
  match points with
  | [] => rfl
  | [_] => rfl
  | [a, b] => exact list_one (hline a b)
  | a :: b :: d :: rest =>
    obtain ⟨last, wn, h1, h2, h⟩ := cubics_basis_exists a b d rest
    have hW : windows basisSegment (doubled (f a :: f b :: f d :: rest.map f)) =
        (windows basisSegment (doubled (a :: b :: d :: rest))).map (Cubic.map f) := by
      show windows basisSegment (doubled ((a :: b :: d :: rest).map f)) = _
      rw [doubled_map, windows_map basisSegment f (Cubic.map f) hbasis]
    have h1' : (f a :: f b :: f d :: rest.map f).getLast? = some (f last) := by
      show ((a :: b :: d :: rest).map f).getLast? = some (f last)
      rw [List.getLast?_map, h1, Option.map_some]
    have h2' : (windows basisSegment (doubled (f a :: f b :: f d :: rest.map f))).getLast? =
        some (wn.map f) := by
      rw [hW, List.getLast?_map, h2, Option.map_some]
    show basis.cubics (f a :: f b :: f d :: rest.map f) = _
    rw [cubics_basis_of _ _ _ _ _ _ h1' h2', h, hW, List.map_append, List.map_cons, List.map_cons,
      List.map_nil, ← hline, ← hline, hbasis]
    rfl

/-- A curve through mapped points is the mapped curve, for a map that every rule follows. -/
theorem cubics_map (f : Vec → Vec)
    (hpair : ∀ (c : Curve) (a b : Vec), c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (hcard : ∀ (k : Rat) (p0 p1 p2 p3 : Vec),
      cardinalSegment k (f p0) (f p1) (f p2) (f p3) = (cardinalSegment k p0 p1 p2 p3).map f)
    (hbasis : ∀ p0 p1 p2 p3 : Vec,
      basisSegment (f p0) (f p1) (f p2) (f p3) = (basisSegment p0 p1 p2 p3).map f)
    (c : Curve) (points : List Vec) :
    c.cubics (points.map f) = (c.cubics points).map (Cubic.map f) := by
  cases c with
  | cardinal tension =>
    show windows (cardinalSegment (cardinalScale tension)) (reflected (points.map f)) = _
    rw [reflected_map]
    exact windows_map (cardinalSegment (cardinalScale tension)) f (Cubic.map f)
      (hcard (cardinalScale tension)) (reflected points)
  | basis => exact cubics_basis_map f (line_map f hpair) hbasis points
  | _ => exact pairs_map f _ (hpair _) points

/-- An open curve through mapped points is the mapped curve, for a map that every rule follows. -/
theorem cubicsOpen_map (f : Vec → Vec)
    (hpair : ∀ (c : Curve) (a b : Vec), c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (hcard : ∀ (k : Rat) (p0 p1 p2 p3 : Vec),
      cardinalSegment k (f p0) (f p1) (f p2) (f p3) = (cardinalSegment k p0 p1 p2 p3).map f)
    (hbasis : ∀ p0 p1 p2 p3 : Vec,
      basisSegment (f p0) (f p1) (f p2) (f p3) = (basisSegment p0 p1 p2 p3).map f)
    (c : Curve) (points : List Vec) :
    c.cubicsOpen (points.map f) = (c.cubicsOpen points).map (Cubic.map f) := by
  cases c with
  | cardinal tension =>
    exact windows_map (cardinalSegment (cardinalScale tension)) f (Cubic.map f)
      (hcard (cardinalScale tension)) points
  | basis => exact windows_map basisSegment f (Cubic.map f) hbasis points
  | _ =>
    show Curve.pairs _ (points.map f).tail.dropLast = _
    rw [← List.map_tail, ← List.map_dropLast]
    exact pairs_map f _ (hpair _) points.tail.dropLast

/-- A closed curve through mapped points is the mapped curve, for a map that every rule follows. -/
theorem cubicsClosed_map (f : Vec → Vec)
    (hpair : ∀ (c : Curve) (a b : Vec), c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (hcard : ∀ (k : Rat) (p0 p1 p2 p3 : Vec),
      cardinalSegment k (f p0) (f p1) (f p2) (f p3) = (cardinalSegment k p0 p1 p2 p3).map f)
    (hbasis : ∀ p0 p1 p2 p3 : Vec,
      basisSegment (f p0) (f p1) (f p2) (f p3) = (basisSegment p0 p1 p2 p3).map f)
    (c : Curve) (points : List Vec) :
    c.cubicsClosed (points.map f) = (c.cubicsClosed points).map (Cubic.map f) := by
  cases c with
  | cardinal tension =>
    show windows (cardinalSegment (cardinalScale tension)) (wrapped (points.map f)) = _
    rw [wrapped_map]
    exact windows_map (cardinalSegment (cardinalScale tension)) f (Cubic.map f)
      (hcard (cardinalScale tension)) (wrapped points)
  | basis =>
    show windows basisSegment (wrapped (points.map f)) = _
    rw [wrapped_map]
    exact windows_map basisSegment f (Cubic.map f) hbasis (wrapped points)
  | _ =>
    cases points with
    | nil => rfl
    | cons first rest =>
      have e : f first :: rest.map f ++ [f first] = (first :: rest ++ [first]).map f := by
        simp only [List.map_append, List.map_cons, List.map_nil]
      show Curve.pairs _ (f first :: rest.map f ++ [f first]) = _
      rw [e]
      exact pairs_map f _ (hpair _) (first :: rest ++ [first])

/-- The outline of an area between mapped lines is the mapped outline, for such a map. -/
theorem areaCubics_map (f : Vec → Vec)
    (hpair : ∀ (c : Curve) (a b : Vec), c.pair (f a) (f b) = (c.pair a b).map (Cubic.map f))
    (hcard : ∀ (k : Rat) (p0 p1 p2 p3 : Vec),
      cardinalSegment k (f p0) (f p1) (f p2) (f p3) = (cardinalSegment k p0 p1 p2 p3).map f)
    (hbasis : ∀ p0 p1 p2 p3 : Vec,
      basisSegment (f p0) (f p1) (f p2) (f p3) = (basisSegment p0 p1 p2 p3).map f)
    (c : Curve) (top base : List Vec) :
    c.areaCubics (top.map f) (base.map f) = (c.areaCubics top base).map (Cubic.map f) := by
  unfold areaCubics
  rw [cubics_map f hpair hcard hbasis, ← List.map_reverse, cubics_map f hpair hcard hbasis,
    List.getLast?_map, List.getLast?_map, List.map_append, List.map_append]
  cases top.getLast? with
  | none => rfl
  | some t =>
    cases base.getLast? with
    | none => rfl
    | some b =>
      exact congrArg
        (fun m => List.map (Cubic.map f) (c.cubics top) ++ m ++
          List.map (Cubic.map f) (c.flip.cubics base.reverse))
        (list_one (line_map f hpair t b))

/-! ## A curve through moved points is the curve, moved -/

/-- A segment of a cardinal spline through moved points is the segment, moved. -/
theorem cardinalSegment_move (k : Rat) (d p0 p1 p2 p3 : Vec) :
    cardinalSegment k (p0 + d) (p1 + d) (p2 + d) (p3 + d) =
      (cardinalSegment k p0 p1 p2 p3).move d := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [cardinalSegment, Cubic.move, Cubic.map, Vec.scale, Vec.add_def, Vec.sub_def] <;>
    grind

/-- A segment of a basis spline through moved points is the segment, moved. -/
theorem basisSegment_move (d p0 p1 p2 p3 : Vec) :
    basisSegment (p0 + d) (p1 + d) (p2 + d) (p3 + d) = (basisSegment p0 p1 p2 p3).move d := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [basisSegment, Cubic.move, Cubic.map, Vec.scale, Vec.add_def] <;> grind

/-- The segments that join two moved points are the segments, moved. -/
theorem pair_move (c : Curve) (d a b : Vec) :
    c.pair (a + d) (b + d) = (c.pair a b).map (Cubic.move d) := by
  cases c with
  | stepX | stepY =>
    apply list_three <;> apply Cubic.ext <;> apply Vec.ext <;>
      simp only [Cubic.move, Cubic.map, Cubic.line, Vec.lerp, Vec.add_def] <;> grind
  | stepBefore | stepAfter =>
    apply list_two <;> apply Cubic.ext <;> apply Vec.ext <;>
      simp only [Cubic.move, Cubic.map, Cubic.line, Vec.lerp, Vec.add_def] <;> grind
  | bumpX r | bumpY r =>
    apply list_one
    apply Cubic.ext <;> apply Vec.ext <;> simp only [Cubic.move, Cubic.map, Vec.add_def] <;> grind
  | _ => exact list_one (Cubic.move_line d a b).symm

/-- The segments through moved points, every two joined on their own, are the segments, moved. -/
theorem pairs_move (c : Curve) (d : Vec) (points : List Vec) :
    c.pairs (points.map fun p => p + d) = (c.pairs points).map (Cubic.move d) :=
  pairs_map (fun p => p + d) c (fun a b => pair_move c d a b) points

/-- A curve through moved points is the curve, moved. -/
theorem cubics_move (c : Curve) (d : Vec) (points : List Vec) :
    c.cubics (points.map fun p => p + d) = (c.cubics points).map (Cubic.move d) :=
  cubics_map (fun p => p + d) (fun c a b => pair_move c d a b)
    (fun k p0 p1 p2 p3 => cardinalSegment_move k d p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_move d p0 p1 p2 p3) c points

/-- An open curve through moved points is the curve, moved. -/
theorem cubicsOpen_move (c : Curve) (d : Vec) (points : List Vec) :
    c.cubicsOpen (points.map fun p => p + d) = (c.cubicsOpen points).map (Cubic.move d) :=
  cubicsOpen_map (fun p => p + d) (fun c a b => pair_move c d a b)
    (fun k p0 p1 p2 p3 => cardinalSegment_move k d p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_move d p0 p1 p2 p3) c points

/-- A closed curve through moved points is the curve, moved. -/
theorem cubicsClosed_move (c : Curve) (d : Vec) (points : List Vec) :
    c.cubicsClosed (points.map fun p => p + d) = (c.cubicsClosed points).map (Cubic.move d) :=
  cubicsClosed_map (fun p => p + d) (fun c a b => pair_move c d a b)
    (fun k p0 p1 p2 p3 => cardinalSegment_move k d p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_move d p0 p1 p2 p3) c points

/-- The outline of an area between moved lines is the outline, moved. -/
theorem areaCubics_move (c : Curve) (d : Vec) (top base : List Vec) :
    c.areaCubics (top.map fun p => p + d) (base.map fun p => p + d) =
      (c.areaCubics top base).map (Cubic.move d) :=
  areaCubics_map (fun p => p + d) (fun c a b => pair_move c d a b)
    (fun k p0 p1 p2 p3 => cardinalSegment_move k d p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_move d p0 p1 p2 p3) c top base

/-! ## A curve through scaled points is the curve, scaled -/

/-- A straight segment between scaled points is the segment, scaled. -/
theorem line_scale (k : Rat) (a b : Vec) :
    Cubic.line (Vec.scale k a) (Vec.scale k b) = (Cubic.line a b).scale k := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [Cubic.scale, Cubic.map, Cubic.line, Vec.lerp, Vec.scale] <;> grind

/-- A segment of a cardinal spline through scaled points is the segment, scaled. -/
theorem cardinalSegment_scale (j k : Rat) (p0 p1 p2 p3 : Vec) :
    cardinalSegment j (Vec.scale k p0) (Vec.scale k p1) (Vec.scale k p2) (Vec.scale k p3) =
      (cardinalSegment j p0 p1 p2 p3).scale k := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [cardinalSegment, Cubic.scale, Cubic.map, Vec.scale, Vec.add_def, Vec.sub_def] <;>
    grind

/-- A segment of a basis spline through scaled points is the segment, scaled. -/
theorem basisSegment_scale (k : Rat) (p0 p1 p2 p3 : Vec) :
    basisSegment (Vec.scale k p0) (Vec.scale k p1) (Vec.scale k p2) (Vec.scale k p3) =
      (basisSegment p0 p1 p2 p3).scale k := by
  apply Cubic.ext <;> apply Vec.ext <;>
    simp only [basisSegment, Cubic.scale, Cubic.map, Vec.scale, Vec.add_def] <;> grind

/-- The segments that join two scaled points are the segments, scaled. -/
theorem pair_scale (c : Curve) (k : Rat) (a b : Vec) :
    c.pair (Vec.scale k a) (Vec.scale k b) = (c.pair a b).map (Cubic.scale k) := by
  cases c with
  | stepX | stepY =>
    apply list_three <;> apply Cubic.ext <;> apply Vec.ext <;>
      simp only [Cubic.scale, Cubic.map, Cubic.line, Vec.lerp, Vec.scale] <;> grind
  | stepBefore | stepAfter =>
    apply list_two <;> apply Cubic.ext <;> apply Vec.ext <;>
      simp only [Cubic.scale, Cubic.map, Cubic.line, Vec.lerp, Vec.scale] <;> grind
  | bumpX r | bumpY r =>
    apply list_one
    apply Cubic.ext <;> apply Vec.ext <;> simp only [Cubic.scale, Cubic.map, Vec.scale] <;> grind
  | _ => exact list_one (line_scale k a b)

/-- A curve through scaled points is the curve, scaled. -/
theorem cubics_scale (c : Curve) (k : Rat) (points : List Vec) :
    c.cubics (points.map (Vec.scale k)) = (c.cubics points).map (Cubic.scale k) :=
  cubics_map (Vec.scale k) (fun c a b => pair_scale c k a b)
    (fun j p0 p1 p2 p3 => cardinalSegment_scale j k p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_scale k p0 p1 p2 p3) c points

/-- A closed curve through scaled points is the curve, scaled. -/
theorem cubicsClosed_scale (c : Curve) (k : Rat) (points : List Vec) :
    c.cubicsClosed (points.map (Vec.scale k)) = (c.cubicsClosed points).map (Cubic.scale k) :=
  cubicsClosed_map (Vec.scale k) (fun c a b => pair_scale c k a b)
    (fun j p0 p1 p2 p3 => cardinalSegment_scale j k p0 p1 p2 p3)
    (fun p0 p1 p2 p3 => basisSegment_scale k p0 p1 p2 p3) c points

end Curve

/-! ## The path as written -/

/-- A chain is written as one subpath. -/
theorem Pen.done_ofCubics? (cs : List Cubic) (places : Nat) (pen : Pen)
    (hc : Cubic.Chained cs = true) (h : Pen.ofCubics? cs places = some pen) : pen.done = [] := by
  cases cs with
  | nil => cases h
  | cons c rest =>
    have e : pen = (Pen.begin (c.p0.round places)).cubics (c :: rest) places :=
      (Option.some.inj h).symm
    rw [e]
    exact (Pen.done_cubics (c :: rest) (Pen.begin (c.p0.round places)) places hc (by
      intro c' hc'
      cases hc'
      rfl)).1

/-- The path of a line ends at its last point, as written. -/
theorem Shape.endPoint_line (c : Curve) (a b : Vec) (rest : List Vec) (places : Nat) :
    (Shape.line c (a :: b :: rest) places).endPoint =
      (a :: b :: rest).getLast?.map fun p => p.round places := by
  have h := Curve.cubics_last c a b rest
  show (Path.ofCubics (c.cubics (a :: b :: rest)) places).endPoint = _
  rw [Path.endPoint_ofCubics, ← h]
  cases (c.cubics (a :: b :: rest)).getLast? <;> rfl

/-- The curve from one point to another ends at the second, as written. -/
theorem Shape.endPoint_link (c : Curve) (a b : Vec) (places : Nat) :
    (Shape.link c a b places).endPoint = some (b.round places) :=
  Shape.endPoint_line c a b [] places

end Whatwg.Svg.Value
