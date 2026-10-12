import Whatwg.Svg.Geometry.Cubic

/-!
# Whatwg.Svg.Geometry.Cubic.Laws

Owner: the laws of a cubic Bézier segment (slice S11 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-51). Each is stated against `Cubic.pointAt`, the point of the segment at a parameter, and
holds for every rational parameter: none asks that it lies between `0` and `1`.

- **Ends.** `pointAt_zero`, `pointAt_one`.
- **The part between two parameters** (`between_pointAt`): the point at `s` of the part from
  `a` to `b` is the point of the whole at `a + s (b - a)`. The rest of the subdivision laws are
  cases of it: `upTo`, `after`, the junction of a split, the part of a part
  (`between_between`), the whole (`between_zero_one`) and the segment backwards
  (`between_one_zero`).
- **Straight and quadratic** (`line_pointAt`, `ofQuad_pointAt`): a straight segment as a cubic
  is the step between its ends, and a quadratic as a cubic is the quadratic.
- **Maps** (`map_pointAt`): a map of the plane that keeps steps takes the segment to the
  segment of the mapped points. A move and a scaling are such maps.
- **Velocity** (`upTo_velocity_one`, `after_velocity_zero`): the part up to `t` arrives with
  `t` times the velocity of the whole at `t`, and the part after it leaves with `1 - t` times
  it, so a split keeps the direction across its junction.
- **Chains.** A chain stays one under a map of the plane, so moved and scaled; the two parts
  of a split are a chain; and two chains that meet are one.

Every proof unfolds the definitions to an equation of two polynomials in each coordinate and
hands it to `grind`.
-/

namespace Whatwg.Svg.Value

namespace Cubic

theorem ext {c d : Cubic} (h0 : c.p0 = d.p0) (h1 : c.p1 = d.p1) (h2 : c.p2 = d.p2)
    (h3 : c.p3 = d.p3) : c = d := by
  cases c
  cases d
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

/-! ## The blossom -/

/-- The blossom reads its first two parameters in either order. -/
theorem blossom_comm (c : Cubic) (r s t : Rat) : c.blossom r s t = c.blossom s r t := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

/-- The blossom reads its last two parameters in either order. -/
theorem blossom_comm_right (c : Cubic) (r s t : Rat) : c.blossom r s t = c.blossom r t s := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

/-- The four points are the blossoms at the four corners. -/
theorem blossom_zero (c : Cubic) : c.blossom 0 0 0 = c.p0 := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

theorem blossom_zero_zero_one (c : Cubic) : c.blossom 0 0 1 = c.p1 := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

theorem blossom_zero_one_one (c : Cubic) : c.blossom 0 1 1 = c.p2 := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

theorem blossom_one (c : Cubic) : c.blossom 1 1 1 = c.p3 := by
  apply Vec.ext <;> simp only [blossom, Vec.lerp] <;> grind

/-! ## Ends -/

theorem pointAt_zero (c : Cubic) : c.pointAt 0 = c.p0 := blossom_zero c

theorem pointAt_one (c : Cubic) : c.pointAt 1 = c.p3 := blossom_one c

/-! ## The part between two parameters -/

/-- **Subdivision.** The point at `s` of the part from `a` to `b` is the point of the whole at
`a + s (b - a)`. -/
theorem between_pointAt (c : Cubic) (a b s : Rat) :
    (c.between a b).pointAt s = c.pointAt (a + s * (b - a)) := by
  apply Vec.ext <;> simp only [pointAt, between, blossom, Vec.lerp] <;> grind

/-- The part of a part is a part of the whole. -/
theorem between_between (c : Cubic) (a b s t : Rat) :
    (c.between a b).between s t = c.between (a + s * (b - a)) (a + t * (b - a)) := by
  apply ext <;> apply Vec.ext <;> simp only [between, blossom, Vec.lerp] <;> grind

/-- The part from `0` to `1` is the whole. -/
theorem between_zero_one (c : Cubic) : c.between 0 1 = c := by
  apply ext
  · exact blossom_zero c
  · exact blossom_zero_zero_one c
  · exact blossom_zero_one_one c
  · exact blossom_one c

/-- The part from `1` to `0` is the segment backwards. -/
theorem between_one_zero (c : Cubic) : c.between 1 0 = c.reverse := by
  apply ext <;> apply Vec.ext <;> simp only [between, blossom, reverse, Vec.lerp] <;> grind

/-- The part from `b` to `a` is the part from `a` to `b`, backwards. -/
theorem between_swap (c : Cubic) (a b : Rat) : c.between b a = (c.between a b).reverse := by
  apply ext <;> apply Vec.ext <;> simp only [between, blossom, reverse, Vec.lerp] <;> grind

theorem upTo_eq_between (c : Cubic) (t : Rat) : c.upTo t = c.between 0 t := by
  apply ext <;> apply Vec.ext <;> simp only [upTo, between, pointAt, blossom, Vec.lerp] <;> grind

theorem after_eq_between (c : Cubic) (t : Rat) : c.after t = c.between t 1 := by
  apply ext <;> apply Vec.ext <;> simp only [after, between, pointAt, blossom, Vec.lerp] <;> grind

/-- The point at `s` of the part up to `t` is the point of the whole at `s * t`. -/
theorem upTo_pointAt (c : Cubic) (t s : Rat) : (c.upTo t).pointAt s = c.pointAt (s * t) := by
  rw [upTo_eq_between, between_pointAt]
  congr 1
  grind

/-- The point at `s` of the part after `t` is the point of the whole at `t + s (1 - t)`. -/
theorem after_pointAt (c : Cubic) (t s : Rat) :
    (c.after t).pointAt s = c.pointAt (t + s * (1 - t)) := by
  rw [after_eq_between, between_pointAt]

/-- The two parts of a split meet at the point of the whole. -/
theorem upTo_p3 (c : Cubic) (t : Rat) : (c.upTo t).p3 = c.pointAt t := rfl

theorem after_p0 (c : Cubic) (t : Rat) : (c.after t).p0 = c.pointAt t := rfl

theorem upTo_p0 (c : Cubic) (t : Rat) : (c.upTo t).p0 = c.p0 := rfl

theorem after_p3 (c : Cubic) (t : Rat) : (c.after t).p3 = c.p3 := rfl

/-- The part up to the end is the whole. -/
theorem upTo_one (c : Cubic) : c.upTo 1 = c := by rw [upTo_eq_between, between_zero_one]

/-- The part after the start is the whole. -/
theorem after_zero (c : Cubic) : c.after 0 = c := by rw [after_eq_between, between_zero_one]

/-- A part up to `t` of a part up to `u` is the part up to `t * u`. -/
theorem upTo_upTo (c : Cubic) (u t : Rat) : (c.upTo u).upTo t = c.upTo (t * u) := by
  rw [upTo_eq_between, upTo_eq_between, upTo_eq_between, between_between]
  congr 1 <;> grind

/-! ## Backwards -/

theorem reverse_reverse (c : Cubic) : c.reverse.reverse = c := rfl

/-- The segment backwards at `t` is the segment at `1 - t`. -/
theorem reverse_pointAt (c : Cubic) (t : Rat) : c.reverse.pointAt t = c.pointAt (1 - t) := by
  apply Vec.ext <;> simp only [pointAt, blossom, reverse, Vec.lerp] <;> grind

/-! ## Straight and quadratic segments -/

/-- A straight segment as a cubic is the step between its ends. -/
theorem line_pointAt (a b : Vec) (t : Rat) : (line a b).pointAt t = a.lerp b t := by
  apply Vec.ext <;> simp only [pointAt, blossom, line, Vec.lerp] <;> grind

/-- A quadratic Bézier segment as a cubic is the quadratic: two rounds of steps. -/
theorem ofQuad_pointAt (a q b : Vec) (t : Rat) :
    (ofQuad a q b).pointAt t = (a.lerp q t).lerp (q.lerp b t) t := by
  apply Vec.ext <;> simp only [pointAt, blossom, ofQuad, Vec.lerp] <;> grind

theorem line_reverse (a b : Vec) : (line a b).reverse = line b a := by
  apply ext <;> apply Vec.ext <;> simp only [line, reverse, Vec.lerp] <;> grind

/-- A part of a straight segment is the straight segment between its two points. -/
theorem line_between (a b : Vec) (s t : Rat) :
    (line a b).between s t = line (a.lerp b s) (a.lerp b t) := by
  apply ext <;> apply Vec.ext <;> simp only [between, blossom, line, Vec.lerp] <;> grind

/-! ## Maps of the plane -/

/-- **A map that keeps steps takes the segment to the segment of the mapped points.** Every
affine map keeps steps. -/
theorem map_blossom (f : Vec → Vec) (hf : ∀ (a b : Vec) (t : Rat), f (a.lerp b t) = (f a).lerp (f b) t)
    (c : Cubic) (r s t : Rat) : (c.map f).blossom r s t = f (c.blossom r s t) := by
  simp only [blossom, map, hf]

theorem map_pointAt (f : Vec → Vec) (hf : ∀ (a b : Vec) (t : Rat), f (a.lerp b t) = (f a).lerp (f b) t)
    (c : Cubic) (t : Rat) : (c.map f).pointAt t = f (c.pointAt t) :=
  map_blossom f hf c t t t

theorem map_between (f : Vec → Vec) (hf : ∀ (a b : Vec) (t : Rat), f (a.lerp b t) = (f a).lerp (f b) t)
    (c : Cubic) (a b : Rat) : (c.map f).between a b = (c.between a b).map f := by
  apply ext <;> simp only [between, map_blossom f hf] <;> rfl

theorem map_map (f g : Vec → Vec) (c : Cubic) : (c.map f).map g = c.map (g ∘ f) := rfl

theorem map_reverse (f : Vec → Vec) (c : Cubic) : (c.map f).reverse = c.reverse.map f := rfl

/-- A move keeps steps. -/
theorem move_keeps (d a b : Vec) (t : Rat) : a.lerp b t + d = (a + d).lerp (b + d) t :=
  (Vec.lerp_add a b d t).symm

/-- A scaling keeps steps. -/
theorem scale_keeps (k : Rat) (a b : Vec) (t : Rat) :
    Vec.scale k (a.lerp b t) = (Vec.scale k a).lerp (Vec.scale k b) t :=
  (Vec.lerp_scale k a b t).symm

/-- A moved segment at `t` is the point, moved. -/
theorem move_pointAt (d : Vec) (c : Cubic) (t : Rat) : (c.move d).pointAt t = c.pointAt t + d :=
  map_pointAt (· + d) (move_keeps d) c t

/-- A scaled segment at `t` is the point, scaled. -/
theorem scale_pointAt (k : Rat) (c : Cubic) (t : Rat) :
    (c.scale k).pointAt t = Vec.scale k (c.pointAt t) :=
  map_pointAt (Vec.scale k) (scale_keeps k) c t

/-- A part of a moved segment is the part, moved. -/
theorem move_between (d : Vec) (c : Cubic) (a b : Rat) :
    (c.move d).between a b = (c.between a b).move d :=
  map_between (· + d) (move_keeps d) c a b

theorem move_upTo (d : Vec) (c : Cubic) (t : Rat) : (c.move d).upTo t = (c.upTo t).move d := by
  rw [upTo_eq_between, upTo_eq_between, move_between]

theorem move_after (d : Vec) (c : Cubic) (t : Rat) : (c.move d).after t = (c.after t).move d := by
  rw [after_eq_between, after_eq_between, move_between]

/-- A segment moved twice is the segment moved by the sum. -/
theorem move_move (d e : Vec) (c : Cubic) : (c.move d).move e = c.move (d + e) := by
  apply ext <;> exact Vec.add_assoc _ _ _

/-- A segment moved by nothing is the segment. -/
theorem move_zero (c : Cubic) : c.move Vec.zero = c := by
  apply ext <;> exact Vec.add_zero _

/-- A moved segment, scaled, is the scaled segment moved by `k` times as far. -/
theorem scale_move (k : Rat) (d : Vec) (c : Cubic) :
    (c.move d).scale k = (c.scale k).move (Vec.scale k d) := by
  apply ext <;> apply Vec.ext <;> simp only [move, scale, map, Vec.scale, Vec.add_def] <;> grind

theorem scale_scale (j k : Rat) (c : Cubic) : (c.scale j).scale k = c.scale (k * j) := by
  apply ext <;> apply Vec.ext <;> simp only [scale, map, Vec.scale] <;> grind

theorem scale_one (c : Cubic) : c.scale 1 = c := by
  apply ext <;> apply Vec.ext <;> simp only [scale, map, Vec.scale] <;> grind

/-- A moved segment has the measure of the segment. -/
theorem move_taxi (d : Vec) (c : Cubic) : (c.move d).taxi = c.taxi := by
  simp only [taxi, move, map, Vec.taxi_move]

theorem move_line (d a b : Vec) : (line a b).move d = line (a + d) (b + d) := by
  apply ext <;> apply Vec.ext <;> simp only [move, map, line, Vec.lerp, Vec.add_def] <;> grind

/-! ## Velocity -/

/-- A segment leaves its start towards its first control point. -/
theorem velocity_zero (c : Cubic) : c.velocity 0 = Vec.scale 3 (c.p1 - c.p0) := by
  apply Vec.ext <;> simp only [velocity, Vec.scale, Vec.lerp, Vec.sub_def] <;> grind

/-- A segment arrives at its end from its second control point. -/
theorem velocity_one (c : Cubic) : c.velocity 1 = Vec.scale 3 (c.p3 - c.p2) := by
  apply Vec.ext <;> simp only [velocity, Vec.scale, Vec.lerp, Vec.sub_def] <;> grind

/-- A moved segment has the velocity of the segment. -/
theorem move_velocity (d : Vec) (c : Cubic) (t : Rat) : (c.move d).velocity t = c.velocity t := by
  apply Vec.ext <;> simp only [velocity, move, map, Vec.scale, Vec.lerp, Vec.sub_def, Vec.add_def] <;>
    grind

/-- A moved segment has the direction of the segment. -/
theorem move_direction (d : Vec) (c : Cubic) (t : Rat) :
    (c.move d).direction t = c.direction t := by
  have hchord : (c.move d).p3 - (c.move d).p0 = c.p3 - c.p0 := by
    apply Vec.ext <;> simp only [move, map, Vec.sub_def, Vec.add_def] <;> grind
  have hstart : (c.move d).p2 - (c.move d).p0 = c.p2 - c.p0 := by
    apply Vec.ext <;> simp only [move, map, Vec.sub_def, Vec.add_def] <;> grind
  have hend : (c.move d).p3 - (c.move d).p1 = c.p3 - c.p1 := by
    apply Vec.ext <;> simp only [move, map, Vec.sub_def, Vec.add_def] <;> grind
  simp only [direction, move_velocity, hchord, hstart, hend]

/-- **The velocity of a part.** The part from `a` to `b` has, at `s`, `b - a` times the
velocity of the whole at `a + s (b - a)`: the chain rule for a change of parameter. -/
theorem between_velocity (c : Cubic) (a b s : Rat) :
    (c.between a b).velocity s = Vec.scale (b - a) (c.velocity (a + s * (b - a))) := by
  apply Vec.ext <;> simp only [velocity, between, blossom, Vec.scale, Vec.lerp, Vec.sub_def] <;> grind

/-- The part up to `t` arrives with `t` times the velocity of the whole at `t`. -/
theorem upTo_velocity_one (c : Cubic) (t : Rat) :
    (c.upTo t).velocity 1 = Vec.scale t (c.velocity t) := by
  rw [upTo_eq_between, between_velocity]
  congr 1 <;> grind

/-- The part after `t` leaves with `1 - t` times the velocity of the whole at `t`. -/
theorem after_velocity_zero (c : Cubic) (t : Rat) :
    (c.after t).velocity 0 = Vec.scale (1 - t) (c.velocity t) := by
  rw [after_eq_between, between_velocity]
  congr 1 <;> grind

/-- The segment backwards has the opposite velocity. -/
theorem reverse_velocity (c : Cubic) (t : Rat) :
    c.reverse.velocity t = -(c.velocity (1 - t)) := by
  apply Vec.ext <;> simp only [velocity, reverse, Vec.scale, Vec.lerp, Vec.sub_def, Vec.neg_def] <;>
    grind

/-! ## Chains -/

theorem chained_nil : Chained [] = true := rfl

theorem chained_singleton (c : Cubic) : Chained [c] = true := rfl

theorem chained_cons (a b : Cubic) (rest : List Cubic) :
    Chained (a :: b :: rest) = (decide (a.p3 = b.p0) && Chained (b :: rest)) := rfl

/-- A chain under a map of the plane is a chain. -/
theorem chained_map (f : Vec → Vec) : ∀ (cs : List Cubic),
    Chained cs = true → Chained (cs.map (map f)) = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [chained_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.map_cons, List.map_cons, chained_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨congrArg f h.1, chained_map f (b :: rest) h.2⟩

/-- A moved chain is a chain. -/
theorem chained_move (d : Vec) (cs : List Cubic) (h : Chained cs = true) :
    Chained (cs.map (move d)) = true :=
  chained_map (· + d) cs h

/-- The two parts of a split are a chain. -/
theorem chained_split (c : Cubic) (t : Rat) : Chained [c.upTo t, c.after t] = true := by
  rw [chained_cons, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨rfl, rfl⟩

/-- Two chains, the second starting where the first ends, are one chain. -/
theorem chained_append : ∀ (cs ds : List Cubic), Chained cs = true → Chained ds = true →
    (∀ a b, cs.getLast? = some a → ds.head? = some b → a.p3 = b.p0) → Chained (cs ++ ds) = true
  | [], _, _, hd, _ => hd
  | [a], [], _, _, _ => rfl
  | [a], b :: ds, _, hd, hj => by
    show Chained (a :: b :: ds) = true
    rw [chained_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hj a b rfl rfl, hd⟩
  | a :: b :: cs, ds, hc, hd, hj => by
    rw [chained_cons, Bool.and_eq_true, decide_eq_true_eq] at hc
    show Chained (a :: b :: (cs ++ ds)) = true
    rw [chained_cons, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hc.1, chained_append (b :: cs) ds hc.2 hd ?_⟩
    intro x y hx hy
    exact hj x y (by rw [List.getLast?_cons_cons]; exact hx) hy

end Cubic

end Whatwg.Svg.Value
