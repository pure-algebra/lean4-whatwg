import Whatwg.Svg.Scene.Between

/-!
# Whatwg.Svg.Scene.Row

Owner: a row whose lengths change, and what it keeps at every moment (slice S14 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-81).

A rank of boxes with gaps between them is a row of lengths: a box, a gap, a box. So is a bar cut
into shares. When a length changes, every thing to its right moves. A step that mixes each
length by itself does not keep the row: the lengths are rounded one by one, and the sum of the
rounded lengths is not the row's length. A step that gives two things two timings loses a gap on
the way (`Whatwg/Svg/Scene/Between.lean`, the second control).

This module moves the edges and not the lengths. An edge is where one length ends and the next
begins. Each edge goes the straight way from its place in one row to its place in the other, at
one eased progress, and a length is what lies between two edges. Then the row is a row at every
moment.

- `Row.spans start ws`: the row of the lengths `ws` from `start`, each length with its left
  edge.
- `Row.Tiles`: each span starts where the one before it ends.
- `Row.between e s s' ws ws'`: the row at the eased progress `e` per mille between the row of
  `ws` from `s` and the row of `ws'` from `s'`.

What the laws say of a row drawn from `between`:

- `tiles_between`: it tiles at every eased progress, in range or not. No gap opens between two
  neighbours and no two lie over each other, with the rounding.
- `between_total`, `between_conserves`: its length is the mixed length. Two rows of one start
  and one length give that length at every eased progress, so a bar of shares stays whole while
  its shares change.
- `between_mem`: each length is the straight mix of its two lengths, or one unit more. With an
  eased progress in range it is between its two lengths. So a gap that is `g` in both rows is
  exactly `g` at every eased progress, in range or not, and a box is never thinner than at its
  thinner end. A row whose lengths do not change moves as one (`between_fixed`).
- `between_start`, `between_end`: at `0` it is the first row and at `1000` the second.

A host that changes a shape point by point keeps the same things. Two boxes drawn as shapes that
share an edge have the same coordinates there in both pictures, and equal numbers mix to equal
numbers on any host. This module says it of the kit's own reading.

What this module does not claim: anything of two rows of different counts, where `between`
stops at the shorter; a row along a curve; that the first edge stays where both rows have it
when the eased progress is out of range and the two starts differ.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Row

/-- The row of the lengths `ws` from `start`: each length with its left edge. -/
def spans : Int → List Int → List (Int × Int)
  | _, [] => []
  | s, w :: ws => (s, w) :: spans (s + w) ws

/-- **The row tiles**: each span starts where the one before it ends. -/
def Tiles : List (Int × Int) → Prop
  | a :: b :: rest => a.1 + a.2 = b.1 ∧ Tiles (b :: rest)
  | _ => True

/-- **The row between two rows**, at the eased progress `e` per mille: each edge the straight
way from its place in the row of `ws` from `s` to its place in the row of `ws'` from `s'`, and
each length what lies between two edges. -/
def between (e : Int) : Int → Int → List Int → List Int → List (Int × Int)
  | s, s', w :: ws, w' :: ws' =>
    (mix s s' e, mix (s + w) (s' + w') e - mix s s' e) :: between e (s + w) (s' + w') ws ws'
  | _, _, _, _ => []

/-- A row of lengths tiles. -/
theorem tiles_spans : ∀ (s : Int) (ws : List Int), Tiles (spans s ws)
  | _, [] => True.intro
  | _, [_] => True.intro
  | s, w :: v :: ws => ⟨rfl, tiles_spans (s + w) (v :: ws)⟩

/-- **The row between two rows tiles at every eased progress**, in range or not: no gap opens
between two neighbours, and no two lie over each other. -/
theorem tiles_between (e : Int) : ∀ (s s' : Int) (ws ws' : List Int),
    Tiles (between e s s' ws ws')
  | _, _, [], _ => True.intro
  | _, _, _ :: _, [] => True.intro
  | _, _, [_], [_] => True.intro
  | _, _, [_], _ :: _ :: _ => True.intro
  | _, _, _ :: _ :: _, [_] => True.intro
  | s, s', w :: v :: ws, w' :: v' :: ws' => by
    refine ⟨?_, tiles_between e (s + w) (s' + w') (v :: ws) (v' :: ws')⟩
    show mix s s' e + (mix (s + w) (s' + w') e - mix s s' e) = mix (s + w) (s' + w') e
    omega

/-- The row between two rows of one count has that count. -/
theorem length_between (e : Int) : ∀ (s s' : Int) (ws ws' : List Int),
    ws.length = ws'.length → (between e s s' ws ws').length = ws.length
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => nomatch h
  | _, _, _ :: _, [], h => nomatch h
  | s, s', w :: ws, w' :: ws', h => by
    have h' : ws.length = ws'.length := Nat.succ.inj h
    show (between e (s + w) (s' + w') ws ws').length + 1 = ws.length + 1
    rw [length_between e (s + w) (s' + w') ws ws' h']

/-- At the eased progress `0` the row is the first row. -/
theorem between_start : ∀ (s s' : Int) (ws ws' : List Int), ws.length = ws'.length →
    between 0 s s' ws ws' = spans s ws
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => nomatch h
  | _, _, _ :: _, [], h => nomatch h
  | s, s', w :: ws, w' :: ws', h => by
    have h' : ws.length = ws'.length := Nat.succ.inj h
    have a : mix s s' 0 = s := by
      show s' + (s - s') * (1000 - 0) / 1000 = s
      omega
    have b : mix (s + w) (s' + w') 0 = s + w := by
      show s' + w' + (s + w - (s' + w')) * (1000 - 0) / 1000 = s + w
      omega
    show (mix s s' 0, mix (s + w) (s' + w') 0 - mix s s' 0) :: between 0 (s + w) (s' + w') ws ws' =
      (s, w) :: spans (s + w) ws
    have c : s + w - s = w := by omega
    rw [a, b, between_start (s + w) (s' + w') ws ws' h', c]

/-- At the eased progress `1000` the row is the second row. -/
theorem between_end : ∀ (s s' : Int) (ws ws' : List Int), ws.length = ws'.length →
    between 1000 s s' ws ws' = spans s' ws'
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => nomatch h
  | _, _, _ :: _, [], h => nomatch h
  | s, s', w :: ws, w' :: ws', h => by
    have h' : ws.length = ws'.length := Nat.succ.inj h
    have a : mix s s' 1000 = s' := by
      show s' + (s - s') * (1000 - 1000) / 1000 = s'
      omega
    have b : mix (s + w) (s' + w') 1000 = s' + w' := by
      show s' + w' + (s + w - (s' + w')) * (1000 - 1000) / 1000 = s' + w'
      omega
    show (mix s s' 1000, mix (s + w) (s' + w') 1000 - mix s s' 1000) ::
        between 1000 (s + w) (s' + w') ws ws' = (s', w') :: spans (s' + w') ws'
    have c : s' + w' - s' = w' := by omega
    rw [a, b, between_end (s + w) (s' + w') ws ws' h', c]

/-- **The length of the row between two rows is the mixed length**: from the mixed start to the
mixed end, at every eased progress. -/
theorem between_total (e : Int) : ∀ (s s' : Int) (ws ws' : List Int), ws.length = ws'.length →
    ((between e s s' ws ws').map fun p => p.2).sum = mix (s + ws.sum) (s' + ws'.sum) e - mix s s' e
  | s, s', [], [], _ => by
    show (0 : Int) = mix (s + 0) (s' + 0) e - mix s s' e
    rw [Int.add_zero, Int.add_zero, Int.sub_self]
  | _, _, [], _ :: _, h => nomatch h
  | _, _, _ :: _, [], h => nomatch h
  | s, s', w :: ws, w' :: ws', h => by
    have h' : ws.length = ws'.length := Nat.succ.inj h
    have ih := between_total e (s + w) (s' + w') ws ws' h'
    show mix (s + w) (s' + w') e - mix s s' e +
        ((between e (s + w) (s' + w') ws ws').map fun p => p.2).sum =
      mix (s + (w :: ws).sum) (s' + (w' :: ws').sum) e - mix s s' e
    rw [ih, List.sum_cons, List.sum_cons, ← Int.add_assoc, ← Int.add_assoc]
    omega

/-- **A row keeps its length while its lengths change.** Two rows of one start and one length
give that length at every eased progress, in range or not. A bar of shares stays whole. -/
theorem between_conserves (e s : Int) (ws ws' : List Int) (h : ws.length = ws'.length)
    (hs : ws.sum = ws'.sum) :
    ((between e s s ws ws').map fun p => p.2).sum = ws.sum := by
  rw [between_total e s s ws ws' h, ← hs]
  show s + ws.sum + (s + ws.sum - (s + ws.sum)) * (1000 - e) / 1000 -
    (s + (s - s) * (1000 - e) / 1000) = ws.sum
  rw [Int.sub_self, Int.sub_self, Int.zero_mul, Int.zero_ediv]
  omega

/-- A length between two mixed edges is the straight mix of its two lengths, or one unit more:
the two roundings differ by one at most. -/
theorem part_near (s s' w w' e : Int) :
    mix w w' e ≤ mix (s + w) (s' + w') e - mix s s' e ∧
      mix (s + w) (s' + w') e - mix s s' e ≤ mix w w' e + 1 := by
  have split : (s + w - (s' + w')) * (1000 - e) = (s - s') * (1000 - e) + (w - w') * (1000 - e) := by
    rw [← Int.add_mul]
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · show w' + (w - w') * (1000 - e) / 1000 ≤
      s' + w' + (s + w - (s' + w')) * (1000 - e) / 1000 - (s' + (s - s') * (1000 - e) / 1000)
    rw [split]
    omega
  · show s' + w' + (s + w - (s' + w')) * (1000 - e) / 1000 - (s' + (s - s') * (1000 - e) / 1000) ≤
      w' + (w - w') * (1000 - e) / 1000 + 1
    rw [split]
    omega

/-- With an eased progress in range, a length between two mixed edges is between its two
lengths. -/
theorem part_mem (s s' w w' e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 1000) :
    min w w' ≤ mix (s + w) (s' + w') e - mix s s' e ∧
      mix (s + w) (s' + w') e - mix s s' e ≤ max w w' := by
  have lo := mix_gap s s' (s + w) (s' + w') (min w w') e h0 h1 (by omega) (by omega)
  have hi := mix_gap (s + w) (s' + w') (s + max w w') (s' + max w w') 0 e h0 h1 (by omega) (by omega)
  rw [mix_add_right s s' (max w w') e] at hi
  refine ⟨?_, ?_⟩
  · omega
  · omega

/-- A length that both rows have is that length between two mixed edges, at every eased
progress, in range or not: its two edges are a fixed step apart. -/
theorem part_fixed (s s' g e : Int) : mix (s + g) (s' + g) e - mix s s' e = g := by
  rw [mix_add_right]
  omega

/-- **Each length of the row between two rows comes from its two lengths.** It is their straight
mix or one unit more, at every eased progress, and it is the length itself where the two are
one. With an eased progress in range it is between the two: a box is never thinner than at its
thinner end, nor wider than at its wider. -/
theorem between_mem (e : Int) : ∀ (s s' : Int) (ws ws' : List Int) (p : Int × Int),
    p ∈ between e s s' ws ws' → ∃ w w', (w, w') ∈ ws.zip ws' ∧
      mix w w' e ≤ p.2 ∧ p.2 ≤ mix w w' e + 1 ∧ (w = w' → p.2 = w) ∧
      (0 ≤ e → e ≤ 1000 → min w w' ≤ p.2 ∧ p.2 ≤ max w w')
  | _, _, [], _, _, h => nomatch h
  | _, _, _ :: _, [], _, h => nomatch h
  | s, s', w :: ws, w' :: ws', p, h => by
    rcases List.mem_cons.mp h with hp | hp
    · subst hp
      refine ⟨w, w', List.mem_cons_self, (part_near s s' w w' e).1, (part_near s s' w w' e).2,
        ?_, fun h0 h1 => part_mem s s' w w' e h0 h1⟩
      intro hw
      subst hw
      exact part_fixed s s' w e
    · obtain ⟨v, v', hv, a, b, c, d⟩ := between_mem e (s + w) (s' + w') ws ws' p hp
      exact ⟨v, v', List.mem_cons_of_mem _ hv, a, b, c, d⟩

/-- **A row whose lengths are the same in both rows moves as one**, at every eased progress, in
range or not: each of its lengths is a length that both rows have. With `between_mem` at one
place, a gap that both rows have is exactly that gap at every moment, whatever the boxes on its
two sides do. -/
theorem between_fixed (e s s' : Int) (ws : List Int) (p : Int × Int)
    (hp : p ∈ between e s s' ws ws) : p.2 ∈ ws := by
  obtain ⟨w, w', hm, _, _, c, _⟩ := between_mem e s s' ws ws p hp
  have hz : ∀ (l : List Int) (q : Int × Int), q ∈ l.zip l → q.1 = q.2 ∧ q.1 ∈ l := by
    intro l
    induction l with
    | nil => exact fun q hq => nomatch hq
    | cons a l ih =>
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst hq
        exact ⟨rfl, List.mem_cons_self⟩
      · exact ⟨(ih q hq).1, List.mem_cons_of_mem _ (ih q hq).2⟩
  have h := hz ws (w, w') hm
  have e1 : w = w' := h.1
  rw [c e1]
  exact h.2

end Row

/-! ## Controls

A rank of two boxes and the gap between them, from the left edge `24`: the boxes `120` and `160`
wide before, `200` and `80` after, the gap `16` in both. At the eased progress `337` the row
tiles, the gap is `16`, and the row is as long as the mixed length. Mixing each length by itself
at that progress gives lengths whose sum is one unit short. -/

#guard Row.between 337 24 24 [120, 16, 160] [200, 16, 80] = [(24, 146), (170, 16), (186, 134)]
#guard ((Row.between 337 24 24 [120, 16, 160] [200, 16, 80]).map fun p => p.2).sum = 296
#guard [mix 120 200 337, mix 16 16 337, mix 160 80 337].sum = 295
#guard Row.between 0 24 24 [120, 16, 160] [200, 16, 80] = Row.spans 24 [120, 16, 160]
#guard Row.between 1000 24 24 [120, 16, 160] [200, 16, 80] = Row.spans 24 [200, 16, 80]
-- An eased progress past the end: the row still tiles, has its length, and has its gap.
#guard (Row.between 1099 24 24 [120, 16, 160] [200, 16, 80]).map (fun p => p.2) = [207, 16, 73]
#guard ((Row.between 1099 24 24 [120, 16, 160] [200, 16, 80]).map fun p => p.2).sum = 296

end Whatwg.Svg.Scene
