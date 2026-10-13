import Whatwg.Svg.Scene.Network

/-!
# Whatwg.Svg.Scene.Network.Laws

Owner: what a picture of a flow network keeps (slice S22 of `docs/SVG-PACKAGE-PLAN.md`; ask
W18 of `docs/research/2026-10-12-whatwg-requests.md`).

The network of `Whatwg/Svg/Scene/Network.lean` is drawn so that a width is a quantity. These
laws say that the picture cannot say a quantity that the data does not have.

- **Conservation, as the reader sees it** (`conserved_heights`, `conserved_fills`): at a node
  where what enters is what leaves, the bands that enter and the bands that leave have one
  height together. On a scale that draws nothing with no length they fill the side of the
  node, both sides.
- **The bands at a side tile** (`outs_stacked`, `ins_stacked`): each starts where the one
  before it ends, so there is no gap and no overlap, on any scale. Their widths sum to the
  length of what leaves, or of what enters (`outs_total`, `ins_total`).
- **The bands stay inside the node** (`outs_inside`, `ins_inside`, `channel_inside`), on a
  scale that rises.
- **A band is as wide as what its link carries** (`channel_spec`, `channel_times`): from the
  length of the sum before it to the length of the sum with it. On a scale of whole units its
  width is the quantity times the unit, at both ends. On a scale that rounds, the two ends of
  one link may differ by the rounding.
- **The bands at a side are the pile of the values there** (`outs_eq`, `ins_eq`): the law that
  the others come from.
- **The nodes of a column do not overlap** (`top_apart`): each stands below the one before it
  in its column by that node's length and the gap. With `layout_clear`, no two nodes share
  room; with `layout_fits`, each is inside the room.
- **A link goes from a column to a later one** (`depth_lt`, `justify_lt`, `box_forward`): along
  an order that serves the links, the column of a link's target is after the column of its
  source, and the source's box ends, across, before the target's begins.
- **Which nodes a link cannot meet** (`channel_misses`, `channel_misses_neighbours`): the room
  of a link shares nothing with a node whose column is not strictly between the link's two. So
  a link between two neighbouring columns meets no node.
- `value_of_conserved`, `enters_le_value`, `leaves_le_value`, `channels_links`: the value of a
  node, and that the placed links are the links, in their order.

What a caller must supply: nodes with no node twice, for the laws of room; an order that
serves the links (`Layers.serves`), for the columns; a scale that rises, for the bands to stay
inside. `rising_times` and `rising_ratio` of the definitions module give the last for the two
scales there.

The laws of the scale that fits a room are in `Whatwg/Svg/Scene/Network/Fit.lean`.

What this module does not claim: anything of a link whose two columns are not in order; that
the picture is the one d3 draws after its relaxation.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Network

variable {ε ν : Type}

/-! ## Lists of numbers -/

/-- Each number of a list is no more than the greatest. -/
theorem le_greatest : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ greatest l
  | [], _, h => nomatch h
  | y :: l, x, h => by
    show x ≤ max y (greatest l)
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_max_left _ _
    | inr h' => exact Nat.le_trans (le_greatest h') (Nat.le_max_right _ _)

/-- The bands of piled values, as boxes, are as high together as the length of the sum past
the length of what was before. No premise is on the scale. -/
theorem pile_heights (scale : Nat → Nat) (x top : Nat) : ∀ (xs : List Nat) (p : Nat),
    (((pile scale p xs).map fun b => band x top b.1 b.2).map IBox.height).sum =
      (scale (p + xs.sum) : Int) - (scale p : Int)
  | [], p => by
    show (0 : Int) = (scale (p + 0) : Int) - (scale p : Int)
    rw [Nat.add_zero, Int.sub_self]
  | y :: xs, p => by
    have ih := pile_heights scale x top xs (p + y)
    rw [Nat.add_assoc] at ih
    show (((top + scale (p + y) : Nat) : Int) - ((top + scale p : Nat) : Int)) +
        (((pile scale (p + y) xs).map fun b => band x top b.1 b.2).map IBox.height).sum =
      (scale (p + (y :: xs).sum) : Int) - (scale p : Int)
    rw [ih, List.sum_cons]
    omega

/-- Bands that tile, as boxes, lie one below the other. -/
theorem stacked_of_tiles (x top : Nat) : ∀ l : List (Nat × Nat), Tiles l →
    Stacked (l.map fun b => band x top b.1 b.2)
  | [], _ => True.intro
  | [_], _ => True.intro
  | _ :: b :: rest, h =>
    ⟨congrArg (fun k : Nat => ((top + k : Nat) : Int)) h.1, stacked_of_tiles x top (b :: rest) h.2⟩

section

variable [DecidableEq ν]

/-! ## The value of a node -/

theorem enters_le_value (n : Network ε ν) (v : ν) : n.enters v ≤ n.value v := Nat.le_max_left _ _

theorem leaves_le_value (n : Network ε ν) (v : ν) : n.leaves v ≤ n.value v := Nat.le_max_right _ _

/-- At a node that conserves, the value is what enters, and what leaves. -/
theorem value_of_conserved {n : Network ε ν} {v : ν} (h : n.Conserved v) :
    n.value v = n.enters v ∧ n.value v = n.leaves v := by
  have h' : n.enters v = n.leaves v := h
  show max (n.enters v) (n.leaves v) = n.enters v ∧ max (n.enters v) (n.leaves v) = n.leaves v
  rw [h']
  exact ⟨Nat.max_self _, Nat.max_self _⟩

/-! ## The columns -/

/-- **A link goes from a column to a later one**: along an order that serves the links, the
depth of a link's target is more than the depth of its source. -/
theorem depth_lt {n : Network ε ν} {order : List ν} (h : Layers.Serves n.steps n.links order)
    {e : ε} (he : e ∈ n.links) : n.depth order (n.src e) < n.depth order (n.dst e) := by
  have h1 : Layers.heights n.steps n.links 0 order (n.src e) + 1 ≤
      Layers.heights n.steps n.links 0 order (n.dst e) := Layers.heights_meets h 0 he
  have h2 := Layers.heights_start n.steps n.links 0 order (n.src e)
  show (Layers.read 0 (Layers.table n.steps n.links 0 order) (n.src e)).toNat <
    (Layers.read 0 (Layers.table n.steps n.links 0 order) (n.dst e)).toNat
  rw [Layers.read_table, Layers.read_table]
  omega

/-- **With the ends in the last column, a link still goes to a later column**, where the
target of the link is among the nodes. -/
theorem justify_lt {n : Network ε ν} {order : List ν} (h : Layers.Serves n.steps n.links order)
    {e : ε} (he : e ∈ n.links) (hd : n.dst e ∈ n.nodes) :
    n.justify order (n.src e) < n.justify order (n.dst e) := by
  have hlt := depth_lt h he
  have hle : n.depth order (n.dst e) ≤ greatest (n.nodes.map (n.depth order)) :=
    le_greatest (List.mem_map_of_mem hd)
  have hany : (n.links.any fun x => decide (n.src x = n.src e)) = true :=
    List.any_eq_true.mpr ⟨e, he, decide_eq_true rfl⟩
  show (if (n.links.any fun x => decide (n.src x = n.src e)) = true then n.depth order (n.src e)
      else greatest (n.nodes.map (n.depth order))) <
    (if (n.links.any fun x => decide (n.src x = n.dst e)) = true then n.depth order (n.dst e)
      else greatest (n.nodes.map (n.depth order)))
  rw [if_pos hany]
  by_cases hb : (n.links.any fun x => decide (n.src x = n.dst e)) = true
  · rw [if_pos hb]
    exact hlt
  · rw [if_neg hb]
    omega

/-! ## Where the nodes stand -/

theorem topIn_cons_self (len : ν → Nat) (gap : Nat) (col : ν → Nat) (v : ν) (us : List ν) :
    topIn len gap col (v :: us) v = 0 := if_pos rfl

theorem topIn_cons_ne (len : ν → Nat) (gap : Nat) (col : ν → Nat) {u v : ν} (h : u ≠ v)
    (us : List ν) : topIn len gap col (u :: us) v =
      (if col u = col v then len u + gap else 0) + topIn len gap col us v := if_neg h

/-- In a list with no node twice, a node stands below each node of its column that is before
it, by that node's length and the gap. -/
theorem topIn_apart (len : ν → Nat) (gap : Nat) (col : ν → Nat) : ∀ l : List ν, l.Nodup →
    l.Pairwise fun u v => col u = col v →
      topIn len gap col l u + len u + gap ≤ topIn len gap col l v
  | [], _ => List.Pairwise.nil
  | x :: xs, nd => by
    have nd' : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp nd
    refine List.Pairwise.cons (fun v hv hc => ?_) ?_
    · have hne : x ≠ v := fun e => nd'.1 (e ▸ hv)
      rw [topIn_cons_self, topIn_cons_ne len gap col hne, if_pos hc]
      omega
    · refine List.Pairwise.imp_of_mem (fun {a b} ha hb h hc => ?_)
        (topIn_apart len gap col xs nd'.2)
      have hxa : x ≠ a := fun e => nd'.1 (e ▸ ha)
      have hxb : x ≠ b := fun e => nd'.1 (e ▸ hb)
      have h' := h hc
      rw [topIn_cons_ne len gap col hxa, topIn_cons_ne len gap col hxb, hc]
      omega

/-- **The nodes of a column do not overlap**: with no node twice, each stands below the one
before it in its column, by that node's length and the gap. -/
theorem top_apart (n : Network ε ν) (m : Measure) (col : ν → Nat) (nd : n.nodes.Nodup) :
    n.nodes.Pairwise fun u v => col u = col v →
      n.top m col u + n.length m u + m.gap ≤ n.top m col v :=
  topIn_apart (n.length m) m.gap col n.nodes nd

/-- **A link goes from left to right**: where the column of one node is before the column of
another, and a node is no thicker than the stride, the first ends, across, before the second
begins. -/
theorem box_forward (n : Network ε ν) {m : Measure} {col : ν → Nat} (ht : m.thick ≤ m.stride)
    {u v : ν} (hc : col u < col v) : (n.box m col u).x1 ≤ (n.box m col v).x0 := by
  have h1 : (col u + 1) * m.stride ≤ col v * m.stride := Nat.mul_le_mul_right m.stride hc
  rw [Nat.succ_mul] at h1
  show ((col u * m.stride + m.thick : Nat) : Int) ≤ ((col v * m.stride : Nat) : Int)
  exact Int.ofNat_le.mpr (by omega)

/-- **No two nodes share room**, where no node is in the list twice and a node is no thicker
than the stride. -/
theorem layout_clear (n : Network ε ν) {m : Measure} (col : ν → Nat) (nd : n.nodes.Nodup)
    (ht : m.thick ≤ m.stride) : (n.layout m col).Clear := by
  refine List.pairwise_map.mpr ((top_apart n m col nd).imp fun {u v} h => ?_)
  show (n.box m col u).Disjoint (n.box m col v)
  by_cases hc : col u = col v
  · have h' := h hc
    refine Or.inr (Or.inr (Or.inl ?_))
    show ((n.top m col u + n.length m u : Nat) : Int) ≤ ((n.top m col v : Nat) : Int)
    exact Int.ofNat_le.mpr (by omega)
  · cases Nat.lt_or_gt_of_ne hc with
    | inl hlt => exact Or.inl (box_forward n ht hlt)
    | inr hgt => exact Or.inr (Or.inl (box_forward n ht hgt))

/-- **Every node is inside the room.** -/
theorem layout_fits (n : Network ε ν) (m : Measure) (col : ν → Nat) : (n.layout m col).Fits := by
  intro a ha
  obtain ⟨v, hv, e⟩ := List.mem_map.mp ha
  rw [← e]
  have hw : left m col v + m.thick ≤ greatest (n.nodes.map fun v => left m col v + m.thick) :=
    le_greatest (List.mem_map_of_mem (f := fun v => left m col v + m.thick) hv)
  have hh : n.top m col v + n.length m v ≤
      greatest (n.nodes.map fun v => n.top m col v + n.length m v) :=
    le_greatest (List.mem_map_of_mem (f := fun v => n.top m col v + n.length m v) hv)
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hw, Int.natCast_nonneg _, Int.ofNat_le.mpr hh⟩

/-! ## The bands of the links -/

theorem bump_self (acc : ν → Nat) (v : ν) (x : Nat) : bump acc v x v = acc v + x := if_pos rfl

theorem bump_ne (acc : ν → Nat) {v k : ν} (h : k ≠ v) (x : Nat) : bump acc v x k = acc k :=
  if_neg h

theorem valuesAt_cons_pos (carry : ε → Nat) {side : ε → ν} {v : ν} {e : ε} (h : side e = v)
    (es : List ε) : valuesAt carry side v (e :: es) = carry e :: valuesAt carry side v es := by
  show ((e :: es).filter fun e => decide (side e = v)).map carry = _
  rw [List.filter_cons_of_pos (p := fun e => decide (side e = v)) (decide_eq_true h)]
  rfl

theorem valuesAt_cons_neg (carry : ε → Nat) {side : ε → ν} {v : ν} {e : ε} (h : side e ≠ v)
    (es : List ε) : valuesAt carry side v (e :: es) = valuesAt carry side v es := by
  show ((e :: es).filter fun e => decide (side e = v)).map carry = _
  rw [List.filter_cons_of_neg (p := fun e => decide (side e = v))
    (fun hh => h (of_decide_eq_true hh))]
  rfl

theorem channelsFrom_cons (n : Network ε ν) (m : Measure) (col : ν → Nat) (out into : ν → Nat)
    (e : ε) (es : List ε) : channelsFrom n m col out into (e :: es) =
      channelAt n m col out into e ::
        channelsFrom n m col (bump out (n.src e) (n.carry e)) (bump into (n.dst e) (n.carry e))
          es := rfl

/-- The bands that leave a node are the pile of what its links carry, in their order. -/
private theorem outsFrom (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    ∀ (es : List ε) (out into : ν → Nat),
      ((channelsFrom n m col out into es).filter fun c => decide (n.src c.link = v)).map
          (·.out) =
        (pile m.scale (out v) (valuesAt n.carry n.src v es)).map fun b =>
          band (left m col v + m.thick) (n.top m col v) b.1 b.2
  | [], _, _ => rfl
  | e :: es, out, into => by
    have ih := outsFrom n m col v es (bump out (n.src e) (n.carry e))
      (bump into (n.dst e) (n.carry e))
    by_cases h : n.src e = v
    · have hp : (fun c : Channel ε => decide (n.src c.link = v)) (channelAt n m col out into e) =
          true := decide_eq_true h
      rw [channelsFrom_cons,
        List.filter_cons_of_pos (p := fun c : Channel ε => decide (n.src c.link = v)) hp,
        List.map_cons, ih, valuesAt_cons_pos n.carry h]
      subst h
      rw [bump_self]
      rfl
    · have hp : ¬(fun c : Channel ε => decide (n.src c.link = v)) (channelAt n m col out into e) =
          true := fun hh => h (of_decide_eq_true hh)
      rw [channelsFrom_cons,
        List.filter_cons_of_neg (p := fun c : Channel ε => decide (n.src c.link = v)) hp,
        ih, valuesAt_cons_neg n.carry h, bump_ne out (fun e' => h e'.symm)]

/-- The bands that enter a node are the pile of what its links carry, in their order. -/
private theorem insFrom (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    ∀ (es : List ε) (out into : ν → Nat),
      ((channelsFrom n m col out into es).filter fun c => decide (n.dst c.link = v)).map
          (·.into) =
        (pile m.scale (into v) (valuesAt n.carry n.dst v es)).map fun b =>
          band (left m col v) (n.top m col v) b.1 b.2
  | [], _, _ => rfl
  | e :: es, out, into => by
    have ih := insFrom n m col v es (bump out (n.src e) (n.carry e))
      (bump into (n.dst e) (n.carry e))
    by_cases h : n.dst e = v
    · have hp : (fun c : Channel ε => decide (n.dst c.link = v)) (channelAt n m col out into e) =
          true := decide_eq_true h
      rw [channelsFrom_cons,
        List.filter_cons_of_pos (p := fun c : Channel ε => decide (n.dst c.link = v)) hp,
        List.map_cons, ih, valuesAt_cons_pos n.carry h]
      subst h
      rw [bump_self]
      rfl
    · have hp : ¬(fun c : Channel ε => decide (n.dst c.link = v)) (channelAt n m col out into e) =
          true := fun hh => h (of_decide_eq_true hh)
      rw [channelsFrom_cons,
        List.filter_cons_of_neg (p := fun c : Channel ε => decide (n.dst c.link = v)) hp,
        ih, valuesAt_cons_neg n.carry h, bump_ne into (fun e' => h e'.symm)]

/-- **The bands that leave a node are the pile of what its links carry**: in the order of the
links, down the right side of the node from its top. Every law of those bands is a law of
`pile`. -/
theorem outs_eq (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    n.outs m col v = (pile m.scale 0 (valuesAt n.carry n.src v n.links)).map fun b =>
      band (left m col v + m.thick) (n.top m col v) b.1 b.2 :=
  outsFrom n m col v n.links _ _

/-- **The bands that enter a node are the pile of what its links carry**, down the left side
of the node from its top. -/
theorem ins_eq (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    n.ins m col v = (pile m.scale 0 (valuesAt n.carry n.dst v n.links)).map fun b =>
      band (left m col v) (n.top m col v) b.1 b.2 :=
  insFrom n m col v n.links _ _

/-- **The bands that leave a node tile**: no gap and no overlap, on any scale. -/
theorem outs_stacked (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    Stacked (n.outs m col v) := by
  rw [outs_eq]
  exact stacked_of_tiles _ _ _ (pile_tiles _ _ _)

/-- **The bands that enter a node tile**: no gap and no overlap, on any scale. -/
theorem ins_stacked (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    Stacked (n.ins m col v) := by
  rw [ins_eq]
  exact stacked_of_tiles _ _ _ (pile_tiles _ _ _)

/-- **The widths of the bands that leave a node sum to what leaves it**, on the scale. -/
theorem outs_total (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    ((n.outs m col v).map IBox.height).sum = (m.scale (n.leaves v) : Int) - (m.scale 0 : Int) := by
  rw [outs_eq, pile_heights, Nat.zero_add]
  rfl

/-- **The widths of the bands that enter a node sum to what enters it**, on the scale. -/
theorem ins_total (n : Network ε ν) (m : Measure) (col : ν → Nat) (v : ν) :
    ((n.ins m col v).map IBox.height).sum = (m.scale (n.enters v) : Int) - (m.scale 0 : Int) := by
  rw [ins_eq, pile_heights, Nat.zero_add]
  rfl

/-- **Conservation.** At a node where what enters is what leaves, the bands that enter and the
bands that leave have one height together. -/
theorem conserved_heights {n : Network ε ν} (m : Measure) (col : ν → Nat) {v : ν}
    (h : n.Conserved v) :
    ((n.ins m col v).map IBox.height).sum = ((n.outs m col v).map IBox.height).sum := by
  have h' : n.enters v = n.leaves v := h
  rw [ins_total, outs_total, h']

/-- **At a node that conserves, the bands fill both sides**, on a scale that draws nothing
with no length: the bands that enter are together as high as the node, and so are the bands
that leave. -/
theorem conserved_fills {n : Network ε ν} {m : Measure} (col : ν → Nat) {v : ν}
    (h : n.Conserved v) (h0 : m.scale 0 = 0) :
    ((n.ins m col v).map IBox.height).sum = (n.box m col v).height ∧
      ((n.outs m col v).map IBox.height).sum = (n.box m col v).height := by
  have hv := value_of_conserved h
  have hb : (n.box m col v).height = (m.scale (n.value v) : Int) := by
    show ((n.top m col v + m.scale (n.value v) : Nat) : Int) - ((n.top m col v : Nat) : Int) = _
    omega
  rw [ins_total, outs_total, hb, h0]
  constructor
  · rw [hv.1]
    omega
  · rw [hv.2]
    omega

/-- **The bands that leave a node stay inside it**, on a scale that rises. -/
theorem outs_inside (n : Network ε ν) {m : Measure} (col : ν → Nat) (hs : Rising m.scale) {v : ν}
    {b : IBox} (hb : b ∈ n.outs m col v) : b.Inside (n.box m col v) := by
  rw [outs_eq] at hb
  obtain ⟨p, hp, e⟩ := List.mem_map.mp hb
  have hm := pile_mem hs _ 0 p hp
  have hl : p.2 ≤ m.scale (n.value v) :=
    Nat.le_trans hm.2.2 (hs _ _ (by rw [Nat.zero_add]; exact leaves_le_value n v))
  rw [← e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((left m col v : Nat) : Int) ≤ ((left m col v + m.thick : Nat) : Int)
    omega
  · exact Int.le_refl _
  · show ((n.top m col v : Nat) : Int) ≤ ((n.top m col v + p.1 : Nat) : Int)
    omega
  · show ((n.top m col v + p.2 : Nat) : Int) ≤ ((n.top m col v + m.scale (n.value v) : Nat) : Int)
    omega

/-- **The bands that enter a node stay inside it**, on a scale that rises. -/
theorem ins_inside (n : Network ε ν) {m : Measure} (col : ν → Nat) (hs : Rising m.scale) {v : ν}
    {b : IBox} (hb : b ∈ n.ins m col v) : b.Inside (n.box m col v) := by
  rw [ins_eq] at hb
  obtain ⟨p, hp, e⟩ := List.mem_map.mp hb
  have hm := pile_mem hs _ 0 p hp
  have hl : p.2 ≤ m.scale (n.value v) :=
    Nat.le_trans hm.2.2 (hs _ _ (by rw [Nat.zero_add]; exact enters_le_value n v))
  rw [← e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Int.le_refl _
  · show ((left m col v : Nat) : Int) ≤ ((left m col v + m.thick : Nat) : Int)
    omega
  · show ((n.top m col v : Nat) : Int) ≤ ((n.top m col v + p.1 : Nat) : Int)
    omega
  · show ((n.top m col v + p.2 : Nat) : Int) ≤ ((n.top m col v + m.scale (n.value v) : Nat) : Int)
    omega

/-! ## One link -/

/-- A placed link of a list is one of its links, placed after some sums. -/
private theorem mem_channelsFrom (n : Network ε ν) (m : Measure) (col : ν → Nat) {c : Channel ε} :
    ∀ (es : List ε) (out into : ν → Nat), c ∈ channelsFrom n m col out into es →
      ∃ out' into' e, e ∈ es ∧ c = channelAt n m col out' into' e
  | [], _, _, h => nomatch h
  | e :: es, out, into, h => by
    rw [channelsFrom_cons] at h
    cases List.mem_cons.mp h with
    | inl he => exact ⟨out, into, e, List.mem_cons_self, he⟩
    | inr h' =>
      obtain ⟨o, i, x, hx, hc⟩ := mem_channelsFrom n m col es _ _ h'
      exact ⟨o, i, x, List.mem_cons_of_mem _ hx, hc⟩

/-- **The placed links are the links**, in their order. -/
theorem channels_links (n : Network ε ν) (m : Measure) (col : ν → Nat) :
    (n.channels m col).map (·.link) = n.links := by
  have key : ∀ (es : List ε) (out into : ν → Nat),
      (channelsFrom n m col out into es).map (·.link) = es := by
    intro es
    induction es with
    | nil => exact fun _ _ => rfl
    | cons e es ih =>
      intro out into
      rw [channelsFrom_cons, List.map_cons, ih]
      rfl
  exact key n.links _ _

/-- **A link is a band as wide as what it carries, at each end.** On the right side of its
source and on the left side of its target, from the top of the node, its band is from the
length of a sum to the length of that sum and what the link carries. -/
theorem channel_spec (n : Network ε ν) (m : Measure) (col : ν → Nat) {c : Channel ε}
    (hc : c ∈ n.channels m col) :
    c.link ∈ n.links ∧ ∃ p q : Nat,
      c.out = band (left m col (n.src c.link) + m.thick) (n.top m col (n.src c.link))
        (m.scale p) (m.scale (p + n.carry c.link)) ∧
      c.into = band (left m col (n.dst c.link)) (n.top m col (n.dst c.link))
        (m.scale q) (m.scale (q + n.carry c.link)) := by
  obtain ⟨o, i, e, he, h⟩ := mem_channelsFrom n m col n.links _ _ hc
  rw [h]
  exact ⟨he, o (n.src e), i (n.dst e), rfl, rfl⟩

/-- **On a scale of whole units, a band is exactly what its link carries, times the unit**, at
both ends. -/
theorem channel_times (n : Network ε ν) {m : Measure} (col : ν → Nat) {k : Nat}
    (hk : m.scale = times k) {c : Channel ε} (hc : c ∈ n.channels m col) :
    c.out.height = (n.carry c.link * k : Nat) ∧ c.into.height = (n.carry c.link * k : Nat) := by
  obtain ⟨_, p, q, ho, hi⟩ := channel_spec n m col hc
  rw [ho, hi, hk]
  constructor
  · show ((n.top m col (n.src c.link) + (p + n.carry c.link) * k : Nat) : Int) -
        ((n.top m col (n.src c.link) + p * k : Nat) : Int) = ((n.carry c.link * k : Nat) : Int)
    rw [Nat.add_mul]
    omega
  · show ((n.top m col (n.dst c.link) + (q + n.carry c.link) * k : Nat) : Int) -
        ((n.top m col (n.dst c.link) + q * k : Nat) : Int) = ((n.carry c.link * k : Nat) : Int)
    rw [Nat.add_mul]
    omega

/-- **Both bands of a link stay inside its two nodes**, on a scale that rises. -/
theorem channel_inside (n : Network ε ν) {m : Measure} (col : ν → Nat) (hs : Rising m.scale)
    {c : Channel ε} (hc : c ∈ n.channels m col) :
    c.out.Inside (n.box m col (n.src c.link)) ∧ c.into.Inside (n.box m col (n.dst c.link)) :=
  ⟨outs_inside n col hs (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true rfl⟩, rfl⟩),
    ins_inside n col hs (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true rfl⟩, rfl⟩)⟩

/-- **Which nodes a link cannot meet.** Where a link goes to a later column, its room, which
is the least box that holds its two bands, shares nothing with a node whose column is the
source's or before it, or the target's or after it. So a link can meet a node only in a column
strictly between its two. -/
theorem channel_misses (n : Network ε ν) {m : Measure} (col : ν → Nat) (ht : m.thick ≤ m.stride)
    {c : Channel ε} (hc : c ∈ n.channels m col) (hf : col (n.src c.link) < col (n.dst c.link))
    (w : ν) (hw : col w ≤ col (n.src c.link) ∨ col (n.dst c.link) ≤ col w) :
    (n.box m col w).Disjoint (Boxed.box c) := by
  obtain ⟨_, p, q, ho, hi⟩ := channel_spec n m col hc
  have h1 : (col (n.src c.link) + 1) * m.stride ≤ col (n.dst c.link) * m.stride :=
    Nat.mul_le_mul_right m.stride hf
  rw [Nat.succ_mul] at h1
  show (n.box m col w).Disjoint (IBox.hull c.out c.into)
  rw [ho, hi]
  cases hw with
  | inl hle =>
    have h2 : col w * m.stride ≤ col (n.src c.link) * m.stride :=
      Nat.mul_le_mul_right m.stride hle
    refine Or.inl ?_
    show ((col w * m.stride + m.thick : Nat) : Int) ≤
      min ((col (n.src c.link) * m.stride + m.thick : Nat) : Int)
        ((col (n.dst c.link) * m.stride : Nat) : Int)
    omega
  | inr hge =>
    have h2 : col (n.dst c.link) * m.stride ≤ col w * m.stride :=
      Nat.mul_le_mul_right m.stride hge
    refine Or.inr (Or.inl ?_)
    show max ((col (n.src c.link) * m.stride + m.thick : Nat) : Int)
        ((col (n.dst c.link) * m.stride : Nat) : Int) ≤ ((col w * m.stride : Nat) : Int)
    omega

/-- **A link between two neighbouring columns meets no node.** -/
theorem channel_misses_neighbours (n : Network ε ν) {m : Measure} (col : ν → Nat)
    (ht : m.thick ≤ m.stride) {c : Channel ε} (hc : c ∈ n.channels m col)
    (hf : col (n.dst c.link) = col (n.src c.link) + 1) (w : ν) :
    (n.box m col w).Disjoint (Boxed.box c) :=
  channel_misses n col ht hc (by omega) w (by omega)

end

end Network

end Whatwg.Svg.Scene