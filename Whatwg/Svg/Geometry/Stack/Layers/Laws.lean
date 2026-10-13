import Whatwg.Svg.Geometry.Stack.Layers
import Whatwg.Svg.Geometry.Through.Laws
import Whatwg.Svg.Geometry.Stack

/-!
# Whatwg.Svg.Geometry.Stack.Layers.Laws

Owner: the laws of a stack of layers (ask W19 of the consumer's list; slice S22 of
`docs/SVG-PACKAGE-PLAN.md`).

d3-shape tests its stack on a handful of tables and states no law. Here the stack is exact, and
its laws are in two groups that a reader must keep apart: what holds **at the beats**, which is
of the numbers and is exact, and what holds **between two beats**, which is of the curve that
carries the edges.

## At the beats

Each law is of layers that have one value for each beat (`Stack.Even`).

- **The height of a layer at a beat is its value** (`heights_pile`, `heights_signed`): the top
  less the baseline, exactly, with its sign. So a layer whose value is zero at a beat has no
  height there (`pile_zero`).
- **Neighbouring layers share their edge** (`bases_pile`): the baselines of the layers of a
  pile are the floor, and then the tops of the layers, each of the layer before it. No gap at a
  beat.
- **At each beat a pile is a row of intervals** (`column_pile`): the bands of the layers at a
  beat are `stack` of `Whatwg/Svg/Geometry/Stack.lean`, of the values there. So where no value
  is negative no two layers overlap at a beat (`pile_apart`), and every layer lies between the
  floor and the sum of the values (`pile_within`): `stack_apart` and `stack_within` of that
  module, at every beat.
- **A stack of values that are never negative is a pile upon zero** (`signed_of_nonneg`), so
  the two laws above are laws of it. In a signed stack a layer with no value below zero stands
  on the upper edge and raises it (`signedFrom_up`), and a layer with no value above zero and
  one below hangs from the lower edge and lowers it (`signedFrom_down`). The two say, layer by
  layer, which edge each layer shares.
- **The signed stack is d3's diverging stack wherever no value is zero**
  (`diverging_eq_span`): its baseline and its top are d3's two edges.
- **A pile upon a raised floor is the pile, raised** (`pile_raise`).

## Between two beats

The edges of a layer are curves of a generator through the tops and through the baselines
(`Curve.Through.between`). What follows is of every generator, and then of the monotone curve.

- `chained_between`: the outline of a layer is a chain. `between_move`, `outlines_move`: **a
  moved stack is the stack, moved**: the abscissae by one number and the heights by another.
- **With the monotone curve an edge passes through its value at every beat**
  (`monotoneX_edge_starts`, `monotoneX_edge_ends`), where the abscissae of the beats go up. So
  the picture has the exact height at each beat.
- **With the monotone curve an edge stays between its two values from one beat to the next**:
  that is `Curve.monotoneX_within` of `Whatwg/Svg/Geometry/Monotone/Laws.lean`, of every piece.
  So an edge never leaves the range of its values (`monotoneX_edge_ge`, `monotoneX_edge_le`),
  and the outline of a layer never leaves the band of its baselines and its tops
  (`between_range`). The picture invents no quantity above the greatest or below the least.
- **Two edges can cross between two beats**, and then a layer has a place where its top is
  under its baseline. It happens where the baseline changes steeply while the layer is thin:
  the control of `WhatwgTest/Svg/Stack.lean` is three beats of two layers. The monotone curve
  keeps each edge between its own two values, and that is no promise about two edges.
- **They do not cross where the two values of the baseline are no more than the two values of
  the top** (`Stack.apart`), from one beat to the next. So a layer upon a level baseline never
  goes under it (`over_level`, and `first_over_level` for a layer of values that are never
  negative upon a floor of one number): the first layer of a pile upon zero, and the units held
  and the offers of the consumer's queue, whose baselines are zero and the brim.

What this module does not claim: that the layers of a stack do not cross between beats, which
is false; a stack whose thicknesses, and not whose edges, are carried by the monotone curve,
which would never cross and whose edges could leave the range of their values instead (a
sketch in the seat's report); a law of the monotone curve under a change of scale, so a caller
scales the heights first and carries the curve through the scaled points.
-/

namespace Whatwg.Svg.Value

namespace Stack

/-! ## Lists that are zipped -/

/-- A function of each member of two lists that agrees with another on the members of the
second gives the same list. -/
theorem zipWith_congr_mem {β γ : Type} {f g : β → Rat → γ} : ∀ (es : List β) (layer : List Rat),
    (∀ e, ∀ v ∈ layer, f e v = g e v) → List.zipWith f es layer = List.zipWith g es layer
  | [], _, _ => by rw [List.zipWith_nil_left, List.zipWith_nil_left]
  | _ :: _, [], _ => rfl
  | e :: es, v :: vs, h => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, h e v List.mem_cons_self,
      zipWith_congr_mem es vs fun e' v' hv => h e' v' (List.mem_cons_of_mem v hv)]

/-- A function of each member of two lists, and then another of the result, is one function of
each member of the two. -/
theorem map_zipWith' {β γ δ : Type} (g : γ → δ) (f : β → Rat → γ) : ∀ (es : List β)
    (layer : List Rat),
    (List.zipWith f es layer).map g = List.zipWith (fun e v => g (f e v)) es layer
  | [], _ => by rw [List.zipWith_nil_left, List.zipWith_nil_left]; rfl
  | _ :: _, [] => rfl
  | e :: es, v :: vs => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.map_cons, map_zipWith' g f es vs]

/-- A function that reads the first of a pair, over a list of pairs, is the function over the
list of the firsts. -/
theorem zipWith_fst {γ : Type} (f : Rat → Rat → γ) : ∀ (es : List (Rat × Rat)) (layer : List Rat),
    List.zipWith (fun e v => f e.1 v) es layer = List.zipWith f (es.map Prod.fst) layer
  | [], _ => by rw [List.zipWith_nil_left]; rfl
  | _ :: _, [] => rfl
  | e :: es, v :: vs => by
    rw [List.zipWith_cons_cons, List.map_cons, List.zipWith_cons_cons, zipWith_fst f es vs]

/-- Where each result has the height of its value, the heights of the results are the values,
for a value at every place. -/
theorem heights_zipWith {β : Type} (f : β → Rat → Rat × Rat)
    (hf : ∀ e v, (f e v).2 - (f e v).1 = v) : ∀ (es : List β) (layer : List Rat),
    layer.length ≤ es.length → heights (List.zipWith f es layer) = layer
  | _, [], _ => by
    show (List.zipWith f _ []).map (fun e => e.2 - e.1) = []
    rw [List.zipWith_nil_right]
    rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | e :: es, v :: vs, h => by
    have ih := heights_zipWith f hf es vs (Nat.le_of_succ_le_succ h)
    show ((f e v).2 - (f e v).1) :: heights (List.zipWith f es vs) = v :: vs
    rw [ih, hf]

/-- Where each result starts at the member of the first list, the baselines of the results are
the first list, for a member of the second at every place. -/
theorem bases_zipWith (f : Rat → Rat → Rat × Rat) (hf : ∀ b v, (f b v).1 = b) :
    ∀ (floor layer : List Rat), floor.length ≤ layer.length →
      bases (List.zipWith f floor layer) = floor
  | [], _, _ => by
    show (List.zipWith f [] _).map Prod.fst = []
    rw [List.zipWith_nil_left]
    rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | b :: bs, v :: vs, h => by
    have ih := bases_zipWith f hf bs vs (Nat.le_of_succ_le_succ h)
    show (f b v).1 :: bases (List.zipWith f bs vs) = b :: bs
    rw [ih, hf]

/-! ## At the beats: a pile -/

/-- **The layers have one value for each of `n` beats.** -/
def Even (n : Nat) (layers : List (List Rat)) : Prop := ∀ layer ∈ layers, layer.length = n

instance (n : Nat) (layers : List (List Rat)) : Decidable (Even n layers) :=
  inferInstanceAs (Decidable (∀ layer ∈ layers, layer.length = n))

/-- The tops of the band of a layer upon a floor are the floor and the values. -/
theorem tops_band (floor layer : List Rat) :
    tops (List.zipWith (fun b v => (b, b + v)) floor layer) =
      List.zipWith (fun b v => b + v) floor layer :=
  map_zipWith' Prod.snd _ floor layer

/-- **Each layer of a pile stands upon the tops of the one before it.** -/
theorem pile_cons (floor layer : List Rat) (rest : List (List Rat)) :
    pile floor (layer :: rest) =
      List.zipWith (fun b v => (b, b + v)) floor layer ::
        pile (tops (List.zipWith (fun b v => (b, b + v)) floor layer)) rest := by
  rw [tops_band]
  rfl

/-- **The height of a layer of a pile at a beat is its value**: the top less the baseline,
exactly, at every beat of every layer. -/
theorem heights_pile : ∀ (layers : List (List Rat)) (floor : List Rat),
    Even floor.length layers → (pile floor layers).map heights = layers
  | [], _, _ => rfl
  | layer :: rest, floor, h => by
    have hl : layer.length = floor.length := h layer List.mem_cons_self
    have hlen : (List.zipWith (fun b v => b + v) floor layer).length = floor.length := by
      rw [List.length_zipWith, hl, Nat.min_self]
    have ih := heights_pile rest (List.zipWith (fun b v => b + v) floor layer) fun l hm =>
      (h l (List.mem_cons_of_mem _ hm)).trans hlen.symm
    show heights (List.zipWith (fun b v => (b, b + v)) floor layer) ::
      (pile (List.zipWith (fun b v => b + v) floor layer) rest).map heights = layer :: rest
    rw [ih, heights_zipWith (fun b v => (b, b + v)) (fun b v => by
      show b + v - b = v
      grind) floor layer (Nat.le_of_eq hl)]

/-- **Neighbouring layers of a pile share their edge.** The baselines of the layers are the
floor, and then the tops of the layers, each of the layer before it: no gap and no overlap at
any beat. -/
theorem bases_pile : ∀ (layers : List (List Rat)) (floor : List Rat),
    Even floor.length layers →
      (pile floor layers).map bases = (floor :: (pile floor layers).map tops).dropLast
  | [], _, _ => rfl
  | layer :: rest, floor, h => by
    have hl : layer.length = floor.length := h layer List.mem_cons_self
    have hlen : (List.zipWith (fun b v => b + v) floor layer).length = floor.length := by
      rw [List.length_zipWith, hl, Nat.min_self]
    have ih := bases_pile rest (List.zipWith (fun b v => b + v) floor layer) fun l hm =>
      (h l (List.mem_cons_of_mem _ hm)).trans hlen.symm
    have hb := bases_zipWith (fun b v => (b, b + v)) (fun _ _ => rfl) floor layer (Nat.le_of_eq hl.symm)
    show bases (List.zipWith (fun b v => (b, b + v)) floor layer) ::
        (pile (List.zipWith (fun b v => b + v) floor layer) rest).map bases =
      floor :: (tops (List.zipWith (fun b v => (b, b + v)) floor layer) ::
        (pile (List.zipWith (fun b v => b + v) floor layer) rest).map tops).dropLast
    rw [hb, ih, tops_band]

/-- **A layer whose value is zero at a beat has no height there**: where a band has the heights
of its layer, an entry whose value is `0` has its top at its baseline. -/
theorem pile_zero {band : List (Rat × Rat)} {layer : List Rat} (h : heights band = layer)
    {i : Nat} {e : Rat × Rat} (he : band[i]? = some e) (hv : layer[i]? = some 0) : e.2 = e.1 := by
  have h' : (heights band)[i]? = some (e.2 - e.1) := by
    show (band.map fun e => e.2 - e.1)[i]? = some (e.2 - e.1)
    rw [List.getElem?_map, he]
    rfl
  rw [h, hv] at h'
  have e0 : (0 : Rat) = e.2 - e.1 := Option.some.inj h'
  grind

/-! ## At one beat a pile is a row of intervals -/

/-- The member of two zipped lists at a place is the function of the two members there. -/
theorem getElem?_zip {γ : Type} (f : Rat → Rat → γ) : ∀ (l l' : List Rat) (i : Nat) (a b : Rat),
    l[i]? = some a → l'[i]? = some b → (List.zipWith f l l')[i]? = some (f a b)
  | [], _, _, _, _, h, _ => by
    rw [List.getElem?_nil] at h
    cases h
  | _ :: _, [], _, _, _, _, h' => by
    rw [List.getElem?_nil] at h'
    cases h'
  | x :: xs, y :: ys, 0, a, b, h, h' => by
    rw [List.getElem?_cons_zero] at h h'
    cases h
    cases h'
    exact List.getElem?_cons_zero
  | x :: xs, y :: ys, i + 1, a, b, h, h' => by
    rw [List.getElem?_cons_succ] at h h'
    show (f x y :: List.zipWith f xs ys)[i + 1]? = some (f a b)
    rw [List.getElem?_cons_succ]
    exact getElem?_zip f xs ys i a b h h'

/-- **At each beat a pile is a row of intervals**: the bands of the layers at the beat `b` are
`stack` of `Whatwg/Svg/Geometry/Stack.lean`, from the floor at that beat, of the values of the
layers there. So the laws of a row are laws of every beat of a pile. -/
theorem column_pile : ∀ (layers : List (List Rat)) (floor : List Rat) (b : Nat) (x : Rat),
    floor[b]? = some x → Even floor.length layers →
      column (pile floor layers) b = stack x (valuesAt layers b)
  | [], _, _, _, _, _ => rfl
  | layer :: rest, floor, b, x, hx, h => by
    have hl : layer.length = floor.length := h layer List.mem_cons_self
    have hlen : (List.zipWith (fun b v => b + v) floor layer).length = floor.length := by
      rw [List.length_zipWith, hl, Nat.min_self]
    cases hv : layer[b]? with
    | none =>
      have h1 := List.getElem?_eq_none_iff.mp hv
      have h2 : floor[b]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      rw [h2] at hx
      cases hx
    | some v =>
      have e1 := getElem?_zip (fun b v => (b, b + v)) floor layer b x v hx hv
      have e2 := getElem?_zip (fun b v => b + v) floor layer b x v hx hv
      have ih := column_pile rest (List.zipWith (fun b v => b + v) floor layer) b (x + v) e2
        fun l hm => (h l (List.mem_cons_of_mem _ hm)).trans hlen.symm
      show (List.zipWith (fun b v => (b, b + v)) floor layer ::
          pile (List.zipWith (fun b v => b + v) floor layer) rest).filterMap
            (fun band => band[b]?) =
        stack x ((layer :: rest).filterMap fun layer => layer[b]?)
      rw [List.filterMap_cons_some (f := fun band : List (Rat × Rat) => band[b]?) e1,
        List.filterMap_cons_some (f := fun layer : List Rat => layer[b]?) hv]
      show (x, x + v) :: column (pile (List.zipWith (fun b v => b + v) floor layer) rest) b =
        (x, x + v) :: stack (x + v) (valuesAt rest b)
      rw [ih]

/-- A value of the layers at a beat is a value of a layer. -/
theorem mem_valuesAt {layers : List (List Rat)} {b : Nat} {w : Rat} (h : w ∈ valuesAt layers b) :
    ∃ layer ∈ layers, w ∈ layer := by
  obtain ⟨layer, hl, hv⟩ := List.mem_filterMap.mp h
  exact ⟨layer, hl, List.mem_of_getElem? hv⟩

/-- **No two layers of a pile overlap at a beat**, where no value is negative: at each beat
every layer ends at or before the start of every later one. With `bases_pile` there is no gap
between two neighbours either. -/
theorem pile_apart (layers : List (List Rat)) (floor : List Rat) (b : Nat) (x : Rat)
    (hx : floor[b]? = some x) (h : Even floor.length layers)
    (hn : ∀ layer ∈ layers, ∀ v ∈ layer, 0 ≤ v) :
    (column (pile floor layers) b).Pairwise fun p q => p.2 ≤ q.1 := by
  rw [column_pile layers floor b x hx h]
  exact stack_apart x _ fun w hw => by
    obtain ⟨layer, hl, hv⟩ := mem_valuesAt hw
    exact hn layer hl w hv

/-- **Every layer of a pile lies between the floor and the sum of the values at a beat**,
where no value is negative. -/
theorem pile_within (layers : List (List Rat)) (floor : List Rat) (b : Nat) (x : Rat)
    (hx : floor[b]? = some x) (h : Even floor.length layers)
    (hn : ∀ layer ∈ layers, ∀ v ∈ layer, 0 ≤ v) :
    ∀ p ∈ column (pile floor layers) b,
      x ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ x + total (valuesAt layers b) := by
  rw [column_pile layers floor b x hx h]
  exact stack_within x _ fun w hw => by
    obtain ⟨layer, hl, hv⟩ := mem_valuesAt hw
    exact hn layer hl w hv

/-- A band raised by `c`: both of its edges at every beat. -/
def raise (c : Rat) (band : List (Rat × Rat)) : List (Rat × Rat) :=
  band.map fun e => (e.1 + c, e.2 + c)

/-- The band of a layer upon a raised floor is the band, raised. -/
theorem band_raise (c : Rat) : ∀ (floor layer : List Rat),
    List.zipWith (fun b v => (b, b + v)) (floor.map fun b => b + c) layer =
      raise c (List.zipWith (fun b v => (b, b + v)) floor layer)
  | [], _ => by
    rw [List.map_nil, List.zipWith_nil_left]
    rfl
  | _ :: _, [] => rfl
  | b :: bs, v :: vs => by
    have e : b + c + v = b + v + c := by grind
    show (b + c, b + c + v) :: List.zipWith (fun b v => (b, b + v)) (bs.map fun b => b + c) vs =
      (b + c, b + v + c) :: raise c (List.zipWith (fun b v => (b, b + v)) bs vs)
    rw [band_raise c bs vs, e]

/-- The tops of a layer upon a raised floor are the tops, raised. -/
theorem tops_raise (c : Rat) : ∀ (floor layer : List Rat),
    List.zipWith (fun b v => b + v) (floor.map fun b => b + c) layer =
      (List.zipWith (fun b v => b + v) floor layer).map fun b => b + c
  | [], _ => by
    rw [List.map_nil, List.zipWith_nil_left]
    rfl
  | _ :: _, [] => rfl
  | b :: bs, v :: vs => by
    have e : b + c + v = b + v + c := by grind
    show (b + c + v) :: List.zipWith (fun b v => b + v) (bs.map fun b => b + c) vs =
      (b + v + c) :: (List.zipWith (fun b v => b + v) bs vs).map fun b => b + c
    rw [tops_raise c bs vs, e]

/-- **A pile upon a raised floor is the pile, raised.** -/
theorem pile_raise (c : Rat) : ∀ (layers : List (List Rat)) (floor : List Rat),
    pile (floor.map fun b => b + c) layers = (pile floor layers).map (raise c)
  | [], _ => rfl
  | layer :: rest, floor => by
    show List.zipWith (fun b v => (b, b + v)) (floor.map fun b => b + c) layer ::
        pile (List.zipWith (fun b v => b + v) (floor.map fun b => b + c) layer) rest =
      raise c (List.zipWith (fun b v => (b, b + v)) floor layer) ::
        (pile (List.zipWith (fun b v => b + v) floor layer) rest).map (raise c)
    rw [band_raise c floor layer, tops_raise c floor layer, pile_raise c rest]

/-! ## At the beats: a signed stack -/

/-- **The height of a layer of a signed stack at a beat is its value, with its sign**: the top
less the baseline, exactly. -/
theorem heights_signedFrom : ∀ (layers : List (List Rat)) (edges : List (Rat × Rat)),
    Even edges.length layers → (signedFrom edges layers).map heights = layers
  | [], _, _ => rfl
  | layer :: rest, edges, h => by
    have hl : layer.length = edges.length := h layer List.mem_cons_self
    have hlen : (List.zipWith grow edges layer).length = edges.length := by
      rw [List.length_zipWith, hl, Nat.min_self]
    have ih := heights_signedFrom rest (List.zipWith grow edges layer) fun l hm =>
      (h l (List.mem_cons_of_mem _ hm)).trans hlen.symm
    show heights (List.zipWith (signedAt (hangs layer)) edges layer) ::
      (signedFrom (List.zipWith grow edges layer) rest).map heights = layer :: rest
    rw [ih, heights_zipWith (signedAt (hangs layer)) (fun e v => by
      show baseAt (hangs layer) e v + v - baseAt (hangs layer) e v = v
      grind) edges layer (Nat.le_of_eq hl)]

/-- The floor at zero has a beat for each value of the first layer. -/
theorem length_ground (layer : List Rat) (rest : List (List Rat)) :
    (ground (layer :: rest)).length = layer.length := List.length_replicate

/-- **The height of a layer of a signed stack at a beat is its value**, for layers that have a
value for each beat of the first. -/
theorem heights_signed (layer : List Rat) (rest : List (List Rat))
    (h : Even layer.length (layer :: rest)) :
    (signed (layer :: rest)).map heights = layer :: rest :=
  heights_signedFrom (layer :: rest) _ (by
    rw [List.length_map, length_ground]
    exact h)

/-- A layer with no value below zero does not hang. -/
theorem hangs_of_nonneg {layer : List Rat} (h : ∀ v ∈ layer, 0 ≤ v) : hangs layer = false :=
  List.any_eq_false.mpr fun v hv => by
    have := h v hv
    simp only [decide_eq_true_eq]
    grind

/-- **A layer with no value below zero stands on the upper edge of the stack and raises it**:
its baseline at each beat is the upper edge, and the upper edge after it is its top. The lower
edge is as it was. -/
theorem signedFrom_up (edges : List (Rat × Rat)) (layer : List Rat) (rest : List (List Rat))
    (h : ∀ v ∈ layer, 0 ≤ v) :
    signedFrom edges (layer :: rest) =
      List.zipWith (fun e v => (e.1, e.1 + v)) edges layer ::
        signedFrom (List.zipWith (fun e v => (e.1 + v, e.2)) edges layer) rest := by
  have e1 : List.zipWith (signedAt (hangs layer)) edges layer =
      List.zipWith (fun e v => (e.1, e.1 + v)) edges layer :=
    zipWith_congr_mem edges layer fun e v hv => by
      have h0 := h v hv
      rw [hangs_of_nonneg h]
      simp only [signedAt, baseAt, Bool.false_eq_true, if_false]
      by_cases hp : 0 < v
      · rw [if_pos hp]
      · rw [if_neg hp, if_neg (by grind)]
  have e2 : List.zipWith grow edges layer =
      List.zipWith (fun e v => (e.1 + v, e.2)) edges layer :=
    zipWith_congr_mem edges layer fun e v hv => by
      have h0 := h v hv
      simp only [grow]
      by_cases hp : 0 < v
      · rw [if_pos hp]
      · have hz : v = 0 := by grind
        rw [if_neg hp, if_neg (by grind), hz, Rat.add_zero]
  show List.zipWith (signedAt (hangs layer)) edges layer ::
    signedFrom (List.zipWith grow edges layer) rest = _
  rw [e1, e2]

/-- **A layer with no value above zero, and one below it, hangs from the lower edge of the
stack and lowers it**: its baseline at each beat is the lower edge, and the lower edge after it
is its top. The upper edge is as it was. -/
theorem signedFrom_down (edges : List (Rat × Rat)) (layer : List Rat) (rest : List (List Rat))
    (h : ∀ v ∈ layer, v ≤ 0) (hd : hangs layer = true) :
    signedFrom edges (layer :: rest) =
      List.zipWith (fun e v => (e.2, e.2 + v)) edges layer ::
        signedFrom (List.zipWith (fun e v => (e.1, e.2 + v)) edges layer) rest := by
  have e1 : List.zipWith (signedAt (hangs layer)) edges layer =
      List.zipWith (fun e v => (e.2, e.2 + v)) edges layer :=
    zipWith_congr_mem edges layer fun e v hv => by
      have h0 := h v hv
      rw [hd]
      simp only [signedAt, baseAt, if_true]
      by_cases hn : v < 0
      · rw [if_neg (by grind), if_pos hn]
      · rw [if_neg (by grind), if_neg hn]
  have e2 : List.zipWith grow edges layer =
      List.zipWith (fun e v => (e.1, e.2 + v)) edges layer :=
    zipWith_congr_mem edges layer fun e v hv => by
      have h0 := h v hv
      simp only [grow]
      by_cases hn : v < 0
      · rw [if_neg (by grind), if_pos hn]
      · have hz : v = 0 := by grind
        rw [if_neg (by grind), if_neg hn, hz, Rat.add_zero]
  show List.zipWith (signedAt (hangs layer)) edges layer ::
    signedFrom (List.zipWith grow edges layer) rest = _
  rw [e1, e2]

/-- A signed stack of values that are never negative, from two edges at each beat, is the pile
upon the upper edges. -/
theorem signedFrom_of_nonneg : ∀ (layers : List (List Rat)) (edges : List (Rat × Rat)),
    (∀ layer ∈ layers, ∀ v ∈ layer, 0 ≤ v) →
      signedFrom edges layers = pile (edges.map Prod.fst) layers
  | [], _, _ => rfl
  | layer :: rest, edges, h => by
    have ih := signedFrom_of_nonneg rest (List.zipWith (fun e v => (e.1 + v, e.2)) edges layer)
      fun l hl => h l (List.mem_cons_of_mem _ hl)
    have e3 : (List.zipWith (fun e v => (e.1 + v, e.2)) edges layer).map Prod.fst =
        List.zipWith (fun b v => b + v) (edges.map Prod.fst) layer := by
      rw [map_zipWith' Prod.fst _ edges layer]
      exact zipWith_fst (fun b v => b + v) edges layer
    rw [signedFrom_up edges layer rest (h layer List.mem_cons_self), ih, e3]
    show List.zipWith (fun e v => (e.1, e.1 + v)) edges layer :: _ =
      List.zipWith (fun b v => (b, b + v)) (edges.map Prod.fst) layer :: _
    rw [zipWith_fst (fun b v => (b, b + v)) edges layer]

/-- **A signed stack of values that are never negative is the pile upon zero.** So the laws of
a pile are laws of it: the height of a layer is its value, and neighbouring layers share their
edge. -/
theorem signed_of_nonneg (layers : List (List Rat)) (h : ∀ layer ∈ layers, ∀ v ∈ layer, 0 ≤ v) :
    signed layers = plain layers := by
  have e : ((ground layers).map fun z => (z, z)).map Prod.fst = ground layers := by
    rw [List.map_map]
    exact List.map_id _
  show signedFrom ((ground layers).map fun z => (z, z)) layers = pile (ground layers) layers
  rw [signedFrom_of_nonneg layers _ h, e]

/-- d3's two edges of a value that is not zero are the baseline and the top of the signed
stack, in order. -/
theorem divergingAt_eq_span (down : Bool) (e : Rat × Rat) {v : Rat} (hv : v ≠ 0) :
    divergingAt e v = span (signedAt down e v) := by
  simp only [divergingAt, span, signedAt, baseAt]
  by_cases hp : 0 < v
  · rw [if_pos hp, if_pos hp]
    exact Prod.ext (by show e.1 = min e.1 (e.1 + v); grind) (by show e.1 + v = max e.1 (e.1 + v); grind)
  · have hn : v < 0 := by grind
    rw [if_neg hp, if_pos hn, if_neg hp, if_pos hn]
    exact Prod.ext (by show e.2 + v = min e.2 (e.2 + v); grind) (by show e.2 = max e.2 (e.2 + v); grind)

/-- d3's diverging offset from two edges at each beat is the signed stack from them, wherever no
value is zero. -/
theorem divergingFrom_eq_span : ∀ (layers : List (List Rat)) (edges : List (Rat × Rat)),
    (∀ layer ∈ layers, ∀ v ∈ layer, v ≠ 0) →
      divergingFrom edges layers = (signedFrom edges layers).map fun band => band.map span
  | [], _, _ => rfl
  | layer :: rest, edges, h => by
    have e1 : List.zipWith divergingAt edges layer =
        (List.zipWith (signedAt (hangs layer)) edges layer).map span := by
      rw [map_zipWith' span _ edges layer]
      exact zipWith_congr_mem edges layer fun e v hv =>
        divergingAt_eq_span (hangs layer) e (h layer List.mem_cons_self v hv)
    show List.zipWith divergingAt edges layer :: divergingFrom (List.zipWith grow edges layer) rest =
      (List.zipWith (signedAt (hangs layer)) edges layer).map span ::
        (signedFrom (List.zipWith grow edges layer) rest).map fun band => band.map span
    rw [e1, divergingFrom_eq_span rest _ fun l hl => h l (List.mem_cons_of_mem _ hl)]

/-- **The signed stack is d3's diverging stack wherever no value is zero**: the baseline and
the top of each layer at each beat are d3's two edges. At a value of zero d3 puts the layer at
zero, and the signed stack on the edge of its side. -/
theorem diverging_eq_span (layers : List (List Rat)) (h : ∀ layer ∈ layers, ∀ v ∈ layer, v ≠ 0) :
    diverging layers = (signed layers).map fun band => band.map span :=
  divergingFrom_eq_span layers _ h

/-! ## Between two beats: every generator -/

/-- A point of an edge has the abscissa of a beat and a height of the edge. -/
theorem mem_edge : ∀ {xs ys : List Rat} {p : Vec}, p ∈ edge xs ys → p.x ∈ xs ∧ p.y ∈ ys
  | [], _, _, h => by
    rw [edge, List.zipWith_nil_left] at h
    cases h
  | _ :: _, [], _, h => nomatch h
  | x :: xs, y :: ys, p, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · have ih := mem_edge (xs := xs) (ys := ys) h'
      exact ⟨List.mem_cons_of_mem x ih.1, List.mem_cons_of_mem y ih.2⟩

/-- The points of an edge whose abscissae and heights are moved are the points, moved. -/
theorem edge_move (d : Vec) : ∀ (xs ys : List Rat),
    edge (xs.map fun x => x + d.x) (ys.map fun y => y + d.y) = (edge xs ys).map fun p => p + d
  | [], _ => by rw [List.map_nil, edge, edge, List.zipWith_nil_left, List.zipWith_nil_left]; rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show (⟨x + d.x, y + d.y⟩ : Vec) :: edge (xs.map fun x => x + d.x) (ys.map fun y => y + d.y) =
      ((⟨x, y⟩ : Vec) + d) :: (edge xs ys).map fun p => p + d
    rw [edge_move d xs ys]
    rfl

end Stack

namespace Curve.Through

open Stack

/-- **The outline of a layer is a chain**, whatever carries the way back. -/
theorem chained_between (g back : Through) (xs : List Rat) (band : List (Rat × Rat)) :
    Cubic.Chained (g.between xs band back) = true :=
  chained_areaCubics g back _ _

/-- **The outline of a moved layer is the outline, moved**: the abscissae of the beats by
`d.x`, and both edges by `d.y`. -/
theorem between_move (g back : Through) (d : Vec) (xs : List Rat) (band : List (Rat × Rat)) :
    g.between (xs.map fun x => x + d.x) (raise d.y band) back =
      (g.between xs band back).map (Cubic.move d) := by
  have et : tops (raise d.y band) = (tops band).map fun y => y + d.y := by
    show (band.map fun e => (e.1 + d.y, e.2 + d.y)).map Prod.snd =
      (band.map Prod.snd).map fun y => y + d.y
    rw [List.map_map, List.map_map]
    rfl
  have eb : bases (raise d.y band) = (bases band).map fun y => y + d.y := by
    show (band.map fun e => (e.1 + d.y, e.2 + d.y)).map Prod.fst =
      (band.map Prod.fst).map fun y => y + d.y
    rw [List.map_map, List.map_map]
    rfl
  show g.areaCubics (edge (xs.map fun x => x + d.x) (tops (raise d.y band)))
      (edge (xs.map fun x => x + d.x) (bases (raise d.y band))) back =
    (g.areaCubics (edge xs (tops band)) (edge xs (bases band)) back).map (Cubic.move d)
  rw [et, eb, edge_move, edge_move, areaCubics_move]

end Curve.Through

namespace Stack

/-- **A moved stack is the stack, moved**: the outlines of the layers at moved abscissae, with
every band raised, are the outlines, moved. With `pile_raise`, the outlines of a pile upon a
raised floor are the outlines of the pile, raised. -/
theorem outlines_move (g : Curve.Through) (d : Vec) (xs : List Rat)
    (bands : List (List (Rat × Rat))) :
    outlines g (xs.map fun x => x + d.x) (bands.map (raise d.y)) =
      (outlines g xs bands).map fun cs => cs.map (Cubic.move d) := by
  show (bands.map (raise d.y)).map (fun band => g.between (xs.map fun x => x + d.x) band) =
    (bands.map fun band => g.between xs band).map fun cs => cs.map (Cubic.move d)
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun band _ => Curve.Through.between_move g g d xs band

/-! ## Between two beats: the monotone curve -/

/-- Points that are each another point than every later one have no point that is the one
before it again. -/
theorem distinct_of_pairwise : ∀ {ps : List Vec}, ps.Pairwise (fun p q => p ≠ q) →
    Monotone.distinct ps = ps
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    have hab : a ≠ b := (List.pairwise_cons.mp h).1 b List.mem_cons_self
    show (if a = b then Monotone.distinct (b :: rest) else a :: Monotone.distinct (b :: rest)) =
      a :: b :: rest
    rw [if_neg hab, distinct_of_pairwise (List.pairwise_cons.mp h).2]

/-- The points of an edge at abscissae that go up are each another point than every later
one. -/
theorem edge_pairwise : ∀ {xs : List Rat} (ys : List Rat), xs.Pairwise (fun a b => a < b) →
    (edge xs ys).Pairwise fun p q => p ≠ q
  | [], _, _ => by
    rw [edge, List.zipWith_nil_left]
    exact List.Pairwise.nil
  | _ :: _, [], _ => List.Pairwise.nil
  | x :: xs, y :: ys, h => by
    have hx := List.pairwise_cons.mp h
    show ((⟨x, y⟩ : Vec) :: edge xs ys).Pairwise fun p q => p ≠ q
    refine List.pairwise_cons.mpr ⟨fun q hq e => ?_, edge_pairwise ys hx.2⟩
    have hlt := hx.1 q.x (mem_edge hq).1
    rw [← e] at hlt
    exact absurd hlt (Rat.lt_irrefl)

/-- **With the monotone curve, an edge starts a piece at its value at every beat but the
last**, in order, where the abscissae of the beats go up. -/
theorem monotoneX_edge_starts {xs : List Rat} (ys : List Rat)
    (h : xs.Pairwise fun a b => a < b) :
    (Curve.monotoneX (edge xs ys)).map (fun c => c.p0) = (edge xs ys).dropLast := by
  rw [Curve.monotoneX_starts, distinct_of_pairwise (edge_pairwise ys h)]

/-- **With the monotone curve, an edge ends a piece at its value at every beat but the
first**, in order, where the abscissae of the beats go up. So the picture has the exact height
of a layer at each beat. -/
theorem monotoneX_edge_ends {xs : List Rat} (ys : List Rat) (h : xs.Pairwise fun a b => a < b) :
    (Curve.monotoneX (edge xs ys)).map (fun c => c.p3) = (edge xs ys).tail := by
  rw [Curve.monotoneX_ends, distinct_of_pairwise (edge_pairwise ys h)]

/-- **With the monotone curve an edge is never under the least of its values.** -/
theorem monotoneX_edge_ge (xs ys : List Rat) {lo : Rat} (h : ∀ y ∈ ys, lo ≤ y) {c : Cubic}
    (hc : c ∈ Curve.monotoneX (edge xs ys)) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lo ≤ (c.pointAt s).y := by
  have w := Curve.monotoneX_within _ hc hs0 hs1
  obtain ⟨m0, m3⟩ := Curve.mem_of_mem_monotoneX hc
  have r0 := h _ (mem_edge m0).2
  have r3 := h _ (mem_edge m3).2
  simp only [Box.Contains, Box.ofCorners] at w
  grind

/-- **With the monotone curve an edge is never over the greatest of its values.** -/
theorem monotoneX_edge_le (xs ys : List Rat) {hi : Rat} (h : ∀ y ∈ ys, y ≤ hi) {c : Cubic}
    (hc : c ∈ Curve.monotoneX (edge xs ys)) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (c.pointAt s).y ≤ hi := by
  have w := Curve.monotoneX_within _ hc hs0 hs1
  obtain ⟨m0, m3⟩ := Curve.mem_of_mem_monotoneX hc
  have r0 := h _ (mem_edge m0).2
  have r3 := h _ (mem_edge m3).2
  simp only [Box.Contains, Box.ofCorners] at w
  grind

/-- **The outline of a layer never leaves the band of its baselines and its tops**, with the
monotone curve: where every baseline and every top is between `lo` and `hi`, so is every point
of the outline. The picture invents no quantity above the greatest or below the least. -/
theorem between_range (xs : List Rat) (band : List (Rat × Rat)) {lo hi : Rat}
    (h : ∀ e ∈ band, lo ≤ e.1 ∧ e.1 ≤ hi ∧ lo ≤ e.2 ∧ e.2 ≤ hi) {c : Cubic}
    (hc : c ∈ Curve.Through.monotoneX.between xs band) {s : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lo ≤ (c.pointAt s).y ∧ (c.pointAt s).y ≤ hi := by
  refine Curve.Through.monotoneX_area_range _ _ (fun p hp => ?_) (fun p hp => ?_) hc hs0 hs1
  · obtain ⟨e, he, hy⟩ := List.mem_map.mp (mem_edge hp).2
    have r := h e he
    rw [← hy]
    exact ⟨r.2.2.1, r.2.2.2⟩
  · obtain ⟨e, he, hy⟩ := List.mem_map.mp (mem_edge hp).2
    have r := h e he
    rw [← hy]
    exact ⟨r.1, r.2.1⟩

/-- **Two pieces of two monotone edges do not cross where the two values of the one are no
more than the two values of the other.** With `c` a piece of the upper edge and `d` a piece of
the lower: where neither end of `d` is higher than either end of `c`, no point of `d` is higher
than any point of `c`. -/
theorem apart {upper lower : List Vec} {c d : Cubic} (hc : c ∈ Curve.monotoneX upper)
    (hd : d ∈ Curve.monotoneX lower) (h : max d.p0.y d.p3.y ≤ min c.p0.y c.p3.y) {s t : Rat}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (d.pointAt t).y ≤ (c.pointAt s).y := by
  have wc := Curve.monotoneX_within _ hc hs0 hs1
  have wd := Curve.monotoneX_within _ hd ht0 ht1
  simp only [Box.Contains, Box.ofCorners] at wc wd
  grind

/-- **A layer upon a level baseline never goes under it**, with the monotone curve. Where
every baseline of the band is `k` and no top is under `k`, every point of the lower edge is at
`k` and no point of the upper edge is under `k`. -/
theorem over_level (xs : List Rat) (band : List (Rat × Rat)) {k : Rat}
    (hb : ∀ b ∈ bases band, b = k) (ht : ∀ t ∈ tops band, k ≤ t) {c d : Cubic}
    (hc : c ∈ Curve.monotoneX (edge xs (tops band)))
    (hd : d ∈ Curve.monotoneX (edge xs (bases band))) {s t : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (d.pointAt t).y = k ∧ k ≤ (c.pointAt s).y := by
  have lo := monotoneX_edge_ge xs (bases band) (lo := k) (fun b hb' => by
    rw [hb b hb']
    exact Rat.le_refl) hd ht0 ht1
  have hi := monotoneX_edge_le xs (bases band) (hi := k) (fun b hb' => by
    rw [hb b hb']
    exact Rat.le_refl) hd ht0 ht1
  exact ⟨Rat.le_antisymm hi lo, monotoneX_edge_ge xs (tops band) ht hc hs0 hs1⟩

/-- An entry of the band of a layer upon a level floor is the floor and the floor with a value
of the layer. -/
theorem band_on_level (k : Rat) : ∀ (n : Nat) (layer : List Rat) (e : Rat × Rat),
    e ∈ List.zipWith (fun b v => (b, b + v)) (List.replicate n k) layer →
      ∃ v ∈ layer, e = (k, k + v)
  | 0, _, _, h => by
    rw [List.replicate_zero, List.zipWith_nil_left] at h
    cases h
  | _ + 1, [], _, h => nomatch h
  | n + 1, v :: vs, e, h => by
    have h' : e ∈ (k, k + v) :: List.zipWith (fun b v => (b, b + v)) (List.replicate n k) vs := h
    rcases List.mem_cons.mp h' with rfl | hm
    · exact ⟨v, List.mem_cons_self, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := band_on_level k n vs e hm
      exact ⟨w, List.mem_cons_of_mem v hw, rfl⟩

/-- **A layer of values that are never negative, upon a level floor, never goes under the
floor**, at a beat or between two, with the monotone curve. It is the first layer of a pile
upon zero, and any layer whose floor is one number at every beat. Every point of its lower edge
is at the floor, and no point of its upper edge is under it. -/
theorem first_over_level (xs : List Rat) (n : Nat) (k : Rat) (layer : List Rat)
    (h : ∀ v ∈ layer, 0 ≤ v) {c d : Cubic}
    (hc : c ∈ Curve.monotoneX
      (edge xs (tops (List.zipWith (fun b v => (b, b + v)) (List.replicate n k) layer))))
    (hd : d ∈ Curve.monotoneX
      (edge xs (bases (List.zipWith (fun b v => (b, b + v)) (List.replicate n k) layer))))
    {s t : Rat} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (d.pointAt t).y = k ∧ k ≤ (c.pointAt s).y := by
  refine over_level xs _ (fun b hb => ?_) (fun top htop => ?_) hc hd hs0 hs1 ht0 ht1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    obtain ⟨v, _, rfl⟩ := band_on_level k n layer e he
    rfl
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp htop
    obtain ⟨v, hv, rfl⟩ := band_on_level k n layer e he
    have h0 := h v hv
    show k ≤ k + v
    grind

end Stack

end Whatwg.Svg.Value
