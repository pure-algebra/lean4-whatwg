
/-!
# Whatwg.Svg.Scene.Layers

Owner: the layers of a graph with no cycle (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A picture of a graph that reads from the top says one thing with its heights: what comes before
stands above. A link says how far: its target stands at least `sep` after its source. The
layers are the places that say this and nothing more. Each thing stands as early as the links
into it allow, and a thing with no link into it stands at the start.

lean4-effect4 computes this twice. `Graph.ranks` of its `tools/Tools/View/Graph.lean` counts in
steps of one, and `Flow.assign` of its `tools/Tools/View/Flow.lean` in pixels, where a link
asks for the height of its source, a gap and the room of a frame. d3-sankey's
`computeNodeDepths` (`src/sankey.js` at `bb7233ea0004`) is the count in steps of one, and its
`computeNodeHeights` the same count along the links turned round. Here it is one function, for
links of any type and things of any type with an equality test.

- `Reading ε ν`: how a caller's links are read. Each link of type `ε` has a source and a target
  of type `ν`, and the least distance from the one to the other. A caller gives three functions
  and converts no data. `Reading.turned` reads the same links from their targets back.
- `heights r links start order`: **the layers.** The things of `order` are placed one after
  another, each at the greater of `start` and, for each link into it, the place of the link's
  source and the link's distance. A thing that is not in `order` stands at `start`.
- `Serves r links order`: the order has no thing twice, and the source of each link stands in
  it before the target. `serves` decides it.
- `table`, `read`: the same layers as a list, for a program that runs. `heights` is a function
  that computes a place again each time it is asked.
- `Path r links a b total`: a way along the links from `a` to `b`, with the sum of its
  distances.

What the laws say of a picture whose heights are the layers along an order that serves the
links:

- `heights_meets`: every link is met. Its target stands at least its distance after its source.
  So with distances that are not negative no link goes up, and along a way the distances add
  (`heights_path`).
- `heights_least`: the layers are the least such places. Any places that are at `start` or
  later and meet every link are at the layers or later, thing by thing. This asks nothing of
  the order. So a picture drawn from the layers is as short as its links allow.
- `heights_unique`: two orders that serve the links give the same layers. A caller may take any
  order that `serves` accepts, and a program that changes how it finds its order changes no
  picture.
- `heights_start`, `heights_of_not_mem`: no thing stands before the start, and a thing outside
  the order stands at it.
- `heights_move`: a later start moves every layer by as much.
- `read_table`: the list gives the layers.
- `serves_iff`: the test is exact. `serves_range`: links that go from a lesser number to a
  greater one below `n` are served by the numbers below `n` in their order.

What a caller must supply: an order. This module makes none. A program takes one from its own
structure, as the numbers of things that were made in order, or computes one and lets `serves`
judge it, as lean4-effect4 does with Kahn's algorithm.

What this module does not claim: an order for every graph with no cycle; anything of a graph
with a cycle, which no order serves; that an order which does not serve leaves a link unmet,
since a source that is placed late may stand at the start where it would have stood; a law of
`Reading.turned`, such as that the order turned round serves the links turned round; places
across a layer; that `table` is fast, since it reads a list for each link; that two things
stand in different layers, which is so only for things joined by a way of positive distance.

Every law here depends on `propext` and `Quot.sound` at most. The fact that the numbers below
`n` have no number twice is proved here, since the lemma of Lean's core library for it reaches
`Classical.choice`.
-/

namespace Whatwg.Svg.Scene

/-- **How a caller's links are read**: the source of a link, its target, and the least distance
from the place of the source to the place of the target. -/
structure Layers.Reading (ε ν : Type) where
  /-- The thing that a link comes from. -/
  src : ε → ν
  /-- The thing that a link goes to. -/
  dst : ε → ν
  /-- How far after its source the target stands, at least. -/
  sep : ε → Int

namespace Layers

variable {ε ν : Type}

/-- The same links read the other way: each from its target to its source. The layers of it
count from the last things back, as d3-sankey's `computeNodeHeights` does. -/
def Reading.turned (r : Reading ε ν) : Reading ε ν := ⟨r.dst, r.src, r.sep⟩

section

variable [DecidableEq ν]

/-- **The earliest place of one thing**: `start`, or after the source of each link into it by
the link's distance, whichever is greatest. `y` gives the places of the sources. -/
def relax (r : Reading ε ν) (links : List ε) (y : ν → Int) (start : Int) (v : ν) : Int :=
  links.foldl (fun m e => if r.dst e = v then max m (y (r.src e) + r.sep e) else m) start

/-- Places along an order: each thing in turn takes its earliest place, from the places that
the things before it have. -/
def along (r : Reading ε ν) (links : List ε) (start : Int) : List ν → (ν → Int) → ν → Int
  | [], y => y
  | v :: vs, y => along r links start vs fun k => if k = v then relax r links y start v else y k

/-- **The layers** of the things of `order` under the links: each as early as the links into it
allow, and no earlier than `start`. -/
def heights (r : Reading ε ν) (links : List ε) (start : Int) (order : List ν) : ν → Int :=
  along r links start order fun _ => start

/-- The place of a thing in a list of places, the newest first: `start` where the list has
none. -/
def read (start : Int) : List (ν × Int) → ν → Int
  | [], _ => start
  | (k, x) :: rest, v => if v = k then x else read start rest v

/-- The places along an order as a list, the newest first, after the places of `known`. -/
def tableFrom (r : Reading ε ν) (links : List ε) (start : Int) :
    List ν → List (ν × Int) → List (ν × Int)
  | [], known => known
  | v :: vs, known =>
    tableFrom r links start vs ((v, relax r links (read start known) start v) :: known)

/-- **The layers as a list**, the last thing of the order first. A program computes it once and
reads it with `read`. -/
def table (r : Reading ε ν) (links : List ε) (start : Int) (order : List ν) : List (ν × Int) :=
  tableFrom r links start order []

/-- Whether `a` stands in an order with `b` after it, and `b` not before it. -/
def before : List ν → ν → ν → Bool
  | [], _, _ => false
  | x :: xs, a, b => if x = b then false else if x = a then decide (b ∈ xs) else before xs a b

/-- Whether an order serves the links: no thing twice, and the source of each link before its
target. -/
def serves (r : Reading ε ν) (links : List ε) (order : List ν) : Bool :=
  decide order.Nodup && links.all fun e => before order (r.src e) (r.dst e)

end

/-- **An order serves the links**: it has no thing twice, and the source of each link stands in
it before the target. -/
def Serves (r : Reading ε ν) (links : List ε) (order : List ν) : Prop :=
  order.Nodup ∧ ∀ e ∈ links, ∃ i j : Nat, i < j ∧ order[i]? = some (r.src e) ∧
    order[j]? = some (r.dst e)

/-- **A way along the links** from one thing to another, with the sum of its distances. -/
inductive Path (r : Reading ε ν) (links : List ε) : ν → ν → Int → Prop
  /-- From a thing to itself, with no distance. -/
  | here (v : ν) : Path r links v v 0
  /-- A link, and then a way from its target. -/
  | step {b : ν} {total : Int} (e : ε) : e ∈ links → Path r links (r.dst e) b total →
      Path r links (r.src e) b (r.sep e + total)

/-- One link is a way. -/
theorem Path.link {r : Reading ε ν} {links : List ε} {e : ε} (he : e ∈ links) :
    Path r links (r.src e) (r.dst e) (r.sep e) := by
  have h := Path.step e he (Path.here (r.dst e))
  rw [Int.add_zero] at h
  exact h

/-- Two ways in a row are a way, and their distances add. -/
theorem Path.trans {r : Reading ε ν} {links : List ε} {a b c : ν} {s t : Int}
    (p : Path r links a b s) (q : Path r links b c t) : Path r links a c (s + t) := by
  induction p with
  | here v =>
    rw [Int.zero_add]
    exact q
  | step e he _ ih =>
    rw [Int.add_assoc]
    exact Path.step e he (ih q)

/-- A way along some links is a way along more. -/
theorem Path.mono {r : Reading ε ν} {links more : List ε} (h : ∀ e ∈ links, e ∈ more) {a b : ν}
    {s : Int} (p : Path r links a b s) : Path r more a b s := by
  induction p with
  | here v => exact Path.here v
  | step e he _ ih => exact Path.step e (h e he) ih

section

variable [DecidableEq ν]

/-! ## The earliest place of one thing -/

/-- The fold of `relax` never goes below where it began. -/
private theorem le_foldl (r : Reading ε ν) (y : ν → Int) (v : ν) : ∀ (l : List ε) (m : Int),
    m ≤ l.foldl (fun m e => if r.dst e = v then max m (y (r.src e) + r.sep e) else m) m
  | [], _ => Int.le_refl _
  | e :: l, m => by
    rw [List.foldl_cons]
    refine Int.le_trans ?_ (le_foldl r y v l _)
    by_cases hv : r.dst e = v
    · rw [if_pos hv]
      exact Int.le_max_left _ _
    · rw [if_neg hv]
      exact Int.le_refl _

/-- The fold of `relax` is at least the term of each link into the thing. -/
private theorem term_le_foldl (r : Reading ε ν) (y : ν → Int) {v : ν} {e : ε}
    (hv : r.dst e = v) : ∀ (l : List ε) (m : Int), e ∈ l →
    y (r.src e) + r.sep e ≤
      l.foldl (fun m e => if r.dst e = v then max m (y (r.src e) + r.sep e) else m) m
  | [], _, he => nomatch he
  | d :: l, m, he => by
    rw [List.foldl_cons]
    cases List.mem_cons.mp he with
    | inl hd =>
      refine Int.le_trans ?_ (le_foldl r y v l _)
      rw [← hd, if_pos hv]
      exact Int.le_max_right _ _
    | inr hl => exact term_le_foldl r y hv l _ hl

/-- The fold of `relax` is no more than a bound of where it began and of each term. -/
private theorem foldl_le (r : Reading ε ν) (y : ν → Int) (v : ν) (b : Int) :
    ∀ (l : List ε) (m : Int), m ≤ b →
      (∀ e ∈ l, r.dst e = v → y (r.src e) + r.sep e ≤ b) →
      l.foldl (fun m e => if r.dst e = v then max m (y (r.src e) + r.sep e) else m) m ≤ b
  | [], _, hm, _ => hm
  | e :: l, m, hm, h => by
    rw [List.foldl_cons]
    refine foldl_le r y v b l _ ?_ fun d hd => h d (List.mem_cons_of_mem e hd)
    by_cases hv : r.dst e = v
    · rw [if_pos hv]
      have ht := h e List.mem_cons_self hv
      omega
    · rw [if_neg hv]
      exact hm

/-- The fold of `relax` from places that are all `d` later, begun `d` later, ends `d` later. -/
private theorem foldl_move (r : Reading ε ν) (y y' : ν → Int) (d : Int) (v : ν)
    (hy : ∀ k, y' k = y k + d) : ∀ (l : List ε) (m : Int),
    l.foldl (fun m e => if r.dst e = v then max m (y' (r.src e) + r.sep e) else m) (m + d) =
      l.foldl (fun m e => if r.dst e = v then max m (y (r.src e) + r.sep e) else m) m + d
  | [], _ => rfl
  | e :: l, m => by
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hv : r.dst e = v
    · rw [if_pos hv, if_pos hv, hy (r.src e)]
      have key : max (m + d) (y (r.src e) + d + r.sep e) = max m (y (r.src e) + r.sep e) + d := by
        omega
      rw [key]
      exact foldl_move r y y' d v hy l _
    · rw [if_neg hv, if_neg hv]
      exact foldl_move r y y' d v hy l m

/-- No thing is placed before the start. -/
theorem start_le_relax (r : Reading ε ν) (links : List ε) (y : ν → Int) (start : Int) (v : ν) :
    start ≤ relax r links y start v := le_foldl r y v links start

/-- A thing is placed after the source of each link into it, by the link's distance. -/
theorem term_le_relax (r : Reading ε ν) {links : List ε} (y : ν → Int) (start : Int) {e : ε}
    (he : e ∈ links) : y (r.src e) + r.sep e ≤ relax r links y start (r.dst e) :=
  term_le_foldl r y rfl links start he

/-- A thing is placed no later than any place that is at the start or later and after the
source of each link into it. -/
theorem relax_le (r : Reading ε ν) {links : List ε} {y : ν → Int} {start : Int} {v : ν} {b : Int}
    (hs : start ≤ b) (h : ∀ e ∈ links, r.dst e = v → y (r.src e) + r.sep e ≤ b) :
    relax r links y start v ≤ b := foldl_le r y v b links start hs h

/-! ## Places along an order -/

theorem along_nil (r : Reading ε ν) (links : List ε) (start : Int) (y : ν → Int) :
    along r links start [] y = y := rfl

theorem along_cons (r : Reading ε ν) (links : List ε) (start : Int) (v : ν) (vs : List ν)
    (y : ν → Int) : along r links start (v :: vs) y =
      along r links start vs fun k => if k = v then relax r links y start v else y k := rfl

/-- A thing that is not in the order keeps its place. -/
theorem along_of_not_mem (r : Reading ε ν) (links : List ε) (start : Int) :
    ∀ (vs : List ν) (y : ν → Int) (v : ν), v ∉ vs → along r links start vs y v = y v
  | [], _, _, _ => rfl
  | w :: ws, y, v, hv => by
    have hw : v ≠ w := fun e => hv (e ▸ List.mem_cons_self)
    have hws : v ∉ ws := fun h => hv (List.mem_cons_of_mem w h)
    rw [along_cons, along_of_not_mem r links start ws _ v hws]
    exact if_neg hw

/-- Two orders in a row: the places along the first, and then along the second. -/
theorem along_append (r : Reading ε ν) (links : List ε) (start : Int) :
    ∀ (as bs : List ν) (y : ν → Int),
      along r links start (as ++ bs) y = along r links start bs (along r links start as y)
  | [], _, _ => rfl
  | _ :: as, bs, _ => along_append r links start as bs _

/-- Places that are all at the start or later stay so along an order. -/
private theorem start_le_along (r : Reading ε ν) (links : List ε) (start : Int) :
    ∀ (vs : List ν) (y : ν → Int), (∀ k, start ≤ y k) → ∀ k, start ≤ along r links start vs y k
  | [], _, hy, k => hy k
  | v :: vs, y, hy, k => by
    rw [along_cons]
    refine start_le_along r links start vs _ (fun j => ?_) k
    by_cases hj : j = v
    · rw [if_pos hj]
      exact start_le_relax r links y start v
    · rw [if_neg hj]
      exact hy j

/-- Places that are all no later than places that meet every link stay so along an order. -/
private theorem along_le (r : Reading ε ν) (links : List ε) (start : Int) (z : ν → Int)
    (hs : ∀ k, start ≤ z k) (hz : ∀ e ∈ links, z (r.src e) + r.sep e ≤ z (r.dst e)) :
    ∀ (vs : List ν) (y : ν → Int), (∀ k, y k ≤ z k) → ∀ k, along r links start vs y k ≤ z k
  | [], _, hy, k => hy k
  | v :: vs, y, hy, k => by
    rw [along_cons]
    refine along_le r links start z hs hz vs _ (fun j => ?_) k
    by_cases hj : j = v
    · rw [if_pos hj, hj]
      refine relax_le r (hs v) fun e he hd => ?_
      have h1 := hy (r.src e)
      have h2 := hz e he
      rw [hd] at h2
      omega
    · rw [if_neg hj]
      exact hy j

/-- Places that are all `d` later, along an order from a start `d` later, are all `d` later. -/
private theorem along_move (r : Reading ε ν) (links : List ε) (start d : Int) :
    ∀ (vs : List ν) (y y' : ν → Int), (∀ k, y' k = y k + d) →
      ∀ k, along r links (start + d) vs y' k = along r links start vs y k + d
  | [], _, _, hy, k => hy k
  | v :: vs, y, y', hy, k => by
    rw [along_cons, along_cons]
    refine along_move r links start d vs _ _ (fun j => ?_) k
    by_cases hj : j = v
    · rw [if_pos hj, if_pos hj]
      exact foldl_move r y y' d v hy links start
    · rw [if_neg hj, if_neg hj]
      exact hy j

/-! ## The layers -/

/-- **No thing stands before the start.** -/
theorem heights_start (r : Reading ε ν) (links : List ε) (start : Int) (order : List ν) (v : ν) :
    start ≤ heights r links start order v :=
  start_le_along r links start order _ (fun _ => Int.le_refl start) v

/-- A thing that is not in the order stands at the start. -/
theorem heights_of_not_mem (r : Reading ε ν) (links : List ε) (start : Int) {order : List ν}
    {v : ν} (h : v ∉ order) : heights r links start order v = start :=
  along_of_not_mem r links start order _ v h

/-- **Every link is met**: along an order that serves the links, the target of each link stands
at least the link's distance after its source. -/
theorem heights_meets {r : Reading ε ν} {links : List ε} {order : List ν}
    (h : Serves r links order) (start : Int) {e : ε} (he : e ∈ links) :
    heights r links start order (r.src e) + r.sep e ≤ heights r links start order (r.dst e) := by
  obtain ⟨i, j, hij, hi, hj⟩ := h.2 e he
  have hjl : j < order.length := (List.getElem?_eq_some_iff.mp hj).1
  have hsplit : order = order.take j ++ r.dst e :: order.drop (j + 1) := by
    have h1 := (List.take_append_drop j order).symm
    rw [List.drop_eq_getElem_cons hjl, (List.getElem?_eq_some_iff.mp hj).2] at h1
    exact h1
  have hs : r.src e ∈ order.take j := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_take, if_pos hij, hi]
  have nd := h.1
  rw [hsplit] at nd
  have nd' := List.nodup_append.mp nd
  have hdr : r.dst e ∉ order.drop (j + 1) := (List.nodup_cons.mp nd'.2.1).1
  have hne : r.src e ≠ r.dst e := fun heq => nd'.2.2 _ hs _ List.mem_cons_self heq
  have hsr : r.src e ∉ order.drop (j + 1) := fun hm =>
    nd'.2.2 _ hs _ (List.mem_cons_of_mem _ hm) rfl
  have e1 : heights r links start order (r.src e) =
      along r links start (order.take j) (fun _ => start) (r.src e) := by
    show along r links start order (fun _ => start) (r.src e) = _
    rw [hsplit, along_append, along_cons, along_of_not_mem r links start _ _ _ hsr,
      ← hsplit]
    exact if_neg hne
  have e2 : heights r links start order (r.dst e) =
      relax r links (along r links start (order.take j) fun _ => start) start (r.dst e) := by
    show along r links start order (fun _ => start) (r.dst e) = _
    rw [hsplit, along_append, along_cons, along_of_not_mem r links start _ _ _ hdr,
      ← hsplit]
    exact if_pos rfl
  rw [e1, e2]
  exact term_le_relax r _ start he

/-- **The layers are the least places that meet the links.** Places that are all at the start
or later, and that meet every link, are at the layers or later. No premise is on the order. -/
theorem heights_least (r : Reading ε ν) (links : List ε) (start : Int) (order : List ν)
    {z : ν → Int} (hs : ∀ k, start ≤ z k)
    (hz : ∀ e ∈ links, z (r.src e) + r.sep e ≤ z (r.dst e)) (v : ν) :
    heights r links start order v ≤ z v :=
  along_le r links start z hs hz order _ hs v

/-- **The layers do not depend on the order**: two orders that serve the links give every
thing the same place. -/
theorem heights_unique {r : Reading ε ν} {links : List ε} {order order' : List ν}
    (h : Serves r links order) (h' : Serves r links order') (start : Int) :
    heights r links start order = heights r links start order' :=
  funext fun v => Int.le_antisymm
    (heights_least r links start order (heights_start r links start order')
      (fun _ he => heights_meets h' start he) v)
    (heights_least r links start order' (heights_start r links start order)
      (fun _ he => heights_meets h start he) v)

/-- **A later start moves every layer by as much.** -/
theorem heights_move (r : Reading ε ν) (links : List ε) (start d : Int) (order : List ν) (v : ν) :
    heights r links (start + d) order v = heights r links start order v + d :=
  along_move r links start d order _ _ (fun _ => rfl) v

/-- **Along a way the distances add**: the end of a way stands at least the sum of its
distances after its beginning. -/
theorem heights_path {r : Reading ε ν} {links : List ε} {order : List ν}
    (h : Serves r links order) (start : Int) {a b : ν} {total : Int}
    (p : Path r links a b total) :
    heights r links start order a + total ≤ heights r links start order b := by
  induction p with
  | here v =>
    rw [Int.add_zero]
    exact Int.le_refl _
  | step e he _ ih =>
    have h1 := heights_meets h start he
    omega

/-- The end of a way stands at least the sum of its distances after the start. -/
theorem heights_path_start {r : Reading ε ν} {links : List ε} {order : List ν}
    (h : Serves r links order) (start : Int) {a b : ν} {total : Int}
    (p : Path r links a b total) : start + total ≤ heights r links start order b := by
  have h1 := heights_path h start p
  have h2 := heights_start r links start order a
  omega

/-! ## The layers as a list -/

/-- **The list gives the places**: reading it is the places along the order, from the places of
the list it began with. -/
theorem read_tableFrom (r : Reading ε ν) (links : List ε) (start : Int) :
    ∀ (vs : List ν) (known : List (ν × Int)) (k : ν),
      read start (tableFrom r links start vs known) k =
        along r links start vs (read start known) k
  | [], _, _ => rfl
  | v :: vs, known, k => by
    rw [tableFrom, read_tableFrom r links start vs _ k, along_cons]
    rfl

/-- **The list gives the layers.** -/
theorem read_table (r : Reading ε ν) (links : List ε) (start : Int) (order : List ν) (k : ν) :
    read start (table r links start order) k = heights r links start order k :=
  read_tableFrom r links start order [] k

/-! ## Orders that serve -/

/-- Where `before` answers yes, the first thing stands at a place before a place of the
second. -/
private theorem before_places : ∀ (order : List ν) (a b : ν), before order a b = true →
    ∃ i j : Nat, i < j ∧ order[i]? = some a ∧ order[j]? = some b
  | [], _, _, h => nomatch h
  | x :: xs, a, b, h => by
    rw [before] at h
    by_cases hb : x = b
    · rw [if_pos hb] at h
      exact nomatch h
    · rw [if_neg hb] at h
      by_cases ha : x = a
      · rw [if_pos ha] at h
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (of_decide_eq_true h)
        exact ⟨0, j + 1, Nat.succ_pos j, congrArg some ha, hj⟩
      · rw [if_neg ha] at h
        obtain ⟨i, j, hij, hi, hj⟩ := before_places xs a b h
        exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, hi, hj⟩

/-- In an order with no thing twice, a thing at a place before a place of another is `before`
it. -/
private theorem before_of_places : ∀ (order : List ν) (a b : ν), order.Nodup →
    ∀ i j : Nat, i < j → order[i]? = some a → order[j]? = some b → before order a b = true
  | [], _, _, _, _, _, _, hi, _ => nomatch hi
  | x :: xs, a, b, nd, i, j, hij, hi, hj => by
    have nd' : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp nd
    cases j with
    | zero => exact nomatch hij
    | succ j =>
      have hbm : b ∈ xs := List.mem_of_getElem? hj
      have hxb : x ≠ b := fun e => nd'.1 (e ▸ hbm)
      rw [before, if_neg hxb]
      cases i with
      | zero =>
        have hxa : x = a := Option.some.inj hi
        rw [if_pos hxa]
        exact decide_eq_true hbm
      | succ i =>
        have ham : a ∈ xs := List.mem_of_getElem? hi
        have hxa : x ≠ a := fun e => nd'.1 (e ▸ ham)
        rw [if_neg hxa]
        exact before_of_places xs a b nd'.2 i j (Nat.lt_of_succ_lt_succ hij) hi hj

/-- **The test is exact**: `serves` answers yes exactly for an order that serves the links. -/
theorem serves_iff (r : Reading ε ν) (links : List ε) (order : List ν) :
    serves r links order = true ↔ Serves r links order := by
  rw [serves, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  constructor
  · intro h
    exact ⟨h.1, fun e he => before_places order _ _ (h.2 e he)⟩
  · intro h
    refine ⟨h.1, fun e he => ?_⟩
    obtain ⟨i, j, hij, hi, hj⟩ := h.2 e he
    exact before_of_places order _ _ h.1 i j hij hi hj

/-- Whether an order serves the links is decided by `serves`. -/
instance (r : Reading ε ν) (links : List ε) (order : List ν) : Decidable (Serves r links order) :=
  decidable_of_iff _ (serves_iff r links order)

end

/-- An order that serves some links serves fewer. -/
theorem Serves.mono {r : Reading ε ν} {links fewer : List ε} {order : List ν}
    (h : Serves r links order) (hs : ∀ e ∈ fewer, e ∈ links) : Serves r fewer order :=
  ⟨h.1, fun e he => h.2 e (hs e he)⟩

/-- The numbers below `n` in their order have no number twice. -/
private theorem nodup_range : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨nodup_range n, List.pairwise_singleton _ _, fun a ha b hb e => ?_⟩
    have h1 : a < n := List.mem_range.mp ha
    have h2 : b = n := List.mem_singleton.mp hb
    omega

/-- **Links that go forward are served by the numbers in their order**: where the things are
the numbers below `n` and each link goes from a lesser number to a greater one. A program whose
things were made in order needs no other order. -/
theorem serves_range {r : Reading ε Nat} {links : List ε} {n : Nat}
    (h : ∀ e ∈ links, r.src e < r.dst e ∧ r.dst e < n) : Serves r links (List.range n) := by
  refine ⟨nodup_range n, fun e he => ⟨r.src e, r.dst e, (h e he).1, ?_, ?_⟩⟩
  · exact List.getElem?_range (Nat.lt_trans (h e he).1 (h e he).2)
  · exact List.getElem?_range (h e he).2

end Layers

end Whatwg.Svg.Scene
