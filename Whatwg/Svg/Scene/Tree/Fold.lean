import Whatwg.Svg.Scene.Tree

/-!
# Whatwg.Svg.Scene.Tree.Fold

Owner: a tree, mapped and folded (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Tree.lean` places a tree. A program that draws one reads more of it than
places: the text of each node, its size, what it leaves for the next frame. Each of those is a
fold, and a program that has several wants to know that they agree. lean4-effect4 states the
three laws of a fold for its own program family (`tools/Tools/View/Algebra.lean`: `cata_fusion`,
`cata_prod`, `cata_keeps`). Here they are laws of `Tree`.

- `Tree.map f t`: the same tree of other values.
- `Tree.fold f t`: **the fold.** `f` gives the result at a node from the node's value and the
  results at its children, in order.
- `Tree.both f g`: two folds side by side, as one fold of pairs.
- `Tree.scan f t`: the tree with each node's result beside its value. This is what d3's
  `eachAfter` does where its callback stores a value on the node, as `sum` and `count` do.
- `Tree.height t`: the number of rows below the root.

What the laws say:

- **Fusion** (`fold_fusion`): a function that commutes with each step of a fold commutes with
  the fold. A reading that is a function of another reading needs no second walk, and no proof
  by induction: the caller checks one node.
- **Two folds are one** (`fold_both`): the fold of two steps side by side is the pair of the two
  folds.
- **What each step keeps, the fold has** (`fold_keeps`): a property that holds at a node
  whenever it holds at its children holds of the fold of every tree.
- **`map` is a functor** (`map_id`, `map_map`), and a fold after a `map` is one fold
  (`fold_map`). `map` is itself a fold (`map_eq_fold`), and the fold with `Tree.node` as its
  step gives the tree back (`fold_node_id`).
- **The readings of `Tree.lean` are folds** (`leaves_eq_fold`, `values_eq_fold`), so fusion
  speaks of them.
- **A placement reads no value** (`spans_map`): the spans of a mapped tree are the spans of the
  tree, with the values mapped. So a tree is placed once, and its picture is relabelled,
  restyled or keyed afterwards. The same holds of the leaves, the values and the links
  (`leaves_map`, `values_map`, `links_map`).
- **`scan` keeps the tree and holds the fold** (`map_fst_scan`, `value_scan`).
- **The picture of a tree has `height + 1` rows** (`spans_depth_le`): no node stands more than
  the height below the root. With `spans_within` of `Tree.lean` this is the room of the
  picture: `leaves t` columns by `height t + 1` rows.

**Beside d3.** `Tree.spans` is the placement of a dendrogram, as d3's `cluster` is
(`d3-hierarchy/src/cluster.js` at the commit `c4ae7066d5a5`), and the two differ in three ways.

1. A parent in d3 stands at the mean of its children (`meanX`). Here it stands over the middle
   of its leaves (`Span.middle2`). Take a node with two leaf children and then a child of three
   leaves. d3 has the leaves at `0`, `1`, `3`, `4`, `5`, the last child at `4`, and the node at
   `5/3`, the mean of `0`, `1` and `4`; the middle of its leaves is `5/2` there. Here the leaves
   are the columns `0` to `4`, and the node stands over the column `2`.
2. Two neighbouring leaves in d3 are `1` apart under one parent and `2` apart under two
   (`defaultSeparation`), as the leaves at `1` and `3` above. Here every leaf has one column.
3. A node's row in d3 counts from the leaves (`maxY`: a leaf is at `0`, a parent one above its
   highest child), so all leaves stand in one row. Here a node's row is its depth from the
   root, and leaves stand in several rows. `Tree.height` is d3's count for the root.

d3 then scales both axes to a size, in fractions. This layer counts in whole numbers and does
not. The numbers said of d3 are computed by hand from its source: nothing here runs d3.
`WhatwgTest/Svg/UseFold.lean` has the same tree placed here. `Tree.spans` is not changed by
this module.

What this module does not claim: a fold that reads the subtree as well as its results; a fold
with a state that goes down, which `Tree.spans` is (its depth and its column); anything of d3's
`tree` (Reingold and Tilford).

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Tree

variable {α β γ : Type}

mutual

/-- **The same tree of other values.** -/
def map (f : α → β) : Tree α → Tree β
  | .node v cs => .node (f v) (mapAll f cs)

/-- A list of trees, each mapped. -/
def mapAll (f : α → β) : List (Tree α) → List (Tree β)
  | [] => []
  | t :: ts => map f t :: mapAll f ts

end

mutual

/-- **The fold of a tree.** `f` gives the result at a node from its value and the results at
its children, in order. -/
def fold (f : α → List β → β) : Tree α → β
  | .node v cs => f v (foldAll f cs)

/-- The folds of a list of trees. -/
def foldAll (f : α → List β → β) : List (Tree α) → List β
  | [] => []
  | t :: ts => fold f t :: foldAll f ts

end

/-- **Two folds side by side**: the step that reads each of the two results at the children. -/
def both (f : α → List β → β) (g : α → List γ → γ) : α → List (β × γ) → β × γ :=
  fun v rs => (f v (rs.map Prod.fst), g v (rs.map Prod.snd))

/-- **The tree with each node's result beside its value**: the fold of the subtree under each
node, kept at the node. -/
def scan (f : α → List β → β) : Tree α → Tree (α × β) :=
  fold fun v cs => .node (v, f v (cs.map fun c => (value c).2)) cs

/-- **The number of rows below the root**: none for a leaf, and one more than the highest child
for a node. -/
def height : Tree α → Nat :=
  fold fun _ rs => rs.foldr (fun r m => max (r + 1) m) 0

/-! ## The two lists -/

/-- A list of trees mapped is each tree mapped. -/
theorem mapAll_eq (f : α → β) : ∀ ts : List (Tree α), mapAll f ts = ts.map (map f)
  | [] => rfl
  | t :: ts => by rw [mapAll, List.map_cons, mapAll_eq f ts]

/-- The folds of a list of trees are the fold of each. -/
theorem foldAll_eq (f : α → List β → β) : ∀ ts : List (Tree α), foldAll f ts = ts.map (fold f)
  | [] => rfl
  | t :: ts => by rw [foldAll, List.map_cons, foldAll_eq f ts]

/-- A node mapped: its value mapped, over its children mapped. -/
theorem map_node (f : α → β) (v : α) (cs : List (Tree α)) :
    map f (.node v cs) = .node (f v) (cs.map (map f)) := by
  rw [map, mapAll_eq]

/-- **The fold at a node** is the step at its value and the folds of its children. -/
theorem fold_node (f : α → List β → β) (v : α) (cs : List (Tree α)) :
    fold f (.node v cs) = f v (cs.map (fold f)) := by
  rw [fold, foldAll_eq]

/-- The value at the root of a mapped tree. -/
theorem value_map (f : α → β) : ∀ t : Tree α, value (map f t) = f (value t)
  | .node _ _ => by
    rw [map]
    rfl

/-! ## The three laws of a fold -/

mutual

/-- **Fusion.** A function that commutes with each step commutes with the fold: where `φ` of a
step of `f` is the step of `g` at `φ` of each result, `φ` of the fold of `f` is the fold of
`g`. -/
theorem fold_fusion {f : α → List β → β} {g : α → List γ → γ} {φ : β → γ}
    (h : ∀ v rs, φ (f v rs) = g v (rs.map φ)) : ∀ t : Tree α, φ (fold f t) = fold g t
  | .node v cs => by rw [fold, fold, h, foldAll_fusion h cs]

/-- The same for a list of trees. -/
theorem foldAll_fusion {f : α → List β → β} {g : α → List γ → γ} {φ : β → γ}
    (h : ∀ v rs, φ (f v rs) = g v (rs.map φ)) : ∀ ts : List (Tree α),
    (foldAll f ts).map φ = foldAll g ts
  | [] => by rw [foldAll, foldAll, List.map_nil]
  | t :: ts => by rw [foldAll, foldAll, List.map_cons, fold_fusion h t, foldAll_fusion h ts]

end

/-- **Two folds are one.** The fold of two steps side by side is the pair of the two folds. So
several readings of one tree come from one walk, and each is stated alone. -/
theorem fold_both (f : α → List β → β) (g : α → List γ → γ) (t : Tree α) :
    fold (both f g) t = (fold f t, fold g t) :=
  Prod.ext (fold_fusion (g := f) (φ := Prod.fst) (fun _ _ => rfl) t)
    (fold_fusion (g := g) (φ := Prod.snd) (fun _ _ => rfl) t)

mutual

/-- **What each step keeps, the fold has.** A property that holds of the step at a node
whenever it holds of every result at its children holds of the fold of every tree. -/
theorem fold_keeps {f : α → List β → β} {P : β → Prop}
    (h : ∀ v rs, (∀ r ∈ rs, P r) → P (f v rs)) : ∀ t : Tree α, P (fold f t)
  | .node v cs => by
    rw [fold]
    exact h v _ (foldAll_keeps h cs)

/-- The same for a list of trees. -/
theorem foldAll_keeps {f : α → List β → β} {P : β → Prop}
    (h : ∀ v rs, (∀ r ∈ rs, P r) → P (f v rs)) : ∀ (ts : List (Tree α)) (r : β),
    r ∈ foldAll f ts → P r
  | [], _, hr => by
    rw [foldAll] at hr
    cases hr
  | t :: ts, r, hr => by
    rw [foldAll] at hr
    cases hr with
    | head => exact fold_keeps h t
    | tail _ hm => exact foldAll_keeps h ts r hm

end

/-! ## `map` -/

mutual

/-- **The fold with `Tree.node` as its step gives the tree back.** -/
theorem fold_node_id : ∀ t : Tree α, fold (fun v cs => Tree.node v cs) t = t
  | .node v cs => by rw [fold, foldAll_node_id cs]

/-- The same for a list of trees. -/
theorem foldAll_node_id : ∀ ts : List (Tree α), foldAll (fun v cs => Tree.node v cs) ts = ts
  | [] => by rw [foldAll]
  | t :: ts => by rw [foldAll, fold_node_id t, foldAll_node_id ts]

end

mutual

/-- **`map` is a fold**: the step that maps the value and keeps the children. -/
theorem map_eq_fold (f : α → β) : ∀ t : Tree α, map f t = fold (fun v cs => Tree.node (f v) cs) t
  | .node v cs => by rw [map, fold, mapAll_eq_foldAll f cs]

/-- The same for a list of trees. -/
theorem mapAll_eq_foldAll (f : α → β) : ∀ ts : List (Tree α),
    mapAll f ts = foldAll (fun v cs => Tree.node (f v) cs) ts
  | [] => by rw [mapAll, foldAll]
  | t :: ts => by rw [mapAll, foldAll, map_eq_fold f t, mapAll_eq_foldAll f ts]

end

/-- **A fold after a `map` is one fold**: the step reads the mapped value. -/
theorem fold_map (g : β → List γ → γ) (f : α → β) (t : Tree α) :
    fold g (map f t) = fold (fun v rs => g (f v) rs) t := by
  rw [map_eq_fold]
  exact fold_fusion (f := fun v cs => Tree.node (f v) cs) (g := fun v rs => g (f v) rs)
    (φ := fold g) (fun v rs => fold_node g (f v) rs) t

/-- A tree mapped by the identity is the tree. -/
theorem map_id (t : Tree α) : map (fun a => a) t = t :=
  (map_eq_fold (fun a => a) t).trans (fold_node_id t)

/-- Two maps in a row are the map of the two functions in a row. -/
theorem map_map (g : β → γ) (f : α → β) (t : Tree α) :
    map g (map f t) = map (fun a => g (f a)) t := by
  rw [map_eq_fold f t, map_eq_fold (fun a => g (f a)) t]
  exact fold_fusion (f := fun v cs => Tree.node (f v) cs)
    (g := fun v cs => Tree.node (g (f v)) cs) (φ := map g) (fun v rs => map_node g (f v) rs) t

/-! ## The readings of a tree are folds -/

mutual

/-- **The number of leaves is a fold**: one for a node with no child, and else the sum of its
children's. -/
theorem leaves_eq_fold : ∀ t : Tree α, leaves t = fold (fun _ rs => max 1 rs.sum) t
  | .node v cs => by rw [leaves, fold, leavesAll_eq_sum cs]

/-- The same for a list of trees. -/
theorem leavesAll_eq_sum : ∀ ts : List (Tree α),
    leavesAll ts = (foldAll (fun _ rs => max 1 rs.sum) ts).sum
  | [] => by rw [leavesAll, foldAll, List.sum_nil]
  | t :: ts => by
    rw [leavesAll, foldAll, List.sum_cons, leaves_eq_fold t, leavesAll_eq_sum ts]

end

mutual

/-- **The values of a tree are a fold**: the value of a node, and then the values under each
child. -/
theorem values_eq_fold : ∀ t : Tree α, values t = fold (fun v rs => v :: rs.flatten) t
  | .node v cs => by rw [values, fold, valuesAll_eq_flatten cs]

/-- The same for a list of trees. -/
theorem valuesAll_eq_flatten : ∀ ts : List (Tree α),
    valuesAll ts = (foldAll (fun v rs => v :: rs.flatten) ts).flatten
  | [] => by rw [valuesAll, foldAll, List.flatten_nil]
  | t :: ts => by
    rw [valuesAll, foldAll, List.flatten_cons, values_eq_fold t, valuesAll_eq_flatten ts]

end

/-! ## A placement reads no value -/

/-- A mapped tree has as many leaves. -/
theorem leaves_map (f : α → β) (t : Tree α) : leaves (map f t) = leaves t := by
  rw [leaves_eq_fold, leaves_eq_fold, fold_map]

/-- A mapped list of trees has as many leaves. -/
theorem leavesAll_mapAll (f : α → β) : ∀ ts : List (Tree α), leavesAll (mapAll f ts) = leavesAll ts
  | [] => by rw [mapAll, leavesAll, leavesAll]
  | t :: ts => by rw [mapAll, leavesAll, leavesAll, leaves_map f t, leavesAll_mapAll f ts]

mutual

/-- **A placement reads no value.** The spans of a mapped tree are the spans of the tree, with
the values mapped: each node keeps its columns and its row. So a tree is placed once, and its
picture is relabelled, restyled or keyed afterwards. -/
theorem spans_map (f : α → β) (depth start : Nat) : ∀ t : Tree α,
    spans depth start (map f t) = (spans depth start t).map fun p => (f p.1, p.2)
  | .node v cs => by
    rw [map, spans, spans, List.map_cons, leavesAll_mapAll f cs,
      spansAll_mapAll f (depth + 1) start cs]

/-- The same for a list of trees. -/
theorem spansAll_mapAll (f : α → β) (depth start : Nat) : ∀ ts : List (Tree α),
    spansAll depth start (mapAll f ts) = (spansAll depth start ts).map fun p => (f p.1, p.2)
  | [] => by rw [mapAll, spansAll, spansAll, List.map_nil]
  | t :: ts => by
    rw [mapAll, spansAll, spansAll, List.map_append, leaves_map f t, spans_map f depth start t,
      spansAll_mapAll f depth (start + leaves t) ts]

end

mutual

/-- The values of a mapped tree are the values of the tree, mapped. -/
theorem values_map (f : α → β) : ∀ t : Tree α, values (map f t) = (values t).map f
  | .node v cs => by rw [map, values, values, List.map_cons, valuesAll_mapAll f cs]

/-- The same for a list of trees. -/
theorem valuesAll_mapAll (f : α → β) : ∀ ts : List (Tree α),
    valuesAll (mapAll f ts) = (valuesAll ts).map f
  | [] => by rw [mapAll, valuesAll, valuesAll, List.map_nil]
  | t :: ts => by
    rw [mapAll, valuesAll, valuesAll, List.map_append, values_map f t, valuesAll_mapAll f ts]

end

mutual

/-- The links of a mapped tree are the links of the tree, with both ends mapped. -/
theorem links_map (f : α → β) : ∀ t : Tree α,
    links (map f t) = (links t).map fun p => (f p.1, f p.2)
  | .node v cs => by rw [map, links, links, linksAll_mapAll f v cs]

/-- The same for a list of trees under one parent. -/
theorem linksAll_mapAll (f : α → β) (parent : α) : ∀ ts : List (Tree α),
    linksAll (f parent) (mapAll f ts) = (linksAll parent ts).map fun p => (f p.1, f p.2)
  | [] => by rw [mapAll, linksAll, linksAll, List.map_nil]
  | t :: ts => by
    rw [mapAll, linksAll, linksAll, List.map_cons, List.map_append, value_map f t, links_map f t,
      linksAll_mapAll f parent ts]

end

/-! ## Each node with its result -/

/-- The step of `scan`: a node of its value with its result, over its scanned children. -/
private def scanStep (f : α → List β → β) : α → List (Tree (α × β)) → Tree (α × β) :=
  fun v cs => .node (v, f v (cs.map fun c => (value c).2)) cs

/-- `scan` is the fold of its step. -/
private theorem scan_eq (f : α → List β → β) (t : Tree α) : scan f t = fold (scanStep f) t := rfl

/-- **`scan` keeps the tree**: without the results it is the tree. -/
theorem map_fst_scan (f : α → List β → β) (t : Tree α) : map Prod.fst (scan f t) = t := by
  rw [scan_eq]
  exact (fold_fusion (f := scanStep f) (g := fun v cs => Tree.node v cs) (φ := map Prod.fst)
    (fun v cs => map_node Prod.fst (v, f v (cs.map fun c => (value c).2)) cs) t).trans
      (fold_node_id t)

/-- **`scan` holds the fold**: the result at the root is the fold of the tree. With
`scan_node` it is the fold of each subtree at its node. -/
theorem value_scan (f : α → List β → β) (t : Tree α) : (value (scan f t)).2 = fold f t := by
  rw [scan_eq]
  exact fold_fusion (f := scanStep f) (g := f) (φ := fun c : Tree (α × β) => (value c).2)
    (fun _ _ => rfl) t

/-- The value at the root of a scanned tree is the value at the root. -/
theorem value_scan_fst (f : α → List β → β) (t : Tree α) : (value (scan f t)).1 = value t := by
  have h := congrArg value (map_fst_scan f t)
  rw [value_map] at h
  exact h

/-- **A node scanned** is its value with the fold of the node, over its children scanned. -/
theorem scan_node (f : α → List β → β) (v : α) (cs : List (Tree α)) :
    scan f (.node v cs) = .node (v, fold f (.node v cs)) (cs.map (scan f)) := by
  have e : (cs.map (scan f)).map (fun c => (value c).2) = cs.map (fold f) := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => value_scan f c
  have h : scan f (.node v cs) =
      .node (v, f v ((cs.map (scan f)).map fun c => (value c).2)) (cs.map (scan f)) :=
    fold_node (scanStep f) v cs
  rw [fold_node f v cs, ← e]
  exact h

/-! ## The rows of a picture -/

/-- The height of a node: one more than the highest child, and none with no child. -/
theorem height_node (v : α) (cs : List (Tree α)) :
    height (.node v cs) = (cs.map height).foldr (fun r m => max (r + 1) m) 0 :=
  fold_node _ v cs

mutual

/-- **No node stands more than the height below the root.** With `spans_within` this is the
room of the picture of a tree: `leaves t` columns by `height t + 1` rows. -/
theorem spans_depth_le (depth start : Nat) : ∀ (t : Tree α) (p : α × Span),
    p ∈ spans depth start t → p.2.depth ≤ depth + height t
  | .node v cs, p, h => by
    rw [spans] at h
    rw [height_node]
    cases h with
    | head => exact Nat.le_add_right _ _
    | tail _ hq =>
      have k := spansAll_depth_le (depth + 1) start cs p hq
      omega

/-- The same for a list of trees: one row is taken by their parent. -/
theorem spansAll_depth_le (depth start : Nat) : ∀ (ts : List (Tree α)) (p : α × Span),
    p ∈ spansAll depth start ts →
    p.2.depth + 1 ≤ depth + (ts.map height).foldr (fun r m => max (r + 1) m) 0
  | [], p, h => by
    rw [spansAll] at h
    cases h
  | t :: ts, p, h => by
    rw [spansAll] at h
    rw [List.map_cons, List.foldr_cons]
    cases List.mem_append.mp h with
    | inl h1 =>
      have k := spans_depth_le depth start t p h1
      omega
    | inr h2 =>
      have k := spansAll_depth_le depth (start + leaves t) ts p h2
      omega

end

end Tree

end Whatwg.Svg.Scene
