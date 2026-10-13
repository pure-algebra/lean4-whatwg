import Whatwg.Svg.Scene.Tree.Fold

/-!
# WhatwgTest.Svg.UseFold

lean4-effect4's folds of a program, on `Whatwg/Svg/Scene/Tree/Fold.lean` (slice S22). The
consumer is read at its checkout `6ad8f7b8d`, and d3 at d3-hierarchy `c4ae7066d5a5`. This module
imports nothing of either: it restates what it reads.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `Layer`, `mapChild`, `fold` (`tools/Tools/View/Algebra.lean`, lines 34 to 58) | a step `α → List β → β` and `Tree.fold`: a node's own data is its value, and its children are the list |
| `fusionHom`, `cata_fusion` (lines 62 to 86) | `Tree.fold_fusion` |
| `Layer.prod`, `cata_prod` (lines 91 to 103) | `Tree.both`, `Tree.fold_both` |
| `childOk`, `Layer.keeping`, `cata_keeps` (lines 108 to 130) | `Tree.fold_keeps` |
| `Node`, `Lines`, `layerWith`, `lines` (`tools/Tools/View/Program.lean`, lines 41 to 48, 129 to 146) | `Line`, `Lines`, `layerWith`, `lines`, for a node that is no spine |
| `Node.under`, `Node.under_under`, `Moves`, `layer_moves`, `lines_at` (lines 158 to 219) | `Line.under`, `Line.under_under`, `Shifts`, `layer_shifts`, `lines_at`: fold induction |
| `textOf`, `layerAt`, `linesWith`, `retext`, `linesWith_map`, `MemoValid`, `linesWith_eq` (`tools/Tools/View/Inc.lean`, lines 63 to 97, 121 to 197) | the same names: fusion |
| `ChildBlind`, `mapChild_mapChild`, `filterMap_childLines_map`, `findSome_argOp_map` (`Inc.lean`, lines 116 to 147) | nothing: a step reads its node's value and the results, so a text reads no child by its type |

**What does not fit.** The consumer's program is a family of seven sorts, and a step there reads
a constructor's name and its arguments by sort. To use `Tree.fold` it builds a `Tree` of each
node's own data, with one fold of its own. A node of a sort that writes no line of its own (a
spine) is then a node whose step writes none; this port leaves spines out. A memo here is a
lookup, a function, where the consumer has its `KeyMap`.

**d3's own tests**, as guards: the two traversals of `test/hierarchy/each-test.js` that are
folds, and the links of `test/hierarchy/links-test.js`. Its breadth-first `each` is no fold of
this kind, and the control says where `Tree.links` and d3's `links` part.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseFold

open Whatwg.Svg.Scene

/-! ## The lines of a program -/

/-- A line of the page: its address, its depth and its text. The consumer's `Program.Node`,
less its operation. -/
structure Line where
  path : List Nat
  depth : Nat
  text : String
  deriving DecidableEq, Repr

/-- The result of the fold at a node: the lines of its subtree, given the subtree's own address
and depth. The consumer's `Lines`. -/
abbrev Lines : Type := List Nat → Nat → List Line

/-- **One step of the lines**: the node's own line, then its children's lines one level deeper,
the child `i` at the address with `i` after it. The consumer's `layerWith`. -/
def layerWith {α : Type} (text : α → String) (v : α) (children : List Lines) : Lines :=
  fun p d => ⟨p, d, text v⟩ :: children.zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + 1)

/-- **A program's lines**, in the order of its addresses: the consumer's `lines`. -/
def lines {α : Type} (text : α → String) (t : Tree α) : List Line :=
  Tree.fold (layerWith text) t [] 0

/-- A line under an address and a depth: the consumer's `Node.under`. -/
def Line.under (p : List Nat) (d : Nat) (n : Line) : Line :=
  { n with path := p ++ n.path, depth := d + n.depth }

/-- A line under one address and then another is under the two in a row. -/
theorem Line.under_under (p q : List Nat) (d e : Nat) (n : Line) :
    (n.under q e).under p d = n.under (p ++ q) (d + e) := by
  show (⟨p ++ (q ++ n.path), d + (e + n.depth), n.text⟩ : Line) =
    ⟨p ++ q ++ n.path, d + e + n.depth, n.text⟩
  rw [List.append_assoc, Nat.add_assoc]

/-- Lines that move: at every address and depth they are the lines at the root, moved there.
The consumer's `Moves`. -/
def Shifts (r : Lines) : Prop := ∀ p d, r p d = (r [] 0).map (Line.under p d)

/-- Two `flatMap`s that agree at each member agree: the consumer's `flatMap_congr_mem`. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α},
    (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A member of a list with its places is a member of the list. -/
theorem fst_mem_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => nomatch h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    cases h with
    | head => exact List.mem_cons_self
    | tail _ hm => exact List.mem_cons_of_mem a (fst_mem_zipIdx l (k + 1) x hm)

/-- **Each step keeps the move**: a node's lines move when its children's lines do. The
consumer's `layer_moves`. -/
theorem layer_shifts {α : Type} (text : α → String) (v : α) (rs : List Lines)
    (h : ∀ r ∈ rs, Shifts r) : Shifts (layerWith text v rs) := by
  have kids (p : List Nat) (d k : Nat) :
      (rs.zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + k)) =
        (rs.zipIdx.flatMap fun x => x.1 [x.2] k).map (Line.under p d) := by
    rw [List.map_flatMap]
    refine flatMap_congr_mem fun x hx => ?_
    have hx' : Shifts x.1 := h x.1 (fst_mem_zipIdx rs 0 x hx)
    rw [hx' (p ++ [x.2]) (d + k), hx' [x.2] k, List.map_map]
    exact List.map_congr_left fun n _ => (Line.under_under p [x.2] d k n).symm
  intro p d
  have e : (⟨[], 0, text v⟩ : Line).under p d = ⟨p, d, text v⟩ := by
    show (⟨p ++ [], d + 0, text v⟩ : Line) = ⟨p, d, text v⟩
    rw [List.append_nil]
    rfl
  show (⟨p, d, text v⟩ : Line) :: (rs.zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + 1)) =
    ((⟨[], 0, text v⟩ : Line) :: (rs.zipIdx.flatMap fun x => x.1 [x.2] 1)).map (Line.under p d)
  rw [List.map_cons, kids p d 1, e]

/-- **Equivariance of the lines**: a subtree's lines, folded at any address and depth, are its
lines at the root, each under that address and depth. The consumer's `lines_at`, by fold
induction (`Tree.fold_keeps` for its `cata_keeps`). -/
theorem lines_at {α : Type} (text : α → String) (t : Tree α) (p : List Nat) (d : Nat) :
    Tree.fold (layerWith text) t p d = (lines text t).map (Line.under p d) :=
  Tree.fold_keeps (P := Shifts) (layer_shifts text) t p d

/-! ## The lines along an edit -/

/-- A line's text along an edit at `edited`: computed under the edited subtree, else the
memo's, else computed. The consumer's `textOf`, its memo a lookup. -/
def textOf (memo : List Nat → Option String) :
    Option (List Nat) → List Nat → (Unit → String) → String
  | some a, p, compute => if a.isPrefixOf p then compute () else (memo p).getD (compute ())
  | none, _, compute => compute ()

/-- `layerWith`, each line's text along an edit: the consumer's `layerAt`. -/
def layerAt {α : Type} (text : α → String) (memo : List Nat → Option String)
    (edited : Option (List Nat)) (v : α) (children : List Lines) : Lines :=
  fun p d => ⟨p, d, textOf memo edited p fun _ => text v⟩ ::
    children.zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + 1)

/-- **The lines of a program along an edit**: the consumer's `linesWith`. -/
def linesWith {α : Type} (text : α → String) (memo : List Nat → Option String)
    (edited : Option (List Nat)) (t : Tree α) : List Line :=
  Tree.fold (layerAt text memo edited) t [] 0

/-- A line with its text along an edit: the consumer's `retext`. -/
def retext (memo : List Nat → Option String) (edited : Option (List Nat)) (n : Line) : Line :=
  { n with text := textOf memo edited n.path fun _ => n.text }

/-- The places of a mapped list go with the mapped members. -/
theorem flatMap_zipIdx_map {α β γ : Type} (φ : α → β) (g : β → Nat → List γ) :
    ∀ (l : List α) (k : Nat),
    ((l.map φ).zipIdx k).flatMap (fun x => g x.1 x.2) =
      (l.zipIdx k).flatMap fun x => g (φ x.1) x.2
  | [], _ => rfl
  | a :: l, k => by
    rw [List.map_cons, List.zipIdx_cons, List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons,
      flatMap_zipIdx_map φ g l (k + 1)]

/-- **The lines along an edit are the fresh lines, each retexted** from the memo outside the
edited subtree. The consumer's `linesWith_map`, by fusion (`Tree.fold_fusion` for its
`cata_fusion`): retexting commutes with each step. -/
theorem linesWith_map {α : Type} (text : α → String) (memo : List Nat → Option String)
    (edited : Option (List Nat)) (t : Tree α) :
    linesWith text memo edited t = (lines text t).map (retext memo edited) := by
  have h := Tree.fold_fusion (f := layerWith text) (g := layerAt text memo edited)
    (φ := fun r p d => (r p d).map (retext memo edited)) (fun v rs => by
      funext p d
      have e1 : (rs.zipIdx.flatMap fun x => x.1 (p ++ [x.2]) (d + 1)).map (retext memo edited) =
          (rs.map fun (r : Lines) p d => (r p d).map (retext memo edited)).zipIdx.flatMap
            fun x => x.1 (p ++ [x.2]) (d + 1) := by
        rw [List.map_flatMap,
          flatMap_zipIdx_map (fun (r : Lines) p d => (r p d).map (retext memo edited))
            (fun r i => r (p ++ [i]) (d + 1)) rs 0]
      exact congrArg (List.cons _) e1) t
  exact (congrFun (congrFun h []) 0).symm

/-- **A memo valid outside `a`** for a program's lines: every text it keeps at the address of a
line outside the subtree at `a` is that line's text. The consumer's `MemoValid`. -/
def MemoValid (memo : List Nat → Option String) (a : List Nat) (ls : List Line) : Prop :=
  ∀ n ∈ ls, a.isPrefixOf n.path = false → ∀ s, memo n.path = some s → s = n.text

/-- **The text law.** Under a memo valid outside `a`, the lines along an edit at `a` are the
fresh lines. The consumer's `linesWith_eq`. -/
theorem linesWith_eq {α : Type} (text : α → String) (memo : List Nat → Option String)
    (a : List Nat) (t : Tree α) (hv : MemoValid memo a (lines text t)) :
    linesWith text memo (some a) t = lines text t := by
  rw [linesWith_map]
  refine (List.map_congr_left fun n hn => ?_).trans (List.map_id' _)
  have e : textOf memo (some a) n.path (fun _ => n.text) = n.text := by
    show (if a.isPrefixOf n.path = true then n.text else (memo n.path).getD n.text) = n.text
    cases hp : a.isPrefixOf n.path with
    | true => rfl
    | false =>
      show (memo n.path).getD n.text = n.text
      cases hs : memo n.path with
      | none => rfl
      | some s => exact hv n hn hp s hs
  show ({ n with text := textOf memo (some a) n.path fun _ => n.text } : Line) = n
  rw [e]

/-! ## Two readings from one walk -/

/-- **The lines and the number of leaves, from one fold.** The consumer's `cata_prod`, read at
the two readings its page takes of a program: its lines, and the columns its tree needs. -/
example {α : Type} (text : α → String) (t : Tree α) :
    Tree.fold (Tree.both (layerWith text) fun _ rs => max 1 rs.sum) t =
      (Tree.fold (layerWith text) t, Tree.leaves t) := by
  rw [Tree.fold_both, Tree.leaves_eq_fold]

/-- **A tree is placed once and labelled afterwards.** The spans of the tree of the texts are
the spans of the tree, each with its text: `Tree.spans_map`, read at the text of a node. -/
example {α : Type} (text : α → String) (t : Tree α) :
    Tree.spans 0 0 (Tree.map text t) = (Tree.spans 0 0 t).map fun p => (text p.1, p.2) :=
  Tree.spans_map text 0 0 t

/-! ## Finite evaluations -/

/-- A small program: a block of two steps, the second a fork with one child. -/
def program : Tree String :=
  .node "block" [.node "yield" [], .node "fork" [.node "succeed" []]]

-- The lines of the program: each node at its address, one level under its parent.
#guard lines id program ==
  [⟨[], 0, "block"⟩, ⟨[0], 1, "yield"⟩, ⟨[1], 1, "fork"⟩, ⟨[1, 0], 2, "succeed"⟩]

-- An edit at `[1]` with a memo that knows the old texts of `[]` and `[0]`: the two lines
-- outside the edit take the memo's text and the two under it are computed. The memo's texts
-- are marked, to show which were taken.
#guard linesWith id (fun p => if p == [] then some "block*" else if p == [0] then some "yield*" else
    if p == [1, 0] then some "stale" else none) (some [1]) program ==
  [⟨[], 0, "block*"⟩, ⟨[0], 1, "yield*"⟩, ⟨[1], 1, "fork"⟩, ⟨[1, 0], 2, "succeed"⟩]

-- The control of the text law's premise: a memo that is not valid outside the edit gives lines
-- that are not the fresh lines. This is the consumer's control (`LiveChecks.lean`, lines 197 to
-- 200).
#guard linesWith id (fun p => if p == [0] then some "other" else none) (some [1]) program !=
  lines id program

/-! ## d3's own tests -/

/-- The tree of `d3-hierarchy/test/hierarchy/each-test.js`. -/
def d3tree : Tree String :=
  .node "root" [.node "a" [.node "ab" []], .node "b" [.node "ba" []]]

-- "node.eachBefore() traverses a hierarchy in pre-order traversal": the values of the tree.
#guard d3tree.values == ["root", "a", "ab", "b", "ba"]

-- "node.eachAfter() traverses a hierarchy in post-order traversal": the fold that writes a
-- node after its children.
#guard Tree.fold (fun v rs => rs.flatten ++ [v]) d3tree == ["ab", "a", "ba", "b", "root"]

-- "node.links() returns an array of {source, target}" (`test/hierarchy/links-test.js`).
#guard (Tree.node "root" [.node "a" [], .node "b" [.node "ba" []]]).links ==
  [("root", "a"), ("root", "b"), ("b", "ba")]

-- Control: where the two part. d3's `links` walks breadth first (`src/hierarchy/links.js`
-- calls `each`), so on the tree of `each-test.js` it would give root to a, root to b, a to ab,
-- b to ba. `Tree.links` gives each child and then the links under it. The same links, in
-- another order. The d3 order is read from its source by hand, and nothing here runs d3.
#guard d3tree.links == [("root", "a"), ("a", "ab"), ("root", "b"), ("b", "ba")]

-- d3's `count` (`src/hierarchy/count.js`) stores at each node the number of leaves under it,
-- and its `sum` (`src/hierarchy/sum.js`) a value of the node and the sums of its children.
-- Each is `Tree.scan` of one step. The numbers are computed here; d3 has no test of either.
#guard (Tree.scan (fun (_ : String) rs => max 1 rs.sum) d3tree).values ==
  [("root", 2), ("a", 1), ("ab", 1), ("b", 1), ("ba", 1)]
#guard (Tree.scan (fun (v : String) rs => v.length + rs.sum) d3tree).values ==
  [("root", 10), ("a", 3), ("ab", 2), ("b", 3), ("ba", 2)]

/-! ## Beside d3's `cluster`

The tree is a node with two leaf children and then a child of three leaves. The numbers said of
d3 are computed by hand from `src/cluster.js`, and nothing here runs d3. -/

/-- A node `r` with the leaves `a` and `b` and the node `c` of three leaves. -/
def uneven : Tree String :=
  .node "r" [.node "a" [], .node "b" [], .node "c" [.node "x" [], .node "y" [], .node "z" []]]

-- Here each leaf has one column, and a node stands over the middle of its leaves: twice the
-- middle of `r` is `4`, so `r` stands over the column `2`. In d3 the leaves stand at `0`, `1`,
-- `3`, `4`, `5`, since `x` is under another parent than `b`; `c` stands at `4`; and `r` at the
-- mean of `0`, `1` and `4`, which is `5/3`, where the middle of its leaves is `5/2`.
#guard (uneven.spans 0 0).map (fun p => (p.1, p.2.first, p.2.last, p.2.middle2)) ==
  [("r", 0, 4, 4), ("a", 0, 0, 0), ("b", 1, 1, 2), ("c", 2, 4, 6), ("x", 2, 2, 4), ("y", 3, 3, 6),
    ("z", 4, 4, 8)]

-- Here a node's row is its depth: the leaves `a` and `b` are level with `c`. In d3 a row counts
-- from the leaves, so `a` and `b` are level with `x`, `y` and `z`. The height of the tree is
-- d3's count for the root, and the picture has that many rows and one.
#guard (uneven.spans 0 0).map (fun p => (p.1, p.2.depth)) ==
  [("r", 0), ("a", 1), ("b", 1), ("c", 1), ("x", 2), ("y", 2), ("z", 2)]
#guard uneven.height == 2 && d3tree.height == 2 && (Tree.node "leaf" ([] : List (Tree String))).height == 0

end WhatwgTest.Svg.UseFold
