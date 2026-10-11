import Whatwg.Html.Node.Raw

/-!
# Whatwg.Html.Node.Walk

Owner: the one top-down walk of a `RawNode` (point T5 of `docs/SVG-PACKAGE-PLAN.md`, section
3.1; ruling SV-23; slice S3b). A walk carries a state down the tree and builds a result up it:

- `step` takes the state at an element and the element's name to the state of its children;
- `element` makes the element's result from the state, the element's own data, and the results
  of its children. It also sees the raw children, because a test of a content model reads
  their names;
- `text`, `entity` and `comment` make a leaf's result from the state.

The checker, the located refusal and the printer are three algebras of this walk. Two laws
are proved here once, by structural recursion on the tree, and each law about a pair of
algebras is an instance:

- `Walk.fusion` (W1): a map of results that commutes with the node maps of two algebras
  commutes with their runs;
- `Walk.transport` (W2): a map of states that commutes with the transitions, through which the
  node maps factor, carries one run to the other.

`Walk.simulation` states both at once, and the two laws are its corollaries. A third law,
`Walk.relate` (W3), is induction over the walk: a relation between a node and its result
holds of the run when every node map preserves it.

This module names no schema and no position. It does not say what any algebra computes.
-/

namespace Whatwg.Html

/-- A top-down walk: a state, its transition, and what each node makes of its children. -/
structure Walk (S R : Type) where
  /-- The state of an element's children, from the element's state and name. -/
  step : S → String → S
  /-- An element's result: its state, name, attributes and raw children, and the results of
  the children at the state `step` gives. -/
  element : S → String → List (String × String) → List RawNode → List R → R
  /-- A text run's result. -/
  text : S → String → R
  /-- An entity reference's result. -/
  entity : S → String → R
  /-- A comment's result. -/
  comment : S → String → R

namespace Walk

variable {S S' R R' : Type}

mutual

/-- The walk's result at a node. -/
def run (w : Walk S R) (s : S) : RawNode → R
  | .element name attrs children =>
      w.element s name attrs children (runAll w (w.step s name) children)
  | .text content => w.text s content
  | .entity name => w.entity s name
  | .comment content => w.comment s content

/-- The walk's results over a forest, each node at the same state. -/
def runAll (w : Walk S R) (s : S) : List RawNode → List R
  | [] => []
  | node :: rest => run w s node :: runAll w s rest

end

theorem run_element (w : Walk S R) (s : S) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    w.run s (.element name attrs children) =
      w.element s name attrs children (w.runAll (w.step s name) children) := by
  rw [run]

theorem runAll_nil (w : Walk S R) (s : S) : w.runAll s [] = [] := by rw [runAll]

theorem runAll_cons (w : Walk S R) (s : S) (node : RawNode) (rest : List RawNode) :
    w.runAll s (node :: rest) = w.run s node :: w.runAll s rest := by
  rw [runAll]

/-- A forest's results are the node results, in order. -/
theorem runAll_eq_map (w : Walk S R) (s : S) :
    ∀ nodes : List RawNode, w.runAll s nodes = nodes.map (w.run s)
  | [] => by rw [runAll_nil, List.map_nil]
  | node :: rest => by rw [runAll_cons, List.map_cons, runAll_eq_map w s rest]

theorem length_runAll (w : Walk S R) (s : S) (nodes : List RawNode) :
    (w.runAll s nodes).length = nodes.length := by
  rw [runAll_eq_map, List.length_map]

/-! ## The two laws -/

mutual

/-- A map of states and a map of results that commute with every part of two algebras
commute with their runs. -/
theorem simulation (A : Walk S R) (B : Walk S' R') (f : S → S') (h : R → R')
    (hstep : ∀ s name, f (A.step s name) = B.step (f s) name)
    (helement : ∀ s name attrs children results,
      h (A.element s name attrs children results) =
        B.element (f s) name attrs children (results.map h))
    (htext : ∀ s content, h (A.text s content) = B.text (f s) content)
    (hentity : ∀ s name, h (A.entity s name) = B.entity (f s) name)
    (hcomment : ∀ s content, h (A.comment s content) = B.comment (f s) content) :
    ∀ (s : S) (node : RawNode), h (A.run s node) = B.run (f s) node
  | s, .element name attrs children => by
    rw [run_element, run_element, helement, ← hstep,
      simulationAll A B f h hstep helement htext hentity hcomment (A.step s name) children]
  | s, .text content => by rw [run, run, htext]
  | s, .entity name => by rw [run, run, hentity]
  | s, .comment content => by rw [run, run, hcomment]

/-- The same over a forest. -/
theorem simulationAll (A : Walk S R) (B : Walk S' R') (f : S → S') (h : R → R')
    (hstep : ∀ s name, f (A.step s name) = B.step (f s) name)
    (helement : ∀ s name attrs children results,
      h (A.element s name attrs children results) =
        B.element (f s) name attrs children (results.map h))
    (htext : ∀ s content, h (A.text s content) = B.text (f s) content)
    (hentity : ∀ s name, h (A.entity s name) = B.entity (f s) name)
    (hcomment : ∀ s content, h (A.comment s content) = B.comment (f s) content) :
    ∀ (s : S) (nodes : List RawNode), (A.runAll s nodes).map h = B.runAll (f s) nodes
  | s, [] => by rw [runAll_nil, runAll_nil, List.map_nil]
  | s, node :: rest => by
    rw [runAll_cons, runAll_cons, List.map_cons,
      simulation A B f h hstep helement htext hentity hcomment s node,
      simulationAll A B f h hstep helement htext hentity hcomment s rest]

end
/-- W1, fusion: a map of results that commutes with the node maps of two algebras over one
state commutes with their runs. -/
theorem fusion (A : Walk S R) (B : Walk S R') (h : R → R')
    (hstep : ∀ s name, A.step s name = B.step s name)
    (helement : ∀ s name attrs children results,
      h (A.element s name attrs children results) =
        B.element s name attrs children (results.map h))
    (htext : ∀ s content, h (A.text s content) = B.text s content)
    (hentity : ∀ s name, h (A.entity s name) = B.entity s name)
    (hcomment : ∀ s content, h (A.comment s content) = B.comment s content)
    (s : S) (node : RawNode) : h (A.run s node) = B.run s node :=
  simulation A B id h hstep helement htext hentity hcomment s node

/-- W2, state homomorphism: a map of states that commutes with the transitions, through which
the node maps factor, carries one algebra's run to the other's. -/
theorem transport (A : Walk S R) (B : Walk S' R) (f : S → S')
    (hstep : ∀ s name, f (A.step s name) = B.step (f s) name)
    (helement : ∀ s name attrs children results,
      A.element s name attrs children results = B.element (f s) name attrs children results)
    (htext : ∀ s content, A.text s content = B.text (f s) content)
    (hentity : ∀ s name, A.entity s name = B.entity (f s) name)
    (hcomment : ∀ s content, A.comment s content = B.comment (f s) content)
    (s : S) (node : RawNode) : A.run s node = B.run (f s) node :=
  simulation A B f id hstep
    (fun s name attrs children results => by rw [List.map_id]; exact helement s name attrs children results)
    htext hentity hcomment s node

/-! ## A relation that every node map preserves -/

/-- Each node of a list stands in the relation to the result at its place. -/
inductive Related (P : RawNode → R → Prop) : List RawNode → List R → Prop where
  | nil : Related P [] []
  | cons {node : RawNode} {result : R} {nodes : List RawNode} {results : List R} :
      P node result → Related P nodes results → Related P (node :: nodes) (result :: results)

mutual

/-- W3: a relation between a node and its result holds of the run, when every node map
preserves it. The element's map may assume it of each child with that child's result. -/
theorem relate (w : Walk S R) (P : RawNode → R → Prop)
    (helement : ∀ s name attrs children results, Related P children results →
      P (.element name attrs children) (w.element s name attrs children results))
    (htext : ∀ s content, P (.text content) (w.text s content))
    (hentity : ∀ s name, P (.entity name) (w.entity s name))
    (hcomment : ∀ s content, P (.comment content) (w.comment s content)) :
    ∀ (s : S) (node : RawNode), P node (w.run s node)
  | s, .element name attrs children => by
    rw [run_element]
    exact helement s name attrs children _
      (relateAll w P helement htext hentity hcomment (w.step s name) children)
  | s, .text content => by rw [run]; exact htext s content
  | s, .entity name => by rw [run]; exact hentity s name
  | s, .comment content => by rw [run]; exact hcomment s content

/-- The same over a forest: each node stands in the relation to its own result. -/
theorem relateAll (w : Walk S R) (P : RawNode → R → Prop)
    (helement : ∀ s name attrs children results, Related P children results →
      P (.element name attrs children) (w.element s name attrs children results))
    (htext : ∀ s content, P (.text content) (w.text s content))
    (hentity : ∀ s name, P (.entity name) (w.entity s name))
    (hcomment : ∀ s content, P (.comment content) (w.comment s content)) :
    ∀ (s : S) (nodes : List RawNode), Related P nodes (w.runAll s nodes)
  | s, [] => by rw [runAll_nil]; exact .nil
  | s, node :: rest => by
    rw [runAll_cons]
    exact .cons (relate w P helement htext hentity hcomment s node)
      (relateAll w P helement htext hentity hcomment s rest)

end

/-- An algebra over one state, read over another through a map of states. -/
def comap (B : Walk S' R) (step : S → String → S) (f : S → S') : Walk S R where
  step := step
  element := fun s => B.element (f s)
  text := fun s => B.text (f s)
  entity := fun s => B.entity (f s)
  comment := fun s => B.comment (f s)

/-- W2 at `comap`: when `f` commutes with the transitions, an algebra that reads only `f` of
the state runs the same over either state. -/
theorem run_comap (B : Walk S' R) (step : S → String → S) (f : S → S')
    (hstep : ∀ s name, f (step s name) = B.step (f s) name) (s : S) (node : RawNode) :
    (B.comap step f).run s node = B.run (f s) node :=
  transport (B.comap step f) B f hstep (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) s node

end Walk

end Whatwg.Html
