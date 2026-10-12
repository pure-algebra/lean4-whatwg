import Whatwg.Svg.Geometry.Vec

/-!
# Whatwg.Svg.Geometry.Stack

Owner: intervals in a row, each as long as its weight (slice S13 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-69).

Many pictures put things side by side along one line, each with the room its weight asks for:
the branches that leave a node, the bars of a stacked bar, the bands of an axis, the children
of a node in an icicle or a flame graph. The rule is one sum that runs along the list.

- `stack start weights`: the intervals, the first starting at `start`, each starting where the
  one before it ends.
- `stackAbout centre weights`: the same row with its middle at `centre`.
- `ports centre weights`: the middles of those intervals. Branches that leave a node at its
  ports lie side by side, in the order of the children, and together are as wide as the sum of
  their widths.

The laws: an interval is as long as its weight (`stack_lengths`); the row ends at the start
and the sum of the weights (`stack_end`); with weights that are not negative the intervals lie
in the row, in order, and no two overlap (`stack_within`, `stack_apart`); and a moved row is
the row, moved (`stack_move`).

What this module does not claim: a row in two directions (a treemap), or gaps between the
intervals, which a caller adds to the weights.
-/

namespace Whatwg.Svg.Value

/-- The sum of a list of numbers. -/
def total : List Rat → Rat
  | [] => 0
  | w :: ws => w + total ws

/-- **Intervals in a row**: the first starts at `start`, each is as long as its weight, and
each starts where the one before it ends. -/
def stack (start : Rat) : List Rat → List (Rat × Rat)
  | [] => []
  | w :: ws => (start, start + w) :: stack (start + w) ws

/-- The row of intervals with its middle at `centre`. -/
def stackAbout (centre : Rat) (weights : List Rat) : List (Rat × Rat) :=
  stack (centre - total weights / 2) weights

/-- **The ports of a row about a centre**: the middle of each interval. -/
def ports (centre : Rat) (weights : List Rat) : List Rat :=
  (stackAbout centre weights).map fun p => (p.1 + p.2) / 2

/-- The sum of weights that are not negative is not negative. -/
theorem total_nonneg : ∀ ws : List Rat, (∀ w ∈ ws, 0 ≤ w) → 0 ≤ total ws
  | [], _ => Rat.le_refl
  | w :: ws, h => by
    have h1 := h w List.mem_cons_self
    have h2 := total_nonneg ws fun x hx => h x (List.mem_cons_of_mem _ hx)
    show 0 ≤ w + total ws
    grind

/-- One interval for each weight. -/
theorem length_stack : ∀ (start : Rat) (ws : List Rat), (stack start ws).length = ws.length
  | _, [] => rfl
  | start, w :: ws => by
    show (stack (start + w) ws).length + 1 = ws.length + 1
    rw [length_stack]

/-- **An interval is as long as its weight.** -/
theorem stack_lengths : ∀ (start : Rat) (ws : List Rat),
    (stack start ws).map (fun p => p.2 - p.1) = ws
  | _, [] => rfl
  | start, w :: ws => by
    show (start + w - start) :: (stack (start + w) ws).map (fun p => p.2 - p.1) = w :: ws
    rw [stack_lengths]
    congr 1
    grind

/-- **The row ends at its start and the sum of the weights.** -/
theorem stack_end : ∀ (start : Rat) (ws : List Rat),
    ((stack start ws).getLast?.map fun p => p.2).getD start = start + total ws
  | start, [] => by
    show start = start + 0
    grind
  | start, [w] => by
    show start + w = start + (w + 0)
    grind
  | start, w :: v :: ws => by
    have ih := stack_end (start + w) (v :: ws)
    show ((stack (start + w) (v :: ws)).getLast?.map fun p => p.2).getD start = start + (w + total (v :: ws))
    have hne : (stack (start + w) (v :: ws)).getLast? ≠ none := by
      show ((start + w, start + w + v) :: stack (start + w + v) ws).getLast? ≠ none
      rw [List.getLast?_cons]
      exact fun h => by cases h
    cases hl : (stack (start + w) (v :: ws)).getLast? with
    | none => exact absurd hl hne
    | some p =>
      rw [hl] at ih
      show p.2 = start + (w + total (v :: ws))
      have e : p.2 = start + w + total (v :: ws) := ih
      rw [e]
      grind

/-- **With weights that are not negative, every interval lies in the row**, and its start is
not after its end. -/
theorem stack_within : ∀ (start : Rat) (ws : List Rat), (∀ w ∈ ws, 0 ≤ w) →
    ∀ p ∈ stack start ws, start ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ start + total ws
  | _, [], _, _, hp => by cases hp
  | start, w :: ws, h, p, hp => by
    have hw := h w List.mem_cons_self
    have hrest : ∀ x ∈ ws, 0 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ht := total_nonneg ws hrest
    cases hp with
    | head =>
      show start ≤ start ∧ start ≤ start + w ∧ start + w ≤ start + (w + total ws)
      grind
    | tail _ hq =>
      have ih := stack_within (start + w) ws hrest p hq
      show start ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ start + (w + total ws)
      grind

/-- **With weights that are not negative, no two intervals of a row overlap**: each ends at or
before the start of every later one. -/
theorem stack_apart : ∀ (start : Rat) (ws : List Rat), (∀ w ∈ ws, 0 ≤ w) →
    (stack start ws).Pairwise fun p q => p.2 ≤ q.1
  | _, [], _ => .nil
  | start, w :: ws, h => by
    have hrest : ∀ x ∈ ws, 0 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine .cons ?_ (stack_apart (start + w) ws hrest)
    intro q hq
    exact (stack_within (start + w) ws hrest q hq).1

/-- **A moved row is the row, moved.** -/
theorem stack_move (d : Rat) : ∀ (start : Rat) (ws : List Rat),
    stack (start + d) ws = (stack start ws).map fun p => (p.1 + d, p.2 + d)
  | _, [] => rfl
  | start, w :: ws => by
    have e : start + d + w = start + w + d := by grind
    show (start + d, start + d + w) :: stack (start + d + w) ws =
      (start + d, start + w + d) :: (stack (start + w) ws).map fun p => (p.1 + d, p.2 + d)
    rw [e, stack_move d (start + w) ws]

/-- A row about a moved centre is the row, moved. -/
theorem stackAbout_move (d centre : Rat) (ws : List Rat) :
    stackAbout (centre + d) ws = (stackAbout centre ws).map fun p => (p.1 + d, p.2 + d) := by
  have e : centre + d - total ws / 2 = centre - total ws / 2 + d := by grind
  rw [stackAbout, e, stack_move]
  rfl

/-- One port for each weight. -/
theorem length_ports (centre : Rat) (ws : List Rat) : (ports centre ws).length = ws.length := by
  rw [ports, List.length_map, stackAbout, length_stack]

/-- The ports about a moved centre are the ports, moved. -/
theorem ports_move (d centre : Rat) (ws : List Rat) :
    ports (centre + d) ws = (ports centre ws).map fun x => x + d := by
  rw [ports, stackAbout_move, ports, List.map_map, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  show (p.1 + d + (p.2 + d)) / 2 = (p.1 + p.2) / 2 + d
  grind

end Whatwg.Svg.Value
