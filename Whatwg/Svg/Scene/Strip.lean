import Whatwg.Svg.Scene.Row
import Whatwg.Svg.Scene.Scale
import Whatwg.Svg.Scene.Moves

/-!
# Whatwg.Svg.Scene.Strip

Owner: a sequence in the room of a word (slice S16 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-89).

A program that is run goes through a sequence of steps, and each fiber is in one state at each
step. A lane draws one fiber: a column for each step, and one box for each stretch of steps in
one state. A small line draws a quantity over the steps, in the room of a word. In both, left
means earlier. A column is a step of control, and no length of time.

A reader believes four things of such a picture. Every step is in one box of its lane, and the
box has the state of the step. A box is as wide as its count of steps. A fiber that does not
exist at a step has no box there: absent is not a state. And when the program goes on by one
step, one column enters at the right, and nothing drawn before it changes. This module has the
functions that draw, and each of the four as a law of them.

It is module M12 of `docs/research/2026-10-12-pictures-craft-modules.md`. Everything counts in
whole numbers, in the caller's own units. A box is a state, a left edge and a width.

- `runs l`: the stretches of a sequence, each state with the count of steps that it lasts.
  `lead` puts one step before some runs, and `glue` puts two rows of runs in a row. `Apart`:
  two runs that follow each other have states that the test of equality tells apart.
- `boxes column l`: the runs as boxes from the left edge `0`, `column` for each step. `place`
  does it from any left edge, on the edges of `Row.spans`.
- `lane column states`: the boxes of a fiber that has a state at some steps and none at others.
  `present` leaves out the boxes with no state, and `shift` moves a box to the right.
- `lanes column rows`: for each key its lane.
- `line scale column values`: a point for each value, the `i`-th in the column `i`, at the
  height that the scale gives it. `lineFrom` does it from any column.
- `marks values`: the columns of the least value, the greatest and the last. `pick` finds the
  first two.

What the laws say of a lane:

- `runs_expand`: the runs written out are the sequence. `runs_pos`, `runs_sum`, `runs_mem`: a
  run lasts one step at least, the counts add up to the count of the steps, and a run has a
  state of the sequence. `runs_apart`, `runs_apart_ne`: a run is as long as it can be.
- `boxes_tile`, `boxes_start`, `boxes_end`: the boxes tile, from `0` to `column` times the count
  of the steps. `boxes_width`, `boxes_states`: a box is `column` times as wide as its run is
  long, and the boxes have the states of the runs, in order.
- `boxes_cover`, `boxes_one`, `boxes_ordered`: the column of a step lies in a box that has the
  state of the step, no place is in two boxes, and a box ends before every later box starts.
- **The law of a picture that grows** (`boxes_snoc`, with `boxes_snoc_new`, `boxes_snoc_same`
  and `boxes_snoc_keeps`): with one more step, a new box of one column stands in the column of
  the step, or the last box is one column wider at the same left edge. Every box before the
  last is the box that it was. `runs_snoc` says it of the runs, and `runs_append` of a sequence
  that grows by many steps at once.
- `mem_lane`, `lane_some`, `lane_none`: a lane is laid out with the absent steps in their
  columns, and those boxes are then left out. A fiber with a state at every step has the boxes
  of its states, and a fiber with no state has no box.
- `lane_hole`: the lane of a sequence with an absent step is the lane of what is before the
  step, and then the lane of what is after it, moved to the right by the columns before the
  step and one more. `lane_absent`: no box of the lane covers the column of an absent step.
  `lane_cover`, `lane_one`: a step with a state is in one box of the lane, of that state.
- `lane_snoc_none`, `lane_snoc_some`, `lane_snoc_keeps`: a lane grows as `boxes` does, and a
  step with no state changes nothing in it. `mem_lanes`: each lane of `lanes` is such a lane.

What the laws say of a small line:

- `line_length`, `line_across`: there is a point for each value, and the `i`-th has the
  abscissa `column * i` and the ordinate that the scale gives its value.
- `line_mono`, `line_anti`, `line_level`: on a scale that rises a greater value never has a
  lesser ordinate, on a scale that falls never a greater one, and equal values are level.
- `line_snoc`: with one more value the line is the line and one more point.
- `marks_least`, `marks_greatest`, `marks_last`, `marks_inside`: the three marks are columns of
  the sequence. The value at the first is no more than every value and less than every value
  left of it, so it is the column furthest left with the least value. The second is so for the
  greatest. The third is the last column.

What a caller must supply. A test of equality on its states. `runs_expand`, `runs_append` and
the laws that follow from them ask for a lawful one (`LawfulBEq`): the laws of a picture that
grows, of a hole, and of the box that a step is in. The laws of tiling, of width and of order
hold of any test. Columns that are not negative, for the laws that compare places:
`boxes_within`, `boxes_ordered`, `boxes_one`, `boxes_cover`, `lane_absent`, `lane_cover` and
`lane_one`. A scale that rises or falls, for `line_mono` and `line_anti`. The ordinate of each
lane and the height of its boxes, which this module does not give. And rows of one count of
steps, where the lanes are to be read against each other.

How this differs from the design note, whose signatures no Lean had checked:

- `runs` gives the counts and `boxes` places them. The note has one function for both.
- A box is a state, a left edge and a width. The note has an `IBox`, which this layer does not
  have yet, and a height, which no law here needs.
- `lanes` gives each key its list of boxes, and takes the width of a column. The note gives one
  list of a key, a state and a box, and takes a cell.
- The note's `runs_tile` and `runs_width` are `boxes_tile`, with `boxes_start` and `boxes_end`,
  and `boxes_width`. Its `lanes_absent` is `lane_absent`, with `lane_hole` for the layout.
- The laws of a picture that grows are added: the note has them as a probe to look at.

What this module does not claim: anything of time, since a column is a step; a break in an
axis; the laws of place for columns that are negative; that two lanes have one count of steps;
`runs_expand` for a test of equality that is not lawful, where two states that differ are one
run (a control below shows it); that two different values of a small line are drawn at two
heights, which `Scale.ties` answers; that the marks are the lowest and the highest points
drawn, since they are found by value and a scale can draw two values alike.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Strip

/-! ## Lists that end -/

/-- A list is empty, or it is a list and one last member. -/
private theorem snoc_cases {α : Type} : ∀ l : List α, l = [] ∨ ∃ front a, l = front ++ [a]
  | [] => Or.inl rfl
  | [a] => Or.inr ⟨[], a, rfl⟩
  | a :: b :: rest => by
    rcases snoc_cases (b :: rest) with h | ⟨front, c, h⟩
    · exact nomatch h
    · exact Or.inr ⟨a :: front, c, congrArg (a :: ·) h⟩

/-- The last member of a list and one last member is that member. -/
private theorem getLast?_snoc {α : Type} (a : α) : ∀ front : List α, (front ++ [a]).getLast? = some a
  | [] => rfl
  | [_] => rfl
  | _ :: c :: rest => getLast?_snoc a (c :: rest)

/-- A list with something after it is not empty. -/
private theorem append_ne_nil {α : Type} (front : List α) {back : List α} (h : back ≠ []) :
    front ++ back ≠ [] := by
  cases front with
  | nil => exact h
  | cons a front => exact fun e => nomatch e

/-! ## The runs of a sequence -/

/-- **One step before some runs.** The step joins the first run where it has that run's state,
and is a run of its own where it has not. Where the test of equality holds of two states that
differ, a run is named by the state of its last step. -/
def lead {σ : Type} [BEq σ] (s : σ) : List (σ × Nat) → List (σ × Nat)
  | [] => [(s, 1)]
  | (t, n) :: more => if s == t then (t, n + 1) :: more else (s, 1) :: (t, n) :: more

/-- **The runs of a sequence**: each state with the count of steps that it lasts, in order. A
run is as long as it can be. -/
def runs {σ : Type} [BEq σ] : List σ → List (σ × Nat)
  | [] => []
  | s :: rest => lead s (runs rest)

/-- **Two rows of runs in a row.** The last run of the first and the first run of the second are
one run where they have one state. -/
def glue {σ : Type} [BEq σ] : List (σ × Nat) → List (σ × Nat) → List (σ × Nat)
  | [], back => back
  | [r], [] => [r]
  | [(s, n)], (t, m) :: back => if s == t then (t, n + m) :: back else (s, n) :: (t, m) :: back
  | r :: r' :: front, back => r :: glue (r' :: front) back

/-- **Runs are apart**: two runs that follow each other have states that the test of equality
tells apart. -/
def Apart {σ : Type} [BEq σ] : List (σ × Nat) → Prop
  | a :: b :: rest => (a.1 == b.1) = false ∧ Apart (b :: rest)
  | _ => True

/-- A step with the state of the first run makes that run one step longer. -/
theorem lead_same {σ : Type} [BEq σ] {s t : σ} (h : (s == t) = true) (n : Nat)
    (more : List (σ × Nat)) : lead s ((t, n) :: more) = (t, n + 1) :: more :=
  if_pos h

/-- A step with another state than the first run is a run of its own. -/
theorem lead_other {σ : Type} [BEq σ] {s t : σ} (h : (s == t) = false) (n : Nat)
    (more : List (σ × Nat)) : lead s ((t, n) :: more) = (s, 1) :: (t, n) :: more :=
  if_neg (ne_true_of_eq_false h)

/-- One step before some runs, written out, is the step before the runs written out. -/
theorem lead_expand {σ : Type} [BEq σ] [LawfulBEq σ] (s : σ) : ∀ rs : List (σ × Nat),
    (lead s rs).flatMap (fun r => List.replicate r.2 r.1) =
      s :: rs.flatMap fun r => List.replicate r.2 r.1
  | [] => rfl
  | (t, n) :: more => by
    cases h : s == t with
    | true =>
      have e : s = t := eq_of_beq h
      subst e
      rw [lead_same h, List.flatMap_cons, List.flatMap_cons, List.replicate_succ, List.cons_append]
    | false =>
      rw [lead_other h, List.flatMap_cons]
      rfl

/-- **The runs written out are the sequence.** Every step is in exactly one run, and it has the
state of its run. -/
theorem runs_expand {σ : Type} [BEq σ] [LawfulBEq σ] : ∀ l : List σ,
    (runs l).flatMap (fun r => List.replicate r.2 r.1) = l
  | [] => rfl
  | s :: rest => by
    show (lead s (runs rest)).flatMap (fun r => List.replicate r.2 r.1) = s :: rest
    rw [lead_expand s (runs rest), runs_expand rest]

/-- One step before runs of one step or more gives runs of one step or more. -/
theorem lead_pos {σ : Type} [BEq σ] (s : σ) : ∀ rs : List (σ × Nat), (∀ r ∈ rs, 0 < r.2) →
    ∀ r ∈ lead s rs, 0 < r.2
  | [], _, r, hr => by
    rcases List.mem_cons.mp hr with e | e
    · rw [e]
      exact Nat.succ_pos 0
    · exact nomatch e
  | (t, n) :: more, h, r, hr => by
    cases hs : s == t with
    | true =>
      rw [lead_same hs] at hr
      rcases List.mem_cons.mp hr with e | e
      · rw [e]
        exact Nat.succ_pos n
      · exact h r (List.mem_cons_of_mem _ e)
    | false =>
      rw [lead_other hs] at hr
      rcases List.mem_cons.mp hr with e | e
      · rw [e]
        exact Nat.succ_pos 0
      · exact h r e

/-- **Every run lasts one step at least.** No box of a lane has no width. -/
theorem runs_pos {σ : Type} [BEq σ] : ∀ (l : List σ) (r : σ × Nat), r ∈ runs l → 0 < r.2
  | [], _, h => nomatch h
  | s :: rest, r, h => lead_pos s (runs rest) (runs_pos rest) r h

/-- One step before some runs is one step more. -/
theorem lead_sum {σ : Type} [BEq σ] (s : σ) : ∀ rs : List (σ × Nat),
    ((lead s rs).map Prod.snd).sum = (rs.map Prod.snd).sum + 1
  | [] => rfl
  | (t, n) :: more => by
    cases hs : s == t with
    | true =>
      rw [lead_same hs, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      omega
    | false =>
      rw [lead_other hs, List.map_cons, List.sum_cons]
      omega

/-- **The counts of the runs add up to the length of the sequence.** -/
theorem runs_sum {σ : Type} [BEq σ] : ∀ l : List σ, ((runs l).map Prod.snd).sum = l.length
  | [] => rfl
  | s :: rest => by
    show ((lead s (runs rest)).map Prod.snd).sum = rest.length + 1
    rw [lead_sum s (runs rest), runs_sum rest]

/-- One step before runs that are apart gives runs that are apart. -/
theorem lead_apart {σ : Type} [BEq σ] (s : σ) : ∀ rs : List (σ × Nat), Apart rs →
    Apart (lead s rs)
  | [], _ => True.intro
  | (t, n) :: more, h => by
    cases hs : s == t with
    | true =>
      rw [lead_same hs]
      cases more with
      | nil => exact True.intro
      | cons u rest => exact h
    | false =>
      rw [lead_other hs]
      exact ⟨hs, h⟩

/-- **A run is as long as it can be**: two runs that follow each other have states that the test
of equality tells apart. -/
theorem runs_apart {σ : Type} [BEq σ] : ∀ l : List σ, Apart (runs l)
  | [] => True.intro
  | s :: rest => lead_apart s (runs rest) (runs_apart rest)

/-- In runs that are apart, two that follow each other are told apart. -/
theorem apart_split {σ : Type} [BEq σ] (a b : σ × Nat) (back : List (σ × Nat)) :
    ∀ front : List (σ × Nat), Apart (front ++ a :: b :: back) → (a.1 == b.1) = false
  | [], h => h.1
  | [_], h => h.2.1
  | _ :: d :: front, h => apart_split a b back (d :: front) h.2

/-- **Two runs that follow each other have different states.** So no two boxes of one state
stand side by side in a lane: a box ends where its state ends. -/
theorem runs_apart_ne {σ : Type} [BEq σ] [LawfulBEq σ] (l : List σ) {front back : List (σ × Nat)}
    {a b : σ × Nat} (h : runs l = front ++ a :: b :: back) : a.1 ≠ b.1 := by
  have ha := runs_apart l
  rw [h] at ha
  exact ne_of_beq_false (apart_split a b back front ha)

/-- The state of a run is a state of the sequence. -/
theorem lead_mem {σ : Type} [BEq σ] (s : σ) (l : List σ) : ∀ rs : List (σ × Nat),
    (∀ r ∈ rs, r.1 ∈ l) → ∀ r ∈ lead s rs, r.1 ∈ s :: l
  | [], _, r, hr => by
    rcases List.mem_cons.mp hr with e | e
    · rw [e]
      exact List.mem_cons_self
    · exact nomatch e
  | (t, n) :: more, h, r, hr => by
    cases hs : s == t with
    | true =>
      rw [lead_same hs] at hr
      rcases List.mem_cons.mp hr with e | e
      · rw [e]
        exact List.mem_cons_of_mem _ (h (t, n) List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (h r (List.mem_cons_of_mem _ e))
    | false =>
      rw [lead_other hs] at hr
      rcases List.mem_cons.mp hr with e | e
      · rw [e]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h r e)

/-- **The state of a run is a state of the sequence.** A lane shows no state that its fiber
never had. -/
theorem runs_mem {σ : Type} [BEq σ] : ∀ (l : List σ) (r : σ × Nat), r ∈ runs l → r.1 ∈ l
  | [], _, h => nomatch h
  | s :: rest, r, h => lead_mem s rest (runs rest) (runs_mem rest) r h

/-! ## Two sequences in a row -/

/-- Runs with nothing after them are the runs. -/
theorem glue_nil_right {σ : Type} [BEq σ] : ∀ front : List (σ × Nat), glue front [] = front
  | [] => rfl
  | [_] => rfl
  | r :: r' :: front => congrArg (r :: ·) (glue_nil_right (r' :: front))

/-- Two single runs of one state are one run. -/
theorem glue_same {σ : Type} [BEq σ] {s t : σ} (h : (s == t) = true) (n m : Nat)
    (back : List (σ × Nat)) : glue [(s, n)] ((t, m) :: back) = (t, n + m) :: back :=
  if_pos h

/-- Two single runs of two states stay two runs. -/
theorem glue_other {σ : Type} [BEq σ] {s t : σ} (h : (s == t) = false) (n m : Nat)
    (back : List (σ × Nat)) : glue [(s, n)] ((t, m) :: back) = (s, n) :: (t, m) :: back :=
  if_neg (ne_true_of_eq_false h)

/-- A run that is not the last of its row is not changed by what comes after the row. -/
theorem glue_cons {σ : Type} [BEq σ] (r : σ × Nat) {front : List (σ × Nat)} (h : front ≠ [])
    (back : List (σ × Nat)) : glue (r :: front) back = r :: glue front back := by
  cases front with
  | nil => exact absurd rfl h
  | cons r' front => rfl

/-- Only the last run of a row can change with what comes after the row. -/
theorem glue_append {σ : Type} [BEq σ] {mid : List (σ × Nat)} (h : mid ≠ [])
    (back : List (σ × Nat)) : ∀ front : List (σ × Nat),
    glue (front ++ mid) back = front ++ glue mid back
  | [] => rfl
  | r :: front => by
    show glue (r :: (front ++ mid)) back = r :: (front ++ glue mid back)
    rw [glue_cons r (append_ne_nil front h) back, glue_append h back front]

/-- One step before a single run and what follows it. -/
theorem lead_glue_one {σ : Type} [BEq σ] [LawfulBEq σ] (s u : σ) (k : Nat) :
    ∀ back : List (σ × Nat), lead s (glue [(u, k)] back) = glue (lead s [(u, k)]) back
  | [] => (glue_nil_right (lead s [(u, k)])).symm
  | (t, m) :: rest => by
    cases hut : u == t with
    | true =>
      have e : u = t := eq_of_beq hut
      subst e
      rw [glue_same hut]
      cases hsu : s == u with
      | true =>
        rw [lead_same hsu, lead_same hsu, glue_same hut, Nat.add_right_comm]
      | false =>
        rw [lead_other hsu, lead_other hsu]
        show (s, 1) :: (u, k + m) :: rest = (s, 1) :: glue [(u, k)] ((u, m) :: rest)
        rw [glue_same hut]
    | false =>
      rw [glue_other hut]
      cases hsu : s == u with
      | true =>
        have e : s = u := eq_of_beq hsu
        subst e
        rw [lead_same hsu, lead_same hsu, glue_other hut]
      | false =>
        rw [lead_other hsu, lead_other hsu]
        show (s, 1) :: (u, k) :: (t, m) :: rest = (s, 1) :: glue [(u, k)] ((t, m) :: rest)
        rw [glue_other hut]

/-- One step before two rows of runs in a row is the step before the first row. -/
theorem lead_glue {σ : Type} [BEq σ] [LawfulBEq σ] (s : σ) :
    ∀ front back : List (σ × Nat), lead s (glue front back) = glue (lead s front) back
  | [], [] => rfl
  | [], (t, m) :: rest => by
    show lead s ((t, m) :: rest) = glue [(s, 1)] ((t, m) :: rest)
    cases hs : s == t with
    | true => rw [lead_same hs, glue_same hs, Nat.add_comm]
    | false => rw [lead_other hs, glue_other hs]
  | [(u, k)], back => lead_glue_one s u k back
  | (u, k) :: r' :: front, back => by
    show lead s ((u, k) :: glue (r' :: front) back) = glue (lead s ((u, k) :: r' :: front)) back
    cases hsu : s == u with
    | true =>
      rw [lead_same hsu, lead_same hsu]
      rfl
    | false =>
      rw [lead_other hsu, lead_other hsu]
      rfl

/-- **The runs of two sequences in a row.** They are the runs of the first and the runs of the
second, and where the first ends in the state that the second starts in, those two runs are
one. -/
theorem runs_append {σ : Type} [BEq σ] [LawfulBEq σ] : ∀ a b : List σ,
    runs (a ++ b) = glue (runs a) (runs b)
  | [], _ => rfl
  | s :: a, b => by
    show lead s (runs (a ++ b)) = glue (lead s (runs a)) (runs b)
    rw [runs_append a b, lead_glue]

/-! ## A sequence that grows by one step -/

/-- The runs of a sequence that ends in `s` end in a run of `s`. -/
theorem runs_snoc_shape {σ : Type} [BEq σ] [LawfulBEq σ] (l : List σ) (s : σ) :
    ∃ front n, runs (l ++ [s]) = front ++ [(s, n)] := by
  have e : runs (l ++ [s]) = glue (runs l) [(s, 1)] := runs_append l [s]
  rcases snoc_cases (runs l) with h | ⟨front, ⟨u, k⟩, h⟩
  · rw [h] at e
    exact ⟨[], 1, e⟩
  · rw [h, glue_append (List.cons_ne_nil _ _) [(s, 1)] front] at e
    cases hu : u == s with
    | true =>
      have eu : u = s := eq_of_beq hu
      subst eu
      rw [glue_same hu] at e
      exact ⟨front, k + 1, e⟩
    | false =>
      rw [glue_other hu] at e
      exact ⟨front ++ [(u, k)], 1, by rw [e, List.append_assoc]; rfl⟩

/-- **A sequence that grows by one step: its runs.** Where the sequence is empty or its last
state is not the new one, the runs are the runs and one new run of one step. Where its last
state is the new one, the runs are the runs with the last one a step longer. No run before the
last changes. -/
theorem runs_snoc {σ : Type} [BEq σ] [LawfulBEq σ] (l : List σ) (s : σ) :
    (l.getLast? ≠ some s ∧ runs (l ++ [s]) = runs l ++ [(s, 1)]) ∨
      (l.getLast? = some s ∧
        ∃ front n, runs l = front ++ [(s, n)] ∧ runs (l ++ [s]) = front ++ [(s, n + 1)]) := by
  have e : runs (l ++ [s]) = glue (runs l) [(s, 1)] := runs_append l [s]
  rcases snoc_cases l with h | ⟨l', t, h⟩
  · subst h
    exact Or.inl ⟨(fun x => nomatch x), rfl⟩
  · subst h
    obtain ⟨front, n, hf⟩ := runs_snoc_shape l' t
    rw [hf, glue_append (List.cons_ne_nil _ _) [(s, 1)] front] at e
    rw [getLast?_snoc t l', hf]
    cases ht : t == s with
    | true =>
      have et : t = s := eq_of_beq ht
      subst et
      rw [glue_same ht] at e
      exact Or.inr ⟨rfl, front, n, rfl, e⟩
    | false =>
      rw [glue_other ht] at e
      refine Or.inl ⟨fun x => ne_of_beq_false ht (Option.some.inj x), ?_⟩
      rw [e, List.append_assoc]
      rfl

/-- **A step of a new state is a new run.** Where the sequence is empty or its last state is not
`s`, the runs of the sequence and `s` are its runs and one run of one step. -/
theorem runs_snoc_new {σ : Type} [BEq σ] [LawfulBEq σ] (l : List σ) (s : σ)
    (h : l.getLast? ≠ some s) : runs (l ++ [s]) = runs l ++ [(s, 1)] := by
  rcases runs_snoc l s with ⟨_, e⟩ | ⟨e, _⟩
  · exact e
  · exact absurd e h

/-- **A step of the last state makes the last run one step longer**, and changes no other
run. -/
theorem runs_snoc_same {σ : Type} [BEq σ] [LawfulBEq σ] (l : List σ) (s : σ)
    (h : l.getLast? = some s) :
    ∃ front n, runs l = front ++ [(s, n)] ∧ runs (l ++ [s]) = front ++ [(s, n + 1)] := by
  rcases runs_snoc l s with ⟨e, _⟩ | ⟨_, e⟩
  · exact absurd h e
  · exact e

/-! ## The boxes of a lane -/

/-- **Runs as boxes from a left edge**: each state with the left edge and the width of its box,
`column` for each step. The edges are those of `Row.spans`. -/
def place {σ : Type} (column start : Int) (rs : List (σ × Nat)) : List (σ × Int × Int) :=
  (rs.map Prod.fst).zip (Row.spans start (rs.map fun r => column * (r.2 : Int)))

/-- **The runs as the boxes of a lane**: each state with the left edge and the width of its box,
`column` for each step, from the left edge `0`. -/
def boxes {σ : Type} [BEq σ] (column : Int) (states : List σ) : List (σ × Int × Int) :=
  place column 0 (runs states)

/-- The first run is a box at the left edge, and the others follow from where it ends. -/
theorem place_cons {σ : Type} (column start : Int) (s : σ) (n : Nat) (rs : List (σ × Nat)) :
    place column start ((s, n) :: rs) =
      (s, start, column * (n : Int)) :: place column (start + column * (n : Int)) rs :=
  rfl

/-- The boxes of two rows of runs in a row: the second row starts where the first ends. -/
theorem place_append {σ : Type} (column : Int) : ∀ (start : Int) (front back : List (σ × Nat)),
    place column start (front ++ back) =
      place column start front ++
        place column (start + column * ((front.map Prod.snd).sum : Nat)) back
  | start, [], back => by
    show place column start back = place column (start + column * 0) back
    rw [Int.mul_zero, Int.add_zero]
  | start, (s, n) :: front, back => by
    show (s, start, column * (n : Int)) ::
        place column (start + column * (n : Int)) (front ++ back) =
      (s, start, column * (n : Int)) :: (place column (start + column * (n : Int)) front ++
        place column (start + column * ((n + (front.map Prod.snd).sum : Nat) : Int)) back)
    rw [place_append column (start + column * (n : Int)) front back, Int.natCast_add, Int.mul_add,
      Int.add_assoc]

/-- The edges and the widths of the boxes are a row of lengths. -/
theorem place_edges {σ : Type} (column : Int) : ∀ (start : Int) (rs : List (σ × Nat)),
    (place column start rs).map Prod.snd = Row.spans start (rs.map fun r => column * (r.2 : Int))
  | _, [] => rfl
  | start, (s, n) :: rs => by
    show (start, column * (n : Int)) ::
        (place column (start + column * (n : Int)) rs).map Prod.snd =
      (start, column * (n : Int)) ::
        Row.spans (start + column * (n : Int)) (rs.map fun r => column * (r.2 : Int))
    rw [place_edges column (start + column * (n : Int)) rs]

/-- The states of the boxes are the states of the runs, in order. -/
theorem place_states {σ : Type} (column : Int) : ∀ (start : Int) (rs : List (σ × Nat)),
    (place column start rs).map Prod.fst = rs.map Prod.fst
  | _, [] => rfl
  | start, (s, n) :: rs => by
    show s :: (place column (start + column * (n : Int)) rs).map Prod.fst = s :: rs.map Prod.fst
    rw [place_states column (start + column * (n : Int)) rs]

/-- A box is `column` times as wide as its run is long. -/
theorem place_widths {σ : Type} (column : Int) : ∀ (start : Int) (rs : List (σ × Nat)),
    (place column start rs).map (fun b => b.2.2) = rs.map fun r => column * (r.2 : Int)
  | _, [] => rfl
  | start, (s, n) :: rs => by
    show column * (n : Int) :: (place column (start + column * (n : Int)) rs).map (fun b => b.2.2) =
      column * (n : Int) :: rs.map fun r => column * (r.2 : Int)
    rw [place_widths column (start + column * (n : Int)) rs]

/-- The last box ends `column` times the count of the steps past the left edge. -/
theorem place_end {σ : Type} (column : Int) : ∀ (start : Int) (rs : List (σ × Nat))
    (b : σ × Int × Int), (place column start rs).getLast? = some b →
      b.2.1 + b.2.2 = start + column * ((rs.map Prod.snd).sum : Nat)
  | _, [], _, h => nomatch h
  | start, [(s, n)], b, h => by
    have e : (s, start, column * (n : Int)) = b := Option.some.inj h
    rw [← e]
    show start + column * (n : Int) = start + column * ((n + 0 : Nat) : Int)
    rw [Nat.add_zero]
  | start, (s, n) :: (t, m) :: rs, b, h => by
    have ih := place_end column (start + column * (n : Int)) ((t, m) :: rs) b h
    rw [ih]
    show start + column * (n : Int) + column * ((((t, m) :: rs).map Prod.snd).sum : Nat) =
      start + column * ((n + (((t, m) :: rs).map Prod.snd).sum : Nat) : Int)
    rw [Int.natCast_add, Int.mul_add, Int.add_assoc]

/-- With columns that are not negative, a box is inside the room of its runs, and its width is
not negative. -/
theorem place_within {σ : Type} (column : Int) (hc : 0 ≤ column) :
    ∀ (start : Int) (rs : List (σ × Nat)) (b : σ × Int × Int), b ∈ place column start rs →
      start ≤ b.2.1 ∧ 0 ≤ b.2.2 ∧ b.2.1 + b.2.2 ≤ start + column * ((rs.map Prod.snd).sum : Nat)
  | _, [], _, h => nomatch h
  | start, (s, n) :: rs, b, h => by
    have hn : 0 ≤ column * (n : Int) := Int.mul_nonneg hc (Int.natCast_nonneg n)
    have hs : 0 ≤ column * (((rs.map Prod.snd).sum : Nat) : Int) :=
      Int.mul_nonneg hc (Int.natCast_nonneg _)
    have e : column * ((((s, n) :: rs).map Prod.snd).sum : Nat) =
        column * (n : Int) + column * (((rs.map Prod.snd).sum : Nat) : Int) := by
      show column * ((n + (rs.map Prod.snd).sum : Nat) : Int) = _
      rw [Int.natCast_add, Int.mul_add]
    rw [e]
    rcases List.mem_cons.mp h with hb | hb
    · rw [hb]
      show start ≤ start ∧ 0 ≤ column * (n : Int) ∧ start + column * (n : Int) ≤
        start + (column * (n : Int) + column * (((rs.map Prod.snd).sum : Nat) : Int))
      refine ⟨Int.le_refl start, hn, ?_⟩
      omega
    · obtain ⟨h1, h2, h3⟩ := place_within column hc (start + column * (n : Int)) rs b hb
      refine ⟨?_, h2, ?_⟩
      · omega
      · omega

/-- **The boxes of a lane tile**: each starts where the one before it ends. No gap opens between
two boxes and no two lie over each other. -/
theorem boxes_tile {σ : Type} [BEq σ] (column : Int) (l : List σ) :
    Row.Tiles ((boxes column l).map Prod.snd) := by
  show Row.Tiles ((place column 0 (runs l)).map Prod.snd)
  rw [place_edges]
  exact Row.tiles_spans _ _

/-- **The first box starts at `0`.** -/
theorem boxes_start {σ : Type} [BEq σ] (column : Int) (l : List σ) (b : σ × Int × Int)
    (h : (boxes column l).head? = some b) : b.2.1 = 0 := by
  have h' : (place column 0 (runs l)).head? = some b := h
  cases hr : runs l with
  | nil =>
    rw [hr] at h'
    exact nomatch h'
  | cons r rs =>
    rw [hr] at h'
    have e : (r.1, (0 : Int), column * (r.2 : Int)) = b := Option.some.inj h'
    rw [← e]

/-- **The last box ends at `column` times the count of the steps.** With `boxes_tile` and
`boxes_start`, the boxes fill the lane from `0` to there. -/
theorem boxes_end {σ : Type} [BEq σ] (column : Int) (l : List σ) (b : σ × Int × Int)
    (h : (boxes column l).getLast? = some b) : b.2.1 + b.2.2 = column * (l.length : Int) := by
  rw [place_end column 0 (runs l) b h, runs_sum, Int.zero_add]

/-- **The states of the boxes are the states of the runs**, in order. -/
theorem boxes_states {σ : Type} [BEq σ] (column : Int) (l : List σ) :
    (boxes column l).map Prod.fst = (runs l).map Prod.fst :=
  place_states column 0 (runs l)

/-- **A box is `column` times as wide as its run is long.** A width says a count of steps, and
no length of time. -/
theorem boxes_width {σ : Type} [BEq σ] (column : Int) (l : List σ) :
    (boxes column l).map (fun b => b.2.2) = (runs l).map fun r => column * (r.2 : Int) :=
  place_widths column 0 (runs l)

/-- A lane has a box for each run. -/
theorem boxes_length {σ : Type} [BEq σ] (column : Int) (l : List σ) :
    (boxes column l).length = (runs l).length := by
  have h := congrArg List.length (boxes_states column l)
  rw [List.length_map, List.length_map] at h
  exact h

/-- **With columns that are not negative, a box is inside its lane**: from `0` to `column` times
the count of the steps, with a width that is not negative. -/
theorem boxes_within {σ : Type} [BEq σ] (column : Int) (hc : 0 ≤ column) (l : List σ)
    (b : σ × Int × Int) (h : b ∈ boxes column l) :
    0 ≤ b.2.1 ∧ 0 ≤ b.2.2 ∧ b.2.1 + b.2.2 ≤ column * (l.length : Int) := by
  have h' := place_within column hc 0 (runs l) b h
  rw [runs_sum, Int.zero_add] at h'
  exact h'

/-- **A sequence that grows by a step of a new state: one box enters at the right.** Where the
sequence is empty or its last state is not `s`, the boxes of the sequence and `s` are its boxes
and one box of one column, in the column of the new step. No box drawn before changes. -/
theorem boxes_snoc_new {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List σ) (s : σ)
    (h : l.getLast? ≠ some s) :
    boxes column (l ++ [s]) = boxes column l ++ [(s, column * (l.length : Int), column)] := by
  show place column 0 (runs (l ++ [s])) = place column 0 (runs l) ++ _
  rw [runs_snoc_new l s h, place_append, runs_sum, Int.zero_add]
  show place column 0 (runs l) ++ [(s, column * (l.length : Int), column * 1)] = _
  rw [Int.mul_one]

/-- **A sequence that grows by a step of its last state: the last box is one column wider.** It
keeps its left edge, and no other box changes. -/
theorem boxes_snoc_same {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List σ) (s : σ)
    (h : l.getLast? = some s) :
    ∃ front x w, boxes column l = front ++ [(s, x, w)] ∧
      boxes column (l ++ [s]) = front ++ [(s, x, w + column)] := by
  obtain ⟨front, n, h1, h2⟩ := runs_snoc_same l s h
  have e : column * ((n + 1 : Nat) : Int) = column * (n : Int) + column := by
    rw [Int.natCast_add, Int.mul_add, Int.natCast_one, Int.mul_one]
  refine ⟨place column 0 front, 0 + column * ((front.map Prod.snd).sum : Nat), column * (n : Int),
    ?_, ?_⟩
  · show place column 0 (runs l) = _
    rw [h1, place_append]
    rfl
  · show place column 0 (runs (l ++ [s])) = _
    rw [h2, place_append, ← e]
    rfl

/-- **The law of a picture that grows.** When a sequence goes on by one step, one column enters
at the right of its lane: a new box of one column in the column of the new step, or the last
box one column wider at the same left edge. In both cases every box before the last is the box
that it was, at the same place. -/
theorem boxes_snoc {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List σ) (s : σ) :
    boxes column (l ++ [s]) = boxes column l ++ [(s, column * (l.length : Int), column)] ∨
      ∃ front x w, boxes column l = front ++ [(s, x, w)] ∧
        boxes column (l ++ [s]) = front ++ [(s, x, w + column)] := by
  rcases runs_snoc l s with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl (boxes_snoc_new column l s h)
  · exact Or.inr (boxes_snoc_same column l s h)

/-- **No earlier box changes when a step is added.** The boxes of a sequence without the last
one are the first boxes of the sequence with one more step, each with its state, its left edge
and its width. -/
theorem boxes_snoc_keeps {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List σ) (s : σ) :
    (boxes column l).dropLast <+: boxes column (l ++ [s]) := by
  rcases boxes_snoc column l s with h | ⟨front, x, w, h1, h2⟩
  · rw [h]
    exact List.IsPrefix.trans (List.dropLast_prefix _) (List.prefix_append _ _)
  · rw [h1, h2, List.dropLast_concat]
    exact List.prefix_append _ _

/-! ## Lanes -/

/-- A box moved `d` to the right. -/
def shift {α : Type} (d : Int) (b : α × Int × Int) : α × Int × Int := (b.1, b.2.1 + d, b.2.2)

/-- **The boxes that have a state.** A box of steps with no state is left out, and the others
keep their places. -/
def present {σ : Type} : List (Option σ × Int × Int) → List (σ × Int × Int)
  | [] => []
  | (none, _) :: rest => present rest
  | (some s, p) :: rest => (s, p) :: present rest

/-- **The lane of a key**: the boxes of its states, a column for each step from the left edge
`0`. The steps at which the key has no state (`none`) keep their columns and have no box:
absent is not a state. -/
def lane {σ : Type} [BEq σ] (column : Int) (states : List (Option σ)) : List (σ × Int × Int) :=
  present (boxes column states)

/-- **Lanes**: for each key the boxes of its states. A key with no state at a step (`none`) has
no box there. -/
def lanes {κ σ : Type} [BEq σ] (column : Int) (rows : List (κ × List (Option σ))) :
    List (κ × List (σ × Int × Int)) :=
  rows.map fun row => (row.1, lane column row.2)

/-- The boxes with a state, of two rows of boxes in a row. -/
theorem present_append {σ : Type} : ∀ a b : List (Option σ × Int × Int),
    present (a ++ b) = present a ++ present b
  | [], _ => rfl
  | (none, _) :: a, b => present_append a b
  | (some s, p) :: a, b => congrArg ((s, p) :: ·) (present_append a b)

/-- A box with a state is kept as it is, and no other box is. -/
theorem mem_present {σ : Type} (s : σ) (p : Int × Int) : ∀ bs : List (Option σ × Int × Int),
    (s, p) ∈ present bs ↔ (some s, p) ∈ bs
  | [] => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | (none, q) :: rest => by
    show (s, p) ∈ present rest ↔ (some s, p) ∈ (none, q) :: rest
    rw [mem_present s p rest]
    constructor
    · exact fun h => List.mem_cons_of_mem _ h
    · intro h
      rcases List.mem_cons.mp h with e | e
      · exact nomatch e
      · exact e
  | (some t, q) :: rest => by
    show (s, p) ∈ (t, q) :: present rest ↔ (some s, p) ∈ (some t, q) :: rest
    constructor
    · intro h
      rcases List.mem_cons.mp h with e | e
      · have e1 : s = t := congrArg Prod.fst e
        have e2 : p = q := congrArg Prod.snd e
        rw [e1, e2]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((mem_present s p rest).mp e)
    · intro h
      rcases List.mem_cons.mp h with e | e
      · have e1 : some s = some t := congrArg Prod.fst e
        have e2 : p = q := congrArg Prod.snd e
        rw [Option.some.inj e1, e2]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((mem_present s p rest).mpr e)

/-- Boxes that all have no state leave no box. -/
theorem present_eq_nil {σ : Type} : ∀ bs : List (Option σ × Int × Int),
    (∀ b ∈ bs, b.1 = none) → present bs = []
  | [], _ => rfl
  | (none, _) :: rest, h => present_eq_nil rest fun b hb => h b (List.mem_cons_of_mem _ hb)
  | (some s, p) :: _, h => nomatch h (some s, p) List.mem_cons_self

/-- The boxes with a state, moved, are the moved boxes with a state. -/
theorem present_shift {σ : Type} (d : Int) : ∀ bs : List (Option σ × Int × Int),
    present (bs.map (shift d)) = (present bs).map (shift d)
  | [] => rfl
  | (none, _) :: rest => present_shift d rest
  | (some s, p) :: rest => congrArg ((s, p.1 + d, p.2) :: ·) (present_shift d rest)

/-- Boxes from a left edge further right are the boxes, moved. -/
theorem place_shift {σ : Type} (column d : Int) : ∀ (start : Int) (rs : List (σ × Nat)),
    place column (start + d) rs = (place column start rs).map (shift d)
  | _, [] => rfl
  | start, (s, n) :: rs => by
    show (s, start + d, column * (n : Int)) :: place column (start + d + column * (n : Int)) rs =
      (s, start + d, column * (n : Int)) ::
        (place column (start + column * (n : Int)) rs).map (shift d)
    rw [← place_shift column d (start + column * (n : Int)) rs, Int.add_right_comm]

/-- **A box of a lane is a box of the states with their absences, and has a state.** The lane
is laid out with the absent steps in their columns, and those boxes are then left out. -/
theorem mem_lane {σ : Type} [BEq σ] (column : Int) (states : List (Option σ)) (s : σ)
    (p : Int × Int) : (s, p) ∈ lane column states ↔ (some s, p) ∈ boxes column states :=
  mem_present s p (boxes column states)

/-- The state of a box is a state of the sequence. -/
theorem boxes_mem {σ : Type} [BEq σ] (column : Int) (l : List σ) (b : σ × Int × Int)
    (h : b ∈ boxes column l) : b.1 ∈ l := by
  have h1 : b.1 ∈ (boxes column l).map Prod.fst := List.mem_map_of_mem h
  rw [boxes_states] at h1
  obtain ⟨r, hr, e⟩ := List.mem_map.mp h1
  rw [← e]
  exact runs_mem l r hr

/-- **A key with no state at any step has no box.** -/
theorem lane_none {σ : Type} [BEq σ] (column : Int) (states : List (Option σ))
    (h : ∀ o ∈ states, o = none) : lane column states = [] :=
  present_eq_nil (boxes column states) fun b hb => h b.1 (boxes_mem column states b hb)

/-- A step with no state before some runs is a run with no state, first. -/
theorem lead_none_shape {σ : Type} [BEq σ] : ∀ rs : List (Option σ × Nat),
    ∃ m rest, lead none rs = (none, m) :: rest
  | [] => ⟨1, [], rfl⟩
  | (none, n) :: more => ⟨n + 1, more, lead_same rfl n more⟩
  | (some v, n) :: more => ⟨1, (some v, n) :: more, lead_other rfl n more⟩

/-- A step with no state before some runs moves their boxes one column to the right, and has no
box of its own. -/
theorem present_lead_none {σ : Type} [BEq σ] (column : Int) :
    ∀ (start : Int) (rs : List (Option σ × Nat)),
      present (place column start (lead none rs)) = present (place column (start + column) rs)
  | _, [] => rfl
  | start, (none, n) :: more => by
    have e : start + column * ((n + 1 : Nat) : Int) = start + column + column * (n : Int) := by
      rw [Int.natCast_add, Int.mul_add, Int.natCast_one, Int.mul_one]
      omega
    rw [lead_same rfl n more]
    show present (place column (start + column * ((n + 1 : Nat) : Int)) more) =
      present (place column (start + column + column * (n : Int)) more)
    rw [e]
  | start, (some v, n) :: more => by
    rw [lead_other rfl n more]
    show present (place column (start + column * 1) ((some v, n) :: more)) = _
    rw [Int.mul_one]

/-- The boxes with a state, of runs before a run with no state: the boxes of the runs, and then
the boxes of what follows from where the runs end. The two rows of runs make one run only where
both have no state, and that run has no box. -/
theorem present_glue_none {σ : Type} [BEq σ] (column : Int) (m : Nat)
    (rest : List (Option σ × Nat)) : ∀ (start : Int) (front : List (Option σ × Nat)),
      present (place column start (glue front ((none, m) :: rest))) =
        present (place column start front) ++
          present (place column (start + column * ((front.map Prod.snd).sum : Nat))
            ((none, m) :: rest))
  | start, [] => by
    show _ = present (place column (start + column * 0) ((none, m) :: rest))
    rw [Int.mul_zero, Int.add_zero]
    rfl
  | start, [(none, n)] => by
    rw [glue_same rfl]
    show present (place column (start + column * ((n + m : Nat) : Int)) rest) =
      present (place column (start + column * ((n + 0 : Nat) : Int) + column * (m : Int)) rest)
    rw [Nat.add_zero, Int.natCast_add, Int.mul_add, Int.add_assoc]
  | start, [(some v, n)] => by
    rw [glue_other rfl]
    show (v, start, column * (n : Int)) ::
        present (place column (start + column * (n : Int)) ((none, m) :: rest)) =
      (v, start, column * (n : Int)) ::
        present (place column (start + column * ((n + 0 : Nat) : Int)) ((none, m) :: rest))
    rw [Nat.add_zero]
  | start, (o, k) :: r' :: front => by
    have ih := present_glue_none column m rest (start + column * (k : Int)) (r' :: front)
    have e : start + column * ((((o, k) :: r' :: front).map Prod.snd).sum : Nat) =
        start + column * (k : Int) + column * (((r' :: front).map Prod.snd).sum : Nat) := by
      show start + column * ((k + ((r' :: front).map Prod.snd).sum : Nat) : Int) = _
      rw [Int.natCast_add, Int.mul_add, Int.add_assoc]
    rw [e]
    cases o with
    | none => exact ih
    | some v => exact congrArg ((v, start, column * (k : Int)) :: ·) ih

/-- **How a lane with a hole is laid out.** The lane of a sequence with an absent step is the
lane of what is before the step, and then the lane of what is after it, moved to the right by
the columns before the step and one more. The hole keeps its column, and the boxes on its two
sides are two boxes, with one state or with two. -/
theorem lane_hole {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (a c : List (Option σ)) :
    lane column (a ++ none :: c) =
      lane column a ++ (lane column c).map (shift (column * ((a.length : Int) + 1))) := by
  obtain ⟨m, rest, hm⟩ := lead_none_shape (runs c)
  have e1 : runs (a ++ none :: c) = glue (runs a) (lead none (runs c)) := runs_append a (none :: c)
  show present (place column 0 (runs (a ++ none :: c))) =
    present (place column 0 (runs a)) ++
      (present (place column 0 (runs c))).map (shift (column * ((a.length : Int) + 1)))
  rw [e1, hm, present_glue_none, ← hm, present_lead_none, runs_sum, ← present_shift,
    ← place_shift, Int.mul_add, Int.mul_one, Int.add_assoc]

/-- **A key has no box at a step where it has no state.** With columns that are not negative,
every box of the lane ends at the column of an absent step or before it, or starts after that
column. So the two boxes on the sides of a hole do not cover it. -/
theorem lane_absent {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (hc : 0 ≤ column)
    (a c : List (Option σ)) (b : σ × Int × Int) (h : b ∈ lane column (a ++ none :: c)) :
    b.2.1 + b.2.2 ≤ column * (a.length : Int) ∨ column * ((a.length : Int) + 1) ≤ b.2.1 := by
  rw [lane_hole] at h
  rcases List.mem_append.mp h with h | h
  · have hb : (some b.1, b.2) ∈ boxes column a := (mem_lane column a b.1 b.2).mp h
    exact Or.inl (boxes_within column hc a _ hb).2.2
  · obtain ⟨b', hb', e⟩ := List.mem_map.mp h
    have hb : (some b'.1, b'.2) ∈ boxes column c := (mem_lane column c b'.1 b'.2).mp hb'
    have h0 : 0 ≤ b'.2.1 := (boxes_within column hc c _ hb).1
    rw [← e]
    show _ ∨ column * ((a.length : Int) + 1) ≤ b'.2.1 + column * ((a.length : Int) + 1)
    exact Or.inr (by omega)

/-- A step with a state before some runs with a state. -/
theorem lead_some {σ : Type} [BEq σ] (s : σ) : ∀ rs : List (σ × Nat),
    lead (some s) (rs.map fun r => (some r.1, r.2)) = (lead s rs).map fun r => (some r.1, r.2)
  | [] => rfl
  | (t, n) :: more => by
    cases h : s == t with
    | true =>
      rw [lead_same h]
      exact lead_same (s := some s) (t := some t) h n _
    | false =>
      rw [lead_other h]
      exact lead_other (s := some s) (t := some t) h n _

/-- The runs of a sequence where every step has a state are the runs of the states. -/
theorem runs_map_some {σ : Type} [BEq σ] : ∀ l : List σ,
    runs (l.map some) = (runs l).map fun r => (some r.1, r.2)
  | [] => rfl
  | s :: rest => by
    show lead (some s) (runs (rest.map some)) = (lead s (runs rest)).map fun r => (some r.1, r.2)
    rw [runs_map_some rest, lead_some]

/-- The boxes of runs with a state are all kept. -/
theorem present_place_some {σ : Type} (column : Int) : ∀ (start : Int) (rs : List (σ × Nat)),
    present (place column start (rs.map fun r => (some r.1, r.2))) = place column start rs
  | _, [] => rfl
  | start, (s, n) :: rs =>
    congrArg ((s, start, column * (n : Int)) :: ·)
      (present_place_some column (start + column * (n : Int)) rs)

/-- **The lane of a key that has a state at every step is the boxes of its states.** -/
theorem lane_some {σ : Type} [BEq σ] (column : Int) (l : List σ) :
    lane column (l.map some) = boxes column l := by
  show present (place column 0 (runs (l.map some))) = place column 0 (runs l)
  rw [runs_map_some, present_place_some]

/-- **A step with no state changes nothing in the lane.** A key that has exited, or waits to be
forked, has the lane that it had. -/
theorem lane_snoc_none {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List (Option σ)) :
    lane column (l ++ [none]) = lane column l := by
  show present (boxes column (l ++ [none])) = present (boxes column l)
  rcases boxes_snoc column l none with h | ⟨front, x, w, h1, h2⟩
  · rw [h, present_append]
    exact List.append_nil _
  · rw [h1, h2, present_append, present_append]
    rfl

/-- **A step of a new state is one new box in the lane**, in the column of the step. It is so
where the sequence is empty, and where the key had no state at the step before, or another
state. No box drawn before changes. -/
theorem lane_snoc_new {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List (Option σ))
    (s : σ) (h : l.getLast? ≠ some (some s)) :
    lane column (l ++ [some s]) = lane column l ++ [(s, column * (l.length : Int), column)] := by
  show present (boxes column (l ++ [some s])) = present (boxes column l) ++ _
  rw [boxes_snoc_new column l (some s) h, present_append]
  rfl

/-- **A step of the state of the step before makes the last box of the lane one column wider.**
It keeps its left edge, and no other box changes. -/
theorem lane_snoc_same {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List (Option σ))
    (s : σ) (h : l.getLast? = some (some s)) :
    ∃ front x w, lane column l = front ++ [(s, x, w)] ∧
      lane column (l ++ [some s]) = front ++ [(s, x, w + column)] := by
  obtain ⟨front, x, w, h1, h2⟩ := boxes_snoc_same column l (some s) h
  refine ⟨present front, x, w, ?_, ?_⟩
  · show present (boxes column l) = _
    rw [h1, present_append]
    rfl
  · show present (boxes column (l ++ [some s])) = _
    rw [h2, present_append]
    rfl

/-- **The law of a lane that grows.** When a key has a state at one more step, one column enters
at the right of its lane: a new box of one column in the column of the step, or the last box
one column wider at the same left edge. Every box before the last is the box that it was. -/
theorem lane_snoc_some {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List (Option σ))
    (s : σ) :
    lane column (l ++ [some s]) = lane column l ++ [(s, column * (l.length : Int), column)] ∨
      ∃ front x w, lane column l = front ++ [(s, x, w)] ∧
        lane column (l ++ [some s]) = front ++ [(s, x, w + column)] := by
  rcases runs_snoc l (some s) with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl (lane_snoc_new column l s h)
  · exact Or.inr (lane_snoc_same column l s h)

/-- **No earlier box of a lane changes when the run goes on by one step**, with a state or with
none. The boxes of the lane without the last one are the first boxes of the lane after the
step. -/
theorem lane_snoc_keeps {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (l : List (Option σ))
    (o : Option σ) : (lane column l).dropLast <+: lane column (l ++ [o]) := by
  cases o with
  | none =>
    rw [lane_snoc_none]
    exact List.dropLast_prefix _
  | some s =>
    rcases lane_snoc_some column l s with h | ⟨front, x, w, h1, h2⟩
    · rw [h]
      exact List.IsPrefix.trans (List.dropLast_prefix _) (List.prefix_append _ _)
    · rw [h1, h2, List.dropLast_concat]
      exact List.prefix_append _ _

/-- The lanes have the keys of the rows, in order. -/
theorem lanes_keys {κ σ : Type} [BEq σ] (column : Int) (rows : List (κ × List (Option σ))) :
    (lanes column rows).map Prod.fst = rows.map Prod.fst := by
  show (rows.map fun row => (row.1, lane column row.2)).map Prod.fst = rows.map Prod.fst
  rw [List.map_map]
  rfl

/-- **A lane of the lanes is the lane of a row**, with the key of the row. So every law of
`lane` is a law of each lane of a picture. -/
theorem mem_lanes {κ σ : Type} [BEq σ] (column : Int) (rows : List (κ × List (Option σ)))
    (k : κ) (bs : List (σ × Int × Int)) :
    (k, bs) ∈ lanes column rows ↔ ∃ states, (k, states) ∈ rows ∧ bs = lane column states := by
  constructor
  · intro h
    obtain ⟨row, hrow, e⟩ := List.mem_map.mp h
    have e1 : row.1 = k := congrArg Prod.fst e
    have e2 : lane column row.2 = bs := congrArg Prod.snd e
    exact ⟨row.2, by rw [← e1]; exact hrow, e2.symm⟩
  · intro ⟨states, hrow, e⟩
    rw [e]
    exact List.mem_map.mpr ⟨(k, states), hrow, rfl⟩

/-! ## Every step is in one box -/

/-- A law of every list that holds of the empty list, and of a list and one last member where
it holds of the list. -/
private theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l : List α, motive l := by
  intro l
  have h : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact nil
    | cons a r ih =>
      rw [List.reverse_cons]
      exact snoc _ a ih
  have e := h l.reverse
  rw [List.reverse_reverse] at e
  exact e

/-- Of two members of a list whose members stand in a relation, each with every later one, the
two are one, or one of them stands in the relation with the other. -/
private theorem pairwise_mem {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ a ∈ l, ∀ b ∈ l, a = b ∨ R a b ∨ R b a
  | [], _, _, ha, _, _ => nomatch ha
  | x :: l, h, a, ha, b, hb => by
    have h' := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with ea | ha'
    · rcases List.mem_cons.mp hb with eb | hb'
      · exact Or.inl (ea.trans eb.symm)
      · exact Or.inr (Or.inl (ea ▸ h'.1 b hb'))
    · rcases List.mem_cons.mp hb with eb | hb'
      · exact Or.inr (Or.inr (eb ▸ h'.1 a ha'))
      · exact pairwise_mem h'.2 a ha' b hb'

/-- With columns that are not negative, a box ends before every later box starts. -/
theorem place_ordered {σ : Type} (column : Int) (hc : 0 ≤ column) :
    ∀ (start : Int) (rs : List (σ × Nat)),
      (place column start rs).Pairwise fun a b => a.2.1 + a.2.2 ≤ b.2.1
  | _, [] => List.Pairwise.nil
  | start, (s, n) :: rs => by
    show ((s, start, column * (n : Int)) :: place column (start + column * (n : Int)) rs).Pairwise
      fun a b => a.2.1 + a.2.2 ≤ b.2.1
    exact List.Pairwise.cons (fun b hb => (place_within column hc _ rs b hb).1)
      (place_ordered column hc _ rs)

/-- **Left means earlier.** With columns that are not negative, a box of a lane ends at the left
edge of every later box, or before it. -/
theorem boxes_ordered {σ : Type} [BEq σ] (column : Int) (hc : 0 ≤ column) (l : List σ) :
    (boxes column l).Pairwise fun a b => a.2.1 + a.2.2 ≤ b.2.1 :=
  place_ordered column hc 0 (runs l)

/-- **No place is in two boxes.** With columns that are not negative, two boxes of a lane that
hold one place are one box. -/
theorem boxes_one {σ : Type} [BEq σ] (column : Int) (hc : 0 ≤ column) (l : List σ) (p : Int)
    (b b' : σ × Int × Int) (hb : b ∈ boxes column l) (hb' : b' ∈ boxes column l)
    (h1 : b.2.1 ≤ p) (h2 : p < b.2.1 + b.2.2) (h1' : b'.2.1 ≤ p) (h2' : p < b'.2.1 + b'.2.2) :
    b = b' := by
  rcases pairwise_mem (boxes_ordered column hc l) b hb b' hb' with e | h | h
  · exact e
  · exact absurd h (by omega)
  · exact absurd h (by omega)

/-- **Every step is in a box of its state.** With columns that are not negative, the column of a
step lies in a box of the lane, and that box has the state of the step. With `boxes_one` it is
the one box that holds the column. -/
theorem boxes_cover {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (hc : 0 ≤ column)
    (a : List σ) (s : σ) (c : List σ) :
    ∃ x w, (s, x, w) ∈ boxes column (a ++ s :: c) ∧ x ≤ column * (a.length : Int) ∧
      column * ((a.length : Int) + 1) ≤ x + w := by
  have hm : column * ((a.length : Int) + 1) = column * (a.length : Int) + column := by
    rw [Int.mul_add, Int.mul_one]
  rw [hm]
  refine snoc_induction (motive := fun c => ∃ x w, (s, x, w) ∈ boxes column (a ++ s :: c) ∧
    x ≤ column * (a.length : Int) ∧ column * (a.length : Int) + column ≤ x + w) ?_ ?_ c
  · rcases boxes_snoc column a s with h | ⟨front, x, w, h1, h2⟩
    · refine ⟨column * (a.length : Int), column, ?_, Int.le_refl _, Int.le_refl _⟩
      rw [h]
      exact List.mem_append_right _ List.mem_cons_self
    · have hmem : (s, x, w) ∈ boxes column a := by
        rw [h1]
        exact List.mem_append_right _ List.mem_cons_self
      have hw : 0 ≤ w := (boxes_within column hc a _ hmem).2.1
      have hl : (boxes column a).getLast? = some (s, x, w) := by
        rw [h1]
        exact getLast?_snoc _ front
      have he : x + w = column * (a.length : Int) := boxes_end column a _ hl
      refine ⟨x, w + column, ?_, ?_, ?_⟩
      · rw [h2]
        exact List.mem_append_right _ List.mem_cons_self
      · omega
      · omega
  · intro c t ⟨x, w, hin, g1, g2⟩
    have e : a ++ s :: (c ++ [t]) = (a ++ s :: c) ++ [t] := (List.append_assoc a (s :: c) [t]).symm
    rw [e]
    rcases boxes_snoc column (a ++ s :: c) t with h | ⟨front, x', w', h1, h2⟩
    · refine ⟨x, w, ?_, g1, g2⟩
      rw [h]
      exact List.mem_append_left _ hin
    · rw [h1] at hin
      rcases List.mem_append.mp hin with hf | hl
      · refine ⟨x, w, ?_, g1, g2⟩
        rw [h2]
        exact List.mem_append_left _ hf
      · have eq : (s, x, w) = (t, x', w') := List.mem_singleton.mp hl
        have e1 : s = t := congrArg Prod.fst eq
        have e2 : x = x' := congrArg (fun b => b.2.1) eq
        have e3 : w = w' := congrArg (fun b => b.2.2) eq
        refine ⟨x, w + column, ?_, g1, ?_⟩
        · rw [h2, e1, e2, e3]
          exact List.mem_append_right _ List.mem_cons_self
        · omega

/-- **A step with a state is in a box of its lane, and the box has that state.** With columns
that are not negative. With `lane_one` it is the one box that holds the column of the step. -/
theorem lane_cover {σ : Type} [BEq σ] [LawfulBEq σ] (column : Int) (hc : 0 ≤ column)
    (a : List (Option σ)) (s : σ) (c : List (Option σ)) :
    ∃ x w, (s, x, w) ∈ lane column (a ++ some s :: c) ∧ x ≤ column * (a.length : Int) ∧
      column * ((a.length : Int) + 1) ≤ x + w := by
  obtain ⟨x, w, hin, h1, h2⟩ := boxes_cover column hc a (some s) c
  exact ⟨x, w, (mem_lane column _ s (x, w)).mpr hin, h1, h2⟩

/-- **No place is in two boxes of a lane.** With columns that are not negative. -/
theorem lane_one {σ : Type} [BEq σ] (column : Int) (hc : 0 ≤ column) (l : List (Option σ))
    (p : Int) (b b' : σ × Int × Int) (hb : b ∈ lane column l) (hb' : b' ∈ lane column l)
    (h1 : b.2.1 ≤ p) (h2 : p < b.2.1 + b.2.2) (h1' : b'.2.1 ≤ p) (h2' : p < b'.2.1 + b'.2.2) :
    b = b' := by
  have e := boxes_one column hc l p (some b.1, b.2) (some b'.1, b'.2)
    ((mem_lane column l b.1 b.2).mp hb) ((mem_lane column l b'.1 b'.2).mp hb') h1 h2 h1' h2'
  have e1 : b.1 = b'.1 :=
    Option.some.inj (congrArg (fun m : Option σ × Int × Int => m.1) e)
  have e2 : b.2 = b'.2 := congrArg (fun m : Option σ × Int × Int => m.2) e
  exact Prod.ext e1 e2

/-! ## A small line -/

/-- The points of some values from the column `i` on. -/
def lineFrom (scale : Scale) (column : Int) : Nat → List Int → List IVec
  | _, [] => []
  | i, v :: vs => ⟨column * (i : Int), scale.at v⟩ :: lineFrom scale column (i + 1) vs

/-- **A sequence of quantities as points**: the `i`-th value in the column `i`, at the height
that the scale gives it. -/
def line (scale : Scale) (column : Int) (values : List Int) : List IVec :=
  lineFrom scale column 0 values

/-- There is a point for each value. -/
theorem lineFrom_length (scale : Scale) (column : Int) : ∀ (i : Nat) (values : List Int),
    (lineFrom scale column i values).length = values.length
  | _, [] => rfl
  | i, _ :: vs => congrArg (· + 1) (lineFrom_length scale column (i + 1) vs)

/-- **A small line has a point for each value.** -/
theorem line_length (scale : Scale) (column : Int) (values : List Int) :
    (line scale column values).length = values.length :=
  lineFrom_length scale column 0 values

/-- The `k`-th point from the column `i` on is in the column `i + k`. -/
theorem lineFrom_get (scale : Scale) (column : Int) : ∀ (i : Nat) (values : List Int) (k : Nat),
    (lineFrom scale column i values)[k]? =
      values[k]?.map fun v => (⟨column * ((i + k : Nat) : Int), scale.at v⟩ : IVec)
  | _, [], _ => by
    show ([] : List IVec)[_]? = ([] : List Int)[_]?.map _
    rw [List.getElem?_nil, List.getElem?_nil]
    rfl
  | i, v :: vs, 0 => by
    show ((⟨column * (i : Int), scale.at v⟩ : IVec) :: lineFrom scale column (i + 1) vs)[0]? = _
    rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
    rfl
  | i, v :: vs, k + 1 => by
    show ((⟨column * (i : Int), scale.at v⟩ : IVec) :: lineFrom scale column (i + 1) vs)[k + 1]? = _
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ, lineFrom_get scale column (i + 1) vs k,
      Nat.add_right_comm i 1 k]
    rfl

/-- **Left means earlier, and a height says a quantity.** The point of the `i`-th value has the
abscissa `column * i`, and the ordinate that the scale gives the value. -/
theorem line_across (scale : Scale) (column : Int) (values : List Int) (i : Nat) :
    (line scale column values)[i]? =
      values[i]?.map fun v => (⟨column * (i : Int), scale.at v⟩ : IVec) := by
  have h := lineFrom_get scale column 0 values i
  rw [Nat.zero_add] at h
  exact h

/-- The point of a value of the sequence. -/
theorem line_point (scale : Scale) (column : Int) (values : List Int) {i : Nat} {a : Int}
    (h : values[i]? = some a) :
    (line scale column values)[i]? = some ⟨column * (i : Int), scale.at a⟩ := by
  rw [line_across, h]
  rfl

/-- **On a scale that rises, a greater value is never drawn at a lesser ordinate.** The
direction is the scale's own: a caller whose ordinates grow downward gives a scale that falls,
and has `line_anti`. -/
theorem line_mono (scale : Scale) (hs : scale.Rising) (column : Int) (values : List Int)
    {i j : Nat} {a b : Int} {p q : IVec} (ha : values[i]? = some a) (hb : values[j]? = some b)
    (hp : (line scale column values)[i]? = some p) (hq : (line scale column values)[j]? = some q)
    (hab : a ≤ b) : p.y ≤ q.y := by
  rw [line_point scale column values ha] at hp
  rw [line_point scale column values hb] at hq
  rw [← Option.some.inj hp, ← Option.some.inj hq]
  exact Scale.at_mono scale hs hab

/-- **On a scale that falls, a greater value is never drawn at a greater ordinate.** On a screen
whose ordinates grow downward, a greater value is never drawn lower. -/
theorem line_anti (scale : Scale) (hs : scale.Falling) (column : Int) (values : List Int)
    {i j : Nat} {a b : Int} {p q : IVec} (ha : values[i]? = some a) (hb : values[j]? = some b)
    (hp : (line scale column values)[i]? = some p) (hq : (line scale column values)[j]? = some q)
    (hab : a ≤ b) : q.y ≤ p.y := by
  rw [line_point scale column values ha] at hp
  rw [line_point scale column values hb] at hq
  rw [← Option.some.inj hp, ← Option.some.inj hq]
  exact Scale.at_anti scale hs hab

/-- **Equal values are level**, on every scale. -/
theorem line_level (scale : Scale) (column : Int) (values : List Int) {i j : Nat} {a : Int}
    {p q : IVec} (ha : values[i]? = some a) (hb : values[j]? = some a)
    (hp : (line scale column values)[i]? = some p) (hq : (line scale column values)[j]? = some q) :
    p.y = q.y := by
  rw [line_point scale column values ha] at hp
  rw [line_point scale column values hb] at hq
  rw [← Option.some.inj hp, ← Option.some.inj hq]

/-- The points of two rows of values in a row. -/
theorem lineFrom_append (scale : Scale) (column : Int) : ∀ (i : Nat) (vs ws : List Int),
    lineFrom scale column i (vs ++ ws) =
      lineFrom scale column i vs ++ lineFrom scale column (i + vs.length) ws
  | _, [], _ => rfl
  | i, v :: vs, ws => by
    show (⟨column * (i : Int), scale.at v⟩ : IVec) :: lineFrom scale column (i + 1) (vs ++ ws) =
      (⟨column * (i : Int), scale.at v⟩ : IVec) ::
        (lineFrom scale column (i + 1) vs ++ lineFrom scale column (i + (vs.length + 1)) ws)
    rw [lineFrom_append scale column (i + 1) vs ws, Nat.add_right_comm i 1 vs.length]
    rfl

/-- **A small line that grows by one value is the line and one more point**, in the column of
the new value. No point drawn before moves. -/
theorem line_snoc (scale : Scale) (column : Int) (values : List Int) (v : Int) :
    line scale column (values ++ [v]) =
      line scale column values ++ [⟨column * (values.length : Int), scale.at v⟩] := by
  show lineFrom scale column 0 (values ++ [v]) = _
  rw [lineFrom_append, Nat.zero_add]
  rfl

/-! ## The three marks of a small line -/

/-- The column and the value of the first of `v :: vs` that `le` puts before every other. Of
two values that `le` puts before every other, it is the one further left. -/
def pick (le : Int → Int → Bool) : Int → List Int → Nat × Int
  | v, [] => (0, v)
  | v, w :: ws =>
    if le v (pick le w ws).2 then (0, v) else ((pick le w ws).1 + 1, (pick le w ws).2)

/-- **The columns of the least value, the greatest and the last**: the three marks of a small
line. Where the least value stands in two columns or more, the mark is at the one furthest
left, and so for the greatest. A sequence with no value has no mark. -/
def marks : List Int → Option (Nat × Nat × Nat)
  | [] => none
  | v :: vs =>
    some ((pick (fun a b => decide (a ≤ b)) v vs).1, (pick (fun a b => decide (b ≤ a)) v vs).1,
      vs.length)

/-- The picked column holds the picked value. -/
theorem pick_get (le : Int → Int → Bool) : ∀ (v : Int) (vs : List Int),
    (v :: vs)[(pick le v vs).1]? = some (pick le v vs).2
  | _, [] => rfl
  | v, w :: ws => by
    cases h : le v (pick le w ws).2 with
    | true =>
      have e : pick le v (w :: ws) = (0, v) := if_pos h
      rw [e]
      rfl
    | false =>
      have e : pick le v (w :: ws) = ((pick le w ws).1 + 1, (pick le w ws).2) :=
        if_neg (ne_true_of_eq_false h)
      rw [e]
      show (v :: w :: ws)[(pick le w ws).1 + 1]? = some (pick le w ws).2
      rw [List.getElem?_cons_succ]
      exact pick_get le w ws

/-- The picked column is a column of the sequence. -/
theorem pick_le (le : Int → Int → Bool) : ∀ (v : Int) (vs : List Int),
    (pick le v vs).1 ≤ vs.length
  | _, [] => Nat.le_refl 0
  | v, w :: ws => by
    cases h : le v (pick le w ws).2 with
    | true =>
      have e : pick le v (w :: ws) = (0, v) := if_pos h
      rw [e]
      exact Nat.zero_le _
    | false =>
      have e : pick le v (w :: ws) = ((pick le w ws).1 + 1, (pick le w ws).2) :=
        if_neg (ne_true_of_eq_false h)
      rw [e]
      exact Nat.succ_le_succ (pick_le le w ws)

/-- The picked value is before every value, where `le` is an order of every two values. -/
theorem pick_best (le : Int → Int → Bool) (total : ∀ a b, le a b = false → le b a = true)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true) :
    ∀ (v : Int) (vs : List Int) (x : Int), x ∈ v :: vs → le (pick le v vs).2 x = true := by
  have refl : ∀ a, le a a = true := by
    intro a
    cases h : le a a with
    | true => rfl
    | false =>
      have t := total a a h
      rw [h] at t
      exact t
  intro v vs
  induction vs generalizing v with
  | nil =>
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · rw [e]
      exact refl v
    · exact nomatch e
  | cons w ws ih =>
    intro x hx
    cases h : le v (pick le w ws).2 with
    | true =>
      have e : pick le v (w :: ws) = (0, v) := if_pos h
      rw [e]
      rcases List.mem_cons.mp hx with ex | hx'
      · rw [ex]
        exact refl v
      · exact trans v _ x h (ih w x hx')
    | false =>
      have e : pick le v (w :: ws) = ((pick le w ws).1 + 1, (pick le w ws).2) :=
        if_neg (ne_true_of_eq_false h)
      rw [e]
      rcases List.mem_cons.mp hx with ex | hx'
      · rw [ex]
        exact total v _ h
      · exact ih w x hx'

/-- No value left of the picked column is before the picked value. -/
theorem pick_first (le : Int → Int → Bool) : ∀ (v : Int) (vs : List Int) (j : Nat) (x : Int),
    j < (pick le v vs).1 → (v :: vs)[j]? = some x → le x (pick le v vs).2 = false
  | _, [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | v, w :: ws, j, x, hj, hx => by
    cases h : le v (pick le w ws).2 with
    | true =>
      have e : pick le v (w :: ws) = (0, v) := if_pos h
      rw [e] at hj
      exact absurd hj (Nat.not_lt_zero _)
    | false =>
      have e : pick le v (w :: ws) = ((pick le w ws).1 + 1, (pick le w ws).2) :=
        if_neg (ne_true_of_eq_false h)
      rw [e] at hj
      rw [e]
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at hx
        rw [← Option.some.inj hx]
        exact h
      | succ j =>
        rw [List.getElem?_cons_succ] at hx
        exact pick_first le w ws j x (Nat.lt_of_succ_lt_succ hj) hx

/-- **A sequence has marks exactly where it has a value.** -/
theorem marks_eq_none (values : List Int) : marks values = none ↔ values = [] := by
  cases values with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons v vs => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- **The third mark is the last column.** -/
theorem marks_last {values : List Int} {lo hi last : Nat}
    (h : marks values = some (lo, hi, last)) : last + 1 = values.length := by
  cases values with
  | nil => exact nomatch h
  | cons v vs =>
    have e := Option.some.inj h
    have e3 : vs.length = last := congrArg (fun m => m.2.2) e
    rw [← e3]
    rfl

/-- **The three marks are columns of the sequence.** -/
theorem marks_inside {values : List Int} {lo hi last : Nat}
    (h : marks values = some (lo, hi, last)) :
    lo < values.length ∧ hi < values.length ∧ last < values.length := by
  cases values with
  | nil => exact nomatch h
  | cons v vs =>
    have e := Option.some.inj h
    have e1 : (pick (fun a b => decide (a ≤ b)) v vs).1 = lo := congrArg Prod.fst e
    have e2 : (pick (fun a b => decide (b ≤ a)) v vs).1 = hi := congrArg (fun m => m.2.1) e
    have e3 : vs.length = last := congrArg (fun m => m.2.2) e
    rw [← e1, ← e2, ← e3]
    exact ⟨Nat.lt_succ_of_le (pick_le _ v vs), Nat.lt_succ_of_le (pick_le _ v vs),
      Nat.lt_succ_self _⟩

/-- **The first mark is at the least value, in the column furthest left that has it.** The
value there is no more than every value, and less than every value left of it. -/
theorem marks_least {values : List Int} {lo hi last : Nat}
    (h : marks values = some (lo, hi, last)) :
    ∃ a, values[lo]? = some a ∧ (∀ x ∈ values, a ≤ x) ∧
      ∀ (j : Nat) (x : Int), j < lo → values[j]? = some x → a < x := by
  cases values with
  | nil => exact nomatch h
  | cons v vs =>
    have e1 : (pick (fun a b => decide (a ≤ b)) v vs).1 = lo :=
      congrArg Prod.fst (Option.some.inj h)
    rw [← e1]
    refine ⟨(pick (fun a b => decide (a ≤ b)) v vs).2, pick_get _ v vs, ?_, ?_⟩
    · intro x hx
      exact of_decide_eq_true (pick_best (fun a b => decide (a ≤ b))
        (fun a b hab => decide_eq_true (Int.le_of_lt (Int.not_le.mp (of_decide_eq_false hab))))
        (fun a b c hab hbc =>
          decide_eq_true (Int.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
        v vs x hx)
    · intro j x hj hx
      exact Int.not_le.mp (of_decide_eq_false (pick_first _ v vs j x hj hx))

/-- **The second mark is at the greatest value, in the column furthest left that has it.** The
value there is no less than every value, and more than every value left of it. -/
theorem marks_greatest {values : List Int} {lo hi last : Nat}
    (h : marks values = some (lo, hi, last)) :
    ∃ b, values[hi]? = some b ∧ (∀ x ∈ values, x ≤ b) ∧
      ∀ (j : Nat) (x : Int), j < hi → values[j]? = some x → x < b := by
  cases values with
  | nil => exact nomatch h
  | cons v vs =>
    have e2 : (pick (fun a b => decide (b ≤ a)) v vs).1 = hi :=
      congrArg (fun m => m.2.1) (Option.some.inj h)
    rw [← e2]
    refine ⟨(pick (fun a b => decide (b ≤ a)) v vs).2, pick_get _ v vs, ?_, ?_⟩
    · intro x hx
      exact of_decide_eq_true (pick_best (fun a b => decide (b ≤ a))
        (fun a b hab => decide_eq_true (Int.le_of_lt (Int.not_le.mp (of_decide_eq_false hab))))
        (fun a b c hab hbc =>
          decide_eq_true (Int.le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
        v vs x hx)
    · intro j x hj hx
      exact Int.not_le.mp (of_decide_eq_false (pick_first _ v vs j x hj hx))

/-! ## Controls

A race of three fibers and their parent, over a run of eight steps, with a column `10` wide. The
parent forks `a`, `b` and `c` at its first three steps and waits. The fiber `a` wins at the step
`5`. The two others are interrupted at the step `6`, and the parent goes on at the step `7`. A
fiber has no state before it is forked and none after it has ended. -/

/-- The states of a fiber in the controls. -/
private inductive Phase where
  /-- The fiber computes. -/
  | running
  /-- The fiber waits for another fiber. -/
  | waiting
  /-- The fiber has ended with a result. -/
  | done
  /-- The fiber was stopped by another fiber. -/
  | interrupted
  deriving DecidableEq

/-- The run of the race: for each fiber its state at each of the eight steps, or none. -/
private def race : List (String × List (Option Phase)) :=
  [("parent", [some .running, some .running, some .running, some .waiting, some .waiting,
      some .waiting, some .waiting, some .running]),
    ("a", [none, some .running, some .running, some .running, some .running, some .done, none,
      none]),
    ("b", [none, none, some .running, some .running, some .waiting, some .waiting,
      some .interrupted, none]),
    ("c", [none, none, none, some .running, some .running, some .running, some .interrupted,
      none])]

/-- A run with one more step: each fiber's state at the new step, in the order of the rows. -/
private def after (rows : List (String × List (Option Phase))) (step : List (Option Phase)) :
    List (String × List (Option Phase)) :=
  (rows.zip step).map fun p => (p.1.1, p.1.2 ++ [p.2])

-- The four lanes. The race is a shape: the lanes of the two losers end one column after the
-- lane of the winner, and no lane starts before its fiber is forked.
#guard lanes 10 race =
  [("parent", [(Phase.running, 0, 30), (Phase.waiting, 30, 40), (Phase.running, 70, 10)]),
    ("a", [(Phase.running, 10, 40), (Phase.done, 50, 10)]),
    ("b", [(Phase.running, 20, 20), (Phase.waiting, 40, 20), (Phase.interrupted, 60, 10)]),
    ("c", [(Phase.running, 30, 30), (Phase.interrupted, 60, 10)])]
#guard ((lanes 10 race).map fun l => l.2.getLast?.map fun b => b.2.1 + b.2.2) =
  [some 80, some 60, some 70, some 70]

-- The run goes on by one step, at which the parent still runs. The last box of its lane is one
-- column wider, at the same left edge. The three other fibers have no state, and their lanes
-- are the lanes that they were.
#guard lanes 10 (after race [some .running, none, none, none]) =
  [("parent", [(Phase.running, 0, 30), (Phase.waiting, 30, 40), (Phase.running, 70, 20)]),
    ("a", [(Phase.running, 10, 40), (Phase.done, 50, 10)]),
    ("b", [(Phase.running, 20, 20), (Phase.waiting, 40, 20), (Phase.interrupted, 60, 10)]),
    ("c", [(Phase.running, 30, 30), (Phase.interrupted, 60, 10)])]

-- The run goes on by one step, at which the parent ends. One box enters at the right of its
-- lane, in the column `8`, and its three boxes before are the boxes that they were.
#guard (lanes 10 (after race [some .done, none, none, none])).head? =
  some ("parent", [(Phase.running, 0, 30), (Phase.waiting, 30, 40), (Phase.running, 70, 10),
    (Phase.done, 80, 10)])

-- A lane with a hole: a fiber that is absent at the steps `2` and `3`, and runs before and
-- after. The two boxes on the sides of the hole are two boxes, and no box holds the columns
-- from `20` to `40`. Read as a state, the absence would be a box of its own.
#guard lane 10 [some Phase.running, some .running, none, none, some .running, some .done] =
  [(Phase.running, 0, 20), (Phase.running, 40, 10), (Phase.done, 50, 10)]
#guard boxes 10 [some Phase.running, some .running, none, none, some .running, some .done] =
  [(some Phase.running, 0, 20), (none, 20, 20), (some Phase.running, 40, 10),
    (some Phase.done, 50, 10)]
#guard lane 10 ([none, none, none] : List (Option Phase)) = []

-- A control of `runs_expand`, which needs a lawful test of equality. With a test that holds of
-- `2` and `3`, the two are one run, named by the later one, and the runs written out are not
-- the sequence.
#guard @runs Nat ⟨fun a b => a / 2 == b / 2⟩ [2, 3, 4] = [(3, 2), (4, 1)]
#guard runs [2, 3, 4] = [(2, 1), (3, 1), (4, 1)]

-- A small line of eight values, `12` high, a column `4` wide, on a screen whose ordinates grow
-- downward: the scale falls, so a greater value is drawn higher. The least value stands in the
-- columns `2` and `5` and the greatest in the columns `1` and `4`: each mark is at the one
-- further left. The third mark is the last column.
#guard line (Scale.linear 0 9 12 0) 4 [3, 9, 2, 8, 9, 2, 6, 7] =
  [⟨0, 8⟩, ⟨4, 0⟩, ⟨8, 9⟩, ⟨12, 1⟩, ⟨16, 0⟩, ⟨20, 9⟩, ⟨24, 4⟩, ⟨28, 2⟩]
#guard marks [3, 9, 2, 8, 9, 2, 6, 7] = some (2, 1, 7)
#guard marks [] = none
#guard decide (Scale.linear 0 9 12 0).Falling

end Strip

end Whatwg.Svg.Scene
