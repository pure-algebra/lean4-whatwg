import Whatwg.Svg.Scene.Scale.Band.Laws
import Whatwg.Svg.Scene.Scale.Chain

/-!
# WhatwgTest.Svg.UseScale

Where lean4-effect4's view maps data to pixels by hand, on the scales of
`Whatwg/Svg/Scene/Scale/` (slice S22). The consumer is read at its checkout `6ad8f7b8d`. It
uses no scale of the package today. This module imports nothing of that package: it restates
the consumer's numbers and functions under the consumer's names.

**What is ported, and what it was.**

| The consumer's | Here |
| --- | --- |
| `CELL`, `LEFT`, `col` (`tools/Tools/View/Grid.lean`, lines 15 to 18, 86) | `columns`, a `Band.ofGap` with no gap; `col_eq` |
| `cols := (W - 2 * LEFT) / CELL` (`Page.lean`, lines 245 and 275) and `room := (W - LEFT - x) / CELL` (line 215) | `Band.fitting`; `cols_eq`, and `cols_fit`, which says what the quotient is |
| `y := ROWH * LEVEL * r` and `height := ROWH * LEVEL * (ranksN - 1) + ROWH * BOXROWS` (`Graph.layout`, `Graph.lean`, lines 308 and 319) | `ranks`, a `Band.ofGap` with a gap of one row; `rankY_eq`, `graphHeight_eq` |
| `w := max fine (trunk * share / 1000000)` (`Graph.organicCalls`, `Graph.lean`, line 638) | `edgeScale`, a `Scale.linear`; `edgeWidth_eq` |

**What the consumer gains.** Each of these is a multiplication or a division written where it
is used, and no law of the consumer says what it gives. On the kit:

- the ranks of a graph lie inside the graph's height and share no row (`ranks_inside`,
  `ranks_apart`), which the consumer has as the finite checks of its specimens;
- **the way back from a pointer**: the column and the rank under a place are `Band.invert`,
  with the law that the answer is the one band that holds the place (`column_under`,
  `rank_under`). The consumer answers a pointer with a box for each line (`.hit`), and has no
  inverse of its grid;
- the width of an edge never falls as its share grows, and the least share that is drawn at a
  width is `Scale.invert` (`edgeWidth_mono`, and the guards at the foot).

What is not ported: `Live.ratchet` (`Live.lean`, line 64), a column rounded up to a multiple of
a step. It is the upper bound of `Ticks.nice` in whole numbers, and the kit has no whole-number
form of it.

The guards are of two kinds. Finite evaluations: the consumer's numbers, each computed by hand
in the comment above it. Controls: a place in a gap and a place past the last band, where
`Band.invert` answers `none`.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.UseScale

open Whatwg.Svg.Scene

/-! ## The grid: the consumer's numbers -/

/-- The width of a cell and the height of a row, in pixels. -/
def CELL : Nat := 8
def ROWH : Nat := 24
/-- The left margin of a page. -/
def LEFT : Int := 24
/-- The rows of a rank, and of a box. -/
def LEVEL : Nat := 3
def BOXROWS : Nat := 2

/-! ## The columns of a page -/

/-- The left edge of a column of cells: the consumer's `col`. -/
def col (c : Int) : Int := LEFT + (CELL : Int) * c

/-- The cells that a page of a width has room for: the consumer's `cols`. -/
def cols (W : Int) : Int := (W - 2 * LEFT) / (CELL : Int)

/-- **The columns of a page are a band scale**: cells with no gap, from the left margin. -/
def columns (n : Nat) : Band := Band.ofGap LEFT CELL 0 n

/-- The consumer's `col` is the left edge of a band. -/
theorem col_eq (n c : Nat) : col c = Band.at (columns n) c := rfl

/-- The consumer's `cols` is the count of bands that fit. -/
theorem cols_eq (W : Nat) (h : 48 ≤ W) : cols W = (Band.fitting CELL 0 (W - 48) : Nat) := by
  show ((W : Int) - 2 * 24) / 8 = (((W - 48 + 0) / (8 + 0) : Nat) : Int)
  omega

/-- **What the quotient is**: `n` columns fit between the two margins exactly when `n` is no
more than `cols`. The consumer has the quotient and no sentence of it. -/
theorem cols_fit (W n : Nat) : n ≤ Band.fitting CELL 0 (W - 48) ↔ n * 8 ≤ W - 48 :=
  Band.le_fitting (by decide) (W - 48) n

/-- **The column under a place.** Among `n` columns, a place answers the column `c` exactly when
`c` is one of them and the place is from its left edge to before the next. -/
theorem column_under (n : Nat) (x : Int) (c : Nat) :
    (columns n).invert x = some c ↔ c < n ∧ col c ≤ x ∧ x < col c + 8 :=
  Band.invert_eq_some (Band.ofGap_apart LEFT CELL 0 n)

/-! ## The ranks of a graph -/

/-- The top of the rank `r`: the consumer's `y` of a placed item. -/
def rankY (r : Nat) : Int := (ROWH : Int) * (LEVEL : Int) * (r : Int)

/-- The height of a graph of `n` ranks: the consumer's `height` of a layout. -/
def graphHeight (n : Nat) : Int :=
  if n == 0 then 0
  else (ROWH : Int) * (LEVEL : Int) * ((n : Int) - 1) + (ROWH : Int) * (BOXROWS : Int)

/-- **The ranks of a graph are a band scale**: boxes two rows high with a gap of one row. -/
def ranks (n : Nat) : Band := Band.ofGap 0 (ROWH * BOXROWS) (ROWH * (LEVEL - BOXROWS)) n

/-- The consumer's `y` is the top of a band. -/
theorem rankY_eq (n r : Nat) : rankY r = Band.at (ranks n) r := by
  show (24 : Int) * 3 * (r : Int) = 0 + ((24 * 2 + 24 * (3 - 2) : Nat) : Int) * (r : Int)
  omega

/-- The consumer's `height` is where the last band ends. -/
theorem graphHeight_eq {n : Nat} (h : 0 < n) :
    graphHeight n = Band.at (ranks n) (n - 1) + ((ranks n).width : Int) := by
  have e : (n == 0) = false := by
    cases n with
    | zero => exact absurd h (Nat.lt_irrefl 0)
    | succ k => rfl
  unfold graphHeight
  rw [e, ← rankY_eq n (n - 1)]
  show (24 : Int) * 3 * ((n : Int) - 1) + 24 * 2 =
    24 * 3 * ((n - 1 : Nat) : Int) + ((24 * 2 : Nat) : Int)
  omega

/-- **The ranks share no row.** -/
theorem ranks_apart (n : Nat) : (ranks n).Apart := Band.ofGap_apart _ _ _ n

/-- **Every rank lies inside the height of its graph.** -/
theorem ranks_inside {n : Nat} (h : 0 < n) : (ranks n).Inside 0 (graphHeight n) := by
  have e := graphHeight_eq h
  have a0 : Band.at (ranks n) 0 = 0 := Band.at_zero _
  have an : Band.at (ranks n) (n - 1) = 72 * ((n - 1 : Nat) : Int) := by
    rw [← rankY_eq]
    rfl
  have w : ((ranks n).width : Int) = 48 := rfl
  refine Band.inside_of_ends ?_ ?_ ?_ ?_
  · omega
  · omega
  · show (0 : Int) ≤ Band.at (ranks n) (n - 1)
    omega
  · show Band.at (ranks n) (n - 1) + ((ranks n).width : Int) ≤ graphHeight n
    omega

/-- **The rank under a place.** Among `n` ranks, a place answers the rank `r` exactly when `r`
is one of them and the place is from its top to before its foot. A place between two ranks
answers none. -/
theorem rank_under (n : Nat) (y : Int) (r : Nat) :
    (ranks n).invert y = some r ↔ r < n ∧ rankY r ≤ y ∧ y < rankY r + 48 := by
  rw [rankY_eq n r]
  exact Band.invert_eq_some (ranks_apart n)

/-! ## The width of an edge -/

/-- The width of a forward edge with a share of the work in millionths, with the finest line `1`
and a trunk of `8`: the consumer's `w` of `organicCalls`. -/
def edgeWidth (share : Nat) : Int := max 1 (8 * (share : Int) / 1000000)

/-- **The width of an edge is a straight line**: from an eighth of the work at the finest line
to all of it at the trunk. -/
def edgeScale : Scale := .linear 125000 1000000 1 8

/-- The consumer's width is the scale's, for every share up to the whole. -/
theorem edgeWidth_eq {share : Nat} (h : share ≤ 1000000) :
    edgeWidth share = edgeScale.at share := by
  show max 1 (8 * (share : Int) / 1000000) =
    1 + (8 - 1) * (max 125000 (min (share : Int) 1000000) - 125000) / (1000000 - 125000)
  omega

/-- **More work is never drawn thinner.** It is `Scale.at_mono` of the scale, where the
consumer has the formula and no law of it. -/
theorem edgeWidth_mono {a b : Nat} (hab : a ≤ b) (hb : b ≤ 1000000) :
    edgeWidth a ≤ edgeWidth b := by
  rw [edgeWidth_eq (Nat.le_trans hab hb), edgeWidth_eq hb]
  exact Scale.at_mono edgeScale (by decide) (Int.ofNat_le.mpr hab)

/-! ## Finite evaluations -/

-- The consumer's columns: the left margin `24` and cells of `8`. A page `1280` wide has
-- `(1280 - 48) / 8 = 154` of them.
#guard [0, 1, 3].map col == [24, 32, 48] && cols 1280 == 154
-- The column under a place: `24` to `31` is the column `0`, and `48` the column `3`. A place in
-- the left margin, and a place past the last of four columns, answer none.
#guard [24, 31, 32, 48].map (columns 4).invert == [some 0, some 0, some 1, some 3]
#guard [23, 0, 56].map (columns 4).invert == [none, none, none]

-- The consumer's ranks: a rank every `72`, a box `48` high. Four ranks are
-- `72 * 3 + 48 = 264` high.
#guard [0, 1, 2, 3].map rankY == [0, 72, 144, 216] && graphHeight 4 == 264 && graphHeight 0 == 0
-- The rank under a place. A place in the row between two ranks answers none: a control of
-- `rank_under`.
#guard [0, 47, 72, 263].map (ranks 4).invert == [some 0, some 0, some 1, some 3]
#guard [48, 71, 264, -1].map (ranks 4).invert == [none, none, none, none]

-- The consumer's width of an edge: half the work is half the trunk, and a share below an
-- eighth is the finest line. The least share drawn `4` wide is half the work.
#guard [0, 100000, 125000, 500000, 1000000].map edgeWidth == [1, 1, 1, 4, 8]
#guard edgeScale.invert 3 == 499999 && edgeScale.at 499999 == 3 && edgeScale.at 500000 == 4

end WhatwgTest.Svg.UseScale
