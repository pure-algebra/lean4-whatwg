import Whatwg.Svg.Scene.Motion.Laws

/-!
# Whatwg.Svg.Scene.Vector

Owner: the readings of motion as tables of numbers (slice S17; ask W3 of
`docs/research/2026-10-12-whatwg-requests.md`).

A program that is not written in Lean can play the tracks of `Whatwg/Svg/Scene/Motion.lean`: it
samples them itself, as lean4-effect4's player in C does. Such a program is right where its
numbers are the kit's at every moment. This module says what the kit's numbers are, as tables,
and writes the tables as text that a test in C reads.

```
Easing.backOut.table                         -- `Easing.at` at the moments 0 … 1000
Easing.backOut.shares 270                    -- `Easing.of n 270` for n = 0 … 270
({ delay := 180, duration := 270 } : Transition).table
track.table                                  -- the numbers of `Track.at` at every moment
Case.text Case.battery                       -- the kit's battery, as the text of a file
Case.text [Case.easing "mine" e, Case.track "box" tr]   -- a caller's own cases
```

- `tableOf f last`: the values of `f` at `0 … last`. Its entry at `i` is `f i`
  (`tableOf_getElem?`), and it has `last + 1` entries (`length_tableOf`).
- `Easing.table`, `Easing.shares`, `Transition.table`, `mixTable`, `Track.table`: the tables of
  the readings, each with the two laws under its own name. The shares of a thousand are the
  table (`Easing.shares_thousand`), and between its delay and its end a transition's table is
  its easing's shares, later by the delay (`Transition.table_between`).
- `Pose.numbers`: a pose as numbers only. A shift is its two coordinates; a size, a part and an
  opacity are one number; a shape is the coordinates of its segments in order, eight for each.
  The numbers lose nothing: two poses of one kind with the same numbers are one pose
  (`Pose.numbers_inj`). So a program whose numbers are the entry of a track's table has computed
  the pose of the track (`Track.eq_of_table`).
- `Easing.numbers`, `Transition.numbers`, `Change.numbers`: the data of a case as numbers, so
  that the test reads what it is to compute from the same line.
- `Case`: a kind of reading, a name, the numbers given and the readings. `Case.line` writes one
  as a line of text, and `Case.text` a list of them as a file.
- `Case.battery`: the cases the kit chose, with the ones that catch a wrong transcription on
  purpose (listed at `Case.battery`).

## The text

Every line is words and whole numbers with one tab between them:

    kind  name  g  x₁ … x_g  r  y₁ … y_r

`kind` and `name` are words with no blank in them, `g` counts the numbers given and `r` the
readings. A test reads two words, a count and that many numbers, a count and that many numbers,
and goes on until the file ends: `fscanf` of C does it with `%s` and `%lld`, and takes a tab and
a line's end alike. The first line is `format whatwg-motion-1 0 0`.

- `mix`. Given: `u v lo last`. Readings: `mix u v e` for `e = lo … lo + last`.
- `at`. Given: an easing. Readings: `Easing.at` at the moments `0 … 1000`.
- `of`. Given: `den` and an easing. Readings: `Easing.of n den` for `n = 0 … den`.
- `timed`. Given: `delay duration` and an easing. Readings: `Transition.at` at the moments
  `0 … 1000`.
- `track`. Given: a change, `delay duration` and an easing. Readings: for each moment
  `0 … 1000`, a count and that many numbers of the pose.

An easing is `0 k v₁ … v_k` for `k` stops, or `1 y1 y2` for a cubic. A change is `0 ax ay bx by`
for a shift, `1 a b` for a size, `2 a b` for a part, `3 a b` for an opacity, and
`4 m c₁ … c_8m n d₁ … d_8n` for a change of shape from `m` segments to `n`.

What this module does not claim. The text is written by rule, and no law here is about text:
the test of this module reads the battery's text back into its numbers, which is a finite
evaluation. A name is the caller's, and `Case.line` writes it as it is: a name with a blank in
it gives a line that does not read back. No test of a name is here, since a function that reads
the characters of a `String` is over this layer's ceiling. A table is the kit's own reading.
That a program in C computes the same numbers is what a test in C shows, case by case;
`Whatwg/Svg/Scene/Machine.lean` says which arithmetic gives them, and that 64 bits hold it.
Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## A reading at every moment -/

/-- The values of `f` at `0`, `1` and so on to `last`. With `last` a thousand it is a reading
at every moment of a step. -/
def tableOf {α : Type} (f : Nat → α) (last : Nat := 1000) : List α :=
  (List.range (last + 1)).map f

/-- A table to `last` has `last + 1` entries. -/
theorem length_tableOf {α : Type} (f : Nat → α) (last : Nat) :
    (tableOf f last).length = last + 1 := by
  rw [tableOf, List.length_map, List.length_range]

/-- **The entry at `i` of a table is the reading at `i`.** -/
theorem tableOf_getElem? {α : Type} (f : Nat → α) (last i : Nat) (h : i ≤ last) :
    (tableOf f last)[i]? = some (f i) := by
  rw [tableOf, List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le h)]
  rfl

/-- Every entry of a table is the reading at a moment of the table. -/
theorem of_mem_tableOf {α : Type} {f : Nat → α} {last : Nat} {x : α} (h : x ∈ tableOf f last) :
    ∃ i, i ≤ last ∧ f i = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
  exact ⟨i, Nat.le_of_lt_succ (List.mem_range.mp hi), rfl⟩

/-! ## The tables of the readings -/

/-- `mix u v e` at every eased progress from `lo` to `lo + last`. A `lo` below `0` and a `last`
past `1000 - lo` take in what an easing reads when it goes below its start or past its end. -/
def mixTable (u v lo : Int) (last : Nat) : List Int := tableOf (fun i => mix u v (lo + i)) last

/-- A table of `mix` to `last` has `last + 1` entries. -/
theorem length_mixTable (u v lo : Int) (last : Nat) : (mixTable u v lo last).length = last + 1 :=
  length_tableOf _ last

/-- The entry at `i` of a table of `mix` is the value at the eased progress `lo + i`. -/
theorem mixTable_getElem? (u v lo : Int) (last i : Nat) (h : i ≤ last) :
    (mixTable u v lo last)[i]? = some (mix u v (lo + i)) :=
  tableOf_getElem? _ last i h

namespace Easing

/-- **The readings of an easing at every moment**: `e.at p` for `p` from `0` to `1000`. -/
def table (e : Easing) : List Int := tableOf e.at

/-- The table of an easing has a thousand and one entries. -/
theorem length_table (e : Easing) : e.table.length = 1001 := length_tableOf e.at 1000

/-- **The entry at `p` of an easing's table is its reading at `p`.** -/
theorem table_getElem? (e : Easing) (p : Nat) (h : p ≤ 1000) : e.table[p]? = some (e.at p) :=
  tableOf_getElem? e.at 1000 p h

/-- **The readings of an easing at every share of `den`**: `e.of num den` for `num` from `0` to
`den`. A transition of the duration `den` reads these, and no others but the start and the end. -/
def shares (e : Easing) (den : Nat) : List Int := tableOf (fun num => e.of num den) den

/-- The shares of `den` are `den + 1` entries. -/
theorem length_shares (e : Easing) (den : Nat) : (e.shares den).length = den + 1 :=
  length_tableOf _ den

/-- **The entry at `num` of the shares of `den` is the reading at the share `num / den`.** -/
theorem shares_getElem? (e : Easing) (den num : Nat) (h : num ≤ den) :
    (e.shares den)[num]? = some (e.of num den) :=
  tableOf_getElem? _ den num h

/-- The shares of a thousand are the table. -/
theorem shares_thousand (e : Easing) : e.shares 1000 = e.table := by
  unfold shares table tableOf
  exact List.map_congr_left fun p _ => of_thousand e p

end Easing

namespace Transition

/-- **The readings of a transition at every moment**: `tr.at t` for `t` from `0` to `1000`. -/
def table (tr : Transition) : List Int := tableOf tr.at

/-- The table of a transition has a thousand and one entries. -/
theorem length_table (tr : Transition) : tr.table.length = 1001 := length_tableOf tr.at 1000

/-- **The entry at `t` of a transition's table is its reading at `t`.** -/
theorem table_getElem? (tr : Transition) (t : Nat) (h : t ≤ 1000) :
    tr.table[t]? = some (tr.at t) :=
  tableOf_getElem? tr.at 1000 t h

/-- **Between its delay and its end, a transition's table is its easing's shares, later by the
delay.** So a test of the shares of a duration is a test of every transition of that duration
and that easing, whatever its delay. -/
theorem table_between (tr : Transition) (t : Nat) (h1 : tr.delay < t)
    (h2 : t < tr.delay + tr.duration) (ht : t ≤ 1000) :
    tr.table[t]? = (tr.ease.shares tr.duration)[t - tr.delay]? := by
  rw [table_getElem? tr t ht, Easing.shares_getElem? tr.ease tr.duration (t - tr.delay) (by omega),
    at_between tr t h1 h2]

end Transition

/-! ## A pose as numbers -/

/-- The eight coordinates of a segment, in order: its start, its two controls and its end, each
as `x` and then `y`. -/
def ICubic.numbers (c : ICubic) : List Int :=
  [c.p0.x, c.p0.y, c.p1.x, c.p1.y, c.p2.x, c.p2.y, c.p3.x, c.p3.y]

/-- A segment is its eight coordinates. -/
theorem ICubic.numbers_inj {a b : ICubic} (h : a.numbers = b.numbers) : a = b := by
  obtain ⟨⟨a0, a1⟩, ⟨a2, a3⟩, ⟨a4, a5⟩, ⟨a6, a7⟩⟩ := a
  obtain ⟨⟨b0, b1⟩, ⟨b2, b3⟩, ⟨b4, b5⟩, ⟨b6, b7⟩⟩ := b
  have h' : [a0, a1, a2, a3, a4, a5, a6, a7] = [b0, b1, b2, b3, b4, b5, b6, b7] := h
  cases h'
  rfl

/-- The coordinates of a list of segments, in order: eight for each. -/
def coordinates (segments : List ICubic) : List Int := segments.flatMap ICubic.numbers

/-- A list of segments has eight coordinates for each. -/
theorem length_coordinates : ∀ segments : List ICubic,
    (coordinates segments).length = 8 * segments.length
  | [] => rfl
  | c :: rest => by
    show (c.numbers ++ coordinates rest).length = 8 * (rest.length + 1)
    rw [List.length_append, length_coordinates rest]
    show 8 + 8 * rest.length = 8 * (rest.length + 1)
    omega

/-- A list of segments is its coordinates. -/
theorem coordinates_inj : ∀ {a b : List ICubic}, coordinates a = coordinates b → a = b
  | [], [], _ => rfl
  | [], c :: rest, h => by
    have hl := congrArg List.length h
    rw [length_coordinates, length_coordinates] at hl
    exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | c :: rest, [], h => by
    have hl := congrArg List.length h
    rw [length_coordinates, length_coordinates] at hl
    exact absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | c :: rest, d :: more, h => by
    have h' : c.numbers ++ coordinates rest = d.numbers ++ coordinates more := h
    obtain ⟨hc, hr⟩ := List.append_inj h' rfl
    rw [ICubic.numbers_inj hc, coordinates_inj hr]

namespace Pose

/-- Which kind a pose is of, as a number: `0` a shift, `1` a size, `2` a part revealed, `3` an
opacity, `4` a shape. -/
def code : Pose → Nat
  | .shift _ => 0
  | .grow _ => 1
  | .reveal _ => 2
  | .fade _ => 3
  | .shape _ => 4

/-- **A pose as numbers only.** A shift is its two coordinates. A size, a part and an opacity
are one number. A shape is the coordinates of its segments in order, eight for each. -/
def numbers : Pose → List Int
  | .shift step => [step.x, step.y]
  | .grow size => [size]
  | .reveal part => [part]
  | .fade shown => [shown]
  | .shape segments => coordinates segments

/-- **The numbers of a pose lose nothing.** Two poses of one kind with the same numbers are one
pose. -/
theorem numbers_inj {p q : Pose} (hc : p.code = q.code) (h : p.numbers = q.numbers) : p = q := by
  cases p with
  | shift a =>
    cases q with
    | shift b =>
      have h' : [a.x, a.y] = [b.x, b.y] := h
      injection h' with hx h'
      injection h' with hy
      exact congrArg Pose.shift (IVec.ext hx hy)
    | _ => cases hc
  | grow a =>
    cases q with
    | grow b =>
      have h' : [a] = [b] := h
      injection h' with ha
      exact congrArg Pose.grow ha
    | _ => cases hc
  | reveal a =>
    cases q with
    | reveal b =>
      have h' : [a] = [b] := h
      injection h' with ha
      exact congrArg Pose.reveal ha
    | _ => cases hc
  | fade a =>
    cases q with
    | fade b =>
      have h' : [a] = [b] := h
      injection h' with ha
      exact congrArg Pose.fade ha
    | _ => cases hc
  | shape a =>
    cases q with
    | shape b => exact congrArg Pose.shape (coordinates_inj h)
    | _ => cases hc

end Pose

namespace Change

/-- Which kind a change is of, as a number: the kind of each of its poses. -/
def code : Change → Nat
  | .shift _ _ => 0
  | .grow _ _ => 1
  | .reveal _ _ => 2
  | .fade _ _ => 3
  | .morph _ _ => 4

/-- A change sets a pose of its own kind at every progress. -/
theorem at_code (c : Change) (e : Int) : (c.at e).code = c.code := by
  cases c with
  | morph a b =>
    show (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
      else if e < 500 then Pose.shape a
      else Pose.shape b).code = 4
    split
    · rfl
    · split
      · rfl
      · rfl
  | _ => rfl

end Change

namespace Track

/-- **The poses of a track at every moment, as numbers**: the numbers of `tr.at t` for `t` from
`0` to `1000`. -/
def table {κ : Type} (tr : Track κ) : List (List Int) := tableOf fun t => (tr.at t).numbers

/-- The table of a track has a thousand and one entries. -/
theorem length_table {κ : Type} (tr : Track κ) : tr.table.length = 1001 := length_tableOf _ 1000

/-- **The entry at `t` of a track's table is the numbers of its pose at `t`.** -/
theorem table_getElem? {κ : Type} (tr : Track κ) (t : Nat) (h : t ≤ 1000) :
    tr.table[t]? = some (tr.at t).numbers :=
  tableOf_getElem? _ 1000 t h

/-- **A program whose numbers are the table's has computed the pose.** A pose of the track's
kind whose numbers are the entry at `t` of the track's table is the pose of the track at `t`. -/
theorem eq_of_table {κ : Type} (tr : Track κ) (t : Nat) (ht : t ≤ 1000) {p : Pose}
    (hc : p.code = tr.change.code) (h : tr.table[t]? = some p.numbers) : p = tr.at t := by
  rw [table_getElem? tr t ht] at h
  exact Pose.numbers_inj (hc.trans (Change.at_code tr.change (tr.timing.at t)).symm)
    (Option.some.inj h).symm

end Track

/-! ## The data of a case as numbers -/

/-- An easing as numbers: `0`, the count of its stops and the stops; or `1` and the two heights
of a cubic. -/
def Easing.numbers : Easing → List Int
  | .stops values => 0 :: (values.length : Int) :: values
  | .cubic y1 y2 => [1, y1, y2]

/-- A transition as numbers: its delay, its duration and its easing. -/
def Transition.numbers (tr : Transition) : List Int :=
  (tr.delay : Int) :: (tr.duration : Int) :: tr.ease.numbers

/-- A change as numbers: its kind, and the pose at its start and the pose at its end. A change
of shape gives the count of segments before the coordinates of each of its two lists. -/
def Change.numbers : Change → List Int
  | .shift a b => [0, a.x, a.y, b.x, b.y]
  | .grow a b => [1, a, b]
  | .reveal a b => [2, a, b]
  | .fade a b => [3, a, b]
  | .morph a b =>
    4 :: (a.length : Int) :: (coordinates a ++ (b.length : Int) :: coordinates b)

/-! ## Cases and their text -/

/-- **One case of a table**: what kind of reading it is, its name, the numbers a test is given
and the readings it must compute. -/
structure Case where
  /-- The kind of reading: `mix`, `at`, `of`, `timed` or `track`. -/
  kind : String
  /-- The name of the case: one word. -/
  name : String
  /-- The numbers a test is given. -/
  given : List Int
  /-- The readings: what the test must compute from them. -/
  readings : List Int
  deriving Repr, Inhabited

namespace Case

/-- `mix u v e` for `e` from `lo` to `lo + last`. Given: `u v lo last`. -/
def mix (name : String) (u v lo : Int) (last : Nat) : Case :=
  ⟨"mix", name, [u, v, lo, last], mixTable u v lo last⟩

/-- An easing at every moment. Given: the easing. -/
def easing (name : String) (e : Easing) : Case := ⟨"at", name, e.numbers, e.table⟩

/-- An easing at every share of `den`. Given: `den` and the easing. -/
def share (name : String) (e : Easing) (den : Nat) : Case :=
  ⟨"of", name, (den : Int) :: e.numbers, e.shares den⟩

/-- A transition at every moment. Given: its delay, its duration and its easing. -/
def transition (name : String) (tr : Transition) : Case := ⟨"timed", name, tr.numbers, tr.table⟩

/-- A track at every moment. Given: its change and its transition. The readings are, for each
moment, a count and that many numbers of the pose: a change of shape between two lists of
different lengths has poses of two sizes. -/
def track {κ : Type} (name : String) (tr : Track κ) : Case :=
  ⟨"track", name, tr.change.numbers ++ tr.timing.numbers,
    tr.table.flatMap fun ns => (ns.length : Int) :: ns⟩

/-- **A case as a line of text**: its kind, its name, the count of the numbers given and the
numbers, the count of the readings and the readings, with one tab between them. -/
def line (c : Case) : String :=
  "\t".intercalate
    (c.kind :: c.name :: toString c.given.length :: c.given.map toString ++
      toString c.readings.length :: c.readings.map toString)

/-- The first line of a table: it names the format, and gives and reads nothing. -/
def format : Case := ⟨"format", "whatwg-motion-1", [], []⟩

/-- **A table as text**: the line of the format, and one line for each case. -/
def text (cases : List Case) : String :=
  String.join ((format :: cases).map fun c => c.line ++ "\n")

/-! ### The kit's battery -/

/-- lean4-effect4's ease in and out, two cubics that no one cubic is, at its twenty-one
points. -/
def inOut : Easing :=
  Easing.sampled fun p =>
    if p < 500 then 4 * (p : Int) ^ 3 / 1000000 else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000

/-- lean4-effect4's critically damped spring, at every twentieth of its progress. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

/-- lean4-effect4's underdamped spring: it goes to `1045` before it settles. -/
def spring : Easing :=
  .stops [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026,
    1019, 1012, 1007, 1003, 1000]

/-- The usual `back` easing turned about: it goes below `0` before it leaves. -/
def backIn : Easing := .cubic 0 (-567)

/-- A cubic that goes below `0` and past `1000`. -/
def bothWays : Easing := .cubic (-567) 1567

/-- Seven pieces, which do not divide a thousand, with a stop below `0` and three past `1000`. -/
def sevenths : Easing := .stops [0, -80, 300, 1100, 1045, 960, 1010, 1000]

/-- Three pieces that end at `250`: an easing that is not proper. -/
def thirds : Easing := .stops [0, 500, 1000, 250]

/-- **The easings of the battery.** Above `1000`: `back-out`, `both-ways`, `spring`, `sevenths`
and `wide`. Below `0`: `back-in`, `both-ways`, `sevenths` and `wide`. Fewer than two stops:
`no-stop` reads `0` everywhere and `one-stop` its one value. Falling values, where the line
between two stops divides a negative number: `down`, `thirds`, `sevenths` and `spring`. `wide`
has heights a hundred times the whole way, to test the width of a machine's numbers. -/
def easings : List (String × Easing) :=
  [("linear", Easing.linear), ("cubic-in", Easing.cubicIn), ("cubic-out", Easing.cubicOut),
    ("back-out", Easing.backOut), ("back-in", backIn), ("both-ways", bothWays),
    ("wide", .cubic 100000 (-100000)), ("in-out", inOut), ("settle", settle), ("spring", spring),
    ("sevenths", sevenths), ("thirds", thirds), ("down", .stops [1000, 0]),
    ("no-stop", .stops []), ("one-stop", .stops [700])]

/-- **The durations whose shares the battery reads.** `270` and `450` are lean4-effect4's: its
kept things move for 270 ms of a step of 600, which is 450 per mille. Neither divides a
thousand, and `7` and `1` are the small ones. `0` is the share of nothing: no transition reads
it, and a division by it gives `0` here. -/
def durations : List Nat := [0, 1, 7, 270, 450]

/-- **The transitions of the battery.** The first five are lean4-effect4's defaults in per
mille of its step. Then: a delay with a duration of `270` and of `450`; no duration, with and
without a delay; a duration of one; a prime duration; a delay past the step; an end past the
step; an easing that is not proper; a whole step; and falling values. -/
def transitions : List (String × Transition) :=
  [("move", { duration := 450, ease := settle }),
    ("leave", { duration := 250, ease := Easing.cubicIn }),
    ("write", { delay := 300, duration := 300 }),
    ("draw", { duration := 220, ease := Easing.cubicOut }),
    ("expand", { duration := 360, ease := spring }),
    ("late-270", { delay := 180, duration := 270, ease := Easing.backOut }),
    ("late-450", { delay := 300, duration := 450, ease := backIn }),
    ("at-once", { duration := 0 }),
    ("at-once-late", { delay := 400, duration := 0, ease := Easing.cubicIn }),
    ("one-long", { delay := 10, duration := 1, ease := Easing.cubicOut }),
    ("prime", { delay := 3, duration := 997, ease := bothWays }),
    ("never", { delay := 1200, duration := 300, ease := spring }),
    ("past-end", { delay := 800, duration := 450, ease := Easing.backOut }),
    ("not-proper", { delay := 100, duration := 333, ease := thirds }),
    ("whole", { ease := sevenths }),
    ("downhill", { delay := 50, duration := 900, ease := .stops [1000, 0] })]

/-- **The pairs that the battery mixes**, each at every eased progress from `-100` to `1100`:
`u < v` and `u > v`, a way of one unit, coordinates below `0`, a value mixed with itself, and
coordinates of a thousand million. -/
def mixes : List (String × Int × Int) :=
  [("up", 0, 100), ("down", 100, 0), ("unit-up", 0, 1), ("unit-down", 1, 0),
    ("across-up", -7, 5), ("across-down", 5, -7), ("below", -100, -3), ("same", 3, 3),
    ("odd", 999, -333), ("far-up", -1000000000, 1000000000),
    ("far-down", 1000000000, -1000000000)]

/-- A segment for the changes of shape of the battery: an edge that bends. -/
def bend : ICubic := ⟨⟨0, 0⟩, ⟨0, 12⟩, ⟨24, 12⟩, ⟨24, 24⟩⟩

/-- The segment that goes on from `bend`, with coordinates below `0`. -/
def bendOn : ICubic := ⟨⟨24, 24⟩, ⟨24, 36⟩, ⟨-9, 36⟩, ⟨-9, 48⟩⟩

/-- The segment that `bend` changes into. -/
def tilt : ICubic := ⟨⟨7, -3⟩, ⟨7, 10⟩, ⟨31, 15⟩, ⟨40, 20⟩⟩

/-- The segment that goes on from `tilt`. -/
def tiltOn : ICubic := ⟨⟨40, 20⟩, ⟨41, 33⟩, ⟨-20, 30⟩, ⟨-25, 51⟩⟩

/-- **The tracks of the battery.** A shift, a size, a part and an opacity by lean4-effect4's
transitions; a shift by an easing that goes past its end and an opacity by one that goes below
its start; a change of shape between lists of one length; three between lists of different
lengths, which jump where the eased progress crosses `500`: once, three times by an easing that
turns back, and from no segment at all; and a shift with no duration. -/
def tracks : List (Track String) :=
  [⟨"shift-settle", .shift ⟨120, -48⟩ 0, { duration := 450, ease := settle }⟩,
    ⟨"shift-back", .shift ⟨-300, 72⟩ ⟨15, -9⟩,
      { delay := 180, duration := 270, ease := Easing.backOut }⟩,
    ⟨"grow-spring", .grow 0 1000, { duration := 360, ease := spring }⟩,
    ⟨"reveal-out", .reveal 0 1000, { duration := 220, ease := Easing.cubicOut }⟩,
    ⟨"fade-out", .fade 1000 0, { duration := 250, ease := Easing.cubicIn }⟩,
    ⟨"fade-below", .fade 0 1000, { delay := 300, duration := 450, ease := backIn }⟩,
    ⟨"morph", .morph [bend] [tilt], { duration := 450, ease := settle }⟩,
    ⟨"morph-jump", .morph [bend] [tilt, tiltOn],
      { delay := 180, duration := 270, ease := Easing.backOut }⟩,
    ⟨"morph-jump-thrice", .morph [bend, bendOn] [tilt], { ease := .stops [0, 800, 300, 1000] }⟩,
    ⟨"morph-from-none", .morph [] [bend], {}⟩,
    ⟨"shift-at-once", .shift ⟨5, 5⟩ ⟨-5, -5⟩, { delay := 400, duration := 0 }⟩]

/-- **The kit's battery**: the pairs mixed, each easing at every moment, each easing at every
share of each duration, each transition at every moment, and each track at every moment. A
name is the name of its data, and a share's name ends in its duration. -/
def battery : List Case :=
  mixes.map (fun (name, u, v) => Case.mix name u v (-100) 1200) ++
    easings.map (fun (name, e) => Case.easing name e) ++
    durations.flatMap (fun den =>
      easings.map fun (name, e) => Case.share (name ++ "/" ++ toString den) e den) ++
    transitions.map (fun (name, tr) => Case.transition name tr) ++
    tracks.map fun tr => Case.track tr.key tr

end Case

end Whatwg.Svg.Scene
