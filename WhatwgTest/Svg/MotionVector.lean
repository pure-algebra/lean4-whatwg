import Whatwg.Svg.Scene.Vector
import Whatwg.Svg.Scene.Machine

/-!
# WhatwgTest.Svg.MotionVector

The tables of `Whatwg/Svg/Scene/Vector.lean` and the machine of `Whatwg/Svg/Scene/Machine.lean`,
at real data (slice S17; ask W3 of `docs/research/2026-10-12-whatwg-requests.md`).

Nothing here says a theorem again. There are four kinds of line.

- **The text.** No law of the kit is about text, so the battery's text is read back into its
  numbers here, by running, and the numbers given into the easings, transitions and changes
  they came from, as a test in C reads them. The line of one small case is compared with the
  line typed by hand.
- **Entries of the tables against numbers computed by hand.** The arithmetic is in the comment
  above each guard. They are the cases a wrong transcription gets wrong: a value that rises and
  one that falls, an easing below `0` and one past `1000`, a duration that does not divide a
  thousand, fewer than two stops, and a change of shape between lists of different lengths.
- **Readers.** The laws of the machine applied to the battery: its easings, transitions and
  tracks pass the test of `Small` by `decide`, which is the check a consumer runs on its look,
  and the width law then holds of each at every moment.
- **Controls.** What a transcription with C's own division computes, at named cases and counted
  over a line of the battery; a product of the kit that 32 bits do not hold; and data past the
  bounds of `Small`, where the machine has no reading, beside data past them that still fits.

Every theorem of this module depends on `propext` and `Quot.sound` at most.
-/

namespace WhatwgTest.Svg.MotionVector

open Whatwg.Svg.Scene

/-! ## The text -/

/-- A line of the text read back: its two words, the numbers given and the readings. -/
def readLine (line : String) : Option (String × String × List Int × List Int) := do
  let kind :: name :: rest := line.splitOn "\t" | none
  let g :: rest ← rest.mapM String.toInt? | none
  let given := rest.take g.toNat
  let r :: readings := rest.drop g.toNat | none
  if readings.length == r.toNat && given.length == g.toNat then some (kind, name, given, readings)
  else none

/-- Whether the text of a list of cases reads back as those cases, after the line of the
format. -/
def readsBack (cases : List Case) : Bool :=
  let lines := ((Case.text cases).splitOn "\n").dropLast
  lines.map readLine ==
    (Case.format :: cases).map fun c => some (c.kind, c.name, c.given, c.readings)

/-- A word of the text: not empty, and no blank in it. -/
def isWord (s : String) : Bool := !s.isEmpty && s.all fun c => !c.isWhitespace

/-- The case of a kind and a name in the battery. -/
def find (kind name : String) : Option Case :=
  Case.battery.find? fun c => c.kind == kind && c.name == name

-- The battery's text reads back: every line gives its case's kind, name and numbers again.
#guard readsBack Case.battery

-- Every kind and every name of the battery is one word, and no kind has a name twice.
#guard Case.battery.all fun c => isWord c.kind && isWord c.name

#guard (Case.battery.map fun c => (c.kind, c.name)).eraseDups.length == Case.battery.length

-- The battery by kind: 11 pairs mixed, 15 easings, 15 easings at each of 5 durations, 16
-- transitions and 11 tracks.
#guard ["mix", "at", "of", "timed", "track"].map (fun k =>
    (Case.battery.filter fun c => c.kind == k).length) == [11, 15, 75, 16, 11]

-- One line, typed by hand. The linear easing at the shares of a duration of one: given are the
-- duration `1` and the easing `0 2 0 1000`, five numbers; the readings are `0` and `1000`.
#guard (Case.share "linear/1" Easing.linear 1).line ==
  "of\tlinear/1\t5\t1\t0\t2\t0\t1000\t2\t0\t1000"

-- The first line of a table names the format.
#guard (Case.text []) == "format\twhatwg-motion-1\t0\t0\n"

-- A track's line gives its change and its transition: a shift from (5, 5) to (-5, -5) is
-- `0 5 5 -5 -5`, then the delay `400`, the duration `0` and the linear easing `0 2 0 1000`.
#guard (find "track" "shift-at-once").map (·.given) == some [0, 5, 5, -5, -5, 400, 0, 0, 2, 0, 1000]

/-! ### The numbers given read back as the data

A test in C reads an easing, a transition and a change from the numbers given. These readers do
the same in Lean, and the guards hold that the battery's numbers give its data again. -/

/-- An easing from the numbers of `Easing.numbers`, and the numbers after it. -/
def readEasing : List Int → Option (Easing × List Int)
  | 0 :: k :: rest =>
    if k.toNat ≤ rest.length then some (.stops (rest.take k.toNat), rest.drop k.toNat) else none
  | 1 :: y1 :: y2 :: rest => some (.cubic y1 y2, rest)
  | _ => none

/-- A transition from the numbers of `Transition.numbers`, and the numbers after it. -/
def readTransition : List Int → Option (Transition × List Int)
  | delay :: duration :: rest =>
    (readEasing rest).map fun (e, more) => (⟨delay.toNat, duration.toNat, e⟩, more)
  | _ => none

/-- A count and that many segments, eight numbers each, and the numbers after them. -/
def readSegments : List Int → Option (List ICubic × List Int)
  | n :: rest =>
    let rec go : Nat → List Int → Option (List ICubic × List Int)
      | 0, xs => some ([], xs)
      | k + 1, a :: b :: c :: d :: e :: f :: g :: h :: xs =>
        (go k xs).map fun (segments, more) => (⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩⟩ :: segments, more)
      | _, _ => none
    go n.toNat rest
  | _ => none

/-- A change from the numbers of `Change.numbers`, and the numbers after it. -/
def readChange : List Int → Option (Change × List Int)
  | 0 :: ax :: ay :: bx :: by' :: rest => some (.shift ⟨ax, ay⟩ ⟨bx, by'⟩, rest)
  | 1 :: a :: b :: rest => some (.grow a b, rest)
  | 2 :: a :: b :: rest => some (.reveal a b, rest)
  | 3 :: a :: b :: rest => some (.fade a b, rest)
  | 4 :: rest => do
    let (a, more) ← readSegments rest
    let (b, more) ← readSegments more
    some (.morph a b, more)
  | _ => none

-- Each easing and each transition of the battery reads back from its numbers, with nothing
-- left over.
#guard Case.easings.all fun (_, e) => readEasing e.numbers == some (e, [])

#guard Case.transitions.all fun (_, tr) => readTransition tr.numbers == some (tr, [])

-- Each track of the battery: its change reads back from the numbers given, and its transition
-- from what is left.
#guard Case.tracks.all fun tr =>
  (readChange (tr.change.numbers ++ tr.timing.numbers)).bind (fun (c, more) =>
    (readTransition more).map fun (timing, rest) => (c, timing, rest)) ==
      some (tr.change, tr.timing, [])

/-! ## Entries of the tables, against numbers computed by hand -/

-- `mix 0 100 e` is `100 + (-100) * (1000 - e) / 1000`, rounded down.
-- At `e = -100`: `100 + (-110000) / 1000 = -10`. At `e = 333`: `100 + (-66700) / 1000`, and
-- `-66.7` rounded down is `-67`, so `33`. At `e = 1100`: `100 + 10000 / 1000 = 110`.
-- The line's entry `i` is at `e = -100 + i`.
#guard (find "mix" "up").map (fun c => [c.readings[0]?, c.readings[433]?, c.readings[1200]?]) ==
  some [some (-10), some 33, some 110]

-- The way back is not the way there turned about: `mix 100 0 333` is `0 + 66700 / 1000 = 66`,
-- and `33 + 66` is one short of a hundred. Both are rounded down.
#guard (find "mix" "down").map (fun c => c.readings[433]?) == some (some 66)

-- A way of one unit: `mix 0 1 500` is `1 + (-500) / 1000 = 1 + (-1) = 0`, and `mix 1 0 500` is
-- `0 + 500 / 1000 = 0`. Neither is at its end until the progress is.
#guard mix 0 1 500 == 0 && mix 1 0 500 == 0 && mix 0 1 1000 == 1 && mix 1 0 0 == 1

-- Coordinates of a thousand million: at `e = 250` three quarters of the way are left, so
-- `1000000000 + (-2000000000) * 750 / 1000 = -500000000`.
#guard (find "mix" "far-up").map (fun c => c.readings[350]?) == some (some (-500000000))

-- `Easing.backOut` is `cubic 1567 1000`. At `p = 700`:
-- `3 * 1567 * 700 * 300² = 296163000000`, `3 * 1000 * 700² * 300 = 441000000000`,
-- `1000 * 700³ = 343000000000`; their sum is `1080163000000`, and over `10⁹` that is `1080`.
#guard Easing.backOut.table[700]? == some 1080

-- At the half of a duration of 270: `135³ * (3 * 1567 + 3 * 1000 + 1000) / 270³` is
-- `8701 / 8 = 1087.625`, so `1087`. The duration is not in the answer, and the half of a
-- thousand reads the same.
#guard (Easing.backOut.shares 270)[135]? == some 1087 && Easing.backOut.table[500]? == some 1087

-- `Case.backIn` is `cubic 0 (-567)`. At `p = 500`: `3 * (-567) * 500² * 500 = -212625000000` and
-- `1000 * 500³ = 125000000000`; the sum is `-87625000000`, and `-87.625` rounded down is `-88`.
#guard Case.backIn.table[500]? == some (-88)

-- The battery has what it says: easings past `1000`, and easings below `0`.
#guard [Easing.backOut, Case.bothWays, Case.spring, Case.sevenths].all fun e =>
  e.table.any (· > 1000)

#guard [Case.backIn, Case.bothWays, Case.sevenths].all fun e => e.table.any (· < 0)

-- `Case.sevenths` is `[0, -80, 300, 1100, 1045, 960, 1010, 1000]`: seven pieces.
-- At `p = 100`: `700` of a thousand into the first piece, `0 + (-80) * 700 / 1000 = -56`.
-- At `p = 150`: `1050` is the second piece and `50` into it, `-80 + 380 * 50 / 1000 = -61`.
-- At `p = 700`: `4900` is the fifth piece and `900` into it, `1045 + (-85) * 900 / 1000`, and
-- `-76.5` rounded down is `-77`, so `968`.
#guard [100, 150, 700].map (Case.sevenths.table[·]?) == [some (-56), some (-61), some 968]

-- `Case.thirds` is `[0, 500, 1000, 250]`. At `p = 999`: `2997` is the third piece and `997`
-- into it, `1000 + (-750) * 997 / 1000`, and `-747.75` rounded down is `-748`, so `252`. At
-- the end it reads its last value, `250`: it is not proper.
#guard Case.thirds.table[999]? == some 252 && Case.thirds.table[1000]? == some 250

-- Fewer than two stops: no stop reads `0` at every moment, and one stop reads its value.
#guard (Easing.stops []).table == List.replicate 1001 0

#guard (Easing.stops [700]).table == List.replicate 1001 700

-- The shares of nothing: one entry, the easing's start. A division by `0` gives `0` here.
#guard Case.easings.all fun (_, e) => e.shares 0 == [e.at 0]

-- Heights a hundred times the whole way, `cubic 100000 (-100000)`. At `p = 500` the two heights
-- weigh the same and cancel: `1000 * 500³ / 10⁹ = 125`. At `p = 250`:
-- `3 * 100000 * 250 * 750 * (750 - 250) + 1000 * 250³ = 28140625000000`, so `28140`.
#guard (Easing.cubic 100000 (-100000)).table[500]? == some 125 &&
  (Easing.cubic 100000 (-100000)).table[250]? == some 28140

-- lean4-effect4's kept things: a duration of 450 and the stops of `Case.settle`, twenty pieces.
-- At `t = 225`, the half, the share falls on the stop `10`, which is `888`.
-- At `t = 100`: `100 * 20 = 2000` is the piece `4` of `450` and `200` into it, between `438`
-- and `555`: `438 + 117 * 200 / 450 = 438 + 52 = 490`. A reader that rounds the share to a per
-- mille first reads `222`, and `438 + 117 * 22 / 50 = 489`: one less.
#guard (find "timed" "move").map (fun c => [c.readings[225]?, c.readings[100]?]) ==
  some [some 888, some 490]

-- A delay of 180 and a duration of 270, by `Easing.backOut`: its start until `180`, the half
-- of its duration at `315`, which reads `1087` as above, and its end from `450`.
#guard (find "timed" "late-270").map (fun c =>
    [c.readings[0]?, c.readings[180]?, c.readings[315]?, c.readings[450]?, c.readings[1000]?]) ==
  some [some 0, some 0, some 1087, some 1000, some 1000]

-- No duration: the start until the delay is over, and the end from that moment on.
#guard (find "timed" "at-once-late").map (fun c => [c.readings[399]?, c.readings[400]?]) ==
  some [some 0, some 1000]

-- A delay past the step: the start at every moment.
#guard (find "timed" "never").map (·.readings) == some (List.replicate 1001 0)

-- An easing that is not proper: its own start before, and its own end, `250`, after.
#guard (find "timed" "not-proper").map (fun c => [c.readings[100]?, c.readings[433]?]) ==
  some [some 0, some 250]

/-- The track of a name in the battery. -/
def track (name : String) : Option (Track String) := Case.tracks.find? fun tr => tr.key == name

-- A shift from (-300, 72) to (15, -9) by the transition above. At `t = 315` the eased progress
-- is `1087`, past the end, so the thing is past its place:
-- `15 + (-315) * (-87) / 1000 = 15 + 27 = 42`, and `-9 + 81 * (-87) / 1000`, where `-7.047`
-- rounded down is `-8`, so `-17`.
#guard (track "shift-back").map (fun tr => tr.table[315]?) == some (some [42, -17])

-- A change of shape from one segment to two, by the same transition: the pose has the eight
-- coordinates of the one segment until the eased progress is `500`, and the sixteen of the two
-- from then on. `Easing.backOut` at the share `34 / 270` is under `500` and at `35 / 270` over
-- it, so the pose changes size at the moment `180 + 35 = 215`.
#guard (track "morph-jump").map (fun tr => tr.table.map List.length) ==
  some (List.replicate 215 8 ++ List.replicate 786 16)

-- The stops `[0, 800, 300, 1000]` cross `500` three times. Rising at `2.4 p`: under `500` to
-- `p = 208`. Falling from `800` by `500 * (3 p - 1000) / 1000`: `500` at `p = 533` and `499`
-- from `534`. Rising from `300` by `700 * (3 p - 2000) / 1000`: `498` at `761` and `500` at
-- `762`. So two segments at the moments `0 … 208` and `534 … 761`, and one at the others.
#guard (track "morph-jump-thrice").map (fun tr => tr.table.map List.length) ==
  some (List.replicate 209 16 ++ List.replicate 325 8 ++ List.replicate 228 16 ++
    List.replicate 239 8)

-- From no segment: nothing until the progress is `500`, and the segment from then on.
#guard (track "morph-from-none").map (fun tr => tr.table.map List.length) ==
  some (List.replicate 500 0 ++ List.replicate 501 8)

/-! ## Readers: the laws of the machine at the battery -/

/-- The check a consumer runs on its look: the tracks of the battery are small, by `decide`. -/
theorem tracks_small : Motion.Small Case.tracks := by decide

/-- So a machine of 64 bits computes each of them as `Track.at` says, at every moment of a
step: `Motion.at?_eq` at the battery. -/
theorem tracks_fit {tr : Track String} (h : tr ∈ Case.tracks) (t : Nat) (ht : t ≤ 1000) :
    tr.at? t = some (tr.at t) :=
  Motion.at?_eq Case.tracks tracks_small h t (by omega)

/-- Held inside its step, a motion is small by its easings and its changes alone:
`Motion.small_within` at the battery, whose tracks have delays up to `1200`. -/
theorem tracks_within_small : (Motion.within Case.tracks).Small :=
  Motion.small_within Case.tracks (by decide) (by decide)

/-- Every easing of the battery is small, the one with heights a hundred times the whole way
too: it is at the bound. -/
theorem easings_small : ∀ p ∈ Case.easings, p.2.Small := by decide

/-- Every transition of the battery is small. -/
theorem transitions_small : ∀ p ∈ Case.transitions, p.2.Small := by decide

/-- So each transition of the battery reads within `±100000` at every moment
(`Transition.at_size`), and a machine computes it as `Transition.at` says. -/
theorem transitions_fit {p : String × Transition} (h : p ∈ Case.transitions) (t : Nat)
    (ht : t ≤ 1000) : Size (p.2.at t) 100000 ∧ p.2.at? t = some (p.2.at t) :=
  ⟨Transition.at_size p.2 t (transitions_small p h).2.2,
    Transition.at?_eq p.2 t (transitions_small p h) (by omega)⟩

/-- The shift of the battery that goes past its end. -/
def shiftBack : Track String :=
  ⟨"shift-back", .shift ⟨-300, 72⟩ ⟨15, -9⟩,
    { delay := 180, duration := 270, ease := Easing.backOut }⟩

/-- A program whose numbers are the entry of a track's table has computed the pose:
`Track.eq_of_table` at that shift. The entry at the moment `315` is `42` and `-17`, so a shift
with those two numbers is the pose of the track there. -/
theorem shiftBack_pose : Pose.shift ⟨42, -17⟩ = shiftBack.at 315 :=
  Track.eq_of_table shiftBack 315 (by decide) rfl (by decide +kernel)

/-! ## Controls -/

/-- `mix` with C's own division, which rounds toward zero: what a transcription computes that
writes `/` for `/`. -/
def mixTowardZero (u v e : Int) : Int := v + ((u - v) * (1000 - e)).tdiv 1000

/-- A cubic at a moment with C's own division. -/
def cubicTowardZero (y1 y2 : Int) (p : Nat) : Int :=
  let q : Int := p
  (3 * y1 * q * (1000 - q) ^ 2 + 3 * y2 * q ^ 2 * (1000 - q) + 1000 * q ^ 3).tdiv 1000000000

-- A division by `0` gives `0`, as Lean's does. In C it is not defined, so `fdiv` tests for it.
#guard fdiv 7 0 == 0 && fdiv (-7) 0 == 0 && (-7 : Int) / 0 == 0

-- The two divisions at a named case: half a unit below nothing is `0` toward zero, and `-1`
-- rounded down.
#guard Int.tdiv (-500) 1000 == 0 && fdiv (-500) 1000 == -1 && (-500 : Int) / 1000 == -1

-- So a thing on its way from `0` to `1` has arrived at the half with C's division, and has
-- not left with the kit's.
#guard mixTowardZero 0 1 500 == 1 && mix 0 1 500 == 0

-- Over the line `up` of the battery, `0` to `100` at the eased progress `-100 … 1100`: the way
-- left is negative until the progress is `1000`, and the product is a whole thousand only at
-- every tenth progress. So C's division is one off at `1100 - 110 = 990` of the 1201 entries.
#guard ((List.range 1201).filter fun (i : Nat) =>
    mixTowardZero 0 100 (-100 + i) != mix 0 100 (-100 + i)).length == 990

-- Over the line `down`, `100` to `0`: the product is negative only past the end, at the
-- progress `1001 … 1100`, less the ten that are whole thousands: `90` entries.
#guard ((List.range 1201).filter fun (i : Nat) =>
    mixTowardZero 100 0 (-100 + i) != mix 100 0 (-100 + i)).length == 90

-- An easing below `0`: `-87.625` is `-87` toward zero and `-88` rounded down.
#guard cubicTowardZero 0 (-567) 500 == -87 && Easing.cubicAt 0 (-567) 500 == -88

-- An easing that does not go below `0` is not safe either: where the kit's own `backOut` is
-- past its end, a value that falls is mixed by a negative product.
#guard mixTowardZero (-300) 15 1087 == 42 && mixTowardZero 72 (-9) 1087 == -16 &&
  mix 72 (-9) 1087 == -17

-- 32 bits. The last term of a cubic at the half of lean4-effect4's duration of 270,
-- `1000 * 135³ = 2460375000`, is over `2³¹ = 2147483648`: a number of 32 bits does not hold a
-- value of the kit's `cubicOut`, and one of 64 does.
#guard (1000 * (135 : Int) ^ 3).natAbs ≥ 2 ^ 31 && decide (Fits (1000 * (135 : Int) ^ 3)) &&
  Easing.cubicOf? 1000 1000 135 270 == some (Easing.cubicOf 1000 1000 135 270)

-- 32 bits again: a thing three thousand units from its place, counted in thousandths, at the
-- start of its way: `3000000 * 1000` is over `2³¹`.
#guard ((3000000 - 0) * (1000 - 0) : Int).natAbs ≥ 2 ^ 31 && mix? 3000000 0 0 == some 3000000

-- Past the bounds of `Small` the machine may have no reading. A duration of a hundred thousand
-- with heights at the bound: `3 * 100000 * 50000 * 50000²` is `3.75 * 10²²`.
#guard Easing.cubicOf? 100000 100000 50000 100000 == none

-- `Small` is a test that suffices. The kit's `cubicOut` at the same share of the same duration
-- fits: `1 - (1/2)³` is `875` per mille.
#guard Easing.cubicOf? 1000 1000 50000 100000 == some 875 &&
  !decide (({ duration := 100000, ease := Easing.cubicOut } : Transition).Small)

-- A coordinate of ten thousand million million does not fit a product by a thousand, and one
-- of a thousand million million does: the bound of `Small`, a thousand million, is far inside.
#guard mix? 10000000000000000 0 0 == none && mix? 1000000000000000 0 0 == some 1000000000000000

end WhatwgTest.Svg.MotionVector
