import Whatwg.Svg.Geometry.Box

/-!
# Whatwg.Svg.Geometry.Noise

Owner: value noise along a line, exact in `Rat`. A program that draws by hand wants a number
that wanders with the length run along a line, stays in a band, and is the same each time the
picture is drawn. It gives a line a width that is not even, or an edge that is not straight.

How it is built:

- `hash` mixes a seed and the number of a cell into 32 bits, and `cell` reads that as one of
  2001 values from `-1` to `1`.
- `value` cuts the line into cells `wave` long. Each cell has its value, and between two cells
  the noise steps from one value to the next along `smooth`, so it has no corner where two
  cells meet.
- `two` adds a second octave: half the wavelength, half the weight.
- `seedOf` makes a seed of a key, so that a mark keeps its noise while its key stays.
- `envelope` fades a noise in from the start of a line and out towards its end.

The cell of a length is a floor and the place in the cell is exact: nothing is rounded.

The laws are the bands, and none has a premise: `cell`, `value` and `two` are in `[-1, 1]` for
every seed, wave and length, and `envelope` is in `[0, 1]`. `smooth` takes `[0, 1]` into
`[0, 1]`, so it needs no clamp.

What this module does not claim: that `hash` spreads its values evenly, or that two seeds give
noises that have nothing to do with each other; that the noise is smooth in the sense of
analysis, which is a statement about real numbers; a noise over the plane. For a wave of zero
every length is in the first cell, since `Rat` divides by zero to zero, and a length below
zero reads the first two cells again and again.
-/

namespace Whatwg.Svg.Value

namespace Noise

/-- A 32-bit mix of a seed and the number of a cell: two multiplications that wrap at `2 ^ 32`,
joined by exclusive or, and two rounds of shifting to bring the high bits down. -/
def hash (seed cell : Nat) : Nat :=
  let m := 4294967296
  let h := ((cell + 374761393) * 668265263 % m) ^^^ ((seed + 1442695041) * 2246822519 % m)
  let h := ((h ^^^ (h >>> 13)) * 1274126177) % m
  h ^^^ (h >>> 16)

/-- The value of a cell, in `[-1, 1]` (`cell_band`): one of 2001 values a thousandth apart. -/
def cell (seed cell : Nat) : Rat := ((hash seed cell % 2001 : Nat) : Rat) / 1000 - 1

/-- Smoothstep: `t² (3 - 2t)`. It is `0` at `0` and `1` at `1`, leaves both with no slope, and
takes `[0, 1]` into `[0, 1]` (`smooth_band`). -/
def smooth (t : Rat) : Rat := t * t * (3 - 2 * t)

/-- **Value noise** at the length `s` along a line, with cells `wave` long: between the values
of the two cells around `s`, along `smooth`. The cell is the floor of `s / wave`, and the
place in the cell is what is left of `s / wave` past its floor. -/
def value (seed : Nat) (wave s : Rat) : Rat :=
  cell seed (s / wave).floor.toNat +
    smooth (s / wave - ((s / wave).floor : Rat)) *
      (cell seed ((s / wave).floor.toNat + 1) - cell seed (s / wave).floor.toNat)

/-- **Noise of two octaves** at the length `s`: the value noise, and the value noise of the
next seed at half the wavelength and half the weight. In `[-1, 1]` (`two_band`). -/
def two (seed : Nat) (wave s : Rat) : Rat :=
  (2 * value seed wave s + value (seed + 1) (wave / 2) s) / 3

/-- The seed of a key: the FNV-1a hash of the codes of its characters, in 32 bits. -/
def seedOf (key : String) : Nat :=
  key.foldl (fun h c => ((h ^^^ c.toNat) * 16777619) % 4294967296) 2166136261

/-- The share of a noise at the length `s` of a line `total` long: none at either end, all of
it beyond `ramp` from both, and in step between. A ramp of zero does not fade. In `[0, 1]`
(`envelope_band`). -/
def envelope (ramp total s : Rat) : Rat :=
  if ramp = 0 then 1 else max 0 (min 1 (min (s / ramp) ((total - s) / ramp)))

/-! ## The bands -/

/-- The value of a cell is in `[-1, 1]`. -/
theorem cell_band (seed k : Nat) : -1 ≤ cell seed k ∧ cell seed k ≤ 1 := by
  unfold cell
  generalize hash seed k = h
  have h0 : (0 : Rat) ≤ ((h % 2001 : Nat) : Rat) := Rat.natCast_nonneg
  have h1 : ((h % 2001 : Nat) : Rat) ≤ ((2000 : Nat) : Rat) :=
    Rat.natCast_le_natCast.mpr (by omega)
  have e : ((2000 : Nat) : Rat) = 2000 := Rat.natCast_ofNat
  rw [e] at h1
  generalize ((h % 2001 : Nat) : Rat) = q at h0 h1 ⊢
  constructor <;> grind

/-- Smoothstep takes `[0, 1]` into `[0, 1]`. -/
theorem smooth_band {t : Rat} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ smooth t ∧ smooth t ≤ 1 := by
  have a : 0 ≤ t * t * (3 - 2 * t) := Rat.mul_nonneg (rat_mul_self_nonneg t) (by grind)
  have b : 0 ≤ (1 - t) * (1 - t) * (1 + 2 * t) :=
    Rat.mul_nonneg (rat_mul_self_nonneg (1 - t)) (by grind)
  unfold smooth
  constructor <;> grind

/-- What a number is past its floor is in `[0, 1]`. -/
theorem fract_band (x : Rat) : 0 ≤ x - (x.floor : Rat) ∧ x - (x.floor : Rat) ≤ 1 := by
  have h0 := Rat.floor_le x
  have h1 := Rat.lt_floor_add_one x
  constructor <;> grind

/-- **Value noise is in `[-1, 1]`**, for every seed, wave and length: a step between the values
of two cells (`Box.step_mem`). -/
theorem value_band (seed : Nat) (wave s : Rat) :
    -1 ≤ value seed wave s ∧ value seed wave s ≤ 1 := by
  have hf := fract_band (s / wave)
  have hu := smooth_band hf.1 hf.2
  have ha := cell_band seed (s / wave).floor.toNat
  have hb := cell_band seed ((s / wave).floor.toNat + 1)
  unfold value
  exact Box.step_mem ha.1 ha.2 hb.1 hb.2 hu.1 hu.2

/-- **The noise of two octaves is in `[-1, 1]`**, for every seed, wave and length. -/
theorem two_band (seed : Nat) (wave s : Rat) : -1 ≤ two seed wave s ∧ two seed wave s ≤ 1 := by
  have h1 := value_band seed wave s
  have h2 := value_band (seed + 1) (wave / 2) s
  unfold two
  -- The two octaves are named before the arithmetic. Left as they stand, the search compares
  -- them by unfolding both down to the hash, whose 32-bit factors exhaust the memory.
  generalize value seed wave s = a at h1 ⊢
  generalize value (seed + 1) (wave / 2) s = b at h2 ⊢
  constructor <;> grind

/-- **The envelope is in `[0, 1]`**, for every ramp and every two lengths. -/
theorem envelope_band (ramp total s : Rat) :
    0 ≤ envelope ramp total s ∧ envelope ramp total s ≤ 1 := by
  unfold envelope
  split <;> constructor <;> grind

end Noise

end Whatwg.Svg.Value
