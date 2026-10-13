import Whatwg.Svg.Scene.Between
import Whatwg.Svg.Scene.Vector

/-!
# Whatwg.Svg.Scene.Machine

Owner: the readings of motion as a machine computes them (slice S17; ask W3 of
`docs/research/2026-10-12-whatwg-requests.md`).

The readings of `Whatwg/Svg/Scene/Motion.lean` are whole-number arithmetic with one division
that rounds down, so a program in C can transcribe them. Two things make a transcription differ
from Lean, and neither shows until a picture is one unit off.

- **The division.** Lean's `/` on `Int` rounds down for a divisor that is not negative. C's `/`
  rounds toward zero, and its `%` has the sign of the dividend: they are `Int.tdiv` and
  `Int.tmod`. The two divisions differ wherever a negative number is divided and does not
  divide evenly: in `mix` of a value that rises, at every moment before its end, and of one
  that falls, past its end; in a cubic below `0`; and in stops that fall.
- **The width.** `Easing.cubicOf` at the middle of a duration of a thousand adds products near
  `10 ^ 12` before it divides. A number of 32 bits holds `2 ^ 31`.

This module says in Lean what the machine computes, and proves it equal to the readings.

- `fdiv a b`: division that rounds down, from C's two operations. It is `/` for a divisor that
  is not negative (`fdiv_eq`), and `0` for the divisor `0`, as `/` is. Every value inside it is
  no larger than `a` (`fdiv_inside`).
- **Each reading with `fdiv` for `/`**, every number an integer: `mix_fdiv`,
  `Easing.cubicAt_fdiv`, `Easing.cubicOf_fdiv`, `Easing.stopsOf_fdiv`. A reader transcribes
  the right side of each line by line. These hold of every input, with numbers of any size.
  `Easing.stopsAt` and `Easing.at` are the same at a share of a thousand
  (`Easing.stopsOf_thousand`, `Easing.of_thousand`), and the other readings divide nothing.
- `Fits x`: a signed number of 64 bits holds `x`, which is less than `2 ^ 63` in size.
  `hold x next`: one value that a machine holds. Where it fits, what comes next reads it; where
  it does not, the machine has no reading.
- **Each reading value by value**: `mix?`, `Easing.cubicOf?`, `Easing.stopsOf?`, `Easing.of?`,
  `Easing.at?`, `Transition.at?`, `ICubic.mix?`, `Change.at?`, `Track.at?`. Every sum, difference
  and product is one value held, in the order a program in C writes them. A division is not held:
  nothing inside it is larger than what it divides (`fdiv_inside`).
- `Easing.Small`, `Transition.Small`, `Change.Small`, `Track.Small`, `Motion.Small`: tests on
  the data, each decidable. An easing is small where its stops or its two heights are within
  `±100000`, a hundred times the whole way, and it has `100001` stops at most. A transition is
  small where its duration is `10000` at most, its delay a thousand million at most, and its
  easing small. A change is small where every coordinate, size, part and opacity is within a
  thousand million.
- **The width laws**: on small data every value fits, and what the machine reads is the reading.
  `mix?_eq`, `Easing.cubicOf?_eq`, `Easing.stopsOf?_eq`, `Easing.of?_eq`, `Easing.at?_eq`,
  `Transition.at?_eq`, `ICubic.mix?_eq`, `Change.at?_eq`, `Track.at?_eq`, and for every track of
  a motion `Motion.at?_eq`. A consumer checks its look once:
  `example : motion.Small := by decide`. A motion held inside its step is small where its
  easings and its changes are, whatever its delays (`Transition.small_within`,
  `Motion.small_within`), so the easings of a look are all that a look has to show.
- What the laws rest on. A small easing reads within `±100000` at every share that is no more
  than the whole (`Easing.of_size`), and a transition at every moment (`Transition.at_size`):
  stops read between the least and the greatest of their values (`Easing.stopsOf_mem`), and a
  cubic between its heights, `0` and `1000` (`Easing.cubicOf_mem`). These hold with the
  rounding, below `0` as well as past `1000`.
- **What the machine reads is the reading**, on data of any size: `mix?_sound`,
  `Easing.of?_sound`, `Transition.at?_sound`, `Change.at?_sound`, `Track.at?_sound`. So these
  functions are a check that runs: where `tr.at? t` has a pose, 64 bits held every value on the
  way, and the pose is `tr.at t`.
- **The tables are what the machine computes**: the entry of a table of
  `Whatwg/Svg/Scene/Vector.lean` is what the machine reads, on small data
  (`Easing.table_machine`, `Easing.shares_machine`, `Transition.table_machine`,
  `Track.table_machine`).

How far the bounds are from the width. `2 ^ 63` is over `9.2 * 10 ^ 18`. On small data the laws
bound every value of a cubic by `6.1 * 10 ^ 17`, every value of stops by `2.1 * 10 ^ 18`, and
every value of `mix` by `2.1 * 10 ^ 14`. The bound of stops is loose: it does not use that what
is left of a division is less than the divisor. So no reading of the kit is out of reach of 64
bits at any size a picture has. At 32 bits a cubic of the duration `270` does not fit:
`1000 * 135 ^ 3` is over `2 ^ 31`.

What this module does not claim. It is a model in Lean of a machine, and no program in C is
read here: that a transcription computes what `hold` says is shown by running it against the
tables of `Whatwg/Svg/Scene/Vector.lean`. `Small` is a test that suffices, with round numbers;
data that fails it may still fit, and the machine (`Track.at?`) can be run on it to see. The
laws are for a share that is no more than the whole, which is every share a transition reads;
`Easing.at` past the moment `1000` is not covered. Reading a list at a place is not arithmetic:
the machine keeps `List.getD`, which a program writes as a test of the place against the count.

Five private lemmas here are copies of private lemmas of `Whatwg/Svg/Scene/Between.lean`, which
this module cannot cite: `ediv_le_of_le`, `rest_le`, `sq_eq`, `add_cube` and `cubic_le`.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## The division -/

/-- **Division that rounds down, from the division that rounds toward zero and its
remainder**, which are C's `/` and `%`. The quotient is one less where the remainder is
negative. A divisor of `0` gives `0`. It is the right division for a divisor that is not
negative, which every divisor of a reading is. -/
def fdiv (a b : Int) : Int :=
  if b = 0 then 0
  else if a.tmod b < 0 then a.tdiv b - 1
  else a.tdiv b

/-- A division by `0` gives `0`. -/
theorem fdiv_zero (a : Int) : fdiv a 0 = 0 := if_pos rfl

/-- **`fdiv` is Lean's `/`**, for a divisor that is not negative. So a reading written with
`fdiv` is the reading. -/
theorem fdiv_eq (a b : Int) (hb : 0 ≤ b) : fdiv a b = a / b := by
  cases Decidable.em (b = 0) with
  | inl hz => rw [hz, fdiv_zero, Int.ediv_zero]
  | inr hne =>
    have hpos : 0 < b := by omega
    have hsum : a.tmod b + a.tdiv b * b = a := Int.tmod_add_tdiv_mul a b
    have hlt : a.tmod b < b := Int.tmod_lt_of_pos a hpos
    have hgt : -b < a.tmod b := Int.lt_tmod_of_pos a hpos
    rw [Int.mul_comm] at hsum
    unfold fdiv
    rw [if_neg hne]
    cases Decidable.em (a.tmod b < 0) with
    | inl hr =>
      rw [if_pos hr]
      have hq : a.tmod b + b + b * (a.tdiv b - 1) = a := by
        rw [Int.mul_sub, Int.mul_one]
        omega
      exact ((Int.ediv_emod_unique hpos).mpr ⟨hq, by omega, by omega⟩).1.symm
    | inr hr =>
      rw [if_neg hr]
      exact ((Int.ediv_emod_unique hpos).mpr ⟨hsum, by omega, hlt⟩).1.symm

/-- `fdiv` is the division of Lean's core that rounds down, `Int.fdiv`, for a divisor that is
not negative. That one is defined by the signs of its two numbers, and this one from C's two
operations. -/
theorem fdiv_eq_fdiv (a b : Int) (hb : 0 ≤ b) : fdiv a b = a.fdiv b :=
  (fdiv_eq a b hb).trans (Int.fdiv_eq_ediv_of_nonneg a hb).symm

/-- **Every value inside `fdiv a b` is no larger than `a`**: the quotient toward zero, the
remainder, and the quotient rounded down. So a division overflows nothing. -/
theorem fdiv_inside (a b : Int) (hb : 0 ≤ b) :
    (a.tdiv b).natAbs ≤ a.natAbs ∧ (a.tmod b).natAbs ≤ a.natAbs ∧ (fdiv a b).natAbs ≤ a.natAbs := by
  refine ⟨Int.natAbs_tdiv_le_natAbs a b, ?_, ?_⟩
  · rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  · rw [fdiv_eq a b hb]
    exact Int.natAbs_ediv_le_natAbs a b

/-! ## Each reading with `fdiv` for `/` -/

/-- **`mix` as a machine writes it.** -/
theorem mix_fdiv (u v e : Int) : mix u v e = v + fdiv ((u - v) * (1000 - e)) 1000 :=
  (congrArg (fun q => v + q) (fdiv_eq ((u - v) * (1000 - e)) 1000 (by decide))).symm

/-- A square is a product. -/
private theorem sq_eq (x : Int) : x ^ 2 = x * x := by
  rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- A cube is a product, as a program writes it. -/
private theorem cube_eq (x : Int) : x ^ 3 = x * x * x := by
  rw [Int.pow_succ, sq_eq]

namespace Easing

/-- **A cubic at a share, as a machine writes it**: every power a product, and the one division
`fdiv`. -/
theorem cubicOf_fdiv (y1 y2 : Int) (num den : Nat) :
    cubicOf y1 y2 num den =
      fdiv (3 * y1 * num * (((den : Int) - num) * ((den : Int) - num)) +
          3 * y2 * ((num : Int) * num) * ((den : Int) - num) + 1000 * ((num : Int) * num * num))
        ((den : Int) * den * den) := by
  have hd : (0 : Int) ≤ (den : Int) * den * den :=
    Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg den) (Int.natCast_nonneg den))
      (Int.natCast_nonneg den)
  show (3 * y1 * (num : Int) * ((den : Int) - num) ^ 2 +
    3 * y2 * (num : Int) ^ 2 * ((den : Int) - num) + 1000 * (num : Int) ^ 3) / (den : Int) ^ 3 = _
  rw [sq_eq, sq_eq, cube_eq, cube_eq, fdiv_eq _ _ hd]

/-- **A cubic at a moment, as a machine writes it.** -/
theorem cubicAt_fdiv (y1 y2 : Int) (p : Nat) :
    cubicAt y1 y2 p =
      fdiv (3 * y1 * p * ((1000 - (p : Int)) * (1000 - (p : Int))) +
          3 * y2 * ((p : Int) * p) * (1000 - (p : Int)) + 1000 * ((p : Int) * p * p))
        1000000000 := by
  show (3 * y1 * (p : Int) * (1000 - (p : Int)) ^ 2 + 3 * y2 * (p : Int) ^ 2 * (1000 - (p : Int)) +
    1000 * (p : Int) ^ 3) / 1000000000 = _
  rw [sq_eq, sq_eq, cube_eq, fdiv_eq _ _ (by decide)]

/-- **Stops at a share, as a machine writes them**: every number an integer, and both divisions
`fdiv`. The count of pieces is one less than the count of stops, and `0` where there is no
stop. The place `i` is not negative, so `toNat` changes nothing: a program reads the value at
`i` where `i` is less than the count, and the last value where it is not. -/
theorem stopsOf_fdiv (values : List Int) (num den : Nat) :
    stopsOf values num den =
      (let count : Int := values.length
       let pieces : Int := if count = 0 then 0 else count - 1
       let last : Int := values.getLast?.getD 0
       let whole : Int := num * pieces
       let i : Int := fdiv whole den
       let rest : Int := whole - den * i
       let a : Int := values.getD i.toNat last
       let b : Int := values.getD (i + 1).toNat last
       a + fdiv ((b - a) * rest) den) := by
  have hp : (if (values.length : Int) = 0 then (0 : Int) else (values.length : Int) - 1) =
      ((values.length - 1 : Nat) : Int) := by
    split <;> omega
  have hi : fdiv ((num : Int) * ((values.length - 1 : Nat) : Int)) den =
      ((num * (values.length - 1) / den : Nat) : Int) := by
    rw [fdiv_eq _ _ (Int.natCast_nonneg den), ← Int.natCast_mul, ← Int.natCast_ediv]
  have hle : den * (num * (values.length - 1) / den) ≤ num * (values.length - 1) :=
    Nat.mul_div_le _ _
  have hr : (num : Int) * ((values.length - 1 : Nat) : Int) -
      (den : Int) * ((num * (values.length - 1) / den : Nat) : Int) =
      ((num * (values.length - 1) - den * (num * (values.length - 1) / den) : Nat) : Int) := by
    rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_sub hle]
  have h1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  simp only [stopsOf, hp, hi, hr, h1, Int.toNat_natCast]
  rw [fdiv_eq _ _ (Int.natCast_nonneg den)]

end Easing

/-! ## A machine of 64 bits -/

/-- **A signed number of 64 bits holds `x`**: it is less than `2 ^ 63` in size. -/
def Fits (x : Int) : Prop := x.natAbs < 2 ^ 63

instance (x : Int) : Decidable (Fits x) := inferInstanceAs (Decidable (_ < _))

/-- `x` is no more than `b` in size. The laws below carry a size through each sum, difference,
product and division, so that the size of a value is read off the sizes of the data. -/
def Size (x : Int) (b : Nat) : Prop := x.natAbs ≤ b

instance (x : Int) (b : Nat) : Decidable (Size x b) := inferInstanceAs (Decidable (_ ≤ _))

namespace Size

/-- A number of a size under `2 ^ 63` fits. -/
theorem fits {x : Int} {b : Nat} (h : Size x b) (hb : b < 2 ^ 63) : Fits x :=
  Nat.lt_of_le_of_lt h hb

/-- A number between `-b` and `b` is of the size `b`. -/
theorem of_mem {x : Int} {b : Nat} (h1 : -(b : Int) ≤ x) (h2 : x ≤ b) : Size x b := by
  unfold Size
  omega

/-- A number of the size `b` is between `-b` and `b`. -/
theorem mem {x : Int} {b : Nat} (h : Size x b) : -(b : Int) ≤ x ∧ x ≤ b := by
  unfold Size at h
  constructor
  · omega
  · omega

/-- A count is of its own size. -/
theorem nat {n b : Nat} (h : n ≤ b) : Size (n : Int) b := by
  unfold Size
  rw [Int.natAbs_natCast]
  exact h

/-- The size of a sum is no more than the sum of the sizes. -/
theorem add {x y : Int} {a b : Nat} (hx : Size x a) (hy : Size y b) : Size (x + y) (a + b) :=
  Nat.le_trans (Int.natAbs_add_le x y) (Nat.add_le_add hx hy)

/-- The size of a difference is no more than the sum of the sizes. -/
theorem sub {x y : Int} {a b : Nat} (hx : Size x a) (hy : Size y b) : Size (x - y) (a + b) :=
  Nat.le_trans (Int.natAbs_sub_le x y) (Nat.add_le_add hx hy)

/-- The size of a product is no more than the product of the sizes. -/
theorem mul {x y : Int} {a b : Nat} (hx : Size x a) (hy : Size y b) : Size (x * y) (a * b) := by
  unfold Size
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul hx hy

/-- A quotient rounded down is no larger than what is divided. -/
theorem fdiv {x d : Int} {a : Nat} (hx : Size x a) (hd : 0 ≤ d) : Size (Scene.fdiv x d) a :=
  Nat.le_trans (fdiv_inside x d hd).2.2 hx

end Size

/-- **One value of a machine.** Where the value fits, what comes next reads it. Where it does
not, the machine has no reading: in C the sum or the product is then not defined. -/
def hold {α : Type} (x : Int) (next : Int → Option α) : Option α :=
  if Fits x then next x else none

/-- A value that fits is held, and what comes next reads it. -/
theorem hold_some {α : Type} {x : Int} {next : Int → Option α} {r : α} (h : Fits x)
    (hn : next x = some r) : hold x next = some r :=
  (if_pos h).trans hn

/-- A machine that has a reading held every value on the way to it. -/
theorem fits_of_hold {α : Type} {x : Int} {next : Int → Option α} {r : α}
    (h : hold x next = some r) : Fits x ∧ next x = some r := by
  unfold hold at h
  cases Decidable.em (Fits x) with
  | inl hx =>
    rw [if_pos hx] at h
    exact ⟨hx, h⟩
  | inr hx =>
    rw [if_neg hx] at h
    exact nomatch h

/-! ## Mixing -/

/-- **`mix`, value by value**: the way, what is left of the progress, their product, and the sum. -/
def mix? (u v e : Int) : Option Int :=
  hold (u - v) fun way =>
  hold (1000 - e) fun left =>
  hold (way * left) fun whole =>
  hold (v + fdiv whole 1000) some

/-- **Mixing fits.** Two values within a thousand million, mixed at an eased progress within
`±100000`, are mixed by a machine of 64 bits as `mix` says. -/
theorem mix?_eq (u v e : Int) (hu : Size u 1000000000) (hv : Size v 1000000000)
    (he : Size e 100000) : mix? u v e = some (mix u v e) := by
  have h1 := hu.sub hv
  have h2 := (by decide : Size (1000 : Int) 1000).sub he
  have h3 := h1.mul h2
  have h4 := hv.add (h3.fdiv (d := 1000) (by decide))
  rw [mix_fdiv]
  exact hold_some (h1.fits (by decide)) (hold_some (h2.fits (by decide))
    (hold_some (h3.fits (by decide)) (hold_some (h4.fits (by decide)) rfl)))

/-! ## Easings: where a reading lies -/

/-- A quotient rounded down is no more than `b`, where the dividend is no more than `b` times
the divisor: with the divisor `0` too, where the quotient is `0`. -/
private theorem ediv_le_of_le (a b c : Int) (hc : 0 ≤ c) (hb : 0 ≤ b) (h : a ≤ b * c) :
    a / c ≤ b := by
  rcases Int.lt_or_eq_of_le hc with hc | hc
  · exact Int.ediv_le_of_le_mul hc h
  · rw [← hc, Int.ediv_zero]
    exact hb

/-- A quotient rounded down is no less than `b`, where the dividend is no less than `b` times
the divisor: with the divisor `0` too. -/
private theorem le_ediv_of_le (a b c : Int) (hc : 0 ≤ c) (hb : b ≤ 0) (h : b * c ≤ a) :
    b ≤ a / c := by
  rcases Int.lt_or_eq_of_le hc with hc | hc
  · exact Int.le_ediv_of_mul_le hc h
  · rw [← hc, Int.ediv_zero]
    exact hb

/-- A point of the straight line from `a` to `b`, rounded down, is between what both are
between. With the divisor `0` the point is `a`. -/
private theorem line_mem (lo hi a b r d : Int) (hr : 0 ≤ r) (hd : r ≤ d ∨ d = 0)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ a + (b - a) * r / d ∧ a + (b - a) * r / d ≤ hi := by
  rcases hd with hd | hd
  · have hd0 : 0 ≤ d := Int.le_trans hr hd
    have up : (b - a) * r / d ≤ hi - a :=
      ediv_le_of_le _ _ _ hd0 (by omega)
        (Int.le_trans (Int.mul_le_mul_of_nonneg_right (by omega : b - a ≤ hi - a) hr)
          (Int.mul_le_mul_of_nonneg_left hd (by omega)))
    have down : lo - a ≤ (b - a) * r / d :=
      le_ediv_of_le _ _ _ hd0 (by omega)
        (Int.le_trans (Int.mul_le_mul_of_nonpos_left (by omega) hd)
          (Int.mul_le_mul_of_nonneg_right (by omega : lo - a ≤ b - a) hr))
    constructor
    · omega
    · omega
  · rw [hd, Int.ediv_zero]
    constructor
    · omega
    · omega

/-- What is left of a number after its whole shares of `den` is no more than `den`, where `den`
is not `0`. -/
private theorem rest_le (n den : Nat) :
    ((n - den * (n / den) : Nat) : Int) ≤ (den : Int) ∨ (den : Int) = 0 := by
  cases den with
  | zero => exact Or.inr rfl
  | succ k =>
    refine Or.inl (Int.ofNat_le.mpr ?_)
    rw [← Nat.mod_def]
    exact Nat.le_of_lt (Nat.mod_lt n (Nat.succ_pos k))

/-- The cube of a sum is the sum of four weights: one cube, each mixed product three times, and
the other cube. -/
private theorem add_cube (a b : Int) :
    (a + b) * ((a + b) * (a + b)) =
      a * (a * a) + (a * (a * b) + a * (a * b) + a * (a * b)) +
        (a * (b * b) + a * (b * b) + a * (b * b)) + b * (b * b) := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_comm b a, Int.mul_left_comm b a]
  omega

/-- The numerator of a cubic at the progress `q` of `q + s` is no more than `m` times the cube
of the whole, where the two heights and the end `1000` are no more than `m`. -/
private theorem cubic_le (y1 y2 m q s : Int) (hq : 0 ≤ q) (hs : 0 ≤ s) (h1 : y1 ≤ m)
    (h2 : y2 ≤ m) (hm : 1000 ≤ m) :
    3 * y1 * q * s ^ 2 + 3 * y2 * q ^ 2 * s + 1000 * q ^ 3 ≤ m * (q + s) ^ 3 := by
  have w0 : 0 ≤ s * (s * s) := Int.mul_nonneg hs (Int.mul_nonneg hs hs)
  have w1 : 0 ≤ q * (s * s) := Int.mul_nonneg hq (Int.mul_nonneg hs hs)
  have w2 : 0 ≤ q * (q * s) := Int.mul_nonneg hq (Int.mul_nonneg hq hs)
  have w3 : 0 ≤ q * (q * q) := Int.mul_nonneg hq (Int.mul_nonneg hq hq)
  have f0 : 0 ≤ m * (s * (s * s)) := Int.mul_nonneg (Int.le_trans (by decide) hm) w0
  have f1 : y1 * (q * (s * s)) ≤ m * (q * (s * s)) := Int.mul_le_mul_of_nonneg_right h1 w1
  have f2 : y2 * (q * (q * s)) ≤ m * (q * (q * s)) := Int.mul_le_mul_of_nonneg_right h2 w2
  have f3 : 1000 * (q * (q * q)) ≤ m * (q * (q * q)) := Int.mul_le_mul_of_nonneg_right hm w3
  have c3 : ∀ x : Int, x ^ 3 = x * (x * x) := fun x => by rw [cube_eq, Int.mul_assoc]
  simp only [sq_eq, c3, Int.mul_assoc]
  rw [add_cube]
  simp only [Int.mul_add]
  omega

/-- The numerator of a cubic is no less than `-m` times the cube of the whole, where the two
heights are no less than `-m`: the bound above, of the cubic with its heights turned about. -/
private theorem le_cubic (y1 y2 m q s : Int) (hq : 0 ≤ q) (hs : 0 ≤ s) (h1 : -m ≤ y1)
    (h2 : -m ≤ y2) (hm : 1000 ≤ m) :
    -(m * (q + s) ^ 3) ≤ 3 * y1 * q * s ^ 2 + 3 * y2 * q ^ 2 * s + 1000 * q ^ 3 := by
  have h := cubic_le (-y1) (-y2) m q s hq hs (by omega) (by omega) hm
  have hc : 0 ≤ q ^ 3 := Int.pow_nonneg hq
  simp only [Int.mul_neg, Int.neg_mul] at h
  omega

namespace Easing

/-- **Stops read between the least and the greatest of their values**, at every share: where
`0` and every value are from `lo` to `hi`, so is the reading. A missing value reads as `0`, so
`0` is one of the things between. It holds below `0` as well as past `1000`. -/
theorem stopsOf_mem (lo hi : Int) (values : List Int) (num den : Nat) (h0 : lo ≤ 0 ∧ 0 ≤ hi)
    (h : ∀ v ∈ values, lo ≤ v ∧ v ≤ hi) :
    lo ≤ stopsOf values num den ∧ stopsOf values num den ≤ hi := by
  have hlast : lo ≤ values.getLast?.getD 0 ∧ values.getLast?.getD 0 ≤ hi :=
    last_of_all (fun v => lo ≤ v ∧ v ≤ hi) values 0 h0 h
  have hget : ∀ i, lo ≤ values.getD i (values.getLast?.getD 0) ∧
      values.getD i (values.getLast?.getD 0) ≤ hi := fun i =>
    getD_of_all (fun v => lo ≤ v ∧ v ≤ hi) values i _ hlast h
  exact line_mem lo hi _ _ _ _ (Int.natCast_nonneg _) (rest_le _ den) (hget _) (hget _)

/-- **A cubic reads between its heights, `0` and `1000`**, at every share that is no more than
the whole: where the two heights are from `-m` to `m` and `m` is `1000` or more, so is the
reading. -/
theorem cubicOf_mem (m y1 y2 : Int) (num den : Nat) (hn : num ≤ den)
    (h1 : -m ≤ y1 ∧ y1 ≤ m) (h2 : -m ≤ y2 ∧ y2 ≤ m) (hm : 1000 ≤ m) :
    -m ≤ cubicOf y1 y2 num den ∧ cubicOf y1 y2 num den ≤ m := by
  have hs : (0 : Int) ≤ (den : Int) - num := Int.sub_nonneg_of_le (Int.ofNat_le.mpr hn)
  have hk : (num : Int) + ((den : Int) - num) = den := by omega
  have hd : (0 : Int) ≤ (den : Int) ^ 3 := Int.pow_nonneg (Int.natCast_nonneg den)
  have up := cubic_le y1 y2 m num ((den : Int) - num) (Int.natCast_nonneg num) hs h1.2 h2.2 hm
  have down := le_cubic y1 y2 m num ((den : Int) - num) (Int.natCast_nonneg num) hs h1.1 h2.1 hm
  rw [hk] at up down
  rw [← Int.neg_mul] at down
  exact ⟨le_ediv_of_le _ _ _ hd (by omega) down, ediv_le_of_le _ _ _ hd (by omega) up⟩

end Easing

/-! ## Easings, value by value -/

/-- **A small easing**: a test on its data. Its stops are within `±100000`, a hundred times the
whole way, and there are `100001` of them at most; or its two heights are within `±100000`. -/
def Easing.Small : Easing → Prop
  | .stops values => values.length ≤ 100001 ∧ ∀ v ∈ values, Size v 100000
  | .cubic y1 y2 => Size y1 100000 ∧ Size y2 100000

instance (e : Easing) : Decidable e.Small := by
  cases e <;> unfold Easing.Small <;> exact inferInstance

namespace Easing

/-- **A small easing reads within `±100000`**, at every share that is no more than the whole. -/
theorem of_size (e : Easing) (num den : Nat) (h : e.Small) (hn : num ≤ den) :
    Size (e.of num den) 100000 := by
  cases e with
  | stops values =>
    have hm := stopsOf_mem (-100000) 100000 values num den (by decide)
      (fun v hv => (h.2 v hv).mem)
    exact Size.of_mem hm.1 hm.2
  | cubic y1 y2 =>
    have hm := cubicOf_mem 100000 y1 y2 num den hn h.1.mem h.2.mem (by decide)
    exact Size.of_mem hm.1 hm.2

/-- **A cubic at a share, value by value**: three differences and products for the powers, three
products for each of the two heights, one for the end, two sums and the division. -/
def cubicOf? (y1 y2 num den : Int) : Option Int :=
  hold (den - num) fun left =>
  hold (left * left) fun left2 =>
  hold (num * num) fun num2 =>
  hold (num2 * num) fun num3 =>
  hold (den * den) fun den2 =>
  hold (den2 * den) fun den3 =>
  hold (3 * y1) fun a =>
  hold (a * num) fun a =>
  hold (a * left2) fun first =>
  hold (3 * y2) fun b =>
  hold (b * num2) fun b =>
  hold (b * left) fun second =>
  hold (1000 * num3) fun third =>
  hold (first + second) fun sum =>
  hold (sum + third) fun sum =>
  some (fdiv sum den3)

/-- **A cubic fits.** With heights within `±100000` and a share of a duration of `10000` at
most, a machine of 64 bits computes the cubic as `Easing.cubicOf` says. -/
theorem cubicOf?_eq (y1 y2 : Int) (num den : Nat) (h1 : Size y1 100000) (h2 : Size y2 100000)
    (hn : num ≤ den) (hd : den ≤ 10000) :
    cubicOf? y1 y2 num den = some (cubicOf y1 y2 num den) := by
  have sn : Size (num : Int) 10000 := Size.nat (Nat.le_trans hn hd)
  have sd : Size (den : Int) 10000 := Size.nat hd
  have sl : Size ((den : Int) - num) 10000 := by
    unfold Size
    omega
  have s3 : Size (3 : Int) 3 := by decide
  have sk : Size (1000 : Int) 1000 := by decide
  have sl2 := sl.mul sl
  have sn2 := sn.mul sn
  have sn3 := sn2.mul sn
  have sd2 := sd.mul sd
  have sd3 := sd2.mul sd
  have sa := ((s3.mul h1).mul sn).mul sl2
  have sb := ((s3.mul h2).mul sn2).mul sl
  have sc := sk.mul sn3
  rw [cubicOf_fdiv]
  unfold cubicOf?
  refine hold_some (sl.fits (by decide)) ?_
  refine hold_some (sl2.fits (by decide)) ?_
  refine hold_some (sn2.fits (by decide)) ?_
  refine hold_some (sn3.fits (by decide)) ?_
  refine hold_some (sd2.fits (by decide)) ?_
  refine hold_some (sd3.fits (by decide)) ?_
  refine hold_some ((s3.mul h1).fits (by decide)) ?_
  refine hold_some (((s3.mul h1).mul sn).fits (by decide)) ?_
  refine hold_some (sa.fits (by decide)) ?_
  refine hold_some ((s3.mul h2).fits (by decide)) ?_
  refine hold_some (((s3.mul h2).mul sn2).fits (by decide)) ?_
  refine hold_some (sb.fits (by decide)) ?_
  refine hold_some (sc.fits (by decide)) ?_
  refine hold_some ((sa.add sb).fits (by decide)) ?_
  refine hold_some (((sa.add sb).add sc).fits (by decide)) ?_
  rfl

/-- **Stops at a share, value by value.** The count and the last value are read from the list. Then:
the count of pieces, the progress in pieces, its whole pieces by a division, what is left of it
by a product and a difference, the place after, the rise between the two values, and the
line. -/
def stopsOf? (values : List Int) (num den : Int) : Option Int :=
  let count : Int := values.length
  let last : Int := values.getLast?.getD 0
  hold (if count = 0 then 0 else count - 1) fun pieces =>
  hold (num * pieces) fun whole =>
  let i : Int := fdiv whole den
  hold (den * i) fun below =>
  hold (whole - below) fun rest =>
  hold (i + 1) fun after =>
  let a : Int := values.getD i.toNat last
  let b : Int := values.getD after.toNat last
  hold (b - a) fun rise =>
  hold (rise * rest) fun part =>
  hold (a + fdiv part den) some

/-- **Stops fit.** With `100001` stops at most, each within `±100000`, and a share of a
duration of `10000` at most, a machine of 64 bits computes the stops as `Easing.stopsOf`
says. -/
theorem stopsOf?_eq (values : List Int) (num den : Nat) (hl : values.length ≤ 100001)
    (hv : ∀ v ∈ values, Size v 100000) (hn : num ≤ den) (hd : den ≤ 10000) :
    stopsOf? values num den = some (stopsOf values num den) := by
  have sp : Size (if (values.length : Int) = 0 then (0 : Int) else (values.length : Int) - 1)
      100000 := by
    unfold Size
    split <;> omega
  have sn : Size (num : Int) 10000 := Size.nat (Nat.le_trans hn hd)
  have sd : Size (den : Int) 10000 := Size.nat hd
  have sw := sn.mul sp
  have si := sw.fdiv (Int.natCast_nonneg den)
  have sb := sd.mul si
  have sr := sw.sub sb
  have sx := si.add (by decide : Size (1 : Int) 1)
  have slast : Size (values.getLast?.getD 0) 100000 :=
    last_of_all (fun v => Size v 100000) values 0 (by decide) hv
  have sget : ∀ i, Size (values.getD i (values.getLast?.getD 0)) 100000 := fun i =>
    getD_of_all (fun v => Size v 100000) values i _ slast hv
  rw [stopsOf_fdiv]
  unfold stopsOf?
  refine hold_some (sp.fits (by decide)) ?_
  refine hold_some (sw.fits (by decide)) ?_
  refine hold_some (sb.fits (by decide)) ?_
  refine hold_some (sr.fits (by decide)) ?_
  refine hold_some (sx.fits (by decide)) ?_
  refine hold_some (((sget _).sub (sget _)).fits (by decide)) ?_
  refine hold_some ((((sget _).sub (sget _)).mul sr).fits (by decide)) ?_
  refine hold_some (((sget _).add ((((sget _).sub (sget _)).mul sr).fdiv
    (Int.natCast_nonneg den))).fits (by decide)) ?_
  rfl

/-- **An easing at a share, value by value.** -/
def of? : Easing → Int → Int → Option Int
  | .stops values, num, den => stopsOf? values num den
  | .cubic y1 y2, num, den => cubicOf? y1 y2 num den

/-- **An easing at a moment, value by value**: at that share of a thousand. -/
def at? (e : Easing) (p : Int) : Option Int := e.of? p 1000

/-- **A small easing fits at every share** of a duration of `10000` at most that is no more
than the whole: a machine of 64 bits computes it as `Easing.of` says. -/
theorem of?_eq (e : Easing) (num den : Nat) (h : e.Small) (hn : num ≤ den) (hd : den ≤ 10000) :
    e.of? num den = some (e.of num den) := by
  cases e with
  | stops values => exact stopsOf?_eq values num den h.1 h.2 hn hd
  | cubic y1 y2 => exact cubicOf?_eq y1 y2 num den h.1 h.2 hn hd

/-- **A small easing fits at every moment** from `0` to `1000`. -/
theorem at?_eq (e : Easing) (p : Nat) (h : e.Small) (hp : p ≤ 1000) :
    e.at? p = some (e.at p) := by
  rw [← of_thousand e p]
  exact of?_eq e p 1000 h hp (by decide)

end Easing

/-! ## Transitions, value by value -/

/-- **A small transition**: its delay is a thousand million at most, its duration `10000` at
most, and its easing is small. A transition held inside a step of a thousand is so where its
easing is. -/
def Transition.Small (tr : Transition) : Prop :=
  tr.delay ≤ 1000000000 ∧ tr.duration ≤ 10000 ∧ tr.ease.Small

instance (tr : Transition) : Decidable tr.Small := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

namespace Transition

/-- **A transition at a moment, value by value**: the moment it is over by a sum, two comparisons,
and what has passed of it by a difference. -/
def at? (tr : Transition) (t : Nat) : Option Int :=
  hold ((tr.delay : Int) + tr.duration) fun over =>
  if over ≤ (t : Int) then tr.ease.at? 1000
  else if (t : Int) ≤ tr.delay then tr.ease.at? 0
  else hold ((t : Int) - tr.delay) fun passed => tr.ease.of? passed tr.duration

/-- **A transition held inside a step is small where its easing is.** So a look is checked by
its easings alone: whatever delay a thing is given, its transition held in the step is small. -/
theorem small_within (tr : Transition) (h : tr.ease.Small) : tr.within.Small := by
  refine ⟨?_, ?_, h⟩
  · show min tr.delay 1000 ≤ 1000000000
    omega
  · show min tr.duration (1000 - min tr.delay 1000) ≤ 10000
    omega

/-- **A transition with a small easing reads within `±100000` at every moment.** -/
theorem at_size (tr : Transition) (t : Nat) (h : tr.ease.Small) : Size (tr.at t) 100000 := by
  obtain ⟨num, den, hn, he⟩ := at_share tr t
  rw [he]
  exact Easing.of_size tr.ease num den h hn

/-- **A small transition fits at every moment** up to a thousand million: a machine of 64 bits
computes it as `Transition.at` says. -/
theorem at?_eq (tr : Transition) (t : Nat) (h : tr.Small) (ht : t ≤ 1000000000) :
    tr.at? t = some (tr.at t) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsum : Fits ((tr.delay : Int) + tr.duration) := by
    unfold Fits
    omega
  have hgap : Fits ((t : Int) - tr.delay) := by
    unfold Fits
    omega
  unfold Transition.at? Transition.at
  refine hold_some hsum ?_
  show (if (tr.delay : Int) + tr.duration ≤ (t : Int) then tr.ease.at? 1000
    else if (t : Int) ≤ tr.delay then tr.ease.at? 0
    else hold ((t : Int) - tr.delay) fun passed => tr.ease.of? passed tr.duration) = _
  cases Decidable.em (tr.delay + tr.duration ≤ t) with
  | inl hover =>
    have hover' : (tr.delay : Int) + tr.duration ≤ (t : Int) := by omega
    rw [if_pos hover, if_pos hover']
    exact Easing.at?_eq tr.ease 1000 h3 (Nat.le_refl 1000)
  | inr hover =>
    have hover' : ¬((tr.delay : Int) + tr.duration ≤ (t : Int)) := by omega
    rw [if_neg hover, if_neg hover']
    cases Decidable.em (t ≤ tr.delay) with
    | inl hbefore =>
      have hbefore' : (t : Int) ≤ tr.delay := by omega
      rw [if_pos hbefore, if_pos hbefore']
      exact Easing.at?_eq tr.ease 0 h3 (Nat.zero_le 1000)
    | inr hbefore =>
      have hbefore' : ¬((t : Int) ≤ tr.delay) := by omega
      have hcast : (t : Int) - tr.delay = ((t - tr.delay : Nat) : Int) := by omega
      rw [if_neg hbefore, if_neg hbefore']
      refine hold_some hgap ?_
      show tr.ease.of? ((t : Int) - tr.delay) tr.duration = _
      rw [hcast]
      exact Easing.of?_eq tr.ease (t - tr.delay) tr.duration h3 (by omega) h2

end Transition

/-! ## Changes and tracks, value by value -/

/-- A small point: each coordinate within a thousand million. -/
def IVec.Small (p : IVec) : Prop := Size p.x 1000000000 ∧ Size p.y 1000000000

instance (p : IVec) : Decidable p.Small := inferInstanceAs (Decidable (_ ∧ _))

/-- A small segment: its four points are small. -/
def ICubic.Small (c : ICubic) : Prop := c.p0.Small ∧ c.p1.Small ∧ c.p2.Small ∧ c.p3.Small

instance (c : ICubic) : Decidable c.Small := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- **A small change**: every coordinate, size, part and opacity of its two poses is within a
thousand million. -/
def Change.Small : Change → Prop
  | .shift a b => a.Small ∧ b.Small
  | .grow a b => Size a 1000000000 ∧ Size b 1000000000
  | .reveal a b => Size a 1000000000 ∧ Size b 1000000000
  | .fade a b => Size a 1000000000 ∧ Size b 1000000000
  | .morph a b => (∀ c ∈ a, c.Small) ∧ ∀ c ∈ b, c.Small

instance (c : Change) : Decidable c.Small := by
  cases c <;> unfold Change.Small <;> exact inferInstance

/-- A point mixed, value by value: each coordinate by `mix?`. -/
def IVec.mix? (a b : IVec) (e : Int) : Option IVec :=
  (Scene.mix? a.x b.x e).bind fun x => (Scene.mix? a.y b.y e).bind fun y => some ⟨x, y⟩

/-- Two small points are mixed by a machine as `mix` says, coordinate by coordinate. -/
theorem IVec.mix?_eq (a b : IVec) (e : Int) (ha : a.Small) (hb : b.Small) (he : Size e 100000) :
    IVec.mix? a b e = some ⟨Scene.mix a.x b.x e, Scene.mix a.y b.y e⟩ := by
  unfold IVec.mix?
  rw [Scene.mix?_eq a.x b.x e ha.1 hb.1 he, Scene.mix?_eq a.y b.y e ha.2 hb.2 he]
  rfl

/-- **A segment mixed, value by value**: each of its eight coordinates by `mix?`. -/
def ICubic.mix? (a b : ICubic) (e : Int) : Option ICubic :=
  (IVec.mix? a.p0 b.p0 e).bind fun p0 =>
  (IVec.mix? a.p1 b.p1 e).bind fun p1 =>
  (IVec.mix? a.p2 b.p2 e).bind fun p2 =>
  (IVec.mix? a.p3 b.p3 e).bind fun p3 => some ⟨p0, p1, p2, p3⟩

/-- **Two small segments are mixed by a machine as `ICubic.mix` says.** -/
theorem ICubic.mix?_eq (a b : ICubic) (e : Int) (ha : a.Small) (hb : b.Small)
    (he : Size e 100000) : ICubic.mix? a b e = some (ICubic.mix a b e) := by
  unfold ICubic.mix?
  rw [IVec.mix?_eq a.p0 b.p0 e ha.1 hb.1 he, IVec.mix?_eq a.p1 b.p1 e ha.2.1 hb.2.1 he,
    IVec.mix?_eq a.p2 b.p2 e ha.2.2.1 hb.2.2.1 he, IVec.mix?_eq a.p3 b.p3 e ha.2.2.2 hb.2.2.2 he]
  rfl

/-- Two lists of segments mixed segment by segment, value by value. -/
def mixEach? : List ICubic → List ICubic → Int → Option (List ICubic)
  | x :: rest, y :: more, e =>
    (ICubic.mix? x y e).bind fun c => (mixEach? rest more e).bind fun cs => some (c :: cs)
  | _, _, _ => some []

/-- Two lists of small segments are mixed by a machine segment by segment. -/
theorem mixEach?_eq : ∀ (a b : List ICubic) (e : Int), (∀ c ∈ a, c.Small) → (∀ c ∈ b, c.Small) →
    Size e 100000 → mixEach? a b e = some (List.zipWith (fun x y => ICubic.mix x y e) a b)
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | x :: rest, y :: more, e, ha, hb, he => by
    show ((ICubic.mix? x y e).bind fun c =>
      (mixEach? rest more e).bind fun cs => some (c :: cs)) = _
    rw [ICubic.mix?_eq x y e (ha x List.mem_cons_self) (hb y List.mem_cons_self) he,
      mixEach?_eq rest more e (fun c hc => ha c (List.mem_cons_of_mem x hc))
        (fun c hc => hb c (List.mem_cons_of_mem y hc)) he]
    rfl

/-- **The pose of a change at an eased progress, value by value.** Each number of the pose is one
`mix?`. A change of shape between two lists of different lengths computes nothing: it compares
the progress with `500`. -/
def Change.at? : Change → Int → Option Pose
  | .shift a b, e => (IVec.mix? a b e).map Pose.shift
  | .grow a b, e => (Scene.mix? a b e).map Pose.grow
  | .reveal a b, e => (Scene.mix? a b e).map Pose.reveal
  | .fade a b, e => (Scene.mix? a b e).map Pose.fade
  | .morph a b, e =>
    if a.length = b.length then (mixEach? a b e).map Pose.shape
    else if e < 500 then some (.shape a)
    else some (.shape b)

/-- **A small change fits** at every eased progress within `±100000`: a machine of 64 bits
computes its pose as `Change.at` says. -/
theorem Change.at?_eq (c : Change) (e : Int) (h : c.Small) (he : Size e 100000) :
    c.at? e = some (c.at e) := by
  cases c with
  | shift a b =>
    show (IVec.mix? a b e).map Pose.shift = _
    rw [IVec.mix?_eq a b e h.1 h.2 he]
    rfl
  | grow a b =>
    show (Scene.mix? a b e).map Pose.grow = _
    rw [mix?_eq a b e h.1 h.2 he]
    rfl
  | reveal a b =>
    show (Scene.mix? a b e).map Pose.reveal = _
    rw [mix?_eq a b e h.1 h.2 he]
    rfl
  | fade a b =>
    show (Scene.mix? a b e).map Pose.fade = _
    rw [mix?_eq a b e h.1 h.2 he]
    rfl
  | morph a b =>
    show (if a.length = b.length then (mixEach? a b e).map Pose.shape
      else if e < 500 then some (Pose.shape a)
      else some (Pose.shape b)) =
      some (if a.length = b.length then
          Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
        else if e < 500 then Pose.shape a
        else Pose.shape b)
    cases Decidable.em (a.length = b.length) with
    | inl hl =>
      rw [if_pos hl, if_pos hl, mixEach?_eq a b e h.1 h.2 he]
      rfl
    | inr hl =>
      rw [if_neg hl, if_neg hl]
      cases Decidable.em (e < 500) with
      | inl h5 => rw [if_pos h5, if_pos h5]
      | inr h5 => rw [if_neg h5, if_neg h5]

/-- **A small track**: its change is small and its transition is small. -/
def Track.Small {κ : Type} (tr : Track κ) : Prop := tr.change.Small ∧ tr.timing.Small

instance {κ : Type} (tr : Track κ) : Decidable tr.Small := inferInstanceAs (Decidable (_ ∧ _))

/-- **The pose of a track at a moment, value by value**: the transition's, then the change's. -/
def Track.at? {κ : Type} (tr : Track κ) (t : Nat) : Option Pose :=
  (tr.timing.at? t).bind tr.change.at?

/-- **A small track fits at every moment** up to a thousand million: a machine of 64 bits
computes its pose as `Track.at` says, and no sum, difference or product on the way is `2 ^ 63`
or more in size. -/
theorem Track.at?_eq {κ : Type} (tr : Track κ) (t : Nat) (h : tr.Small) (ht : t ≤ 1000000000) :
    tr.at? t = some (tr.at t) := by
  unfold Track.at?
  rw [Transition.at?_eq tr.timing t h.2 ht]
  exact Change.at?_eq tr.change (tr.timing.at t) h.1 (Transition.at_size tr.timing t h.2.2.2)

/-- **A small motion**: every track of it is small. A consumer checks its look once, with
`decide`. -/
def Motion.Small {κ : Type} (m : Motion κ) : Prop := ∀ tr ∈ m, tr.Small

instance {κ : Type} (m : Motion κ) : Decidable m.Small :=
  inferInstanceAs (Decidable (∀ tr ∈ m, tr.Small))

/-- **A motion held inside its step is small where its easings and its changes are.** The
delays and the durations need no check: the step holds them. -/
theorem Motion.small_within {κ : Type} (m : Motion κ) (hc : ∀ tr ∈ m, tr.change.Small)
    (he : ∀ tr ∈ m, tr.timing.ease.Small) : m.within.Small := by
  intro tr htr
  obtain ⟨tr0, h0, rfl⟩ := List.mem_map.mp htr
  exact ⟨hc tr0 h0, Transition.small_within tr0.timing (he tr0 h0)⟩

/-- **Every track of a small motion fits at every moment.** -/
theorem Motion.at?_eq {κ : Type} (m : Motion κ) (h : m.Small) {tr : Track κ} (htr : tr ∈ m)
    (t : Nat) (ht : t ≤ 1000000000) : tr.at? t = some (tr.at t) :=
  Track.at?_eq tr t (h tr htr) ht

/-! ## What a machine reads is the reading

The laws above ask that the data is small. These ask nothing: wherever the machine has a
reading, on data of any size, it is the reading of `Whatwg/Svg/Scene/Motion.lean`. So it can
be run on data that fails `Small`, to see whether it fits all the same. -/

/-- What comes after a reading that is known reads that reading. -/
private theorem bind_sound {α β : Type} {x : Option α} {f : α → Option β} {a : α} {r : β}
    (hx : ∀ y, x = some y → y = a) (h : x.bind f = some r) : f a = some r := by
  cases x with
  | none => exact nomatch h
  | some y =>
    rw [← hx y rfl]
    exact h

/-- A reading that is known, under a function, is the function of it. -/
private theorem map_sound {α β : Type} {x : Option α} {f : α → β} {a : α} {r : β}
    (hx : ∀ y, x = some y → y = a) (h : x.map f = some r) : r = f a := by
  cases x with
  | none => exact nomatch h
  | some y =>
    rw [← hx y rfl]
    exact (Option.some.inj h).symm

/-- **Where a machine has a reading of `mix`, it is `mix`.** -/
theorem mix?_sound {u v e r : Int} (h : mix? u v e = some r) : r = mix u v e := by
  unfold mix? at h
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  exact (Option.some.inj h).symm.trans (mix_fdiv u v e).symm

namespace Easing

/-- Where a machine has a reading of a cubic, it is `Easing.cubicOf`. -/
theorem cubicOf?_sound {y1 y2 : Int} {num den : Nat} {r : Int}
    (h : cubicOf? y1 y2 num den = some r) : r = cubicOf y1 y2 num den := by
  unfold cubicOf? at h
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  exact (Option.some.inj h).symm.trans (cubicOf_fdiv y1 y2 num den).symm

/-- Where a machine has a reading of stops, it is `Easing.stopsOf`. -/
theorem stopsOf?_sound {values : List Int} {num den : Nat} {r : Int}
    (h : stopsOf? values num den = some r) : r = stopsOf values num den := by
  unfold stopsOf? at h
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  have h := (fits_of_hold h).2
  exact (Option.some.inj h).symm.trans (stopsOf_fdiv values num den).symm

/-- **Where a machine has a reading of an easing at a share, it is `Easing.of`.** -/
theorem of?_sound {e : Easing} {num den : Nat} {r : Int} (h : e.of? num den = some r) :
    r = e.of num den := by
  cases e with
  | stops values => exact stopsOf?_sound h
  | cubic y1 y2 => exact cubicOf?_sound h

/-- Where a machine has a reading of an easing at a moment, it is `Easing.at`. -/
theorem at?_sound {e : Easing} {p : Nat} {r : Int} (h : e.at? p = some r) : r = e.at p := by
  rw [← of_thousand e p]
  exact of?_sound (den := 1000) h

end Easing

/-- **Where a machine has a reading of a transition, it is `Transition.at`.** -/
theorem Transition.at?_sound {tr : Transition} {t : Nat} {r : Int} (h : tr.at? t = some r) :
    r = tr.at t := by
  unfold Transition.at? at h
  have h := (fits_of_hold h).2
  have h : (if (tr.delay : Int) + tr.duration ≤ (t : Int) then tr.ease.at? 1000
      else if (t : Int) ≤ tr.delay then tr.ease.at? 0
      else hold ((t : Int) - tr.delay) fun passed => tr.ease.of? passed tr.duration) = some r := h
  unfold Transition.at
  cases Decidable.em (tr.delay + tr.duration ≤ t) with
  | inl hover =>
    have hover' : (tr.delay : Int) + tr.duration ≤ (t : Int) := by omega
    rw [if_pos hover'] at h
    rw [if_pos hover]
    exact Easing.at?_sound (p := 1000) h
  | inr hover =>
    have hover' : ¬((tr.delay : Int) + tr.duration ≤ (t : Int)) := by omega
    rw [if_neg hover'] at h
    rw [if_neg hover]
    cases Decidable.em (t ≤ tr.delay) with
    | inl hbefore =>
      have hbefore' : (t : Int) ≤ tr.delay := by omega
      rw [if_pos hbefore'] at h
      rw [if_pos hbefore]
      exact Easing.at?_sound (p := 0) h
    | inr hbefore =>
      have hbefore' : ¬((t : Int) ≤ tr.delay) := by omega
      have hcast : (t : Int) - tr.delay = ((t - tr.delay : Nat) : Int) := by omega
      rw [if_neg hbefore'] at h
      rw [if_neg hbefore]
      have h := (fits_of_hold h).2
      have h : tr.ease.of? ((t : Int) - tr.delay) tr.duration = some r := h
      rw [hcast] at h
      exact Easing.of?_sound h

/-- Where a machine has a reading of a point mixed, it is the point mixed. -/
theorem IVec.mix?_sound {a b : IVec} {e : Int} {r : IVec} (h : IVec.mix? a b e = some r) :
    r = ⟨Scene.mix a.x b.x e, Scene.mix a.y b.y e⟩ := by
  unfold IVec.mix? at h
  have h := bind_sound (fun _ hy => Scene.mix?_sound hy) h
  have h := bind_sound (fun _ hy => Scene.mix?_sound hy) h
  exact (Option.some.inj h).symm

/-- Where a machine has a reading of a segment mixed, it is `ICubic.mix`. -/
theorem ICubic.mix?_sound {a b : ICubic} {e : Int} {r : ICubic} (h : ICubic.mix? a b e = some r) :
    r = ICubic.mix a b e := by
  unfold ICubic.mix? at h
  have h := bind_sound (fun _ hy => IVec.mix?_sound hy) h
  have h := bind_sound (fun _ hy => IVec.mix?_sound hy) h
  have h := bind_sound (fun _ hy => IVec.mix?_sound hy) h
  have h := bind_sound (fun _ hy => IVec.mix?_sound hy) h
  exact (Option.some.inj h).symm

/-- Where a machine has a reading of two lists of segments mixed, it is the two lists mixed
segment by segment. -/
theorem mixEach?_sound : ∀ (a b : List ICubic) (e : Int) {r : List ICubic},
    mixEach? a b e = some r → r = List.zipWith (fun x y => ICubic.mix x y e) a b
  | [], _, _, _, h => (Option.some.inj h).symm
  | _ :: _, [], _, _, h => (Option.some.inj h).symm
  | x :: rest, y :: more, e, r, h => by
    have h : ((ICubic.mix? x y e).bind fun c =>
        (mixEach? rest more e).bind fun cs => some (c :: cs)) = some r := h
    have h := bind_sound (fun _ hc => ICubic.mix?_sound hc) h
    have h := bind_sound (fun _ hcs => mixEach?_sound rest more e hcs) h
    exact (Option.some.inj h).symm

/-- **Where a machine has a pose of a change, it is the pose of `Change.at`.** -/
theorem Change.at?_sound {c : Change} {e : Int} {r : Pose} (h : c.at? e = some r) :
    r = c.at e := by
  cases c with
  | shift a b => exact map_sound (f := Pose.shift) (fun _ hy => IVec.mix?_sound hy) h
  | grow a b => exact map_sound (f := Pose.grow) (fun _ hy => mix?_sound hy) h
  | reveal a b => exact map_sound (f := Pose.reveal) (fun _ hy => mix?_sound hy) h
  | fade a b => exact map_sound (f := Pose.fade) (fun _ hy => mix?_sound hy) h
  | morph a b =>
    have h : (if a.length = b.length then (mixEach? a b e).map Pose.shape
        else if e < 500 then some (Pose.shape a)
        else some (Pose.shape b)) = some r := h
    show r = (if a.length = b.length then
        Pose.shape (List.zipWith (fun x y => ICubic.mix x y e) a b)
      else if e < 500 then Pose.shape a
      else Pose.shape b)
    cases Decidable.em (a.length = b.length) with
    | inl hl =>
      rw [if_pos hl] at h
      rw [if_pos hl]
      exact map_sound (f := Pose.shape) (fun _ hy => mixEach?_sound a b e hy) h
    | inr hl =>
      rw [if_neg hl] at h
      rw [if_neg hl]
      cases Decidable.em (e < 500) with
      | inl h5 =>
        rw [if_pos h5] at h
        rw [if_pos h5]
        exact (Option.some.inj h).symm
      | inr h5 =>
        rw [if_neg h5] at h
        rw [if_neg h5]
        exact (Option.some.inj h).symm

/-- **Where a machine has a pose of a track, it is the pose of `Track.at`**, on data of any
size: a machine of 64 bits that overflows nowhere computes what the kit reads. -/
theorem Track.at?_sound {κ : Type} {tr : Track κ} {t : Nat} {r : Pose} (h : tr.at? t = some r) :
    r = tr.at t := by
  unfold Track.at? at h
  exact Change.at?_sound (bind_sound (fun _ hy => Transition.at?_sound hy) h)

/-! ## The tables are what the machine computes -/

/-- **The entry at `p` of a small easing's table is what a machine of 64 bits computes.** -/
theorem Easing.table_machine (e : Easing) (h : e.Small) (p : Nat) (hp : p ≤ 1000) :
    e.table[p]? = e.at? p := by
  rw [Easing.table_getElem? e p hp, Easing.at?_eq e p h hp]

/-- The entry at `num` of the shares of a duration of `10000` at most, of a small easing, is
what a machine of 64 bits computes. -/
theorem Easing.shares_machine (e : Easing) (h : e.Small) (den num : Nat) (hn : num ≤ den)
    (hd : den ≤ 10000) : (e.shares den)[num]? = e.of? num den := by
  rw [Easing.shares_getElem? e den num hn, Easing.of?_eq e num den h hn hd]

/-- **The entry at `t` of a small transition's table is what a machine of 64 bits computes.** -/
theorem Transition.table_machine (tr : Transition) (h : tr.Small) (t : Nat) (ht : t ≤ 1000) :
    tr.table[t]? = tr.at? t := by
  rw [Transition.table_getElem? tr t ht, Transition.at?_eq tr t h (by omega)]

/-- **The entry at `t` of a small track's table is the numbers of the pose that a machine of
64 bits computes.** -/
theorem Track.table_machine {κ : Type} (tr : Track κ) (h : tr.Small) (t : Nat) (ht : t ≤ 1000) :
    tr.table[t]? = (tr.at? t).map Pose.numbers := by
  rw [Track.table_getElem? tr t ht, Track.at?_eq tr t h (by omega)]
  rfl

end Whatwg.Svg.Scene