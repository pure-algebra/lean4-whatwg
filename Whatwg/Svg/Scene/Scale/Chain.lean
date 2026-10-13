import Whatwg.Svg.Scene.Scale.Invert

/-!
# Whatwg.Svg.Scene.Scale.Chain

Owner: one scale after another (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A picture often draws a quantity in two steps. The first changes the quantity: a share
becomes a level, a count its logarithm, a value its place on a line of a thousand parts. The
second places the result: on the width of a page, or down a screen whose ordinates grow
downward. Each step is a `Scale`. This module says what the two together keep.

- `Scale.andThen s t v`: the length that `t` gives the length that `s` gives `v`.
- `Scale.chain c v`: the same for a list of scales, read from the first.
- `Scale.Meets s t`: the stages meet, which is that the domain of `t` is what `s` draws the
  ends of its own domain at. It is decided.

What the laws say:

- **Chains are put end to end** (`chain_append`): the chain of two lists in a row is the second
  chain after the first. With `chain_nil` this is the law of a monoid that acts on values, so a
  caller may build a chain in pieces.
- **The direction of two stages is the product of their directions** (`andThen_mono`,
  `andThen_anti_left`, `andThen_anti_right`, `andThen_mono_of_falling`): two rising stages rise,
  one falling stage makes the pair fall, and two falling stages rise. A chain of rising stages
  rises (`chain_mono`).
- **The ends are kept** (`andThen_lo`, `andThen_hi`, `andThen_linear`): where the stages meet,
  the ends of the first domain are drawn where the second stage draws the ends of its own.
- **What the first stage draws alike, the pair draws alike** (`andThen_tie`): a later stage
  cannot tell apart what an earlier one has drawn at one length. A control below shows the
  cost of a coarse stage in the middle.
- **The inverse of two stages is the two inverses, the second first** (`andThen_galois`): for
  rising stages that meet, `andThen s t v ≤ y ↔ v ≤ s.invert (t.invert y)`. So the value under
  a mark of the pair is found by going back through each stage, and it is exact: it is the
  greatest value of the first domain that the pair draws at the mark or before it
  (`andThen_invert_le`).
- `log2_as_chain`: a `log2` scale is the logarithm and then a straight line. It is the chain
  that the package already had.

What this module does not claim: one scale that draws as two stages do. Two straight lines
after each other round twice, and are not the straight line from the first domain to the
second range. Nor the inverse of a chain of more than two stages as one law, which follows by
taking `andThen_galois` once for each stage; nor the inverse of a pair with a falling stage.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Scale

/-- **One scale after another**: the length that `t` gives the length that `s` gives `v`. -/
def andThen (s t : Scale) (v : Int) : Int := t.at (s.at v)

/-- **A chain of scales**, read from the first: each draws what the one before it drew. -/
def chain (c : List Scale) (v : Int) : Int := c.foldl (fun x s => s.at x) v

/-- **The stages meet**: the domain of `t` is what `s` draws the ends of its own domain at. -/
def Meets (s t : Scale) : Prop :=
  t.domain.1 = s.at s.domain.1 ∧ t.domain.2 = s.at s.domain.2

/-- Whether two stages meet is decided. -/
instance (s t : Scale) : Decidable (Meets s t) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Chains -/

theorem chain_nil (v : Int) : chain [] v = v := rfl

theorem chain_cons (s : Scale) (c : List Scale) (v : Int) : chain (s :: c) v = chain c (s.at v) :=
  rfl

/-- A chain of two is one scale after another. -/
theorem chain_pair (s t : Scale) (v : Int) : chain [s, t] v = andThen s t v := rfl

/-- **Chains are put end to end.** -/
theorem chain_append : ∀ (c d : List Scale) (v : Int), chain (c ++ d) v = chain d (chain c v)
  | [], _, _ => rfl
  | s :: c, d, v => chain_append c d (s.at v)

/-- **A chain of rising stages rises**: more is never drawn as less. -/
theorem chain_mono : ∀ c : List Scale, (∀ s ∈ c, s.Rising) → ∀ {a b : Int}, a ≤ b →
    chain c a ≤ chain c b
  | [], _, _, _, h => h
  | s :: c, hr, _, _, h =>
    chain_mono c (fun t ht => hr t (List.mem_cons_of_mem s ht))
      (at_mono s (hr s List.mem_cons_self) h)

/-! ## The direction of two stages -/

/-- Two rising stages rise. -/
theorem andThen_mono {s t : Scale} (hs : s.Rising) (ht : t.Rising) {a b : Int} (h : a ≤ b) :
    andThen s t a ≤ andThen s t b :=
  at_mono t ht (at_mono s hs h)

/-- A falling stage and then a rising one fall. -/
theorem andThen_anti_left {s t : Scale} (hs : s.Falling) (ht : t.Rising) {a b : Int} (h : a ≤ b) :
    andThen s t b ≤ andThen s t a :=
  at_mono t ht (at_anti s hs h)

/-- A rising stage and then a falling one fall. A value in thousandths placed down a screen is
such a pair. -/
theorem andThen_anti_right {s t : Scale} (hs : s.Rising) (ht : t.Falling) {a b : Int} (h : a ≤ b) :
    andThen s t b ≤ andThen s t a :=
  at_anti t ht (at_mono s hs h)

/-- Two falling stages rise. -/
theorem andThen_mono_of_falling {s t : Scale} (hs : s.Falling) (ht : t.Falling) {a b : Int}
    (h : a ≤ b) : andThen s t a ≤ andThen s t b :=
  at_anti t ht (at_anti s hs h)

/-- **What the first stage draws alike, the pair draws alike.** So every pair of
`Scale.ties s values` is drawn alike by `andThen s t`, whatever `t` is. -/
theorem andThen_tie (s t : Scale) {a b : Int} (h : s.at a = s.at b) :
    andThen s t a = andThen s t b :=
  congrArg t.at h

/-! ## The ends -/

/-- Where the stages meet, the low end of the first domain is drawn where the second stage
draws the low end of its own. -/
theorem andThen_lo {s t : Scale} (h : Meets s t) : andThen s t s.domain.1 = t.at t.domain.1 := by
  unfold andThen
  rw [h.1]

/-- Where the stages meet, the high end of the first domain is drawn where the second stage
draws the high end of its own. -/
theorem andThen_hi {s t : Scale} (h : Meets s t) : andThen s t s.domain.2 = t.at t.domain.2 := by
  unfold andThen
  rw [h.2]

/-- A straight line onto a range, and a straight line from that range, meet. -/
theorem meets_linear (dataLo dataHi lo hi lo' hi' : Int) (h : dataLo < dataHi) :
    Meets (Scale.linear dataLo dataHi lo hi) (Scale.linear lo hi lo' hi') :=
  ⟨(linear_lo dataLo dataHi lo hi (Int.le_of_lt h)).symm, (linear_hi dataLo dataHi lo hi h).symm⟩

/-- **Two straight lines after each other keep the ends**: the low end of the data is drawn at
the low end of the last range, and the high end at the high end. -/
theorem andThen_linear (dataLo dataHi lo hi lo' hi' : Int) (h : dataLo < dataHi) (h' : lo < hi) :
    andThen (Scale.linear dataLo dataHi lo hi) (Scale.linear lo hi lo' hi') dataLo = lo' ∧
      andThen (Scale.linear dataLo dataHi lo hi) (Scale.linear lo hi lo' hi') dataHi = hi' := by
  unfold andThen
  rw [linear_lo dataLo dataHi lo hi (Int.le_of_lt h), linear_hi dataLo dataHi lo hi h]
  exact ⟨linear_lo lo hi lo' hi' (Int.le_of_lt h'), linear_hi lo hi lo' hi' h'⟩

/-- **A `log2` scale is the logarithm and then a straight line.** -/
theorem log2_as_chain (dataLo dataHi : Nat) (lo hi v : Int) :
    (Scale.log2 dataLo dataHi lo hi).at v =
      (Scale.linear (Nat.log2 dataLo : Nat) (Nat.log2 dataHi : Nat) lo hi).at
        ((Nat.log2 v.toNat : Nat) : Int) := rfl

/-! ## The value under a mark of two stages -/

/-- **The inverse of two stages is the two inverses, the second first.** For rising stages that
meet, a value of the first domain is drawn at `y` or before it exactly when it is no more than
the value that the first stage has under the value that the second has under `y`. -/
theorem andThen_galois {s t : Scale} (hs : s.Rising) (ht : t.Rising) (hf : Meets s t) {y : Int}
    (hy : t.at t.domain.1 ≤ y) {v : Int} (h1 : s.domain.1 ≤ v) (h2 : v ≤ s.domain.2) :
    andThen s t v ≤ y ↔ v ≤ s.invert (t.invert y) := by
  have a1 : t.domain.1 ≤ s.at v := by
    rw [hf.1]
    exact at_mono s hs h1
  have a2 : s.at v ≤ t.domain.2 := by
    rw [hf.2]
    exact at_mono s hs h2
  have b1 : s.at s.domain.1 ≤ t.invert y := by
    rw [← hf.1]
    exact (invert_mem t (Int.le_trans a1 a2) y).1
  exact (invert_galois t ht hy a1 a2).trans (invert_galois s hs b1 h1 h2)

/-- **Back through both stages and forward again is no later than the mark.** With
`andThen_galois`, the value found is the greatest of the first domain that the pair draws at
the mark or before it. -/
theorem andThen_invert_le {s t : Scale} (hs : s.Rising) (ht : t.Rising) (hf : Meets s t)
    (hd : s.domain.1 ≤ s.domain.2) {y : Int} (hy : t.at t.domain.1 ≤ y) :
    andThen s t (s.invert (t.invert y)) ≤ y :=
  (andThen_galois hs ht hf hy (invert_mem s hd _).1 (invert_mem s hd _).2).mpr (Int.le_refl _)

end Scale

/-! ## Finite evaluations -/

-- A value in thousandths, placed down a screen from the ordinate `300` to the ordinate `20`:
-- a rising stage and then a falling one. The ends are kept, and the middle is the middle.
#guard [0, 500, 1000].map (Scale.andThen (.linear 0 1000 0 100) (.linear 0 100 300 20)) ==
  [300, 160, 20]
#guard decide (Scale.Meets (.linear 0 1000 0 100) (.linear 0 100 300 20))

-- The value under a mark of two rising stages: a share in millionths as a width from `1` to
-- `8`, and the width as a tone from `200` to `900`. Back through both stages, the tone `500`
-- answers the greatest share that is drawn no darker.
#guard Scale.andThen (.linear 125000 1000000 1 8) (.linear 1 8 200 900) 625000 == 600
#guard (Scale.linear 125000 1000000 1 8).invert ((Scale.linear 1 8 200 900).invert 500) == 624999
#guard Scale.andThen (.linear 125000 1000000 1 8) (.linear 1 8 200 900) 624999 == 500

-- A chain in pieces is the chain at once.
#guard Scale.chain ([.linear 0 1000 0 100] ++ [.linear 0 100 300 20, .steps 0 [(100, 1), (200, 2)]])
    500 == Scale.chain [.linear 0 100 300 20, .steps 0 [(100, 1), (200, 2)]]
      (Scale.chain [.linear 0 1000 0 100] 500)

-- A control: a coarse stage in the middle. Ten values on three units, and then on a hundred:
-- the pair draws `5` at `33`, where the straight line from the data to the hundred draws it at
-- `50`. The first stage draws `4`, `5` and `6` alike, so the pair must.
#guard Scale.andThen (.linear 0 10 0 3) (.linear 0 3 0 100) 5 == 33 &&
  (Scale.linear 0 10 0 100).at 5 == 50
#guard [4, 5, 6].map (Scale.andThen (.linear 0 10 0 3) (.linear 0 3 0 100)) == [33, 33, 33]

-- A control of `Scale.Meets`: a second stage whose domain is not the first range.
#guard !decide (Scale.Meets (.linear 0 1000 0 100) (.linear 0 50 300 20))

end Whatwg.Svg.Scene
