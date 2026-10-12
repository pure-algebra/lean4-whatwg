/-!
# Whatwg.Svg.Scene.Branch

Owner: the width of each branch of a fork (slice S13 of `docs/SVG-PACKAGE-PLAN.md`; ruling
SV-73).

A line in a picture of a program carries a share of the work, and its width says how much. Where
a line forks, the branches together carry what the line carries. The rule of width here is the
one of Leonardo and of Murray: the `k`-th powers of the widths add. A share is two whole numbers,
and a share of a share multiplies both, so no share is ever rounded. A width is rounded once,
down, by a root in whole numbers. So the layer needs no fraction and stays under the strict
ceiling.

- `rootDown k n`: the greatest `r` with `r ^ k ≤ n`, for `k > 0`.
- `Share`: `num` parts of `den`. `Share.whole` is the share of the trunk.
- `Share.split s weights`: the shares of the branches of a line with the share `s`, the branches
  carrying `weights`.
- `Share.width k trunk s`: the width of a line with the share `s`, where the trunk is `trunk`
  wide.
- `Branch.wobbleRoom narrow wide`: how far two widths may wobble and still be told apart at
  every point, in per mille of a width.

What the laws say of a picture drawn with these widths:

- `rootDown_pow_le`, `lt_rootDown_succ_pow`: the root is exact to one unit, and it is the
  greatest such number (`le_rootDown`). The root of a `k`-th power is exact (`rootDown_pow`), so
  the trunk is drawn at the trunk's width (`Share.width_whole`).
- `Share.width_conserves`: at a fork, the `k`-th powers of the branches' widths sum to the
  line's quantity at most, and to more than it once each width is one unit wider. The quantity
  is `trunk ^ k * s.num / s.den`, rounded down. So the branches together carry what the line
  carries, to the rounding of one unit of width on each branch.
- `Share.split_exact`: a branch of a branch has the products of the weights over the products of
  their sums, whatever weights each fork has. So a width is rounded once, at any depth, and does
  not depend on how deep its line is nested. `Share.split_split` is the same for a whole fork.
- `Share.width_mono`: a greater share is never drawn narrower, so a wider line never carries
  less (`Share.lt_of_width_lt`). `Share.width_mono_cross` is the same for two shares of
  different denominators. A branch is never wider than its line (`Share.width_split_le`).
- `Branch.wobbleRoom_apart`: two lines whose wobble is within the room cannot be taken for each
  other at any point. `Branch.wobbleRoom_greatest`: no greater wobble has that.

Three things are the owner's to rule, and each is a parameter:

- the exponent `k`. With `k = 1` widths add, as in a flow diagram. With `k = 2` areas add
  (Leonardo's rule), and the branches of a fork of two are 41 per cent wider together than
  their line: a legend must say that areas add. With `k = 3` volumes add (Murray's law);
- the weights. Equal weights give each branch an equal share. A branch of ten nodes and a
  branch of one may have ten parts and one;
- the least width. This module draws a small share as narrow as its root, down to `0`. A caller
  that draws no line finer than some width takes the greater of the two, and below that width
  different shares are drawn alike.

What this module does not claim: that the powers of the branches' widths sum to the line's
exactly, since a root is rounded; that two different shares have different widths; a root for
`k = 0`, where `rootDown` is `0`; a width for a share whose denominator is `0`, which is drawn
`0` wide.
-/

namespace Whatwg.Svg.Scene

/-! ## The root, rounded down -/

/-- One step of the root: twice `r`, and one more where the `k`-th power of that is `n` at
most. -/
def rootDown.step (k n r : Nat) : Nat := if (2 * r + 1) ^ k ≤ n then 2 * r + 1 else 2 * r

/-- The root on a fuel: the root of `n / 2 ^ k`, doubled, and one more where that fits. A step
takes `k` binary digits off `n`, so there are as many steps as the root has binary digits. -/
def rootDown.go (k : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else rootDown.step k n (rootDown.go k fuel (n / 2 ^ k))

/-- **The greatest `r` with `r ^ k ≤ n`**, for `k > 0`: the `k`-th root of `n`, rounded down.
With `k = 0` no number is the greatest, and the value is `0`. -/
def rootDown (k n : Nat) : Nat := if k = 0 then 0 else rootDown.go k n n

/-- A step keeps the two bounds: where `r` is the root of `n / 2 ^ k`, the step is the root of
`n`. -/
theorem rootDown.step_spec (k n r : Nat) (h1 : r ^ k ≤ n / 2 ^ k) (h2 : n / 2 ^ k < (r + 1) ^ k) :
    rootDown.step k n r ^ k ≤ n ∧ n < (rootDown.step k n r + 1) ^ k := by
  have lo : (2 * r) ^ k ≤ n := by
    rw [Nat.mul_pow]
    exact Nat.le_trans (Nat.mul_le_mul_left _ h1) (Nat.mul_div_le n (2 ^ k))
  have hi : n < (2 * r + 1 + 1) ^ k := by
    have e : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
    rw [e, Nat.mul_pow]
    exact Nat.lt_of_lt_of_le (Nat.lt_mul_div_succ n (Nat.pow_pos (by decide)))
      (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h2))
  unfold rootDown.step
  cases Nat.decLe ((2 * r + 1) ^ k) n with
  | isTrue h =>
    rw [if_pos h]
    exact ⟨h, hi⟩
  | isFalse h =>
    rw [if_neg h]
    exact ⟨lo, Nat.lt_of_not_le h⟩

/-- With fuel enough, the root on a fuel has the two bounds. -/
theorem rootDown.go_spec (k : Nat) (hk : 0 < k) : ∀ (fuel n : Nat), n ≤ fuel →
    rootDown.go k fuel n ^ k ≤ n ∧ n < (rootDown.go k fuel n + 1) ^ k
  | 0, n, h => by
    rw [rootDown.go, Nat.zero_pow hk, Nat.zero_add, Nat.one_pow]
    exact ⟨Nat.zero_le n, Nat.lt_of_le_of_lt h Nat.one_pos⟩
  | fuel + 1, n, h => by
    rw [rootDown.go]
    cases Nat.decEq n 0 with
    | isTrue hn =>
      rw [if_pos hn, Nat.zero_pow hk, Nat.zero_add, Nat.one_pow]
      exact ⟨Nat.zero_le n, Nat.lt_of_le_of_lt (Nat.le_of_eq hn) Nat.one_pos⟩
    | isFalse hn =>
      rw [if_neg hn]
      have hlt : n / 2 ^ k < n :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_two_pow (Nat.ne_of_gt hk))
      have ih := rootDown.go_spec k hk fuel (n / 2 ^ k)
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt h))
      exact rootDown.step_spec k n _ ih.1 ih.2

/-- **The `k`-th power of the root is `n` at most.** -/
theorem rootDown_pow_le (k n : Nat) (hk : 0 < k) : rootDown k n ^ k ≤ n := by
  rw [rootDown, if_neg (Nat.ne_of_gt hk)]
  exact (rootDown.go_spec k hk n n (Nat.le_refl n)).1

/-- **The `k`-th power of the next number is more than `n`.** -/
theorem lt_rootDown_succ_pow (k n : Nat) (hk : 0 < k) : n < (rootDown k n + 1) ^ k := by
  rw [rootDown, if_neg (Nat.ne_of_gt hk)]
  exact (rootDown.go_spec k hk n n (Nat.le_refl n)).2

/-- The root is the greatest: a number whose `k`-th power is `n` at most is the root at most. -/
theorem le_rootDown (k n r : Nat) (hk : 0 < k) (h : r ^ k ≤ n) : r ≤ rootDown k n := by
  cases Nat.lt_or_ge (rootDown k n) r with
  | inl hlt =>
    exact absurd (Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.pow_le_pow_left (Nat.succ_le_of_lt hlt) k) h)
      (lt_rootDown_succ_pow k n hk)) (Nat.lt_irrefl _)
  | inr hge => exact hge

/-- With the exponent `0` the root is `0`. -/
theorem rootDown_exp_zero (n : Nat) : rootDown 0 n = 0 := rfl

/-- A greater number has no smaller root. -/
theorem rootDown_mono (k : Nat) {n m : Nat} (h : n ≤ m) : rootDown k n ≤ rootDown k m := by
  cases Nat.eq_zero_or_pos k with
  | inl hk =>
    rw [hk, rootDown_exp_zero, rootDown_exp_zero]
    exact Nat.zero_le 0
  | inr hk => exact le_rootDown k m _ hk (Nat.le_trans (rootDown_pow_le k n hk) h)

/-- The root of a `k`-th power is exact. -/
theorem rootDown_pow (k r : Nat) (hk : 0 < k) : rootDown k (r ^ k) = r := by
  refine Nat.le_antisymm ?_ (le_rootDown k (r ^ k) r hk (Nat.le_refl _))
  cases Nat.lt_or_ge r (rootDown k (r ^ k)) with
  | inl h =>
    exact absurd (rootDown_pow_le k (r ^ k) hk)
      (Nat.not_le_of_lt (Nat.pow_lt_pow_left h (Nat.ne_of_gt hk)))
  | inr h => exact h

/-! ## Sums and floors -/

namespace Branch

/-- A sum is no more than another, where each of its terms is no more. -/
theorem sum_map_le {α : Type} (f g : α → Nat) : ∀ l : List α, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (sum_map_le f g l fun b hb => h b (List.mem_cons_of_mem a hb))

/-- The sum of the multiples is the multiple of the sum. -/
theorem sum_map_mul_left (c : Nat) : ∀ l : List Nat, (l.map fun x => c * x).sum = c * l.sum
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.sum_cons, sum_map_mul_left c l, Nat.mul_add]

/-- The products of each member of one list with each member of another sum to the product of
the two sums. -/
theorem sum_products (vs : List Nat) : ∀ ws : List Nat,
    (ws.flatMap fun w => vs.map fun v => w * v).sum = ws.sum * vs.sum
  | [] => (Nat.zero_mul _).symm
  | w :: ws => by
    rw [List.flatMap_cons, List.sum_append, sum_map_mul_left, sum_products vs ws, List.sum_cons,
      Nat.add_mul]

/-- A member of a list is its sum at most. -/
theorem le_sum_of_mem (w : Nat) : ∀ l : List Nat, w ∈ l → w ≤ l.sum
  | [], h => nomatch h
  | x :: l, h => by
    rw [List.sum_cons]
    cases List.mem_cons.mp h with
    | inl e =>
      rw [e]
      exact Nat.le_add_right x _
    | inr hl => exact Nat.le_trans (le_sum_of_mem w l hl) (Nat.le_add_left _ x)

/-- A list of numbers whose sum is more than `0` has a member. -/
theorem length_pos_of_sum_pos : ∀ l : List Nat, 0 < l.sum → 0 < l.length
  | [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _ => Nat.succ_pos _

/-- Two floors are no more than the floor of the sum: a rounding down never adds. -/
theorem div_add_div_le (x y d : Nat) : x / d + y / d ≤ (x + y) / d := by
  cases Nat.eq_zero_or_pos d with
  | inl h =>
    rw [h, Nat.div_zero, Nat.div_zero]
    exact Nat.zero_le _
  | inr h =>
    rw [Nat.le_div_iff_mul_le h, Nat.add_mul]
    exact Nat.add_le_add (Nat.div_mul_le_self x d) (Nat.div_mul_le_self y d)

/-- The floor of a sum is no more than the two floors and one. -/
theorem add_div_le (x y d : Nat) : (x + y) / d ≤ x / d + y / d + 1 := by
  cases Nat.eq_zero_or_pos d with
  | inl h =>
    rw [h, Nat.div_zero (x + y)]
    exact Nat.zero_le _
  | inr h =>
    refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul h).mpr ?_)
    have hx : x < d * (x / d + 1) := Nat.lt_mul_div_succ x h
    have hy : y < d * (y / d + 1) := Nat.lt_mul_div_succ y h
    have e : (x / d + y / d + 1 + 1) * d = d * (x / d + 1) + d * (y / d + 1) := by
      rw [Nat.mul_comm, ← Nat.mul_add]
      exact congrArg (d * ·) (by omega)
    rw [e]
    exact Nat.add_lt_add hx hy

/-- The floors of the terms sum to the floor of the sum at most. -/
theorem sum_map_div_le {α : Type} (f : α → Nat) (d : Nat) : ∀ l : List α,
    (l.map fun a => f a / d).sum ≤ (l.map f).sum / d
  | [] => Nat.zero_le _
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left (sum_map_div_le f d l) _) (div_add_div_le _ _ d)

/-- The floor of a sum of one term or more is less than the sum of the floors of the terms, each
and one more. -/
theorem div_lt_sum_map_succ {α : Type} (f : α → Nat) (d : Nat) : ∀ l : List α, 0 < l.length →
    (l.map f).sum / d < (l.map fun a => f a / d + 1).sum
  | [], h => absurd h (Nat.lt_irrefl 0)
  | [a], _ => by
    show (f a + 0) / d < f a / d + 1 + 0
    exact Nat.lt_succ_self _
  | a :: b :: l, _ => by
    have ih := div_lt_sum_map_succ f d (b :: l) (Nat.succ_pos _)
    have h1 := add_div_le (f a) ((b :: l).map f).sum d
    show (f a + ((b :: l).map f).sum) / d <
      f a / d + 1 + ((b :: l).map fun c => f c / d + 1).sum
    omega

/-- One quotient is no more than another, where the cross products say so. -/
theorem div_le_div_of_cross (x y c d : Nat) (hd : 0 < d) (h : x * d ≤ y * c) : x / c ≤ y / d := by
  refine (Nat.le_div_iff_mul_le hd).mpr ?_
  cases Nat.eq_zero_or_pos c with
  | inl hc =>
    rw [hc, Nat.div_zero, Nat.zero_mul]
    exact Nat.zero_le y
  | inr hc =>
    refine Nat.le_of_mul_le_mul_right ?_ hc
    rw [Nat.mul_right_comm]
    exact Nat.le_trans (Nat.mul_le_mul_right d (Nat.div_mul_le_self x c)) h

end Branch

/-! ## Shares -/

/-- A share of the work: `num` parts of `den`. A share of a share multiplies both, exactly. -/
structure Share where
  num : Nat
  den : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Share

/-- The whole of the work: the share of the trunk. -/
def whole : Share := ⟨1, 1⟩

/-- The shares of the branches of a line with the share `s`, the branches carrying `weights`:
each branch has its weight's part of the sum of the weights. -/
def split (s : Share) (weights : List Nat) : List Share :=
  weights.map fun w => ⟨s.num * w, s.den * weights.sum⟩

/-- **The width of a line with the share `s`**, where the trunk is `trunk` wide and the `k`-th
powers of widths add. `k = 1`: widths add, as in a flow diagram. `k = 2`: Leonardo's rule.
`k = 3`: Murray's law. One rounding, down. -/
def width (k trunk : Nat) (s : Share) : Nat := rootDown k (trunk ^ k * s.num / s.den)

/-- The trunk is drawn at the trunk's width. -/
theorem width_whole (k trunk : Nat) (hk : 0 < k) : whole.width k trunk = trunk := by
  show rootDown k (trunk ^ k * 1 / 1) = trunk
  rw [Nat.mul_one, Nat.div_one]
  exact rootDown_pow k trunk hk

/-- **A greater share is never drawn narrower**: of two shares of one denominator, the one with
more parts is as wide at least. -/
theorem width_mono (k trunk : Nat) {a b : Share} (hd : a.den = b.den) (h : a.num ≤ b.num) :
    a.width k trunk ≤ b.width k trunk := by
  show rootDown k (trunk ^ k * a.num / a.den) ≤ rootDown k (trunk ^ k * b.num / b.den)
  rw [hd]
  exact rootDown_mono k (Nat.div_le_div_right (Nat.mul_le_mul_left _ h))

/-- **A wider line never carries less**: of two shares of one denominator, the one drawn wider
has more parts. -/
theorem lt_of_width_lt (k trunk : Nat) {a b : Share} (hd : a.den = b.den)
    (h : a.width k trunk < b.width k trunk) : a.num < b.num :=
  Nat.lt_of_not_le fun hle => Nat.not_le_of_lt h (width_mono k trunk hd.symm hle)

/-- A greater share is never drawn narrower, whatever the two denominators: `a` is `b` at most
where `a.num / a.den ≤ b.num / b.den`, said with the cross products. -/
theorem width_mono_cross (k trunk : Nat) {a b : Share} (hb : 0 < b.den)
    (h : a.num * b.den ≤ b.num * a.den) : a.width k trunk ≤ b.width k trunk := by
  refine rootDown_mono k (Branch.div_le_div_of_cross _ _ a.den b.den hb ?_)
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h

/-- **A branch of a branch has the products of the parts**, with no rounding: its weight in its
fork times its line's weight, over the product of the two sums. The two forks may have any
weights, so this holds at every depth, and a width is rounded once. -/
theorem split_exact (s : Share) (ws vs : List Nat) {c u : Share} (hc : c ∈ s.split ws)
    (hu : u ∈ c.split vs) :
    ∃ w ∈ ws, ∃ v ∈ vs, u = ⟨s.num * (w * v), s.den * (ws.sum * vs.sum)⟩ := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact ⟨w, hw, v, hv, congr (congrArg Share.mk (Nat.mul_assoc _ _ _)) (Nat.mul_assoc _ _ _)⟩

/-- The branches of branches, where the denominator is given. -/
theorem split_split_aux (n d e : Nat) (vs : List Nat) : ∀ ws : List Nat,
    (ws.map fun w => (⟨n * w, d⟩ : Share)).flatMap
        (fun c => vs.map fun v => (⟨c.num * v, c.den * e⟩ : Share)) =
      (ws.flatMap fun w => vs.map fun v => w * v).map fun x => (⟨n * x, d * e⟩ : Share)
  | [] => rfl
  | w :: ws => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      split_split_aux n d e vs ws, List.map_map]
    exact congrArg (· ++ _) (List.map_congr_left fun v _ =>
      congrArg (fun x => (⟨x, d * e⟩ : Share)) (Nat.mul_assoc n w v))

/-- **A fork in every branch of a fork is one fork**, whose weights are the products of the
weights: the same shares, in the same order, with no rounding. -/
theorem split_split (s : Share) (ws vs : List Nat) :
    (s.split ws).flatMap (fun c => c.split vs) =
      s.split (ws.flatMap fun w => vs.map fun v => w * v) := by
  show (ws.map fun w => (⟨s.num * w, s.den * ws.sum⟩ : Share)).flatMap
      (fun c => vs.map fun v => (⟨c.num * v, c.den * vs.sum⟩ : Share)) =
    (ws.flatMap fun w => vs.map fun v => w * v).map fun x =>
      (⟨s.num * x, s.den * (ws.flatMap fun w => vs.map fun v => w * v).sum⟩ : Share)
  rw [split_split_aux s.num (s.den * ws.sum) vs.sum vs ws, Branch.sum_products vs ws,
    Nat.mul_assoc]

/-- A branch is never wider than its line. -/
theorem width_split_le (k trunk : Nat) (s : Share) (weights : List Nat) {c : Share}
    (hc : c ∈ s.split weights) : c.width k trunk ≤ s.width k trunk := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  cases Nat.eq_zero_or_pos s.den with
  | inl h0 =>
    show rootDown k (trunk ^ k * (s.num * w) / (s.den * weights.sum)) ≤
      rootDown k (trunk ^ k * s.num / s.den)
    rw [h0, Nat.zero_mul, Nat.div_zero, Nat.div_zero]
    exact Nat.le_refl _
  | inr hpos =>
    refine width_mono_cross k trunk hpos ?_
    show s.num * w * s.den ≤ s.num * (s.den * weights.sum)
    rw [Nat.mul_assoc, Nat.mul_comm w s.den]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Branch.le_sum_of_mem w weights hw))

/-- The sum of the exact quantities of the branches is the quantity of the line, before any
rounding. -/
theorem sum_split_quantity (k trunk : Nat) (s : Share) (weights : List Nat)
    (hw : 0 < weights.sum) :
    (weights.map fun w => trunk ^ k * (s.num * w)).sum / (s.den * weights.sum) =
      trunk ^ k * s.num / s.den := by
  have e : (weights.map fun w => trunk ^ k * (s.num * w)).sum =
      trunk ^ k * s.num * weights.sum := by
    rw [← Branch.sum_map_mul_left (trunk ^ k * s.num) weights]
    exact congrArg List.sum (List.map_congr_left fun w _ => (Nat.mul_assoc _ _ _).symm)
  rw [e, Nat.mul_div_mul_right _ _ hw]

/-- **The branches carry no more than their line.** The `k`-th powers of the widths of the
branches sum to the line's quantity at most. -/
theorem width_conserves_le (k trunk : Nat) (hk : 0 < k) (s : Share) (weights : List Nat)
    (hw : 0 < weights.sum) :
    ((s.split weights).map fun c => c.width k trunk ^ k).sum ≤ trunk ^ k * s.num / s.den := by
  rw [split, List.map_map, ← sum_split_quantity k trunk s weights hw]
  show (weights.map fun w =>
    rootDown k (trunk ^ k * (s.num * w) / (s.den * weights.sum)) ^ k).sum ≤ _
  exact Nat.le_trans
    (Branch.sum_map_le _ (fun w => trunk ^ k * (s.num * w) / (s.den * weights.sum)) weights
      fun w _ => rootDown_pow_le k _ hk)
    (Branch.sum_map_div_le (fun w => trunk ^ k * (s.num * w)) (s.den * weights.sum) weights)

/-- **The branches carry no less than their line, to one unit of width each.** With every
branch one unit wider, the `k`-th powers of the widths sum to more than the line's quantity. -/
theorem width_conserves_lt (k trunk : Nat) (hk : 0 < k) (s : Share) (weights : List Nat)
    (hw : 0 < weights.sum) :
    trunk ^ k * s.num / s.den <
      ((s.split weights).map fun c => (c.width k trunk + 1) ^ k).sum := by
  rw [split, List.map_map, ← sum_split_quantity k trunk s weights hw]
  show _ < (weights.map fun w =>
    (rootDown k (trunk ^ k * (s.num * w) / (s.den * weights.sum)) + 1) ^ k).sum
  exact Nat.lt_of_lt_of_le
    (Branch.div_lt_sum_map_succ (fun w => trunk ^ k * (s.num * w)) (s.den * weights.sum) weights
      (Branch.length_pos_of_sum_pos weights hw))
    (Branch.sum_map_le (fun w => trunk ^ k * (s.num * w) / (s.den * weights.sum) + 1) _ weights
      fun w _ => Nat.succ_le_of_lt (lt_rootDown_succ_pow k _ hk))

/-- **At a fork the widths conserve.** For the widths `c` of the branches of a line with the
share `s`, and `q` the line's quantity `trunk ^ k * s.num / s.den`: the powers `c ^ k` sum to
`q` at most, and the powers `(c + 1) ^ k` to more than `q`. This holds for every exponent
`k > 0` and for unequal weights, where some weight is not `0`. -/
theorem width_conserves (k trunk : Nat) (hk : 0 < k) (s : Share) (weights : List Nat)
    (hw : 0 < weights.sum) :
    ((s.split weights).map fun c => c.width k trunk ^ k).sum ≤ trunk ^ k * s.num / s.den ∧
      trunk ^ k * s.num / s.den <
        ((s.split weights).map fun c => (c.width k trunk + 1) ^ k).sum :=
  ⟨width_conserves_le k trunk hk s weights hw, width_conserves_lt k trunk hk s weights hw⟩

end Share

/-! ## Lines that wobble -/

namespace Branch

/-- **The greatest wobble, per mille of a width, at which a line `narrow` wide is narrower than
a line `wide` wide at every point**: the narrow line at its widest is then no wider than the
wide line at its narrowest. -/
def wobbleRoom (narrow wide : Nat) : Nat := 1000 * (wide - narrow) / (wide + narrow)

/-- **Within the room, two lines are apart.** A line `n` wide that wobbles `amp` per mille wider
is no wider than a line `w` wide that wobbles `amp` per mille narrower, where `n` is `w` at
most. -/
theorem wobbleRoom_apart (n w amp : Nat) (hnw : n ≤ w) (h : amp ≤ wobbleRoom n w) :
    n * (1000 + amp) ≤ w * (1000 - amp) := by
  have h1 : amp * (w + n) ≤ 1000 * (w - n) :=
    Nat.le_trans (Nat.mul_le_mul_right (w + n) h) (Nat.div_mul_le_self _ _)
  rw [Nat.mul_add] at h1
  rw [Nat.mul_add, Nat.mul_sub, Nat.mul_comm n amp, Nat.mul_comm w amp]
  omega

/-- **The room is the greatest.** A wobble of a thousand per mille at most that keeps the two
lines apart is within the room, where one of the two widths is not `0`. -/
theorem wobbleRoom_greatest (n w amp : Nat) (hpos : 0 < w + n) (ha : amp ≤ 1000)
    (h : n * (1000 + amp) ≤ w * (1000 - amp)) : amp ≤ wobbleRoom n w := by
  refine (Nat.le_div_iff_mul_le hpos).mpr ?_
  have h2 : amp * w ≤ 1000 * w := Nat.mul_le_mul_right w ha
  rw [Nat.mul_add, Nat.mul_sub, Nat.mul_comm n amp, Nat.mul_comm w amp] at h
  rw [Nat.mul_add]
  omega

end Branch

/-! ## Finite evaluations -/

#guard rootDown 2 2 = 1
#guard rootDown 3 1000 = 10
#guard rootDown 2 (10 ^ 18) = 10 ^ 9
#guard Branch.wobbleRoom (Share.width 2 1000000 ⟨1, 2⟩) (Share.width 2 1000000 Share.whole) = 171

end Whatwg.Svg.Scene
