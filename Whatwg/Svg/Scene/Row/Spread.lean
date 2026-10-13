
/-!
# Whatwg.Svg.Scene.Row.Spread

Owner: things of one row put apart (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

A method that places the things of a row near their neighbours in other rows gives each thing a
place that it asks for, and two of them may ask for one place. A last pass puts them apart,
from the left: each thing stays where it asked to be, or moves right as far as the thing before
it makes it. lean4-effect4 has this as `spread` of its `tools/Tools/View/Place.lean`, after the
places of Brandes and Köpf, and proves of it that each thing is apart from the one before it.
Here it is for things of any type and any distance between two things, and the laws say more:
every two things are apart and not neighbours only, and no row that is apart and gives each
thing its place or more stands anywhere to the left of this one.

- `Row.spread sep l`: **the things of `l`, apart.** `l` has each thing with the place that it
  asks for, and `sep a b` is how far the place of `b` must be after the place of `a` when `b`
  follows `a`.
- `Row.Apart sep l`: each thing of the row is as far after the thing before it as `sep` asks.
- `Row.NoLess l m`: `m` has the things of `l`, in their order, each at its place or further on.

What the laws say:

- `spread_apart`: the row is apart.
- `spread_noLess`: it has the things given, in their order, and no thing stands before the
  place that it asked for.
- `spread_least`: **it is the least such row.** Any row that is apart and has each thing at the
  place it asked for or further on has it at its place in `spread`, or further on. So the row
  is as far left as it can be, thing by thing.
- `spread_of_apart`: a row that is apart is left as it is. So spreading twice is spreading once.
- `Apart.pairwise`, `spread_pairwise`: **every two things are apart**, and not neighbours only,
  where `sep` does not shorten a way: `sep a c ≤ sep a b + sep b c`. A distance that is the
  half widths of two things and a gap is so.
- `NoLess.refl`, `NoLess.trans`: `NoLess` is an order of the rows of one list of things.

What a caller must supply: the distance `sep`. It reads two things, so it can be their half
widths and a gap, as the consumer has it.

What this module does not claim: that the row is the narrowest that keeps the order, since a
thing that asks for a place far to the right keeps it; a pass from the right, or one that
shares a move between the two sides; anything of the order of the things, which it keeps as
given.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Row

variable {α : Type}

/-- **The row is apart**: each thing is as far after the thing before it as `sep` asks. -/
def Apart (sep : α → α → Int) : List (α × Int) → Prop
  | a :: b :: rest => a.2 + sep a.1 b.1 ≤ b.2 ∧ Apart sep (b :: rest)
  | _ => True

/-- **The second row has the things of the first**, in their order, each at its place or
further on. -/
def NoLess : List (α × Int) → List (α × Int) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.1 = b.1 ∧ a.2 ≤ b.2 ∧ NoLess as bs
  | _, _ => False

/-- Whether a row is apart, decided along the row. -/
def decApart (sep : α → α → Int) : ∀ l : List (α × Int), Decidable (Apart sep l)
  | [] => isTrue True.intro
  | [_] => isTrue True.intro
  | a :: b :: rest =>
    have : Decidable (Apart sep (b :: rest)) := decApart sep (b :: rest)
    inferInstanceAs (Decidable (a.2 + sep a.1 b.1 ≤ b.2 ∧ Apart sep (b :: rest)))

/-- Whether a row is apart is decided, so a program can test a row that it did not build with
`spread`. -/
instance (sep : α → α → Int) (l : List (α × Int)) : Decidable (Apart sep l) := decApart sep l

/-- The things after a thing `u` at `xu`, apart: each at the place it asks for, or as far after
the thing before it as `sep` asks, whichever is further on. -/
def spreadAfter (sep : α → α → Int) : α → Int → List (α × Int) → List (α × Int)
  | _, _, [] => []
  | u, xu, (k, x) :: rest =>
    (k, max x (xu + sep u k)) :: spreadAfter sep k (max x (xu + sep u k)) rest

/-- **The things of a row, apart.** The first stays at the place it asks for, and each later
thing at its place, or as far after the thing before it as `sep` asks. -/
def spread (sep : α → α → Int) : List (α × Int) → List (α × Int)
  | [] => []
  | (k, x) :: rest => (k, x) :: spreadAfter sep k x rest

/-! ## The order of rows -/

/-- A row has its own things at their places. -/
theorem NoLess.refl : ∀ l : List (α × Int), NoLess l l
  | [] => True.intro
  | a :: l => ⟨rfl, Int.le_refl a.2, NoLess.refl l⟩

theorem NoLess.trans : ∀ {l m n : List (α × Int)}, NoLess l m → NoLess m n → NoLess l n
  | [], [], [], _, _ => True.intro
  | _ :: _, _ :: _, _ :: _, h, k =>
    ⟨h.1.trans k.1, Int.le_trans h.2.1 k.2.1, NoLess.trans h.2.2 k.2.2⟩

/-- A row that is no less than another has as many things. -/
theorem NoLess.length : ∀ {l m : List (α × Int)}, NoLess l m → l.length = m.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (NoLess.length h.2.2)

/-- A row that is no less than another has its things, in their order. -/
theorem NoLess.keys : ∀ {l m : List (α × Int)}, NoLess l m →
    l.map (fun p => p.1) = m.map (fun p => p.1)
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    rw [List.map_cons, List.map_cons, h.1, NoLess.keys h.2.2]

/-! ## What `spread` gives -/

/-- A thing and the things after it, apart, are apart. -/
private theorem apart_after (sep : α → α → Int) : ∀ (u : α) (xu : Int) (rest : List (α × Int)),
    Apart sep ((u, xu) :: spreadAfter sep u xu rest)
  | _, _, [] => True.intro
  | u, xu, (k, x) :: rest =>
    ⟨Int.le_max_right x (xu + sep u k), apart_after sep k _ rest⟩

/-- **The row is apart.** -/
theorem spread_apart (sep : α → α → Int) : ∀ l : List (α × Int), Apart sep (spread sep l)
  | [] => True.intro
  | (k, x) :: rest => apart_after sep k x rest

private theorem noLess_after (sep : α → α → Int) : ∀ (u : α) (xu : Int) (rest : List (α × Int)),
    NoLess rest (spreadAfter sep u xu rest)
  | _, _, [] => True.intro
  | u, xu, (k, x) :: rest =>
    ⟨rfl, Int.le_max_left x (xu + sep u k), noLess_after sep k _ rest⟩

/-- **The row has the things given, and no thing stands before the place that it asked
for.** -/
theorem spread_noLess (sep : α → α → Int) : ∀ l : List (α × Int), NoLess l (spread sep l)
  | [] => True.intro
  | (k, x) :: rest => ⟨rfl, Int.le_refl x, noLess_after sep k x rest⟩

private theorem least_after (sep : α → α → Int) : ∀ (u : α) (xu zu : Int)
    (rest z : List (α × Int)), xu ≤ zu → NoLess rest z → Apart sep ((u, zu) :: z) →
    NoLess (spreadAfter sep u xu rest) z
  | _, _, _, [], [], _, _, _ => True.intro
  | u, xu, zu, (k, x) :: rest, (k', zx) :: zs, hx, hn, ha => by
    have ek : k = k' := hn.1
    have h1 : x ≤ zx := hn.2.1
    have h2 : zu + sep u k' ≤ zx := ha.1
    have h3 : max x (xu + sep u k) ≤ zx := by
      rw [ek]
      omega
    refine ⟨ek, h3, least_after sep k _ zx rest zs h3 hn.2.2 ?_⟩
    rw [ek]
    exact ha.2

/-- **The row is the least that is apart and gives each thing its place or more.** -/
theorem spread_least (sep : α → α → Int) : ∀ {l z : List (α × Int)}, NoLess l z → Apart sep z →
    NoLess (spread sep l) z
  | [], [], _, _ => True.intro
  | (k, x) :: rest, (k', zx) :: zs, hn, ha => by
    have ek : k = k' := hn.1
    refine ⟨ek, hn.2.1, least_after sep k x zx rest zs hn.2.1 hn.2.2 ?_⟩
    rw [ek]
    exact ha

private theorem after_of_apart (sep : α → α → Int) : ∀ (u : α) (xu : Int)
    (rest : List (α × Int)), Apart sep ((u, xu) :: rest) → spreadAfter sep u xu rest = rest
  | _, _, [], _ => rfl
  | u, xu, (k, x) :: rest, h => by
    have h1 : xu + sep u k ≤ x := h.1
    have e : max x (xu + sep u k) = x := by omega
    show (k, max x (xu + sep u k)) :: spreadAfter sep k (max x (xu + sep u k)) rest =
      (k, x) :: rest
    rw [e, after_of_apart sep k x rest h.2]

/-- **A row that is apart is left as it is.** -/
theorem spread_of_apart (sep : α → α → Int) : ∀ {l : List (α × Int)}, Apart sep l →
    spread sep l = l
  | [], _ => rfl
  | (k, x) :: rest, h => congrArg ((k, x) :: ·) (after_of_apart sep k x rest h)

/-- Spreading twice is spreading once. -/
theorem spread_spread (sep : α → α → Int) (l : List (α × Int)) :
    spread sep (spread sep l) = spread sep l := spread_of_apart sep (spread_apart sep l)

/-! ## Every two things -/

/-- In a row that is apart, where `sep` does not shorten a way, the first thing is apart from
every later thing. -/
private theorem apart_head {sep : α → α → Int} (ht : ∀ a b c, sep a c ≤ sep a b + sep b c) :
    ∀ (rest : List (α × Int)) (a : α × Int), Apart sep (a :: rest) →
      ∀ q ∈ rest, a.2 + sep a.1 q.1 ≤ q.2
  | [], _, _, _, hq => nomatch hq
  | b :: rest, a, h, q, hq => by
    have h1 : a.2 + sep a.1 b.1 ≤ b.2 := h.1
    cases List.mem_cons.mp hq with
    | inl e =>
      rw [e]
      exact h1
    | inr hq' =>
      have h2 := apart_head ht rest b h.2 q hq'
      have h3 := ht a.1 b.1 q.1
      omega

/-- **In a row that is apart, every two things are apart**, where `sep` does not shorten a
way. -/
theorem Apart.pairwise {sep : α → α → Int} (ht : ∀ a b c, sep a c ≤ sep a b + sep b c) :
    ∀ {l : List (α × Int)}, Apart sep l → l.Pairwise fun p q => p.2 + sep p.1 q.1 ≤ q.2
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.cons (fun _ hq => nomatch hq) List.Pairwise.nil
  | a :: b :: rest, h =>
    List.Pairwise.cons (apart_head ht (b :: rest) a h) (Apart.pairwise ht h.2)

/-- **Every two things of the row are apart**, where `sep` does not shorten a way. -/
theorem spread_pairwise {sep : α → α → Int} (ht : ∀ a b c, sep a c ≤ sep a b + sep b c)
    (l : List (α × Int)) : (spread sep l).Pairwise fun p q => p.2 + sep p.1 q.1 ≤ q.2 :=
  Apart.pairwise ht (spread_apart sep l)

end Row

end Whatwg.Svg.Scene
